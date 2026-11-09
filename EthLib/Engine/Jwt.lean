module

public import EthLib.Base.Base64
public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Engine.Jwt.Json

/-!
# Engine API authentication with JSON Web Tokens

The Engine profile uses a 32-byte secret, HS256 and an `iat` within 60 seconds of the clock.

HS256 is HMAC-SHA-256 over the original encoded header, a period, and the encoded claims.

Unknown claims are ignored, as [Engine authentication, JWT Claims][engine] requires.

The compact form and critical headers follow [RFC 7515 §§3.1 and 4.1.11][jws].

The MAC follows [RFC 7518 §3.2][hs256], and NumericDate follows [RFC 7519 §§2 and 4.1.6][jwt].

The secret and tag comparison make no constant-time claim (SOUNDNESS.md A3).

[engine]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/authentication.md
[jws]: https://www.rfc-editor.org/rfc/rfc7515#section-3.1
[hs256]: https://www.rfc-editor.org/rfc/rfc7518#section-3.2
[jwt]: https://www.rfc-editor.org/rfc/rfc7519#section-4.1.6
-/

@[expose] public section

namespace EthLib.Engine.Jwt

open EthLib.Base

/-- Why building or authenticating an Engine token failed. -/
inductive JwtError where
  | secretLength
  | compact
  | header
  | algorithm
  | critical
  | claims
  | signature
  | serialization
  deriving Repr, DecidableEq

/-- Stable error codes for the bindings, one per failure. -/
def JwtError.code : JwtError → UInt32
  | .secretLength => 1 | .compact => 2 | .header => 3 | .algorithm => 4
  | .critical => 5 | .claims => 6 | .signature => 7 | .serialization => 8

/-- The three encoded parts of the JWS compact form. -/
structure Parts where
  header : String
  claims : String
  signature : String

/-- Split the compact form at its two period separators, RFC 7515 §3.1. -/
def parts (token : String) : Option Parts :=
  match token.toList.splitOn '.' with
  | [header, claims, signature] =>
    some ⟨String.ofList header, String.ofList claims, String.ofList signature⟩
  | _ => none

/-- Join three encoded parts with the separators of RFC 7515 §3.1. -/
def compact (header claims signature : String) : String :=
  header ++ "." ++ claims ++ "." ++ signature

/-- The original ASCII signing input, RFC 7515 §5.2, step 8. -/
def signingInput (header claims : String) : ByteArray := (header ++ "." ++ claims).toUTF8

/-- The HS256 signature, encoded as base64url, RFC 7518 §3.2. -/
def signature (secret : ByteArray) (header claims : String) : String :=
  Base64.encode (Cryptography.Hash.Hmac.hmac secret (signingInput header claims))

/-- Decode a base64url part to the fields of its UTF-8 JSON object. -/
def objectFields (segment : String) : Option (List (String × Json.Value)) := do
  let .ok bytes := Base64.decode segment | none
  let text ← String.fromUTF8? bytes
  Json.fields text

/-- The algorithm of a header with no unsupported critical extension, RFC 7515 §4.1.11. -/
def algorithm (header : String) : Except JwtError String := do
  let some fields := objectFields header | throw .header
  if (fields.lookup "crit").isSome then throw .critical else do
  let some (.str name) := fields.lookup "alg" | throw .algorithm
  return name

/-- Read the issued-at claim after enforcing the sole supported algorithm, HS256. -/
def issuedAt (header claims : String) : Except JwtError Json.Number := do
  let name ← algorithm header
  if name ≠ "HS256" then throw .algorithm else do
  let some fields := objectFields claims | throw .claims
  let some (.num time) := fields.lookup "iat" | throw .claims
  return time

/-- Authenticate the compact token and return its issued-at time before checking the clock. -/
def authenticate (secret : ByteArray) (token : String) : Except JwtError Json.Number := do
  if secret.size ≠ 32 then throw .secretLength else do
  let some p := parts token | throw .compact
  let time ← issuedAt p.header p.claims
  let .ok mac := Base64.decode p.signature | throw .signature
  if mac = Cryptography.Hash.Hmac.hmac secret (signingInput p.header p.claims) then
    return time
  else throw .signature

/-- Accept an authenticated Engine token only within 60 seconds of its issued-at claim. -/
def check (secret : ByteArray) (token : String) (clock : Nat) : Bool :=
  match authenticate secret token with
  | .ok time => Json.within time clock
  | .error _ => false

/-- Build a token for an integral issued-at time, then sign its compact header and claims.

The builder checks that its generated JSON reads back with that time before signing.

A disagreement is a serialization error, so a successful build carries no parser assumption. -/
def build (secret : ByteArray) (time : Nat) : Except JwtError String := do
  if secret.size ≠ 32 then throw .secretLength else do
  let header := Base64.encode "{\"alg\":\"HS256\",\"typ\":\"JWT\"}".toUTF8
  let claims := Base64.encode ("{\"iat\":" ++ time.repr ++ "}").toUTF8
  match issuedAt header claims with
  | .ok parsed =>
    if parsed = ⟨time, 0⟩ then return compact header claims (signature secret header claims)
    else throw .serialization
  | .error _ => throw .serialization

end EthLib.Engine.Jwt
