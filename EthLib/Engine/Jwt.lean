module

public import EthLib.Base.Base64
public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Engine.Jwt.Json

/-!
# Engine API authentication with JSON Web Tokens

The Engine profile uses a 32-byte secret, HS256 and an `iat` within 60 seconds of the clock.

The secret and tag comparison make no constant-time claim (SOUNDNESS.md A3).

A step comment names its source and section, as in RFC 7515 §5.2, step 8.

The sources:

- [Engine authentication][engine], at commit `3284ee8` of execution-apis
- the compact form and critical headers, [RFC 7515 §§3.1 and 4.1.11][jws]
- making and validating a JWS, [RFC 7515 §5.1][jws-make] and [§5.2][jws-check]
- the MAC, [RFC 7518 §3.2][hs256]
- NumericDate and the issued-at claim, [RFC 7519 §§2 and 4.1.6][jwt]
- making and validating a JWT, [RFC 7519 §7.1][jwt-make] and [§7.2][jwt-check]
- [erratum 8225][eid8225] of RFC 7519, on step 9 of §7.2

[engine]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/authentication.md
[jws]: https://www.rfc-editor.org/rfc/rfc7515#section-3.1
[jws-make]: https://www.rfc-editor.org/rfc/rfc7515#section-5.1
[jws-check]: https://www.rfc-editor.org/rfc/rfc7515#section-5.2
[hs256]: https://www.rfc-editor.org/rfc/rfc7518#section-3.2
[jwt]: https://www.rfc-editor.org/rfc/rfc7519#section-4.1.6
[jwt-make]: https://www.rfc-editor.org/rfc/rfc7519#section-7.1
[jwt-check]: https://www.rfc-editor.org/rfc/rfc7519#section-7.2
[eid8225]: https://www.rfc-editor.org/errata/eid8225
-/

@[expose] public section

namespace EthLib.Engine.Jwt

open EthLib.Base

/-- Why building or authenticating an Engine token failed.

A failed signature check carries nothing, so that it reveals nothing about the expected tag. -/
inductive JwtError where
  /-- The secret has `size` bytes, where the Engine API takes 32.

  The size of a rejected secret says nothing about a key of 32 bytes. -/
  | secretLength (size : Nat)
  /-- The token has `count` parts separated by periods, where the compact form has three.

  The count comes from the token, not from the key. -/
  | compact (count : Nat)
  /-- The header is not a JSON object. -/
  | header
  /-- The header names the algorithm `name`, other than HS256, or no algorithm as a string. -/
  | algorithm (name : Option String)
  /-- The header names a critical extension, which this profile does not support. -/
  | critical
  /-- The claims are not a JSON object with a numeric issued-at time. -/
  | claims
  /-- The signature does not decode, or does not match. -/
  | signature
  /-- A built token does not read back with its time, which never happens. -/
  | serialization
  deriving Repr, DecidableEq

/-- Stable error codes for the bindings, one per failure. -/
def JwtError.code : JwtError → UInt32
  | .secretLength _ => 1 | .compact _ => 2 | .header => 3 | .algorithm _ => 4
  | .critical => 5 | .claims => 6 | .signature => 7 | .serialization => 8

/-- The three encoded parts of the JWS compact form. -/
structure Parts where
  header : String
  claims : String
  signature : String

/-- Split the compact form at its two period separators, RFC 7515 §3.1. -/
def parts (token : String) : Option Parts :=
  -- RFC 7515 §5.2, step 1: the encoded header, payload and signature, in that order.
  --
  -- A single period separates each from the next, so exactly two periods.
  match token.toList.splitOn '.' with
  | [header, claims, signature] =>
    some ⟨String.ofList header, String.ofList claims, String.ofList signature⟩
  -- Any other count of parts is not the compact form, so step 1 fails.
  | _ => none

/-- Join three encoded parts with the separators of RFC 7515 §3.1. -/
def compact (header claims signature : String) : String :=
  -- RFC 7515 §5.1, step 8: `H || '.' || P || '.' || S`.
  --
  -- `H`, `P` and `S` are the encoded header, payload and signature.
  header ++ "." ++ claims ++ "." ++ signature

/-- The original ASCII signing input, RFC 7515 §5.2, step 8. -/
def signingInput (header claims : String) : ByteArray :=
  -- RFC 7515 §5.1, step 5, and §5.2, step 8: `ASCII(H || '.' || P)`, for the encoded parts.
  --
  -- For validation they are the parts as received, never encoded again.
  --
  -- For base64url text, its UTF-8 bytes are its ASCII bytes; any other part fails to decode later.
  (header ++ "." ++ claims).toUTF8

/-- The HS256 signature, encoded as base64url, RFC 7518 §3.2. -/
def signature (secret : ByteArray) (header claims : String) : String :=
  -- RFC 7518 §3.2: the HMAC of RFC 2104, with SHA-256 as `H` and the signing input as `text`.
  --
  -- RFC 7515 §5.1, step 6: the encoded signature is `BASE64URL(JWS Signature)`.
  Base64.encode (Cryptography.Hash.Hmac.hmac secret (signingInput header claims))

/-- Decode a base64url part to the fields of its UTF-8 JSON object. -/
def objectFields (segment : String) : Option (List (String × Json.Value)) := do
  -- RFC 7515 §5.2, step 2 for the header and step 6 for the payload: base64url-decode the part.
  --
  -- The decoder takes only the text its encoder writes, so no line break, space or other character.
  let .ok bytes := Base64.decode segment | none
  -- RFC 7515 §5.2, step 3, and RFC 7519 §7.2, steps 4 and 10: the bytes are UTF-8.
  let text ← String.fromUTF8? bytes
  -- They encode a completely valid JSON object, read by RFC 8259, which obsoletes RFC 7159.
  Json.fields text

/-- The algorithm of a header with no unsupported critical extension, RFC 7515 §4.1.11. -/
def algorithm (header : String) : Except JwtError String := do
  -- RFC 7515 §5.2, steps 2 and 3, then step 4: the compact form's JOSE Header is this object.
  --
  -- Step 4 also rejects duplicate names, and EthLib keeps the lexically last one instead.
  --
  -- RFC 7515 §4 allows a parser that returns only the lexically last duplicate member name.
  let some fields := objectFields header | throw .header
  -- Step 5 and §4.1.11: a critical extension that the recipient does not support is invalid.
  --
  -- This profile supports no extension, so any `crit` parameter makes the token invalid.
  if (fields.lookup "crit").isSome then throw .critical else do
  -- Step 8: the `alg` parameter is present, a string that names the algorithm.
  --
  -- RFC 7519 §7.2, step 5 asks that every header parameter be understood or ignorable.
  --
  -- EthLib reads only `alg` and `crit`, and ignores the others, `typ` and `cty` included.
  --
  -- RFC 7515 §4: a parameter not listed as critical MUST be ignored when not understood.
  --
  -- So it never reads a nested JWT, as step 8 of RFC 7519 §7.2 would for `cty` JWT.
  let some (.str name) := fields.lookup "alg" | throw (.algorithm none)
  return name

/-- Read the issued-at claim after enforcing the sole supported algorithm, HS256. -/
def issuedAt (header claims : String) : Except JwtError Json.Number := do
  let name ← algorithm header
  -- Engine authentication, JWT specifications: HS256 MUST be supported and `none` MUST be rejected.
  --
  -- EthLib accepts HS256 alone, an application decision that RFC 7515 §5.2 allows.
  if name ≠ "HS256" then throw (.algorithm (some name)) else do
  -- RFC 7519 §7.2, steps 7 and 10: the payload decodes to a JSON object, the JWT Claims Set.
  --
  -- Step 9 decodes the Message a second time, and EthLib decodes it once.
  --
  -- RFC 7519 erratum 8225, still at status Reported, says that second decoding is wrong.
  let some fields := objectFields claims | throw .claims
  -- Engine authentication, JWT claims: the `iat` claim is required.
  --
  -- RFC 7519 §4.1.6: its value is a number containing a NumericDate.
  --
  -- Unrecognized claims must be ignored, and EthLib ignores every other claim, `id` and `clv` too.
  let some (.num time) := fields.lookup "iat" | throw .claims
  return time

/-- Authenticate the compact token and return its issued-at time before checking the clock. -/
def authenticate (secret : ByteArray) (token : String) : Except JwtError Json.Number := do
  -- Engine authentication, key distribution: a secret key of 256 bits.
  --
  -- RFC 7518 §3.2 asks for a key at least the size of the hash output, 256 bits for HS256.
  --
  -- EthLib takes exactly 32 bytes, the Engine key, and refuses a longer key.
  if secret.size ≠ 32 then throw (.secretLength secret.size) else do
  -- RFC 7515 §5.2, step 1: the three parts of the compact form.
  let some p := parts token | throw (.compact (token.toList.splitOn '.').length)
  -- Step 7: base64url-decode the signature.
  let .ok mac := Base64.decode p.signature | throw .signature
  -- Step 8 and RFC 7518 §3.2: the HMAC SHA-256 of the received signing input is the signature.
  --
  -- RFC 7518 §3.2: the comparison MUST be constant-time, to thwart timing attacks.
  --
  -- This comparison makes no constant-time claim, as SOUNDNESS.md A3 records.
  --
  -- EthLib runs this step before steps 2 to 6, so the JSON reader sees only a matching tag.
  --
  -- §5.2 lets the order change where no step needs the output of another.
  --
  -- Step 8 needs `alg` only to pick the MAC, and this profile fixes it to HS256.
  if mac ≠ Cryptography.Hash.Hmac.hmac secret (signingInput p.header p.claims) then
    throw .signature
  -- Steps 2 to 6, then the algorithm and the claims, for a token whose tag matches.
  else issuedAt p.header p.claims

/-- Accept an authenticated Engine token only within 60 seconds of its issued-at claim. -/
def check (secret : ByteArray) (token : String) (clock : Nat) : Bool :=
  match authenticate secret token with
  -- Engine authentication, JWT claims: `iat` within +-60 seconds of the current time.
  --
  -- The source says SHOULD, and EthLib always enforces it.
  | .ok time => Json.within time clock
  | .error _ => false

/-- The encoded header of a built token: HS256 and the type JWT. -/
def headerPart : String :=
  -- RFC 7515 §5.1, steps 3 and 4: `BASE64URL(UTF8(JWS Protected Header))`.
  --
  -- The header has `alg` HS256 and `typ` JWT.
  Base64.encode "{\"alg\":\"HS256\",\"typ\":\"JWT\"}".toUTF8

/-- The encoded claims of a built token: only the issued-at time, in decimal. -/
def claimsPart (time : Nat) : String :=
  -- RFC 7519 §7.1, steps 1 and 2: the Message is the UTF-8 of a claims set with `iat` alone.
  --
  -- RFC 7515 §5.1, steps 1 and 2: it is the payload, encoded as `BASE64URL(JWS Payload)`.
  Base64.encode ("{\"iat\":" ++ time.repr ++ "}").toUTF8

/-- Build a token for an integral issued-at time, then sign its compact header and claims. -/
def build (secret : ByteArray) (time : Nat) : Except JwtError String := do
  -- Engine authentication, key distribution: a secret key of 256 bits.
  if secret.size ≠ 32 then throw (.secretLength secret.size) else do
  -- Not in the RFCs: the built header and claims must read back with the given time.
  --
  -- That check never fails, so a 32-byte secret always gives a token.
  match issuedAt headerPart (claimsPart time) with
  | .ok parsed =>
    if parsed = ⟨time, 0⟩ then
      -- RFC 7515 §5.1, steps 5, 6 and 8: sign the signing input, then join the three parts.
      return compact headerPart (claimsPart time) (signature secret headerPart (claimsPart time))
    else throw .serialization
  | .error _ => throw .serialization

end EthLib.Engine.Jwt
