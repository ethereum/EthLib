module

public import EthLib.Networking.Quic.Tls.Wire
public import EthLib.Networking.Libp2p.Tls
public import EthLib.Cryptography.X25519
public import EthLib.Cryptography.Secp256r1.Encoding
public import EthLib.Cryptography.Secp256r1.Sign

/-!
# Cryptographic operations of the certificate handshake

The group encodings and shared secrets follow [RFC 8446 §§4.2.8.2 and 7.4.2][tls].

P-256 signing and ECDH follow [SEC 1 v2 §§4.1.3 and 3.3.1][sec1].

The signing nonce is the deterministic nonce of RFC 6979, so no caller supplies or reuses one.

The caller's policy, not this module, chooses which algorithms are accepted.

The caller supplies the private keys.

No operation claims constant-time execution or generates randomness.

[tls]: https://www.rfc-editor.org/rfc/rfc8446
[sec1]: https://www.secg.org/sec1-v2.pdf
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Crypto

open EthLib.Base
open EthLib.Cryptography
open EthLib.Serialization

/-- An unsupported algorithm, malformed key, degenerate exchange or exhausted nonce generator. -/
inductive Error where
  /-- The NamedGroup `group` has no ECDHE backend here (RFC 8446 §4.2.7). -/
  | group (group : Wire.CodePoint)
  /-- The private key is not a usable scalar. -/
  | privateKey
  /-- The peer key share is not a valid public key of its group. -/
  | keyShare
  /-- The shared secret is degenerate. -/
  | sharedSecret
  /-- The SignatureScheme `scheme` has no signing backend here (RFC 8446 §4.2.3). -/
  | signatureScheme (scheme : Wire.CodePoint)
  /-- No signing nonce was usable. -/
  | nonce
  deriving Repr, DecidableEq

/-- Stable local error codes for the cryptographic boundary. -/
def Error.code : Error → UInt32
  | .group _ => 1
  | .privateKey => 2
  | .keyShare => 3
  | .sharedSecret => 4
  | .signatureScheme _ => 5
  | .nonce => 6

/-- Whether an ECDHE backend implements this NamedGroup, RFC 8446 §4.2.7. -/
def supportedGroup (group : Wire.CodePoint) : Bool :=
  -- §4.2.7: x25519 is 0x001D and secp256r1 is 0x0017; no other NamedGroup has a backend here.
  group.val == 0x001d || group.val == 0x0017

/-- Whether a CertificateVerify backend implements this SignatureScheme, RFC 8446 §4.2.3. -/
def supportedSignatureScheme (algorithm : Wire.CodePoint) : Bool :=
  -- §4.2.3: 0x0403 is ECDSA with secp256r1 and SHA-256, the only scheme with a backend here.
  algorithm.val == 0x0403

/-- A nonzero P-256 scalar, read without reduction from a big-endian private input. -/
def readScalar (bytes : Vector UInt8 32) (error : Error) : Except Error Secp256r1.Fn :=
  let value := bytesToNat bytes.toList
  -- SEC 1 v2 §3.2.1: a private key `d` is an integer in `[1, n - 1]`.
  --
  -- EthLib rejects a value of `n` or more, rather than reduce it mod `n`.
  if h : 0 < value ∧ value < Secp256r1.Fn.modulus then .ok ⟨value, h.2⟩
  else .error error

/-- A field coordinate as 32 big-endian octets, with leading zeros, RFC 8446 §7.4.2. -/
def coordinate (value : Secp256r1.Fp) : Vector UInt8 32 :=
  -- §7.4.2: the octet string of FE2OSP has constant length, and its leading zeros stay.
  ⟨value.toBytes.toArray, by simp [Secp256r1.Fp.toBytes, natToBytes_length]⟩

/-- Read an uncompressed P-256 key share, RFC 8446 §4.2.8.2 and SEC 1 v2 §2.3.4. -/
def readP256Share (peer : ByteArray) : Except Error Secp256r1.Point :=
  -- §4.2.8.2: `legacy_form = 4`, then `X` and `Y`, of 32 octets each for P-256.
  --
  -- Validation step (2): `x` and `y` lie in `[0, p - 1]`.
  --
  -- Validation step (3): `(x, y)` solves the curve equation.
  --
  -- Validation step (1) holds by the form: it never encodes the point at infinity O.
  --
  -- The subgroup check that §4.2.8.2 does not require holds too: the cofactor of P-256 is one.
  match Secp256r1.decodeUncompressed peer.toList with
  | some point => .ok point
  -- A value that fails a step is not a valid public key of the group.
  | none => .error .keyShare

/-- Encode one public ECDHE key, RFC 8446 §§4.2.8.2 and 7.4.2.

X25519 uses the scalar bytes of RFC 7748 §5; P-256 reads a big-endian scalar. -/
def keyShare (group : Wire.CodePoint) (privateKey : Vector UInt8 32) :
    Except Error ByteArray := do
  -- x25519, 0x001D.
  if group.val = 0x001d then
    -- §7.4.2: the scalar multiplication of the standard base point, u = 9 (RFC 7748 §4.1).
    --
    -- §4.2.8.2: the public value is the 32-byte output of RFC 7748.
    return packBytes (X25519.publicKey privateKey)
  -- secp256r1, 0x0017.
  else if group.val = 0x0017 then
    -- SEC 1 v2 §3.2.1: the secret key `d` lies in `[1, n - 1]`.
    let scalar ← readScalar privateKey .privateKey
    -- SEC 1 v2 §3.2.1: the public key is `Q = dG`.
    match Secp256r1.Point.mul scalar .generator with
    -- `Q = O` needs `d = 0` mod `n`, which the range excludes, so this case never occurs.
    | .infinity => throw .privateKey
    -- §4.2.8.2: `legacy_form = 4`, then `X` and `Y`, each in 32 octets.
    | .affine x y => return ⟨(Secp256r1.encodeUncompressed x y).toArray⟩
  -- No other NamedGroup has a backend here.
  else throw (.group group)

/-- Compute ECDHE and reject invalid input or an all-zero X25519 result, RFC 8446 §7.4.2. -/
def sharedSecret (group : Wire.CodePoint) (privateKey : Vector UInt8 32) (peer : ByteArray) :
    Except Error (Vector UInt8 32) := do
  -- x25519, 0x001D.
  if group.val = 0x001d then
    -- §4.2.8.2: an X25519 public value has 32 bytes.
    let peer ← exactBytes 32 peer fun _ => .keyShare
    -- §7.4.2: the scalar multiplication of the peer's public key by the secret key, used raw.
    let output := X25519.x25519 privateKey peer
    -- §7.4.2: abort if the shared secret is the all-zero value, as in RFC 7748 §6.
    ensure (output ≠ Vector.replicate 32 0) .sharedSecret
    return output
  -- secp256r1, 0x0017.
  else if group.val = 0x0017 then
    -- SEC 1 v2 §3.2.1: the secret key `d` lies in `[1, n - 1]`.
    let scalar ← readScalar privateKey .privateKey
    -- §4.2.8.2: the peer's public value `Q`, validated.
    let point ← readP256Share peer
    -- SEC 1 v2 §3.3.1, step 1: `P = dQ`.
    match Secp256r1.Point.mul scalar point with
    -- Step 2: if `P = O`, output invalid and stop.
    | .infinity => throw .sharedSecret
    -- Step 3 and §7.4.2: the shared secret is `z = x_P`, as the 32 octets of FE2OSP.
    | .affine x _ => return coordinate x
  -- No other NamedGroup has a backend here.
  else throw (.group group)

/-- Sign CertificateVerify's complete content with P-256/SHA-256, RFC 8446 §4.4.3. -/
def signCertificateVerify (algorithm : Wire.CodePoint) (privateKey : Vector UInt8 32)
    (content : ByteArray) : Except Error ByteArray := do
  -- §4.2.3: only 0x0403, ECDSA with secp256r1 and SHA-256, has a signing backend here.
  ensure (algorithm.val = 0x0403) (.signatureScheme algorithm)
  -- SEC 1 v2 §3.2.1: the signing key `d` lies in `[1, n - 1]`.
  let secret ← readScalar privateKey .privateKey
  -- SEC 1 v2 §4.1.3 over the SHA-256 hash of the content, with the nonce of RFC 6979 §3.2.
  match Secp256r1.Ecdsa.sign secret (Hash.Sha256.hash32 content) with
  -- No candidate nonce gave a usable signature.
  | none => throw .nonce
  -- §4.2.3: a DER-encoded ECDSA-Sig-Value, `SEQUENCE { r INTEGER, s INTEGER }`, RFC 3279 §2.2.3.
  | some (r, s) => return Der.encodeEcdsaSignature r.val s.val

/-- Verify CertificateVerify's signed content under the certificate SPKI, RFC 8446 §4.4.3. -/
def verifyCertificateVerify (algorithm : Wire.CodePoint) (spki content signature : ByteArray) :
    Bool :=
  -- §4.2.3: only 0x0403, ECDSA with secp256r1 and SHA-256, has a verifying backend here.
  --
  -- Then ECDSA verification under the key of the certificate, over the SHA-256 hash of the content.
  algorithm.val == 0x0403 && Libp2p.Tls.verifyP256 spki content signature

/-- Whether a P-256 signing secret matches the certificate's public key. -/
def publicKeyMatches (privateKey : Vector UInt8 32) (spki : ByteArray) : Bool :=
  -- A secret `d` in `[1, n - 1]`, and a P-256 key `Q` read from the certificate.
  match readScalar privateKey .privateKey, Libp2p.Tls.readP256 spki with
  -- They match when `Q = dG`, as SEC 1 v2 §3.2.1 derives a public key.
  | .ok scalar, .ok point => Secp256r1.Point.mul scalar .generator == point
  -- A malformed secret or key matches nothing.
  | _, _ => false

end EthLib.Networking.Quic.Tls.Crypto
