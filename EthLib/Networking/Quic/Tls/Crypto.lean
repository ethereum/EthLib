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
  group.val == 0x001d || group.val == 0x0017

/-- Whether a CertificateVerify backend implements this SignatureScheme, RFC 8446 §4.2.3. -/
def supportedSignatureScheme (algorithm : Wire.CodePoint) : Bool :=
  algorithm.val == 0x0403

/-- A nonzero P-256 scalar, read without reduction from a big-endian private input. -/
def readScalar (bytes : Vector UInt8 32) (error : Error) : Except Error Secp256r1.Fn :=
  let value := bytesToNat bytes.toList
  if h : 0 < value ∧ value < Secp256r1.Fn.modulus then .ok ⟨value, h.2⟩
  else .error error

/-- A field coordinate as 32 big-endian octets, with leading zeros, RFC 8446 §7.4.2. -/
def coordinate (value : Secp256r1.Fp) : Vector UInt8 32 :=
  ⟨value.toBytes.toArray, by simp [Secp256r1.Fp.toBytes, natToBytes_length]⟩

/-- Read an uncompressed P-256 key share, RFC 8446 §4.2.8.2 and SEC 1 v2 §2.3.4.

The cofactor is one, so an affine point on P-256 satisfies its subgroup check. -/
def readP256Share (peer : ByteArray) : Except Error Secp256r1.Point :=
  match Secp256r1.decodeUncompressed peer.toList with
  | some point => .ok point
  | none => .error .keyShare

/-- Encode one public ECDHE key, RFC 8446 §§4.2.8.2 and 7.4.2.

X25519 uses the scalar bytes of RFC 7748 §5; P-256 reads a big-endian scalar in `[1, n - 1]`. -/
def keyShare (group : Wire.CodePoint) (privateKey : Vector UInt8 32) :
    Except Error ByteArray := do
  if group.val = 0x001d then
    return packBytes (X25519.publicKey privateKey)
  else if group.val = 0x0017 then
    let scalar ← readScalar privateKey .privateKey
    match Secp256r1.Point.mul scalar .generator with
    | .infinity => throw .privateKey
    | .affine x y => return ⟨(Secp256r1.encodeUncompressed x y).toArray⟩
  else throw (.group group)

/-- Compute ECDHE and reject invalid input or an all-zero X25519 result, RFC 8446 §7.4.2. -/
def sharedSecret (group : Wire.CodePoint) (privateKey : Vector UInt8 32) (peer : ByteArray) :
    Except Error (Vector UInt8 32) := do
  if group.val = 0x001d then
    if h : peer.size = 32 then
      let output := X25519.x25519 privateKey (readBytes peer 0 32 (by omega))
      ensure (output ≠ Vector.replicate 32 0) .sharedSecret
      return output
    else throw .keyShare
  else if group.val = 0x0017 then
    let scalar ← readScalar privateKey .privateKey
    let point ← readP256Share peer
    match Secp256r1.Point.mul scalar point with
    | .infinity => throw .sharedSecret
    | .affine x _ => return coordinate x
  else throw (.group group)

/-- Sign CertificateVerify's complete content with P-256/SHA-256, RFC 8446 §4.4.3.

The ECDSA operation is SEC 1 v2 §4.1.3, with the deterministic nonce of RFC 6979 §3.2.

The DER sequence of the signature scalars follows RFC 3279 §2.2.3. -/
def signCertificateVerify (algorithm : Wire.CodePoint) (privateKey : Vector UInt8 32)
    (content : ByteArray) : Except Error ByteArray := do
  ensure (algorithm.val = 0x0403) (.signatureScheme algorithm)
  let secret ← readScalar privateKey .privateKey
  match Secp256r1.Ecdsa.sign secret (Hash.Sha256.hash32 content) with
  | none => throw .nonce
  | some (r, s) => return Libp2p.encodeSignature r.val s.val

/-- Verify CertificateVerify's signed content under the certificate SPKI, RFC 8446 §4.4.3. -/
def verifyCertificateVerify (algorithm : Wire.CodePoint) (spki content signature : ByteArray) :
    Bool :=
  algorithm.val == 0x0403 && Libp2p.Tls.verifyP256 spki content signature

/-- Whether a P-256 signing secret matches the certificate's public key. -/
def publicKeyMatches (privateKey : Vector UInt8 32) (spki : ByteArray) : Bool :=
  match readScalar privateKey .privateKey, Libp2p.Tls.readP256 spki with
  | .ok scalar, .ok point => Secp256r1.Point.mul scalar .generator == point
  | _, _ => false

end EthLib.Networking.Quic.Tls.Crypto
