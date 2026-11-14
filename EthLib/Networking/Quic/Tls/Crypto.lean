module

public import EthLib.Networking.Quic.Tls.Wire
public import EthLib.Networking.Libp2p.Tls
public import EthLib.Cryptography.X25519

/-!
# Cryptographic operations of the certificate handshake

The group encodings and shared secrets follow [RFC 8446 §§4.2.8.2 and 7.4.2][tls].

P-256 signing and ECDH follow [SEC 1 v2 §§4.1.3 and 3.3.1][sec1].

These backends select no accepted algorithm policy.

The caller supplies private keys and a fresh secret nonce for each ECDSA signature.

A nonce that produces a zero signature scalar is rejected so that the caller can try another.

No operation claims constant-time execution or generates randomness.

[tls]: https://www.rfc-editor.org/rfc/rfc8446#section-7.4.2
[sec1]: https://www.secg.org/sec1-v2.pdf
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Crypto

open EthLib.Base
open EthLib.Cryptography

/-- An unsupported algorithm, malformed key, degenerate exchange or unsuitable signing nonce. -/
inductive Error where
  | group
  | privateKey
  | keyShare
  | sharedSecret
  | signatureScheme
  | nonce
  deriving Repr, DecidableEq

/-- Stable local error codes for the cryptographic boundary. -/
def Error.code : Error → UInt32
  | .group => 1
  | .privateKey => 2
  | .keyShare => 3
  | .sharedSecret => 4
  | .signatureScheme => 5
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

/-- A field coordinate as 32 big-endian octets, including leading zeros (§7.4.2). -/
def coordinate (value : Secp256r1.Fp) : Vector UInt8 32 :=
  ⟨(natToBytes 32 value.val).toArray, by simp [natToBytes_length]⟩

/-- Read an uncompressed P-256 key share, RFC 8446 §4.2.8.2 and SEC 1 v2 §2.3.4.

The cofactor is one, so an affine point on P-256 satisfies its subgroup check. -/
def readP256Share (peer : ByteArray) : Except Error Secp256r1.Point := do
  match peer.toList with
  | 4 :: coords =>
    ensure (coords.length = 64) .keyShare
    let x := bytesToNat (coords.take 32)
    let y := bytesToNat (coords.drop 32)
    if hx : x < Secp256r1.Fp.modulus then
      if hy : y < Secp256r1.Fp.modulus then
        let point := Secp256r1.Point.affine ⟨x, hx⟩ ⟨y, hy⟩
        ensure (point.isOnCurve = true) .keyShare
        return point
      else throw .keyShare
    else throw .keyShare
  | _ => throw .keyShare

/-- Encode one public ECDHE key, RFC 8446 §§4.2.8.2 and 7.4.2.

X25519 uses the RFC 7748 scalar bytes; P-256 reads a big-endian scalar in `[1, n - 1]`. -/
def keyShare (group : Wire.CodePoint) (privateKey : Vector UInt8 32) :
    Except Error ByteArray := do
  if group.val = 0x001d then
    return packBytes (X25519.publicKey privateKey)
  else if group.val = 0x0017 then
    let scalar ← readScalar privateKey .privateKey
    match Secp256r1.Point.mul scalar .generator with
    | .infinity => throw .privateKey
    | .affine x y => return ⟨(4 :: (coordinate x).toList ++ (coordinate y).toList).toArray⟩
  else throw .group

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
  else throw .group

/-- Sign CertificateVerify's complete content with P-256/SHA-256, RFC 8446 §4.4.3.

The ECDSA operation is SEC 1 v2 §4.1.3, with a caller-supplied nonce in `[1, n - 1]`.

The DER sequence of the signature scalars follows RFC 3279 §2.2.3. -/
def signCertificateVerify (algorithm : Wire.CodePoint) (privateKey nonce : Vector UInt8 32)
    (content : ByteArray) : Except Error ByteArray := do
  ensure (algorithm.val = 0x0403) .signatureScheme
  let secret ← readScalar privateKey .privateKey
  let k ← readScalar nonce .nonce
  match Secp256r1.Point.mul k .generator with
  | .infinity => throw .nonce
  | .affine x _ =>
    let r : Secp256r1.Fn := Fin.ofNat _ x.val
    let e : Secp256r1.Fn := Fin.ofNat _ (bytesToNat (Hash.Sha256.hash32 content).toList)
    let s := Secp256r1.Fn.inv k * (e + r * secret)
    ensure (r ≠ 0 ∧ s ≠ 0) .nonce
    return Libp2p.encodeSignature r.val s.val

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
