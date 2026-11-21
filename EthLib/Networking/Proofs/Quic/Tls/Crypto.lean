module

public import EthLib.Base.Proofs.Except
public import EthLib.Networking.Quic.Tls.Crypto
public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.X25519.Agreement
public import EthLib.Cryptography.Proofs.Secp256r1.Sign
public import EthLib.Serialization.Proofs.Der

/-!
# Proofs: handshake cryptographic checks

X25519 exchanges agree and reject the all-zero result required by RFC 8446 §7.4.2.

CertificateVerify uses the certificate's key and the advertised P-256/SHA-256 scheme.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Crypto

open EthLib.Base
open EthLib.Cryptography
open EthLib.Serialization

/-- A parsed private scalar is nonzero and retains its exact input integer. -/
theorem readScalar_eq_ok_iff (bytes : Vector UInt8 32) (error : Error) (scalar : Secp256r1.Fn) :
    readScalar bytes error = .ok scalar ↔
      scalar.val = bytesToNat bytes.toList ∧ scalar ≠ 0 := by
  unfold readScalar
  dsimp only
  split
  · rename_i h
    simp only [Except.ok.injEq]
    constructor
    · intro he
      subst scalar
      constructor
      · rfl
      · intro hz
        have := congrArg Fin.val hz
        simp at this
        omega
    · rintro ⟨hv, _⟩
      exact Fin.ext hv.symm
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro ⟨hv, hn⟩
    have positive : 0 < scalar.val := Nat.pos_of_ne_zero fun hz => hn (Fin.ext hz)
    exact h ⟨by omega, by simp [← hv]⟩

/-- X25519 accepts exactly its nonzero shared output, without rewriting its bytes. -/
theorem sharedSecret_x25519_eq_ok_iff (privateKey peer output : Vector UInt8 32) :
    sharedSecret 0x001d privateKey (packBytes peer) = .ok output ↔
      X25519.x25519 privateKey peer = output ∧ output ≠ Vector.replicate 32 0 := by
  simp [sharedSecret, bind_ok_iff, ensure_ok_iff, pure, Except.pure]
  constructor
  · rintro ⟨nonzero, rfl⟩
    exact ⟨rfl, nonzero⟩
  · rintro ⟨rfl, nonzero⟩
    exact ⟨nonzero, rfl⟩

/-- The all-zero X25519 output is never accepted, RFC 8446 §7.4.2. -/
theorem sharedSecret_x25519_nonzero (privateKey peer output : Vector UInt8 32)
    (accepted : sharedSecret 0x001d privateKey (packBytes peer) = .ok output) :
    output ≠ Vector.replicate 32 0 :=
  (sharedSecret_x25519_eq_ok_iff privateKey peer output).mp accepted |>.2

/-- Two honest X25519 public shares give the same accepted result or the same rejection. -/
theorem sharedSecret_x25519_agree (a b : Vector UInt8 32) :
    sharedSecret 0x001d a (packBytes (X25519.publicKey b)) =
      sharedSecret 0x001d b (packBytes (X25519.publicKey a)) := by
  simp [sharedSecret, X25519.x25519_agree a b, bind, Except.bind]

/-- CertificateVerify checks both the P-256/SHA-256 identifier and its strict DER signature. -/
theorem verifyCertificateVerify_eq_true_iff (algorithm : Wire.CodePoint)
    (spki content signature : ByteArray) :
    verifyCertificateVerify algorithm spki content signature = true ↔
      algorithm.val = 0x0403 ∧ Libp2p.Tls.verifyP256 spki content signature = true := by
  simp [verifyCertificateVerify]

/-- A generated CertificateVerify verifies under the matching P-256 certificate key. -/
theorem verifyCertificateVerify_signCertificateVerify (privateKey : Vector UInt8 32)
    (content signature spki : ByteArray) (secret : Secp256r1.Fn)
    (key : readScalar privateKey .privateKey = .ok secret)
    (publicKey : Libp2p.Tls.readP256 spki = .ok (Secp256r1.Point.mul secret .generator))
    (signed : signCertificateVerify 0x0403 privateKey content = .ok signature) :
    verifyCertificateVerify 0x0403 spki content signature = true := by
  cases hs : Secp256r1.Ecdsa.sign secret (Hash.Sha256.hash32 content) with
  | none =>
    simp [signCertificateVerify, ensure, key, hs, bind, Except.bind] at signed
  | some rs =>
    obtain ⟨r, s⟩ := rs
    have sig : Der.encodeEcdsaSignature r.val s.val = signature := by
      simpa [signCertificateVerify, ensure, key, hs, bind, Except.bind, pure, Except.pure] using
        signed
    subst signature
    have verified := Secp256r1.Ecdsa.verify_sign_of_sign hs
    -- Signing returns nonzero scalars, so the DER sequence decodes back to them.
    have hd := ((readScalar_eq_ok_iff privateKey .privateKey secret).mp key).2
    simp only [Secp256r1.Ecdsa.sign, hd, ↓reduceIte] at hs
    obtain ⟨k, x, y, -, -, rfl, hr0, -, hs0⟩ := Secp256r1.Ecdsa.signWith_spec hs
    have decoded :=
      EthLib.Serialization.Proofs.Der.decodeEcdsaScalars_eq_some_iff.mpr
        ⟨Nat.pos_of_ne_zero (fun hz => hr0 (Fin.ext hz)), Nat.lt_trans (Fin.isLt _) (by decide),
          Nat.pos_of_ne_zero (fun hz => hs0 (Fin.ext hz)), Nat.lt_trans (Fin.isLt _) (by decide),
          rfl⟩
    simp only [verifyCertificateVerify, show (0x0403 : Wire.CodePoint).val = 0x0403 from rfl,
      beq_self_eq_true, Bool.true_and, Libp2p.Tls.verifyP256, publicKey, decoded]
    exact verified

end EthLib.Networking.Quic.Tls.Crypto
