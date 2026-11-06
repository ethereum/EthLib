module

public import EthLib.Networking.Enr.V4
public import EthLib.Cryptography.Proofs.Secp256k1.Sign
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding

/-!
# Proofs: the "v4" identity scheme

The "v4" identity scheme of EIP-778, from its section of that name.

A record verifies exactly when ECDSA accepts its 64-byte signature, read as `r` then `s`.

So any ECDSA signature of the hash of its content, under the key of its pair, makes it verify.

The deterministic signer, with the nonce of RFC 6979 and the low-s rule of EIP-2, is one case.

These are correctness statements: no theorem here states that a signature cannot be forged.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Serialization.Rlp

/-- The public key of a record is the point that its `secp256k1` value encodes.

It holds when the `id` is `v4` and the value compresses a curve point other than infinity. -/
theorem publicKeyV4_of_get {r : Enr} {q : Point} (hq : q.isOnCurve = true) (hinf : q ≠ .infinity)
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes q.encodeCompressed)) :
    r.publicKeyV4 = .ok q := by
  cases q with
  | infinity => exact absurd rfl hinf
  | affine x y =>
    have hsize := Point.size_encodeCompressed x y
    have hdec := Point.decode_encodeCompressed hq hinf
    simp only [Enr.publicKeyV4, hid, hkey, ↓reduceIte, hsize, hdec, Except.mapError]

/-- A record verifies exactly when ECDSA accepts its signature under its public key.

The signature has 64 bytes: `r` then `s`, big-endian.

ECDSA signs the Keccak-256 hash of the RLP encoding of the content. -/
theorem verifyV4_eq_true_iff {r : Enr} :
    verifyV4 r = true ↔ ∃ q content, r.publicKeyV4 = .ok q ∧
      Serialization.Rlp.encode r.content = .ok content ∧ r.signature.size = 64 ∧
      Ecdsa.verify q (Hash.Keccak.keccak256 content) (ofBytesBE (r.signature.data.toList.take 32))
        (ofBytesBE (r.signature.data.toList.drop 32)) = true := by
  unfold verifyV4
  constructor
  · intro h
    split at h
    · rename_i q content hq hc
      split at h
      · rename_i hsz
        exact ⟨q, content, hq, hc, hsz, h⟩
      · cases h
    · cases h
  · rintro ⟨q, content, hq, hc, hsz, hv⟩
    rw [hq, hc]
    simp only [hsz, ↓reduceIte]
    exact hv

/-- A record that verifies has a public key. -/
theorem publicKeyV4_ok_of_verifyV4 {r : Enr} (h : verifyV4 r = true) :
    ∃ q, r.publicKeyV4 = .ok q := by
  obtain ⟨q, _, hq, -⟩ := verifyV4_eq_true_iff.mp h
  exact ⟨q, hq⟩

/-- A record verifies when ECDSA accepts `(r, s)` under the key of its `secp256k1` pair.

The signature is `r` then `s`, each in 32 big-endian bytes, as the "v4" scheme of EIP-778 says.

ECDSA signs the Keccak-256 hash of the RLP encoding of the content.

Any nonce and either sign of `s` will do. -/
theorem verifyV4_of_verify {r : Enr} {q : Point} {rr ss : Fn} {content : ByteArray}
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes q.encodeCompressed))
    (hc : Serialization.Rlp.encode r.content = .ok content)
    (hsig : r.signature = ⟨(toBytesBE 32 rr.val ++ toBytesBE 32 ss.val).toArray⟩)
    (hv : Ecdsa.verify q (Hash.Keccak.keccak256 content) rr.val ss.val = true) :
    verifyV4 r = true := by
  -- ECDSA rejects the point at infinity and points off the curve, so the key decodes.
  have hinf : q ≠ .infinity := fun h => by
    have h0 : Ecdsa.verify .infinity (Hash.Keccak.keccak256 content) rr.val ss.val = false :=
      Ecdsa.verify_infinity _ _ _
    rw [h, h0] at hv
    cases hv
  have hcurve : q.isOnCurve = true := by
    cases hq : q.isOnCurve
    · have h0 : Ecdsa.verify q (Hash.Keccak.keccak256 content) rr.val ss.val = false :=
        Ecdsa.verify_of_not_isOnCurve hq _ _ _
      rw [h0] at hv
      cases hv
    · rfl
  have hlr := length_toBytesBE 32 rr.val
  have hls := length_toBytesBE 32 ss.val
  have hmod (x : Fn) : x.val % 256 ^ 32 = x.val :=
    Nat.mod_eq_of_lt (lt_trans x.isLt (by decide : Fn.modulus < 256 ^ 32))
  refine verifyV4_eq_true_iff.mpr ⟨q, content, publicKeyV4_of_get hcurve hinf hid hkey, hc,
    by rw [hsig]; simp [ByteArray.size, hlr, hls], ?_⟩
  have hlist : r.signature.data.toList = toBytesBE 32 rr.val ++ toBytesBE 32 ss.val := by
    rw [hsig]
  rw [hlist, List.take_left' hlr, List.drop_left' hlr, ofBytesBE_toBytesBE,
    ofBytesBE_toBytesBE, hmod, hmod]
  exact hv

/-- A record verifies when its signature is the deterministic one from its private key `sk`.

Its `secp256k1` pair holds the compressed form of `sk G`.

The nonce is that of RFC 6979, and `s` is low, as EIP-2 asks.

The signature is `r` then `s`, each in 32 big-endian bytes, without the recovery ID.

It signs the Keccak-256 hash of the RLP encoding of the content. -/
theorem verifyV4_of_sign {r : Enr} {sk rr ss : Fn} {odd : Bool} {content : ByteArray}
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes (Point.mul sk Point.generator).encodeCompressed))
    (hc : Serialization.Rlp.encode r.content = .ok content)
    (hsign : Ecdsa.sign sk (Hash.Keccak.keccak256 content) = .ok (rr, ss, odd))
    (hsig : r.signature = ⟨(toBytesBE 32 rr.val ++ toBytesBE 32 ss.val).toArray⟩) :
    verifyV4 r = true :=
  verifyV4_of_verify hid hkey hc hsig (Ecdsa.verify_sign_rfc6979 hsign)

end EthLib.Networking.Enr
