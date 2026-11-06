module

public import EthLib.Networking.Enr.V4
public import EthLib.Cryptography.Proofs.Secp256k1.Sign
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding

/-!
# Proofs: the "v4" identity scheme

A record signed with the private key of its `secp256k1` pair verifies.

The public key of a record is the point that its compressed `secp256k1` value encodes, when the
`id` pair is `v4`.

A record that verifies has a public key.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Serialization.Rlp

/-- The public key of a record whose `id` is `v4` and whose `secp256k1` value is the compressed
form of a point on the curve other than infinity is that point. -/
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

/-- A record that verifies has a public key. -/
theorem publicKeyV4_ok_of_verifyV4 {r : Enr} (h : verifyV4 r = true) :
    ∃ q, r.publicKeyV4 = .ok q := by
  unfold verifyV4 at h
  split at h
  · rename_i q _ hq _
    exact ⟨q, hq⟩
  · cases h

/-- Signing the content of a record with the private key `sk` of its `secp256k1` pair makes the
record verify.

The signature is `r || s`, each in 32 bytes, from the signing operation of SEC 1 v2 §4.1.3 with
the Keccak-256 hash of the RLP content. -/
theorem verifyV4_of_sign {r : Enr} {sk rr ss : Fn} {odd : Bool} {content : ByteArray}
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes (Point.mul sk Point.generator).encodeCompressed))
    (hc : Serialization.Rlp.encode r.content = .ok content)
    (hsign : Ecdsa.sign sk (Hash.Keccak.keccak256 content) = .ok (rr, ss, odd))
    (hsig : r.signature = ⟨(toBytesBE 32 rr.val ++ toBytesBE 32 ss.val).toArray⟩) :
    verifyV4 r = true := by
  have hv := Ecdsa.verify_sign_rfc6979 hsign
  have hinf : Point.mul sk Point.generator ≠ .infinity := fun h => by
    have h0 : Ecdsa.verify .infinity (Hash.Keccak.keccak256 content) rr.val ss.val = false :=
      Ecdsa.verify_infinity _ _ _
    rw [h, h0] at hv
    cases hv
  have hcurve : (Point.mul sk Point.generator).isOnCurve = true := by
    cases hq : (Point.mul sk Point.generator).isOnCurve
    · have h0 : Ecdsa.verify (Point.mul sk Point.generator) (Hash.Keccak.keccak256 content)
          rr.val ss.val = false := Ecdsa.verify_of_not_isOnCurve hq _ _ _
      rw [h0] at hv
      cases hv
    · rfl
  have hlr := length_toBytesBE 32 rr.val
  have hls := length_toBytesBE 32 ss.val
  have hmod (x : Fn) : x.val % 256 ^ 32 = x.val :=
    Nat.mod_eq_of_lt (lt_trans x.isLt (by decide : Fn.modulus < 256 ^ 32))
  have hpk := publicKeyV4_of_get hcurve hinf hid hkey
  unfold verifyV4
  rw [hpk, hc]
  have hsz : r.signature.size = 64 := by
    rw [hsig]; simp [ByteArray.size, hlr, hls]
  have hlist : r.signature.data.toList = toBytesBE 32 rr.val ++ toBytesBE 32 ss.val := by
    rw [hsig]
  dsimp only
  rw [ite_eq_left hsz]
  rw [hlist, List.take_left' hlr, List.drop_left' hlr, ofBytesBE_toBytesBE,
    ofBytesBE_toBytesBE, hmod, hmod]
  exact hv

end EthLib.Networking.Enr
