module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Cryptography.Proofs.Hash.Hkdf
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding
public import EthLib.Cryptography.Proofs.Secp256k1.Sign
public import EthLib.Networking.Discv5.Identity

/-!
# `Networking.Proofs.Discv5.Identity`

Properties of the node distance and of the "v4" handshake cryptography of discv5.

- The distance and the logarithmic distance are symmetric.
- Each is 0 exactly for equal IDs, and the logarithmic distance is at most 256.
- The key derivation always succeeds, with two keys of 16 bytes.
- An ID signature verifies under the public key of its signer.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Discv5.Identity

open EthLib.Networking.Discv5
open EthLib.Cryptography.Secp256k1

/-! ## Distance -/

/-- The distance is symmetric. -/
theorem distance_comm (a b : NodeId) : distance a b = distance b a :=
  Nat.xor_comm _ _

/-- Two IDs of 32 bytes with one big-endian value are equal. -/
theorem eq_of_bytesToNat_eq {a b : NodeId}
    (h : Base.bytesToNat a.toList = Base.bytesToNat b.toList) : a = b := by
  have ha := Base.natToBytes_bytesToNat a.toList
  have hb := Base.natToBytes_bytesToNat b.toList
  simp only [Vector.length_toList] at ha hb
  exact Vector.toList_inj.mp (ha.symm.trans (h ▸ hb))

/-- The distance is 0 exactly between equal IDs. -/
theorem distance_eq_zero_iff {a b : NodeId} : distance a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply eq_of_bytesToNat_eq
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (·.testBit i) h
    simp only [distance, Nat.testBit_xor, Nat.zero_testBit] at this
    revert this
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> simp
  · rintro rfl
    exact Nat.xor_self _

/-- The distance is below 2^256. -/
theorem distance_lt (a b : NodeId) : distance a b < 2 ^ 256 := by
  have ha := Base.bytesToNat_lt a.toList
  have hb := Base.bytesToNat_lt b.toList
  simp only [Vector.length_toList] at ha hb
  exact Nat.xor_lt_two_pow (by simpa [Nat.pow_mul] using ha) (by simpa [Nat.pow_mul] using hb)

/-- The logarithmic distance is symmetric. -/
theorem logDistance_comm (a b : NodeId) : logDistance a b = logDistance b a := by
  simp only [logDistance, distance_comm a b]

/-- The logarithmic distance is 0 exactly between equal IDs. -/
theorem logDistance_eq_zero_iff {a b : NodeId} : logDistance a b = 0 ↔ a = b := by
  simp only [logDistance]
  split
  · exact ⟨fun _ => distance_eq_zero_iff.mp ‹_›, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (Nat.succ_ne_zero _),
      fun h => absurd (distance_eq_zero_iff.mpr h) ‹_›⟩

/-- The logarithmic distance is at most 256. -/
theorem logDistance_le (a b : NodeId) : logDistance a b ≤ 256 := by
  simp only [logDistance]
  split
  · omega
  · have := (Nat.log2_lt ‹_›).mpr (distance_lt a b)
    omega

/-! ## Key derivation -/

/-- The key derivation succeeds, with an initiator key and a recipient key of 16 bytes each. -/
theorem deriveKeys_ok (secret challengeData : ByteArray) (nodeIdA nodeIdB : NodeId) :
    ∃ keys, deriveKeys secret challengeData nodeIdA nodeIdB = .ok keys ∧
      keys.initiatorKey.size = 16 ∧ keys.recipientKey.size = 16 := by
  unfold deriveKeys
  -- HKDF accepts an output of 32 bytes, and returns exactly that many.
  obtain ⟨okm, hk, hs⟩ := Cryptography.Hash.Hkdf.hkdf_ok
    (salt := challengeData) (ikm := secret)
    (info := asciiBytes "discovery v5 key agreement" ++ ⟨nodeIdA.toArray⟩ ++ ⟨nodeIdB.toArray⟩)
    (length := 32) (by simp [Cryptography.Hash.Hkdf.HASH_LEN])
  refine ⟨⟨okm.extract 0 16, okm.extract 16 32⟩, by simp only [hk]; rfl, ?_, ?_⟩ <;>
    simp only [ByteArray.size_extract, hs] <;> omega

/-! ## ID signatures -/

/-- An ID signature from signing verifies under the signer's public key `sk G`. -/
theorem idVerify_idSign {sk : Fn} {challengeData ephemeralPubkey signature : ByteArray}
    {nodeIdB : NodeId} (h : idSign sk challengeData ephemeralPubkey nodeIdB = .ok signature) :
    idVerify (Point.mul sk Point.generator) challengeData ephemeralPubkey nodeIdB signature =
      true := by
  unfold idSign at h
  generalize hs :
    Ecdsa.sign sk (idSignatureHash challengeData ephemeralPubkey nodeIdB) = result at h
  cases result with
  | error e => simp [bind, Except.bind] at h
  | ok rso =>
    obtain ⟨r, s, odd⟩ := rso
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hv := Ecdsa.verify_sign_rfc6979 hs
    have hr := length_toBytesBE 32 r.val
    have hs' := length_toBytesBE 32 s.val
    simp only [idVerify, Bool.and_eq_true, beq_iff_eq]
    refine ⟨by simp [ByteArray.size, hr, hs'], ?_⟩
    simp only [List.take_left' hr, List.drop_left' hr, bytesToNat_toBytesBE]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans s.isLt (by decide))]
    exact hv

end EthLib.Networking.Proofs.Discv5.Identity
