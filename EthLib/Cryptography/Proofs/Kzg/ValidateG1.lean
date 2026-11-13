module

public import EthLib.Cryptography.Kzg.Core
public import EthLib.Cryptography.Proofs.Bls.KeyValidate

/-!
# Proofs: validation of KZG points in `G1`

KZG validation is key validation that also accepts the point at infinity.

So it accepts exactly the encodings of the points of order dividing `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 Fr)
open EthLib.Cryptography.Kzg.Constants

/-- The encoding of the point at infinity decodes to the zero triple. -/
theorem uncompress_G1_POINT_AT_INFINITY :
    G1.uncompress ⟨G1_POINT_AT_INFINITY.toArray⟩ = .ok G1.zero := by
  change G1.uncompress G1.infinityBytes = .ok G1.zero
  exact G1.uncompress_infinityBytes

/-- KZG validation accepts exactly the decodable points of order dividing `r`. -/
theorem validateKzgG1Point_eq_ok_iff {b : Bytes48} {P : G1} :
    validateKzgG1Point b = .ok P ↔
      G1.uncompress ⟨b.toArray⟩ = .ok P ∧ Fr.modulus • G1.toPoint P = 0 := by
  unfold validateKzgG1Point
  by_cases hb : (b == G1_POINT_AT_INFINITY) = true
  · rw [ite_eq_left hb, beq_iff_eq.mp hb, uncompress_G1_POINT_AT_INFINITY]
    constructor
    · intro h
      cases h
      exact ⟨rfl, by rw [G1.toPoint_zero]; exact nsmul_zero _⟩
    · intro h
      exact (Except.ok.inj h.1).symm ▸ rfl
  · rw [ite_eq_right hb]
    -- Away from the encoding of infinity, a decoded point of order dividing `r` is nonzero.
    have key : G1.keyValidatePoint ⟨b.toArray⟩ = .ok P ↔
        G1.uncompress ⟨b.toArray⟩ = .ok P ∧ Fr.modulus • G1.toPoint P = 0 := by
      rw [G1.keyValidatePoint_eq_ok_iff]
      refine ⟨fun h => ⟨h.1, h.2.2.2⟩, fun ⟨hu, hr⟩ => ⟨hu, G1.uncompress_valid hu, ?_, hr⟩⟩
      intro h0
      have hinf := (G1.isInfinity_eq_true_iff_toPoint_eq_zero (G1.uncompress_valid hu)).mpr h0
      have hc := G1.compress_uncompress hu
      unfold G1.compress at hc
      simp only [Id.run, hinf, ite_true] at hc
      have hdata := (congrArg ByteArray.data hc).symm.trans rfl
      exact hb (beq_iff_eq.mpr (Vector.toArray_inj.mp hdata))
    rw [← key]
    cases G1.keyValidatePoint ⟨b.toArray⟩ with
    | error e => exact iff_of_false (fun h => by cases h) (fun h => by cases h)
    | ok q => exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩

/-- Bytes that pass KZG validation decode to a point of the subgroup. -/
theorem exists_validateKzgG1Point_of_validateKzgG1 {b : Bytes48} (h : validateKzgG1 b = true) :
    ∃ P, validateKzgG1Point b = .ok P := by
  unfold validateKzgG1 at h
  unfold validateKzgG1Point
  by_cases hb : (b == G1_POINT_AT_INFINITY) = true
  · exact ⟨_, ite_eq_left hb⟩
  · rw [ite_eq_right hb] at h ⊢
    cases hk : G1.keyValidatePoint ⟨b.toArray⟩ with
    | error e =>
      simp [G1.keyValidate, hk, bind, Except.bind, Except.isOk, Except.toBool] at h
    | ok q => exact ⟨q, rfl⟩

/-- Bytes that decode to a point of the subgroup pass KZG validation. -/
theorem validateKzgG1_of_validateKzgG1Point {b : Bytes48} {P : G1}
    (h : validateKzgG1Point b = .ok P) : validateKzgG1 b = true := by
  unfold validateKzgG1Point at h
  unfold validateKzgG1
  by_cases hb : (b == G1_POINT_AT_INFINITY) = true
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb] at h ⊢
    cases hk : G1.keyValidatePoint ⟨b.toArray⟩ with
    | error e => rw [hk] at h; cases h
    | ok q =>
      simp only [G1.keyValidate, hk, bind, Except.bind, Except.isOk, Except.toBool]
      rfl

/-- Bytes that decode to a point of the subgroup decompress to that point. -/
theorem uncompressG1_of_validateKzgG1Point {b : Bytes48} {P : G1}
    (h : validateKzgG1Point b = .ok P) : uncompressG1 b = .ok P := by
  unfold uncompressG1
  rw [(validateKzgG1Point_eq_ok_iff.mp h).1]
  rfl

/-! ## The conversions of EIP-4844

The conversion of a commitment or a proof validates its bytes and returns them unchanged.

The verifiers then decode the bytes, as EIP-4844 does.

The theorems below relate each conversion to KZG validation.
-/

/-- Bytes that decode to a point of the subgroup convert to a commitment, unchanged. -/
theorem bytesToKzgCommitment_of_validateKzgG1Point {b : Bytes48} {P : G1}
    (h : validateKzgG1Point b = .ok P) : bytesToKzgCommitment b = .ok b := by
  rw [bytesToKzgCommitment, ite_eq_left (validateKzgG1_of_validateKzgG1Point h)]

/-- Bytes that decode to a point of the subgroup convert to a proof, unchanged. -/
theorem bytesToKzgProof_of_validateKzgG1Point {b : Bytes48} {P : G1}
    (h : validateKzgG1Point b = .ok P) : bytesToKzgProof b = .ok b := by
  rw [bytesToKzgProof, ite_eq_left (validateKzgG1_of_validateKzgG1Point h)]

/-- Bytes that do not decode to a point of the subgroup are rejected as a commitment. -/
theorem bytesToKzgCommitment_of_validateKzgG1Point_error {b : Bytes48} {e : KzgError}
    (h : validateKzgG1Point b = .error e) :
    bytesToKzgCommitment b = .error (.invalidCommitment none) := by
  -- Valid bytes would decode to a point, and `h` says that they do not.
  have hv : validateKzgG1 b ≠ true := fun hv => by
    obtain ⟨P, hP⟩ := exists_validateKzgG1Point_of_validateKzgG1 hv
    rw [hP] at h
    cases h
  rw [bytesToKzgCommitment, ite_eq_right hv]

/-- Bytes that do not decode to a point of the subgroup are rejected as a proof. -/
theorem bytesToKzgProof_of_validateKzgG1Point_error {b : Bytes48} {e : KzgError}
    (h : validateKzgG1Point b = .error e) :
    bytesToKzgProof b = .error (.invalidProof none) := by
  -- Valid bytes would decode to a point, and `h` says that they do not.
  have hv : validateKzgG1 b ≠ true := fun hv => by
    obtain ⟨P, hP⟩ := exists_validateKzgG1Point_of_validateKzgG1 hv
    rw [hP] at h
    cases h
  rw [bytesToKzgProof, ite_eq_right hv]

/-- A commitment that converts and then decodes is the input bytes, and validation gives its point.

EIP-4844 gets the point of a commitment the same way: it converts the bytes, then decodes them. -/
theorem validateKzgG1Point_of_bytesToKzgCommitment {b : Bytes48} {c : KZGCommitment} {C : G1}
    (hc : bytesToKzgCommitment b = .ok c) (hC : uncompressG1 c = .ok C) :
    c = b ∧ validateKzgG1Point b = .ok C := by
  unfold bytesToKzgCommitment at hc
  split at hc
  · rename_i hv
    cases hc
    -- Valid bytes decode to a point of the subgroup, and decompression returns that same point.
    obtain ⟨Q, hQ⟩ := exists_validateKzgG1Point_of_validateKzgG1 hv
    rw [uncompressG1_of_validateKzgG1Point hQ] at hC
    cases hC
    exact ⟨rfl, hQ⟩
  · cases hc

/-- A proof that converts and then decodes is the input bytes, and validation gives its point.

EIP-4844 gets the point of a proof the same way: it converts the bytes, then decodes them. -/
theorem validateKzgG1Point_of_bytesToKzgProof {b : Bytes48} {p : KZGProof} {P : G1}
    (hp : bytesToKzgProof b = .ok p) (hP : uncompressG1 p = .ok P) :
    p = b ∧ validateKzgG1Point b = .ok P := by
  unfold bytesToKzgProof at hp
  split at hp
  · rename_i hv
    cases hp
    -- Valid bytes decode to a point of the subgroup, and decompression returns that same point.
    obtain ⟨Q, hQ⟩ := exists_validateKzgG1Point_of_validateKzgG1 hv
    rw [uncompressG1_of_validateKzgG1Point hQ] at hP
    cases hP
    exact ⟨rfl, hQ⟩
  · cases hp

end EthLib.Cryptography.Kzg
