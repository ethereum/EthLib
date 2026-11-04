module

public import EthLib.Cryptography.Bls.MapToCurve
public import EthLib.Cryptography.Proofs.Bls.CofactorSubgroupLanding
public import EthLib.Cryptography.Proofs.Bls.G1CofactorClearing
public import EthLib.Cryptography.Proofs.Bls.MapToG1

/-!
# Proofs: the maps to `G1` and `G2`

The map of a field element to `G1` or `G2` always succeeds.

Its output is a valid point of the subgroup of order `r`.

The source is [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), §6.6.3, §8.8.1 and §8.8.2.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.MapToCurve

open EthLib.Cryptography.Bls.HashToCurve

/-- The map to `G1` succeeds on every input. -/
theorem mapToG1_ok (u : Fp) : ∃ P, mapToG1 u = .ok P := by
  obtain ⟨p, hp⟩ := simpleSwuG1_ok u
  exact ⟨_, by rw [mapToG1, hp]; rfl⟩

/-- Every output of the map to `G1` is valid and lies in the subgroup of order `r`. -/
theorem mapToG1_inSubgroup {u : Fp} {P : G1} (h : mapToG1 u = .ok P) :
    G1.Valid P ∧ G1.inSubgroup P = true := by
  unfold mapToG1 at h
  cases hp : simpleSwuG1 u with
  | error e =>
    rw [hp] at h
    cases h
  | ok p =>
    rw [hp] at h
    obtain rfl : clearCofactorG1 (isoMapG1 p.1 p.2) = P := Except.ok.inj h
    have hv := isoMapG1_valid (simpleSwuG1_curve_eq hp)
    exact ⟨G1.valid_mulNat hv _, clearCofactorG1_inSubgroup hv⟩

/-- The map to `G2` succeeds on every input. -/
theorem mapToG2_ok (u : Fp2) : ∃ P, mapToG2 u = .ok P := by
  obtain ⟨p, hp⟩ := simpleSwu_ok u
  exact ⟨_, by rw [mapToG2, hp]; rfl⟩

/-- Every output of the map to `G2` is valid and lies in the subgroup of order `r`. -/
theorem mapToG2_inSubgroup {u : Fp2} {P : G2} (h : mapToG2 u = .ok P) :
    G2.Valid P ∧ G2.inSubgroup P = true := by
  unfold mapToG2 at h
  cases hp : simpleSwu u with
  | error e =>
    rw [hp] at h
    cases h
  | ok p =>
    rw [hp] at h
    -- Injectivity avoids unfolding the field arithmetic of the output.
    obtain rfl : clearCofactor (isoMapG2 p.1 p.2) = P := Except.ok.inj h
    have hv := simpleSwu_isoMapG2_valid hp
    exact ⟨clearCofactor_valid hv, clearCofactor_inSubgroup hv⟩

end EthLib.Cryptography.Bls.MapToCurve
