module

public import EthLib.Cryptography.Bls.MapToCurve
public import EthLib.Cryptography.Proofs.Bls.CofactorSubgroupLanding

/-!
# Proofs: the map to `G2`

The map of a field element to `G2` always succeeds.

Its output is a valid point of the subgroup of order `r`.

The source is [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), §6.6.3 and §8.8.2.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.MapToCurve

open EthLib.Cryptography.Bls.HashToCurve

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
