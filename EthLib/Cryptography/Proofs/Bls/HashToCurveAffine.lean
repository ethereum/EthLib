module

public import EthLib.Cryptography.Proofs.Bls.MapToCurve
public import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity
public import EthLib.Cryptography.Proofs.Bls.PairingCongr

/-!
# Proofs: the hash and the map to `G2` give the points of RFC 9380 as written

Source: RFC 9380 §3, §6.6.2, §6.6.3, Appendix E.3 and Appendix F.2.

The specification maps to the curve in Jacobian coordinates, by Appendix F.2 and Appendix G.1.

Here the references are the same maps written as §6.6.2 and Appendix E.3 give them.

Both give valid points of `G2` that are the same group element.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

/-! ## The hash with the maps as written -/

namespace Affine

/-- The hash to curve of [RFC 9380 §3][h2c], with the maps of §6.6.2 and Appendix E.3 as written.

It is the reference for the hash of the specification, which computes the same point.

[h2c]: https://www.rfc-editor.org/rfc/rfc9380#section-3
-/
def hashToG2 {F : Type} [BaseField F] (msg dst : ByteArray) : Except BlsError (G2 F) := do
  -- Step 1: `u` is the pair of elements of `Fp2` that the hash to the field gives for `msg`.
  let us ← hashToFieldFp2 msg dst 2
  -- Steps 2 and 3, first half: the simplified SWU map of `u[0]` and `u[1]` to `E'`.
  let (x0, y0) ← Affine.simpleSwu us[0]
  let (x1, y1) ← Affine.simpleSwu us[1]
  -- Steps 2 and 3, second half: `Q0` and `Q1` are the images on `E` by the 3-isogeny.
  --
  -- Step 4: `R = Q0 + Q1`.
  --
  -- Steps 5 and 6: the output `P` is `R` with its cofactor cleared.
  return clearCofactor (G2.add (Affine.isoMapG2 x0 y0) (Affine.isoMapG2 x1 y1))

end Affine

/-- The hash to G2 gives the point of the hash with the maps of RFC 9380 as written. -/
theorem hashToG2_eq_affine (msg dst : ByteArray) :
    ∃ P Q, hashToG2 msg dst = .ok P ∧ Affine.hashToG2 msg dst = .ok Q ∧
      G2.Valid P ∧ G2.Valid Q ∧ G2.toPoint P = G2.toPoint Q := by
  obtain ⟨us, hus⟩ := hashToFieldFp2_two_ok msg dst
  obtain ⟨⟨x0, y0⟩, h0, e0⟩ := toPoint_isoMapG2_simpleSwu us[0]
  obtain ⟨⟨x1, y1⟩, h1, e1⟩ := toPoint_isoMapG2_simpleSwu us[1]
  have v0 := simpleSwu_isoMapG2_valid us[0]
  have v1 := simpleSwu_isoMapG2_valid us[1]
  have w0 := Affine.simpleSwu_isoMapG2_valid h0
  have w1 := Affine.simpleSwu_isoMapG2_valid h1
  refine ⟨_, _, ?_, ?_, clearCofactor_valid (G2.valid_add v0 v1),
    clearCofactor_valid (G2.valid_add w0 w1), ?_⟩
  · rw [hashToG2, hus, Base.ok_bind]
    rfl
  · rw [Affine.hashToG2, hus, Base.ok_bind, h0, Base.ok_bind, h1]
    rfl
  · rw [toPoint_clearCofactor (G2.valid_add v0 v1), toPoint_clearCofactor (G2.valid_add w0 w1),
      G2.toPoint_add v0 v1, G2.toPoint_add w0 w1, e0, e1]

/-- The hash to G2 gives the affine coordinates of the hash with the maps as written.

So the bytes of the two encodings agree. -/
theorem hashToG2_toAffine_eq_affine (msg dst : ByteArray) :
    ∃ P Q : G2, hashToG2 msg dst = .ok P ∧ Affine.hashToG2 msg dst = .ok Q ∧
      P.isInfinity = Q.isInfinity ∧ P.toAffine = Q.toAffine := by
  obtain ⟨P, Q, hP, hQ, vP, vQ, e⟩ := hashToG2_eq_affine msg dst
  exact ⟨P, Q, hP, hQ, G2.toAffine_congr vP vQ e⟩

end EthLib.Cryptography.Bls.HashToCurve

namespace EthLib.Cryptography.Bls.MapToCurve

open EthLib.Cryptography.Bls.HashToCurve

namespace Affine

/-- The map to `G2` with the maps of RFC 9380 §6.6.2 and Appendix E.3 as written.

It is the reference for the map of the specification, which computes the same point. -/
def mapToG2 {F : Type} [BaseField F] (u : Fp2 F) : Except BlsError (G2 F) := do
  -- §6.6.3 step 1: `(x', y')` is the image of `u` by the simplified SWU map, a point of `E'`.
  let (xp, yp) ← HashToCurve.Affine.simpleSwu u
  -- Step 2: `(x, y)` is the image of `(x', y')` by the isogeny, a point of `E`.
  --
  -- Step 3 returns `(x, y)`; the field-to-curve document of EIP-2537 then clears the cofactor.
  return HashToCurve.clearCofactor (HashToCurve.Affine.isoMapG2 xp yp)

end Affine

/-- The map to `G2` gives the point of the map with the maps of RFC 9380 as written. -/
theorem mapToG2_eq_affine (u : Fp2) :
    ∃ P Q, mapToG2 u = .ok P ∧ Affine.mapToG2 u = .ok Q ∧
      G2.Valid P ∧ G2.Valid Q ∧ G2.toPoint P = G2.toPoint Q := by
  obtain ⟨⟨x, y⟩, h0, e0⟩ := toPoint_isoMapG2_simpleSwu u
  have v := simpleSwu_isoMapG2_valid u
  have w := Affine.simpleSwu_isoMapG2_valid h0
  refine ⟨_, _, rfl, ?_, clearCofactor_valid v, clearCofactor_valid w, ?_⟩
  · rw [Affine.mapToG2, h0]
    rfl
  · rw [toPoint_clearCofactor v, toPoint_clearCofactor w, e0]

/-- The map to `G2` gives the affine coordinates of the map with the maps as written. -/
theorem mapToG2_toAffine_eq_affine (u : Fp2) :
    ∃ P Q, mapToG2 u = .ok P ∧ Affine.mapToG2 u = .ok Q ∧
      P.isInfinity = Q.isInfinity ∧ P.toAffine = Q.toAffine := by
  obtain ⟨P, Q, hP, hQ, vP, vQ, e⟩ := mapToG2_eq_affine u
  exact ⟨P, Q, hP, hQ, G2.toAffine_congr vP vQ e⟩

end EthLib.Cryptography.Bls.MapToCurve
