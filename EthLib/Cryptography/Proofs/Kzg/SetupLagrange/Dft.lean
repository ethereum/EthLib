module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Points
public import EthLib.Cryptography.Proofs.Kzg.FftG1

/-!
# Proofs: a kernel check of one small transform of points

The FFT of `G1` multiplies points by roots of unity and adds them, in a recursion on halves.

Here the same recursion runs on coordinates as naturals, with the operations of the torsion check.

So the kernel can run it on concrete points, without reducing `Fp` or `Fr`.

The check takes affine inputs, a scalar for each input, the roots, and affine outputs.

It multiplies each input by its scalar, runs the transform, and compares the results.

The comparison is projective, so the check never inverts a coordinate.

If the check passes, each output point is the sum that the transform defines.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls
open scoped EthLib.Cryptography.Bls.Fr
open EthLib.Cryptography.Bls.G1.TorsionCheck (Coords coords mulNatAux add neg)

/-- The FFT of `G1` on coordinates, in the steps of the FFT of `G1`. -/
def fftNat : (k : Nat) → Vector Coords (2 ^ k) → Vector Nat (2 ^ k) → Vector Coords (2 ^ k)
  | 0, vals, _ => vals
  | k + 1, vals, roots =>
    let halfRoots := everyOther roots 0
    let l := fftNat k (everyOther vals 0) halfRoots
    let r := fftNat k (everyOther vals 1) halfRoots
    let t := Vector.ofFn (n := 2 ^ k) fun i => mulNatAux 256 r[i] (roots[i.val]'(by
      have hlt := i.isLt
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
      omega))
    Vector.ofFn fun i =>
      if h : i.val < 2 ^ k then add l[i.val] t[i.val]
      else
        have hi : i.val - 2 ^ k < 2 ^ k := by
          have hlt := i.isLt
          have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
          omega
        add l[i.val - 2 ^ k] (neg t[i.val - 2 ^ k])

private theorem everyOther_map {α β : Type} {k : Nat} (f : α → β) (xs : Vector α (2 ^ (k + 1)))
    (s : Fin 2) : everyOther (xs.map f) s = (everyOther xs s).map f := by
  ext i hi
  simp [everyOther]

/-- A product of `G1` by a scalar, on coordinates. -/
private theorem coords_mul (q : G1) (s : Fr) :
    coords (G1.mul q s) = mulNatAux 256 (coords q) s.val := by
  rw [G1.mul, ← G1.mulNatAux_eq 256 q s.val
    (Nat.lt_trans (Fr.val_lt s) (by decide)), G1.TorsionCheck.coords_mulNatAux]

/-- The FFT of `G1` has the coordinates that the FFT on coordinates computes. -/
theorem map_coords_fftG1Vector (k : Nat) (vals : Vector G1 (2 ^ k)) (roots : Vector Fr (2 ^ k)) :
    (fftG1Vector k vals roots).map coords = fftNat k (vals.map coords) (roots.map Fr.val) := by
  have hget {α : Type} (f : Unit → α) : (Task.spawn f).get = f () := rfl
  have hneg (q : G1) : coords (G1.neg q) = neg (coords q) := rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fftG1Vector, fftNat]
    simp only [everyOther_map, ← ih]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_map, Vector.getElem_ofFn, hget, Fin.getElem_fin]
    split
    · simp only [G1.TorsionCheck.coords_add, coords_mul]
    · simp only [G1.TorsionCheck.coords_add, hneg, coords_mul]

/-! ## The check -/

/-- The check of one transform: each pair is on the curve, and each output matches.

Input `i` is first multiplied by its scalar `tw[i]`. -/
def dftCheck {k : Nat} (ins : Vector (Nat × Nat) (2 ^ k)) (tw roots : Vector Nat (2 ^ k))
    (outs : Vector (Nat × Nat) (2 ^ k)) : Bool :=
  let res := fftNat k
    (Vector.ofFn fun (i : Fin (2 ^ k)) => mulNatAux 256 (ins[i].1, ins[i].2, 1) tw[i]) roots
  ins.all (fun q => onCurve q.1 q.2) && outs.all (fun q => onCurve q.1 q.2) &&
    (Vector.ofFn fun (i : Fin (2 ^ k)) => sameAffine res[i] outs[i].1 outs[i].2).all id

/-- If the check passes, output `j` is the sum over `i` of `ω^(i j) tw[i]` times input `i`.

The roots are the powers of a primitive root `ω`, and the inputs have order dividing `r`. -/
theorem toPoint_of_dftCheck {k : Nat} {ω : Fr} (hω : IsPrimitiveRoot ω (2 ^ k))
    {ins : Vector (Nat × Nat) (2 ^ k)} {tw roots : Vector Nat (2 ^ k)}
    {outs : Vector (Nat × Nat) (2 ^ k)} (h : dftCheck ins tw roots outs = true)
    (hroots : ∀ (i : Nat) (hi : i < 2 ^ k), roots[i] < Fr.modulus ∧ Fr.ofNat roots[i] = ω ^ i)
    (htw : ∀ (i : Nat) (hi : i < 2 ^ k), tw[i] < Fr.modulus)
    (htor : ∀ (i : Nat) (hi : i < 2 ^ k),
      Fr.modulus • G1.toPoint (affinePoint ins[i].1 ins[i].2) = 0)
    (j : Fin (2 ^ k)) :
    G1.toPoint (affinePoint outs[j].1 outs[j].2) =
      ∑ i : Fin (2 ^ k), (ω ^ (i.val * j.val)).val •
        tw[i] • G1.toPoint (affinePoint ins[i].1 ins[i].2) := by
  simp only [dftCheck, Bool.and_eq_true, Vector.all_eq_true, id_eq, Vector.getElem_ofFn,
    Fin.getElem_fin] at h
  obtain ⟨⟨hin, hout⟩, hcmp⟩ := h
  -- The same transform in `G1`, on the points `tw[i] • P_i` and the roots of `Fr`.
  let rootsFr : Vector Fr (2 ^ k) := Vector.ofFn fun i => Fr.ofNat roots[i]
  let vals : Vector G1 (2 ^ k) :=
    Vector.ofFn fun i => G1.mul (affinePoint ins[i].1 ins[i].2) (Fr.ofNat tw[i])
  have hrv : rootsFr.map Fr.val = roots := by
    refine Vector.ext fun i hi => ?_
    simp only [rootsFr, Vector.getElem_map, Vector.getElem_ofFn, Fr.val_ofNat]
    exact Nat.mod_eq_of_lt (hroots i hi).1
  have hvv : vals.map coords =
      Vector.ofFn fun (i : Fin (2 ^ k)) =>
        mulNatAux 256 (ins[i.val].1, ins[i.val].2, 1) tw[i.val] := by
    refine Vector.ext fun i hi => ?_
    simp only [vals, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, coords_mul,
      coords_affinePoint (hin i hi), Fr.val_ofNat, Nat.mod_eq_of_lt (htw i hi)]
  have hres := map_coords_fftG1Vector k vals rootsFr
  rw [hvv, hrv] at hres
  have hvalid (i : Nat) (hi : i < 2 ^ k) : G1.Valid vals.toArray[i]! := by
    rw [getElem!_pos vals.toArray i (by simpa using hi)]
    simpa [vals] using G1.valid_mul (valid_affinePoint (hin i hi)) (Fr.ofNat tw[i])
  have hpt (i : Nat) (hi : i < 2 ^ k) : G1.toPoint vals.toArray[i]! =
      tw[i] • G1.toPoint (affinePoint ins[i].1 ins[i].2) := by
    rw [getElem!_pos vals.toArray i (by simpa using hi)]
    simp only [vals, Vector.getElem_toArray, Vector.getElem_ofFn, Fin.getElem_fin]
    rw [G1.toPoint_mul (valid_affinePoint (hin i hi)), Fr.val_ofNat,
      Nat.mod_eq_of_lt (htw i hi)]
  have htor' (i : Nat) (hi : i < 2 ^ k) : Fr.modulus • G1.toPoint vals.toArray[i]! = 0 := by
    rw [hpt i hi, smul_comm, htor i hi, nsmul_zero]
  have hroots' (i : Nat) (hi : i < 2 ^ k) : rootsFr.toArray[i]! = ω ^ i := by
    rw [getElem!_pos rootsFr.toArray i (by simpa using hi)]
    simpa [rootsFr] using (hroots i hi).2
  have hfft := toPoint_getElem!_fftG1 hω vals.toArray rootsFr.toArray (by simp) (by simp)
    hroots' hvalid htor' j.val j.isLt
  rw [fftG1_eq_fftG1Vector (k := k) _ _ (by simp) (by simp)] at hfft
  -- The output point is the point that the transform computes.
  have heq : G1.toPoint (fftG1Vector k vals rootsFr)[j] =
      G1.toPoint (affinePoint outs[j].1 outs[j].2) := by
    refine toPoint_eq_of_sameAffine (coords_affinePoint (hout j j.isLt)) ?_
    have hc := congrArg (fun v : Vector Coords (2 ^ k) => v[j.val]) hres
    simp only [Vector.getElem_map] at hc
    rw [Fin.getElem_fin, hc]
    exact hcmp j j.isLt
  rw [← heq, Fin.getElem_fin, Vector.getElem_eq_getElem!_toArray]
  refine hfft.trans ((Fin.sum_univ_eq_sum_range
    (fun i => (ω ^ (i * j.val)).val • G1.toPoint vals.toArray[i]!) (2 ^ k)).symm.trans
    (Finset.sum_congr rfl fun i _ => ?_))
  rw [hpt i i.isLt]
  simp only [Fin.getElem_fin]

end EthLib.Cryptography.Kzg.SetupLagrange
