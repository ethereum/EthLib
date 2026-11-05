module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Glv
public import EthLib.Cryptography.Proofs.Kzg.FftG1

/-!
# Proofs: a kernel check of one small transform of points

The FFT of `G1` multiplies points by roots of unity and adds them, in a recursion on halves.

Here the same recursion runs on coordinates as naturals, with the operations of the torsion check.

So the kernel can run it on concrete points, without reducing `Fp` or `Fr`.

Each product by a root splits the root in two halves of 128 bits, as in `Glv`.

The split gives other coordinates than the products of the FFT of `G1`, but the same points.

The check takes affine inputs, a scalar for each input, the roots, and affine outputs.

It multiplies each input by its scalar, runs the transform, and compares the results.

The comparison is projective, so the check never inverts a coordinate.

If the check passes, each output point is the sum that the transform defines.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls
open scoped EthLib.Cryptography.Bls.Fr
open EthLib.Cryptography.Bls.G1.TorsionCheck (Coords coords)

/-- The FFT of `G1` on coordinates, with the products split in two halves. -/
def fftNat : (k : Nat) → Vector Coords (2 ^ k) → Vector Nat (2 ^ k) → Vector Coords (2 ^ k)
  | 0, vals, _ => vals
  | k + 1, vals, roots =>
    let halfRoots := everyOther roots 0
    let l := fftNat k (everyOther vals 0) halfRoots
    let r := fftNat k (everyOther vals 1) halfRoots
    let t := Vector.ofFn (n := 2 ^ k) fun i => glvNat r[i] (roots[i.val]'(by
      have hlt := i.isLt
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
      omega))
    Vector.ofFn fun i =>
      if h : i.val < 2 ^ k then G1.TorsionCheck.add l[i.val] t[i.val]
      else
        have hi : i.val - 2 ^ k < 2 ^ k := by
          have hlt := i.isLt
          have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
          omega
        G1.TorsionCheck.add l[i.val - 2 ^ k] (G1.TorsionCheck.neg t[i.val - 2 ^ k])

/-- The same transform on points of `G1`, step for step. -/
def fftGlv : (k : Nat) → Vector G1 (2 ^ k) → Vector Nat (2 ^ k) → Vector G1 (2 ^ k)
  | 0, vals, _ => vals
  | k + 1, vals, roots =>
    let halfRoots := everyOther roots 0
    let l := fftGlv k (everyOther vals 0) halfRoots
    let r := fftGlv k (everyOther vals 1) halfRoots
    let t := Vector.ofFn (n := 2 ^ k) fun i => glvMul r[i] (roots[i.val]'(by
      have hlt := i.isLt
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
      omega))
    Vector.ofFn fun i =>
      if h : i.val < 2 ^ k then G1.add l[i.val] t[i.val]
      else
        have hi : i.val - 2 ^ k < 2 ^ k := by
          have hlt := i.isLt
          have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
          omega
        G1.add l[i.val - 2 ^ k] (G1.neg t[i.val - 2 ^ k])

private theorem everyOther_map {α β : Type} {k : Nat} (f : α → β) (xs : Vector α (2 ^ (k + 1)))
    (s : Fin 2) : everyOther (xs.map f) s = (everyOther xs s).map f := by
  ext i hi
  simp [everyOther]

/-- The transform on points has the coordinates that the transform on naturals computes. -/
theorem map_coords_fftGlv (k : Nat) (vals : Vector G1 (2 ^ k)) (roots : Vector Nat (2 ^ k)) :
    (fftGlv k vals roots).map coords = fftNat k (vals.map coords) roots := by
  have hneg (q : G1) : coords (G1.neg q) = G1.TorsionCheck.neg (coords q) := rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fftGlv, fftNat]
    simp only [everyOther_map, ← ih]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
    split
    · simp only [G1.TorsionCheck.coords_add, coords_glvMul]
    · simp only [G1.TorsionCheck.coords_add, hneg, coords_glvMul]

/-! ## The same points as the FFT of `G1` -/

/-- `Q` is a valid point equal to the valid point `P`, of order dividing `r`. -/
def SamePoint (P Q : G1) : Prop :=
  G1.Valid P ∧ G1.Valid Q ∧ Fr.modulus • G1.toPoint P = 0 ∧ G1.toPoint Q = G1.toPoint P

private theorem SamePoint.add {P Q P' Q' : G1} (h : SamePoint P Q) (h' : SamePoint P' Q') :
    SamePoint (G1.add P P') (G1.add Q Q') := by
  obtain ⟨hP, hQ, ht, he⟩ := h
  obtain ⟨hP', hQ', ht', he'⟩ := h'
  refine ⟨G1.valid_add hP hP', G1.valid_add hQ hQ', ?_, ?_⟩
  · rw [G1.toPoint_add hP hP', nsmul_add, ht, ht', add_zero]
  · rw [G1.toPoint_add hQ hQ', G1.toPoint_add hP hP', he, he']

private theorem SamePoint.neg {P Q : G1} (h : SamePoint P Q) : SamePoint (G1.neg P) (G1.neg Q) := by
  obtain ⟨hP, hQ, ht, he⟩ := h
  refine ⟨G1.valid_neg hP, G1.valid_neg hQ, ?_, ?_⟩
  · rw [G1.toPoint_neg hP, neg_nsmul, ht, neg_zero]
  · rw [G1.toPoint_neg hQ, G1.toPoint_neg hP, he]

private theorem SamePoint.mul {P Q : G1} (h : SamePoint P Q) (s : Fr) :
    SamePoint (G1.mul P s) (glvMul Q s.val) := by
  obtain ⟨hP, hQ, ht, he⟩ := h
  obtain ⟨hv, hpt⟩ := glvMul_spec hQ (by rw [he, ht]) (Fr.val_lt s)
  refine ⟨G1.valid_mul hP s, hv, ?_, ?_⟩
  · rw [G1.toPoint_mul hP, smul_comm, ht, nsmul_zero]
  · rw [hpt, G1.toPoint_mul hP, he]

/-- On points of order dividing `r`, the transform gives the points of the FFT of `G1`. -/
theorem samePoint_fftGlv (k : Nat) {vals vals' : Vector G1 (2 ^ k)} (roots : Vector Fr (2 ^ k))
    (h : ∀ (i : Nat) (hi : i < 2 ^ k), SamePoint vals[i] vals'[i]) (i : Nat) (hi : i < 2 ^ k) :
    SamePoint (fftG1Vector k vals roots)[i] (fftGlv k vals' (roots.map Fr.val))[i] := by
  have hget {α : Type} (f : Unit → α) : (Task.spawn f).get = f () := rfl
  induction k generalizing i with
  | zero => exact h i hi
  | succ k ih =>
    have hl := ih (vals := everyOther vals 0) (vals' := everyOther vals' 0) (everyOther roots 0)
      (fun j hj => by simpa [everyOther] using h (2 * j) (by rw [Nat.pow_succ]; omega))
    have hr := ih (vals := everyOther vals 1) (vals' := everyOther vals' 1) (everyOther roots 0)
      (fun j hj => by simpa [everyOther] using h (1 + 2 * j) (by rw [Nat.pow_succ]; omega))
    rw [fftG1Vector, fftGlv]
    simp only [everyOther_map, Vector.getElem_ofFn, Vector.getElem_map, hget]
    split
    · exact (hl i ‹_›).add ((hr i ‹_›).mul _)
    · exact (hl _ _).add ((hr _ _).mul _).neg

/-! ## The check -/

/-- A test of every element reads the same on a vector and on its list.

The kernel computes the test on the list, by structural recursion. -/
theorem toList_all {α : Type} {n : Nat} (xs : Vector α n) (p : α → Bool) :
    xs.toList.all p = xs.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, Vector.all_eq_true]
  constructor
  · intro h i hi
    exact h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    exact h i hi

/-- The check of one transform: each pair is on the curve, and each output matches.

Input `i` is first multiplied by its scalar `tw[i]`. -/
def dftCheck {k : Nat} (ins : Vector (Nat × Nat) (2 ^ k)) (tw roots : Vector Nat (2 ^ k))
    (outs : Vector (Nat × Nat) (2 ^ k)) : Bool :=
  let res := fftNat k
    (Vector.ofFn fun (i : Fin (2 ^ k)) => glvNat (ins[i].1, ins[i].2, 1) tw[i]) roots
  ins.toList.all (fun q => onCurve q.1 q.2) && outs.toList.all (fun q => onCurve q.1 q.2) &&
    (Vector.ofFn fun (i : Fin (2 ^ k)) => sameAffine res[i] outs[i].1 outs[i].2).toList.all id

/-- If the check passes, output `j` is the sum over `i` of `ω^(i j) tw[i]` times input `i`.

The roots are the powers of a primitive root `ω`, below `r`.

The scalars are below `r`, and the inputs have order dividing `r`. -/
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
  simp only [dftCheck, toList_all, Bool.and_eq_true, Vector.all_eq_true, id_eq,
    Vector.getElem_ofFn, Fin.getElem_fin] at h
  obtain ⟨⟨hin, hout⟩, hcmp⟩ := h
  -- The FFT of `G1` on the points `tw[i] • P_i` and the roots of `Fr`, and its split form.
  let rootsFr : Vector Fr (2 ^ k) := Vector.ofFn fun i => Fr.ofNat roots[i]
  let vals : Vector G1 (2 ^ k) :=
    Vector.ofFn fun i => G1.mul (affinePoint ins[i].1 ins[i].2) (Fr.ofNat tw[i])
  let vals' : Vector G1 (2 ^ k) :=
    Vector.ofFn fun i => glvMul (affinePoint ins[i].1 ins[i].2) tw[i]
  have hrv : rootsFr.map Fr.val = roots := by
    refine Vector.ext fun i hi => ?_
    simp only [rootsFr, Vector.getElem_map, Vector.getElem_ofFn, Fr.val_ofNat]
    exact Nat.mod_eq_of_lt (hroots i hi).1
  have hvv : vals'.map coords =
      Vector.ofFn fun (i : Fin (2 ^ k)) => glvNat (ins[i.val].1, ins[i.val].2, 1) tw[i.val] := by
    refine Vector.ext fun i hi => ?_
    simp only [vals', Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, coords_glvMul,
      coords_affinePoint (hin i hi)]
  have hpt (i : Nat) (hi : i < 2 ^ k) : G1.toPoint vals[i] =
      tw[i] • G1.toPoint (affinePoint ins[i].1 ins[i].2) := by
    simp only [vals, Vector.getElem_ofFn, Fin.getElem_fin]
    rw [G1.toPoint_mul (valid_affinePoint (hin i hi)), Fr.val_ofNat,
      Nat.mod_eq_of_lt (htw i hi)]
  have hsame (i : Nat) (hi : i < 2 ^ k) : SamePoint vals[i] vals'[i] := by
    have hv := valid_affinePoint (hin i hi)
    obtain ⟨hv', hpt'⟩ := glvMul_spec hv (htor i hi) (htw i hi)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [vals] using G1.valid_mul hv (Fr.ofNat tw[i])
    · simpa [vals'] using hv'
    · rw [hpt i hi, smul_comm, htor i hi, nsmul_zero]
    · rw [hpt i hi]
      simpa [vals'] using hpt'
  have hres := map_coords_fftGlv k vals' roots
  rw [hvv] at hres
  have hvalid (i : Nat) (hi : i < 2 ^ k) : G1.Valid vals.toArray[i]! := by
    rw [getElem!_pos vals.toArray i (by simpa using hi)]
    exact (hsame i hi).1
  have htor' (i : Nat) (hi : i < 2 ^ k) : Fr.modulus • G1.toPoint vals.toArray[i]! = 0 := by
    rw [getElem!_pos vals.toArray i (by simpa using hi)]
    exact (hsame i hi).2.2.1
  have hroots' (i : Nat) (hi : i < 2 ^ k) : rootsFr.toArray[i]! = ω ^ i := by
    rw [getElem!_pos rootsFr.toArray i (by simpa using hi)]
    simpa [rootsFr] using (hroots i hi).2
  have hfft := toPoint_getElem!_fftG1 hω vals.toArray rootsFr.toArray (by simp) (by simp)
    hroots' hvalid htor' j.val j.isLt
  rw [fftG1_eq_fftG1Vector (k := k) _ _ (by simp) (by simp)] at hfft
  -- The output point is the point that the split transform computes, and that of the FFT.
  have heq : G1.toPoint (fftGlv k vals' roots)[j] =
      G1.toPoint (affinePoint outs[j].1 outs[j].2) := by
    refine toPoint_eq_of_sameAffine (coords_affinePoint (hout j j.isLt)) ?_
    have hc := congrArg (fun v : Vector Coords (2 ^ k) => v[j.val]) hres
    simp only [Vector.getElem_map] at hc
    rw [Fin.getElem_fin, hc]
    exact hcmp j j.isLt
  have hfg := (samePoint_fftGlv k rootsFr hsame j.val j.isLt).2.2.2
  rw [hrv] at hfg
  rw [← heq, Fin.getElem_fin, hfg, Vector.getElem_eq_getElem!_toArray]
  refine hfft.trans ((Fin.sum_univ_eq_sum_range
    (fun i => (ω ^ (i * j.val)).val • G1.toPoint vals.toArray[i]!) (2 ^ k)).symm.trans
    (Finset.sum_congr rfl fun i _ => ?_))
  rw [getElem!_pos vals.toArray i.val (by simp), Vector.getElem_toArray, hpt i i.isLt]
  simp only [Fin.getElem_fin]

end EthLib.Cryptography.Kzg.SetupLagrange
