module

public import EthLib.Cryptography.Proofs.Kzg.CellBatching
public import EthLib.Cryptography.Proofs.Kzg.Arsdh

/-!
# Proofs: code-binding of the PeerDAS commitment, deterministic form

This is the argument of Lemma 4 of Wagner and Zapico, ePrint 2025/1683, §3.1.

<https://eprint.iacr.org/2025/1683>

The code is Reed–Solomon: a blob is a polynomial of degree below 4096.

A cell holds its values on one of 128 cosets of 64 points.

Code-binding asks that no valid openings of one commitment disagree with every such polynomial.

Take exactly 64 cells `J` and one more cell `jx`.

Let each of them satisfy the scalar equation of a valid cell for the commitment `c`.

That is `c - I_j(τ) = w_j (τ^64 - h_j^64)`, not the acceptance of the verifier.

Let `I` interpolate the cells of `J`, on their 4096 points.

If `I` also takes the values of cell `jx`, the cells agree with a polynomial of degree below 4096.

Otherwise there are two cases.

- If `I(τ) = c`, the honest opening of cell `jx` from `I` is valid and has other values.
  The search of the cell binding then returns a bilinear strong Diffie–Hellman solution.
- If `I(τ) ≠ c`, Lemma 2 joins the openings of `J` into `c - I(τ) = φ V(τ)`.
  The commitment minus the commitment to `I`, with the joined proof, is an ARSDH solution.

Both searches read only the setup, the commitment, the cells and the proofs, not `τ`.

The paper calls them the reductions `B1` and `B2`.

The bound of Lemma 4 on the advantages is proved for games in another file.

The running times of the reductions are not formalized.

The first search uses the sign of the extended KZG paper; `isBsdhSolution_iff_sub` relates it to
the sign of ePrint 2025/1683.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial Lagrange

/-! ## Points from the setup -/

/-- The commitment to a polynomial: its first 4096 coefficients times the monomial points. -/
def commitPoly (s : TrustedSetup) (p : Fr[X]) : G1 :=
  G1.msm s.g1Monomial.toArray (Array.ofFn fun k : Fin FIELD_ELEMENTS_PER_BLOB => p.coeff k)

/-- The commitment to a polynomial of degree below 4096 represents its value at the secret.

Only the monomial points of `G1` must represent the powers of the secret. -/
theorem represents_commitPoly_of_monomial {s : TrustedSetup} {τ : Fr}
    (hm : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Represents s.g1Monomial[i] (τ ^ i.val))
    {p : Fr[X]} (hp : p.natDegree < FIELD_ELEMENTS_PER_BLOB) :
    G1.Represents (commitPoly s p) (p.eval τ) := by
  have h := G1.represents_msm (points := s.g1Monomial.toArray)
    (scalars := Array.ofFn fun k : Fin FIELD_ELEMENTS_PER_BLOB => p.coeff k)
    (a := fun j => τ ^ j) (by simp) fun j hj => by
      have hj' : j < FIELD_ELEMENTS_PER_BLOB := by simpa using hj
      rw [getElem!_pos _ j hj, Vector.getElem_toArray]
      exact hm ⟨j, hj'⟩
  rw [commitPoly]
  convert h using 1
  rw [eval_eq_sum_range' hp, Vector.size_toArray]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

/-- The commitment to a polynomial of degree below 4096 represents its value at the secret. -/
theorem represents_commitPoly {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ) {p : Fr[X]}
    (hp : p.natDegree < FIELD_ELEMENTS_PER_BLOB) : G1.Represents (commitPoly s p) (p.eval τ) :=
  represents_commitPoly_of_monomial hs.monomial_g1 hp

/-- The sum of the points `P j` times the weights `a j`, over a finite set `J` of indices. -/
def weightedSum (J : Finset Nat) (P : Nat → G1) (a : Nat → Fr) : G1 :=
  G1.msm ((J.sort (· ≤ ·)).toArray.map P) ((J.sort (· ≤ ·)).toArray.map a)

/-- A weighted sum of representatives represents the weighted sum of their scalars. -/
theorem represents_weightedSum {J : Finset Nat} {P : Nat → G1} {w : Nat → Fr}
    (hP : ∀ j ∈ J, G1.Represents (P j) (w j)) (a : Nat → Fr) :
    G1.Represents (weightedSum J P a) (∑ j ∈ J, a j * w j) := by
  have e1 : ∑ j ∈ J, a j * w j = ((J.sort (· ≤ ·)).map fun j => a j * w j).sum := by
    have h := List.sum_toFinset (fun j => a j * w j) (Finset.sort_nodup (s := J) (r := (· ≤ ·)))
    rw [Finset.sort_toFinset] at h
    exact h
  set L := J.sort (· ≤ ·)
  have h := G1.represents_msm (points := L.toArray.map P) (scalars := L.toArray.map a)
    (a := fun k => w L[k]!) (by simp) fun k hk => by
      have hk' : k < L.length := by simpa using hk
      rw [getElem!_pos _ k hk, Array.getElem_map, List.getElem_toArray,
        getElem!_pos L k hk']
      exact hP _ ((Finset.mem_sort _).mp (List.getElem_mem hk'))
  rw [weightedSum]
  convert h using 1
  have e2 : (L.map fun j => a j * w j) =
      List.ofFn fun k : Fin L.length => a L[k] * w L[k] := by
    apply List.ext_getElem <;> simp
  rw [e1, e2]
  refine List.sum_ofFn.trans ?_
  have hsz : (L.toArray.map P).size = L.length := by simp
  rw [hsz, ← Fin.sum_univ_eq_sum_range (fun k => (L.toArray.map a)[k]! * w L[k]!) L.length]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getElem!_pos _ k.val (by simp), getElem!_pos L k.val k.isLt, Array.getElem_map,
    List.getElem_toArray]
  rfl

/-! ## The interpolation of 64 cells -/

/-- The points of a set of cells below 128 are distinct. -/
theorem domainPoint_injOn_cells {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB) :
    Set.InjOn domainPoint (J.biUnion cellNodes) := domainPoint_injOn.mono fun i hi => by
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
  exact cellNodes_subset_range (hJ j hj) hij

/-- A cell has 64 nodes. -/
theorem card_cellNodes (j : Nat) : (cellNodes j).card = FIELD_ELEMENTS_PER_CELL := by
  rw [cellNodes, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

/-- A set of cells has 64 nodes per cell. -/
theorem card_biUnion_cellNodes (J : Finset Nat) :
    (J.biUnion cellNodes).card = FIELD_ELEMENTS_PER_CELL * J.card := by
  rw [Finset.card_biUnion (cellNodes_pairwiseDisjoint J)]
  simp [card_cellNodes, mul_comm]

/-- The interpolation of at most 64 cells has degree below 4096. -/
theorem natDegree_cellsInterpolant_lt {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB)
    (hJcard : J.card ≤ FIELD_ELEMENTS_PER_CELL) (ev : Nat → CosetEvals) :
    (cellsInterpolant J ev).natDegree < FIELD_ELEMENTS_PER_BLOB := by
  have h := degree_interpolate_lt (r := cellValue ev) (domainPoint_injOn_cells hJ)
  rw [card_biUnion_cellNodes] at h
  have hle : FIELD_ELEMENTS_PER_CELL * J.card ≤ FIELD_ELEMENTS_PER_BLOB :=
    (Nat.mul_le_mul_left _ hJcard).trans (by decide)
  rcases eq_or_ne (cellsInterpolant J ev) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    decide
  · rw [cellsInterpolant] at h0
    rw [cellsInterpolant, ← Nat.cast_lt (α := WithBot Nat), ← degree_eq_natDegree h0]
    exact h.trans_le (by exact_mod_cast hle)

/-- The vanishing polynomial of the points of a set of cells, at `τ`, is the product over the
cells of `τ^64 - h^64`. -/
theorem vanishingAt_cells {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB) (τ : Fr) :
    vanishingAt ((J.biUnion cellNodes).image domainPoint) τ =
      ∏ j ∈ J, (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift j ^ FIELD_ELEMENTS_PER_CELL) := by
  rw [vanishingAt, Finset.prod_image (domainPoint_injOn_cells hJ)]
  refine (eval_nodal (s := J.biUnion cellNodes) (v := domainPoint) (x := τ)).symm.trans ?_
  rw [nodal_biUnion (cellNodes_pairwiseDisjoint J), eval_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [nodal_cellNodes (hJ j hj), eval_sub, eval_pow, eval_X, eval_C]

/-! ## The searches of the reductions -/

/-- The vanishing polynomial `X^64 - h^64` of the coset of a cell. -/
noncomputable def cellVanishing (cellIndex : Nat) : Fr[X] :=
  X ^ FIELD_ELEMENTS_PER_CELL - C (cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL)

/-- The values that the interpolation of the cells of `J` takes on cell `jx`. -/
noncomputable def honestEvals (J : Finset Nat) (ev : Nat → CosetEvals) (jx : Nat) : CosetEvals :=
  Array.ofFn fun m : Fin FIELD_ELEMENTS_PER_CELL => (cellsInterpolant J ev).eval (cellPoint jx m)

/-- The honest proof of cell `jx` for the interpolation of the cells of `J`.

It commits to the quotient of that interpolation by the vanishing polynomial of the cell. -/
noncomputable def honestProof (s : TrustedSetup) (J : Finset Nat) (ev : Nat → CosetEvals)
    (jx : Nat) : G1 :=
  commitPoly s (cellsInterpolant J ev /ₘ cellVanishing jx)

/-- The candidate of the second reduction.

It is the set of points of the cells of `J`, the commitment minus the commitment to their
interpolation, and the sum of their proofs over their weights. -/
noncomputable def arsdhCandidate (s : TrustedSetup) (J : Finset Nat) (ev : Nat → CosetEvals)
    (C : G1) (P : Nat → G1) : Finset Fr × G1 × G1 :=
  ((J.biUnion cellNodes).image domainPoint,
    G1.add C (G1.neg (commitPoly s (cellsInterpolant J ev))),
    weightedSum J P fun j => (cellWeight J j)⁻¹)

/-- The vanishing polynomial of a cell is monic. -/
theorem cellVanishing_monic (cellIndex : Nat) : (cellVanishing cellIndex).Monic :=
  monic_X_pow_sub_C _ (by decide)

/-- A sum with a zero term. -/
private theorem add_zero_mul_fr {a b c : Fr} (h : a + 0 * b = c) : a = c := by
  rw [← h, zero_mul, add_zero]

/-- The honest values of cell `jx` interpolate to a remainder.

It is the remainder of the interpolation of the cells by the vanishing polynomial of `jx`. -/
theorem cellInterpolant_honestEvals {J : Finset Nat} (ev : Nat → CosetEvals) {jx : Nat}
    (hjx : jx < CELLS_PER_EXT_BLOB) :
    cellInterpolant jx (honestEvals J ev jx) = cellsInterpolant J ev %ₘ cellVanishing jx := by
  symm
  refine eq_interpolate_of_eval_eq _ (cellPoint_injOn hjx) ?_ fun m hm => ?_
  · rw [Finset.card_range]
    refine (degree_modByMonic_lt _ (cellVanishing_monic jx)).trans_le ?_
    rw [cellVanishing, degree_X_pow_sub_C (by decide)]
  · have hm' := Finset.mem_range.mp hm
    have hz : (cellVanishing jx).eval (cellPoint jx m) = 0 := by
      rw [cellVanishing, eval_sub, eval_pow, eval_X, eval_C, cellPoint_pow hjx hm', sub_self]
    have h := congrArg (eval (cellPoint jx m))
      (modByMonic_add_div (cellsInterpolant J ev) (cellVanishing jx))
    rw [eval_add, eval_mul, hz] at h
    rw [add_zero_mul_fr h, honestEvals, getElem!_pos _ m (by simpa using hm'), Array.getElem_ofFn]

/-- The honest opening. -/
private theorem honest_fr {r z q c : Fr} (h : r + z * q = c) : c - r = q * z := by
  rw [← h]
  ring

/-- A difference that is not zero. -/
private theorem add_neg_ne_zero_fr {c x : Fr} (h : x ≠ c) : c + -x ≠ 0 := by
  rw [← sub_eq_add_neg]
  exact sub_ne_zero.mpr (Ne.symm h)

/-- A difference as a sum with the negation. -/
private theorem add_neg_eq_fr {c x y : Fr} (h : c - x = y) : c + -x = y :=
  (sub_eq_add_neg c x).symm.trans h

/-- **Code-binding of the PeerDAS commitment, deterministic form (Lemma 4 of ePrint 2025/1683).**

Take a model of the target group and a well-formed setup of the secret `τ`.

Let `J` be a set of 64 cells below 128, and `jx` one more cell below 128.

Let the commitment `C` represent `c`, and the proof `P j` of cell `j` represent `w j`.

Let every cell of `J` and the cell `jx` satisfy the scalar equation of a valid cell for `c`.

The values of a cell `j` are read as `(ev j)[m]!`, so a cell of `J` with fewer than 64 values is
read with zeros; only the cell `jx` must have 64 values.

Then one of three cases holds.

- All the cells take the values of one polynomial of degree below 4096: the interpolation of `J`.
- The search on cell `jx` and its honest values gives a bilinear strong Diffie–Hellman solution.
- The candidate of the second search is a `(4095, 64)`-ARSDH winning solution. -/
theorem code_binding {GT : Type} [CommMonoid GT] (M : TargetGroup GT) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB)
    (hJcard : J.card = FIELD_ELEMENTS_PER_CELL) {jx : Nat} (hjx : jx < CELLS_PER_EXT_BLOB)
    (ev : Nat → CosetEvals) (hev : (ev jx).size = FIELD_ELEMENTS_PER_CELL) {C : G1} {c : Fr}
    (hC : G1.Represents C c) {P : Nat → G1} {w : Nat → Fr}
    (hP : ∀ j ∈ insert jx J, G1.Represents (P j) (w j))
    (hv : ∀ j ∈ insert jx J, c - (cellInterpolant j (ev j)).eval τ =
      w j * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift j ^ FIELD_ELEMENTS_PER_CELL)) :
    ((cellsInterpolant J ev).natDegree < FIELD_ELEMENTS_PER_BLOB ∧
        ∀ j ∈ insert jx J, ∀ m < FIELD_ELEMENTS_PER_CELL,
          (cellsInterpolant J ev).eval (cellPoint j m) = (ev j)[m]!) ∨
      (∃ sol, findBsdh M s jx (ev jx) (honestEvals J ev jx) (P jx) (honestProof s J ev jx) =
        some sol ∧ IsBsdhSolution M τ sol) ∨
      IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ (arsdhCandidate s J ev C P) := by
  have hdeg := natDegree_cellsInterpolant_lt hJ hJcard.le ev
  by_cases hcons : ∀ m < FIELD_ELEMENTS_PER_CELL,
      (cellsInterpolant J ev).eval (cellPoint jx m) = (ev jx)[m]!
  · refine Or.inl ⟨hdeg, fun j hj m hm => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hcons m hm
    · exact eval_cellsInterpolant hJ ev hj hm
  refine Or.inr ?_
  have hJne : J.Nonempty := Finset.card_pos.mp (by rw [hJcard]; decide)
  by_cases hc : (cellsInterpolant J ev).eval τ = c
  · -- The honest opening of cell `jx` is valid and has other values.
    refine Or.inl (findBsdh_valid M hs hjx hev (by simp [honestEvals]) ?_
      (hP jx (Finset.mem_insert_self _ _)) (represents_commitPoly hs ?_)
      (hv jx (Finset.mem_insert_self _ _)) ?_)
    · intro heq
      refine hcons fun m hm => ?_
      rw [heq, honestEvals, getElem!_pos _ m (by simpa using hm), Array.getElem_ofFn]
    · rw [natDegree_divByMonic _ (cellVanishing_monic jx)]
      omega
    · have h := congrArg (eval τ) (modByMonic_add_div (cellsInterpolant J ev)
        (cellVanishing jx))
      rw [eval_add, eval_mul, hc] at h
      rw [cellInterpolant_honestEvals ev hjx]
      rw [cellVanishing, eval_sub, eval_pow, eval_X, eval_C] at h
      exact honest_fr h
  · -- The batched opening of the cells of `J` is an ARSDH solution.
    refine Or.inr ?_
    have hφ := represents_weightedSum (J := J) (P := P) (w := w)
      (fun j hj => hP j (Finset.mem_insert_of_mem hj)) fun j => (cellWeight J j)⁻¹
    have hg := hC.add (represents_commitPoly hs hdeg).neg
    rw [arsdhCandidate, isArsdhSolution_iff hg hφ, Finset.card_image_of_injOn
      (domainPoint_injOn_cells hJ), card_biUnion_cellNodes, hJcard, vanishingAt_cells hJ]
    have hb := cell_multiproof_batching hJ hJne ev (c := c) (τ := τ) (φ := w)
      fun j hj => hv j (Finset.mem_insert_of_mem hj)
    exact ⟨rfl, add_neg_ne_zero_fr hc, add_neg_eq_fr hb⟩

end EthLib.Cryptography.Kzg
