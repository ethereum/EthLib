module

public import EthLib.Cryptography.Proofs.Kzg.MultiproofBatching
public import EthLib.Cryptography.Proofs.Kzg.CellBinding
public import EthLib.Cryptography.Proofs.Kzg.Fk20Proofs

/-!
# Proofs: Lemmas 1 and 2 of ePrint 2025/1683 for the cells of PeerDAS

Cell `j` holds the values of a polynomial on the coset `h_j μ_64`.

Here `μ_64` is the group of 64th roots of unity.

Its point `m` is `h_j ω^(rev m)`, for a primitive 64th root `ω` and the 6-bit reversal `rev`.

The vanishing polynomial of the coset is `X^64 - h_j^64`, the first step of the proof of Lemma 1.

Lemma 1 says that, on another cell `i`, it takes the one value `h_i^64 - h_j^64`.

Lemma 2, the multiproof batching lemma, joins the openings of several cells into one.

Take a set `J` of cells, and let each cell satisfy `c - I_j(τ) = φ_j (τ^64 - h_j^64)`.

Then the interpolation `I` of all their values satisfies `c - I(τ) = φ V(τ)`.

The polynomial `V` vanishes on all their points, and `φ = sum_j φ_j / δ_j`.

The weight `δ_j` is the product of `h_j^64 - h_{j'}^64` over the other cells `j'`.

The paper is Wagner and Zapico, "Proving the Security of PeerDAS without the AGM", §2.3.

It credits Lemma 2 to Anthoine, Fiore and Zapico.

<https://eprint.iacr.org/2025/1683>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial Lagrange

/-- Point `i` of the bit-reversed domain of 8192 points. -/
def domainPoint (i : Nat) : Fr := (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[i]!

/-- The indices in the domain of the 64 points of cell `j`. -/
def cellNodes (cellIndex : Nat) : Finset Nat :=
  (Finset.range FIELD_ELEMENTS_PER_CELL).image (FIELD_ELEMENTS_PER_CELL * cellIndex + ·)

/-- The vanishing polynomial of the coset of a cell is `X^64 - h^64`, as the proof of Lemma 1 says.
-/
theorem nodal_cellNodes {cellIndex : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB) :
    nodal (cellNodes cellIndex) domainPoint =
      X ^ FIELD_ELEMENTS_PER_CELL - C (cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL) := by
  have himg : nodal (cellNodes cellIndex) domainPoint =
      nodal (Finset.range FIELD_ELEMENTS_PER_CELL) (cellPoint cellIndex) := by
    rw [cellNodes, nodal_eq, nodal_eq, Finset.prod_image fun a _ b _ h => by omega]
    rfl
  rw [himg]
  have hmonic : (X ^ FIELD_ELEMENTS_PER_CELL - C (cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL) :
      Fr[X]).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : (X ^ FIELD_ELEMENTS_PER_CELL - C (cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL) :
      Fr[X]).degree = FIELD_ELEMENTS_PER_CELL := degree_X_pow_sub_C (by decide) _
  refine eq_of_degree_sub_lt_of_eval_index_eq _ (cellPoint_injOn hci) ?_ fun m hm => ?_
  · have hlt := degree_sub_lt_left (p := nodal (Finset.range FIELD_ELEMENTS_PER_CELL)
      (cellPoint cellIndex)) (q := X ^ FIELD_ELEMENTS_PER_CELL -
        C (cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL))
      (by rw [degree_nodal, hdeg, Finset.card_range]) nodal_ne_zero
      (by rw [nodal_monic.leadingCoeff, hmonic.leadingCoeff])
    rwa [degree_nodal] at hlt
  · rw [eval_nodal_at_node hm, eval_sub, eval_pow, eval_X, eval_C,
      cellPoint_pow hci (Finset.mem_range.mp hm), sub_self]

/-- A node of a cell is point `m` of that cell, for its offset `m` below 64. -/
theorem mem_cellNodes {cellIndex i : Nat} :
    i ∈ cellNodes cellIndex ↔ ∃ m < FIELD_ELEMENTS_PER_CELL,
      FIELD_ELEMENTS_PER_CELL * cellIndex + m = i := by
  simp [cellNodes]

/-- The node of offset `m` in a cell is point `m` of the cell. -/
theorem domainPoint_cellNode (cellIndex m : Nat) :
    domainPoint (FIELD_ELEMENTS_PER_CELL * cellIndex + m) = cellPoint cellIndex m := rfl

/-- The nodes of two different cells are disjoint. -/
theorem cellNodes_pairwiseDisjoint (J : Finset Nat) :
    (J : Set Nat).PairwiseDisjoint cellNodes := by
  intro j _ j' _ hne
  refine Finset.disjoint_left.mpr fun i hi hi' => hne ?_
  obtain ⟨m, hm, rfl⟩ := mem_cellNodes.mp hi
  obtain ⟨m', hm', he⟩ := mem_cellNodes.mp hi'
  simp only [FIELD_ELEMENTS_PER_CELL] at hm hm' he ⊢
  omega

/-- The nodes of a cell below 128 lie in the domain of 8192 points. -/
theorem cellNodes_subset_range {cellIndex : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB) :
    cellNodes cellIndex ⊆ Finset.range FIELD_ELEMENTS_PER_EXT_BLOB := by
  intro i hi
  obtain ⟨m, hm, rfl⟩ := mem_cellNodes.mp hi
  simp only [Finset.mem_range, FIELD_ELEMENTS_PER_CELL, FIELD_ELEMENTS_PER_EXT_BLOB,
    CELLS_PER_EXT_BLOB] at hm hci ⊢
  omega

/-- The points of the domain are distinct. -/
theorem domainPoint_injOn :
    Set.InjOn domainPoint (Finset.range FIELD_ELEMENTS_PER_EXT_BLOB) := fun i hi j hj h =>
  getElem_rootsOfUnityBrp_inj (k := 13) rfl (Nat.dvd_of_mod_eq_zero (by decide))
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h

/-- Two cells below 128 with the same `h^64` are the same cell. -/
theorem cellShift_pow_inj {j j' : Nat} (hj : j < CELLS_PER_EXT_BLOB)
    (hj' : j' < CELLS_PER_EXT_BLOB)
    (h : cellShift j ^ FIELD_ELEMENTS_PER_CELL = cellShift j' ^ FIELD_ELEMENTS_PER_CELL) :
    j = j' := by
  rw [cellShift, cellShift, cosetShift_pow_cell j hj, cosetShift_pow_cell j' hj',
    getElem!_pos _ _ (by rw [size_computeRootsOfUnity]; exact reverseBits_lt_two_pow j 7),
    getElem!_pos _ _ (by rw [size_computeRootsOfUnity]; exact reverseBits_lt_two_pow j' 7),
    getElem_computeRootsOfUnity, getElem_computeRootsOfUnity] at h
  have hrev := (isPrimitiveRoot_domainRoot (order := CELLS_PER_EXT_BLOB)
    (Nat.dvd_of_mod_eq_zero (by decide))).pow_inj (reverseBits_lt_two_pow j 7)
    (reverseBits_lt_two_pow j' 7) h
  have := congrArg (reverseBits · (2 ^ 7)) hrev
  simpa [reverseBits_reverseBits (k := 7) hj, reverseBits_reverseBits (k := 7) hj'] using this

/-- The vanishing polynomial of a disjoint union is the product of those of its parts. -/
theorem nodal_biUnion {F ι κ : Type} [CommRing F] [DecidableEq ι] {T : Finset κ}
    {part : κ → Finset ι} (hdisj : (T : Set κ).PairwiseDisjoint part) (v : ι → F) :
    nodal (T.biUnion part) v = ∏ j ∈ T, nodal (part j) v := by
  simp only [nodal_eq]
  exact Finset.prod_biUnion hdisj

/-- Lemma 1: the vanishing polynomial of cell `j'` takes the value `h^64 - h'^64` on cell `j`. -/
theorem eval_nodal_cellNodes {j j' i : Nat} (hj : j < CELLS_PER_EXT_BLOB)
    (hj' : j' < CELLS_PER_EXT_BLOB) (hi : i ∈ cellNodes j) :
    (nodal (cellNodes j') domainPoint).eval (domainPoint i) =
      cellShift j ^ FIELD_ELEMENTS_PER_CELL - cellShift j' ^ FIELD_ELEMENTS_PER_CELL := by
  obtain ⟨m, hm, rfl⟩ := mem_cellNodes.mp hi
  rw [nodal_cellNodes hj', eval_sub, eval_pow, eval_X, eval_C, domainPoint_cellNode,
    cellPoint_pow hj hm]

/-- The weight of cell `j` in a set `J` of cells.

It is the product of `h_j^64 - h_{j'}^64` over the other cells `j'`.

It is the value of the vanishing polynomial of the other cells on cell `j`. -/
def cellWeight (J : Finset Nat) (j : Nat) : Fr :=
  ∏ j' ∈ J.erase j, (cellShift j ^ FIELD_ELEMENTS_PER_CELL - cellShift j' ^ FIELD_ELEMENTS_PER_CELL)

/-- The weight of a cell is not zero: two different cells have different `h^64`. -/
theorem cellWeight_ne_zero {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB) {j : Nat}
    (hj : j ∈ J) : cellWeight J j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j' hj' => sub_ne_zero.mpr fun h =>
    Finset.ne_of_mem_erase hj' (cellShift_pow_inj (hJ j' (Finset.mem_of_mem_erase hj'))
      (hJ j hj) h.symm)

/-- The vanishing polynomial of the other cells takes the weight of the cell on its nodes. -/
theorem eval_nodal_sdiff_cellNodes {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB)
    {j : Nat} (hj : j ∈ J) {i : Nat} (hi : i ∈ cellNodes j) :
    (nodal (J.biUnion cellNodes \ cellNodes j) domainPoint).eval (domainPoint i) =
      cellWeight J j := by
  have hrest : J.biUnion cellNodes \ cellNodes j = (J.erase j).biUnion cellNodes := by
    ext i'
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · rintro ⟨⟨j', hj', hi'⟩, hnot⟩
      exact ⟨j', ⟨fun h => hnot (h ▸ hi'), hj'⟩, hi'⟩
    · rintro ⟨j', ⟨hne, hj'⟩, hi'⟩
      exact ⟨⟨j', hj', hi'⟩, fun hij => Finset.disjoint_left.mp
        (cellNodes_pairwiseDisjoint J hj' hj hne) hi' hij⟩
  rw [hrest, nodal_biUnion (cellNodes_pairwiseDisjoint _), eval_prod, cellWeight]
  exact Finset.prod_congr rfl fun j' hj' =>
    eval_nodal_cellNodes (hJ j hj) (hJ j' (Finset.mem_of_mem_erase hj')) hi

/-- The values of a family of cells, indexed by the points of the domain. -/
def cellValue (ev : Nat → CosetEvals) (i : Nat) : Fr :=
  (ev (i / FIELD_ELEMENTS_PER_CELL))[i % FIELD_ELEMENTS_PER_CELL]!

/-- The interpolation of a cell is the interpolation of its values on its nodes. -/
theorem cellInterpolant_eq_interpolate {cellIndex : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB)
    (ev : Nat → CosetEvals) :
    cellInterpolant cellIndex (ev cellIndex) =
      interpolate (cellNodes cellIndex) domainPoint (cellValue ev) := by
  refine eq_interpolate_of_eval_eq _ (domainPoint_injOn.mono (cellNodes_subset_range hci)) ?_
    fun i hi => ?_
  · have hcard : (cellNodes cellIndex).card = FIELD_ELEMENTS_PER_CELL := by
      rw [cellNodes, Finset.card_image_of_injective _ (fun a b h => by omega),
        Finset.card_range]
    rw [hcard]
    exact (degree_le_natDegree).trans_lt
      (WithBot.coe_lt_coe.mpr (natDegree_cellInterpolant_lt hci _))
  · obtain ⟨m, hm, rfl⟩ := mem_cellNodes.mp hi
    rw [domainPoint_cellNode, eval_cellInterpolant_cellPoint hci hm, cellValue]
    have hd : (FIELD_ELEMENTS_PER_CELL * cellIndex + m) / FIELD_ELEMENTS_PER_CELL = cellIndex := by
      simp only [FIELD_ELEMENTS_PER_CELL] at hm ⊢
      omega
    have hr : (FIELD_ELEMENTS_PER_CELL * cellIndex + m) % FIELD_ELEMENTS_PER_CELL = m := by
      simp only [FIELD_ELEMENTS_PER_CELL] at hm ⊢
      omega
    rw [hd, hr]

/-- The interpolation of the values of the cells of `J` on all their nodes. -/
noncomputable def cellsInterpolant (J : Finset Nat) (ev : Nat → CosetEvals) : Fr[X] :=
  interpolate (J.biUnion cellNodes) domainPoint (cellValue ev)

/-- The interpolation of the cells takes the value of cell `j` at its point `m`. -/
theorem eval_cellsInterpolant {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB)
    (ev : Nat → CosetEvals) {j m : Nat} (hj : j ∈ J) (hm : m < FIELD_ELEMENTS_PER_CELL) :
    (cellsInterpolant J ev).eval (cellPoint j m) = (ev j)[m]! := by
  have hv : Set.InjOn domainPoint (J.biUnion cellNodes) := domainPoint_injOn.mono fun i hi => by
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    exact cellNodes_subset_range (hJ j hj) hij
  have hmem : FIELD_ELEMENTS_PER_CELL * j + m ∈ J.biUnion cellNodes :=
    Finset.mem_biUnion.mpr ⟨j, hj, mem_cellNodes.mpr ⟨m, hm, rfl⟩⟩
  rw [cellsInterpolant, ← domainPoint_cellNode, eval_interpolate_at_node _ hv hmem, cellValue]
  have hd : (FIELD_ELEMENTS_PER_CELL * j + m) / FIELD_ELEMENTS_PER_CELL = j := by
    simp only [FIELD_ELEMENTS_PER_CELL] at hm ⊢
    omega
  have hr : (FIELD_ELEMENTS_PER_CELL * j + m) % FIELD_ELEMENTS_PER_CELL = m := by
    simp only [FIELD_ELEMENTS_PER_CELL] at hm ⊢
    omega
  rw [hd, hr]

/-- **Lemma 2 for cells.**

Let `J` be a nonempty set of cells below 128, and let cell `j` have values `ev j`.

Let each cell satisfy `c - I_j(τ) = φ_j (τ^64 - h_j^64)`.

Then the interpolation `I` of all the cells satisfies `c - I(τ) = φ V(τ)`.

Here `V` is the product of the `X^64 - h_j^64`, and `φ` is the sum of `φ_j` over the weights. -/
theorem cell_multiproof_batching {J : Finset Nat} (hJ : ∀ j ∈ J, j < CELLS_PER_EXT_BLOB)
    (hJne : J.Nonempty) (ev : Nat → CosetEvals) {c τ : Fr} {φ : Nat → Fr}
    (h : ∀ j ∈ J, c - (cellInterpolant j (ev j)).eval τ =
      φ j * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift j ^ FIELD_ELEMENTS_PER_CELL)) :
    c - (cellsInterpolant J ev).eval τ =
      (∑ j ∈ J, (cellWeight J j)⁻¹ * φ j) *
        ∏ j ∈ J, (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift j ^ FIELD_ELEMENTS_PER_CELL) := by
  have hv : Set.InjOn domainPoint (J.biUnion cellNodes) := domainPoint_injOn.mono fun i hi => by
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    exact cellNodes_subset_range (hJ j hj) hij
  have hb := multiproof_batching (cellNodes_pairwiseDisjoint J) hv
    (fun j hj i hi => eval_nodal_sdiff_cellNodes hJ hj hi)
    (fun j _ => ⟨FIELD_ELEMENTS_PER_CELL * j, mem_cellNodes.mpr ⟨0, by decide, rfl⟩⟩) hJne
    (cellValue ev) (c := c) (τ := τ) (φ := φ) fun j hj => by
      rw [← cellInterpolant_eq_interpolate (hJ j hj), nodal_cellNodes (hJ j hj),
        eval_sub, eval_pow, eval_X, eval_C]
      exact h j hj
  rw [nodal_biUnion (cellNodes_pairwiseDisjoint J), eval_prod] at hb
  refine hb.trans (congrArg _ (Finset.prod_congr rfl fun j hj => ?_))
  rw [nodal_cellNodes (hJ j hj), eval_sub, eval_pow, eval_X, eval_C]

end EthLib.Cryptography.Kzg
