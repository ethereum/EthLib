module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Network.Cells

/-!
# Proofs: the cells of eth/72

A response of cells that passes the check holds only requested cell indices.

It holds only requested transactions, in order, with one group of cells for each transaction.

Each group has one cell of 2048 bytes for each blob of its transaction and each marked index.

A response passes the check exactly when it keeps these rules.

A bitmap marks index `i` exactly when `i < 128` and bit `i % 8` of byte `i / 8` is set.

A bitmap is a subset of another exactly when the other marks each index that it marks.

The count of a bitmap is the number of set bits of its 16 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base

/-- Bit `j < 8` of a byte, read by a shift and a mask of 1, is bit `j` of its number. -/
private theorem shift_and_one (x : UInt8) {j : Nat} (hj : j < 8) :
    ((x >>> j.toUInt8) &&& 1 == 1) = x.toNat.testBit j := by
  have h1 : (j.toUInt8).toNat % 8 = j := by simp [Nat.toUInt8]; omega
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt8.toNat_inj]
  simp only [UInt8.toNat_and, UInt8.toNat_shiftRight, h1, UInt8.reduceToNat]
  rw [Nat.testBit, Nat.and_comm]
  have : x.toNat >>> j &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  constructor <;> intro h <;> simp_all <;> omega

/-- A bitmap marks index `i` exactly when `i < 128` and bit `i % 8` of byte `i / 8` is set. -/
theorem CellMask.has_eq_true_iff {mask : CellMask} {i : Nat} :
    mask.has i = true ↔ ∃ h : i < 128, (mask[i / 8]'(by omega)).toNat.testBit (i % 8) = true := by
  unfold CellMask.has
  by_cases h : i < 128
  · have h' : i / 8 < 16 := by omega
    simp only [h', ↓reduceDIte, shift_and_one _ (Nat.mod_lt i (by decide) : i % 8 < 8), h,
      exists_true_left]
  · have h' : ¬ i / 8 < 16 := by omega
    simp [h, h']

/-- A bitmap marks no index from 128 on. -/
private theorem CellMask.has_of_le {mask : CellMask} {i : Nat} (h : 128 ≤ i) :
    mask.has i = false := by
  cases hm : mask.has i
  · rfl
  · obtain ⟨hi, _⟩ := CellMask.has_eq_true_iff.mp hm
    omega

/-- A bitmap is a subset of another exactly when the other marks each index that it marks. -/
theorem CellMask.subset_eq_true_iff {a b : CellMask} :
    a.subset b = true ↔ ∀ i, a.has i = true → b.has i = true := by
  simp only [CellMask.subset, CELL_INDICES, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · intro H i hi
    by_cases hlt : i < 128
    · rcases H i hlt with h | h
      · simp [h] at hi
      · exact h
    · simp [CellMask.has_of_le (Nat.le_of_not_lt hlt)] at hi
  · intro H i _
    cases hi : a.has i
    · exact Or.inl rfl
    · exact Or.inr (H i hi)

/-- The count of a bitmap is the sum, over its 16 bytes, of the number of set bits of each. -/
theorem CellMask.count_eq_sum {mask : CellMask} :
    mask.count =
      (mask.toList.map fun x => (List.range 8).countP fun j => x.toNat.testBit j).sum := by
  have hr : List.range 128 =
      (List.range 16).flatMap (fun k => (List.range 8).map (8 * k + ·)) := by
    decide
  unfold CellMask.count
  rw [CELL_INDICES, hr, ← List.countP_eq_length_filter, List.countP_flatMap]
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 _
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Vector.getElem_toList, Function.comp_apply,
    List.countP_map]
  apply List.countP_congr
  intro j hj
  have hj8 : j < 8 := List.mem_range.mp hj
  have hdiv : (8 * k + j) / 8 = k := by omega
  have hmod : (8 * k + j) % 8 = j := by omega
  simp only [Function.comp_apply]
  rw [CellMask.has_eq_true_iff]
  simp only [hdiv, hmod]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨by omega, h⟩⟩

/-- A subset counts no more indices than the bitmap that holds it.

So a response that passes the check has no more cells for each blob than the request asks for. -/
theorem CellMask.count_le_count_of_subset {a b : CellMask} (h : a.subset b = true) :
    a.count ≤ b.count := by
  unfold CellMask.count
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun i _ hi => CellMask.subset_eq_true_iff.mp h i hi

/-- A response passes the check exactly when it keeps every rule of a Cells answer.

- It marks only indices that the request asks for.
- It holds requested transactions, in the order of the request.
- It has one group of cells and one blob count for each transaction.
- Each group has one cell for each blob of its transaction and each marked index.
- Each cell has 2048 bytes. -/
theorem checkCells_eq_ok_iff {requested : List Hash32} {requestMask : CellMask}
    {blobs : List Nat} {hashes : List Hash32} {groups : List (List ByteArray)} {mask : CellMask} :
    checkCells requested requestMask blobs hashes groups mask = .ok () ↔
      mask.subset requestMask ∧ hashes.Sublist requested ∧ groups.length = hashes.length ∧
        blobs.length = hashes.length ∧
        ∀ (i : Nat) (hg : i < groups.length) (hb : i < blobs.length),
          groups[i].length = blobs[i] * mask.count ∧
            ∀ cell ∈ groups[i], cell.size = BYTES_PER_CELL := by
  unfold checkCells
  by_cases hm : mask.subset requestMask
  · by_cases hs : hashes.isSublist requested
    · by_cases hg : groups.length = hashes.length
      · by_cases hb : blobs.length = hashes.length
        · simp only [hm, hs, hg, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq,
            not_true_eq_false, true_and, List.isSublist_iff_sublist.mp hs]
          simp only [bind_unit_ok_iff, pure, Except.pure, and_true]
          -- No step of either loop stops it early, so each loop passes when each step does.
          rw [forIn_unit_ok_iff (fun x => by
            split <;> simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] <;>
              (try split) <;> simp)]
          rw [List.forall_mem_iff_forall_getElem]
          simp only [List.length_zip, List.length_range, List.getElem_zip, List.getElem_range,
            hg, hb, Nat.min_self]
          refine forall_congr' fun i => ⟨fun H hgi _ => ?_, fun H hi => ?_⟩
          · have h1 := H (by omega)
            by_cases hA : groups[i].length = blobs[i] * mask.count
            · simp only [hA, not_true_eq_false, ↓reduceIte, bind_unit_ok_iff, true_and] at h1 ⊢
              rw [forIn_unit_ok_iff (fun cell => by
                split <;> simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])] at h1
              intro cell hc
              have h2 := h1.1 cell hc
              by_cases hsz : cell.size = BYTES_PER_CELL
              · exact hsz
              · simp [hsz, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h2
            · simp [hA, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h1
          · obtain ⟨hA, hcells⟩ := H hi (by omega)
            simp only [hA, not_true_eq_false, ↓reduceIte, bind_unit_ok_iff, and_true]
            rw [forIn_unit_ok_iff (fun cell => by
              split <;> simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])]
            intro cell hc
            simp [hcells cell hc]
        · simp [hm, hs, hg, hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      · simp [hm, hs, hg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    · have hs' : ¬ hashes.Sublist requested := fun h => hs (List.isSublist_iff_sublist.mpr h)
      simp [hm, hs, hs', throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp [hm, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A response that passes the check marks only indices that the request asks for.

It holds requested transactions in order, and has one group of cells for each. -/
theorem of_checkCells {requested : List Hash32} {requestMask : CellMask} {blobs : List Nat}
    {hashes : List Hash32} {groups : List (List ByteArray)} {mask : CellMask}
    (h : checkCells requested requestMask blobs hashes groups mask = .ok ()) :
    mask.subset requestMask ∧ hashes.Sublist requested ∧ groups.length = hashes.length :=
  let ⟨hm, hs, hg, _⟩ := checkCells_eq_ok_iff.mp h
  ⟨hm, hs, hg⟩

/-- Two errors with one code come from one constructor. -/
theorem CellsError.code_injective (e₁ e₂ : CellsError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [CellsError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Network
