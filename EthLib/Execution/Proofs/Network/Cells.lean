module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Network.Cells

/-!
# Proofs: the cells of eth/72

A response of cells that passes the check holds only requested cell indices.

It holds only requested transactions, in order, with one group of cells for each transaction.

Each group has one cell of 2048 bytes for each blob of its transaction and each marked index.

A response passes the check exactly when it keeps these rules.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base

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
