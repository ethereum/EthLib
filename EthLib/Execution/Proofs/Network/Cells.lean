module

public import EthLib.Execution.Network.Cells

/-!
# Proofs: the cells of eth/72

A response of cells that passes the check holds only requested cell indices.

It holds only requested transactions, in order, with one group of cells for each transaction.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base

/-- A response that passes the check marks only indices that the request asks for.

It holds requested transactions in order, and has one group of cells for each. -/
theorem of_checkCells {requested : List Hash32} {requestMask : CellMask} {blobs : List Nat}
    {hashes : List Hash32} {groups : List (List ByteArray)} {mask : CellMask}
    (h : checkCells requested requestMask blobs hashes groups mask = .ok ()) :
    mask.subset requestMask ∧ hashes.Sublist requested ∧ groups.length = hashes.length := by
  unfold checkCells at h
  by_cases hm : mask.subset requestMask
  · by_cases hs : hashes.isSublist requested
    · by_cases hg : groups.length = hashes.length
      · exact ⟨hm, List.isSublist_iff_sublist.mp hs, hg⟩
      · simp [hm, hs, hg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp [hm, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [hm, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- Two errors with one code come from one constructor. -/
theorem CellsError.code_injective (e₁ e₂ : CellsError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [CellsError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Network
