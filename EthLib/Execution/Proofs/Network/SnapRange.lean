module

public import EthLib.Execution.Network.SnapRange
public import EthLib.Execution.Proofs.Trie.Range

/-!
# Proofs: the checks of snap range answers

Two errors of a range answer with one code come from one constructor.

A failed range check keeps its own code, which no other constructor takes.

No error of a range answer has the code of a snap message error, so one Python class carries both.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Execution.Trie

/-- Two errors with one code come from one constructor. -/
theorem SnapRangeError.code_injective (e₁ e₂ : SnapRangeError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;> simp only [SnapRangeError.code] at h <;> try rfl
  all_goals
    first
    | (have := RangeError.le_code ‹_›; rw [h] at this; exact absurd this (by decide))
    | (have := RangeError.le_code ‹_›; rw [← h] at this; exact absurd this (by decide))
    | exact absurd h (by decide)

/-- An error of a range answer never has the code of a snap message error. -/
theorem SnapRangeError.code_ne_snap (e : SnapRangeError) (r : SnapError) : e.code ≠ r.code := by
  cases e with
  | range e =>
    have := RangeError.le_code e
    cases r <;> simp only [SnapRangeError.code, SnapError.code] <;> intro h <;> rw [h] at this <;>
      exact absurd this (by decide)
  | _ => cases r <;> simp only [SnapRangeError.code, SnapError.code] <;> decide

/-- A failed range check keeps the code of its own error. -/
theorem SnapRangeError.code_range (e : RangeError) : (SnapRangeError.range e).code = e.code :=
  rfl

end EthLib.Execution.Network
