module

public import EthLib.Execution.Network.Bodies
public import EthLib.Execution.Proofs.Blocks.Roots
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the check of a block body

Two errors with one code come from one constructor.

A body whose ommers list holds three items is rejected, once its shape and its transactions pass.

A body without withdrawals from Shapella, or with them before, is rejected for that reason.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks

variable {fork : Fork}

/-- Two errors with one code come from one constructor. -/
theorem BodyError.code_injective (e₁ e₂ : BodyError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [BodyError.code] at h; exact absurd h (by decide))

/-- An ommers list of more than `MAX_OMMERS` items is rejected, whatever its items. -/
theorem checkOmmers_tooMany {header : Header fork} {items : List Item}
    (h : MAX_OMMERS < items.length) :
    checkOmmers header (.list items) = .error (.tooManyOmmers items.length) := by
  have hn : ¬ items.length ≤ MAX_OMMERS := Nat.not_le.mpr h
  simp only [checkOmmers, Item.toItems, Except.mapError, ensure, bind, Except.bind, hn, ite_false]

/-- The empty ommers list is accepted when the header commits to it. -/
theorem checkOmmers_nil {header : Header fork} (h : header.ommersHash = EMPTY_OMMER_HASH) :
    checkOmmers header (.list []) = .ok () := by
  have he : encode (.list []) = .ok ⟨#[0xc0]⟩ := by rfl
  simp only [checkOmmers, Item.toItems, Except.mapError, ensure, bind, Except.bind, he, h,
    EMPTY_OMMER_HASH, MAX_OMMERS, List.length_nil, Nat.zero_le, ite_true, beq_self_eq_true,
    List.range_zero, List.zip_nil_left]
  rfl

/-- Before Shapella, a body with three items is rejected for its withdrawals. -/
theorem checkBody_unexpectedWithdrawals (hfork : ¬ .shapella ≤ fork) {header : Header fork}
    {a b c : Item} : checkBody header (.list [a, b, c]) = .error .unexpectedWithdrawals := by
  simp only [checkBody, hfork, ↓reduceDIte]
  rfl

/-- From Shapella, a body with two items is rejected for its withdrawals. -/
theorem checkBody_missingWithdrawals (hfork : .shapella ≤ fork) {header : Header fork}
    {a b : Item} : checkBody header (.list [a, b]) = .error .missingWithdrawals := by
  simp only [checkBody, hfork, ↓reduceDIte]
  rfl

end EthLib.Execution.Network
