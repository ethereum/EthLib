module

public import EthLib.Execution.Evm.Machine.Stack

/-!
# Proofs: `Evm.Machine.Stack`

A pop fails exactly on the empty stack, and a push fails exactly on a stack of 1024 words.

A pop after a push gives back the word and the stack before the push.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Stack

open EthLib.Base (U256)

/-- A pop fails exactly on the empty stack, with an underflow. -/
theorem pop_eq_error_iff {stack : Stack} {e : EvmError} :
    stack.pop = .error e ↔ stack.val = [] ∧ e = .stackUnderflow := by
  obtain ⟨_ | ⟨x, rest⟩, h⟩ := stack <;> simp [pop, eq_comm]

/-- A pop of a stack with a word on top gives that word and the rest. -/
theorem pop_eq_ok_iff {stack : Stack} {x : U256} {rest : Stack} :
    stack.pop = .ok (x, rest) ↔ stack.val = x :: rest.val := by
  obtain ⟨_ | ⟨y, items⟩, h⟩ := stack
  · simp [pop]
  · obtain ⟨rest, _⟩ := rest
    simp only [pop, Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq, List.cons.injEq]

/-- A push fails exactly on a full stack, with an overflow. -/
theorem push_eq_error_iff {stack : Stack} {x : U256} {e : EvmError} :
    stack.push x = .error e ↔ stack.val.length = STACK_LIMIT ∧ e = .stackOverflow := by
  unfold push
  split
  · simp_all [eq_comm]
  · simp_all

/-- A push that succeeds puts the word on top. -/
theorem push_eq_ok_iff {stack after : Stack} {x : U256} :
    stack.push x = .ok after ↔ stack.val.length < STACK_LIMIT ∧ after.val = x :: stack.val := by
  have := stack.property
  unfold push
  split
  · simp_all
  · simp only [Except.ok.injEq]
    constructor
    · rintro rfl
      exact ⟨by omega, rfl⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h.symm

/-- A pop after a push gives back the word and the stack before the push. -/
theorem pop_of_push {stack after : Stack} {x : U256} (h : stack.push x = .ok after) :
    after.pop = .ok (x, stack) :=
  pop_eq_ok_iff.mpr (push_eq_ok_iff.mp h).2

end EthLib.Execution.Evm.Stack
