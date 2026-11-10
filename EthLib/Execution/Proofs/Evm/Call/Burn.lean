module

public import EthLib.Execution.Proofs.Evm.Call.Supply

/-!
# Proofs: the ether that a step of a frame burns

Only SELFDESTRUCT burns ether in a message, when the account it runs in is its own beneficiary.

From Cancun, only an account created in the transaction burns, by [EIP-6780][e6780].

From Glamsterdam, none does, by [EIP-8246][e8246].

A log of burns records each such burn, in the order of the run.

It also holds the log of each frame that rolls back, which counts for nothing.

The total of a log is the wei of its burns that no rollback discards.

The log of a step of SELFDESTRUCT reads the beneficiary on the stack and the balance of the account.

A step that runs any other opcode burns nothing.

So the next frame of a step has the supply of the frame before, less the burn of the step.

A step that sends a message gives a caller frame with the supply of the frame before.

Each burn that a log counts comes from a step of SELFDESTRUCT, with the burn of that step.

[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
[e8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The log of burns -/

/-- A log of the ether that a run burns.

It is empty, one burn of SELFDESTRUCT, two logs in order, or the log of a frame that rolls back. -/
inductive BurnLog where
  | empty
  | selfdestruct (originator beneficiary : Address) (amount : Nat)
  | append (first second : BurnLog)
  | rollback (discarded : BurnLog)

/-- The wei of the burns of the log that no rollback discards. -/
def BurnLog.total : BurnLog → Nat
  | .empty => 0
  | .selfdestruct _ _ amount => amount
  | .append first second => first.total + second.total
  | .rollback _ => 0

/-- The log counts a burn of `amount` from `originator` to `beneficiary` that no rollback drops. -/
def BurnLog.Counted (originator beneficiary : Address) (amount : Nat) : BurnLog → Prop
  | .empty => False
  | .selfdestruct o b a => o = originator ∧ b = beneficiary ∧ a = amount
  | .append first second => first.Counted originator beneficiary amount ∨
      second.Counted originator beneficiary amount
  | .rollback _ => False

/-- A log that counts no burn has a total of 0. -/
theorem BurnLog.total_eq_zero_of_not_counted {log : BurnLog}
    (none : ∀ originator beneficiary amount, ¬log.Counted originator beneficiary amount) :
    log.total = 0 := by
  induction log with
  | empty => rfl
  | selfdestruct o b a => exact absurd ⟨rfl, rfl, rfl⟩ (none o b a)
  | append first second ih1 ih2 =>
    simp only [BurnLog.total]
    rw [ih1 fun o b a c => none o b a (.inl c), ih2 fun o b a c => none o b a (.inr c)]
  | rollback => rfl

/-- The log of a move of the balance of SELFDESTRUCT, in the state `state`.

It is empty when the move burns nothing. -/
def selfdestructLog (fork : Fork) (state : TransactionState) (originator beneficiary : Address) :
    BurnLog :=
  let amount := selfdestructBurn fork state originator beneficiary
  if amount = 0 then .empty else .selfdestruct originator beneficiary amount

/-- The log of a move of the balance of SELFDESTRUCT counts exactly its burn. -/
theorem total_selfdestructLog (fork : Fork) (state : TransactionState)
    (originator beneficiary : Address) :
    (selfdestructLog fork state originator beneficiary).total =
      selfdestructBurn fork state originator beneficiary := by
  unfold selfdestructLog
  dsimp only
  split <;> simp_all [BurnLog.total]

/-! ## A step of SELFDESTRUCT -/

omit [GasMeter Meter] in
/-- A step that keeps the state up to the records of reads keeps the burn of SELFDESTRUCT. -/
theorem selfdestructBurn_of_staticStep {evm paid : Evm fork Meter}
    (h : StaticStep evm paid) (beneficiary : Address) :
    selfdestructBurn fork paid.state paid.message.currentTarget beneficiary =
      selfdestructBurn fork evm.state evm.message.currentTarget beneficiary := by
  simp only [selfdestructBurn, h.message, h.created, TransactionState.balanceOf,
    getAccount_of_staticStep h]

/-- The log of a step of SELFDESTRUCT from `evm` to `after`.

It reads the beneficiary at the top of the stack of `evm`, and the burn in the state of `evm`.

The log counts the burn only when the step leaves the account with balance 0, as a halt keeps it.

A balance that starts at 0 burns nothing anyway. -/
def selfdestructStepLog (evm after : Evm fork Meter) : BurnLog :=
  match evm.stack.val with
  | [] => .empty
  | word :: _ =>
    if after.state.balanceOf evm.message.currentTarget = 0 then
      selfdestructLog fork evm.state evm.message.currentTarget (toAddressMasked word)
    else .empty

/-- A successful step of SELFDESTRUCT lowers the supply by exactly the total of its log. -/
theorem supply_selfdestructStep {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) :
    after.state.supply + (selfdestructStepLog evm after).total = evm.state.supply := by
  obtain ⟨word, rest, paid, stack, hpaid, ⟨refund, finished⟩ | halted⟩ := selfdestructStep_eq_ok h
  · unfold finishSelfdestruct at finished
    split at finished
    · cases finished
    · obtain ⟨state, ht, finished⟩ := Base.bind_ok_iff.mp finished
      cases finished
      have transfer := Base.mapError_ok_iff.mp ht
      have hsum := supply_selfdestructTransfer transfer
      rw [selfdestructBurn_of_staticStep hpaid] at hsum
      have prior := TransactionState.supply_eq_of_sameOutside hpaid.state
      simp only [selfdestructStepLog, stack]
      by_cases zero : selfdestructBurn fork evm.state evm.message.currentTarget
          (toAddressMasked word) = 0
      · simp only [selfdestructLog, zero, ↓reduceIte]
        split <;> simp only [BurnLog.total] <;> omega
      · have cleared := balanceOf_selfdestructTransfer_eq_zero transfer
            (fun hzero => zero ((selfdestructBurn_of_staticStep hpaid _).symm.trans hzero))
        rw [hpaid.message] at cleared
        simp only [cleared, ↓reduceIte, total_selfdestructLog]
        omega
  · obtain ⟨error, rfl⟩ := halted
    have halted := hpaid.trans (staticStep_exceptionalHalt paid error)
    have unchanged := TransactionState.supply_eq_of_sameOutside halted.state
    have balance : (exceptionalHalt paid error).state.balanceOf evm.message.currentTarget =
        evm.state.balanceOf evm.message.currentTarget := by
      unfold TransactionState.balanceOf
      rw [getAccount_of_staticStep halted]
    simp only [selfdestructStepLog, stack]
    split
    · rename_i cleared
      have zero := selfdestructBurn_eq_zero_of_balanceOf_eq_zero (fork := fork)
        (beneficiary := toAddressMasked word) (balance.symm.trans cleared)
      simp only [selfdestructLog, zero, ↓reduceIte, BurnLog.total, Nat.add_zero]
      exact unchanged
    · simpa only [BurnLog.total, Nat.add_zero] using unchanged

/-! ## Every step -/

/-- The log of a step from `evm` to `after`: that of SELFDESTRUCT when the step runs it, else none.
-/
def stepBurnLog (evm after : Evm fork Meter) : BurnLog :=
  if RunsSelfdestruct evm then selfdestructStepLog evm after else .empty

omit [GasMeter Meter] in
/-- The log of a step that runs SELFDESTRUCT is the log of SELFDESTRUCT. -/
theorem stepBurnLog_of_runsSelfdestruct {evm : Evm fork Meter} (runs : RunsSelfdestruct evm)
    (after : Evm fork Meter) : stepBurnLog evm after = selfdestructStepLog evm after :=
  ite_eq_left runs

omit [GasMeter Meter] in
/-- The log of a step that runs another opcode is empty. -/
theorem stepBurnLog_of_not_runsSelfdestruct {evm : Evm fork Meter}
    (other : ¬RunsSelfdestruct evm) (after : Evm fork Meter) : stepBurnLog evm after = .empty :=
  ite_eq_right other

/-- A successful step that gives the next frame lowers the supply by the total of its log. -/
theorem supply_of_step_eq_next {evm after : Evm fork Meter}
    (h : step fork evm = .ok (.next after)) :
    after.state.supply + (stepBurnLog evm after).total = evm.state.supply := by
  rcases ordinaryStepRules_supply.step h with ⟨runs, _, next, sd⟩ | ⟨other, keeps⟩
  · cases next
    rw [stepBurnLog_of_runsSelfdestruct runs]
    exact supply_selfdestructStep sd
  · rw [stepBurnLog_of_not_runsSelfdestruct other]
    exact keeps

/-- A successful step that sends a message gives a caller frame with the supply of the frame before.
-/
theorem supply_of_step_eq_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    caller.state.supply = evm.state.supply := by
  rcases ordinaryStepRules_supply.step h with ⟨-, _, next, -⟩ | ⟨-, keeps⟩
  · cases next
  · exact keeps.1

omit [GasMeter Meter] in
/-- Each burn that the log of a step counts is the burn of SELFDESTRUCT from the frame before.

The step runs SELFDESTRUCT, in the account of that frame, and the burn is above 0. -/
theorem counted_stepBurnLog {evm after : Evm fork Meter} {originator beneficiary : Address}
    {amount : Nat} (counted : (stepBurnLog evm after).Counted originator beneficiary amount) :
    RunsSelfdestruct evm ∧ originator = evm.message.currentTarget ∧
      amount = selfdestructBurn fork evm.state originator beneficiary ∧ amount ≠ 0 := by
  unfold stepBurnLog at counted
  split at counted
  · rename_i runs
    unfold selfdestructStepLog at counted
    split at counted
    · exact counted.elim
    · split at counted
      · unfold selfdestructLog at counted
        dsimp only at counted
        split at counted
        · exact counted.elim
        · rename_i nonzero
          obtain ⟨rfl, rfl, rfl⟩ := counted
          exact ⟨runs, rfl, rfl, nonzero⟩
      · exact counted.elim
  · exact counted.elim

end EthLib.Execution.Evm
