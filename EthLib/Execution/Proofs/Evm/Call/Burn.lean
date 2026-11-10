module

public import EthLib.Execution.Proofs.Evm.Call.Supply

/-!
# Proofs: the ether that a step of a frame burns

Only SELFDESTRUCT burns ether in a message, when the account it runs in is its own beneficiary.

A log of burns records each such burn, in the order of the run.

It also holds the log of each frame that rolls back, which counts for nothing.

The total of a log is the wei of its burns that no rollback discards.

The log of a step of SELFDESTRUCT reads the beneficiary on the stack and the balance of the account.

A step that runs any other opcode burns nothing.

So the next frame of a step has the supply of the frame before, less the burn of the step.

A step that sends a message keeps the supply up to the frame that sends it.
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

/-- An account with no balance burns nothing. -/
theorem selfdestructBurn_eq_zero {state : TransactionState} {originator beneficiary : Address}
    (balance : state.balanceOf originator = 0) :
    selfdestructBurn fork state originator beneficiary = 0 := by
  unfold selfdestructBurn
  split <;> first | assumption | rfl

/-- A move of the balance of SELFDESTRUCT that burns some wei leaves its account with no balance. -/
theorem balanceOf_selfdestructTransfer_eq_zero {state after : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork state originator beneficiary = .ok after)
    (nonzero : selfdestructBurn fork state originator beneficiary ≠ 0) :
    after.balanceOf originator = 0 := by
  have setZero : ∀ {a b : TransactionState}, a.setAccountBalance fork originator 0 = .ok b →
      b.balanceOf originator = 0 := by
    intro a b h
    obtain ⟨account, changed, read, -⟩ := TransactionState.modifyState_eq_ok h
    cases changed
    unfold TransactionState.balanceOf
    rw [read]
    rfl
  unfold selfdestructTransfer at h
  split at h
  · rename_i hdencun
    obtain ⟨mid, moved, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact setZero h
    · rename_i notCreated
      cases h
      apply False.elim
      apply nonzero
      unfold selfdestructBurn
      split
      · rename_i condition
        rcases condition.2 with early | created
        · exact False.elim (Nat.not_lt_of_ge hdencun early)
        · exact False.elim (notCreated
            (TransactionState.createdAccounts_moveEther moved ▸ created))
      · rfl
  · obtain ⟨mid, _, h⟩ := Base.bind_ok_iff.mp h
    exact setZero h

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

A step that fails leaves the balance, so the log counts the burn only when the balance ends at 0.

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
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨word, e1⟩, hp, h⟩ := Base.bind_ok_iff.mp h
  have stack := (popWord_eq_ok hp).1
  dsimp only at h
  rcases ha : accessAddress e1 (toAddressMasked word) with ⟨cold, e2⟩
  simp only [ha] at h
  have access := staticStep_accessAddress e1 (toAddressMasked word)
  rw [ha] at access
  have pre : StaticStep evm (recordAccountRead e2 (toAddressMasked word)) :=
    ((StaticStep.of_sameContext (popWord_sameContext hp)).trans access).trans
      (staticStep_recordAccountRead _ _)
  obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, hg, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, hsg, h⟩ := Base.bind_ok_iff.mp h
    have paid : StaticStep evm e4 := pre.trans (.of_sameContext
      ((chargeGas_sameContext hg).trans (chargeStateGas_sameContext hsg)))
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨state, ht, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have transfer := Base.mapError_ok_iff.mp ht
      have hsum := supply_selfdestructTransfer transfer
      rw [selfdestructBurn_of_staticStep paid] at hsum
      have prior := TransactionState.supply_eq_of_sameOutside paid.state
      simp only [selfdestructStepLog, stack]
      by_cases zero : selfdestructBurn fork evm.state evm.message.currentTarget
          (toAddressMasked word) = 0
      · simp only [selfdestructLog, zero, ↓reduceIte]
        split <;> simp only [BurnLog.total] <;> omega
      · have cleared := balanceOf_selfdestructTransfer_eq_zero transfer
            (fun hzero => zero ((selfdestructBurn_of_staticStep paid _).symm.trans hzero))
        rw [paid.message] at cleared
        simp only [cleared, ↓reduceIte, total_selfdestructLog]
        omega
  · have unchanged := TransactionState.supply_eq_of_sameOutside pre.state
    have balance : (recordAccountRead e2 (toAddressMasked word)).state.balanceOf
        evm.message.currentTarget = evm.state.balanceOf evm.message.currentTarget := by
      unfold TransactionState.balanceOf
      rw [getAccount_of_staticStep pre]
    simp only [selfdestructStepLog, stack]
    change (recordAccountRead e2 (toAddressMasked word)).state.supply +
      BurnLog.total (if (recordAccountRead e2 (toAddressMasked word)).state.balanceOf
          evm.message.currentTarget = 0 then
        selfdestructLog fork evm.state evm.message.currentTarget (toAddressMasked word)
      else .empty) = evm.state.supply
    split
    · rename_i cleared
      have zero := selfdestructBurn_eq_zero (fork := fork) (beneficiary := toAddressMasked word)
        (balance.symm.trans cleared)
      simp only [selfdestructLog, zero, ↓reduceIte, BurnLog.total, Nat.add_zero]
      exact unchanged
    · exact unchanged

/-! ## Every step -/

/-- The log of a step from `evm` to `after`: that of SELFDESTRUCT when it runs it, else empty. -/
def stepBurnLog (evm after : Evm fork Meter) : BurnLog :=
  if within : evm.pc < evm.code.size then
    if Op.ofByte fork evm.code[evm.pc] = some .selfdestruct then selfdestructStepLog evm after
    else .empty
  else .empty

omit [GasMeter Meter] in
/-- The log of a step that runs SELFDESTRUCT is the log of SELFDESTRUCT. -/
theorem stepBurnLog_of_runsSelfdestruct {evm : Evm fork Meter} (runs : RunsSelfdestruct evm)
    (after : Evm fork Meter) : stepBurnLog evm after = selfdestructStepLog evm after := by
  obtain ⟨within, decoded⟩ := runs
  simp only [stepBurnLog, within, ↓reduceDIte, decoded, ↓reduceIte]

omit [GasMeter Meter] in
/-- The log of a step that runs another opcode is empty. -/
theorem stepBurnLog_of_not_runsSelfdestruct {evm : Evm fork Meter}
    (other : ¬RunsSelfdestruct evm) (after : Evm fork Meter) : stepBurnLog evm after = .empty := by
  unfold stepBurnLog
  split
  · rename_i within
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun decoded => other ⟨within, decoded⟩)]
  · rfl

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

/-- A successful step that sends a message keeps the supply up to the frame that sends it. -/
theorem supply_of_step_eq_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    caller.state.supply = evm.state.supply := by
  rcases ordinaryStepRules_supply.step h with ⟨-, _, next, -⟩ | ⟨-, keeps⟩
  · cases next
  · exact keeps.1

end EthLib.Execution.Evm
