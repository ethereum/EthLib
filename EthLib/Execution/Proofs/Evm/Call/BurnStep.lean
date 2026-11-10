module

public import EthLib.Execution.Proofs.Evm.Call.Burn
public import EthLib.Execution.Proofs.Evm.Call.OrdinarySupply

/-!
# Proofs: the burn recorded by one SELFDESTRUCT step

The event uses the instruction's own target, popped beneficiary and starting balance.

A nonzero self-burn clears that balance; a failed gas check keeps it.

Thus the resulting balance distinguishes a completed nonzero burn from a failed step.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A nonzero burn event, or an empty log when the operation burns nothing. -/
def selfdestructLog (fork : Fork) (state : TransactionState) (originator beneficiary : Address) :
    BurnLog :=
  let amount := selfdestructBurn fork state originator beneficiary
  if amount = 0 then .empty else .selfdestruct originator beneficiary amount

/-- The total of one event is its SELFDESTRUCT burn formula. -/
theorem total_selfdestructLog (fork : Fork) (state : TransactionState)
    (originator beneficiary : Address) :
    (selfdestructLog fork state originator beneficiary).total =
      selfdestructBurn fork state originator beneficiary := by
  unfold selfdestructLog
  dsimp only
  split <;> simp_all [BurnLog.total]

/-- A zero starting balance cannot contribute a self-burn. -/
theorem selfdestructBurn_eq_zero {state : TransactionState} {originator beneficiary : Address}
    (balance : state.balanceOf originator = 0) :
    selfdestructBurn fork state originator beneficiary = 0 := by
  unfold selfdestructBurn
  split <;> first | assumption | rfl

/-- A nonzero self-burn leaves the originator's balance zero. -/
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
/-- Static preparation preserves the amount in the SELFDESTRUCT formula. -/
theorem selfdestructBurn_of_staticStep {evm paid : Evm fork Meter}
    (h : StaticStep evm paid) (beneficiary : Address) :
    selfdestructBurn fork paid.state paid.message.currentTarget beneficiary =
      selfdestructBurn fork evm.state evm.message.currentTarget beneficiary := by
  simp only [selfdestructBurn, h.message, h.created, TransactionState.balanceOf,
    getAccount_of_staticStep h]

/-- The log of a SELFDESTRUCT step, from its initial operands and its resulting balance.

Only a completed nonzero self-burn can clear the originator's nonzero balance. -/
def selfdestructStepLog (evm after : Evm fork Meter) : BurnLog :=
  match evm.stack.val with
  | [] => .empty
  | word :: _ =>
    if after.state.balanceOf evm.message.currentTarget = 0 then
      selfdestructLog fork evm.state evm.message.currentTarget (toAddressMasked word)
    else .empty

/-- A successful SELFDESTRUCT step loses exactly the burn of its own operands. -/
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


/-- Only the opcode SELFDESTRUCT can add a burn event in a single step. -/
def stepBurnLog (evm after : Evm fork Meter) : BurnLog :=
  if within : evm.pc < evm.code.size then
    if Op.ofByte fork evm.code[evm.pc] = some .selfdestruct then selfdestructStepLog evm after
    else .empty
  else .empty


/-- The next frame loses exactly the log computed from the actual opcode and operands. -/
theorem supply_step_next {evm after : Evm fork Meter}
    (h : step fork evm = .ok (.next after)) :
    after.state.supply + (stepBurnLog evm after).total = evm.state.supply := by
  unfold step at h
  split at h
  · rename_i within
    dsimp only at h
    split at h
    · cases h
    · rename_i op decoded
      split at h
      · rename_i run selected
        cases hr : run evm with
        | error error => simp [hr, Functor.map, Except.map] at h
        | ok next =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq, StepResult.next.injEq] at h
          subst h
          by_cases ordinary : op = .selfdestruct
          · subst ordinary
            have selectedSD : instruction (Meter := Meter) fork .selfdestruct =
                some (selfdestructStep fork) := rfl
            rw [selectedSD, Option.some.injEq] at selected
            subst selected
            simp only [stepBurnLog, within, ↓reduceDIte, decoded, ↓reduceIte]
            exact supply_selfdestructStep hr
          · simp only [stepBurnLog, within, ↓reduceDIte, decoded, Option.some.injEq, ordinary,
              ↓reduceIte, BurnLog.total, Nat.add_zero]
            exact instruction_supply_eq_of_ne_selfdestruct ordinary selected hr
      · have ordinary : op ≠ .selfdestruct := by
          intro same
          subst same
          have none := ‹instruction (Meter := Meter) fork .selfdestruct = none›
          have someSD : instruction (Meter := Meter) fork .selfdestruct =
              some (selfdestructStep fork) := rfl
          rw [someSD] at none
          cases none
        split at h
        · rename_i run selected
          simp only [stepBurnLog, within, ↓reduceDIte, decoded, Option.some.injEq, ordinary,
            ↓reduceIte, BurnLog.total, Nat.add_zero]
          exact messageInstruction_head_supply selected h
        · cases h
  · rename_i outside
    simp only [stepBurnLog, outside, ↓reduceDIte, BurnLog.total, Nat.add_zero]
    simp only [stopStep, Functor.map, Except.map, Except.ok.injEq, StepResult.next.injEq] at h
    cases h
    rfl

/-- A call or creation preserves supply before it starts its child. -/
theorem supply_step_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    caller.state.supply = evm.state.supply := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm <;>
          simp [hr, Functor.map, Except.map] at h
      · split at h
        · rename_i selected
          exact messageInstruction_head_supply selected h
        · cases h
  · simp [stopStep, Functor.map, Except.map] at h

end EthLib.Execution.Evm
