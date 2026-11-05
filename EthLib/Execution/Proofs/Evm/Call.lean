module

public import EthLib.Execution.Evm.Call
public import EthLib.Execution.Proofs.Evm.StateGas

/-!
# Proofs: `Evm.Call`

From Glamsterdam, sending value with a call costs 11300 execution gas.

A new account then costs no execution gas, and CALL pays 183600 state gas for it instead.

Only CALL with value to a dead account pays that state gas, and no call pays it before Glamsterdam.

A callee that fails gives the caller back that state gas, and so does a call that runs no message.

With the meter of EIP-8037, the caller then has the net state gas it had before the call.

That holds when the failed callee has rolled back, as every failed message does.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type}

/-! ## Prices -/

/-- The state gas of a new account is 120 bytes at 1530 gas each. -/
theorem newAccountStateGas_eq : NEW_ACCOUNT_STATE_GAS = 183600 := rfl

/-- From Glamsterdam, sending value with a call costs 11300. -/
theorem callValueCost_of_glamsterdam (h : fork ≥ .glamsterdam) {value : U256} (hv : value ≠ 0) :
    callValueCost fork value = 11300 := by
  simp only [callValueCost, hv, h, ite_false, ite_true]
  rfl

/-- From Glamsterdam, a new account costs a call no execution gas. -/
theorem callNewAccountCost_of_glamsterdam (h : fork ≥ .glamsterdam)
    (state : State.TransactionState) (to : Base.Address) (value : U256) :
    callNewAccountCost fork state to value = 0 := by
  simp only [callNewAccountCost, h, ite_true]

/-- Before Glamsterdam, no call pays state gas. -/
theorem callNewAccountStateGas_of_lt (h : fork < .glamsterdam) (kind : CallKind)
    (state : State.TransactionState) (call : CallOperands) :
    callNewAccountStateGas fork kind state call = 0 := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [callNewAccountStateGas, this, false_and, ite_false]

/-- From Glamsterdam, a call pays state gas exactly when it is CALL with value to a dead account.

It then pays the state gas of a new account. -/
theorem callNewAccountStateGas_of_glamsterdam (h : fork ≥ .glamsterdam) (kind : CallKind)
    (state : State.TransactionState) (call : CallOperands) :
    callNewAccountStateGas fork kind state call =
      if kind = .call ∧ call.value ≠ 0 ∧ ¬state.isAccountAlive call.address then
        NEW_ACCOUNT_STATE_GAS
      else 0 := by
  simp only [callNewAccountStateGas, h, true_and]

/-! ## The refill -/

/-- A callee that fails gives the caller back `newAccount` state gas, after its own gas. -/
theorem resumeCall_gas_of_error [GasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256} (failed : child.error.isSome)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.gas = GasMeter.refill (GasMeter.absorb caller.gas child.gas false) newAccount := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  have hn : child.error.isNone = false := by
    cases e : child.error <;> simp_all
  simp only [advance, hn, Bool.false_eq_true, ite_false, refillStateGas, incorporateChild]

/-- A callee that succeeds gives the caller back its gas, and no state gas. -/
theorem resumeCall_gas_of_success [GasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256} (ok : child.error = none)
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.gas = GasMeter.absorb caller.gas child.gas true := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  simp only [advance, ok, Option.isNone_none, ite_true, incorporateChild]

/-- A call that lacks the value runs no message.

The caller gets back `newAccount` state gas, then the gas and the reservoir of the message. -/
theorem finishCall_of_balance_lt [GasMeter Meter] {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (low : (evm.state.getAccount evm.message.currentTarget).balance < call.value)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    ∃ after, result = .next after ∧
      after.gas = GasMeter.credit (GasMeter.refill (GasMeter.drain evm.gas) newAccount) subCall
        (GasMeter.reservoir evm.gas) := by
  unfold finishCall at h
  split at h
  · cases h
  · dsimp only at h
    simp only [low, ↓reduceIte] at h
    cases hs : skipCall (refillStateGas
        { evm with memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      refine ⟨after, h.symm, ?_⟩
      obtain ⟨_, h1, h2⟩ := Base.bind_ok_iff.mp hs
      cases h2
      obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
      cases h1
      rfl

/-! ## The net state gas of a call, with the meter of EIP-8037 -/

namespace StateGasMeter

/-- A failed callee gives the caller back the net state gas it had before the call.

The caller `meter` charges `amount` state gas, pays `gas`, and passes on its reservoir.

The callee then fails, and rolls back to the reservoir it got, with no spill.

The caller absorbs it and refills `amount`. -/
theorem stateGasUsed_call_of_error {meter charged paid child : StateGasMeter} {amount gas : Nat}
    (hc : meter.chargeState amount = .ok charged) (hp : charged.charge gas = .ok paid)
    (reservoir : child.reservoir = paid.reservoir) (spill : child.spill = 0) :
    ((paid.drain.absorb child false).refill amount).stateGasUsed = meter.stateGasUsed := by
  have hu := stateGasUsed_chargeState hc
  unfold charge at hp
  split at hp
  · cases hp
  · cases hp
    dsimp only at reservoir
    rw [stateGasUsed_refill]
    simp only [absorb, drain, Bool.false_eq_true, ite_false, stateGasUsed] at hu ⊢
    omega

/-- A call that runs no message gives the caller back the net state gas it had before the call.

The caller `meter` charges `amount` state gas, pays `gas`, and passes on its reservoir.

It then refills `amount`, and gets back `subCall` execution gas and its reservoir. -/
theorem stateGasUsed_call_of_skip {meter charged paid : StateGasMeter} {amount gas subCall : Nat}
    (hc : meter.chargeState amount = .ok charged) (hp : charged.charge gas = .ok paid) :
    ((paid.drain.refill amount).cancel (start subCall paid.reservoir)).stateGasUsed =
      meter.stateGasUsed := by
  have hu := stateGasUsed_chargeState hc
  unfold charge at hp
  split at hp
  · cases hp
  · cases hp
    simp only [cancel, refill, drain, start, stateGasUsed] at hu ⊢
    omega

end StateGasMeter

end EthLib.Execution.Evm
