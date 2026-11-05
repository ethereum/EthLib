module

public import EthLib.Execution.Evm.MessageCall
public import EthLib.Execution.Proofs.Evm.StateGas

/-!
# Proofs: `Evm.Create`

From Glamsterdam, a creation costs 12000 execution gas, and a dead new address 183600 state gas.

No creation pays state gas before Glamsterdam.

A creation that fails its first checks leaves the state and the accessed addresses as they were.

A creation whose init code fails gives back the state gas of the new account.

From Glamsterdam, the code of a creation costs 1530 state gas a byte.

No creation deploys code longer than 65536 bytes from Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Prices -/

/-- From Glamsterdam, a creation costs 12000 before memory, init code and hash. -/
theorem createBaseCost_of_glamsterdam (h : fork ≥ .glamsterdam) : createBaseCost fork = 12000 := by
  simp only [createBaseCost, h, ite_true]
  rfl

/-- Before Glamsterdam, a creation costs 32000 before memory, init code and hash. -/
theorem createBaseCost_of_lt (h : fork < .glamsterdam) : createBaseCost fork = 32000 := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [createBaseCost, this, ite_false]
  rfl

/-- Before Glamsterdam, a creation pays no state gas. -/
theorem createNewAccountStateGas_of_lt (h : fork < .glamsterdam) (state : TransactionState)
    (address : Address) : createNewAccountStateGas fork state address = 0 := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [createNewAccountStateGas, this, false_and, ite_false]

/-- From Glamsterdam, a creation pays the state gas of a new account exactly at a dead address. -/
theorem createNewAccountStateGas_of_glamsterdam (h : fork ≥ .glamsterdam)
    (state : TransactionState) (address : Address) :
    createNewAccountStateGas fork state address =
      if state.isAccountAlive address then 0 else NEW_ACCOUNT_STATE_GAS := by
  by_cases alive : state.isAccountAlive address <;>
    simp [createNewAccountStateGas, h, alive]

/-! ## The first checks -/

/-- A creation that fails its first checks runs no message.

It pushes 0 and keeps its gas and its substate, so it accesses no new address.

Its state only records the read of the sender. -/
theorem launchCreate_of_preflight {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (fails : (evm.state.getAccount evm.message.currentTarget).balance < value ∨
      (evm.state.getAccount evm.message.currentTarget).nonce = MAX_NONCE ∨
      evm.message.depth + 1 > STACK_DEPTH_LIMIT)
    (h : launchCreate evm value initCode salt = .ok result) :
    ∃ after, result = .next after ∧
      after.state = evm.state.recordAccountRead evm.message.currentTarget ∧
      after.substate = evm.substate ∧ after.gas = GasMeter.credit evm.gas 0 0 := by
  unfold launchCreate at h
  dsimp only at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by exact fails))] at h
  cases hs : skipCall (recordAccountRead { evm with returnData := .empty }
      evm.message.currentTarget) 0 0 with
  | error => simp [hs, Functor.map, Except.map] at h
  | ok after =>
    simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
    refine ⟨after, h.symm, ?_⟩
    obtain ⟨_, h1, h2⟩ := Base.bind_ok_iff.mp hs
    cases h2
    obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
    cases h1
    exact ⟨rfl, rfl, rfl⟩

/-! ## The refill -/

/-- A creation whose init code fails gives the caller back `newAccount` state gas. -/
theorem resumeCreate_gas_of_error {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (failed : child.error.isSome)
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.gas = GasMeter.refill (GasMeter.absorb caller.gas child.gas false) newAccount := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  have hn : child.error.isNone = false := by
    cases e : child.error <;> simp_all
  simp only [advance, hn, Bool.false_eq_true, ite_false, refillStateGas, incorporateChild]

/-- A creation whose init code succeeds gives the caller back its gas, and no state gas. -/
theorem resumeCreate_gas_of_success {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (ok : child.error = none)
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.gas = GasMeter.absorb caller.gas child.gas true := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  simp only [advance, ok, Option.isNone_none, ite_true, incorporateChild]

/-! ## The code -/

/-- From Glamsterdam, the code of `size` bytes raises the net state gas by 1530 a byte. -/
theorem stateGasUsed_chargeCodeDeposit (h : fork ≥ .glamsterdam) {meter after : StateGasMeter}
    {size : Nat} (hc : chargeCodeDeposit fork meter size = .ok after) :
    after.stateGasUsed = meter.stateGasUsed + size * 1530 := by
  simp only [chargeCodeDeposit, h, ite_true] at hc
  obtain ⟨charged, h1, h2⟩ := Base.bind_ok_iff.mp hc
  rw [StateGasMeter.stateGasUsed_chargeState h2]
  simp only [GasMeter.charge, StateGasMeter.charge] at h1
  split at h1
  · cases h1
  · cases h1
    simp only [StateGasMeter.stateGasUsed, CPSB]
    omega

/-- From Glamsterdam, a creation that deploys its code deploys at most 65536 bytes. -/
theorem depositCode_size_le (h : fork ≥ .glamsterdam) {snapshot : TransactionState}
    {evm after : Evm fork Meter} (hd : depositCode fork snapshot evm = .ok after)
    (ok : after.error = none) : evm.output.size ≤ 65536 := by
  have hm : maxCodeSize fork = some 65536 := by simp only [maxCodeSize, h, ite_true]
  unfold depositCode at hd
  dsimp only at hd
  split at hd
  · cases hd
    rename_i failed
    simp_all
  split at hd
  · cases hd
    simp at ok
  split at hd
  · cases hd
    simp at ok
  · rename_i _ fits
    simp only [hm, Option.any_some, decide_eq_true_eq, h, true_and, Nat.not_lt] at fits
    exact fits

end EthLib.Execution.Evm
