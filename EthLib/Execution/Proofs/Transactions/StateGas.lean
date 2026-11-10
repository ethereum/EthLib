module

public import EthLib.Execution.Proofs.Evm.Call.MeterRules
public import EthLib.Execution.Proofs.Transactions.Process
public import EthLib.Execution.Proofs.Transactions.Validity

/-!
# Proofs: the gas counts of a transaction from Glamsterdam

From Glamsterdam, a transaction splits its gas into execution gas and a reservoir of state gas.

The block then counts the execution gas and the state gas of the transaction apart.

The message of a transaction keeps its starting reservoir, so that reservoir counts as state gas.

The gas left, the reservoir left and the net state gas used add up to at most the gas given.

For a valid transaction, the execution gas that the block counts is at most the gas limit.

It is also at most `2^24`, the cap of [EIP-7825][eip7825] that EIP-8037 keeps for execution gas.

The state gas that the block counts is at most the gas limit of the transaction.

[EIP-8037][eip8037] defines the reservoir and the two counts.

[eip7825]: https://eips.ethereum.org/EIPS/eip-7825#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The message of a transaction -/

/-- The meter `b` keeps the starting reservoir of `a`, and holds at most its execution gas.

That gas counts the gas left, the spill and the committed spill. -/
private def Spends (a b : StateGasMeter) : Prop :=
  b.grant = a.grant ∧ b.gasLeft + b.spill + b.committed ≤ a.gasLeft + a.spill + a.committed

/-- A meter that spends from another that spends is one that spends. -/
private theorem Spends.trans {a b c : StateGasMeter} (hab : Spends a b) (hbc : Spends b c) :
    Spends a c :=
  ⟨hbc.1.trans hab.1, Nat.le_trans hbc.2 hab.2⟩

/-- A charge of execution gas spends. -/
private theorem Spends.charge {meter after : StateGasMeter} {amount : Nat}
    (h : GasMeter.charge meter amount = .ok after) : Spends meter after := by
  simp only [GasMeter.charge, StateGasMeter.charge] at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, by dsimp only; omega⟩

/-- A charge of state gas spends. -/
private theorem Spends.chargeState {meter after : StateGasMeter} {amount : Nat}
    (h : GasMeter.chargeState meter amount = .ok after) : Spends meter after := by
  simp only [GasMeter.chargeState, StateGasMeter.chargeState] at h
  split at h
  · cases h
    exact ⟨rfl, Nat.le_refl _⟩
  · split at h
    · cases h
      exact ⟨rfl, by dsimp only; omega⟩
    · cases h

/-- A commit spends. -/
private theorem Spends.commit (meter : StateGasMeter) : Spends meter (GasMeter.commit meter) :=
  ⟨rfl, by simp only [GasMeter.commit, StateGasMeter.commit]; omega⟩

/-- The starting reservoir of a message counts as state gas, and it leaves at most its gas. -/
private theorem processMessageCall_gas {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := StateGasMeter) chainId message state substate auths paid =
      .ok output) :
    (message.reservoir : Int) ≤ output.reservoir + output.stateGasUsed ∧
      (output.gasLeft + output.reservoir : Int) + output.stateGasUsed ≤
        message.gas + message.reservoir := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      simp only [CallOutput.ofHalt]
      omega
  rename_i first hfirst
  obtain ⟨hgrant0, hspent0⟩ := meter_prepareFirstFrame (Q := Spends) (fun _ => ⟨rfl, Nat.le_refl _⟩)
    Spends.trans Spends.charge Spends.chargeState Spends.commit hfirst
  have hgas := gas_prepareFirstFrame hfirst
  simp only [GasMeter.start, StateGasMeter.start] at hgrant0 hspent0
  have finish : ∀ (evm : Evm fork StateGasMeter) (refund : Nat) touched,
      evm.gas.grant = first.meter.grant → evm.gas.committed = first.meter.committed →
      GasMeter.gasHeld evm.gas ≤ first.message.gas →
      (message.reservoir : Int) ≤ (CallOutput.ofFrame evm refund touched).reservoir +
          (CallOutput.ofFrame evm refund touched).stateGasUsed ∧
        ((CallOutput.ofFrame evm refund touched).gasLeft +
            (CallOutput.ofFrame evm refund touched).reservoir : Int) +
          (CallOutput.ofFrame evm refund touched).stateGasUsed ≤
        message.gas + message.reservoir := by
    intro evm refund touched hg hc hheld
    rw [hgas] at hheld
    simp only [GasMeter.gasHeld, StateGasMeter.gasHeld] at hheld
    have hr : (CallOutput.ofFrame evm refund touched).reservoir = evm.gas.reservoir := by
      unfold CallOutput.ofFrame
      split <;> rfl
    have hl : (CallOutput.ofFrame evm refund touched).gasLeft = evm.gas.gasLeft := by
      unfold CallOutput.ofFrame
      split <;> rfl
    have hs : (CallOutput.ofFrame evm refund touched).stateGasUsed =
        StateGasMeter.stateGasUsed evm.gas := by
      unfold CallOutput.ofFrame
      split <;> rfl
    rw [hr, hl, hs]
    simp only [StateGasMeter.stateGasUsed]
    omega
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    have hg := Evm.StateGasMeter.processCreateMessage_grant hrun
    have hc := Evm.StateGasMeter.processCreateMessage_committed hrun
    exact finish evm _ _ hg hc used
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    have hg := Evm.StateGasMeter.processMessage_grant hrun
    have hc := Evm.StateGasMeter.processMessage_committed hrun
    exact finish evm _ _ hg hc used

/-- The reservoir that the message of a transaction starts with counts as state gas at its end.
-/
theorem processMessageCall_reservoir_le {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := StateGasMeter) chainId message state substate auths paid =
      .ok output) :
    (message.reservoir : Int) ≤ output.reservoir + output.stateGasUsed :=
  (processMessageCall_gas h).1

/-- The message of a transaction leaves at most the gas it is given.

What it leaves is the execution gas left, the reservoir left and the net state gas used.

What it is given is its execution gas and its reservoir. -/
theorem processMessageCall_spent_le {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := StateGasMeter) chainId message state substate auths paid =
      .ok output) :
    (output.gasLeft + output.reservoir : Int) + output.stateGasUsed ≤
      message.gas + message.reservoir :=
  (processMessageCall_gas h).2

/-! ## The counts of the block from Glamsterdam -/

/-- From Glamsterdam, a valid transaction adds at most its capped gas limit to the execution gas.

That cap is `2^24`. -/
theorem processTransaction_blockGas_execution_le_of_glamsterdam {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (hGlam : .glamsterdam ≤ fork)
    (hValid : validateTransaction fork included.sender tx = .ok included.intrinsicGas)
    (h : processTransaction env block included tx = .ok out) :
    out.blockGas.execution ≤ executionCapacity fork tx := by
  obtain ⟨hIntrinsic, hMin, -, -, -, hAfter⟩ := validateTransaction_ok hValid
  obtain ⟨-, hMax⟩ := hAfter hGlam
  have hI := intrinsicGas_le_minimumGas fork included.sender tx
  have hFloor := calldataFloor_le_minimumGas (Nat.le_trans (by decide) hGlam) included.sender tx
  obtain ⟨_, _, message, output, -, -, hMessage, hOutput, -, hBlock⟩ :=
    processTransaction_gasUsed_of_glamsterdam hGlam (processTransaction_lt_hegota h) h
  have hsum := allocateGas_add fork tx included.intrinsicGas
  have hexec := allocateGas_execution_le hGlam tx included.intrinsicGas
  have hmg := gas_transactionMessage hMessage
  have hres := processMessageCall_reservoir_le hOutput
  dsimp only at hres
  rw [hBlock]
  simp only [executionCapacity, hGlam, ↓reduceIte]
  rw [← hIntrinsic] at hI
  simp only [GasCosts.TX_MAX_GAS_LIMIT] at hMax hexec ⊢
  omega

/-- From Glamsterdam, a transaction that runs adds at most its gas limit to the state gas. -/
theorem processTransaction_blockGas_state_le_of_glamsterdam {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (hGlam : .glamsterdam ≤ fork) (h : processTransaction env block included tx = .ok out) :
    out.blockGas.state ≤ tx.gas.toNat := by
  obtain ⟨_, _, message, output, -, -, hMessage, hOutput, -, hBlock⟩ :=
    processTransaction_gasUsed_of_glamsterdam hGlam (processTransaction_lt_hegota h) h
  have hsum := allocateGas_add fork tx included.intrinsicGas
  have hmg := gas_transactionMessage hMessage
  have hheld := processMessageCall_spent_le hOutput
  dsimp only at hheld
  rw [hmg] at hheld
  rw [hBlock]
  dsimp only
  omega

end EthLib.Execution.Transactions
