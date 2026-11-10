module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract
public import EthLib.Execution.Proofs.Evm.Logic.MeterReach

/-!
# Proofs: system contracts with either gas meter

A successful conservative run of code that does not observe gas gives the same state and output.

From Glamsterdam, this lifts that run to the execution and state gas meter of EIP-8037.

The system call receives its reservoir for sixteen new slots, and 30,000,000 execution gas.

The conservative run pays both gas dimensions from its execution counter.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.SystemContract

open EthLib.Base (Fork U256 Address)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions (prepareFirstFrame_of_value_eq_zero processMessageCall)

variable {fork : Fork} {code : ByteArray}

/-- A conservative specification of supported code gives a system call with either meter. -/
theorem systemCall_of_spec_all {env : BlockEnvironment fork} {block : State.BlockState}
    {target : Address} {data : ByteArray}
    {Q : TransactionState → TransactionState → ByteArray → Prop}
    (hparis : .paris ≤ fork) (supported : SupportedCode code = true)
    (hcode : codeAt block target = .ok code) (hsize : code.size ≠ 0)
    (hpre : Precompiles.addedAt target.toU256.toNat = none)
    (hdelegate : delegatedAddress code = none)
    (hspec : ∀ (message : Message fork) (state : TransactionState) (substate : Substate),
      message.caller = SYSTEM_ADDRESS → message.currentTarget = target →
      message.isStatic = false → message.blockEnv = env → message.data = data →
      message.gas = SYSTEM_TRANSACTION_GAS → (state.getAccountOptional target).isSome = true →
      state = (TransactionState.ofBlock block).recordAccountRead target →
      Spec fork (At code message 0 [] .empty message.gas state substate .empty)
        fun evm => evm.error = none ∧ Q state evm.state evm.output) :
    ∃ out, systemCall env block target data = .ok out ∧ out.error = none ∧
      Q ((TransactionState.ofBlock block).recordAccountRead target) out.state out.output := by
  by_cases hglam : fork < .glamsterdam
  · exact systemCall_of_spec hparis hglam hcode hsize hpre hdelegate hspec
  have glam : .glamsterdam ≤ fork := Nat.le_of_not_gt hglam
  have hc := EthLib.Base.mapError_ok_iff.mp hcode
  have hfirst := prepareFirstFrame_of_value_eq_zero (Meter := StateGasMeter)
    (chainId := env.chainId.toNat) (message := systemMessage env target data)
    (state := .ofBlock block) (substate := Substate.empty) (paid := ∅)
    rfl rfl hc (fun _ => hdelegate)
  generalize hF : Transactions.FirstFrame.ofMeter (Meter := StateGasMeter) _ _ _ _ _ = first
    at hfirst
  have hnot : ¬fork < .paris := Nat.not_lt.mpr hparis
  have hstart : startState fork first.message first.state = first.state := by
    simp only [startState, hnot, ↓reduceIte]
  have hacc : (first.state.getAccountOptional target).isSome = true := by
    subst hF
    exact isSome_of_getCode hsize hc
  have hpre' : precompileAddress fork first.message = none := by
    subst hF
    simp [Transactions.FirstFrame.ofMeter, precompileAddress, systemMessage,
      Precompiles.isPrecompile, hpre]
  have hvalue : ¬(first.message.shouldTransferValue = true ∧ first.message.value ≠ 0) := by
    subst hF
    simp [Transactions.FirstFrame.ofMeter, systemMessage]
  have hcodeM : first.message.code = code := by subst hF; rfl
  have spec := hspec first.message first.state first.substate
    (by subst hF; rfl) (by subst hF; rfl) (by subst hF; rfl) (by subst hF; rfl)
    (by subst hF; rfl) (by subst hF; rfl) hacc (by subst hF; rfl)
  let low : Evm fork Nat := startFrame first.message first.state first.substate first.message.gas
  obtain ⟨stopped, reached, halted, herr, hq⟩ := spec low (at_startFrame hcodeM _ _)
  have hbound : low.pc ∈ opcodePositions low.code := by
    apply mem_opcodePositions_iff.mpr
    exact .here (by change 0 < first.message.code.size; rw [hcodeM]; omega)
  have below : low.gas ≤ first.meter.gasLeft := by subst hF; exact Nat.le_refl _
  obtain ⟨meter, _, highReached⟩ := reached.followsMeter
    (by change SupportedCode first.message.code = true; rw [hcodeM]; exact supported)
    rfl (.inr hbound) herr below
  have ran := runFrame_of_reaches (runChild := processRunner fork first.message.gas)
    highReached (show (withStateGas stopped meter).running = false
    from halted) first.held
  have ran' : runFrame (step fork) (step_decreases fork) first.message.gas
      (processRunner fork first.message.gas)
      (startFrame first.message (startState fork first.message first.state)
        first.substate first.meter) first.held = .ok (withStateGas stopped meter) := by
    rw [hstart]
    exact ran
  have hpm := processMessage_map_val hvalue hpre' ran'
  have noRollback : rollbackOnError first.state (withStateGas stopped meter) =
      withStateGas stopped meter := by simp [rollbackOnError, withStateGas, herr]
  simp only [Except.map] at hpm
  rw [noRollback] at hpm
  cases hp : processMessage fork first.message first.state first.substate
      first.meter first.held with
  | error e => rw [hp] at hpm; cases hpm
  | ok ended =>
    rw [hp] at hpm
    have hv : ended.val = withStateGas stopped meter := Except.ok.inj hpm
    rw [systemCall_of_glamsterdam glam]
    have htarget : (systemMessage env target data).target = some target := rfl
    simp only [processMessageCall, hfirst, hp, htarget, bind, Except.bind, pure, Except.pure,
      Except.map]
    refine ⟨_, rfl, ?_⟩
    simp only [Transactions.CallOutput.ofFrame, hv, withStateGas, herr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte]
    subst hF
    exact ⟨trivial, hq⟩

/-- A conservative storage specification gives the same storage after the actual system call. -/
theorem systemCall_of_writesStorage_all {env : BlockEnvironment fork} {block : State.BlockState}
    {target : Address} {data : ByteArray} {P : (U256 → U256) → Prop}
    (output : (U256 → U256) → ByteArray) (store : (U256 → U256) → U256 → U256)
    (hparis : .paris ≤ fork) (supported : SupportedCode code = true)
    (hcode : codeAt block target = .ok code) (hsize : code.size ≠ 0)
    (hpre : Precompiles.addedAt target.toU256.toNat = none)
    (hdelegate : delegatedAddress code = none)
    (hread : P (storageOf (.ofBlock block) target))
    (hspec : ∀ (message : Message fork) (state : TransactionState) (substate : Substate),
      message.caller = SYSTEM_ADDRESS → message.currentTarget = target →
      message.isStatic = false → message.blockEnv = env → message.data = data →
      message.gas = SYSTEM_TRANSACTION_GAS → (state.getAccountOptional target).isSome = true →
      P (storageOf state target) →
      Spec fork (At code message 0 [] .empty message.gas state substate .empty) fun evm =>
        evm.error = none ∧ evm.output = output (storageOf state target) ∧
        WritesStorage target (store (storageOf state target)) state evm.state) :
    ∃ out, systemCall env block target data = .ok out ∧ out.error = none ∧
      out.output = output (storageOf (.ofBlock block) target) ∧
      WritesStorage target (store (storageOf (.ofBlock block) target)) (.ofBlock block)
        out.state :=
  systemCall_of_spec_all (Q := fun S post out => out = output (storageOf S target) ∧
      WritesStorage target (store (storageOf S target)) S post)
    hparis supported hcode hsize hpre hdelegate
    fun message state substate hcaller htarget hstatic henv hdata hgas hacc hstate =>
      hspec message state substate hcaller htarget hstatic henv hdata hgas hacc
        (by subst hstate; exact hread)

end EthLib.Execution.Blocks.SystemContract
