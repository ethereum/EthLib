module

public import EthLib.Execution.Proofs.Evm.Logic.Create
public import EthLib.Execution.Proofs.State.Tracker
public import EthLib.Execution.Proofs.Evm.Logic.Callee

/-!
# Proofs: the deposit of the code of a creation

The frame that ends the init code of a creation deposits its output as the code of the new account.

The rules here hold from Berlin to the fork before Glamsterdam, with one counter of gas.

The deposit pays 200 gas a byte, from Frontier.

From London, an output that starts with the byte `0xEF` fails, by EIP-3541.

From Spurious Dragon, an output longer than 24576 bytes fails, by EIP-170.

A deposit that fails puts back the state from before the creation.

It then takes all the gas, and has no output.

Sources: EIP-170 and EIP-3541.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- From Berlin to before Glamsterdam, a frame with no error deposits its output as code.

From London, the output must not start with `0xEF`.

It holds at most 24576 bytes, and the frame holds 200 gas for each of them.

The deposit pays that gas and sets the code of the current account. -/
theorem depositCode_of_ok (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {snapshot : TransactionState} {evm : Evm fork Nat} (herr : evm.error = none)
    (hprefix : .london ≤ fork → evm.output[0]? ≠ some 0xef)
    (hsize : evm.output.size ≤ 24576) (hgas : evm.output.size * CODE_DEPOSIT_PER_BYTE ≤ evm.gas) :
    ∃ state', evm.state.setCode fork evm.message.currentTarget evm.output = .ok state' ∧
      depositCode fork snapshot evm =
        .ok { evm with
          gas := evm.gas - evm.output.size * CODE_DEPOSIT_PER_BYTE, state := state' } := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨state', hset⟩ := State.TransactionState.setCode_isOk fork evm.state
    evm.message.currentTarget evm.output
  refine ⟨state', hset, ?_⟩
  have hp : ¬(fork ≥ .london ∧ evm.output[0]? = some 0xef) := fun ⟨h1, h2⟩ => hprefix h1 h2
  simp [depositCode, herr, hp, hng, chargeCodeDeposit, GasMeter.charge, Nat.not_lt.mpr hgas,
    maxCodeSize, hsd, Nat.not_lt.mpr hsize, hset, Except.mapError, bind, Except.bind, pure,
    Except.pure]

/-- From London, an output that starts with `0xEF` fails to deposit.

The frame then has the state from before the creation, no gas, no output and that error. -/
theorem depositCode_of_prefix (hfork : .london ≤ fork) {snapshot : TransactionState}
    {evm : Evm fork Nat} (herr : evm.error = none)
    (hprefix : evm.output[0]? = some 0xef) :
    depositCode fork snapshot evm = .ok { evm with
      state := evm.state.restoreTxState snapshot, gas := 0, output := .empty,
      error := some .invalidContractPrefix } := by
  have hby : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  simp [depositCode, herr, hprefix, hfork, hby, GasMeter.exhaust]

/-- From Berlin to before Glamsterdam, an output too long or too dear fails to deposit.

From London, the output does not start with `0xEF`.

It holds more than 24576 bytes, or the frame holds less than 200 gas for each of them.

The frame then has the state from before the creation, no gas, no output and out of gas. -/
theorem depositCode_of_outOfGas (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {snapshot : TransactionState} {evm : Evm fork Nat} (herr : evm.error = none)
    (hprefix : .london ≤ fork → evm.output[0]? ≠ some 0xef)
    (hbad : 24576 < evm.output.size ∨ evm.gas < evm.output.size * CODE_DEPOSIT_PER_BYTE) :
    depositCode fork snapshot evm = .ok { evm with
      state := evm.state.restoreTxState snapshot, gas := 0, output := .empty,
      error := some .outOfGas } := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hby : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  have hho : Fork.homestead ≤ fork := Nat.le_trans (by decide) hfork
  have hp : ¬(fork ≥ .london ∧ evm.output[0]? = some 0xef) := fun ⟨h1, h2⟩ => hprefix h1 h2
  by_cases hg : evm.gas < evm.output.size * CODE_DEPOSIT_PER_BYTE
  · simp [depositCode, herr, hp, hng, chargeCodeDeposit, GasMeter.charge, hg, hby, hho,
      GasMeter.exhaust]
  · have hs : 24576 < evm.output.size := hbad.resolve_right hg
    simp [depositCode, herr, hp, hng, chargeCodeDeposit, GasMeter.charge, hg, maxCodeSize, hsd,
      hs, hby, GasMeter.exhaust]

/-- A creation with no value and no precompile ends as its init code ends, then deposits.

It prepares the state of the new account first, and its init code runs from that state.

The frame that ends the init code is rolled back on a failure, then deposits its output. -/
theorem processCreateMessage_eq_ok {message : Message fork} {state : TransactionState}
    {substate : Substate} {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (h : processCreateMessage fork message state substate = .ok ended) :
    ∃ prepared stopped, prepareCreation fork state message.currentTarget = .ok prepared ∧
      runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
        (startFrame message (startState fork message prepared) substate
          (GasMeter.start message.gas message.reservoir)) (Nat.le_refl _) = .ok stopped ∧
      depositCode fork state (rollbackOnError prepared stopped) = .ok ended.val := by
  rw [processCreateMessage] at h
  obtain ⟨prepared, hprep, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨ev, hrun, h⟩ := Base.bind_ok_iff.mp h
  have hdep : depositCode fork state ev.val = .ok ended.val := by
    rcases ev with ⟨evm, used⟩
    dsimp only at h ⊢
    split at h
    · cases h
    · rename_i after hd
      rw [← Except.ok.inj h]
      exact hd
  have hmap := congrArg (Except.map Subtype.val) hrun
  cases hr : runFrame (step fork) (step_decreases fork) message.gas
      (processRunner fork message.gas)
      (startFrame message (startState fork message prepared) substate
        (GasMeter.start message.gas message.reservoir)) (Nat.le_refl _) with
  | error e =>
    rw [processMessage_map_val noValue noPrecompile hr] at hmap
    cases hmap
  | ok stopped =>
    rw [processMessage_map_val noValue noPrecompile hr] at hmap
    have he : rollbackOnError prepared stopped = ev.val := Except.ok.inj hmap
    exact ⟨prepared, stopped, hprep, hr, by rw [he]; exact hdep⟩

/-- The assumption that a creation with code `code` runs as a specification of that code says.

The message runs that code, has no target, sends no value, and runs no precompile.

`G` holds of the message, of the state that the creation prepares, and of the substate.

Then the frame that ends the init code is a stopped frame of `Q`.

The frame that ends the creation is the deposit of that frame, after the rollback of a failure. -/
def CreatesAs (code : ByteArray) (G : Message fork → TransactionState → Substate → Prop)
    (Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop)
    (caller : Evm fork Nat) (message : Message fork) (child : Evm fork Nat) : Prop :=
  message.code = code → message.target = none →
    ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) →
    precompileAddress fork message = none →
    ∀ prepared, prepareCreation fork caller.state message.currentTarget = .ok prepared →
      G message prepared caller.substate.child →
      ∃ stopped, Q message prepared caller.substate.child stopped ∧
        depositCode fork caller.state (rollbackOnError prepared stopped) = .ok child

/-- The runner of the interpreter meets the assumption of a specification of some init code.

The specification holds of every message with that code and `G`, from the frame it starts.

The init code sends no message. -/
theorem meets_of_spec_create {code : ByteArray}
    {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ message state substate, message.code = code → G message state substate →
      Spec fork (At code message 0 [] .empty message.gas (startState fork message state) substate)
        (Q message state substate))
    (bound : Nat) :
    Meets (CreatesAs code G Q) (processRunner fork bound) := by
  refine ⟨fun caller message _ child ran hcode htarget noValue noPrecompile prepared hprep hg => ?_,
    (meets_process fork bound).aborts⟩
  simp only [processRunner, htarget] at ran
  obtain ⟨prepared', stopped, hprep', hrun, hdep⟩ :=
    processCreateMessage_eq_ok noValue noPrecompile ran
  rw [hprep] at hprep'
  cases hprep'
  rcases (SpecUnder.of_spec (callee := fun _ _ _ => True)
      (hspec message prepared caller.substate.child hcode hg)).runFrame
      ((meets_process fork) message.gas) (at_startFrame hcode _ _) (Nat.le_refl _) with
    ⟨stopped', hrun', hq⟩ | ⟨e, hrun', -⟩
  · cases hrun.symm.trans hrun'
    exact ⟨stopped, hq, hdep⟩
  · cases hrun.symm.trans hrun'

end EthLib.Execution.Evm.Logic
