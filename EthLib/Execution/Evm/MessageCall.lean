module

public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Evm.JumpDest
public import EthLib.Execution.Evm.Precompiles.Table

/-!
# `Evm.MessageCall`

The execution of a message: move its value, then run its code or a precompile.

A message that fails leaves the state as it was before the message.

Only the record of the accounts that the transaction created stays.

An exceptional halt also leaves no gas, while a revert keeps it.

From Glamsterdam, both roll the state gas of the frame back, by [EIP-8037][eip8037].

A message starts with the reservoir that its caller passes on.

A message runs each message of its code in the same way, with less gas than it has.

So the recursion of messages ends, by the gas of the message.

Before Paris, a message gives its target an empty account when it has none.

From Spurious Dragon, the transaction deletes such an account at its end, by EIP-161.

From Paris, EIP-7523 forbids empty accounts, so the message creates none.

A precompile charges its price, and its failure is an exceptional halt.

The caller checks the depth of the message and the balance it sends before the message runs.

A creation first wipes the storage of the new account and records it as created.

From Spurious Dragon, the new account starts with nonce 1, by EIP-161.

Once the init code succeeds, its output is the code of the new account, at 200 gas a byte.

From Homestead, a creation that cannot pay for its code fails, by EIP-2.

Before, it succeeds and deploys no code.

From Spurious Dragon, code longer than the limit fails, by EIP-170.

From London, code that starts with `0xef` fails, by EIP-3541.

The section Message Call of the Yellow Paper, Shanghai version, defines the execution of a message.

Its section Contract Creation defines the creation.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[EIP-2][eip2], [EIP-161][eip161], [EIP-170][eip170] and [EIP-3541][eip3541] change the creation.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip2]: https://eips.ethereum.org/EIPS/eip-2#specification
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip170]: https://eips.ethereum.org/EIPS/eip-170#specification
[eip3541]: https://eips.ethereum.org/EIPS/eip-3541#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-halts-and-reverts
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The substate that a message starts from: no log and no refund.

It keeps the accesses so far, and the accounts that its callers will delete.

Before London, SELFDESTRUCT gives a refund only for an account outside that set. -/
def Substate.child (substate : Substate) : Substate :=
  { Substate.empty with
    accountsToDelete := substate.accountsToDelete
    accessedAddresses := substate.accessedAddresses
    accessedStorageKeys := substate.accessedStorageKeys }

/-- The frame of a message at its start, with the state and the substate it starts from. -/
def startFrame (message : Message fork) (state : TransactionState) (substate : Substate) :
    Evm fork Meter where
  pc := 0
  stack := .empty
  memory := .empty
  code := message.code
  validJumpDestinations := validJumpDestinations message.code
  gas := GasMeter.start message.gas message.reservoir
  running := true
  message := message
  output := .empty
  returnData := .empty
  state := state
  substate := substate
  error := none

/-- The frame after the precompile at `address` runs on the call data, or none for no precompile.

A precompile that succeeds charges its price and gives its output.

A precompile that fails halts the frame exceptionally. -/
def runPrecompile (fork : Fork) (address : Nat) (evm : Evm fork Meter) : Option (Evm fork Meter) :=
  match Precompiles.run fork address evm.message.data evm.message.gas with
  | none => none
  | some (.error _) => some (exceptionalHalt evm .precompile)
  | some (.ok output) =>
    match GasMeter.charge evm.gas ((Precompiles.price fork address evm.message.data).getD 0) with
    | .error e => some (exceptionalHalt evm e)
    | .ok gas => some { evm with gas, output, running := false }

/-- A precompile ends with no more gas than its frame. -/
theorem gasHeld_runPrecompile_le [LawfulGasMeter Meter] {address : Nat}
    {evm after : Evm fork Meter} (h : runPrecompile fork address evm = some after) :
    GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld evm.gas := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    simp only [exceptionalHalt, LawfulGasMeter.gasHeld_exhaust]
    exact Nat.zero_le _
  · split at h
    · cases h
      simp only [exceptionalHalt, LawfulGasMeter.gasHeld_exhaust]
      exact Nat.zero_le _
    · rename_i hc
      cases h
      exact Nat.le_trans (Nat.le_add_right _ _) (LawfulGasMeter.gasHeld_charge hc)

/-- The address of the precompile that a message calls at fork `fork`, or none. -/
def precompileAddress (fork : Fork) (message : Message fork) : Option Nat :=
  match message.codeAddress with
  | some address =>
    let number := address.toU256.toNat
    if Precompiles.isPrecompile fork number then some number else none
  | none => none

/-- The frame that ends a message, with the writes of `snapshot` back when the message failed.

A revert also rolls back the state gas of the frame.

An exceptional halt has already rolled it back. -/
def rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) : Evm fork Meter :=
  if evm.error.isSome then
    { evm with
      state := evm.state.restoreTxState snapshot
      gas := if evm.error = some .revert then GasMeter.rollback evm.gas else evm.gas }
  else evm

/-- The state at the start of the creation of the account at `address`, at fork `fork`.

Its storage is wiped, and it is recorded as created.

From Spurious Dragon, its nonce grows from 0 to 1. -/
def prepareCreation (fork : Fork) (state : TransactionState) (address : Address) :
    Except EvmError TransactionState :=
  let state := (state.destroyStorage address).markAccountCreated address
  if fork ≥ .spuriousDragon then (state.incrementNonce fork address).mapError .state
  else .ok state

/-- The frame that ends a creation, from the frame `evm` that ends its init code.

A creation that fails puts back the state `snapshot` from before it.

A creation whose init code succeeds pays for the output and deploys it as code.

When it cannot, it fails with no gas left, and from Byzantium with no output. -/
def depositCode (fork : Fork) (snapshot : TransactionState) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) :=
  if evm.error.isSome then .ok { evm with state := evm.state.restoreTxState snapshot }
  else
    let code := evm.output
    let fail (error : EvmError) : Evm fork Meter :=
      { evm with
        state := evm.state.restoreTxState snapshot
        gas := GasMeter.exhaust evm.gas
        output := if fork ≥ .byzantium then .empty else evm.output
        error := some error }
    if fork ≥ .london ∧ code[0]? = some 0xef then .ok (fail .invalidContractPrefix)
    else
      match GasMeter.charge evm.gas (code.size * CODE_DEPOSIT_PER_BYTE) with
      | .error e => .ok (if fork ≥ .homestead then fail e else { evm with output := .empty })
      | .ok gas =>
        if (maxCodeSize fork).any (· < code.size) then .ok (fail .outOfGas)
        else do
          let state ← (evm.state.setCode fork evm.message.currentTarget code).mapError .state
          return { evm with gas, state }

/-- The deposit of the code leaves no more gas than the init code left. -/
theorem gasHeld_depositCode_le [LawfulGasMeter Meter] {snapshot : TransactionState}
    {evm after : Evm fork Meter} (h : depositCode fork snapshot evm = .ok after) :
    GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld evm.gas := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact Nat.le_refl _
  · split at h
    · cases h
      simp only [LawfulGasMeter.gasHeld_exhaust]
      exact Nat.zero_le _
    · split at h
      · cases h
        split
        · simp only [LawfulGasMeter.gasHeld_exhaust]
          exact Nat.zero_le _
        · exact Nat.le_refl _
      · rename_i hc
        split at h
        · cases h
          simp only [LawfulGasMeter.gasHeld_exhaust]
          exact Nat.zero_le _
        · obtain ⟨_, -, h⟩ := except_bind_eq_ok h
          cases h
          exact Nat.le_trans (Nat.le_add_right _ _) (LawfulGasMeter.gasHeld_charge hc)

mutual

/-- Run a message at fork `fork`, from the state and the substate it starts from.

The frame that ends the message has at most the gas of the message.

The run fails only with an error that aborts the whole execution. -/
def processMessage [LawfulGasMeter Meter] (fork : Fork) (message : Message fork)
    (state : TransactionState) (substate : Substate) :
    Except EvmError { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas } :=
  let rollback (ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }) :
      { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas } :=
    ⟨rollbackOnError state ended.val, by
      unfold rollbackOnError
      split
      · dsimp only
        split
        · exact Nat.le_trans (LawfulGasMeter.gasHeld_rollback _) ended.property
        · exact ended.property
      · exact ended.property⟩
  Except.map rollback do
    let state := if fork < .paris then state.touchAccount message.currentTarget else state
    let state ←
      if message.shouldTransferValue ∧ message.value ≠ 0 then
        (state.moveEther fork message.caller message.currentTarget message.value).mapError .state
      else pure state
    let evm : Evm fork Meter := startFrame message state substate
    have start : GasMeter.gasHeld evm.gas = message.gas := LawfulGasMeter.gasHeld_start _ _
    match precompileAddress fork message with
    | some address =>
      if message.disablePrecompiles then
        pure ⟨{ evm with running := false }, Nat.le_of_eq start⟩
      else
        match h : runPrecompile fork address evm with
        | some after => pure ⟨after, start ▸ gasHeld_runPrecompile_le h⟩
        | none => pure ⟨{ evm with running := false }, Nat.le_of_eq start⟩
    | none =>
      match h : runFrame (step fork) (step_decreases fork) message.gas
          (fun caller child _ =>
            match child.target with
            | some _ => processMessage fork child caller.state caller.substate.child
            | none => processCreateMessage fork child caller.state caller.substate.child)
          evm (Nat.le_of_eq start) with
      | .error e => throw e
      | .ok after => pure ⟨after, start ▸ gasHeld_runFrame_le h⟩
termination_by (message.gas, 0)

/-- Run the creation `message` at fork `fork`, from the state and the substate it starts from.

The frame that ends the creation has at most the gas of the message. -/
def processCreateMessage [LawfulGasMeter Meter] (fork : Fork) (message : Message fork)
    (state : TransactionState) (substate : Substate) :
    Except EvmError { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas } := do
  let prepared ← prepareCreation fork state message.currentTarget
  let ⟨evm, used⟩ ← processMessage fork message prepared substate
  match h : depositCode fork state evm with
  | .error e => throw e
  | .ok after => pure ⟨after, Nat.le_trans (gasHeld_depositCode_le h) used⟩
termination_by (message.gas, 1)

end

end EthLib.Execution.Evm
