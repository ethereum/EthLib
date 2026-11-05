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

A message runs each message of its code in the same way, with less gas than it has.

So the recursion of messages ends, by the gas of the message.

Before Paris, a message gives its target an empty account when it has none.

From Spurious Dragon, the transaction deletes such an account at its end, by EIP-161.

From Paris, EIP-7523 forbids empty accounts, so the message creates none.

A precompile charges its price, and its failure is an exceptional halt.

The caller checks the depth of the message and the balance it sends before the message runs.

The section Message Call of the Yellow Paper, Shanghai version, defines the execution of a message.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The substate that a message starts from: no log, no refund, and the accesses so far. -/
def Substate.child (substate : Substate) : Substate :=
  { Substate.empty with
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
  gas := GasMeter.start message.gas
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
theorem gasLeft_runPrecompile_le [LawfulGasMeter Meter] {address : Nat}
    {evm after : Evm fork Meter} (h : runPrecompile fork address evm = some after) :
    GasMeter.gasLeft after.gas ≤ GasMeter.gasLeft evm.gas := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    simp only [exceptionalHalt, LawfulGasMeter.gasLeft_exhaust]
    exact Nat.zero_le _
  · split at h
    · cases h
      simp only [exceptionalHalt, LawfulGasMeter.gasLeft_exhaust]
      exact Nat.zero_le _
    · rename_i hc
      cases h
      exact Nat.le_trans (Nat.le_add_right _ _) (LawfulGasMeter.gasLeft_charge hc)

/-- The address of the precompile that a message calls at fork `fork`, or none. -/
def precompileAddress (fork : Fork) (message : Message fork) : Option Nat :=
  match message.codeAddress with
  | some address =>
    let number := address.toU256.toNat
    if Precompiles.isPrecompile fork number then some number else none
  | none => none

/-- The frame that ends a message, with the writes of `snapshot` back when the message failed. -/
def rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) : Evm fork Meter :=
  if evm.error.isSome then { evm with state := evm.state.restoreTxState snapshot } else evm

/-- Run a message at fork `fork`, from the state and the substate it starts from.

The frame that ends the message has at most the gas of the message.

The run fails only with an error that aborts the whole execution. -/
def processMessage [LawfulGasMeter Meter] (fork : Fork) (message : Message fork)
    (state : TransactionState) (substate : Substate) :
    Except EvmError { evm : Evm fork Meter // GasMeter.gasLeft evm.gas ≤ message.gas } :=
  let rollback (ended : { evm : Evm fork Meter // GasMeter.gasLeft evm.gas ≤ message.gas }) :
      { evm : Evm fork Meter // GasMeter.gasLeft evm.gas ≤ message.gas } :=
    ⟨rollbackOnError state ended.val, by
      unfold rollbackOnError
      split
      · exact ended.property
      · exact ended.property⟩
  Except.map rollback do
    let state := if fork < .paris then state.touchAccount message.currentTarget else state
    let state ←
      if message.shouldTransferValue ∧ message.value ≠ 0 then
        (state.moveEther fork message.caller message.currentTarget message.value).mapError .state
      else pure state
    let evm : Evm fork Meter := startFrame message state substate
    have start : GasMeter.gasLeft evm.gas = message.gas := LawfulGasMeter.gasLeft_start _
    match precompileAddress fork message with
    | some address =>
      if message.disablePrecompiles then
        pure ⟨{ evm with running := false }, Nat.le_of_eq start⟩
      else
        match h : runPrecompile fork address evm with
        | some after => pure ⟨after, start ▸ gasLeft_runPrecompile_le h⟩
        | none => pure ⟨{ evm with running := false }, Nat.le_of_eq start⟩
    | none =>
      match h : runFrame (step fork) (step_decreases fork) message.gas
          (fun caller child _ => processMessage fork child caller.state caller.substate.child)
          evm (Nat.le_of_eq start) with
      | .error e => throw e
      | .ok after => pure ⟨after, start ▸ gasLeft_runFrame_le h⟩
termination_by message.gas

/-- The address of the RIPEMD-160 precompile, 0x03. -/
def RIPEMD160_ADDRESS : Address := Vector.ofFn fun i => if i.val = 19 then 3 else 0

/-- The accounts that a failed message leaves touched, from Spurious Dragon to Paris.

A failed message undoes its touches, except one: the precompile at 0x03 stays touched.

Block 2675119 of the main network deleted that empty account after a call to it ran out of gas.

The rule keeps that history, and applies when the child touched 0x03 or was a call to it. -/
def touchedOnError (fork : Fork) (caller child : Evm fork Meter) : Std.ExtTreeSet Address :=
  let touched := caller.substate.touchedAccounts
  if fork ≥ .spuriousDragon ∧ fork < .paris ∧
      (RIPEMD160_ADDRESS ∈ child.substate.touchedAccounts ∨
        (child.message.currentTarget = RIPEMD160_ADDRESS ∧
          child.state.accountExistsAndIsEmpty RIPEMD160_ADDRESS)) then
    touched.insert RIPEMD160_ADDRESS
  else touched

/-- The accounts that a successful message leaves touched.

From Spurious Dragon to Paris, they gain those of the child, and its target when that is empty. -/
def touchedOnSuccess (fork : Fork) (caller child : Evm fork Meter) : Std.ExtTreeSet Address :=
  let touched := caller.substate.touchedAccounts
  if fork ≥ .spuriousDragon ∧ fork < .paris then
    let touched := touched.insertMany child.substate.touchedAccounts.toList
    if child.state.accountExistsAndIsEmpty child.message.currentTarget then
      touched.insert child.message.currentTarget
    else touched
  else touched

/-- The calling frame after the message it ran ends with the frame `child`.

The caller gets back the gas left of the child, and the state that the child leaves.

A child that succeeds also passes on its logs, its refund, its accounts to delete and its accesses.

A child that fails passes on none of them. -/
def incorporateChild (fork : Fork) (caller child : Evm fork Meter) : Evm fork Meter :=
  let gas := GasMeter.credit caller.gas (GasMeter.gasLeft child.gas)
  if child.error.isNone then
    { caller with
      gas
      state := child.state
      substate := {
        accountsToDelete :=
          caller.substate.accountsToDelete.insertMany child.substate.accountsToDelete.toList
        logs := caller.substate.logs ++ child.substate.logs
        touchedAccounts := touchedOnSuccess fork caller child
        refundCounter := caller.substate.refundCounter + child.substate.refundCounter
        accessedAddresses := child.substate.accessedAddresses
        accessedStorageKeys := child.substate.accessedStorageKeys } }
  else
    { caller with
      gas
      state := child.state
      substate := { caller.substate with touchedAccounts := touchedOnError fork caller child } }

/-- The caller gets back exactly the gas left of the child. -/
theorem gasLeft_incorporateChild [LawfulGasMeter Meter] (caller child : Evm fork Meter) :
    GasMeter.gasLeft (incorporateChild fork caller child).gas =
      GasMeter.gasLeft caller.gas + GasMeter.gasLeft child.gas := by
  unfold incorporateChild
  split <;> exact LawfulGasMeter.gasLeft_credit _ _

end EthLib.Execution.Evm
