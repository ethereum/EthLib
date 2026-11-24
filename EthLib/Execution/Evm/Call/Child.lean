module

public import EthLib.Execution.Evm.Machine.Frame

/-!
# `Evm.Call.Child`

The calling frame after the message that it ran, for a call or a creation.

From Spurious Dragon and before Paris, a failed child undoes its touches, except that of 0x03.

The Yellow Paper, Shanghai version, records it in its appendix Anomalies on the Main Network.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The greatest depth of a message: a call or a creation at this depth runs no message. -/
def STACK_DEPTH_LIMIT : Nat := 1024

/-! ## The caller after its callee -/

/-- The address of the RIPEMD-160 precompile, 0x03. -/
def RIPEMD160_ADDRESS : Address := Vector.ofFn fun i => if i.val = 19 then 3 else 0

/-- The accounts that a failed message leaves touched, from Spurious Dragon to Paris.

A failed message undoes its touches, except one: the precompile at 0x03 stays touched.

Block 2675119 of the main network deleted that empty account after a call to it ran out of gas.

The rule keeps that history, and applies when the child touched 0x03 or was a call to it. -/
def touchedOnError (fork : Fork) (caller child : Evm fork Meter) : Std.ExtTreeSet Address :=
  let touched := caller.substate.touchedAccounts
  -- 0x03 stays touched when the child touched it.
  --
  -- It also stays touched when the child was a call to it and its account exists and is empty.
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
    -- The touched accounts of the child join those of the caller.
    let touched := touched.insertMany child.substate.touchedAccounts.toList
    -- The target of the child is touched when its account exists and is empty.
    if child.state.accountExistsAndIsEmpty child.message.currentTarget then
      touched.insert child.message.currentTarget
    else touched
  else touched

/-- The calling frame after the message it ran ends with the frame `child`.

The caller gets back the gas that the child holds, its reservoir, and the state it leaves.

A child that succeeds also passes on its logs, its refund, its accounts to delete and its accesses.

A child that fails passes on none of them. -/
def incorporateChild (fork : Fork) (caller child : Evm fork Meter) : Evm fork Meter :=
  -- The caller gets back the gas left of the child, and its reservoir from Glamsterdam (EIP-8037).
  let gas := GasMeter.absorb caller.gas child.gas child.error.isNone
  if child.error.isNone then
    { caller with
      gas
      state := child.state
      substate := {
        -- The accounts to delete of the child join those of the caller.
        accountsToDelete :=
          caller.substate.accountsToDelete.insertMany child.substate.accountsToDelete.toList
        -- The logs of the child follow those of the caller.
        logs := caller.substate.logs ++ child.substate.logs
        -- No fork defines the logs that a simulation reports; the child's follow the caller's.
        simulatedLogs := caller.substate.simulatedLogs ++ child.substate.simulatedLogs
        touchedAccounts := touchedOnSuccess fork caller child
        -- The refund counter of the child adds to that of the caller.
        refundCounter := caller.substate.refundCounter + child.substate.refundCounter
        -- From Berlin, the accessed addresses and storage keys of the child join the caller's.
        --
        -- The child started from the caller's sets, so its sets hold both.
        accessedAddresses := child.substate.accessedAddresses
        accessedStorageKeys := child.substate.accessedStorageKeys } }
  else
    { caller with
      gas
      state := child.state
      substate := { caller.substate with touchedAccounts := touchedOnError fork caller child } }

/-- The caller gets back exactly the gas that the child holds. -/
theorem gasHeld_incorporateChild [LawfulGasMeter Meter] (caller child : Evm fork Meter) :
    GasMeter.gasHeld (incorporateChild fork caller child).gas =
      GasMeter.gasHeld caller.gas + GasMeter.gasHeld child.gas := by
  unfold incorporateChild
  split <;> exact LawfulGasMeter.gasHeld_absorb _ _ _

/-- The caller runs after its callee exactly when it ran before. -/
theorem running_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).running = caller.running := by
  unfold incorporateChild
  split <;> rfl

end EthLib.Execution.Evm
