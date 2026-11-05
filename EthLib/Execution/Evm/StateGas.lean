module

public import EthLib.Execution.Evm.Errors

/-!
# `Evm.StateGas`

The gas meter of Glamsterdam, which meters state gas beside execution gas, by EIP-8037.

A state creation pays state gas: a new account, a new storage slot, code, a delegation.

Every other charge pays execution gas.

The state gas of a frame comes from its reservoir first, then from its execution gas.

The meter records that second part as a spill, and credits it back first on a refill.

A call passes on its whole reservoir, and the reservoir comes back when the call ends.

A frame that reverts or halts rolls its state gas back to a baseline.

The baseline is the reservoir at the start of the frame, or at the last commit.

A commit marks the state gas so far as kept by a rollback.

Only the top frame commits, for the delegations that a transaction applies before its code.

Source: [EIP-8037][eip8037], its reservoir model and its accounting for halts and reverts.

EIP-8037 has the status Last Call.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

namespace GasCosts

/-- The price of one new byte of state, in state gas: the cost per state byte of EIP-8037. -/
def CPSB : Nat := 1530
/-- The bytes of state that a new storage slot adds, from EIP-8037. -/
def STATE_BYTES_PER_STORAGE_SET : Nat := 64
/-- The bytes of state that a new account adds, from EIP-8037. -/
def STATE_BYTES_PER_NEW_ACCOUNT : Nat := 120
/-- The bytes of state that a delegation of EIP-7702 adds, from EIP-8037. -/
def STATE_BYTES_PER_AUTH_BASE : Nat := 23
/-- The state gas of a new storage slot: 64 bytes of state, the parameter `GAS_STORAGE_SET`. -/
def STORAGE_SET_STATE_GAS : Nat := STATE_BYTES_PER_STORAGE_SET * CPSB
/-- The state gas of a new account: 120 bytes of state, the parameter `GAS_NEW_ACCOUNT`. -/
def NEW_ACCOUNT_STATE_GAS : Nat := STATE_BYTES_PER_NEW_ACCOUNT * CPSB
/-- The state gas of a new delegation indicator of EIP-7702: 23 bytes of state.

It is the parameter `STATE_BYTES_PER_AUTH_BASE × CPSB`. -/
def AUTH_BASE_STATE_GAS : Nat := STATE_BYTES_PER_AUTH_BASE * CPSB
/-- The new storage slots that a system call may write, a margin of EIP-8037. -/
def SYSTEM_MAX_SSTORES_PER_CALL : Nat := 16

end GasCosts

/-- The gas meter of a frame from Glamsterdam: execution gas and state gas, by EIP-8037. -/
structure StateGasMeter where
  /-- The execution gas left, which the GAS instruction pushes. -/
  gasLeft : Nat
  /-- The state gas left in the reservoir. -/
  reservoir : Nat
  /-- The reservoir that a rollback puts back. -/
  baseline : Nat
  /-- The state gas paid from execution gas and not yet credited back.

  EIP-8037 names it the state gas from the gas left. -/
  spill : Nat
  /-- The spill that a commit marks as kept by a rollback. -/
  committed : Nat
  /-- The reservoir at the start of the frame. -/
  grant : Nat
  deriving DecidableEq, Repr

namespace StateGasMeter

/-- The meter of a frame that starts with `gas` execution gas and a reservoir of `reservoir`. -/
def start (gas reservoir : Nat) : StateGasMeter :=
  ⟨gas, reservoir, reservoir, 0, 0, reservoir⟩

/-- The meter after a charge of `amount` execution gas, or out of gas. -/
def charge (meter : StateGasMeter) (amount : Nat) : Except EvmError StateGasMeter :=
  if meter.gasLeft < amount then .error .outOfGas
  else .ok { meter with gasLeft := meter.gasLeft - amount }

/-- The meter after a charge of `amount` state gas, or out of gas.

The charge takes the reservoir first.

Past the reservoir, it takes execution gas, and adds that part to the spill. -/
def chargeState (meter : StateGasMeter) (amount : Nat) : Except EvmError StateGasMeter :=
  if amount ≤ meter.reservoir then .ok { meter with reservoir := meter.reservoir - amount }
  else if amount ≤ meter.reservoir + meter.gasLeft then
    let rest := amount - meter.reservoir
    .ok { meter with reservoir := 0, gasLeft := meter.gasLeft - rest, spill := meter.spill + rest }
  else .error .outOfGas

/-- The meter after a refill of `amount` state gas, for a state creation that is undone.

The refill credits the pools in the reverse order of a charge.

It credits execution gas first, up to the spill, and the rest goes to the reservoir. -/
def refill (meter : StateGasMeter) (amount : Nat) : StateGasMeter :=
  let back := min amount meter.spill
  { meter with
    gasLeft := meter.gasLeft + back
    spill := meter.spill - back
    reservoir := meter.reservoir + (amount - back) }

/-- The meter after a commit: a rollback keeps the state gas paid so far.

The spill moves to the committed part, and the baseline becomes the reservoir. -/
def commit (meter : StateGasMeter) : StateGasMeter :=
  { meter with committed := meter.committed + meter.spill, baseline := meter.reservoir, spill := 0 }

/-- The meter after a rollback to the baseline, when the frame reverts or halts.

The spill returns to execution gas, and the reservoir becomes the baseline. -/
def restore (meter : StateGasMeter) : StateGasMeter :=
  { meter with gasLeft := meter.gasLeft + meter.spill, spill := 0, reservoir := meter.baseline }

/-- The meter after a rollback to the start of the frame, which also undoes the commits.

The transaction uses it when it fails before its first frame runs. -/
def restoreToEntry (meter : StateGasMeter) : StateGasMeter :=
  { meter with
    gasLeft := meter.gasLeft + meter.spill + meter.committed
    spill := 0
    committed := 0
    reservoir := meter.grant
    baseline := meter.grant }

/-- The meter after an exceptional halt: a rollback, then no execution gas left. -/
def halt (meter : StateGasMeter) : StateGasMeter :=
  { meter.restore with gasLeft := 0 }

/-- The meter after the reservoir pays back the spill, as far as both go.

A refill can reach the reservoir while execution gas paid the charge it undoes.

The merge of a child that succeeds moves that gas back. -/
def repay (meter : StateGasMeter) : StateGasMeter :=
  let back := min meter.reservoir meter.spill
  { meter with
    gasLeft := meter.gasLeft + back
    reservoir := meter.reservoir - back
    spill := meter.spill - back }

/-- The meter of a frame that passes on its whole reservoir to a message. -/
def drain (meter : StateGasMeter) : StateGasMeter :=
  { meter with reservoir := 0 }

/-- The caller and the child at the start of a call that passes on `gas` execution gas.

The caller has already paid `gas`.

The child gets the whole reservoir of the caller, which keeps none of it. -/
def enter (meter : StateGasMeter) (gas : Nat) : StateGasMeter × StateGasMeter :=
  (meter.drain, start gas meter.reservoir)

/-- The caller after a child that never ran: it gets back the gas and the reservoir of the child. -/
def cancel (caller child : StateGasMeter) : StateGasMeter :=
  { caller with
    gasLeft := caller.gasLeft + child.gasLeft
    reservoir := caller.reservoir + child.reservoir }

/-- The caller after its child ends with the meter `child`.

The caller gets back the execution gas, the reservoir and the spill of the child.

A child that failed has already rolled back.

The merge of a child that succeeds then repays the spill from the reservoir. -/
def absorb (caller child : StateGasMeter) (succeeded : Bool) : StateGasMeter :=
  let merged :=
    { caller with
      gasLeft := caller.gasLeft + child.gasLeft
      reservoir := caller.reservoir + child.reservoir
      spill := caller.spill + child.spill }
  if succeeded then merged.repay else merged

/-- The execution gas that the meter holds: the gas left, and the spill a rollback credits back.

Charges of state gas, refills and rollbacks keep it, and a charge of execution gas lowers it. -/
def gasHeld (meter : StateGasMeter) : Nat :=
  meter.gasLeft + meter.spill

/-- The net state gas that the frame has used since it started, which can be negative.

It is the reservoir drawn since the start, plus the spill, committed or not.

Of the top frame at the end, it is the state gas that the transaction used. -/
def stateGasUsed (meter : StateGasMeter) : Int :=
  (meter.grant : Int) - meter.reservoir + meter.spill + meter.committed

end StateGasMeter

end EthLib.Execution.Evm
