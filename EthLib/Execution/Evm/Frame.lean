module

public import EthLib.Execution.Blocks.Log
public import EthLib.Execution.Evm.Environment
public import EthLib.Execution.Evm.Stack
public import EthLib.Execution.Evm.StateGas
public import EthLib.Execution.State.Tracker

/-!
# `Evm.Frame`

The state of one execution of code by the EVM, and the message that starts it.

The gas meter is a parameter, because a fork can change how an instruction pays.

Up to BPO5, the meter is one counter of the gas left.

From Glamsterdam, it also meters state gas, with a reservoir, by EIP-8037.

A charge of state gas that the reservoir cannot cover takes execution gas, as a spill.

A rollback credits the spill back to the execution gas.

So a frame holds its execution gas left plus its spill, and the laws of a meter bound that sum.

A charge of execution gas lowers it by at least its amount.

No other operation inside a frame raises it, and an exceptional halt leaves none.

A frame starts with the execution gas it is given.

A message gives back exactly the gas that its frame holds at its end.

A frame also holds the writes of its transaction so far, and the accrued substate.

The substate gathers what the transaction acts on after its code runs.

The subsections Machine State and Substate of the Yellow Paper, Shanghai version, define them.

[EIP-2929](https://eips.ethereum.org/EIPS/eip-2929#specification) adds the accessed sets.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.Blocks (Log)
open EthLib.Execution.State (TransactionState)

/-- A gas meter: how an instruction pays its gas, and the gas left.

From Glamsterdam, a meter also holds a reservoir of state gas, which a call passes on. -/
class GasMeter (Meter : Type) where
  /-- The meter after a charge of `amount` execution gas, or out of gas when it holds less. -/
  charge : Meter → Nat → Except EvmError Meter
  /-- The meter after a charge of `amount` state gas, or out of gas when it holds less. -/
  chargeState : Meter → Nat → Except EvmError Meter
  /-- The meter after a refill of `amount` state gas, for a state creation that is undone. -/
  refill : Meter → Nat → Meter
  /-- The execution gas left, which the GAS instruction pushes. -/
  gasLeft : Meter → Nat
  /-- The execution gas that the frame holds: the gas left, and what a rollback gives back. -/
  gasHeld : Meter → Nat
  /-- The state gas left in the reservoir. -/
  reservoir : Meter → Nat
  /-- The meter after an exceptional halt, which consumes all the execution gas left. -/
  exhaust : Meter → Meter
  /-- The meter after a revert, which rolls back its state gas. -/
  rollback : Meter → Meter
  /-- The meter of a frame that starts with `gas` execution gas and a reservoir of `reservoir`. -/
  start : (gas reservoir : Nat) → Meter
  /-- The meter of a frame that passes on its whole reservoir to a message. -/
  drain : Meter → Meter
  /-- The meter after a message that never ran gives back `gas` and the reservoir `reservoir`. -/
  credit : Meter → (gas reservoir : Nat) → Meter
  /-- The meter after a message that it ran ends with the meter `child`.

  The flag says whether the message succeeded. -/
  absorb : Meter → (child : Meter) → (succeeded : Bool) → Meter

/-- The laws of a gas meter.

They bound the execution gas that a frame holds, which makes the execution end. -/
class LawfulGasMeter (Meter : Type) [GasMeter Meter] : Prop where
  /-- A frame holds at least its execution gas left. -/
  gasLeft_le_gasHeld (meter : Meter) : GasMeter.gasLeft meter ≤ GasMeter.gasHeld meter
  /-- A charge of `amount` execution gas lowers the gas held by at least `amount`. -/
  gasHeld_charge {meter after : Meter} {amount : Nat} :
    GasMeter.charge meter amount = .ok after →
      GasMeter.gasHeld after + amount ≤ GasMeter.gasHeld meter
  /-- A charge of state gas does not raise the gas held. -/
  gasHeld_chargeState {meter after : Meter} {amount : Nat} :
    GasMeter.chargeState meter amount = .ok after → GasMeter.gasHeld after ≤ GasMeter.gasHeld meter
  /-- A refill of state gas does not raise the gas held. -/
  gasHeld_refill (meter : Meter) (amount : Nat) :
    GasMeter.gasHeld (GasMeter.refill meter amount) ≤ GasMeter.gasHeld meter
  /-- An exceptional halt leaves no gas. -/
  gasHeld_exhaust (meter : Meter) : GasMeter.gasHeld (GasMeter.exhaust meter) = 0
  /-- A revert does not raise the gas held. -/
  gasHeld_rollback (meter : Meter) :
    GasMeter.gasHeld (GasMeter.rollback meter) ≤ GasMeter.gasHeld meter
  /-- A frame starts with the execution gas it is given. -/
  gasHeld_start (gas reservoir : Nat) :
    GasMeter.gasHeld (GasMeter.start (Meter := Meter) gas reservoir) = gas
  /-- Passing on the reservoir keeps the gas held. -/
  gasHeld_drain (meter : Meter) : GasMeter.gasHeld (GasMeter.drain meter) = GasMeter.gasHeld meter
  /-- A message that never ran gives back exactly its execution gas. -/
  gasHeld_credit (meter : Meter) (gas reservoir : Nat) :
    GasMeter.gasHeld (GasMeter.credit meter gas reservoir) = GasMeter.gasHeld meter + gas
  /-- A message that ran gives back exactly the gas its frame holds. -/
  gasHeld_absorb (meter child : Meter) (succeeded : Bool) :
    GasMeter.gasHeld (GasMeter.absorb meter child succeeded) =
      GasMeter.gasHeld meter + GasMeter.gasHeld child

/-- The meter of every fork up to BPO5: one counter of the gas left.

These forks have no state gas, so a charge of state gas is a charge of execution gas.

There is no reservoir, and nothing to refill or to roll back. -/
instance : GasMeter Nat where
  charge gas amount := if gas < amount then .error .outOfGas else .ok (gas - amount)
  chargeState gas amount := if gas < amount then .error .outOfGas else .ok (gas - amount)
  refill gas _ := gas
  gasLeft gas := gas
  gasHeld gas := gas
  reservoir _ := 0
  exhaust _ := 0
  rollback gas := gas
  start gas _ := gas
  drain gas := gas
  credit gas amount _ := gas + amount
  absorb gas child _ := gas + child

/-- One counter of gas obeys the laws of a meter. -/
instance : LawfulGasMeter Nat where
  gasLeft_le_gasHeld _ := Nat.le_refl _
  gasHeld_charge {gas after amount} h := by
    simp only [GasMeter.charge] at h
    split at h
    · cases h
    · cases h
      simp only [GasMeter.gasHeld]
      omega
  gasHeld_chargeState {gas after amount} h := by
    simp only [GasMeter.chargeState] at h
    split at h
    · cases h
    · cases h
      simp only [GasMeter.gasHeld]
      omega
  gasHeld_refill _ _ := Nat.le_refl _
  gasHeld_exhaust _ := rfl
  gasHeld_rollback _ := Nat.le_refl _
  gasHeld_start _ _ := rfl
  gasHeld_drain _ := rfl
  gasHeld_credit _ _ _ := rfl
  gasHeld_absorb _ _ _ := rfl

/-- The meter of every fork from Glamsterdam: execution gas and state gas, by EIP-8037.

The meter of a message starts with the reservoir of its caller, which the caller gives up.

A message that never ran gives the caller back its execution gas and its reservoir.

A message that ran gives back its execution gas, its reservoir and its spill.

A revert rolls the state gas back to the baseline. -/
instance : GasMeter StateGasMeter where
  charge := StateGasMeter.charge
  chargeState := StateGasMeter.chargeState
  refill := StateGasMeter.refill
  gasLeft meter := meter.gasLeft
  gasHeld := StateGasMeter.gasHeld
  reservoir meter := meter.reservoir
  exhaust := StateGasMeter.halt
  rollback := StateGasMeter.restore
  start := StateGasMeter.start
  drain := StateGasMeter.drain
  credit meter gas reservoir := StateGasMeter.cancel meter (StateGasMeter.start gas reservoir)
  absorb := StateGasMeter.absorb

/-- The meter of EIP-8037 obeys the laws of a meter. -/
instance : LawfulGasMeter StateGasMeter where
  gasLeft_le_gasHeld meter := Nat.le_add_right meter.gasLeft meter.spill
  gasHeld_charge {meter after amount} h := by
    simp only [GasMeter.charge, StateGasMeter.charge] at h
    split at h
    · cases h
    · cases h
      simp only [GasMeter.gasHeld, StateGasMeter.gasHeld]
      omega
  gasHeld_chargeState {meter after amount} h := by
    simp only [GasMeter.chargeState, StateGasMeter.chargeState] at h
    split at h
    · cases h
      exact Nat.le_refl _
    · split at h
      · cases h
        simp only [GasMeter.gasHeld, StateGasMeter.gasHeld]
        omega
      · cases h
  gasHeld_refill meter amount := by
    simp only [GasMeter.gasHeld, GasMeter.refill, StateGasMeter.gasHeld, StateGasMeter.refill]
    omega
  gasHeld_exhaust _ := rfl
  gasHeld_rollback meter := by
    simp only [GasMeter.gasHeld, GasMeter.rollback, StateGasMeter.gasHeld,
      StateGasMeter.restore]
    omega
  gasHeld_start _ _ := rfl
  gasHeld_drain _ := rfl
  gasHeld_credit meter gas reservoir := by
    simp only [GasMeter.gasHeld, GasMeter.credit, StateGasMeter.gasHeld, StateGasMeter.cancel,
      StateGasMeter.start]
    omega
  gasHeld_absorb meter child succeeded := by
    simp only [GasMeter.gasHeld, GasMeter.absorb, StateGasMeter.gasHeld, StateGasMeter.absorb]
    cases succeeded
    · simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [↓reduceIte, StateGasMeter.repay]
      omega

/-- A message at fork `fork`: a call to an account, or the creation of a contract. -/
structure Message (fork : Fork) where
  /-- The block that runs the code. -/
  blockEnv : BlockEnvironment fork
  /-- The transaction that runs the code. -/
  txEnv : TransactionEnvironment fork
  /-- The account that sends the message. -/
  caller : Address
  /-- The account that the message calls, or none for a creation. -/
  target : Option Address
  /-- The account whose storage and balance the code uses. -/
  currentTarget : Address
  /-- The execution gas that the message has. -/
  gas : Nat
  /-- The state gas that the message has in its reservoir, which is 0 before Glamsterdam. -/
  reservoir : Nat := 0
  /-- The wei that the message sends. -/
  value : U256
  /-- The call data. -/
  data : ByteArray
  /-- The account whose code runs, or none for a creation. -/
  codeAddress : Option Address
  /-- The code that runs. -/
  code : ByteArray
  /-- The number of frames below this one. -/
  depth : Nat
  /-- Whether the message moves its value to the target. -/
  shouldTransferValue : Bool
  /-- Whether the frame must not change the state. -/
  isStatic : Bool
  /-- Whether a call to a precompile address runs its code instead, by EIP-7702. -/
  disablePrecompiles : Bool

/-- What a transaction accrues as its code runs, and acts on once the code ends. -/
structure Substate where
  /-- The accounts to delete at the end of the transaction. -/
  accountsToDelete : Std.ExtTreeSet Address
  /-- The logs, oldest first. -/
  logs : Array Log
  /-- The accounts that the transaction touched, whose empty ones EIP-161 deletes. -/
  touchedAccounts : Std.ExtTreeSet Address
  /-- The gas to give back at the end of the transaction, which can be negative within a frame. -/
  refundCounter : Int
  /-- The addresses that the transaction accessed. -/
  accessedAddresses : Std.ExtTreeSet Address
  /-- The storage keys that the transaction accessed, at each address. -/
  accessedStorageKeys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)

/-- The substate with no account, no log, no refund and no access. -/
def Substate.empty : Substate := ⟨∅, #[], ∅, 0, ∅, ∅⟩

/-- The state of one frame of execution at fork `fork`, with a gas meter of type `Meter`. -/
structure Evm (fork : Fork) (Meter : Type) where
  /-- The program counter: the index in the code of the next opcode. -/
  pc : Nat
  /-- The stack. -/
  stack : Stack
  /-- The memory, whose size is a multiple of 32. -/
  memory : ByteArray
  /-- The code that runs. -/
  code : ByteArray
  /-- The valid jump destinations of the code, one flag for each position.

  The frame must hold the flags that the scan of its code gives, or a jump checks the wrong code. -/
  validJumpDestinations : Array Bool
  /-- The gas meter. -/
  gas : Meter
  /-- Whether the frame still runs. -/
  running : Bool
  /-- The message that starts the frame. -/
  message : Message fork
  /-- The data that RETURN or REVERT gives back. -/
  output : ByteArray
  /-- The data that the last call or creation of this frame gave back. -/
  returnData : ByteArray
  /-- The writes of the transaction so far. -/
  state : TransactionState
  /-- The substate that the transaction has accrued so far. -/
  substate : Substate
  /-- The error that stops the frame, if any. -/
  error : Option EvmError

/-- The frame after a charge of `amount` gas, or out of gas. -/
def chargeGas {fork : Fork} {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter)
    (amount : Nat) : Except EvmError (Evm fork Meter) := do
  let gas ← GasMeter.charge evm.gas amount
  return { evm with gas }

/-- The frame after a charge of `amount` state gas, or out of gas. -/
def chargeStateGas {fork : Fork} {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter)
    (amount : Nat) : Except EvmError (Evm fork Meter) := do
  let gas ← GasMeter.chargeState evm.gas amount
  return { evm with gas }

/-- The frame after a refill of `amount` state gas, for a state creation that is undone. -/
def refillStateGas {fork : Fork} {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter)
    (amount : Nat) : Evm fork Meter :=
  { evm with gas := GasMeter.refill evm.gas amount }

end EthLib.Execution.Evm
