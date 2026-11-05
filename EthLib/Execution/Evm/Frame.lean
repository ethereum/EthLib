module

public import EthLib.Execution.Blocks.Log
public import EthLib.Execution.Evm.Environment
public import EthLib.Execution.Evm.Stack
public import EthLib.Execution.State.Tracker

/-!
# `Evm.Frame`

The state of one execution of code by the EVM, and the message that starts it.

The gas meter is a parameter, because a fork can change how an instruction pays.

Up to Fusaka, the meter is one counter of the gas left.

A meter obeys four laws.

A charge lowers the gas left by at least its amount.

An exceptional halt leaves no gas.

A frame starts with the gas it is given.

A credit of gas raises the gas left by exactly that much.

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

/-- A gas meter: how an instruction pays its gas, and the gas left. -/
class GasMeter (Meter : Type) where
  /-- The meter after a charge of `amount`, or out of gas when it holds less. -/
  charge : Meter → Nat → Except EvmError Meter
  /-- The gas left, which the GAS instruction pushes. -/
  gasLeft : Meter → Nat
  /-- The meter after an exceptional halt, which consumes all the gas left. -/
  exhaust : Meter → Meter
  /-- The meter of a frame that starts with `gas`. -/
  start : Nat → Meter
  /-- The meter after a message that it ran gives back `amount` gas. -/
  credit : Meter → Nat → Meter

/-- The laws of a gas meter. -/
class LawfulGasMeter (Meter : Type) [GasMeter Meter] : Prop where
  /-- A charge of `amount` lowers the gas left by at least `amount`. -/
  gasLeft_charge {meter after : Meter} {amount : Nat} :
    GasMeter.charge meter amount = .ok after →
      GasMeter.gasLeft after + amount ≤ GasMeter.gasLeft meter
  /-- An exceptional halt leaves no gas. -/
  gasLeft_exhaust (meter : Meter) : GasMeter.gasLeft (GasMeter.exhaust meter) = 0
  /-- A frame starts with the gas it is given. -/
  gasLeft_start (gas : Nat) : GasMeter.gasLeft (GasMeter.start (Meter := Meter) gas) = gas
  /-- A credit of `amount` raises the gas left by exactly `amount`. -/
  gasLeft_credit (meter : Meter) (amount : Nat) :
    GasMeter.gasLeft (GasMeter.credit meter amount) = GasMeter.gasLeft meter + amount

/-- The meter of every fork up to Fusaka: one counter of the gas left. -/
instance : GasMeter Nat where
  charge gas amount := if gas < amount then .error .outOfGas else .ok (gas - amount)
  gasLeft gas := gas
  exhaust _ := 0
  start gas := gas
  credit gas amount := gas + amount

/-- One counter of gas obeys the laws of a meter. -/
instance : LawfulGasMeter Nat where
  gasLeft_charge {gas after amount} h := by
    simp only [GasMeter.charge] at h
    split at h
    · cases h
    · cases h
      simp only [GasMeter.gasLeft]
      omega
  gasLeft_exhaust _ := rfl
  gasLeft_start _ := rfl
  gasLeft_credit _ _ := rfl

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
  /-- The gas that the message has. -/
  gas : Nat
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

end EthLib.Execution.Evm
