module

public import EthLib.Base.Address
public import EthLib.Execution.Evm.Stack

/-!
# `Evm.Frame`

The state of one execution of code by the EVM, and the message that starts it.

The gas meter is a parameter, because a fork can change how an instruction pays.

Up to Fusaka, the meter is one counter of the gas left.

The world state, the environments and the access sets are not here yet.

The subsection Machine State of the Yellow Paper, Shanghai version, defines this state.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address U256)

/-- A gas meter: how an instruction pays its gas, and the gas left. -/
class GasMeter (Meter : Type) where
  /-- The meter after a charge of `amount`, or out of gas when it holds less. -/
  charge : Meter → Nat → Except EvmError Meter
  /-- The gas left, which the GAS instruction pushes. -/
  gasLeft : Meter → Nat

/-- The meter of every fork up to Fusaka: one counter of the gas left. -/
instance : GasMeter Nat where
  charge gas amount := if gas < amount then .error .outOfGas else .ok (gas - amount)
  gasLeft gas := gas

/-- A message: a call to an account, or the creation of a contract. -/
structure Message where
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

/-- The state of one frame of execution, with a gas meter of type `Meter`. -/
structure Evm (Meter : Type) where
  /-- The program counter: the index in the code of the next opcode. -/
  pc : Nat
  /-- The stack. -/
  stack : Stack
  /-- The memory, whose size is a multiple of 32. -/
  memory : ByteArray
  /-- The code that runs. -/
  code : ByteArray
  /-- The gas meter. -/
  gas : Meter
  /-- Whether the frame still runs. -/
  running : Bool
  /-- The message that starts the frame. -/
  message : Message
  /-- The data that RETURN or REVERT gives back. -/
  output : ByteArray
  /-- The data that the last call or creation of this frame gave back. -/
  returnData : ByteArray
  /-- The gas to give back at the end of the transaction, which can be negative within a frame. -/
  refundCounter : Int
  /-- The error that stops the frame, if any. -/
  error : Option EvmError

/-- The frame after a charge of `amount` gas, or out of gas. -/
def chargeGas {Meter : Type} [GasMeter Meter] (evm : Evm Meter) (amount : Nat) :
    Except EvmError (Evm Meter) := do
  let gas ← GasMeter.charge evm.gas amount
  return { evm with gas }

end EthLib.Execution.Evm
