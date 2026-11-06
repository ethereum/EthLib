module

public import EthLib.Execution.State.Tracker
public import EthLib.Serialization.Rlp.Item

/-!
# `Evm.Machine.Errors`

The ways in which the execution of EVM code can stop before its end.

A revert keeps the gas left and returns data.

A state that lacks data it must hold stops the whole execution, and is no halt.

So does a nonce too large for the address of a creation.

So does an opcode whose instruction is not yet specified.

Every other error is an exceptional halt, which consumes all the gas of the frame.

The subsection Exceptional Halting of the Yellow Paper, Shanghai version, lists most of them.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- A reason why the execution of EVM code stops before its end. -/
inductive EvmError where
  /-- An instruction needs more items than the stack holds. -/
  | stackUnderflow
  /-- An instruction pushes onto a stack of 1024 items. -/
  | stackOverflow
  /-- An instruction costs more than the gas left of the frame. -/
  | outOfGas
  /-- The byte at the program counter is no opcode at the fork. -/
  | invalidOpcode (code : UInt8)
  /-- A jump goes to a position that is not a valid jump destination. -/
  | invalidJumpDest
  /-- A call or a creation goes deeper than 1024 frames. -/
  | stackDepthLimit
  /-- An instruction changes the state in a static frame. -/
  | writeInStaticContext
  /-- RETURNDATACOPY reads past the end of the return data. -/
  | outOfBoundsRead
  /-- A parameter of an instruction is out of its range. -/
  | invalidParameter
  /-- The code that a creation deploys starts with the byte `0xef`. -/
  | invalidContractPrefix
  /-- A creation targets an address that already has code, a nonce or storage. -/
  | addressCollision
  /-- A precompiled contract rejects its input, or lacks gas. -/
  | precompile
  /-- REVERT stops the frame, which keeps its gas left. -/
  | revert
  /-- The state lacks data that it must hold, such as the code of a code hash. -/
  | state (e : State.StateError)
  /-- The byte is an opcode at the fork, but its instruction is not yet specified here. -/
  | unspecifiedOpcode (code : UInt8)
  /-- The address of a creation has no RLP preimage, which no nonce below 2^256 gives. -/
  | encoding (e : Serialization.Rlp.RlpError)
  /-- The rules of a transaction at the fork are not yet specified here. -/
  | forkNotYetSpecified (fork : Base.Fork)
  deriving DecidableEq, Repr

/-- Whether an error aborts the whole execution, instead of halting one frame.

A state that lacks data aborts, and so does an opcode whose instruction is not yet specified.

So does a creation whose address has no preimage, which no nonce below 2^256 gives.

So does a transaction at a fork whose rules are not yet specified. -/
def EvmError.aborts : EvmError → Bool
  | .state _ | .unspecifiedOpcode _ | .encoding _ | .forkNotYetSpecified _ => true
  | _ => false

end EthLib.Execution.Evm
