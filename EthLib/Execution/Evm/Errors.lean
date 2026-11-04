module

/-!
# `Evm.Errors`

The ways in which the execution of EVM code can stop before its end.

A revert keeps the gas left and returns data.

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
  /-- A creation targets an address that already has code or a nonce. -/
  | addressCollision
  /-- The point evaluation precompile rejects its proof. -/
  | kzgProofError
  /-- REVERT stops the frame, which keeps its gas left. -/
  | revert
  deriving DecidableEq, Repr

end EthLib.Execution.Evm
