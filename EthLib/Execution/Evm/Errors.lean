module

public import EthLib.Execution.ErrorFormat
public import EthLib.Execution.State.Tracker
public import EthLib.Serialization.Rlp.Item

/-!
# `Evm.Errors`

The ways in which the execution of EVM code can stop before its end.

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
  /-- A jump goes to `destination`, which is not a valid jump destination. -/
  | invalidJumpDest (destination : Nat)
  /-- An instruction changes the state in a static frame. -/
  | writeInStaticContext
  /-- RETURNDATACOPY reads `size` bytes from `offset`, past the end of `available` bytes.

  The bytes are those of the return data. -/
  | outOfBoundsRead (offset size available : Nat)
  /-- The immediate byte `immediate` of an instruction is out of its range. -/
  | invalidParameter (immediate : UInt8)
  /-- The code that a creation deploys starts with the byte `0xef`. -/
  | invalidContractPrefix
  /-- A creation targets the address `address`, which already has code or a nonce. -/
  | addressCollision (address : Base.Address)
  /-- The precompile `address`, which the message runs, rejects its input, or lacks gas. -/
  | precompile (address : Nat)
  /-- REVERT stops the frame, which keeps its gas left and returns data. -/
  | revert
  /-- The state lacks data that it must hold, such as the code of a code hash. -/
  | state (e : State.StateError)
  /-- The byte is an opcode at the fork, but its instruction is not yet specified here. -/
  | unspecifiedOpcode (code : UInt8)
  /-- The address of a creation has no RLP preimage, which no nonce below 2^256 gives. -/
  | encoding (e : Serialization.Rlp.RlpError)
  /-- The rules of a transaction at the fork are not yet specified here. -/
  | forkNotYetSpecified (fork : Base.Fork)
  /-- An instruction pushes `value`, a value of the block or the transaction of `2^256` or more.

  No word holds it, and no source says what the instruction does then. -/
  | wordOverflow (value : Nat)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def evmErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Evm.EvmError." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named and each address in hex. -/
def EvmError.reprPrec : EvmError → Nat → Std.Format
  | .stackUnderflow, p => evmErrorFormat "stackUnderflow" [] p
  | .stackOverflow, p => evmErrorFormat "stackOverflow" [] p
  | .outOfGas, p => evmErrorFormat "outOfGas" [] p
  | .invalidOpcode code, p => evmErrorFormat "invalidOpcode" [namedArg "code" code] p
  | .invalidJumpDest destination, p =>
    evmErrorFormat "invalidJumpDest" [namedArg "destination" destination] p
  | .writeInStaticContext, p => evmErrorFormat "writeInStaticContext" [] p
  | .outOfBoundsRead offset size available, p =>
    evmErrorFormat "outOfBoundsRead"
      [namedArg "offset" offset, namedArg "size" size, namedArg "available" available] p
  | .invalidParameter immediate, p =>
    evmErrorFormat "invalidParameter" [namedArg "immediate" immediate] p
  | .invalidContractPrefix, p => evmErrorFormat "invalidContractPrefix" [] p
  | .addressCollision address, p =>
    evmErrorFormat "addressCollision" [namedArg "address" address] p
  | .precompile address, p => evmErrorFormat "precompile" [namedArg "address" address] p
  | .revert, p => evmErrorFormat "revert" [] p
  | .state e, p => evmErrorFormat "state" [reprArg e] p
  | .unspecifiedOpcode code, p => evmErrorFormat "unspecifiedOpcode" [namedArg "code" code] p
  | .encoding e, p => evmErrorFormat "encoding" [reprArg e] p
  | .forkNotYetSpecified fork, p =>
    evmErrorFormat "forkNotYetSpecified" [namedArg "fork" fork] p
  | .wordOverflow value, p => evmErrorFormat "wordOverflow" [namedArg "value" value] p

instance : Repr EvmError := ⟨EvmError.reprPrec⟩

/-- Whether an error aborts the whole execution, instead of halting one frame.

A state that lacks data aborts, and so does an opcode whose instruction is not yet specified.

So does a creation whose address has no preimage, which no nonce below 2^256 gives.

So does a transaction at a fork whose rules are not yet specified.

So does a value of the environment that no word holds. -/
def EvmError.aborts : EvmError → Bool
  | .state _ | .unspecifiedOpcode _ | .encoding _ | .forkNotYetSpecified _ | .wordOverflow _ => true
  -- Every other error is a halt of one frame.
  --
  -- Each of them but a revert is an exceptional halt, which consumes all the gas of the frame.
  | _ => false

end EthLib.Execution.Evm
