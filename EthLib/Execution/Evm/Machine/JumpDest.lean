module

public import EthLib.Execution.Evm.Machine.Memory
public import EthLib.Execution.Evm.Op

/-!
# `Evm.Machine.JumpDest`

The valid jump destinations of code: the JUMPDEST bytes at the start of an opcode.

A scan reads the code from its first byte, one opcode at a time.

A PUSH1 to PUSH32 opcode skips its data, so a byte `0x5b` in that data is no destination.

Every other byte, a valid opcode or not, takes one position.

The scan is the same at every fork, because JUMPDEST and PUSH1 to PUSH32 date from Frontier.

The subsection Jump Destination Validity of the Yellow Paper, Shanghai version, defines it.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (byteAt)

/-- The byte of JUMPDEST. -/
def JUMPDEST : UInt8 := 0x5b

/-- The position of the opcode after the one at `pc`, past the data of a PUSH. -/
def nextOpcode (code : ByteArray) (pc : Nat) : Nat :=
  match Op.decode (byteAt code pc) with
  -- PUSHn has `n` bytes of data, and PUSH0 has none.
  | some (.push n) => pc + n.val + 1
  | _ => pc + 1

/-- The positions of the opcodes of the code from `pc`, scanning at most `fuel` opcodes. -/
def opcodePositionsFrom (code : ByteArray) : (fuel pc : Nat) → List Nat
  | 0, _ => []
  | fuel + 1, pc =>
    if pc < code.size then pc :: opcodePositionsFrom code fuel (nextOpcode code pc) else []

/-- The positions of the opcodes of the code.

Each opcode takes at least one byte, so the size of the code bounds the number of steps. -/
def opcodePositions (code : ByteArray) : List Nat :=
  opcodePositionsFrom code code.size 0

/-- The flags with each JUMPDEST set that starts an opcode of the code from `pc`.

It scans at most `fuel` opcodes, the same positions as the list of opcode positions.

It calls itself only last, so a scan of millions of opcodes needs no deep stack. -/
def markJumpDestsFrom (code : ByteArray) : (fuel pc : Nat) → Array Bool → Array Bool
  | 0, _, flags => flags
  | fuel + 1, pc, flags =>
    if pc < code.size then
      markJumpDestsFrom code fuel (nextOpcode code pc)
        (if byteAt code pc = JUMPDEST then flags.set! pc true else flags)
    else flags

/-- The valid jump destinations of the code, as one flag for each position.

A flag is true when an opcode starts at the position and the byte there is JUMPDEST. -/
def validJumpDestinations (code : ByteArray) : Array Bool :=
  markJumpDestsFrom code code.size 0 (Array.replicate code.size false)

/-- Whether a position is a valid jump destination, given the flags of the code. -/
def isValidJumpDest (flags : Array Bool) (pc : Nat) : Bool :=
  flags.getD pc false

end EthLib.Execution.Evm
