module

public import EthLib.Base.Fork

/-!
# `Evm.Op`

The opcodes of the EVM, from Frontier to Fusaka.

Each opcode is one byte of code, and a fork can add opcodes.

So a byte decodes to an opcode only from the fork that adds that opcode.

No fork up to Fusaka removes an opcode or gives a byte to another opcode.

Appendix H.2 of the Yellow Paper, Shanghai version, lists the opcodes up to Shanghai.

The EIP that adds a later opcode gives its byte.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

/-- An opcode of the EVM at some fork. -/
inductive Op where
  | stop
  | add
  | mul
  | sub
  | div
  | sdiv
  | mod
  | smod
  | addmod
  | mulmod
  | exp
  | signextend
  | lt
  | gt
  | slt
  | sgt
  | eq
  | iszero
  | and
  | or
  | xor
  | not
  | byte
  | shl
  | shr
  | sar
  | clz
  | keccak256
  | address
  | balance
  | origin
  | caller
  | callvalue
  | calldataload
  | calldatasize
  | calldatacopy
  | codesize
  | codecopy
  | gasprice
  | extcodesize
  | extcodecopy
  | returndatasize
  | returndatacopy
  | extcodehash
  | blockhash
  | coinbase
  | timestamp
  | number
  /-- PREVRANDAO, which is DIFFICULTY before Paris, by EIP-4399. -/
  | prevrandao
  | gaslimit
  | chainid
  | selfbalance
  | basefee
  | blobhash
  | blobbasefee
  | pop
  | mload
  | mstore
  | mstore8
  | sload
  | sstore
  | jump
  | jumpi
  | pc
  | msize
  | gas
  | jumpdest
  | tload
  | tstore
  | mcopy
  /-- PUSHn, which pushes the next `n` bytes of code, for `n` from 0 to 32. -/
  | push (n : Fin 33)
  /-- DUP(n + 1), which copies the item at depth `n` of the stack to its top. -/
  | dup (n : Fin 16)
  /-- SWAP(n + 1), which exchanges the top of the stack with the item at depth `n + 1`. -/
  | swap (n : Fin 16)
  /-- LOGn, which emits a log with `n` topics, for `n` from 0 to 4. -/
  | log (n : Fin 5)
  | create
  | call
  | callcode
  | «return»
  | delegatecall
  | create2
  | staticcall
  | revert
  | selfdestruct
  deriving DecidableEq, Repr

namespace Op

/-- The byte of an opcode. -/
def toByte : Op → UInt8
  | .stop => 0x00
  | .add => 0x01
  | .mul => 0x02
  | .sub => 0x03
  | .div => 0x04
  | .sdiv => 0x05
  | .mod => 0x06
  | .smod => 0x07
  | .addmod => 0x08
  | .mulmod => 0x09
  | .exp => 0x0a
  | .signextend => 0x0b
  | .lt => 0x10
  | .gt => 0x11
  | .slt => 0x12
  | .sgt => 0x13
  | .eq => 0x14
  | .iszero => 0x15
  | .and => 0x16
  | .or => 0x17
  | .xor => 0x18
  | .not => 0x19
  | .byte => 0x1a
  | .shl => 0x1b
  | .shr => 0x1c
  | .sar => 0x1d
  | .clz => 0x1e
  | .keccak256 => 0x20
  | .address => 0x30
  | .balance => 0x31
  | .origin => 0x32
  | .caller => 0x33
  | .callvalue => 0x34
  | .calldataload => 0x35
  | .calldatasize => 0x36
  | .calldatacopy => 0x37
  | .codesize => 0x38
  | .codecopy => 0x39
  | .gasprice => 0x3a
  | .extcodesize => 0x3b
  | .extcodecopy => 0x3c
  | .returndatasize => 0x3d
  | .returndatacopy => 0x3e
  | .extcodehash => 0x3f
  | .blockhash => 0x40
  | .coinbase => 0x41
  | .timestamp => 0x42
  | .number => 0x43
  | .prevrandao => 0x44
  | .gaslimit => 0x45
  | .chainid => 0x46
  | .selfbalance => 0x47
  | .basefee => 0x48
  | .blobhash => 0x49
  | .blobbasefee => 0x4a
  | .pop => 0x50
  | .mload => 0x51
  | .mstore => 0x52
  | .mstore8 => 0x53
  | .sload => 0x54
  | .sstore => 0x55
  | .jump => 0x56
  | .jumpi => 0x57
  | .pc => 0x58
  | .msize => 0x59
  | .gas => 0x5a
  | .jumpdest => 0x5b
  | .tload => 0x5c
  | .tstore => 0x5d
  | .mcopy => 0x5e
  | .push n => (0x5f + n.val).toUInt8
  | .dup n => (0x80 + n.val).toUInt8
  | .swap n => (0x90 + n.val).toUInt8
  | .log n => (0xa0 + n.val).toUInt8
  | .create => 0xf0
  | .call => 0xf1
  | .callcode => 0xf2
  | .«return» => 0xf3
  | .delegatecall => 0xf4
  | .create2 => 0xf5
  | .staticcall => 0xfa
  | .revert => 0xfd
  | .selfdestruct => 0xff

/-- The fork that adds an opcode. -/
def since : Op → Fork
  -- EIP-7
  | .delegatecall => .homestead
  -- EIP-211, EIP-214 and EIP-140
  | .returndatasize | .returndatacopy | .staticcall | .revert => .byzantium
  -- EIP-145, EIP-1052 and EIP-1014
  | .shl | .shr | .sar | .extcodehash | .create2 => .constantinople
  -- EIP-1344 and EIP-1884
  | .chainid | .selfbalance => .istanbul
  -- EIP-3198
  | .basefee => .london
  -- EIP-3855 adds PUSH0, and the other pushes date from Frontier.
  | .push n => if n = 0 then .shapella else .frontier
  -- EIP-4844, EIP-7516, EIP-1153 and EIP-5656
  | .blobhash | .blobbasefee | .tload | .tstore | .mcopy => .dencun
  -- EIP-7939
  | .clz => .fusaka
  | _ => .frontier

/-- The opcode of a byte, at the fork that adds that opcode or later, or none. -/
def decode (byte : UInt8) : Option Op :=
  let b := byte.toNat
  if h : 0x5f ≤ b ∧ b ≤ 0x7f then some (.push ⟨b - 0x5f, by omega⟩)
  else if h : 0x80 ≤ b ∧ b ≤ 0x8f then some (.dup ⟨b - 0x80, by omega⟩)
  else if h : 0x90 ≤ b ∧ b ≤ 0x9f then some (.swap ⟨b - 0x90, by omega⟩)
  else if h : 0xa0 ≤ b ∧ b ≤ 0xa4 then some (.log ⟨b - 0xa0, by omega⟩)
  else match b with
    | 0x00 => some .stop
    | 0x01 => some .add
    | 0x02 => some .mul
    | 0x03 => some .sub
    | 0x04 => some .div
    | 0x05 => some .sdiv
    | 0x06 => some .mod
    | 0x07 => some .smod
    | 0x08 => some .addmod
    | 0x09 => some .mulmod
    | 0x0a => some .exp
    | 0x0b => some .signextend
    | 0x10 => some .lt
    | 0x11 => some .gt
    | 0x12 => some .slt
    | 0x13 => some .sgt
    | 0x14 => some .eq
    | 0x15 => some .iszero
    | 0x16 => some .and
    | 0x17 => some .or
    | 0x18 => some .xor
    | 0x19 => some .not
    | 0x1a => some .byte
    | 0x1b => some .shl
    | 0x1c => some .shr
    | 0x1d => some .sar
    | 0x1e => some .clz
    | 0x20 => some .keccak256
    | 0x30 => some .address
    | 0x31 => some .balance
    | 0x32 => some .origin
    | 0x33 => some .caller
    | 0x34 => some .callvalue
    | 0x35 => some .calldataload
    | 0x36 => some .calldatasize
    | 0x37 => some .calldatacopy
    | 0x38 => some .codesize
    | 0x39 => some .codecopy
    | 0x3a => some .gasprice
    | 0x3b => some .extcodesize
    | 0x3c => some .extcodecopy
    | 0x3d => some .returndatasize
    | 0x3e => some .returndatacopy
    | 0x3f => some .extcodehash
    | 0x40 => some .blockhash
    | 0x41 => some .coinbase
    | 0x42 => some .timestamp
    | 0x43 => some .number
    | 0x44 => some .prevrandao
    | 0x45 => some .gaslimit
    | 0x46 => some .chainid
    | 0x47 => some .selfbalance
    | 0x48 => some .basefee
    | 0x49 => some .blobhash
    | 0x4a => some .blobbasefee
    | 0x50 => some .pop
    | 0x51 => some .mload
    | 0x52 => some .mstore
    | 0x53 => some .mstore8
    | 0x54 => some .sload
    | 0x55 => some .sstore
    | 0x56 => some .jump
    | 0x57 => some .jumpi
    | 0x58 => some .pc
    | 0x59 => some .msize
    | 0x5a => some .gas
    | 0x5b => some .jumpdest
    | 0x5c => some .tload
    | 0x5d => some .tstore
    | 0x5e => some .mcopy
    | 0xf0 => some .create
    | 0xf1 => some .call
    | 0xf2 => some .callcode
    | 0xf3 => some .«return»
    | 0xf4 => some .delegatecall
    | 0xf5 => some .create2
    | 0xfa => some .staticcall
    | 0xfd => some .revert
    | 0xff => some .selfdestruct
    | _ => none

/-- The opcode of a byte at a fork, or none when the fork has no opcode with that byte. -/
def ofByte (fork : Fork) (byte : UInt8) : Option Op :=
  (decode byte).filter fun op => op.since ≤ fork

end Op

end EthLib.Execution.Evm
