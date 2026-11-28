module

public import EthLib.Execution.Evm.Call.Create
public import EthLib.Execution.Evm.Instructions.StackN
public import EthLib.Execution.Evm.Instructions.Storage

/-!
# `Evm.OpTables`

The tables of the opcodes: the words each one takes and leaves, and its constant price at each fork.

Source: Appendix H of [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper, and the EIPs named below.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open GasCosts

namespace Op

/-- The words that the opcode takes from the top of the stack, and the words it leaves there.

None when its immediate byte encodes no depth or pair. -/
def stackWords (op : Op) (immediate : UInt8) : Option (Nat × Nat) :=
  -- Appendix H.2: `δ` the words taken and `α` the words left, in that order.
  match op with
  | .stop | .jumpdest => some (0, 0)
  | .add | .mul | .sub | .div | .sdiv | .mod | .smod | .exp | .signextend | .lt | .gt | .slt
  | .sgt | .eq | .and | .or | .xor | .byte | .shl | .shr | .sar | .keccak256 => some (2, 1)
  | .addmod | .mulmod => some (3, 1)
  -- EIP-7939 gives CLZ one word in and one out.
  | .iszero | .not | .clz | .balance | .calldataload | .extcodesize | .extcodehash | .blockhash
  | .blobhash | .mload | .sload | .tload => some (1, 1)
  -- EIP-7843 gives SLOTNUM no word in and one out, as the other reads of the block.
  | .address | .origin | .caller | .callvalue | .calldatasize | .codesize | .gasprice
  | .returndatasize | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid
  | .selfbalance | .basefee | .blobbasefee | .slotnum | .pc | .msize | .gas | .push _ =>
    some (0, 1)
  | .pop | .jump | .selfdestruct => some (1, 0)
  | .mstore | .mstore8 | .sstore | .jumpi | .tstore | .«return» | .revert => some (2, 0)
  | .calldatacopy | .codecopy | .returndatacopy | .mcopy => some (3, 0)
  | .extcodecopy => some (4, 0)
  -- DUP(n + 1) copies the item at depth `n + 1`, counted from 1, on top.
  | .dup n => some (n.val + 1, n.val + 2)
  -- SWAP(n + 1) exchanges the top with the item `n + 1` below it.
  | .swap n => some (n.val + 2, n.val + 2)
  -- LOGn takes a range of memory and `n` topics.
  | .log n => some (n.val + 2, 0)
  -- A call or a creation leaves one word, which it pushes when it resumes.
  --
  -- One that runs no message pushes that word at once.
  | .create => some (3, 1)
  | .create2 => some (4, 1)
  | .call | .callcode => some (7, 1)
  | .delegatecall | .staticcall => some (6, 1)
  -- EIP-8024: DUPN copies the item at depth `n` on top, as DUPn does.
  | .dupn => (decodeSingle immediate).map fun n => (n, n + 1)
  -- EIP-8024: SWAPN exchanges the top with the item `n` below it, as SWAPn does.
  | .swapn => (decodeSingle immediate).map fun n => (n + 1, n + 1)
  -- EIP-8024: EXCHANGE exchanges the items `n` and `m` below the top, with `n < m`.
  | .exchange => (decodePair immediate).map fun (_, m) => (m + 1, m + 1)

/-- A price that each run of the opcode pays at the fork, whatever its operands, accesses and state.

The rest of its price is dynamic.

It means nothing for an opcode that the fork lacks. -/
def constantGas (fork : Fork) (op : Op) : Nat :=
  match op with
  | .stop | .«return» | .revert => 0
  | .add => OPCODE_ADD
  | .mul => OPCODE_MUL
  | .sub => OPCODE_SUB
  | .div => OPCODE_DIV
  | .sdiv => OPCODE_SDIV
  | .mod => OPCODE_MOD
  | .smod => OPCODE_SMOD
  | .addmod => OPCODE_ADDMOD
  | .mulmod => OPCODE_MULMOD
  -- Appendix H.1: `G_exp`, and the bytes of the exponent are dynamic.
  | .exp => OPCODE_EXP_BASE
  | .signextend => OPCODE_SIGNEXTEND
  | .lt => OPCODE_LT
  | .gt => OPCODE_GT
  | .slt => OPCODE_SLT
  | .sgt => OPCODE_SGT
  | .eq => OPCODE_EQ
  | .iszero => OPCODE_ISZERO
  | .and => OPCODE_AND
  | .or => OPCODE_OR
  | .xor => OPCODE_XOR
  | .not => OPCODE_NOT
  | .byte => OPCODE_BYTE
  | .shl => OPCODE_SHL
  | .shr => OPCODE_SHR
  | .sar => OPCODE_SAR
  | .clz => OPCODE_CLZ
  -- Appendix H.1: `G_keccak256`, and the words hashed and the memory are dynamic.
  | .keccak256 => OPCODE_KECCAK256_BASE
  | .address => OPCODE_ADDRESS
  -- From Berlin, a warm access, and a cold one costs more, by EIP-2929.
  | .balance => balanceCost fork false
  | .origin => OPCODE_ORIGIN
  | .caller => OPCODE_CALLER
  | .callvalue => OPCODE_CALLVALUE
  | .calldataload => OPCODE_CALLDATALOAD
  | .calldatasize => OPCODE_CALLDATASIZE
  -- A copy pays its words and the growth of memory on top.
  | .calldatacopy => OPCODE_CALLDATACOPY_BASE
  | .codesize => OPCODE_CODESIZE
  | .codecopy => OPCODE_CODECOPY_BASE
  | .gasprice => OPCODE_GASPRICE
  | .extcodesize | .extcodecopy => externalBaseCost fork false
  | .returndatasize => OPCODE_RETURNDATASIZE
  | .returndatacopy => OPCODE_RETURNDATACOPY_BASE
  | .extcodehash => extcodehashCost fork false
  | .blockhash => OPCODE_BLOCKHASH
  | .coinbase => OPCODE_COINBASE
  | .timestamp => OPCODE_TIMESTAMP
  | .number => OPCODE_NUMBER
  | .prevrandao => OPCODE_PREVRANDAO
  | .gaslimit => OPCODE_GASLIMIT
  | .chainid => OPCODE_CHAINID
  | .selfbalance => OPCODE_SELFBALANCE
  | .basefee => OPCODE_BASEFEE
  | .blobhash => OPCODE_BLOBHASH
  | .blobbasefee => OPCODE_BLOBBASEFEE
  | .slotnum => OPCODE_SLOTNUM
  | .pop => OPCODE_POP
  | .mload => OPCODE_MLOAD_BASE
  | .mstore => OPCODE_MSTORE_BASE
  | .mstore8 => OPCODE_MSTORE8_BASE
  | .sload => sloadCost fork false
  -- From Istanbul, EIP-2200 prices a write that changes nothing as a read.
  --
  -- From Berlin, that read is a warm access, by EIP-2929.
  --
  -- Before Istanbul, every write that sets no new slot pays the reset price.
  | .sstore => if fork ≥ .istanbul then sstoreReadCost fork else COLD_STORAGE_WRITE
  | .jump => OPCODE_JUMP
  | .jumpi => OPCODE_JUMPI
  | .pc => OPCODE_PC
  | .msize => OPCODE_MSIZE
  | .gas => OPCODE_GAS
  | .jumpdest => OPCODE_JUMPDEST
  | .tload => OPCODE_TLOAD
  | .tstore => OPCODE_TSTORE
  | .mcopy => OPCODE_MCOPY_BASE
  -- EIP-3855 prices PUSH0 as `G_base`, below the other pushes.
  | .push n => if n = 0 then OPCODE_PUSH0 else OPCODE_PUSH
  | .dup _ => OPCODE_DUP
  | .swap _ => OPCODE_SWAP
  -- Appendix H.1: `G_log + n G_logtopic`, and the bytes of data and the memory are dynamic.
  | .log n => OPCODE_LOG_BASE + OPCODE_LOG_TOPIC * n.val
  | .dupn => OPCODE_DUPN
  | .swapn => OPCODE_SWAPN
  | .exchange => OPCODE_EXCHANGE
  -- The init code, the hash of CREATE2 and the gas passed on are dynamic.
  | .create | .create2 => createBaseCost fork
  -- The access, the value, a new account, a delegate and the gas passed on are dynamic.
  | .call | .callcode | .delegatecall | .staticcall => callBaseCost fork false
  -- A cold or a new beneficiary is dynamic.
  | .selfdestruct => (gasSchedule fork).OPCODE_SELFDESTRUCT_BASE

end Op

end EthLib.Execution.Evm
