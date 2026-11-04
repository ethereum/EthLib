module

public import EthLib.Base.U256
public import EthLib.Execution.Evm.Words

/-!
# `Evm.Gas`

The gas prices of the EVM, and the price of memory.

Memory costs 3 gas per 32-byte word plus the square of the words over 512.

So a large memory costs quadratic gas.

An instruction that grows memory pays the price of the new size minus the price of the old size.

Appendix G, Fee Schedule, of the Yellow Paper, Shanghai version, lists most prices.

Appendix H.1 there defines the price of memory and the growth of memory.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

A price that an EIP adds or changes names that EIP:

- [EIP-150](https://eips.ethereum.org/EIPS/eip-150#specification), all but one 64th
- [EIP-1153](https://eips.ethereum.org/EIPS/eip-1153), TLOAD and TSTORE
- [EIP-3855](https://eips.ethereum.org/EIPS/eip-3855), PUSH0
- [EIP-3860](https://eips.ethereum.org/EIPS/eip-3860#parameters), init code
- [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844), BLOBHASH
- [EIP-5656](https://eips.ethereum.org/EIPS/eip-5656), MCOPY
- [EIP-7516](https://eips.ethereum.org/EIPS/eip-7516), BLOBBASEFEE
- [EIP-7623](https://eips.ethereum.org/EIPS/eip-7623#specification), the call data floor
- [EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#parameters), authorizations
- [EIP-7825](https://eips.ethereum.org/EIPS/eip-7825#specification), the gas cap of a transaction
- [EIP-7939](https://eips.ethereum.org/EIPS/eip-7939#specification), CLZ

The prices of the precompiles are with each precompile, and the blob prices with the blob fees.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-! The gas prices of the instructions, of memory, of transactions and of blocks. -/

namespace GasCosts

/-- The price of the base tier of instructions. -/
def BASE : Nat := 2
/-- The price of the very low tier. -/
def VERY_LOW : Nat := 3
/-- The price of the low tier. -/
def LOW : Nat := 5
/-- The price of the mid tier. -/
def MID : Nat := 8
/-- The price of the high tier. -/
def HIGH : Nat := 10

/-- The price to access an account or a storage slot that the transaction already accessed. -/
def WARM_ACCESS : Nat := 100
/-- The price of the first access to an account in a transaction. -/
def COLD_ACCOUNT_ACCESS : Nat := 2600
/-- The price of the first access to a storage slot in a transaction. -/
def COLD_STORAGE_ACCESS : Nat := 2100

/-- The price to change a storage slot whose original value is zero. -/
def STORAGE_SET : Nat := 20000
/-- The price to change a storage slot whose original value is not zero, cold access included. -/
def COLD_STORAGE_WRITE : Nat := 5000

/-- The gas that a call with value gives the callee on top of the gas it passes. -/
def CALL_STIPEND : Nat := 2300
/-- The price to send value with a call. -/
def CALL_VALUE : Nat := 9000
/-- The extra price of a call with value to an account that is not alive. -/
def NEW_ACCOUNT : Nat := 25000

/-- The price per byte of the code that a contract creation stores. -/
def CODE_DEPOSIT_PER_BYTE : Nat := 200
/-- The price per 32-byte word of init code, from EIP-3860. -/
def CODE_INIT_PER_WORD : Nat := 2

/-- The price of each authorization in a transaction, from EIP-7702. -/
def AUTH_PER_EMPTY_ACCOUNT : Nat := 25000

/-- A price of zero. -/
def ZERO : Nat := 0
/-- The linear price per 32-byte word of memory. -/
def MEMORY_PER_WORD : Nat := 3
/-- The price of the fast-step tier. -/
def FAST_STEP : Nat := 5

/-- The refund to clear a storage slot whose original value is not zero. -/
def REFUND_STORAGE_CLEAR : Nat := 4800
/-- An authorization for an account that exists gets back its price minus this, from EIP-7702. -/
def REFUND_AUTH_PER_EXISTING_ACCOUNT : Nat := 12500

/-- The base price of a transaction. -/
def TX_BASE : Nat := 21000
/-- The extra price of a transaction that creates a contract. -/
def TX_CREATE : Nat := 32000
/-- The standard price per token of call data. -/
def TX_DATA_TOKEN_STANDARD : Nat := 4
/-- The floor price per token of call data, from EIP-7623. -/
def TX_DATA_TOKEN_FLOOR : Nat := 10
/-- The price per address of an access list. -/
def TX_ACCESS_LIST_ADDRESS : Nat := 2400
/-- The price per storage key of an access list. -/
def TX_ACCESS_LIST_STORAGE_KEY : Nat := 1900
/-- The largest gas of a transaction, `2^24`, from EIP-7825. -/
def TX_MAX_GAS_LIMIT : Nat := 16777216

/-- A block gas limit differs from its parent's by less than the parent's over this. -/
def LIMIT_ADJUSTMENT_FACTOR : Nat := 1024
/-- The smallest gas limit of a block. -/
def LIMIT_MINIMUM : Nat := 5000

/-- The price of ADD. -/
def OPCODE_ADD : Nat := VERY_LOW
/-- The price of SUB. -/
def OPCODE_SUB : Nat := VERY_LOW
/-- The price of MUL. -/
def OPCODE_MUL : Nat := LOW
/-- The price of DIV. -/
def OPCODE_DIV : Nat := LOW
/-- The price of SDIV. -/
def OPCODE_SDIV : Nat := LOW
/-- The price of MOD. -/
def OPCODE_MOD : Nat := LOW
/-- The price of SMOD. -/
def OPCODE_SMOD : Nat := LOW
/-- The price of ADDMOD. -/
def OPCODE_ADDMOD : Nat := MID
/-- The price of MULMOD. -/
def OPCODE_MULMOD : Nat := MID
/-- The price of SIGNEXTEND. -/
def OPCODE_SIGNEXTEND : Nat := LOW
/-- The price of LT. -/
def OPCODE_LT : Nat := VERY_LOW
/-- The price of GT. -/
def OPCODE_GT : Nat := VERY_LOW
/-- The price of SLT. -/
def OPCODE_SLT : Nat := VERY_LOW
/-- The price of SGT. -/
def OPCODE_SGT : Nat := VERY_LOW
/-- The price of EQ. -/
def OPCODE_EQ : Nat := VERY_LOW
/-- The price of ISZERO. -/
def OPCODE_ISZERO : Nat := VERY_LOW
/-- The price of AND. -/
def OPCODE_AND : Nat := VERY_LOW
/-- The price of OR. -/
def OPCODE_OR : Nat := VERY_LOW
/-- The price of XOR. -/
def OPCODE_XOR : Nat := VERY_LOW
/-- The price of NOT. -/
def OPCODE_NOT : Nat := VERY_LOW
/-- The price of BYTE. -/
def OPCODE_BYTE : Nat := VERY_LOW
/-- The price of SHL. -/
def OPCODE_SHL : Nat := VERY_LOW
/-- The price of SHR. -/
def OPCODE_SHR : Nat := VERY_LOW
/-- The price of SAR. -/
def OPCODE_SAR : Nat := VERY_LOW
/-- The price of CLZ, from EIP-7939. -/
def OPCODE_CLZ : Nat := LOW
/-- The price of JUMP. -/
def OPCODE_JUMP : Nat := MID
/-- The price of JUMPI. -/
def OPCODE_JUMPI : Nat := HIGH
/-- The price of JUMPDEST. -/
def OPCODE_JUMPDEST : Nat := 1
/-- The price of CALLDATALOAD. -/
def OPCODE_CALLDATALOAD : Nat := VERY_LOW
/-- The price of BLOCKHASH. -/
def OPCODE_BLOCKHASH : Nat := 20
/-- The price of COINBASE. -/
def OPCODE_COINBASE : Nat := BASE
/-- The price of POP. -/
def OPCODE_POP : Nat := BASE
/-- The price of MSIZE. -/
def OPCODE_MSIZE : Nat := BASE
/-- The price of PC. -/
def OPCODE_PC : Nat := BASE
/-- The price of GAS. -/
def OPCODE_GAS : Nat := BASE
/-- The price of ADDRESS. -/
def OPCODE_ADDRESS : Nat := BASE
/-- The price of ORIGIN. -/
def OPCODE_ORIGIN : Nat := BASE
/-- The price of CALLER. -/
def OPCODE_CALLER : Nat := BASE
/-- The price of CALLVALUE. -/
def OPCODE_CALLVALUE : Nat := BASE
/-- The price of CALLDATASIZE. -/
def OPCODE_CALLDATASIZE : Nat := BASE
/-- The price of CODESIZE. -/
def OPCODE_CODESIZE : Nat := BASE
/-- The price of GASPRICE. -/
def OPCODE_GASPRICE : Nat := BASE
/-- The price of TIMESTAMP. -/
def OPCODE_TIMESTAMP : Nat := BASE
/-- The price of NUMBER. -/
def OPCODE_NUMBER : Nat := BASE
/-- The price of GASLIMIT. -/
def OPCODE_GASLIMIT : Nat := BASE
/-- The price of PREVRANDAO. -/
def OPCODE_PREVRANDAO : Nat := BASE
/-- The price of RETURNDATASIZE. -/
def OPCODE_RETURNDATASIZE : Nat := BASE
/-- The price of CHAINID. -/
def OPCODE_CHAINID : Nat := BASE
/-- The price of SELFBALANCE. -/
def OPCODE_SELFBALANCE : Nat := FAST_STEP
/-- The price of BASEFEE. -/
def OPCODE_BASEFEE : Nat := BASE
/-- The price of BLOBBASEFEE, from EIP-7516. -/
def OPCODE_BLOBBASEFEE : Nat := BASE
/-- The price of BLOBHASH, from EIP-4844. -/
def OPCODE_BLOBHASH : Nat := 3
/-- The price of PUSH1 to PUSH32. -/
def OPCODE_PUSH : Nat := VERY_LOW
/-- The price of PUSH0, from EIP-3855. -/
def OPCODE_PUSH0 : Nat := BASE
/-- The price of DUP1 to DUP16. -/
def OPCODE_DUP : Nat := VERY_LOW
/-- The price of SWAP1 to SWAP16. -/
def OPCODE_SWAP : Nat := VERY_LOW
/-- The price of TLOAD, from EIP-1153. -/
def OPCODE_TLOAD : Nat := WARM_ACCESS
/-- The price of TSTORE, from EIP-1153. -/
def OPCODE_TSTORE : Nat := WARM_ACCESS

/-- The base price of RETURNDATACOPY. -/
def OPCODE_RETURNDATACOPY_BASE : Nat := VERY_LOW
/-- The price per copied word of RETURNDATACOPY. -/
def OPCODE_RETURNDATACOPY_PER_WORD : Nat := 3
/-- The base price of CALLDATACOPY. -/
def OPCODE_CALLDATACOPY_BASE : Nat := VERY_LOW
/-- The base price of CODECOPY. -/
def OPCODE_CODECOPY_BASE : Nat := VERY_LOW
/-- The base price of MCOPY, from EIP-5656. -/
def OPCODE_MCOPY_BASE : Nat := VERY_LOW
/-- The base price of MLOAD. -/
def OPCODE_MLOAD_BASE : Nat := VERY_LOW
/-- The base price of MSTORE. -/
def OPCODE_MSTORE_BASE : Nat := VERY_LOW
/-- The base price of MSTORE8. -/
def OPCODE_MSTORE8_BASE : Nat := VERY_LOW
/-- The price per copied word of CALLDATACOPY, CODECOPY, EXTCODECOPY and MCOPY. -/
def OPCODE_COPY_PER_WORD : Nat := 3
/-- The base price of CREATE and CREATE2. -/
def OPCODE_CREATE_BASE : Nat := 32000
/-- The base price of EXP. -/
def OPCODE_EXP_BASE : Nat := 10
/-- The price per byte of the exponent of EXP. -/
def OPCODE_EXP_PER_BYTE : Nat := 50
/-- The base price of KECCAK256. -/
def OPCODE_KECCAK256_BASE : Nat := 30
/-- The price per hashed word of KECCAK256. -/
def OPCODE_KECCAK256_PER_WORD : Nat := 6
/-- The base price of LOG0 to LOG4. -/
def OPCODE_LOG_BASE : Nat := 375
/-- The price per logged byte. -/
def OPCODE_LOG_DATA_PER_BYTE : Nat := 8
/-- The price per log topic. -/
def OPCODE_LOG_TOPIC : Nat := 375
/-- The base price of SELFDESTRUCT. -/
def OPCODE_SELFDESTRUCT_BASE : Nat := 5000
/-- The extra price of SELFDESTRUCT that sends a balance to an account that is not alive. -/
def OPCODE_SELFDESTRUCT_NEW_ACCOUNT : Nat := 25000

end GasCosts

open EthLib.Base (U256)
open GasCosts

/-- The price of a memory of `sizeInBytes` bytes.

The size rounds up to whole words.

Each word costs 3, and the square of the words over 512 is added.

Source: the memory cost `C_mem` of Appendix H.1 of the Yellow Paper. -/
def memoryGasCost (sizeInBytes : Nat) : Nat :=
  let sizeInWords := wordCount sizeInBytes
  let linearCost := sizeInWords * MEMORY_PER_WORD
  let quadraticCost := sizeInWords ^ 2 / 512
  linearCost + quadraticCost

/-- What an instruction pays to grow memory, and the number of bytes it grows by. -/
structure ExtendMemory where
  /-- The gas to pay for the growth. -/
  cost : Nat
  /-- The number of bytes that memory grows by. -/
  expandBy : Nat
  deriving DecidableEq, Repr

/-- The growth of a memory of `currentSize` bytes for a list of ranges.

Each range is a start and a size, read in order.

A range of size 0 never grows memory.

A range that ends past the rounded memory grows it to the rounded end of the range.

It pays the price of the new size minus the price of the old size.

Source: the memory growth `M` of Appendix H.1 of the Yellow Paper. -/
def extendMemory (currentSize : Nat) : List (U256 × U256) → ExtendMemory
  | [] => ⟨0, 0⟩
  | (startPosition, size) :: extensions =>
    if size = 0 then
      extendMemory currentSize extensions
    else
      let beforeSize := ceil32 currentSize
      let afterSize := ceil32 (startPosition.toNat + size.toNat)
      if afterSize ≤ beforeSize then
        extendMemory currentSize extensions
      else
        let rest := extendMemory afterSize extensions
        ⟨memoryGasCost afterSize - memoryGasCost beforeSize + rest.cost,
          afterSize - beforeSize + rest.expandBy⟩

/-- The most gas that a call can pass on: all but one 64th of the gas, rounded up.

Source: EIP-150, and the function `L` of Appendix H.1 of the Yellow Paper. -/
def maxMessageCallGas (gas : Nat) : Nat :=
  gas - gas / 64

/-- The price of init code: 2 gas per 32-byte word.

Source: EIP-3860. -/
def initCodeCost (initCodeLength : Nat) : Nat :=
  CODE_INIT_PER_WORD * wordCount initCodeLength

end EthLib.Execution.Evm
