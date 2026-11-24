module

public import EthLib.Base.Denominations
public import EthLib.Base.Fork
public import EthLib.Base.U256
public import EthLib.Execution.Evm.Gas.StateGas
public import EthLib.Execution.Evm.Words

/-!
# `Evm.Gas.Prices`

The gas prices of the EVM, and the other values of the execution layer that change at forks.

Appendix G, Fee Schedule, of the Yellow Paper, Shanghai version, lists most prices.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

Appendix G of its Berlin version, at [`beacfbd`][yp-berlin], gives the refunds before London.

Each price that Appendix G lists names its symbol, such as `G_verylow`.

The price of an instruction in a set of Appendix G names that set `W_*` instead.

A price that an EIP adds or changes names that EIP:

- [EIP-2](https://eips.ethereum.org/EIPS/eip-2#specification), contract creation by a transaction
- [EIP-145](https://eips.ethereum.org/EIPS/eip-145#specification), SHL, SHR and SAR
- [EIP-150](https://eips.ethereum.org/EIPS/eip-150#specification), IO, calls and all but one 64th
- [EIP-160](https://eips.ethereum.org/EIPS/eip-160#specification), EXP
- [EIP-211](https://eips.ethereum.org/EIPS/eip-211#specification), RETURNDATASIZE, RETURNDATACOPY
- [EIP-1014](https://eips.ethereum.org/EIPS/eip-1014#specification), CREATE2
- [EIP-1052](https://eips.ethereum.org/EIPS/eip-1052#specification), EXTCODEHASH
- [EIP-1153](https://eips.ethereum.org/EIPS/eip-1153), TLOAD and TSTORE
- [EIP-1344](https://eips.ethereum.org/EIPS/eip-1344#specification), CHAINID
- [EIP-1884](https://eips.ethereum.org/EIPS/eip-1884#specification), SLOAD, BALANCE, EXTCODEHASH
- [EIP-2028](https://eips.ethereum.org/EIPS/eip-2028#specification), call data
- [EIP-2200](https://eips.ethereum.org/EIPS/eip-2200#specification), the price to reset a slot
- [EIP-2929](https://eips.ethereum.org/EIPS/eip-2929#parameters), cold and warm accesses
- [EIP-2930](https://eips.ethereum.org/EIPS/eip-2930#parameters), access lists
- [EIP-3198](https://eips.ethereum.org/EIPS/eip-3198#specification), BASEFEE
- [EIP-3529](https://eips.ethereum.org/EIPS/eip-3529#specification), refunds
- [EIP-3855](https://eips.ethereum.org/EIPS/eip-3855), PUSH0
- [EIP-3860](https://eips.ethereum.org/EIPS/eip-3860#parameters), init code
- [EIP-4399](https://eips.ethereum.org/EIPS/eip-4399#specification), PREVRANDAO
- [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844), BLOBHASH
- [EIP-5656](https://eips.ethereum.org/EIPS/eip-5656), MCOPY
- [EIP-7516](https://eips.ethereum.org/EIPS/eip-7516), BLOBBASEFEE
- [EIP-7623](https://eips.ethereum.org/EIPS/eip-7623#specification), the call data floor
- [EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#parameters), authorizations
- [EIP-7825](https://eips.ethereum.org/EIPS/eip-7825#specification), the gas cap of a transaction
- [EIP-7939](https://eips.ethereum.org/EIPS/eip-7939#specification), CLZ
- [EIP-2780][eip-2780], the parts of a transaction
- [EIP-7843][eip-7843], SLOTNUM
- [EIP-7976][eip-7976], the call data floor
- [EIP-8024][eip-8024], DUPN, SWAPN and EXCHANGE
- [EIP-8037][eip-8037], authorizations, gas limit
- [EIP-8038][eip-8038], accounts, calls and access lists

The last six are in Last Call, so their prices may still change.

The blob prices are with the blob fees.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[yp-berlin]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip-2780]: https://eips.ethereum.org/EIPS/eip-2780#parameters
[eip-7843]: https://eips.ethereum.org/EIPS/eip-7843#gas-cost
[eip-7976]: https://eips.ethereum.org/EIPS/eip-7976#specification
[eip-8024]: https://eips.ethereum.org/EIPS/eip-8024#specification
[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
[eip-8038]: https://eips.ethereum.org/EIPS/eip-8038#parameters
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-! The gas prices that no fork changed.

A price that a fork adds holds from that fork on. -/

namespace GasCosts

/-- The price of the base tier of instructions, `G_base`. -/
def BASE : Nat := 2
/-- The price of the very low tier, `G_verylow`. -/
def VERY_LOW : Nat := 3
/-- The price of the low tier, `G_low`. -/
def LOW : Nat := 5
/-- The price of the mid tier, `G_mid`. -/
def MID : Nat := 8
/-- The price of the high tier, `G_high`. -/
def HIGH : Nat := 10

/-- The price to access an account or a storage slot that the transaction already accessed.

It is `G_warmaccess`, from EIP-2929. -/
def WARM_ACCESS : Nat := 100
/-- The price of the first access to a storage slot in a transaction.

It is `G_coldsload`, from EIP-2929. -/
def COLD_STORAGE_ACCESS : Nat := 2100

/-- The price to set a storage slot from zero to a value that is not zero, `G_sset`. -/
def STORAGE_SET : Nat := 20000
/-- The price to change a storage slot whose value is not zero.

From Berlin, it includes the price of a cold access to the slot, by EIP-2929.

It is `SSTORE_RESET_GAS` as EIP-2200 sets it, which EIP-8038 calls `GAS_STORAGE_UPDATE`.

The `COLD_STORAGE_WRITE` of the rationale of EIP-8038 is a gas estimate from measured run times.

It is not this price.

In the Shanghai paper it is `G_sreset` plus `G_coldsload`, 2900 + 2100. -/
def COLD_STORAGE_WRITE : Nat := 5000

/-- The price of a write that moves a slot away from its original value, by EIP-8038. -/
def STORAGE_WRITE : Nat := 10000

/-- The gas that a call with value gives the callee on top of the gas it passes.

It is `G_callstipend`. -/
def CALL_STIPEND : Nat := 2300
/-- The price to send value with a call, `G_callvalue`, up to BPO5. -/
def CALL_VALUE : Nat := 9000
/-- The price to write the leaf values of an account, from EIP-8038.

From Glamsterdam, the price to send value with a call is this plus the stipend. -/
def ACCOUNT_WRITE : Nat := 9000
/-- The extra price of a call that creates an account, `G_newaccount`. -/
def NEW_ACCOUNT : Nat := 25000

/-- The price per byte of the code that a contract creation stores, `G_codedeposit`. -/
def CODE_DEPOSIT_PER_BYTE : Nat := 200
/-- The price per 32-byte word of init code, `G_initcodeword`, from EIP-3860. -/
def CODE_INIT_PER_WORD : Nat := 2

/-- The price of each authorization in a transaction, from EIP-7702. -/
def AUTH_PER_EMPTY_ACCOUNT : Nat := 25000

/-- A price of zero, `G_zero`. -/
def ZERO : Nat := 0
/-- The linear price per 32-byte word of memory, `G_memory`. -/
def MEMORY_PER_WORD : Nat := 3
/-- The price of the fast-step tier, from EIP-1884. -/
def FAST_STEP : Nat := 5

/-- An authorization for an account that exists gets back its price minus this, from EIP-7702. -/
def REFUND_AUTH_PER_EXISTING_ACCOUNT : Nat := 12500

/-- The base price of a transaction, `G_transaction`. -/
def TX_BASE : Nat := 21000
/-- The price per zero byte of call data, `G_txdatazero`. -/
def TX_DATA_PER_ZERO : Nat := 4
/-- The standard price per token of call data, from EIP-7623. -/
def TX_DATA_TOKEN_STANDARD : Nat := 4
/-- The largest gas of a transaction, `2^24`, from EIP-7825.

From Glamsterdam it bounds the gas that the transaction itself costs, by EIP-8037. -/
def TX_MAX_GAS_LIMIT : Nat := 16777216

/-- The price of the sender of a transaction, from EIP-2780, at Glamsterdam. -/
def TX_BASE_COST : Nat := 12000
/-- The price of a transaction that sends value to another account, from EIP-2780. -/
def TX_VALUE_COST : Nat := 6000
/-- The price of each authorization of a transaction, from EIP-8037, at Glamsterdam.

EIP-8037 defines it as a sum of four parts:

- 1616 for the 101 bytes of an authorization of EIP-7702, at 16 gas per byte
- 3000 for ECRECOVER, which recovers the authority
- 3000 for a cold access to the authority, the price of EIP-8038
- 200 for two warm accesses to store values in the authority

The price of ECRECOVER is in the precompiles, and this file does not import them.

So the definition keeps the number, and a proof checks the sum. -/
def EXECUTION_PER_AUTH_BASE_COST : Nat := 7816
/-- The largest gas limit of a transaction, `2^32 - 1`, from EIP-8037. -/
def TX_MAX_TOTAL_GAS_LIMIT : Nat := 4294967295

/-- The price of ADD, in the set `W_verylow`. -/
def OPCODE_ADD : Nat := VERY_LOW
/-- The price of SUB, in the set `W_verylow`. -/
def OPCODE_SUB : Nat := VERY_LOW
/-- The price of MUL, in the set `W_low`. -/
def OPCODE_MUL : Nat := LOW
/-- The price of DIV, in the set `W_low`. -/
def OPCODE_DIV : Nat := LOW
/-- The price of SDIV, in the set `W_low`. -/
def OPCODE_SDIV : Nat := LOW
/-- The price of MOD, in the set `W_low`. -/
def OPCODE_MOD : Nat := LOW
/-- The price of SMOD, in the set `W_low`. -/
def OPCODE_SMOD : Nat := LOW
/-- The price of ADDMOD, in the set `W_mid`. -/
def OPCODE_ADDMOD : Nat := MID
/-- The price of MULMOD, in the set `W_mid`. -/
def OPCODE_MULMOD : Nat := MID
/-- The price of SIGNEXTEND, in the set `W_low`. -/
def OPCODE_SIGNEXTEND : Nat := LOW
/-- The price of LT, in the set `W_verylow`. -/
def OPCODE_LT : Nat := VERY_LOW
/-- The price of GT, in the set `W_verylow`. -/
def OPCODE_GT : Nat := VERY_LOW
/-- The price of SLT, in the set `W_verylow`. -/
def OPCODE_SLT : Nat := VERY_LOW
/-- The price of SGT, in the set `W_verylow`. -/
def OPCODE_SGT : Nat := VERY_LOW
/-- The price of EQ, in the set `W_verylow`. -/
def OPCODE_EQ : Nat := VERY_LOW
/-- The price of ISZERO, in the set `W_verylow`. -/
def OPCODE_ISZERO : Nat := VERY_LOW
/-- The price of AND, in the set `W_verylow`. -/
def OPCODE_AND : Nat := VERY_LOW
/-- The price of OR, in the set `W_verylow`. -/
def OPCODE_OR : Nat := VERY_LOW
/-- The price of XOR, in the set `W_verylow`. -/
def OPCODE_XOR : Nat := VERY_LOW
/-- The price of NOT, in the set `W_verylow`. -/
def OPCODE_NOT : Nat := VERY_LOW
/-- The price of BYTE, in the set `W_verylow`. -/
def OPCODE_BYTE : Nat := VERY_LOW
/-- The price of SHL, in the set `W_verylow`, from EIP-145. -/
def OPCODE_SHL : Nat := VERY_LOW
/-- The price of SHR, in the set `W_verylow`, from EIP-145. -/
def OPCODE_SHR : Nat := VERY_LOW
/-- The price of SAR, in the set `W_verylow`, from EIP-145. -/
def OPCODE_SAR : Nat := VERY_LOW
/-- The price of CLZ, from EIP-7939. -/
def OPCODE_CLZ : Nat := LOW
/-- The price of JUMP, in the set `W_mid`. -/
def OPCODE_JUMP : Nat := MID
/-- The price of JUMPI, in the set `W_high`. -/
def OPCODE_JUMPI : Nat := HIGH
/-- The price of JUMPDEST, `G_jumpdest`. -/
def OPCODE_JUMPDEST : Nat := 1
/-- The price of CALLDATALOAD, in the set `W_verylow`. -/
def OPCODE_CALLDATALOAD : Nat := VERY_LOW
/-- The price of BLOCKHASH, `G_blockhash`. -/
def OPCODE_BLOCKHASH : Nat := 20
/-- The price of COINBASE, in the set `W_base`. -/
def OPCODE_COINBASE : Nat := BASE
/-- The price of POP, in the set `W_base`. -/
def OPCODE_POP : Nat := BASE
/-- The price of MSIZE, in the set `W_base`. -/
def OPCODE_MSIZE : Nat := BASE
/-- The price of PC, in the set `W_base`. -/
def OPCODE_PC : Nat := BASE
/-- The price of GAS, in the set `W_base`. -/
def OPCODE_GAS : Nat := BASE
/-- The price of ADDRESS, in the set `W_base`. -/
def OPCODE_ADDRESS : Nat := BASE
/-- The price of ORIGIN, in the set `W_base`. -/
def OPCODE_ORIGIN : Nat := BASE
/-- The price of CALLER, in the set `W_base`. -/
def OPCODE_CALLER : Nat := BASE
/-- The price of CALLVALUE, in the set `W_base`. -/
def OPCODE_CALLVALUE : Nat := BASE
/-- The price of CALLDATASIZE, in the set `W_base`. -/
def OPCODE_CALLDATASIZE : Nat := BASE
/-- The price of CODESIZE, in the set `W_base`. -/
def OPCODE_CODESIZE : Nat := BASE
/-- The price of GASPRICE, in the set `W_base`. -/
def OPCODE_GASPRICE : Nat := BASE
/-- The price of TIMESTAMP, in the set `W_base`. -/
def OPCODE_TIMESTAMP : Nat := BASE
/-- The price of NUMBER, in the set `W_base`. -/
def OPCODE_NUMBER : Nat := BASE
/-- The price of GASLIMIT, in the set `W_base`. -/
def OPCODE_GASLIMIT : Nat := BASE
/-- The price of PREVRANDAO, DIFFICULTY before EIP-4399, in the set `W_base`. -/
def OPCODE_PREVRANDAO : Nat := BASE
/-- The price of RETURNDATASIZE, in the set `W_base`, from EIP-211. -/
def OPCODE_RETURNDATASIZE : Nat := BASE
/-- The price of CHAINID, in the set `W_base`, from EIP-1344. -/
def OPCODE_CHAINID : Nat := BASE
/-- The price of SELFBALANCE, in the set `W_low`, from EIP-1884. -/
def OPCODE_SELFBALANCE : Nat := FAST_STEP
/-- The price of BASEFEE, in the set `W_base`, from EIP-3198. -/
def OPCODE_BASEFEE : Nat := BASE
/-- The price of BLOBBASEFEE, from EIP-7516. -/
def OPCODE_BLOBBASEFEE : Nat := BASE
/-- The price of SLOTNUM, from EIP-7843. -/
def OPCODE_SLOTNUM : Nat := BASE
/-- The price of BLOBHASH, from EIP-4844. -/
def OPCODE_BLOBHASH : Nat := 3
/-- The price of PUSH1 to PUSH32, in the set `W_verylow`. -/
def OPCODE_PUSH : Nat := VERY_LOW
/-- The price of PUSH0, in the set `W_base`, from EIP-3855. -/
def OPCODE_PUSH0 : Nat := BASE
/-- The price of DUP1 to DUP16, in the set `W_verylow`. -/
def OPCODE_DUP : Nat := VERY_LOW
/-- The price of SWAP1 to SWAP16, in the set `W_verylow`. -/
def OPCODE_SWAP : Nat := VERY_LOW
/-- The price of DUPN, from EIP-8024. -/
def OPCODE_DUPN : Nat := VERY_LOW
/-- The price of SWAPN, from EIP-8024. -/
def OPCODE_SWAPN : Nat := VERY_LOW
/-- The price of EXCHANGE, from EIP-8024. -/
def OPCODE_EXCHANGE : Nat := VERY_LOW
/-- The price of TLOAD, from EIP-1153. -/
def OPCODE_TLOAD : Nat := WARM_ACCESS
/-- The price of TSTORE, from EIP-1153. -/
def OPCODE_TSTORE : Nat := WARM_ACCESS

/-- The base price of RETURNDATACOPY, `G_verylow` of the set `W_copy`, from EIP-211. -/
def OPCODE_RETURNDATACOPY_BASE : Nat := VERY_LOW
/-- The price per copied word of RETURNDATACOPY, `G_copy`, from EIP-211. -/
def OPCODE_RETURNDATACOPY_PER_WORD : Nat := 3
/-- The base price of CALLDATACOPY, `G_verylow` of the set `W_copy`. -/
def OPCODE_CALLDATACOPY_BASE : Nat := VERY_LOW
/-- The base price of CODECOPY, `G_verylow` of the set `W_copy`. -/
def OPCODE_CODECOPY_BASE : Nat := VERY_LOW
/-- The base price of MCOPY, from EIP-5656. -/
def OPCODE_MCOPY_BASE : Nat := VERY_LOW
/-- The base price of MLOAD, in the set `W_verylow`. -/
def OPCODE_MLOAD_BASE : Nat := VERY_LOW
/-- The base price of MSTORE, in the set `W_verylow`. -/
def OPCODE_MSTORE_BASE : Nat := VERY_LOW
/-- The base price of MSTORE8, in the set `W_verylow`. -/
def OPCODE_MSTORE8_BASE : Nat := VERY_LOW
/-- The price per copied word of CALLDATACOPY, CODECOPY and EXTCODECOPY, `G_copy`, and of MCOPY. -/
def OPCODE_COPY_PER_WORD : Nat := 3
/-- The base price of CREATE, `G_create`, and of CREATE2 from EIP-1014. -/
def OPCODE_CREATE_BASE : Nat := 32000
/-- The base price of EXP, `G_exp`. -/
def OPCODE_EXP_BASE : Nat := 10
/-- The base price of KECCAK256, `G_keccak256`. -/
def OPCODE_KECCAK256_BASE : Nat := 30
/-- The price per hashed word of KECCAK256, `G_keccak256word`. -/
def OPCODE_KECCAK256_PER_WORD : Nat := 6
/-- The base price of LOG0 to LOG4, `G_log`. -/
def OPCODE_LOG_BASE : Nat := 375
/-- The price per logged byte, `G_logdata`. -/
def OPCODE_LOG_DATA_PER_BYTE : Nat := 8
/-- The price per log topic, `G_logtopic`. -/
def OPCODE_LOG_TOPIC : Nat := 375
end GasCosts

open EthLib.Base (Fork U256 WEI_PER_ETHER)
open GasCosts

-- A price that a fork changed and that depends only on the fork is a field of the gas schedule.
--
-- A price that a fork changed and that also depends on an access or an input is its own function.
--
-- The prices of SLOAD, BALANCE, EXTCODESIZE, EXTCODEHASH and CALL depend on the access.
--
-- The prices that no fork changed are the constants above.

/-- The price of SLOAD.

From Berlin, it is the price of a cold or a warm access to the slot.

Before Berlin, it does not depend on the access. -/
def sloadCost (fork : Fork) (cold : Bool) : Nat :=
  if fork ≥ .berlin then
    -- `G_coldsload` or `G_warmaccess`, which replace the price of 800, by EIP-2929.
    if cold then COLD_STORAGE_ACCESS else WARM_ACCESS
  else if fork ≥ .istanbul then
    -- EIP-1884 raises the price from 200 to 800.
    800
  else if fork ≥ .tangerineWhistle then
    -- EIP-150 raises the price from 50 to 200.
    200
  else 50

/-- The parameters of the execution layer that a fork changed, and that depend only on the fork.

They are gas prices and refunds, the limits of code and the reservoir of a system call.

They are also the reward and the bomb of a block. -/
structure GasSchedule where
  /-- The price per byte of the exponent of EXP. -/
  OPCODE_EXP_PER_BYTE : Nat
  /-- The base price of SELFDESTRUCT. -/
  OPCODE_SELFDESTRUCT_BASE : Nat
  /-- The extra price in execution gas of a SELFDESTRUCT that creates an account. -/
  OPCODE_SELFDESTRUCT_NEW_ACCOUNT : Nat
  /-- The extra price of a transaction that creates a contract. -/
  TX_CREATE : Nat
  /-- The price per nonzero byte of call data. -/
  TX_DATA_PER_NON_ZERO : Nat
  /-- The floor price per token of call data, from Pectra. -/
  TX_DATA_TOKEN_FLOOR : Nat
  /-- The price per address of an access list, from Berlin. -/
  TX_ACCESS_LIST_ADDRESS : Nat
  /-- The price per storage key of an access list, from Berlin. -/
  TX_ACCESS_LIST_STORAGE_KEY : Nat
  /-- The price of the first access to an account in a transaction, from Berlin. -/
  COLD_ACCOUNT_ACCESS : Nat
  /-- The refund to clear a storage slot whose value is not zero. -/
  REFUND_STORAGE_CLEAR : Nat
  /-- The refund for each account that SELFDESTRUCT destroys. -/
  REFUND_SELF_DESTRUCT : Nat
  /-- The quotient of the gas used that caps the refund of a transaction. -/
  MAX_REFUND_QUOTIENT : Nat
  /-- The price of SSTORE when the write leaves the slot as it is, or the slot is already dirty.

  It is read only from Istanbul on. -/
  SSTORE_READ : Nat
  /-- The price of SSTORE to change a slot whose original value is not zero.

  It is read only from Istanbul on. -/
  SSTORE_RESET : Nat
  /-- The price of a creation, before memory, init code and the hash of CREATE2. -/
  CREATE_BASE : Nat
  /-- The price of each authorization of a transaction, from Pectra. -/
  TX_AUTHORIZATION : Nat
  -- The prices of the addition and the scalar multiplication on the alt_bn128 curve are here.
  --
  -- The other precompiles keep their prices with their own definitions.
  /-- The price of the addition precompile of the alt_bn128 curve. -/
  PRECOMPILE_ECADD : Nat
  /-- The price of the scalar multiplication precompile of the alt_bn128 curve. -/
  PRECOMPILE_ECMUL : Nat
  /-- The reservoir of state gas of a system call. -/
  SYSTEM_RESERVOIR : Nat
  /-- The most bytes of code that a creation may deploy, or none for no bound. -/
  MAX_CODE_SIZE : Option Nat
  /-- The most bytes of init code, read only from Shapella on. -/
  MAX_INIT_CODE_SIZE : Nat
  /-- The block reward in wei, read only before Paris. -/
  BLOCK_REWARD : Nat
  /-- The blocks by which the difficulty bomb is delayed, read only before Paris. -/
  BOMB_DELAY : Nat
  deriving DecidableEq, Repr

/-- The parameters of the execution layer at `fork` that depend only on the fork.

Each value changes only at the forks that the comments name.

From Glamsterdam, the prices of an access list and the refund to clear a slot derive from others.

The section Conversion to gas costs of [EIP-8038][eip-8038] gives their formulas.

[eip-8038]: https://eips.ethereum.org/EIPS/eip-8038#conversion-to-gas-costs
-/
def gasSchedule (fork : Fork) : GasSchedule :=
  -- Each value names its symbol, then each change with its fork and its EIP.
  --
  -- `G_coldaccountaccess`: 2600 from Berlin by EIP-2929, 3000 from Glamsterdam by EIP-8038.
  let coldAccountAccess := if fork ≥ .glamsterdam then 3000 else 2600
  { -- `G_expbyte`: 10, then 50 from Spurious Dragon by EIP-160.
    OPCODE_EXP_PER_BYTE := if fork ≥ .spuriousDragon then 50 else 10
    -- `G_selfdestruct`: 0, then 5000 from Tangerine Whistle by EIP-150.
    OPCODE_SELFDESTRUCT_BASE := if fork ≥ .tangerineWhistle then 5000 else 0
    -- `G_newaccount` of SELFDESTRUCT: 25000 from Tangerine Whistle by EIP-150.
    --
    -- From Glamsterdam, EIP-8038 replaces it with its `ACCOUNT_WRITE`, 9000.
    OPCODE_SELFDESTRUCT_NEW_ACCOUNT :=
      if fork ≥ .glamsterdam then ACCOUNT_WRITE
      else if fork ≥ .tangerineWhistle then 25000 else 0
    -- `G_txcreate`: 32000 from Homestead by EIP-2, which raises a creation from 21000 to 53000.
    TX_CREATE := if fork ≥ .homestead then 32000 else 0
    -- `G_txdatanonzero`: 68, then 16 from Istanbul by EIP-2028.
    TX_DATA_PER_NON_ZERO := if fork ≥ .istanbul then 16 else 68
    -- `TOTAL_COST_FLOOR_PER_TOKEN`: 10 from Pectra by EIP-7623, 16 from Glamsterdam by EIP-7976.
    TX_DATA_TOKEN_FLOOR := if fork ≥ .glamsterdam then 16 else 10
    -- `G_accesslistaddress`: 2400 from Berlin by EIP-2930.
    --
    -- From Glamsterdam, EIP-8038 sets it at the cold minus the warm price, 2900.
    TX_ACCESS_LIST_ADDRESS :=
      if fork ≥ .glamsterdam then coldAccountAccess - WARM_ACCESS else 2400
    -- `G_accessliststorage`: 1900 from Berlin by EIP-2930.
    --
    -- From Glamsterdam, EIP-8038 sets it at the cold minus the warm price, 2000.
    TX_ACCESS_LIST_STORAGE_KEY :=
      if fork ≥ .glamsterdam then COLD_STORAGE_ACCESS - WARM_ACCESS else 1900
    COLD_ACCOUNT_ACCESS := coldAccountAccess
    -- `R_sclear`: 15000 in the Berlin paper, 4800 from London by EIP-3529.
    --
    -- From Glamsterdam, 11616 by EIP-8038.
    --
    -- EIP-8038 gives it as `(STORAGE_WRITE + COLD_STORAGE_ACCESS) * (4800/5000)`.
    --
    -- The code multiplies before it divides, so the division in `Nat` is exact.
    --
    -- It is exact since `12100 * 4800 = 11616 * 5000`.
    REFUND_STORAGE_CLEAR :=
      if fork ≥ .glamsterdam then (STORAGE_WRITE + COLD_STORAGE_ACCESS) * 4800 / 5000
      else if fork ≥ .london then 4800 else 15000
    -- `R_selfdestruct`: 24000 in the Berlin paper, then 0 from London by EIP-3529.
    REFUND_SELF_DESTRUCT := if fork ≥ .london then 0 else 24000
    -- The refund is at most the gas used over 2, then over 5 from London by EIP-3529.
    MAX_REFUND_QUOTIENT := if fork ≥ .london then 5 else 2
    -- EIP-2200's `SLOAD_GAS`, the price of SLOAD, which EIP-2929 sets to `WARM_STORAGE_READ_COST`.
    SSTORE_READ := if fork ≥ .berlin then WARM_ACCESS else sloadCost fork false
    -- EIP-2200's `SSTORE_RESET_GAS`, which EIP-2929 sets to `5000 - COLD_SLOAD_COST`.
    --
    -- From Berlin it leaves out the price of a cold access, which SSTORE adds on its own.
    SSTORE_RESET :=
      if fork ≥ .berlin then COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS else COLD_STORAGE_WRITE
    -- `G_create`: 32000 up to BPO5.
    --
    -- From Glamsterdam, the write and the cold access of the new account, 12000, by EIP-8038.
    CREATE_BASE :=
      if fork ≥ .glamsterdam then ACCOUNT_WRITE + coldAccountAccess else OPCODE_CREATE_BASE
    -- `PER_EMPTY_ACCOUNT_COST`, 25000, by EIP-7702.
    --
    -- From Glamsterdam, EIP-8037 lowers it to 7816, and charges the rest at run time.
    TX_AUTHORIZATION :=
      if fork ≥ .glamsterdam then EXECUTION_PER_AUTH_BASE_COST else AUTH_PER_EMPTY_ACCOUNT
    -- EIP-196, Gas costs: 500; EIP-1108, Specification: 150, here from Istanbul.
    PRECOMPILE_ECADD := if fork ≥ .istanbul then 150 else 500
    -- EIP-196, Gas costs: 40000; EIP-1108, Specification: 6000, here from Istanbul.
    PRECOMPILE_ECMUL := if fork ≥ .istanbul then 6000 else 40000
    -- From Glamsterdam, the state gas of 16 new storage slots, 1,566,720, by EIP-8037.
    --
    -- Before Glamsterdam, 0.
    SYSTEM_RESERVOIR :=
      if fork ≥ .glamsterdam then STORAGE_SET_STATE_GAS * SYSTEM_MAX_SSTORES_PER_CALL else 0
    -- 24576 from Spurious Dragon by EIP-170, and 65536 from Glamsterdam by EIP-7954.
    MAX_CODE_SIZE :=
      if fork ≥ .glamsterdam then some 65536
      else if fork ≥ .spuriousDragon then some 24576
      else none
    -- 49152 from Shapella by EIP-3860, and 131072 from Glamsterdam by EIP-7954.
    --
    -- Both are twice the code limit, but no code limit exists before Spurious Dragon.
    --
    -- So the value keeps its own numbers, and each rule that reads it checks the fork.
    MAX_INIT_CODE_SIZE := if fork ≥ .glamsterdam then 131072 else 49152
    -- `R_block` of §11.3 of the Berlin paper, in wei.
    BLOCK_REWARD :=
      -- `R_block = 10^18 × 5` before Byzantium.
      if fork < .byzantium then 5 * WEI_PER_ETHER
      -- `10^18 × 3` from Byzantium, by EIP-649.
      else if fork < .constantinople then 3 * WEI_PER_ETHER
      -- `10^18 × 2` from Constantinople, by EIP-1234.
      else 2 * WEI_PER_ETHER
    -- `kappa` of §4.3.4 of the Berlin paper, one case for each range of forks.
    --
    -- §4.3.4 leaves `kappa` undefined before Byzantium; there EIP-2 reads `H_i` itself, so 0.
    BOMB_DELAY :=
      if fork < .byzantium then 0
      -- 3,000,000 from Byzantium, by EIP-649.
      else if fork < .constantinople then 3000000
      -- 5,000,000 from Constantinople, by EIP-1234.
      else if fork < .muirGlacier then 5000000
      -- 9,000,000 from Muir Glacier, by EIP-2384.
      else if fork < .london then 9000000
      -- 9,700,000 from London, by EIP-3554.
      else if fork < .arrowGlacier then 9700000
      -- 10,700,000 from Arrow Glacier, by EIP-4345.
      else if fork < .grayGlacier then 10700000
      -- 11,400,000 from Gray Glacier, by EIP-5133.
      else 11400000 }

namespace GasCosts

/-- The price to access and write the account that a contract creation deploys, from EIP-8038.

It is the price of a creation in the schedule of Glamsterdam.

That price is the write of an account plus a cold access to it, 9000 + 3000 = 12000.

The section Conversion to gas costs of [EIP-8038][eip-8038] gives this formula.

[eip-8038]: https://eips.ethereum.org/EIPS/eip-8038#conversion-to-gas-costs
-/
def CREATE_ACCESS : Nat := (gasSchedule .glamsterdam).CREATE_BASE

end GasCosts

/-- The price of an access to an account at `fork`, from EIP-2929.

The first access to an account in a transaction is cold, and a later one is warm.

EIP-8038 raises the cold price from 2600 to 3000 at Glamsterdam. -/
def accountAccessCost (fork : Fork) (cold : Bool) : Nat :=
  if cold then (gasSchedule fork).COLD_ACCOUNT_ACCESS else WARM_ACCESS

/-- The price of BALANCE.

From Berlin, it is the price of a cold or a warm access to the account.

Before Berlin, it does not depend on the access. -/
def balanceCost (fork : Fork) (cold : Bool) : Nat :=
  if fork ≥ .berlin then
    -- EIP-2929 replaces the price of 700 with the price of the access.
    accountAccessCost fork cold
  else if fork ≥ .istanbul then
    -- EIP-1884 raises the price from 400 to 700.
    700
  else if fork ≥ .tangerineWhistle then
    -- EIP-150 raises the price from 20 to 400.
    400
  else 20

/-- The price of EXTCODESIZE, and the base price of EXTCODECOPY.

From Berlin, it is the price of a cold or a warm access to the account.

From Glamsterdam, it adds the price of a warm access for the read of the code.

Before Berlin, it does not depend on the access. -/
def externalBaseCost (fork : Fork) (cold : Bool) : Nat :=
  if fork ≥ .glamsterdam then
    -- EIP-8038 adds a warm access for the second read.
    accountAccessCost fork cold + WARM_ACCESS
  else if fork ≥ .berlin then
    -- EIP-2929 replaces the price of 700 with the price of the access.
    accountAccessCost fork cold
  else if fork ≥ .tangerineWhistle then
    -- EIP-150 raises the price from 20 to 700.
    700
  else 20

/-- The price of EXTCODEHASH, which EIP-1052 adds at Constantinople.

From Berlin, it is the price of a cold or a warm access to the account.

Before Berlin, it does not depend on the access. -/
def extcodehashCost (fork : Fork) (cold : Bool) : Nat :=
  if fork ≥ .berlin then
    -- EIP-2929 replaces the price of 700 with the price of the access.
    accountAccessCost fork cold
  else if fork ≥ .istanbul then
    -- EIP-1884 raises the price from 400 to 700.
    700
  else 400

/-- The base price of CALL, CALLCODE, DELEGATECALL and STATICCALL.

From Berlin, it is the price of a cold or a warm access to the account.

Before Berlin, it does not depend on the access. -/
def callBaseCost (fork : Fork) (cold : Bool) : Nat :=
  if fork ≥ .berlin then
    -- EIP-2929 replaces the price of 700 with the price of the access.
    accountAccessCost fork cold
  else if fork ≥ .tangerineWhistle then
    -- EIP-150 raises the price from 40 to 700.
    700
  else 40

/-- The most gas that a call can pass on: all but one 64th of the gas, rounded up.

The limit holds from Tangerine Whistle.

Source: EIP-150, and the function `L` of Appendix H.1 of the Yellow Paper. -/
def maxMessageCallGas (gas : Nat) : Nat :=
  gas - gas / 64

/-- The price of init code: 2 gas per 32-byte word.

The price holds from Shanghai.

Source: EIP-3860. -/
def initCodeCost (initCodeLength : Nat) : Nat :=
  CODE_INIT_PER_WORD * wordCount initCodeLength

/-- The most bytes of code that a creation may deploy at `fork`, or none for no bound.

[EIP-170](https://eips.ethereum.org/EIPS/eip-170#specification) sets it at 24576 at Spurious Dragon.

[EIP-7954][eip-7954] raises it to 65536 at Glamsterdam.

[eip-7954]: https://eips.ethereum.org/EIPS/eip-7954#specification
-/
def maxCodeSize (fork : Fork) : Option Nat :=
  (gasSchedule fork).MAX_CODE_SIZE

/-- The most bytes of init code at `fork`, from Shapella on.

[EIP-3860](https://eips.ethereum.org/EIPS/eip-3860#parameters) sets it at 49152 at Shapella.

It defines the limit as twice the code limit, and only from Shapella on.

[EIP-7954][eip-7954] raises it to 131072 at Glamsterdam, and keeps that ratio.

[eip-7954]: https://eips.ethereum.org/EIPS/eip-7954#specification
-/
def maxInitCodeSize (fork : Fork) : Nat :=
  -- No limit of init code exists before Shapella, so each rule that reads this one checks the fork.
  (gasSchedule fork).MAX_INIT_CODE_SIZE

end EthLib.Execution.Evm
