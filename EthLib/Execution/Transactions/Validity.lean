module

public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Evm.Precompiles.PointEvaluation
public import EthLib.Execution.Transactions.Signature

/-!
# `Transactions.Validity`

The gas that a transaction pays before it runs, and the rules that a transaction must pass alone.

The intrinsic gas pays for the transaction itself, before it runs.

It prices the call data, a contract creation, the access list and the authorizations.

Section 6.2 of the Yellow Paper, Shanghai version, defines it, and later EIPs add terms.

Source: [`Paper.tex` at `efc5f9a`][yp].

The rules here need no state.

They read the gas limit, the nonce, the fees, the chain, the blobs and the authorizations.

The rules that read the state, such as the balance of the sender, belong to the block.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Evm.GasCosts

/-! ## The fields that the rules read -/

namespace Transaction

/-- The gas limit of a transaction. -/
def gas : Transaction → U256
  | .legacy tx => tx.gas
  | .accessList tx => tx.gas
  | .feeMarket tx => tx.gas
  | .blob tx => tx.gas
  | .setCode tx => tx.gas

/-- The nonce of a transaction. -/
def nonce : Transaction → U256
  | .legacy tx => tx.nonce
  | .accessList tx => tx.nonce
  | .feeMarket tx => tx.nonce
  | .blob tx => tx.nonce
  | .setCode tx => tx.nonce

/-- The call data of a transaction, or the init code of a contract creation. -/
def data : Transaction → ByteArray
  | .legacy tx => tx.data
  | .accessList tx => tx.data
  | .feeMarket tx => tx.data
  | .blob tx => tx.data
  | .setCode tx => tx.data

/-- The recipient of a transaction, or none for a contract creation. -/
def to : Transaction → Option Address
  | .legacy tx => tx.to
  | .accessList tx => tx.to
  | .feeMarket tx => tx.to
  | .blob tx => some tx.to
  | .setCode tx => some tx.to

/-- The access list of a transaction, empty for a legacy transaction. -/
def accesses : Transaction → List Access
  | .legacy _ => []
  | .accessList tx => tx.accessList
  | .feeMarket tx => tx.accessList
  | .blob tx => tx.accessList
  | .setCode tx => tx.accessList

/-- The authorizations of a transaction, empty unless it sets code. -/
def authorizations : Transaction → List Authorization
  | .setCode tx => tx.authorizations
  | _ => []

end Transaction

/-! ## The intrinsic gas -/

/-- The number of zero bytes of call data. -/
def zeroBytes (data : ByteArray) : Nat :=
  data.data.toList.countP (· = 0)

/-- The price of call data at `fork`: 4 gas per zero byte, and a price per nonzero byte.

The price per nonzero byte is 68, and 16 from Istanbul.

[EIP-2028](https://eips.ethereum.org/EIPS/eip-2028#specification) lowers it. -/
def dataCost (fork : Fork) (data : ByteArray) : Nat :=
  TX_DATA_PER_ZERO * zeroBytes data +
    (gasSchedule fork).TX_DATA_PER_NON_ZERO * (data.size - zeroBytes data)

/-- The price of a contract creation at `fork`, for `size` bytes of init code.

It is 32000 from Homestead, by [EIP-2](https://eips.ethereum.org/EIPS/eip-2#specification).

From Shapella, it adds 2 gas per 32-byte word of init code.

[EIP-3860](https://eips.ethereum.org/EIPS/eip-3860#specification) adds that price. -/
def createCost (fork : Fork) (size : Nat) : Nat :=
  (gasSchedule fork).TX_CREATE + if fork ≥ .shapella then initCodeCost size else 0

/-- The price of an access list: 2400 gas per address and 1900 gas per storage key.

[EIP-2930](https://eips.ethereum.org/EIPS/eip-2930#specification) adds it at Berlin. -/
def accessListCost (accessList : List Access) : Nat :=
  (accessList.map fun a => TX_ACCESS_LIST_ADDRESS + TX_ACCESS_LIST_STORAGE_KEY * a.slots.length).sum

/-- The intrinsic gas of a transaction at `fork`.

It is 21000, plus the call data, a contract creation, the access list and the authorizations.

[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#gas-costs) prices each authorization at 25000. -/
def intrinsicGas (fork : Fork) (tx : Transaction) : Nat :=
  TX_BASE + dataCost fork tx.data +
    (if tx.to.isNone then createCost fork tx.data.size else 0) +
    accessListCost tx.accesses + AUTH_PER_EMPTY_ACCOUNT * tx.authorizations.length

/-- The tokens of call data: 1 per zero byte and 4 per nonzero byte. -/
def tokens (data : ByteArray) : Nat :=
  zeroBytes data + 4 * (data.size - zeroBytes data)

/-- The call data floor: 21000 plus 10 gas per token.

[EIP-7623](https://eips.ethereum.org/EIPS/eip-7623#specification) adds it at Pectra. -/
def calldataFloor (data : ByteArray) : Nat :=
  TX_BASE + TX_DATA_TOKEN_FLOOR * tokens data

/-- The least gas limit of a transaction at `fork`: its intrinsic gas, and from Pectra the floor. -/
def minimumGas (fork : Fork) (tx : Transaction) : Nat :=
  if fork ≥ .pectra then max (intrinsicGas fork tx) (calldataFloor tx.data)
  else intrinsicGas fork tx

/-! ## The rules -/

/-- The most bytes of init code, twice the most bytes of code.

[EIP-3860](https://eips.ethereum.org/EIPS/eip-3860#parameters) sets it at Shapella. -/
def MAX_INIT_CODE_SIZE : Nat := 49152

/-- The most blobs of one transaction.

[EIP-7594](https://eips.ethereum.org/EIPS/eip-7594#specification) sets it at Fusaka. -/
def MAX_BLOBS_PER_TRANSACTION : Nat := 6

/-- Check the fees, the gas limit and the nonce of a transaction at `fork`.

It returns the intrinsic gas.

- The gas limit covers the least gas limit of the fork.
- From Shapella, init code has at most 49152 bytes.
- From Fusaka, the gas limit is at most `2^24`, as EIP-7825 asks.
- The nonce is below `2^64 - 1`, as EIP-2681 asks.
- The priority fee is at most the maximum fee, as EIP-1559 asks.

[EIP-7825](https://eips.ethereum.org/EIPS/eip-7825#specification),
[EIP-2681](https://eips.ethereum.org/EIPS/eip-2681#specification) and
[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification) state these rules. -/
def validateTransaction (fork : Fork) (tx : Transaction) : Except TransactionError Nat :=
  if tx.gas.toNat < minimumGas fork tx then
    .error (.insufficientGas (minimumGas fork tx) tx.gas.toNat)
  else if fork ≥ .shapella ∧ tx.to.isNone ∧ MAX_INIT_CODE_SIZE < tx.data.size then
    .error (.initCodeTooLarge tx.data.size)
  else if fork ≥ .fusaka ∧ TX_MAX_GAS_LIMIT < tx.gas.toNat then
    .error (.gasLimitExceeded tx.gas.toNat)
  else if 2 ^ 64 - 1 ≤ tx.nonce.toNat then
    .error .nonceOverflow
  else if feesInverted tx then
    .error .priorityFeeGreaterThanMaxFee
  else .ok (intrinsicGas fork tx)
where
  /-- Whether the priority fee per gas is above the maximum fee per gas. -/
  feesInverted : Transaction → Bool
    | .feeMarket tx => tx.maxFeePerGas.toNat < tx.maxPriorityFeePerGas.toNat
    | .blob tx => tx.maxFeePerGas.toNat < tx.maxPriorityFeePerGas.toNat
    | .setCode tx => tx.maxFeePerGas.toNat < tx.maxPriorityFeePerGas.toNat
    | _ => false

/-- Check the blobs and the authorizations of a transaction at `fork`.

- A blob transaction has at least one blob, and each versioned hash starts with `0x01`.
- From Fusaka, it has at most 6 blobs.
- A set code transaction has at least one authorization, as EIP-7702 asks.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#execution-layer-validation),
[EIP-7594](https://eips.ethereum.org/EIPS/eip-7594#specification) and
[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#set-code-transaction) state these rules. -/
def checkContents (fork : Fork) : Transaction → Except TransactionError Unit
  | .blob tx =>
    if tx.blobVersionedHashes.isEmpty then .error .noBlobData
    else if fork ≥ .fusaka ∧ MAX_BLOBS_PER_TRANSACTION < tx.blobVersionedHashes.length then
      .error (.blobCountExceeded tx.blobVersionedHashes.length)
    else if tx.blobVersionedHashes.any
        (fun h => h[0] != Precompiles.PointEvaluation.VERSIONED_HASH_VERSION_KZG) then
      .error .invalidBlobVersionedHash
    else .ok ()
  | .setCode tx => if tx.authorizations.isEmpty then .error .emptyAuthorizationList else .ok ()
  | _ => .ok ()

/-- Check that a transaction signs no chain, or the chain `chainId` of the network. -/
def checkChainId (fork : Fork) (chainId : UInt64) (tx : Transaction) :
    Except TransactionError Unit := do
  match ← tx.chainId fork with
  | none => .ok ()
  | some c =>
    if c.toNat = chainId.toNat then .ok () else .error (.wrongChainId chainId.toNat c.toNat)

/-- Check a transaction alone, at `fork` on the chain `chainId`.

It returns the sender and the intrinsic gas.

The checks run in order: the gas and the nonce, the chain, the signature, then the contents. -/
def checkTransaction (fork : Fork) (chainId : UInt64) (tx : Transaction) :
    Except TransactionError (Address × Nat) := do
  let gas ← validateTransaction fork tx
  checkChainId fork chainId tx
  let sender ← recoverSender fork tx
  checkContents fork tx
  return (sender, gas)

end EthLib.Execution.Transactions
