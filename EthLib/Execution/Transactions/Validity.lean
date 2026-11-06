module

public import EthLib.Execution.Evm.Gas.Prices
public import EthLib.Cryptography.Kzg.VersionedHash
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

Glamsterdam changes the intrinsic gas, the floor and the bounds on the gas limit:

- EIP-2780 splits the base by sender, recipient and value, so the intrinsic gas reads the sender;
- EIP-7976 raises the floor of call data;
- EIP-7981 adds a data price for access lists;
- EIP-8037 lowers the price of an authorization and bounds the gas limit at `2^32 - 1`;
- EIP-8038 raises the prices of access lists;
- EIP-7954 raises the bound on init code.

These EIPs are in Last Call, so their rules may still change.

Hegotá has no rules of its own here yet, so the exports reject it.

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

/-- The ether that a transaction sends, in wei. -/
def value : Transaction → U256
  | .legacy tx => tx.value
  | .accessList tx => tx.value
  | .feeMarket tx => tx.value
  | .blob tx => tx.value
  | .setCode tx => tx.value

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

/-- The price of an access list at `fork`, per address and per storage key.

[EIP-2930][eip-2930] adds it at Berlin, at 2400 and 1900 gas.

[EIP-8038][eip-8038] raises them to 2900 and 2000 at Glamsterdam.

[eip-2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
[eip-8038]: https://eips.ethereum.org/EIPS/eip-8038#parameters -/
def accessListCost (fork : Fork) (accessList : List Access) : Nat :=
  (accessList.map fun a => (gasSchedule fork).TX_ACCESS_LIST_ADDRESS +
    (gasSchedule fork).TX_ACCESS_LIST_STORAGE_KEY * a.slots.length).sum

/-- The bytes of an access list: 20 per address and 32 per storage key. -/
def accessListBytes (accessList : List Access) : Nat :=
  (accessList.map fun a => 20 + 32 * a.slots.length).sum

/-- The data price of an access list from Glamsterdam: 64 gas per byte, 0 before.

[EIP-7981][eip-7981] adds it to the intrinsic gas and to the floor.

[eip-7981]: https://eips.ethereum.org/EIPS/eip-7981#specification -/
def accessListDataCost (fork : Fork) (accessList : List Access) : Nat :=
  if fork ≥ .glamsterdam then
    TX_DATA_TOKEN_STANDARD * (gasSchedule fork).TX_DATA_TOKEN_FLOOR * accessListBytes accessList
  else 0

/-- The base of the intrinsic gas of a transaction from `sender`, at `fork`.

Before Glamsterdam it is 21000.

From Glamsterdam it adds three parts, as [EIP-2780][eip-2780] sets them:

- the sender pays 12000;
- a contract creation pays 12000 to deploy, a call to another account pays 3000 to touch it;
- a call that sends value to another account pays 6000 more.

A transaction that calls its own sender pays neither of the last two.

[eip-2780]: https://eips.ethereum.org/EIPS/eip-2780#intrinsic-gas-costs -/
def baseCost (fork : Fork) (sender : Address) (tx : Transaction) : Nat :=
  if fork ≥ .glamsterdam then
    TX_BASE_COST +
      match tx.to with
      | none => CREATE_ACCESS
      | some to =>
        if to = sender then 0
        else (gasSchedule fork).COLD_ACCOUNT_ACCESS + if tx.value = 0 then 0 else TX_VALUE_COST
  else TX_BASE

/-- The price of an authorization at `fork`.

[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#gas-costs) prices it at 25000.

[EIP-8037][eip-8037] lowers it to 7816 at Glamsterdam, and charges the rest at run time.

[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#parameter-changes -/
def authorizationCost (fork : Fork) : Nat :=
  if fork ≥ .glamsterdam then EXECUTION_PER_AUTH_BASE_COST else AUTH_PER_EMPTY_ACCOUNT

/-- The price of a contract creation at `fork` beyond the base, for `size` bytes of init code.

It is 32000 from Homestead, by [EIP-2](https://eips.ethereum.org/EIPS/eip-2#specification).

From Shapella, it adds 2 gas per 32-byte word of init code.

[EIP-3860](https://eips.ethereum.org/EIPS/eip-3860#specification) adds that price.

From Glamsterdam, the base holds the price of the deployment, so only the init code remains. -/
def createCost (fork : Fork) (size : Nat) : Nat :=
  (if fork ≥ .glamsterdam then 0 else (gasSchedule fork).TX_CREATE) +
    if fork ≥ .shapella then initCodeCost size else 0

/-- The intrinsic gas of a transaction from `sender`, at `fork`.

It is the base, plus the call data, a contract creation, the access list and the authorizations.

Only the base reads the sender, and only from Glamsterdam. -/
def intrinsicGas (fork : Fork) (sender : Address) (tx : Transaction) : Nat :=
  baseCost fork sender tx + dataCost fork tx.data +
    (if tx.to.isNone then createCost fork tx.data.size else 0) +
    accessListCost fork tx.accesses + accessListDataCost fork tx.accesses +
    authorizationCost fork * tx.authorizations.length

/-- The tokens of call data: 1 per zero byte and 4 per nonzero byte. -/
def tokens (data : ByteArray) : Nat :=
  zeroBytes data + 4 * (data.size - zeroBytes data)

/-- The floor tokens of call data at `fork`.

Before Glamsterdam they are the tokens.

From Glamsterdam, [EIP-7976][eip-7976] counts 4 tokens for every byte.

[eip-7976]: https://eips.ethereum.org/EIPS/eip-7976#specification -/
def floorTokens (fork : Fork) (data : ByteArray) : Nat :=
  if fork ≥ .glamsterdam then TX_DATA_TOKEN_STANDARD * data.size else tokens data

/-- The call data floor of a transaction from `sender`, at `fork`.

It is the base, plus the floor price for each floor token, plus the data price of the access list.

[EIP-7623][eip-7623] adds it at Pectra, with 10 gas per token.

EIP-7976 raises the price to 16 at Glamsterdam, and EIP-2780 replaces 21000 by the base.

[eip-7623]: https://eips.ethereum.org/EIPS/eip-7623#specification -/
def calldataFloor (fork : Fork) (sender : Address) (tx : Transaction) : Nat :=
  baseCost fork sender tx + (gasSchedule fork).TX_DATA_TOKEN_FLOOR * floorTokens fork tx.data +
    accessListDataCost fork tx.accesses

/-- The least gas limit of a transaction at `fork`: its intrinsic gas, and from Pectra the floor. -/
def minimumGas (fork : Fork) (sender : Address) (tx : Transaction) : Nat :=
  if fork ≥ .pectra then max (intrinsicGas fork sender tx) (calldataFloor fork sender tx)
  else intrinsicGas fork sender tx

/-! ## The rules -/

/-- The most blobs of one transaction.

[EIP-7594](https://eips.ethereum.org/EIPS/eip-7594#specification) sets it at Fusaka. -/
def MAX_BLOBS_PER_TRANSACTION : Nat := 6

/-- Check the fees, the gas limit and the nonce of a transaction from `sender` at `fork`.

It returns the intrinsic gas.

- The gas limit covers the least gas limit of the fork.
- From Shapella, init code has at most the size that the fork allows.
- From Fusaka to BPO5, the gas limit is at most `2^24`, as EIP-7825 asks.
- From Glamsterdam, the gas limit is at most `2^32 - 1`, as EIP-8037 asks.
- From Glamsterdam, the intrinsic gas and the floor are at most `2^24` each, as EIP-8037 asks.
- The nonce is below `2^64 - 1`, as EIP-2681 asks.
- The priority fee is at most the maximum fee, as EIP-1559 asks.

Sources: [EIP-7825][eip-7825], [EIP-8037][eip-8037], [EIP-2681][eip-2681], [EIP-1559][eip-1559].

[eip-7825]: https://eips.ethereum.org/EIPS/eip-7825#specification
[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-validation
[eip-2681]: https://eips.ethereum.org/EIPS/eip-2681#specification
[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification -/
def validateTransaction (fork : Fork) (sender : Address) (tx : Transaction) :
    Except TransactionError Nat :=
  if tx.gas.toNat < minimumGas fork sender tx then
    .error (.insufficientGas (minimumGas fork sender tx) tx.gas.toNat)
  else if fork ≥ .shapella ∧ tx.to.isNone ∧ maxInitCodeSize fork < tx.data.size then
    .error (.initCodeTooLarge tx.data.size)
  else if fork ≥ .glamsterdam ∧ TX_MAX_TOTAL_GAS_LIMIT < tx.gas.toNat then
    .error (.gasLimitExceeded tx.gas.toNat)
  else if fork ≥ .glamsterdam ∧ TX_MAX_GAS_LIMIT < minimumGas fork sender tx then
    .error (.intrinsicGasAboveLimit (minimumGas fork sender tx))
  else if fork ≥ .fusaka ∧ fork < .glamsterdam ∧ TX_MAX_GAS_LIMIT < tx.gas.toNat then
    .error (.gasLimitExceeded tx.gas.toNat)
  else if 2 ^ 64 - 1 ≤ tx.nonce.toNat then
    .error .nonceOverflow
  else if feesInverted tx then
    .error .priorityFeeGreaterThanMaxFee
  else .ok (intrinsicGas fork sender tx)
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
        (fun h => h[0] != Cryptography.Kzg.VERSIONED_HASH_VERSION_KZG) then
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

The checks run in order: the chain, the signature, the gas and the nonce, then the contents.

The signature comes before the gas, since from Glamsterdam the intrinsic gas reads the sender. -/
def checkTransaction (fork : Fork) (chainId : UInt64) (tx : Transaction) :
    Except TransactionError (Address × Nat) := do
  checkChainId fork chainId tx
  let sender ← recoverSender fork tx
  let gas ← validateTransaction fork sender tx
  checkContents fork tx
  return (sender, gas)

end EthLib.Execution.Transactions
