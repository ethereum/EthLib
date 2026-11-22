module

public import EthLib.Base.Except
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

The step comments write the terms of `g_0` in the notation of §6.2, in ASCII.

Only `ethereum/execution-specs` writes out the order of the checks, in its [fork folders][es].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[es]: https://github.com/ethereum/execution-specs/tree/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks
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

/-- The nonce of a transaction, as a 256-bit word. -/
def nonce : Transaction → U256
  | .legacy tx => tx.nonce
  | .accessList tx => tx.nonce
  | .feeMarket tx => tx.nonce
  | .blob tx => tx.nonce
  -- A set-code transaction holds its nonce in 64 bits, which a word holds unchanged.
  | .setCode tx => BitVec.ofNat 256 tx.nonce.toNat

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
  -- `sum_{i in T_i, T_d} (G_txdatazero if i = 0, G_txdatanonzero otherwise)`, a term of `g_0`.
  --
  -- The sum is grouped: the zero bytes, then the other bytes.
  TX_DATA_PER_ZERO * zeroBytes data +
    (gasSchedule fork).TX_DATA_PER_NON_ZERO * (data.size - zeroBytes data)

/-- The price of an access list at `fork`, per address and per storage key.

[EIP-2930][eip-2930] adds it at Berlin, at 2400 and 1900 gas.

[EIP-8038][eip-8038] raises them to 2900 and 2000 at Glamsterdam.

[eip-2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
[eip-8038]: https://eips.ethereum.org/EIPS/eip-8038#parameters -/
def accessListCost (fork : Fork) (accessList : List Access) : Nat :=
  -- `sum_{j = 0}^{||T_A|| - 1} (G_accesslistaddress + ||T_A[j]_s|| G_accessliststorage)`.
  (accessList.map fun a => (gasSchedule fork).TX_ACCESS_LIST_ADDRESS +
    (gasSchedule fork).TX_ACCESS_LIST_STORAGE_KEY * a.slots.length).sum

/-- The bytes of an access list: 20 per address and 32 per storage key. -/
def accessListBytes (accessList : List Access) : Nat :=
  -- EIP-7981: 20 bytes for each address and 32 bytes for each storage key.
  (accessList.map fun a => 20 + 32 * a.slots.length).sum

/-- The data price of an access list from Glamsterdam: 64 gas per byte, 0 before.

[EIP-7981][eip-7981] adds it to the intrinsic gas and to the floor.

[eip-7981]: https://eips.ethereum.org/EIPS/eip-7981#specification -/
def accessListDataCost (fork : Fork) (accessList : List Access) : Nat :=
  if fork ≥ .glamsterdam then
    -- EIP-7981: 64 gas per byte of the access list.
    --
    -- The 64 is 4 floor tokens per byte, as in EIP-7976, times 16 gas per floor token.
    --
    -- The 4 per byte reuses the gas price of a token, which is also 4.
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
    -- EIP-2780: the sender pays `TX_BASE_COST`.
    TX_BASE_COST +
      -- The charge for the recipient depends on its kind.
      match tx.to with
      -- A contract creation costs `CREATE_ACCESS`.
      --
      -- A creation pays no value charge, which `CREATE_ACCESS` covers.
      | none => CREATE_ACCESS
      | some to =>
        -- A transfer to the sender itself costs nothing, for its value too.
        if to = sender then 0
        -- Any other recipient costs `COLD_ACCOUNT_ACCESS`.
        --
        -- A nonzero value then costs `TX_VALUE_COST`, and a zero value nothing.
        else (gasSchedule fork).COLD_ACCOUNT_ACCESS + if tx.value = 0 then 0 else TX_VALUE_COST
  -- `G_transaction`, a term of `g_0`.
  else TX_BASE

/-- The price of an authorization at `fork`.

[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#gas-costs) prices it at 25000.

[EIP-8037][eip-8037] lowers it to 7816 at Glamsterdam, and charges the rest at run time.

[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#parameter-changes -/
def authorizationCost (fork : Fork) : Nat :=
  -- From Glamsterdam, EIP-2780 charges this base cost for each authorization of EIP-7702.
  --
  -- Before, EIP-7702 charges `PER_EMPTY_ACCOUNT_COST` for each authorization.
  if fork ≥ .glamsterdam then EXECUTION_PER_AUTH_BASE_COST else AUTH_PER_EMPTY_ACCOUNT

/-- The price of a contract creation at `fork` beyond the base, for `size` bytes of init code.

It is 32000 from Homestead, by [EIP-2](https://eips.ethereum.org/EIPS/eip-2#specification).

From Shapella, it adds 2 gas per 32-byte word of init code.

[EIP-3860](https://eips.ethereum.org/EIPS/eip-3860#specification) adds that price.

From Glamsterdam, the base holds the price of the deployment, so only the init code remains. -/
def createCost (fork : Fork) (size : Nat) : Nat :=
  -- `G_txcreate + R(||T_i||)` if `T_t = {}`, a term of `g_0`; the caller checks `T_t = {}`.
  --
  -- `G_txcreate` is dropped from Glamsterdam, where the base holds `CREATE_ACCESS`.
  (if fork ≥ .glamsterdam then 0 else (gasSchedule fork).TX_CREATE) +
    -- `R(x) = G_initcodeword * ceil(x / 32)`, which EIP-3860 adds at Shapella.
    if fork ≥ .shapella then initCodeCost size else 0

/-- The intrinsic gas of a transaction from `sender`, at `fork`.

Only the base reads the sender, and only from Glamsterdam. -/
def intrinsicGas (fork : Fork) (sender : Address) (tx : Transaction) : Nat :=
  -- `g_0`, with `G_transaction` moved first, since the sum commutes.
  --
  -- Then the data of `T_i` or `T_d`.
  baseCost fork sender tx + dataCost fork tx.data +
    -- The creation term if `T_t = {}`, 0 otherwise.
    (if tx.to.isNone then createCost fork tx.data.size else 0) +
    -- The access list term, then the access list data of EIP-7981.
    accessListCost fork tx.accesses + accessListDataCost fork tx.accesses +
    -- The authorizations, which EIP-7702 adds.
    authorizationCost fork * tx.authorizations.length

/-- The tokens of call data: 1 per zero byte and 4 per nonzero byte. -/
def tokens (data : ByteArray) : Nat :=
  -- EIP-7623: the tokens are the zero bytes plus 4 times the nonzero bytes.
  zeroBytes data + 4 * (data.size - zeroBytes data)

/-- The floor tokens of call data at `fork`.

Before Glamsterdam they are the tokens.

From Glamsterdam, [EIP-7976][eip-7976] counts 4 tokens for every byte.

[eip-7976]: https://eips.ethereum.org/EIPS/eip-7976#specification -/
def floorTokens (fork : Fork) (data : ByteArray) : Nat :=
  -- EIP-7976 counts 4 floor tokens for every byte, zero or not.
  --
  -- The 4 per byte reuses the gas price of a token, which is also 4.
  --
  -- Before, the floor counts the tokens of EIP-7623.
  if fork ≥ .glamsterdam then TX_DATA_TOKEN_STANDARD * data.size else tokens data

/-- The call data floor of a transaction from `sender`, at `fork`.

It is the base, plus the floor price for each floor token, plus the data price of the access list.

[EIP-7623][eip-7623] adds it at Pectra, with 10 gas per token.

EIP-7976 raises the price to 16 at Glamsterdam, and EIP-2780 replaces 21000 by the base.

[eip-7623]: https://eips.ethereum.org/EIPS/eip-7623#specification -/
def calldataFloor (fork : Fork) (sender : Address) (tx : Transaction) : Nat :=
  -- EIP-7623: 21000 plus the floor price per token times the tokens.
  --
  -- The base stands for 21000, and EIP-7981 adds the data price of the access list.
  baseCost fork sender tx + (gasSchedule fork).TX_DATA_TOKEN_FLOOR * floorTokens fork tx.data +
    accessListDataCost fork tx.accesses

/-- The least gas limit of a transaction at `fork`: its intrinsic gas, and from Pectra the floor. -/
def minimumGas (fork : Fork) (sender : Address) (tx : Transaction) : Nat :=
  -- EIP-7623: the gas limit covers the larger of the intrinsic gas and the floor.
  if fork ≥ .pectra then max (intrinsicGas fork sender tx) (calldataFloor fork sender tx)
  else intrinsicGas fork sender tx

/-! ## The rules -/

/-- The most blobs of one transaction.

[EIP-7594](https://eips.ethereum.org/EIPS/eip-7594#specification) sets it at Fusaka. -/
def MAX_BLOBS_PER_TRANSACTION : Nat := 6

/-- Check the blobs and the authorizations of a transaction at `fork`.

- A blob transaction has at least one blob, and each versioned hash starts with `0x01`.
- From Fusaka, it has at most 6 blobs.
- A set code transaction has at least one authorization, as EIP-7702 asks.

Sources: [EIP-4844][eip-4844], [EIP-7594][eip-7594], [EIP-7702][eip-7702].

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#execution-layer-validation
[eip-7594]: https://eips.ethereum.org/EIPS/eip-7594#specification
[eip-7702]: https://eips.ethereum.org/EIPS/eip-7702#set-code-transaction -/
def checkContents (fork : Fork) : Transaction → Except TransactionError Unit
  | .blob tx =>
    -- A blob transaction fails without a blob.
    if tx.blobVersionedHashes.isEmpty then .error .noBlobData
    -- From Fusaka, it fails with more than 6 blobs.
    else if fork ≥ .fusaka ∧ MAX_BLOBS_PER_TRANSACTION < tx.blobVersionedHashes.length then
      .error (.blobCountExceeded tx.blobVersionedHashes.length)
    -- It fails when the first byte of a versioned hash is not the KZG version `0x01`.
    else if tx.blobVersionedHashes.any
        (fun h => h[0] != Cryptography.Kzg.VERSIONED_HASH_VERSION_KZG) then
      -- Some hash has the wrong version, so the first such hash has an index below the length.
      let index := tx.blobVersionedHashes.findIdx
        (fun h => h[0] != Cryptography.Kzg.VERSIONED_HASH_VERSION_KZG)
      .error (.invalidBlobVersionedHash index (tx.blobVersionedHashes.getD index 0))
    else .ok ()
  -- A set code transaction fails without an authorization.
  --
  -- A blob or set code transaction always has a recipient here, so a check of it is moot.
  | .setCode tx => if tx.authorizations.isEmpty then .error .emptyAuthorizationList else .ok ()
  | _ => .ok ()

/-- The rules of a transaction that a simulation lifts.

By default every rule holds, as in a real block.

[EIP-8037][eip-8037] adds the two caps on the gas.

[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-validation -/
structure LiftedRules where
  /-- Skip the check that the nonce of the transaction is the nonce of its sender. -/
  nonce : Bool := false
  /-- Lift the caps at `2^24` on the intrinsic gas, the floor and the execution gas.

  They exist from Glamsterdam; the cap of Fusaka to BPO5 stays. -/
  gasCap : Bool := false
  /-- Lift the cap at `2^32 - 1` on the gas limit, which a simulation does in both modes. -/
  totalGasCap : Bool := false
  /-- Let a transaction with a maximum fee per gas of 0 pay for its gas at a base fee of 0.

  It then passes the check of the base fee, and pays nothing for its gas. -/
  zeroFee : Bool := false
  deriving DecidableEq, Repr

/-- Check the type, the fees, the gas limit and the nonce of a transaction from `sender` at `fork`.

It returns the intrinsic gas.

- The type of the transaction exists at the fork.
- The gas limit covers the least gas limit of the fork.
- From Shapella, init code has at most the size that the fork allows.
- From Fusaka to BPO5, the gas limit is at most `2^24`, as EIP-7825 asks.
- From Glamsterdam, the gas limit is at most `2^32 - 1`, as EIP-8037 asks.
- From Glamsterdam, the intrinsic gas and the floor are at most `2^24` each, as EIP-8037 asks.
- The nonce is below `2^64 - 1`, as EIP-2681 asks.
- The priority fee is at most the maximum fee, as EIP-1559 asks.
- From Glamsterdam, the blobs and the authorizations pass their rules.

The first rule that fails gives the error, and the body marks the order of each fork.

A simulation can lift the caps of Glamsterdam on the gas.

A typed transaction exists from the fork of the EIP that adds its type to [EIP-2718][eip-2718]:

- type 1 from Berlin, by [EIP-2930][eip-2930];
- type 2 from London, by [EIP-1559][eip-1559];
- type 3 from Dencun, by [EIP-4844][eip-4844];
- type 4 from Pectra, by [EIP-7702][eip-7702].

Decoding rejects such a type too, and this rule also covers a transaction built without bytes.

Sources: [EIP-7825][eip-7825], [EIP-8037][eip-8037], [EIP-2681][eip-2681], [EIP-1559][eip-1559].

[eip-2718]: https://eips.ethereum.org/EIPS/eip-2718#specification
[eip-2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#blob-transaction
[eip-7702]: https://eips.ethereum.org/EIPS/eip-7702#set-code-transaction
[eip-7825]: https://eips.ethereum.org/EIPS/eip-7825#specification
[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-validation
[eip-2681]: https://eips.ethereum.org/EIPS/eip-2681#specification
[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification -/
def validateTransaction (fork : Fork) (sender : Address) (tx : Transaction)
    (lifted : LiftedRules := {}) : Except TransactionError Nat := do
  -- The checks are named first and run below in the order of each fork.
  --
  -- The gas limit covers the larger of the intrinsic gas and the floor, which the source splits.
  let minimum := minimumGas fork sender tx
  let coversMinimum := ensure (minimum ≤ tx.gas.toNat) (.insufficientGas minimum tx.gas.toNat)
  -- From Shapella, the init code of a creation is at most the largest init code size of the fork.
  let initCodeFits := ensure (fork ≥ .shapella → tx.to = none → tx.data.size ≤ maxInitCodeSize fork)
    (.initCodeTooLarge tx.data.size)
  -- The nonce is below `2^64 - 1`.
  let nonceFits := ensure (tx.nonce.toNat < 2 ^ 64 - 1) (.nonceOverflow tx.nonce.toNat)
  -- The priority fee per gas is at most the maximum fee per gas, for a fee market transaction.
  let feesOrdered := ensure (feesInverted tx = false)
    (.priorityFeeGreaterThanMaxFee (feeCaps tx).1 (feeCaps tx).2)
  -- First at every fork: the type exists at the fork.
  --
  -- The sources reject an unknown type when they decode it.
  ensure (tx.fork ≤ fork) (.unsupportedType tx.type)
  if fork ≥ .glamsterdam then
    -- From Glamsterdam: the nonce, the init code, then the gas limit is at most `2^32 - 1`.
    nonceFits
    initCodeFits
    -- A simulation may lift this cap; the source has no such mode.
    unless lifted.totalGasCap do
      ensure (tx.gas.toNat ≤ TX_MAX_TOTAL_GAS_LIMIT) (.gasLimitExceeded tx.gas.toNat)
    -- Then the fees, then the blobs and the authorizations.
    feesOrdered
    checkContents fork tx
    -- Then the gas limit covers the intrinsic gas and the floor, in one check.
    coversMinimum
    -- Then the intrinsic gas and the floor are each at most `2^24`.
    --
    -- The two are one check on their maximum, so the error carries that maximum.
    --
    -- A simulation may lift this cap; the source has no such mode.
    unless lifted.gasCap do ensure (minimum ≤ TX_MAX_GAS_LIMIT) (.intrinsicGasAboveLimit minimum)
  else
    -- Before Glamsterdam: the gas, the init code, then from Fusaka the gas limit is at most `2^24`.
    coversMinimum
    initCodeFits
    ensure (fork ≥ .fusaka → tx.gas.toNat ≤ TX_MAX_GAS_LIMIT) (.gasLimitExceeded tx.gas.toNat)
    -- Then the nonce and the fees.
    nonceFits
    feesOrdered
  -- The intrinsic gas; the floor is computed again where the gas is settled.
  return intrinsicGas fork sender tx
where
  /-- Whether the priority fee per gas is above the maximum fee per gas. -/
  feesInverted : Transaction → Bool
    | .feeMarket tx => tx.maxFeePerGas.toNat < tx.maxPriorityFeePerGas.toNat
    | .blob tx => tx.maxFeePerGas.toNat < tx.maxPriorityFeePerGas.toNat
    | .setCode tx => tx.maxFeePerGas.toNat < tx.maxPriorityFeePerGas.toNat
    | _ => false
  /-- The priority fee per gas and the maximum fee per gas, of a transaction that has both.

  A transaction without them gives zeros, and the fee check never fails on it. -/
  feeCaps : Transaction → Nat × Nat
    | .feeMarket tx => (tx.maxPriorityFeePerGas.toNat, tx.maxFeePerGas.toNat)
    | .blob tx => (tx.maxPriorityFeePerGas.toNat, tx.maxFeePerGas.toNat)
    | .setCode tx => (tx.maxPriorityFeePerGas.toNat, tx.maxFeePerGas.toNat)
    | _ => (0, 0)

/-- Check that a transaction signs no chain, or the chain `chainId` of the network. -/
def checkChainId (fork : Fork) (chainId : UInt64) (tx : Transaction) :
    Except TransactionError Unit := do
  -- EIP-155 and the typed transactions of EIP-2718 sign a chain; a pre-EIP-155 signature does not.
  match ← tx.chainId fork with
  | none => .ok ()
  | some c =>
    if c.toNat = chainId.toNat then .ok () else .error (.wrongChainId chainId.toNat c.toNat)

/-- Check a transaction alone, at `fork` on the chain `chainId`.

It returns the sender and the intrinsic gas.

The checks run in order: the chain, the signature, the type, the gas and nonce, then the contents.

The signature comes before the gas, since from Glamsterdam the intrinsic gas reads the sender.

From Glamsterdam the gas and nonce rules check the contents already. -/
def checkTransaction (fork : Fork) (chainId : UInt64) (tx : Transaction) :
    Except TransactionError (Address × Nat) := do
  -- From Glamsterdam the source checks the chain, then the sender, then the rest with the sender.
  --
  -- Before, it checks the transaction alone before the chain and the sender.
  --
  -- Here the chain and the signature come first at every fork.
  --
  -- So before Glamsterdam, one that also fails a gas or nonce rule reports the chain or signature.
  checkChainId fork chainId tx
  let sender ← recoverSender fork tx
  let gas ← validateTransaction fork sender tx
  -- Before Glamsterdam, the blobs and the authorizations come last.
  --
  -- The source checks them after the fee checks of the block, kept apart here.
  if fork < .glamsterdam then checkContents fork tx
  return (sender, gas)

end EthLib.Execution.Transactions
