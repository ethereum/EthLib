module

public import EthLib.Execution.Rpc.Fees
public import EthLib.Execution.Transactions.Inclusion
public import EthLib.Execution.Transactions.Network

/-!
# `Execution.Rpc.Submit`

The method `eth_sendRawTransaction` of [`submit.yaml`][submit]: it submits a signed transaction.

Its parameter is the raw form of the transaction, and its result is the hash of the transaction.

The raw form of a blob transaction is its network form, with its blobs, commitments and proofs.

The source says so for EIP-4844, with its KZG proofs, and for EIP-7594, with cell proofs.

It also says that a node rejects cell proofs before the PeerDAS fork of EIP-7594.

That fork is Fusaka.

From Fusaka, the source says that a node "may" still accept proofs per blob and convert them.

The conversion computes the cell proofs of each blob, and the source calls it expensive.

This method takes the choice that the word "may" leaves, and rejects that form from Fusaka.

The hash is that of the transaction alone, without its blobs, commitments and proofs.

Which transactions a pool keeps is the choice of the node, and the source does not fix it.

Here the pool accepts each transaction that passes these checks:

- its raw form decodes at the fork of the next block;
- the counts of its blobs, commitments and proofs match, and each commitment has its hash;
- its KZG proofs verify against the trusted setup of the view;
- the inclusion checks pass in the next block, against the state of the head.

The next block is taken one second after the head, its earliest time, as in the fee history.

Its fork, base fees and blob schedule are those that the fee history gives it.

So in the last slot before a fork by time, a transaction is decoded at the fork before it.

Its gas limit is that of the head, and no transaction runs before this one.

A nonce above that of the sender is a future transaction, which a pool may keep for later.

So the checks read the state of the head with the nonce of the sender raised to that nonce.

A nonce below that of the sender still fails.

A raw form that does not decode, or whose blobs fail their counts, hashes or proofs, gets `-32000`.

A failed inclusion check gets the code of the error groups that names its condition.

A failed inclusion check that no code names gets `-32003`, "Transaction rejected".

[submit]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/submit.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Evm (BlockEnvironment)
open EthLib.Execution.Fees.BlobBaseFee (chainBlobSchedule)
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions
open EthLib.Serialization.JsonRpc (RpcError)

/-- A transaction in its raw form: a transaction, or the network form of a blob transaction. -/
inductive RawTransaction where
  /-- A transaction that is not a blob transaction, in the form of a block. -/
  | plain (tx : Transaction)
  /-- A blob transaction with its blobs, commitments and proofs. -/
  | network (w : NetworkBlobTransaction)

/-- The transaction of a raw form, without blobs, commitments or proofs. -/
def RawTransaction.tx : RawTransaction → Transaction
  | .plain tx => tx
  | .network w => .blob w.tx

/-- The transaction that the raw form `bytes` holds at `fork`.

From Dencun, a blob transaction must come in its network form at that fork. -/
def decodeRawTransaction (fork : Fork) (bytes : ByteArray) : Except NetworkError RawTransaction :=
  if bytes.data[0]? = some 3 ∧ .dencun ≤ fork then .network <$> decodeNetwork fork bytes
  else (.plain <$> decodeTransaction fork bytes).mapError .transaction

/-- The groups of error codes that the method lists in the source. -/
def submitErrorGroups : List ErrorGroup :=
  [rpcStandardErrors, rpcNonStandardErrors, gasErrors, executionErrors, txPoolErrors]

/-- The code of the error groups that names the condition of a failed inclusion check, if any.

The code 800 says "Intrinsic gas too low / Intrinsic gas exceeds gas limit".

A gas limit of a transaction below its intrinsic gas, or below the floor of EIP-7623, gets 800.

An intrinsic gas above the cap of EIP-7825 gets no code, since that cap is not a gas limit.

The method checks a transaction with no gas used before it in the block.

So the gas allowance of the block is exceeded exactly when the gas limit is above the block's.

That is the condition of 803.

The cost behind 809 also counts the blob gas at its fee cap, beyond "gas * price + value". -/
def rpcCode : InclusionError → Option ErrorCode
  | .transaction (.insufficientGas ..) => some intrinsicGasTooLow
  | .gasAllowanceExceeded .. => some gasLimitAboveBlock
  | .transaction (.priorityFeeGreaterThanMaxFee) => some priorityFeeAboveCap
  | .transaction (.invalidSignature) => some invalidSender
  | .insufficientMaxFeePerGas .. => some feeCapBelowBaseFee
  | .nonceTooLow .. => some nonceTooLow
  | .nonceTooHigh .. => some nonceTooHigh
  | .insufficientBalance .. => some insufficientFunds
  | _ => none

/-- What makes a transaction invalid, as the data of its error. -/
def transactionErrorText : TransactionError → String
  | .emptyTransaction => "the input holds no transaction"
  | .unsupportedType type => s!"transaction type {type.toNat} does not exist at the fork"
  | .decoding _ => "the RLP of the transaction does not decode"
  | .encoding _ => "the signed fields of the transaction have no RLP encoding"
  | .invalidSignature => "the signature names no sender"
  | .insufficientGas needed gas =>
    s!"gas limit {gas} is below {needed}, the intrinsic gas or the call data floor"
  | .initCodeTooLarge size => s!"init code of {size} bytes is above the limit"
  | .gasLimitExceeded gas => s!"gas limit {gas} is above the limit of a transaction"
  | .nonceOverflow => "the nonce is at least 2^64 - 1"
  | .priorityFeeGreaterThanMaxFee => "the priority fee per gas is above the maximum fee per gas"
  | .wrongChainId expected actual => s!"chain ID {actual}, not {expected}"
  | .noBlobData => "a blob transaction carries no blob"
  | .blobCountExceeded count => s!"{count} blobs are above the limit"
  | .invalidBlobVersionedHash => "a versioned hash has the wrong version"
  | .emptyAuthorizationList => "a set code transaction carries no authorization"
  | .intrinsicGasAboveLimit gas =>
    s!"intrinsic gas or floor {gas} is above the limit of a transaction"

/-- Why a transaction cannot enter its block, as the data of its error. -/
def inclusionErrorText : InclusionError → String
  | .transaction e => transactionErrorText e
  | .gasAllowanceExceeded gas available => s!"gas {gas} is above the {available} left in the block"
  | .blobGasLimitExceeded blobGas available =>
    s!"blob gas {blobGas} is above the {available} left in the block"
  | .insufficientMaxFeePerGas maxFee baseFee =>
    s!"maximum fee per gas {maxFee} is below the base fee {baseFee}"
  | .insufficientMaxFeePerBlobGas maxFee blobGasPrice =>
    s!"maximum fee per blob gas {maxFee} is below the blob gas price {blobGasPrice}"
  | .nonceTooLow expected nonce => s!"nonce {nonce} is below the nonce {expected} of the sender"
  | .nonceTooHigh expected nonce => s!"nonce {nonce} is above the nonce {expected} of the sender"
  | .insufficientBalance balance cost => s!"balance {balance} is below the cost {cost}"
  | .senderNotEoa => "the sender has code that is not an allowed delegation"
  | .missingCode _ => "the state does not hold the code of the sender"

/-- The error object of a failed check: the code of its condition, else `-32003`. -/
def submitError (e : InclusionError) : RpcError :=
  ((rpcCode e).getD transactionRejected).toRpcError (some (.str (inclusionErrorText e)))

/-- What makes a raw form invalid, as the data of its error. -/
def networkErrorText : NetworkError → String
  | .transaction e => transactionErrorText e
  | .wrongVersion version => s!"wrapper version {version}, not 1"
  | .countMismatch .. => "the counts of blobs, commitments and proofs do not match"
  | .versionedHashMismatch => "a commitment does not hash to its versioned hash"
  | .kzg _ => "a blob, a commitment or a proof is not a valid KZG input"
  | .proofRejected => "the proofs do not match the blobs"

/-- A state in which the sender has the nonce of a transaction, when that nonce is the higher.

The other fields of the account are those of the state. -/
def withFutureNonce (state : TransactionState) (sender : Address) (tx : Transaction) :
    TransactionState :=
  let account := state.getAccount sender
  if account.nonce < tx.nonce.toNat then
    state.setAccount sender (some { account with nonce := tx.nonce.toNat })
  else state

namespace ChainView

/-- The environment of the next block, in which a submitted transaction is checked.

It is one second after the head.

Its fork, base fee and blob schedule are those of the fee history.

Its excess blob gas is the one that the header rule gives it.

Its gas limit is that of the head, and its other fields are those of the head or 0. -/
def nextEnvironment (v : ChainView) : BlockEnvironment (v.head.nextFork v.config) :=
  let head := v.head
  let header := head.block.header
  let fork := head.nextFork v.config
  let schedule := chainBlobSchedule v.config fork (header.number + 1) (header.timestamp.toNat + 1)
  { chainId := v.config.chainId
    coinbase := header.coinbase
    number := header.number + 1
    gasLimit := header.gasLimit
    timestamp := header.timestamp + 1
    difficulty := 0
    blockHashes := []
    baseFeePerGas := fun _ => head.nextBaseFee v.config
    prevRandao := fun _ => 0
    excessBlobGas := fun h =>
      if hLondon : .london ≤ head.fork then
        (expectedExcessBlobGas hLondon h header schedule).toUInt64
      else 0
    parentBeaconBlockRoot := fun _ => 0
    slotNumber := fun _ => 0
    blobSchedule := schedule }

/-- The hash of a submitted transaction, or the error of the check that it fails. -/
def sendRawTransaction (v : ChainView) (bytes : ByteArray) : Except RpcError Hash32 := do
  let fork := v.head.nextFork v.config
  let invalid := fun (e : NetworkError) =>
    invalidInput.toRpcError (some (.str (networkErrorText e)))
  let raw ← (decodeRawTransaction fork bytes).mapError invalid
  if let .network w := raw then
    (validateNetwork v.setup fork w).mapError invalid
  let head := TransactionState.ofBlock ⟨v.head.state, ∅, ∅, ∅, ∅⟩
  -- A signature that names no sender fails in the inclusion checks, with its own code.
  let state := match recoverSender fork raw.tx with
    | .ok sender => withFutureNonce head sender raw.tx
    | .error _ => head
  discard <| (checkInclusion v.config.chainId v.nextEnvironment ⟨0, 0, 0⟩ state raw.tx).mapError
    submitError
  (transactionHash raw.tx).mapError fun _ =>
    internalError.toRpcError (some (.str "transaction hash: the transaction has no RLP encoding"))

end ChainView

end EthLib.Execution.Rpc
