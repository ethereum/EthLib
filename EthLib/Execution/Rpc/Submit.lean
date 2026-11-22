module

public import EthLib.Execution.Rpc.Fees
public import EthLib.Execution.Transactions.Inclusion
public import EthLib.Execution.Transactions.Network

/-!
# `Execution.Rpc.Submit`

The method `eth_sendRawTransaction` of [`submit.yaml`][submit]: it submits a signed transaction.

Its parameter is the raw form of the transaction, and its result is the hash of the transaction.

The raw form of a blob transaction is its network form, with its blobs, commitments and proofs.

The source asks for proofs per blob by EIP-4844, and for cell proofs from Fusaka by EIP-7594.

From Fusaka, the source lets a node still accept proofs per blob and convert them, at a cost.

EthLib takes the stricter choice and rejects that form from Fusaka.

Which transactions a pool keeps is the choice of the node, and the source does not fix it.

EthLib keeps each transaction that the next block could include, a future nonce allowed.

The next block is EthLib's choice: one second after the head, as in the fee history.

So in the last slot before a fork by time, a transaction is decoded at the fork before it.

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

An intrinsic gas above the cap of EIP-7825 gets no code, since that cap is not a gas limit. -/
def rpcCode : InclusionError → Option ErrorCode
  -- A gas limit below the intrinsic gas, or below the floor of EIP-7623: 800.
  | .transaction (.insufficientGas ..) => some intrinsicGasTooLow
  -- No gas is used before, so the block's gas is exceeded exactly above its gas limit: 803.
  | .gasAllowanceExceeded .. => some gasLimitAboveBlock
  -- A priority fee above the fee cap: 804.
  | .transaction (.priorityFeeGreaterThanMaxFee ..) => some priorityFeeAboveCap
  -- A signature that names no sender: 1001.
  | .transaction (.invalidSignature) => some invalidSender
  -- A fee cap below the base fee: 806.
  | .insufficientMaxFeePerGas .. => some feeCapBelowBaseFee
  -- A nonce below or above that of the sender: 1 or 2.
  | .nonceTooLow .. => some nonceTooLow
  | .nonceTooHigh .. => some nonceTooHigh
  -- A balance below the cost, which also counts the blob gas at its fee cap: 809.
  | .insufficientBalance .. => some insufficientFunds
  -- Any other condition, which no code of the groups names.
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
  | .nonceOverflow nonce => s!"the nonce {nonce} is at least 2^64 - 1"
  | .priorityFeeGreaterThanMaxFee priorityFee maxFee =>
    s!"the priority fee per gas {priorityFee} is above the maximum fee per gas {maxFee}"
  | .wrongChainId expected actual => s!"chain ID {actual}, not {expected}"
  | .noBlobData => "a blob transaction carries no blob"
  | .blobCountExceeded count => s!"{count} blobs are above the limit"
  | .invalidBlobVersionedHash index hash =>
    s!"versioned hash {index}, {hexString hash.toList}, has the wrong version"
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
  | .senderNotEoa sender =>
    s!"the sender {hexString sender.toList} has code that is not an allowed delegation"
  | .missingCode _ => "the state does not hold the code of the sender"

/-- The error object of a failed check: the code of its condition, else `-32003`. -/
def submitError (e : InclusionError) : RpcError :=
  -- EthLib's choice: -32003, Transaction rejected, for a condition that no code names.
  ((rpcCode e).getD transactionRejected).toRpcError (some (.str (inclusionErrorText e)))

/-- What makes a raw form invalid, as the data of its error. -/
def networkErrorText : NetworkError → String
  | .transaction e => transactionErrorText e
  | .wrongVersion version => s!"wrapper version {version}, not 1"
  | .countMismatch .. => "the counts of blobs, commitments and proofs do not match"
  | .versionedHashMismatch index _ _ => s!"commitment {index} does not hash to its versioned hash"
  | .kzg _ => "a blob, a commitment or a proof is not a valid KZG input"
  | .proofRejected => "the proofs do not match the blobs"

/-- A state in which the sender has the nonce of a transaction, when that nonce is the higher.

The other fields of the account are those of the state. -/
def withFutureNonce (state : TransactionState) (sender : Address) (tx : Transaction) :
    TransactionState :=
  let account := state.getAccount sender
  -- A nonce above that of the sender raises it, so that a future transaction passes.
  --
  -- A nonce below it is left, and still fails.
  if account.nonce < tx.nonce.toNat then
    state.setAccount sender (some { account with nonce := tx.nonce.toNat })
  else state

namespace ChainView

/-- The blob schedule of the next block, one second after the head. -/
def nextBlobSchedule (v : ChainView) : Since .dencun (v.head.nextFork v.config) BlobSchedule :=
  let header := v.head.block.header
  chainBlobSchedule v.config (v.head.nextFork v.config) (header.number + 1)
    (header.timestamp.toNat + 1)

/-- The excess blob gas of the next block, by EIP-4844 and EIP-7918, or 0 before Dencun. -/
def nextExcessBlobGas (v : ChainView) : Nat :=
  let header := v.head.block.header
  childExcessBlobGas v.config (v.head.nextFork v.config) header (header.number + 1)
    (header.timestamp.toNat + 1)

/-- The environment of the next block, in which a submitted transaction is checked.

Its excess blob gas must fit 64 bits. -/
def nextEnvironment (v : ChainView) (fits : v.nextExcessBlobGas < 2 ^ 64) :
    BlockEnvironment (v.head.nextFork v.config) :=
  let head := v.head
  let header := head.block.header
  -- EthLib's choice: the block after the head, one second later, with the head's gas limit.
  { chainId := v.config.chainId
    coinbase := header.coinbase
    number := header.number + 1
    gasLimit := header.gasLimit
    timestamp := header.timestamp + 1
    -- A field that no check reads: 0, or empty.
    difficulty := 0
    blockHashes := []
    -- The base fee of EIP-1559 after the head, as the fee history gives it.
    baseFeePerGas := fun _ => head.nextBaseFee v.config
    -- A field that no check reads: 0.
    prevRandao := fun _ => 0
    -- The excess blob gas after the head, by EIP-4844 and from Fusaka by EIP-7918.
    excessBlobGas := fun _ => UInt64.ofNatLT v.nextExcessBlobGas fits
    -- A field that no check reads: 0.
    parentBeaconBlockRoot := fun _ => 0
    slotNumber := fun _ => 0
    -- The blob schedule of the chain at that number and time, as in the fee history.
    blobSchedule := v.nextBlobSchedule }

/-- The hash of a submitted transaction, or the error of the check that it fails.

When the next block's excess blob gas is `2^64` or more, the result is an internal error.

No header holds such an excess. -/
def sendRawTransaction (v : ChainView) (bytes : ByteArray) : Except RpcError Hash32 := do
  -- The fork of the next block, one second after the head.
  let fork := v.head.nextFork v.config
  let invalid := fun (e : NetworkError) =>
    invalidInput.toRpcError (some (.str (networkErrorText e)))
  -- The raw form decodes at that fork, else code -32000, EthLib's choice.
  --
  -- Before Fusaka, a form with cell proofs fails here, as the source asks.
  --
  -- From Fusaka, a form with proofs per blob has no wrapper version, so it fails here too.
  let raw ← (decodeRawTransaction fork bytes).mapError invalid
  -- EIP-4844 and EIP-7594: the counts, the versioned hashes and the proofs.
  --
  -- The proofs verify against the trusted setup of the view, else code -32000, EthLib's choice.
  if let .network w := raw then
    (validateNetwork v.setup fork w).mapError invalid
  -- The state of the head, with no transaction before this one.
  let head := TransactionState.ofBlock ⟨v.head.state, ∅, ∅, ∅, ∅⟩
  -- A signature that names no sender fails in the inclusion checks, with its own code.
  let state := match recoverSender fork raw.tx with
    | .ok sender => withFutureNonce head sender raw.tx
    | .error _ => head
  -- The header holds the excess blob gas in 64 bits, so a larger excess builds no next block.
  let some env := if h : v.nextExcessBlobGas < 2 ^ 64 then some (v.nextEnvironment h) else none
    | throw (internalError.toRpcError
        (some (.str "next block: the excess blob gas is 2^64 or more")))
  -- The inclusion checks in the next block, with no gas used before, else their code.
  discard <| (checkInclusion v.config.chainId env ⟨0, 0, 0⟩ state raw.tx).mapError submitError
  -- EIP-4844: the hash of the transaction alone, without its blobs, commitments and proofs.
  (transactionHash raw.tx).mapError fun _ =>
    internalError.toRpcError (some (.str "transaction hash: the transaction has no RLP encoding"))

end ChainView

end EthLib.Execution.Rpc
