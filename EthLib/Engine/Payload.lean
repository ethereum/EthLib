module

public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Transactions.Types

/-!
# `Engine.Payload`

The structures that the Engine API passes between the consensus and the execution layers.

An execution payload carries the fields of an execution block that the consensus layer keeps.

Its version follows the fork: 1 at Paris, 2 at Shapella, 3 from Dencun to BPO5, 4 at Glamsterdam.

The Engine API calls the execution side of Glamsterdam Amsterdam.

Versions 2 and 3 append fields to the one before, so one type with fields by fork holds the three.

Version 4 appends the block access list of EIP-7928 and the slot number of EIP-7843.

The header holds the hash of the list and the slot number, and the body holds neither.

So the type keeps these two fields apart, and the method passes them beside the payload.

A withdrawal of the Engine API has the four fields of a withdrawal of the execution layer.

The Engine API specification defines each structure, at commit `3284ee8` of execution-apis:

- [`ExecutionPayloadV1`][v1], [`ForkchoiceStateV1`][fcs] and [`PayloadStatusV1`][status]
- [`WithdrawalV1`][withdrawal] and [`ExecutionPayloadV2`][v2]
- [`ExecutionPayloadV3`][v3]
- [`ExecutionPayloadV4`][v4]
- the error codes, in [Errors][errors]

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#executionpayloadv1
[fcs]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#forkchoicestatev1
[status]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payloadstatusv1
[withdrawal]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#withdrawalv1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#executionpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#executionpayloadv3
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#executionpayloadv4
[errors]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/common.md#errors
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Execution.Transactions (TransactionError)

/-- An execution payload at fork `fork`, from Paris on. -/
structure ExecutionPayload (fork : Fork) : Type where
  /-- The hash of the parent block. -/
  parentHash : Hash32
  /-- The account that receives the fees of the block. -/
  feeRecipient : Address
  /-- The root of the state trie after the block. -/
  stateRoot : Hash32
  /-- The root of the trie of the receipts. -/
  receiptsRoot : Hash32
  /-- The Bloom filter of the logs of the block. -/
  logsBloom : Bytes256
  /-- The RANDAO mix that the block reads. -/
  prevRandao : Bytes32
  /-- The number of the block. -/
  blockNumber : UInt64
  /-- The most gas that the transactions of the block may use. -/
  gasLimit : UInt64
  /-- The gas that the transactions of the block use. -/
  gasUsed : UInt64
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : UInt64
  /-- Free bytes that the producer of the block chooses. -/
  extraData : ByteArray
  /-- The base fee per gas. -/
  baseFeePerGas : U256
  /-- The hash of the header of the block. -/
  blockHash : Hash32
  /-- The bytes of each transaction, in the order that they run. -/
  transactions : List ByteArray
  /-- The withdrawals, from Shapella. -/
  withdrawals : Since .shapella fork (List Withdrawal)
  /-- The blob gas that the transactions use, from Dencun. -/
  blobGasUsed : Since .dencun fork UInt64
  /-- The blob gas above the target before the block, from Dencun. -/
  excessBlobGas : Since .dencun fork UInt64

/-- The three blocks that the consensus layer names to the execution layer. -/
structure ForkchoiceState where
  /-- The head of the canonical chain. -/
  headBlockHash : Hash32
  /-- The safe block, which must be the head or one of its ancestors.

  It may be all zero bytes while the chain has no safe block. -/
  safeBlockHash : Hash32
  /-- The most recent finalized block.

  It may be all zero bytes while the chain has no finalized block. -/
  finalizedBlockHash : Hash32
  deriving DecidableEq, Repr

/-- The verdict of the execution layer on a payload. -/
inductive Status where
  /-- The payload and its ancestors are valid. -/
  | valid
  /-- The payload or one of its ancestors is not valid. -/
  | invalid
  /-- The execution layer lacks the data to validate the payload. -/
  | syncing
  /-- The payload is well formed, but its branch is not validated yet. -/
  | accepted
  /-- The block hash of the payload is wrong; only version 1 of the method returns it. -/
  | invalidBlockHash
  deriving DecidableEq, Repr

/-- The name of a status, as the Engine API writes it. -/
def Status.name : Status → String
  | .valid => "VALID"
  | .invalid => "INVALID"
  | .syncing => "SYNCING"
  | .accepted => "ACCEPTED"
  | .invalidBlockHash => "INVALID_BLOCK_HASH"

/-- The result of processing a payload.

The Engine API also allows a free message on an error, which is not part of the verdict. -/
structure PayloadStatus where
  /-- The verdict. -/
  status : Status
  /-- The most recent valid block of the branch of the payload, if the execution layer knows it. -/
  latestValidHash : Option Hash32
  deriving DecidableEq, Repr

/-- An error that a method returns instead of a result. -/
inductive EngineError where
  /-- The parameters do not have the structure that the method expects. -/
  | invalidParams (reason : String)
  /-- The payload belongs to a fork that the method does not support. -/
  | unsupportedFork
  /-- The safe or the finalized block is not on the chain of the head. -/
  | invalidForkchoiceState
  /-- The request names more items than the execution layer takes in one request. -/
  | tooLargeRequest
  /-- The payload attributes do not have a structure that the version of the method takes. -/
  | invalidPayloadAttributes
  /-- No build process has the requested payload ID. -/
  | unknownPayload
  deriving DecidableEq, Repr

/-- The code of an error: its JSON-RPC code is the negative of this number. -/
def EngineError.code : EngineError → UInt32
  | .invalidParams _ => 32602
  | .unsupportedFork => 38005
  | .invalidForkchoiceState => 38002
  | .tooLargeRequest => 38004
  | .invalidPayloadAttributes => 38003
  | .unknownPayload => 38001

/-- Why a payload is not valid, before its transactions run or when they run. -/
inductive PayloadError where
  /-- The transaction at an index, from 0, does not decode at the fork of the payload. -/
  | invalidTransaction (index : Nat) (error : TransactionError)
  /-- A root or the header of the block has no encoding, since a field is too long. -/
  | noEncoding
  /-- The block hash of the payload is not the hash of the header that it gives. -/
  | wrongBlockHash (expected computed : Hash32)
  /-- The expected versioned hashes are not those of the blob transactions, in order. -/
  | wrongVersionedHashes
  /-- The block of the payload fails the state transition, with `error`. -/
  | invalidBlock (error : Execution.Blocks.BlockError)
  /-- The block access list is not the RLP encoding of a block access list. -/
  | invalidBlockAccessList
  deriving DecidableEq, Repr

/-- The stable code of a reason, one per constructor, for the C exports.

The codes start at 401, above the codes of the errors of a block.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PayloadError.code : PayloadError → UInt32
  | .invalidTransaction .. => 401
  | .noEncoding => 402
  | .wrongBlockHash .. => 403
  | .wrongVersionedHashes => 404
  | .invalidBlock _ => 405
  | .invalidBlockAccessList => 406

end EthLib.Engine
