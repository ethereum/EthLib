module

public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Transactions.Types

/-!
# `Engine.Payload`

The structures that the Engine API passes between the consensus and the execution layers.

The Engine API calls the execution side of Glamsterdam Amsterdam.

Sources, at commit `1ca0818` of execution-apis:

- [`ExecutionPayloadV1`][v1], [`ForkchoiceStateV1`][fcs] and [`PayloadStatusV1`][status]
- [`WithdrawalV1`][withdrawal] and [`ExecutionPayloadV2`][v2]
- [`ExecutionPayloadV3`][v3]
- [`ExecutionPayloadV4`][v4]
- the error codes, in [Errors][errors]

[v1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#executionpayloadv1
[fcs]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#forkchoicestatev1
[status]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payloadstatusv1
[withdrawal]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#withdrawalv1
[v2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#executionpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#executionpayloadv3
[v4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#executionpayloadv4
[errors]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#errors
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Execution.Transactions (TransactionError)

/-- An execution payload at fork `fork`, from Paris on.

It carries the fields of an execution block that the consensus layer keeps.

Its version follows the fork: 1 at Paris, 2 at Shapella, 3 from Dencun to BPO5, 4 at Glamsterdam.
-/
structure ExecutionPayload (fork : Fork) : Type where
  -- `ExecutionPayloadV1`, in its order: `DATA` of 32, 20, 32, 32, 256 and 32 bytes.
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
  -- `blockNumber`, `gasLimit`, `gasUsed` and `timestamp`: `QUANTITY` of 64 bits.
  /-- The number of the block. -/
  blockNumber : UInt64
  /-- The most gas that the transactions of the block may use. -/
  gasLimit : UInt64
  /-- The gas that the transactions of the block use. -/
  gasUsed : UInt64
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : UInt64
  -- `extraData`: `DATA` of 0 to 32 bytes.
  --
  -- The type leaves the bound out, and the readers and the payload form of a block check it.
  /-- Free bytes that the producer of the block chooses. -/
  extraData : ByteArray
  -- `baseFeePerGas`: `QUANTITY` of 256 bits, and `blockHash`: `DATA` of 32 bytes.
  /-- The base fee per gas. -/
  baseFeePerGas : U256
  /-- The hash of the header of the block. -/
  blockHash : Hash32
  -- `transactions`: each `TransactionType || TransactionPayload` or `LegacyTransaction`, EIP-2718.
  /-- The bytes of each transaction, in the order that they run. -/
  transactions : List ByteArray
  -- `ExecutionPayloadV2` appends `withdrawals`, an array of `WithdrawalV1`.
  --
  -- A `WithdrawalV1` has the four fields of a withdrawal of the execution layer.
  --
  -- Versions 2 and 3 append fields to the one before, so one type with fields by fork holds 1 to 3.
  /-- The withdrawals, from Shapella. -/
  withdrawals : Since .shapella fork (List Withdrawal)
  -- `ExecutionPayloadV3` appends `blobGasUsed` and `excessBlobGas`, `QUANTITY` of 64 bits.
  /-- The blob gas that the transactions use, from Dencun. -/
  blobGasUsed : Since .dencun fork UInt64
  /-- The blob gas above the target before the block, from Dencun. -/
  excessBlobGas : Since .dencun fork UInt64
  -- No field follows for `ExecutionPayloadV4`.
  --
  -- That version appends the block access list of EIP-7928 and the slot number of EIP-7843.
  --
  -- The header holds the hash of the list and the slot number, and the body holds neither.
  --
  -- So the type keeps these two fields apart, and the method passes them beside the payload.

/-- The eight-byte identifier of a payload build process. -/
abbrev PayloadId := Bytes8

/-- The three blocks that the consensus layer names to the execution layer. -/
structure ForkchoiceState where
  /-- The head of the canonical chain. -/
  headBlockHash : Hash32
  /-- The safe block, which must be the head or one of its ancestors.

  It may be all zero bytes until the transition block is finalized. -/
  safeBlockHash : Hash32
  /-- The most recent finalized block.

  It may be all zero bytes until the transition block is finalized. -/
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
  -- `PayloadStatusV1`: `status` is one of these five names.
  --
  -- From version 2 of `engine_newPayload`, `INVALID` supplants `INVALID_BLOCK_HASH`.
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
  /-- The method was asked to serve a fork, `fork`, that it does not support.

  It is the fork of the payload, of the block the attributes build, or of the stored build.

  For blobs, it is the fork the node is at.

  It is none when the configuration has no fork active at the block. -/
  | unsupportedFork (fork : Option Fork)
  /-- The safe or the finalized block is not on the chain of the head.

  `safe` and `finalized` are the two hashes of the forkchoice state. -/
  | invalidForkchoiceState (safe finalized : Hash32)
  /-- The request names `count` items, more than the `limit` the execution layer takes at once. -/
  | tooLargeRequest (count limit : Nat)
  /-- The payload attributes do not have a structure that the version of the method takes. -/
  | invalidPayloadAttributes
  /-- No build process has the requested payload ID, `id`. -/
  | unknownPayload (id : PayloadId)
  /-- The reorg to the head of the forkchoice state is deeper than the execution layer allows.

  The client software sets that limit, so no method of this library returns this error. -/
  | tooDeepReorg
  deriving DecidableEq

/-- The constructor and its fields, laid out as a derived form would lay them out.

Byte strings print in hex and forks by name.

Hex keeps a hash on one short line, where a list of 32 numbers would wrap. -/
instance : Repr EngineError where
  reprPrec e prec :=
    let hex (bytes : List UInt8) : Std.Format := Base.hexString bytes
    let apply (name : String) (args : List Std.Format) : Std.Format :=
      Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec ≥ max_prec then 1 else 2)
        (args.foldl (fun f arg => f ++ Std.Format.line ++ arg)
          (Std.Format.text ("EthLib.Engine.EngineError." ++ name))))) prec
    match e with
    | .invalidParams reason => apply "invalidParams" [reprArg reason]
    | .unsupportedFork fork => apply "unsupportedFork" [reprArg (fork.map Fork.name)]
    -- Two hashes do not fit the width of a line together, so they stay on one line unbroken.
    | .invalidForkchoiceState safe finalized =>
      Repr.addAppParen (Std.Format.text ("EthLib.Engine.EngineError.invalidForkchoiceState " ++
        Base.hexString safe.toList ++ " " ++ Base.hexString finalized.toList)) prec
    | .tooLargeRequest count limit => apply "tooLargeRequest" [reprArg count, reprArg limit]
    | .invalidPayloadAttributes => apply "invalidPayloadAttributes" []
    | .unknownPayload id => apply "unknownPayload" [hex id.toList]
    | .tooDeepReorg => apply "tooDeepReorg" []

/-- The code of an error: its JSON-RPC code is the negative of this number. -/
def EngineError.code : EngineError → UInt32
  -- The table of errors of the Engine API, `-32602` from JSON-RPC and `-38001` to `-38006`.
  | .invalidParams _ => 32602
  | .unsupportedFork _ => 38005
  | .invalidForkchoiceState .. => 38002
  | .tooLargeRequest .. => 38004
  | .invalidPayloadAttributes => 38003
  | .unknownPayload _ => 38001
  | .tooDeepReorg => 38006

/-- Why a payload is not valid, before its transactions run or when they run. -/
inductive PayloadError where
  /-- The transaction at an index, from 0, does not decode at the fork of the payload. -/
  | invalidTransaction (index : Nat) (error : TransactionError)
  /-- A root or the header of the block has no encoding, since a field is too long. -/
  | noEncoding
  /-- The block hash of the payload is not the hash of the header that it gives. -/
  | wrongBlockHash (expected computed : Hash32)
  /-- The expected versioned hashes are not those of the blob transactions, in order.

  `expected` are the hashes of the request, and `actual` those of the transactions. -/
  | wrongVersionedHashes (expected actual : List Hash32)
  /-- The block of the payload fails the state transition, with `error`. -/
  | invalidBlock (error : Execution.Blocks.BlockError)
  /-- The block access list is not the RLP encoding of a block access list. -/
  | invalidBlockAccessList
  /-- The parent, of hash `parent`, is a block of proof of work that is not terminal. -/
  | invalidTerminalBlock (parent : Hash32)
  deriving DecidableEq, Repr

/-- The stable code of a reason, one per constructor, for the C exports.

The codes start at 401, above the codes of the errors of a block.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PayloadError.code : PayloadError → UInt32
  -- Not in the source: the Engine API gives these reasons only as the message `validationError`.
  | .invalidTransaction .. => 401
  | .noEncoding => 402
  | .wrongBlockHash .. => 403
  | .wrongVersionedHashes .. => 404
  | .invalidBlock _ => 405
  | .invalidBlockAccessList => 406
  | .invalidTerminalBlock _ => 407

end EthLib.Engine
