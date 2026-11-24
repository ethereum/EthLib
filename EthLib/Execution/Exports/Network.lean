module

public import EthLib.Base.Exports
public import EthLib.Execution.Network.Bodies
public import EthLib.Execution.Network.Message
public import EthLib.Networking.Exports.ForkId

/-!
# `Exports.Network`

C-ABI exports for the messages of the eth capability, callable from the Python C extension.

A version crosses the boundary as its number, such as 69.

A message crosses it as its ID within the capability, and the RLP encoding of its data.

Cell errors have codes from 401.

A bad argument has code 0.
-/

public section

namespace EthLib.Execution.Network.Exports

open EthLib.Exports (ExportError Result UnreadArgument forkUpTo rejectArgument toResult)

/-- A message for a rejected message, phrased for someone reading a Python traceback. -/
def ethMessage : EthError → String
  | .unknownId id => s!"message ID {id} is not used by this eth version, or not read by EthLib yet"
  | .rlp _ => "message data is not RLP of the expected shape"
  | .unequalLengths t s h => s!"announcement has {t} types and {s} sizes for {h} hashes"

/-- A rejected message reaches Python with its code, and its message names the fault. -/
instance : ExportError EthError where
  -- Message errors have codes from 1.
  code := EthError.code
  message := ethMessage

/-- A message for a refused Status, phrased for someone reading a Python traceback. -/
def statusMessage : StatusError → String
  | .version v => s!"Status announces version {v}, not the negotiated one"
  | .forkId e => s!"fork identifier refused: {Networking.Devp2p.Exports.forkIdMessage e}"
  | .range e l => s!"block range starts at {e}, after its end {l}"

/-- A refused Status reaches Python with its code, and its message names the fault. -/
instance : ExportError StatusError where
  -- Status errors have codes from 101.
  code := StatusError.code
  message := statusMessage

/-- A message for a refused answer of headers, phrased for someone reading a Python traceback. -/
def headersMessage : HeadersError → String
  | .tooMany c l => s!"answer holds {c} headers, more than the limit {l}"
  | .rlp _ => "a header is not a list with a parent hash and a number"
  | .wrongStart => "first header is not the start block"
  | .wrongNumber e g => s!"header has number {g}, not {e}"
  | .notChained n => s!"header {n} does not chain to the header before it"
  | .notAnswer => "response is not BlockHeaders with the request ID of the request"

/-- A refused answer of headers reaches Python with its code, and its message names the fault. -/
instance : ExportError HeadersError where
  -- Header errors have codes from 201.
  code := HeadersError.code
  message := headersMessage

/-- A message for a refused answer of transactions, phrased for someone reading a traceback. -/
def poolMessage : PoolError → String
  | .notRequested => "transactions are not requested ones in the order of the request"
  | .notAnswer => "response is not PooledTransactions with the request ID of the request"

/-- A refused answer of transactions reaches Python with its code, and its message names it. -/
instance : ExportError PoolError where
  -- Transaction errors have codes from 302.
  code := PoolError.code
  message := poolMessage

/-- The version with a number, or code 0 when EthLib does not specify it. -/
def readVersion (number : UInt64) : Result EthVersion :=
  match EthVersion.ofNumber? number.toNat with
  | some v => pure v
  | none => rejectArgument none s!"eth/{number} is not a version that EthLib specifies"

/-- The canonical data of the message with the ID `id` and the data `data`, on a version.

It reads the message, and returns the data once the message reads.

The decoder takes only the canonical encoding of a message, so the data is that encoding. -/
@[export eth_message_decode]
def decodeExport (version id : UInt64) (data : ByteArray) : Result ByteArray := do
  let v ← readVersion version
  let _ ← toResult none (Message.decode v id.toNat data)
  return data

/-- Whether a node accepts the Status `data` of a peer, on a version, at a head.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_status]
def checkStatusExport (version : UInt64) (schedule : ByteArray) (number timestamp : UInt64)
    (data : ByteArray) : Result Bool := do
  let v ← readVersion version
  -- A schedule crosses the boundary as the fork identifier exports read it.
  let s ← Networking.Devp2p.Exports.readSchedule schedule
  match Message.decode v STATUS_ID data with
  | .error e => toResult none (.error e : Except EthError Bool)
  | .ok (.status status) =>
    toResult none ((checkStatus v s number.toNat timestamp.toNat status).map fun _ => true)
  | .ok _ => rejectArgument none "message is not Status"

/-- Whether the BlockHeaders data `response` answers the GetBlockHeaders data `request`.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_headers]
def checkHeadersExport (version : UInt64) (request response : ByteArray) : Result Bool := do
  let v ← readVersion version
  let req ← toResult none (Message.decode v GET_BLOCK_HEADERS_ID request)
  let resp ← toResult none (Message.decode v BLOCK_HEADERS_ID response)
  toResult none ((Message.checkHeaderResponse req resp).map fun _ => true)

/-- Whether the PooledTransactions data `response` answers GetPooledTransactions data `request`.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_pooled]
def checkPooledExport (version : UInt64) (request response : ByteArray) : Result Bool := do
  let v ← readVersion version
  let req ← toResult none (Message.decode v GET_POOLED_TRANSACTIONS_ID request)
  let resp ← toResult none (Message.decode v POOLED_TRANSACTIONS_ID response)
  toResult none ((Message.checkPooledResponse req resp).map fun _ => true)

/-- The hash of a transaction as it crosses the wire, from the bytes of its RLP item. -/
@[export eth_wire_hash]
def wireHashExport (tx : ByteArray) : Result ByteArray := do
  match Serialization.Rlp.decode tx with
  | .error _ => rejectArgument none "transaction is not one RLP item"
  | .ok item => return ⟨(wireHash ⟨item, tx⟩).toArray⟩

/-- Whether the receipts of a block, as a version sends them, match a receipts root.

The receipts are one RLP list, and the fork names the fork of the block.

The forks after Glamsterdam fail with code 0, since EthLib does not specify their blocks yet. -/
@[export eth_receipts_match]
def receiptsMatchExport (version : UInt64) (fork root receipts : ByteArray) : Result Bool := do
  let v ← readVersion version
  let fork ← forkUpTo .glamsterdam fork
  let some (root : Base.Hash32) := Base.exactBytes? 32 root
    | rejectArgument none "receipts root is not 32 bytes"
  match Serialization.Rlp.decode receipts with
  | .ok (.list items) => return receiptsMatch v fork root items
  | _ => rejectArgument none "receipts are not one RLP list"

/-- Whether `response` answers a GetBlockAccessLists `request`, given each block's access list hash.

The response is BlockAccessLists data, and both messages exist from eth/71 on. -/
@[export eth_access_lists_answer]
def accessListsAnswerExport (version : UInt64) (request response : ByteArray)
    (expected : Array ByteArray) : Result Bool := do
  let v ← readVersion version
  let req ← toResult none (Message.decode v GET_BLOCK_ACCESS_LISTS_ID request)
  let resp ← toResult none (Message.decode v BLOCK_ACCESS_LISTS_ID response)
  let hashes ← expected.toList.mapM fun b =>
    toResult none (Base.exactBytes 32 b fun _ =>
      UnreadArgument.mk "an access list hash is not 32 bytes")
  return Message.accessListsResponse hashes req resp

/-- A message for a refused partial list, phrased for someone reading a Python traceback. -/
def partialMessage : PartialReceiptsError → String
  | .tooMany d t => s!"{d} receipts delivered for {t} transactions"
  | .receiptTooLarge i s b => s!"receipt {i} has {s} bytes, more than {b}"
  | .totalTooLarge s b => s!"receipts have {s} bytes, more than {b}"

/-- A refused partial list reaches Python with its code, and its message names the fault. -/
instance : ExportError PartialReceiptsError where
  -- Partial receipts errors have codes from 501.
  code := PartialReceiptsError.code
  message := partialMessage

/-- Whether the receipts delivered so far of one block pass the checks of EIP-7975.

The receipts are one RLP list, each receipt counting the bytes of its RLP encoding.

The gas limits of the transactions are one RLP list of scalars. -/
@[export eth_check_partial_receipts]
def checkPartialReceiptsExport (gasLimits : ByteArray) (blockGasLimit : UInt64)
    (receipts : ByteArray) : Result Bool := do
  let .ok (limits : List Nat) := Serialization.Rlp.Codec.decode gasLimits
    | rejectArgument none "gas limits are not an RLP list of scalars"
  let .ok sizes := receiptSizes receipts
    | rejectArgument none "receipts are not one RLP list"
  toResult none ((checkPartialReceipts limits blockGasLimit.toNat sizes).map fun _ => true)

/-- A hash in hex, as a message writes it. -/
def hex (hash : Base.Hash32) : String :=
  Base.hexString hash.toList

/-- A message for a refused body, phrased for someone reading a Python traceback. -/
def bodyMessage : BodyError → String
  | .decoding e => s!"body is not the RLP list of its parts: {reprStr e}"
  | .trie e => s!"a root of the body cannot be computed: {reprStr e}"
  | .wrongTransactionsRoot expected actual =>
    s!"transactions have the root {hex actual}, not the transactions root {hex expected}"
  | .missingWithdrawals => "body has no withdrawals, which the fork asks for"
  | .unexpectedWithdrawals => "body has withdrawals, which the fork does not have"
  | .wrongWithdrawalsRoot expected actual =>
    s!"withdrawals have the root {hex actual}, not the withdrawals root {hex expected}"
  | .tooManyOmmers c => s!"body holds {c} ommers, more than {Blocks.MAX_OMMERS}"
  | .wrongOmmersHash expected actual =>
    s!"ommers have the hash {hex actual}, not the ommers hash {hex expected}"
  | .ommerAfterBlock i n => s!"ommer {i} has number {n}, after the block"
  | .untypedTransaction none => "a transaction is an empty byte string"
  | .untypedTransaction (some first) =>
    s!"a transaction is a byte string that starts with {Base.hexString [first]}, not a type"
  | .invalidTransaction i e => s!"transaction {i} is not a transaction of the fork: {reprStr e}"
  | .gasLimitAboveBlock i gas limit =>
    s!"transaction {i} has gas limit {gas}, above the gas limit {limit} of the block"

/-- A refused body reaches Python with its code, and its message names the fault. -/
instance : ExportError BodyError where
  -- Body errors have codes from 601.
  code := BodyError.code
  message := bodyMessage

/-- Whether the body `body` of a BlockBodies answer belongs to the header `header` at a fork.

The header and the body are RLP.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_body]
def checkBodyExport (fork header body : ByteArray) : Result Bool := do
  let fork ← forkUpTo .glamsterdam fork
  let h : Blocks.Header fork ← toResult none ((Serialization.Rlp.Codec.decode header).mapError
    fun e => UnreadArgument.mk s!"header does not decode at this fork: {reprStr e}")
  let .ok item := Serialization.Rlp.decode body
    | rejectArgument none "body is not RLP"
  toResult none ((checkBody h ⟨item, body⟩).map fun _ => true)

end EthLib.Execution.Network.Exports
