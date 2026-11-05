module

public import EthLib.Execution.Network.Blocks
public import EthLib.Execution.Network.Cells
public import EthLib.Execution.Network.Receipts
public import EthLib.Execution.Network.Snap
public import EthLib.Execution.Network.Status
public import EthLib.Execution.Network.Transactions

/-!
# `Execution.Network.Message`

The messages of the eth capability, read by their message ID and the negotiated version.

A message on the wire is its message ID, then the RLP list of its data, as in
"Message Encoding" of [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#message-encoding

Here the ID is relative to the capability: Status is 0x00 whatever offset RLPx gives eth.

A message whose ID the version does not use is rejected.

So is a message that EthLib does not read yet.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The message ID of GetBlockAccessLists, from eth/71 on. -/
def GET_BLOCK_ACCESS_LISTS_ID : Nat := 0x12

/-- The message ID of BlockAccessLists, from eth/71 on. -/
def BLOCK_ACCESS_LISTS_ID : Nat := 0x13

/-- A message of the eth capability. -/
inductive Message where
  /-- Status (0x00), the handshake. -/
  | status (s : Status)
  /-- NewBlockHashes (0x01): `[[blockhash, number], ...]`. -/
  | newBlockHashes (blocks : List BlockAnnouncement)
  /-- Transactions (0x02): `[tx, ...]`. -/
  | transactions (txs : List Item)
  /-- GetBlockHeaders (0x03): `[request-id, [startblock, limit, skip, reverse]]`. -/
  | getBlockHeaders (requestId : UInt64) (request : HeaderRequest)
  /-- BlockHeaders (0x04): `[request-id, [header, ...]]`. -/
  | blockHeaders (requestId : UInt64) (headers : List Item)
  /-- GetBlockBodies (0x05): `[request-id, [blockhash, ...]]`. -/
  | getBlockBodies (requestId : UInt64) (hashes : List Hash32)
  /-- BlockBodies (0x06): `[request-id, [block-body, ...]]`. -/
  | blockBodies (requestId : UInt64) (bodies : List Item)
  /-- NewBlock (0x07): `[block, td]`, with the total difficulty of the block. -/
  | newBlock (block : Item) (totalDifficulty : Nat)
  /-- NewPooledTransactionHashes (0x08): the types, sizes and hashes of new transactions. -/
  | newPooledTransactionHashes (a : Announcement)
  /-- GetPooledTransactions (0x09): `[request-id, [txhash, ...]]`. -/
  | getPooledTransactions (requestId : UInt64) (hashes : List Hash32)
  /-- PooledTransactions (0x0a): `[request-id, [tx, ...]]`. -/
  | pooledTransactions (requestId : UInt64) (txs : List Item)
  /-- GetReceipts (0x0f): `[request-id, [blockhash, ...]]`.

  From eth/70 on, `firstBlockReceiptIndex` comes after the request ID. -/
  | getReceipts (requestId : UInt64) (firstIndex : Option Nat) (hashes : List Hash32)
  /-- Receipts (0x10): `[request-id, [[receipt, ...], ...]]`, one list for each block.

  From eth/70 on, `lastBlockIncomplete` comes after the request ID. -/
  | receipts (requestId : UInt64) (lastIncomplete : Option Bool) (lists : List (List Item))
  /-- BlockRangeUpdate (0x11), from eth/69 on. -/
  | blockRangeUpdate (r : BlockRange)
  /-- GetBlockAccessLists (0x12) of eth/71: `[request-id, [blockhash, ...]]`. -/
  | getBlockAccessLists (requestId : UInt64) (hashes : List Hash32)
  /-- BlockAccessLists (0x13) of eth/71: `[request-id, [bal, ...]]`.

  Each access list is its RLP item, or the empty string when the peer does not have it. -/
  | blockAccessLists (requestId : UInt64) (lists : List Item)
  /-- GetCells (0x14) of eth/72: `[request-id, [txhash, ...], cells]`. -/
  | getCells (requestId : UInt64) (hashes : List Hash32) (mask : CellMask)
  /-- Cells (0x15) of eth/72: `[request-id, [txhash, ...], [[cell, ...], ...], cells]`. -/
  | cells (requestId : UInt64) (hashes : List Hash32) (groups : List (List ByteArray))
      (mask : CellMask)
  deriving DecidableEq

/-- Every way a message can be rejected. -/
inductive EthError where
  /-- The version does not use the message ID, or EthLib does not read that message yet. -/
  | unknownId (id : Nat)
  /-- The data is not RLP of the shape that the message asks for. -/
  | rlp (error : RlpError)
  /-- An announcement has not as many types and sizes as hashes. -/
  | unequalLengths (types sizes hashes : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EthError.code : EthError → UInt32
  | .unknownId _ => 1
  | .rlp _ => 2
  | .unequalLengths .. => 3

namespace Message

/-- The message ID. -/
def id : Message → Nat
  | status _ => STATUS_ID
  | newBlockHashes _ => NEW_BLOCK_HASHES_ID
  | transactions _ => TRANSACTIONS_ID
  | getBlockHeaders .. => GET_BLOCK_HEADERS_ID
  | blockHeaders .. => BLOCK_HEADERS_ID
  | getBlockBodies .. => GET_BLOCK_BODIES_ID
  | blockBodies .. => BLOCK_BODIES_ID
  | newBlock .. => NEW_BLOCK_ID
  | newPooledTransactionHashes _ => NEW_POOLED_TRANSACTION_HASHES_ID
  | getPooledTransactions .. => GET_POOLED_TRANSACTIONS_ID
  | pooledTransactions .. => POOLED_TRANSACTIONS_ID
  | getReceipts .. => GET_RECEIPTS_ID
  | receipts .. => RECEIPTS_ID
  | blockRangeUpdate _ => BLOCK_RANGE_UPDATE_ID
  | getBlockAccessLists .. => GET_BLOCK_ACCESS_LISTS_ID
  | blockAccessLists .. => BLOCK_ACCESS_LISTS_ID
  | getCells .. => GET_CELLS_ID
  | cells .. => CELLS_ID

/-- The envelope of a request or a response: `[request-id, payload]`, from EIP-2481. -/
def envelope (requestId : UInt64) (payload : Item) : Item :=
  .list [Codec.toItem requestId, payload]

/-- The envelope of eth/70, `[request-id, part, payload]`, or `[request-id, payload]` without a
part. -/
def withPart {α : Type} [Codec α] (requestId : UInt64) (part : Option α) (payload : Item) :
    Item :=
  match part with
  | none => envelope requestId payload
  | some p => .list [Codec.toItem requestId, Codec.toItem p, payload]

/-- The data of the message, as one RLP item. -/
def toItem : Message → Item
  | status s => s.toItem
  | newBlockHashes bs => Codec.toItem bs
  | transactions txs => .list txs
  | getBlockHeaders i r => envelope i (Codec.toItem r)
  | blockHeaders i hs => envelope i (.list hs)
  | getBlockBodies i hs => envelope i (Codec.toItem hs)
  | blockBodies i bs => envelope i (.list bs)
  | newBlock b td => .list [b, Codec.toItem td]
  | newPooledTransactionHashes a => a.toItem
  | getPooledTransactions i hs => envelope i (Codec.toItem hs)
  | pooledTransactions i txs => envelope i (.list txs)
  | getReceipts i k hs => withPart i k (Codec.toItem hs)
  | receipts i b ls => withPart i b (.list (ls.map .list))
  | blockRangeUpdate r => Codec.toItem r
  | getBlockAccessLists i hs => envelope i (Codec.toItem hs)
  | blockAccessLists i ls => envelope i (.list ls)
  | getCells i hs m => .list [Codec.toItem i, Codec.toItem hs, Codec.toItem m]
  | cells i hs gs m => .list [Codec.toItem i, Codec.toItem hs, Codec.toItem gs, Codec.toItem m]

/-- The request ID and the payload in the envelope `[request-id, payload]`. -/
def readEnvelope {α : Type} [Codec α] (item : Item) : Except RlpError (UInt64 × α) := do
  match ← item.fields 2 with
  | [i, p] => return (← i.field 0, ← p.field 1)
  | items => throw (.wrongFieldCount 2 items.length)

/-- The request ID, the part and the payload of `[request-id, part, payload]` from eth/70 on, or
of `[request-id, payload]` before. -/
def readWithPart {α β : Type} [Codec α] [Codec β] (version : EthVersion) (item : Item) :
    Except RlpError (UInt64 × Option α × β) := do
  if version < .eth70 then
    let (i, p) ← readEnvelope (α := β) item
    return (i, none, p)
  else
    match ← item.fields 3 with
    | [i, k, p] => return (← i.field 0, some (← k.field 1), ← p.field 2)
    | items => throw (.wrongFieldCount 3 items.length)

/-- The request ID of a request or a response, and none for the other messages. -/
def requestId? : Message → Option UInt64
  | getBlockHeaders i _ | blockHeaders i _ | getBlockBodies i _ | blockBodies i _
  | getPooledTransactions i _ | pooledTransactions i _ | getReceipts i _ _ | receipts i _ _
  | getBlockAccessLists i _ | blockAccessLists i _ | getCells i _ _ | cells i _ _ _ => some i
  | _ => none

/-- Whether `response` answers `request`: it is the response type of the request type, and it
repeats the request ID. -/
def answers (request response : Message) : Bool :=
  match request, response with
  | getBlockHeaders i _, blockHeaders j _ => i == j
  | getBlockBodies i _, blockBodies j _ => i == j
  | getPooledTransactions i _, pooledTransactions j _ => i == j
  | getReceipts i _ _, receipts j _ _ => i == j
  | getBlockAccessLists i _, blockAccessLists j _ => i == j
  | getCells i _ _, cells j _ _ _ => i == j
  | _, _ => false

/-- The message with the ID `id` and the data `item`, on the version `version`.

BlockRangeUpdate exists from eth/69 on. -/
def ofItem (version : EthVersion) (id : Nat) (item : Item) : Except EthError Message :=
  if id = STATUS_ID then (status <$> Status.ofItem version item).mapError .rlp
  else if id = NEW_BLOCK_HASHES_ID then (newBlockHashes <$> Codec.ofItem item).mapError .rlp
  else if id = TRANSACTIONS_ID then (transactions <$> Codec.ofItem item).mapError .rlp
  else if id = GET_BLOCK_HEADERS_ID then
    ((fun (i, r) => getBlockHeaders i r) <$> readEnvelope item).mapError .rlp
  else if id = BLOCK_HEADERS_ID then
    ((fun (i, hs) => blockHeaders i hs) <$> readEnvelope item).mapError .rlp
  else if id = GET_BLOCK_BODIES_ID then
    ((fun (i, hs) => getBlockBodies i hs) <$> readEnvelope item).mapError .rlp
  else if id = BLOCK_BODIES_ID then
    ((fun (i, bs) => blockBodies i bs) <$> readEnvelope item).mapError .rlp
  else if id = NEW_BLOCK_ID then Except.mapError .rlp do
    match ← item.fields 2 with
    | [b, td] => return newBlock b (← td.field 1)
    | items => throw (.wrongFieldCount 2 items.length)
  else if id = NEW_POOLED_TRANSACTION_HASHES_ID then do
    let a ← (Announcement.ofItem version item).mapError .rlp
    let (t, s, h) := a.lists
    if a.lengthsAgree then return newPooledTransactionHashes a
    else throw (.unequalLengths t.size s.length h.length)
  else if id = GET_POOLED_TRANSACTIONS_ID then
    ((fun (i, hs) => getPooledTransactions i hs) <$> readEnvelope item).mapError .rlp
  else if id = POOLED_TRANSACTIONS_ID then
    ((fun (i, txs) => pooledTransactions i txs) <$> readEnvelope item).mapError .rlp
  else if id = GET_RECEIPTS_ID then
    ((fun (i, k, hs) => getReceipts i k hs) <$> readWithPart version item).mapError .rlp
  else if id = RECEIPTS_ID then
    ((fun (i, b, ls) => receipts i b ls) <$> readWithPart version item).mapError .rlp
  else if id = GET_BLOCK_ACCESS_LISTS_ID ∧ EthVersion.eth71 ≤ version then
    ((fun (i, hs) => getBlockAccessLists i hs) <$> readEnvelope item).mapError .rlp
  else if id = BLOCK_ACCESS_LISTS_ID ∧ EthVersion.eth71 ≤ version then
    ((fun (i, ls) => blockAccessLists i ls) <$> readEnvelope item).mapError .rlp
  else if id = GET_CELLS_ID ∧ EthVersion.eth72 ≤ version then Except.mapError .rlp do
    match ← item.fields 3 with
    | [i, hs, m] => return getCells (← i.field 0) (← hs.field 1) (← m.field 2)
    | items => throw (.wrongFieldCount 3 items.length)
  else if id = CELLS_ID ∧ EthVersion.eth72 ≤ version then Except.mapError .rlp do
    match ← item.fields 4 with
    | [i, hs, gs, m] => return cells (← i.field 0) (← hs.field 1) (← gs.field 2) (← m.field 3)
    | items => throw (.wrongFieldCount 4 items.length)
  else if id = BLOCK_RANGE_UPDATE_ID ∧ EthVersion.eth69 ≤ version then
    (blockRangeUpdate <$> Codec.ofItem item).mapError .rlp
  else .error (.unknownId id)

/-- The message with the ID `id` whose data is the RLP encoding `data`. -/
def decode (version : EthVersion) (id : Nat) (data : ByteArray) : Except EthError Message := do
  ofItem version id (← (Serialization.Rlp.decode data).mapError .rlp)

/-- The RLP encoding of the data of a message. -/
def encode (m : Message) : Except EthError ByteArray :=
  (Serialization.Rlp.encode m.toItem).mapError .rlp

/-- Whether `response` is BlockHeaders that answers the GetBlockHeaders `request`.

It must repeat the request ID, and its headers must pass the check of the request. -/
def checkHeaderResponse (request response : Message) : Except HeadersError Unit :=
  match request, response with
  | getBlockHeaders i r, blockHeaders j hs => if i = j then checkHeaders r hs else throw .notAnswer
  | _, _ => throw .notAnswer

/-- Whether `response` is PooledTransactions that answers the GetPooledTransactions `request`.

It must repeat the request ID, and its transactions must be requested ones, in order. -/
def checkPooledResponse (request response : Message) : Except PoolError Unit :=
  match request, response with
  | getPooledTransactions i hs, pooledTransactions j txs =>
    if i = j then checkPooled hs txs else throw .notAnswer
  | _, _ => throw .notAnswer

/-- Whether `response` is Cells that answers the GetCells `request`.

It must repeat the request ID and pass the checks of the cells, with `blobs` the number of blobs
of each transaction of the response. -/
def checkCellsResponse (blobs : List Nat) (request response : Message) :
    Except CellsError Unit :=
  match request, response with
  | getCells i requested requestMask, cells j hashes groups mask =>
    if i = j then checkCells requested requestMask blobs hashes groups mask else throw .notAnswer
  | _, _ => throw .notAnswer

/-- Whether `response` is BlockAccessLists that answers the GetBlockAccessLists `request`.

`expected` holds the access list hash of the header of each requested block.

`eth.md` gives each element of the response one requested block, so the response has exactly
one entry per request, unlike snap/2, which lets the peer cut the tail. -/
def accessListsResponse (expected : List Hash32) (request response : Message) : Bool :=
  match request, response with
  | getBlockAccessLists i _, blockAccessLists j lists =>
    i == j && lists.length == expected.length && accessListsAnswer expected lists
  | _, _ => false

end Message

end EthLib.Execution.Network
