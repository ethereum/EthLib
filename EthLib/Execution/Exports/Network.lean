module

public import EthLib.Base.Exports
public import EthLib.Execution.Network.Message
public import EthLib.Networking.Exports.ForkId

/-!
# `Exports.Network`

C-ABI exports for the messages of the eth capability, callable from the Python C extension.

A version crosses the boundary as its number, such as 69.

A message crosses it as its ID within the capability, and the RLP encoding of its data.

A schedule crosses it as the fork identifier exports read it.

Message errors have codes from 1, Status errors from 101, header errors from 201, transaction
errors from 301, and a bad argument code 0.
-/

public section

namespace EthLib.Execution.Network.Exports

open EthLib.Exports (Result forkUpTo)

/-- A message for a rejected message, phrased for someone reading a Python traceback. -/
def ethMessage : EthError → String
  | .unknownId id => s!"message ID {id} is not used by this eth version, or not read by EthLib yet"
  | .rlp _ => "message data is not RLP of the expected shape"
  | .unequalLengths t s h => s!"announcement has {t} types and {s} sizes for {h} hashes"

/-- A message for a refused Status, phrased for someone reading a Python traceback. -/
def statusMessage : StatusError → String
  | .version v => s!"Status announces version {v}, not the negotiated one"
  | .forkId e => s!"fork identifier refused: {Networking.Devp2p.Exports.forkIdMessage e}"
  | .range e l => s!"block range starts at {e}, after its end {l}"

/-- A message for a refused answer of headers, phrased for someone reading a Python traceback. -/
def headersMessage : HeadersError → String
  | .tooMany c l => s!"answer holds {c} headers, more than the limit {l}"
  | .rlp _ => "a header is not a list with a parent hash and a number"
  | .wrongStart => "first header is not the start block"
  | .wrongNumber e g => s!"header has number {g}, not {e}"
  | .notChained n => s!"header {n} does not chain to the header before it"
  | .notAnswer => "response is not BlockHeaders with the request ID of the request"

/-- A message for a refused answer of transactions, phrased for someone reading a traceback. -/
def poolMessage : PoolError → String
  | .rlp _ => "a transaction has no RLP encoding"
  | .notRequested => "transactions are not requested ones in the order of the request"
  | .notAnswer => "response is not PooledTransactions with the request ID of the request"

/-- The version with a number, or code 0 when EthLib does not specify it. -/
def readVersion (number : UInt64) : Result EthVersion :=
  match EthVersion.ofNumber? number.toNat with
  | some v => pure v
  | none => throw (0, s!"eth/{number} is not a version that EthLib specifies")

/-- The canonical data of the message with the ID `id` and the data `data`, on a version.

It reads the message, then writes it back. -/
@[export eth_message_decode]
def decodeExport (version id : UInt64) (data : ByteArray) : Result ByteArray := do
  let v ← readVersion version
  let run {α : Type} (act : Except EthError α) : Result α :=
    act.mapError fun e => (e.code, ethMessage e)
  run (← run (Message.decode v id.toNat data)).encode

/-- Whether a node accepts the Status `data` of a peer, on a version, at a head.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_status]
def checkStatusExport (version : UInt64) (schedule : ByteArray) (number timestamp : UInt64)
    (data : ByteArray) : Result Bool := do
  let v ← readVersion version
  let s ← Networking.Devp2p.Exports.readSchedule schedule
  match Message.decode v STATUS_ID data with
  | .error e => throw (e.code, ethMessage e)
  | .ok (.status status) =>
    (checkStatus v s number.toNat timestamp.toNat status).map (fun _ => true)
      |>.mapError fun e => (e.code, statusMessage e)
  | .ok _ => throw (0, "message is not Status")

/-- Whether the BlockHeaders data `response` answers the GetBlockHeaders data `request`.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_headers]
def checkHeadersExport (version : UInt64) (request response : ByteArray) : Result Bool := do
  let v ← readVersion version
  let run {α : Type} (act : Except EthError α) : Result α :=
    act.mapError fun e => (e.code, ethMessage e)
  let req ← run (Message.decode v GET_BLOCK_HEADERS_ID request)
  let resp ← run (Message.decode v BLOCK_HEADERS_ID response)
  (Message.checkHeaderResponse req resp).map (fun _ => true)
    |>.mapError fun e => (e.code, headersMessage e)

/-- Whether the PooledTransactions data `response` answers the GetPooledTransactions data
`request`.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_pooled]
def checkPooledExport (version : UInt64) (request response : ByteArray) : Result Bool := do
  let v ← readVersion version
  let run {α : Type} (act : Except EthError α) : Result α :=
    act.mapError fun e => (e.code, ethMessage e)
  let req ← run (Message.decode v GET_POOLED_TRANSACTIONS_ID request)
  let resp ← run (Message.decode v POOLED_TRANSACTIONS_ID response)
  (Message.checkPooledResponse req resp).map (fun _ => true)
    |>.mapError fun e => (e.code, poolMessage e)

/-- The hash of a transaction as it crosses the wire, from its RLP item. -/
@[export eth_wire_hash]
def wireHashExport (tx : ByteArray) : Result ByteArray := do
  match Serialization.Rlp.decode tx with
  | .error _ => throw (0, "transaction is not one RLP item")
  | .ok item =>
    match wireHash item with
    | .error _ => throw (0, "transaction has no RLP encoding")
    | .ok h => return ⟨h.toArray⟩

/-- Whether the receipts of a block, as a version sends them, match a receipts root.

The receipts are one RLP list, and the fork names the fork of the block.

The forks after Glamsterdam fail with code 0, since EthLib does not specify their blocks yet. -/
@[export eth_receipts_match]
def receiptsMatchExport (version : UInt64) (fork root receipts : ByteArray) : Result Bool := do
  let v ← readVersion version
  let fork ← forkUpTo .glamsterdam fork
  let some (root : Base.Hash32) := (if h : root.size = 32 then some ⟨root.data, h⟩ else none)
    | throw (0, "receipts root is not 32 bytes")
  match Serialization.Rlp.decode receipts with
  | .ok (.list items) => return receiptsMatch v fork root items
  | _ => throw (0, "receipts are not one RLP list")

end EthLib.Execution.Network.Exports
