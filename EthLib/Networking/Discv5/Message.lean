module

public import EthLib.Serialization.Rlp.Codec

/-!
# `Networking.Discv5.Message`

The messages of discv5, from the section Protocol Messages of `discv5-wire.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv5/discv5-wire.md>

A message is its type byte, then the RLP list of its fields.

The first field of every message is the request ID, a byte string of at most 8 bytes.

A node record in a message stays an RLP item, for the ENR decoder to read.

The text gives `total` and `wait-time` no width; its WHOAREYOU packet types `enr-seq` as `uint64`.

EthLib reads `total` and `wait-time` as 64-bit integers, so a larger value is refused.

No count of responses or wait in milliseconds comes near `2^64`.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Serialization.Rlp

/-- The largest request ID, in bytes. -/
def MAX_REQUEST_ID_SIZE : Nat := 8

/-- The largest logarithmic distance between two node IDs. -/
def MAX_DISTANCE : Nat := 256

/-- A message of discv5, one constructor for each message type. -/
inductive Message where
  /-- Type 1: whether the recipient is alive, with the ENR sequence number of the sender. -/
  | ping (requestId : ByteArray) (enrSeq : UInt64)
  /-- Type 2: the reply to PING, with the address and UDP port of the recipient as seen. -/
  | pong (requestId : ByteArray) (enrSeq : UInt64) (recipientIp : ByteArray)
      (recipientPort : UInt16)
  /-- Type 3: the nodes at some logarithmic distances from the recipient. -/
  | findnode (requestId : ByteArray) (distances : List Nat)
  /-- Type 4: node records, with the total number of responses to the request. -/
  | nodes (requestId : ByteArray) (total : UInt64) (records : List Item)
  /-- Type 5: an application request, for the protocol that the protocol name selects. -/
  | talkreq (requestId : ByteArray) (protocol request : ByteArray)
  /-- Type 6: the reply to TALKREQ. -/
  | talkresp (requestId : ByteArray) (response : ByteArray)
  /-- Type 7: a request to register the sender for a topic, with its record and its ticket. -/
  | regtopic (requestId : ByteArray) (topic : Vector UInt8 32) (record : Item)
      (ticket : ByteArray) (distances : List Nat)
  /-- Type 8: the reply to REGTOPIC, with a ticket and a waiting time in milliseconds. -/
  | regconfirmation (requestId : ByteArray) (total : UInt64) (ticket : ByteArray)
      (waitTime : UInt64)
  /-- Type 9: a request for the registered advertisers of a topic. -/
  | topicquery (requestId : ByteArray) (topic : Vector UInt8 32) (distances : List Nat)
  /-- Type 10: advertiser records for a topic, with the total number of responses. -/
  | topicnodes (requestId : ByteArray) (total : UInt64) (records : List Item)
  deriving DecidableEq

/-- Every way a message can be rejected. -/
inductive MessageError where
  /-- The plaintext is empty, so it has no message type. -/
  | empty
  /-- The message type is not one of 1 to 10. -/
  | unknownType (type : UInt8)
  /-- The bytes after the type are not one RLP list, or a field has the wrong form. -/
  | rlp (e : RlpError)
  /-- The message of type `type` has `count` fields, more or fewer than its type. -/
  | fields (type : UInt8) (count : Nat)
  /-- A request ID, an address or a distance of a message of type `type` is out of its range. -/
  | invalid (type : UInt8)
  deriving DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 101, since the packet errors share their Python class and use 1 to 7.

A new constructor takes a new code, so that each code keeps its meaning. -/
def MessageError.code : MessageError → UInt32
  | .empty => 101
  | .unknownType _ => 102
  | .rlp _ => 103
  | .fields .. => 104
  | .invalid _ => 105

/-- A port, a scalar below 2^16. -/
def portItem (port : UInt16) : Item := .scalar port.toNat

/-- The port that a scalar below 2^16 writes. -/
def portOfItem (item : Item) : Except RlpError UInt16 := do
  return UInt16.ofNat (← item.toScalarBelow 16)

namespace Message

/-- The message type byte. -/
def type : Message → UInt8
  | .ping .. => 1
  | .pong .. => 2
  | .findnode .. => 3
  | .nodes .. => 4
  | .talkreq .. => 5
  | .talkresp .. => 6
  | .regtopic .. => 7
  | .regconfirmation .. => 8
  | .topicquery .. => 9
  | .topicnodes .. => 10

/-- The fields of a message, in order. -/
def fields : Message → List Item
  -- PING (0x01): `message-data = [request-id, enr-seq]`.
  | .ping id seq => [Codec.toItem id, Codec.toItem seq]
  -- PONG (0x02): `message-data = [request-id, enr-seq, recipient-ip, recipient-port]`.
  | .pong id seq ip port => [Codec.toItem id, Codec.toItem seq, Codec.toItem ip, portItem port]
  -- FINDNODE (0x03): `message-data = [request-id, [distance₁, distance₂, ..., distanceₙ]]`.
  | .findnode id ds => [Codec.toItem id, Codec.toItem ds]
  -- NODES (0x04): `message-data = [request-id, total, [ENR, ...]]`.
  | .nodes id total rs => [Codec.toItem id, Codec.toItem total, Codec.toItem rs]
  -- TALKREQ (0x05): `message-data = [request-id, protocol, request]`.
  | .talkreq id p r => [Codec.toItem id, Codec.toItem p, Codec.toItem r]
  -- TALKRESP (0x06): `message-data = [request-id, response]`.
  | .talkresp id r => [Codec.toItem id, Codec.toItem r]
  -- REGTOPIC (0x07): `[request-id, topic, ENR, ticket, [topic-distance₁, ..., topic-distanceₙ]]`.
  | .regtopic id t rec ticket ds =>
    [Codec.toItem id, Codec.toItem t, rec, Codec.toItem ticket, Codec.toItem ds]
  -- REGCONFIRMATION (0x08): `message-data = [request-id, total, ticket, wait-time]`.
  | .regconfirmation id total ticket wait =>
    [Codec.toItem id, Codec.toItem total, Codec.toItem ticket, Codec.toItem wait]
  -- TOPICQUERY (0x09): `[request-id, topic, [topic-distance₁, ..., topic-distanceₙ]]`.
  | .topicquery id t ds => [Codec.toItem id, Codec.toItem t, Codec.toItem ds]
  -- TOPICNODES (0x0a): `message-data = [request-id, total, [ENR, ...]]`.
  | .topicnodes id total rs => [Codec.toItem id, Codec.toItem total, Codec.toItem rs]

/-- The message of a type, from its fields, without the checks on sizes and distances. -/
def ofFields (type : UInt8) (items : List Item) : Except RlpError (Option Message) :=
  -- Each type reads the fields of its `message-data`, in the order of the source.
  --
  -- A field count other than that of the type gives none.
  match type.toNat, items with
  -- PING (0x01): `[request-id, enr-seq]`.
  | 1, [id, seq] => do return some (.ping (← Codec.ofItem id) (← Codec.ofItem seq))
  -- PONG (0x02): `[request-id, enr-seq, recipient-ip, recipient-port]`, the port a 16-bit integer.
  | 2, [id, seq, ip, port] => do
    return some (.pong (← Codec.ofItem id) (← Codec.ofItem seq) (← Codec.ofItem ip)
      (← portOfItem port))
  -- FINDNODE (0x03): `[request-id, [distance₁, ..., distanceₙ]]`.
  | 3, [id, ds] => do return some (.findnode (← Codec.ofItem id) (← Codec.ofItem ds))
  -- NODES (0x04): `[request-id, total, [ENR, ...]]`, each ENR kept as an RLP item.
  | 4, [id, total, rs] => do
    return some (.nodes (← Codec.ofItem id) (← Codec.ofItem total) (← Codec.ofItem rs))
  -- TALKREQ (0x05): `[request-id, protocol, request]`, both RLP byte arrays.
  | 5, [id, p, r] => do
    return some (.talkreq (← Codec.ofItem id) (← Codec.ofItem p) (← Codec.ofItem r))
  -- TALKRESP (0x06): `[request-id, response]`, an RLP byte array.
  | 6, [id, r] => do return some (.talkresp (← Codec.ofItem id) (← Codec.ofItem r))
  -- REGTOPIC (0x07): `[request-id, topic, ENR, ticket, [topic-distance₁, ...]]`.
  --
  -- The topic has 32 bytes, and the ENR stays an RLP item.
  | 7, [id, t, rec, ticket, ds] => do
    return some (.regtopic (← Codec.ofItem id) (← Codec.ofItem t) rec (← Codec.ofItem ticket)
      (← Codec.ofItem ds))
  -- REGCONFIRMATION (0x08): `[request-id, total, ticket, wait-time]`.
  | 8, [id, total, ticket, wait] => do
    return some (.regconfirmation (← Codec.ofItem id) (← Codec.ofItem total)
      (← Codec.ofItem ticket) (← Codec.ofItem wait))
  -- TOPICQUERY (0x09): `[request-id, topic, [topic-distance₁, ...]]`, the topic of 32 bytes.
  | 9, [id, t, ds] => do
    return some (.topicquery (← Codec.ofItem id) (← Codec.ofItem t) (← Codec.ofItem ds))
  -- TOPICNODES (0x0a): `[request-id, total, [ENR, ...]]`.
  | 10, [id, total, rs] => do
    return some (.topicnodes (← Codec.ofItem id) (← Codec.ofItem total) (← Codec.ofItem rs))
  | _, _ => return none

/-- The request ID of a message. -/
def requestId : Message → ByteArray
  | .ping id .. | .pong id .. | .findnode id .. | .nodes id .. | .talkreq id ..
  | .talkresp id .. | .regtopic id .. | .regconfirmation id .. | .topicquery id ..
  | .topicnodes id .. => id

/-- Whether the sizes and distances of a message are those that the wire format allows. -/
def valid (m : Message) : Bool :=
  -- `request-id` is an RLP byte array of length `≤ 8` bytes.
  m.requestId.size ≤ MAX_REQUEST_ID_SIZE &&
    match m with
    -- PONG: `recipient-ip` is a 16 or 4 byte IP address.
    | .pong _ _ ip _ => ip.size == 4 || ip.size == 16
    -- FINDNODE: each distance is at most 256, the largest log2 distance of 256-bit node IDs.
    --
    -- The grammar says positive, but the text says what distance 0 returns, so 0 is allowed.
    | .findnode _ ds => ds.all (· ≤ MAX_DISTANCE)
    -- REGTOPIC and TOPICQUERY: each `topic-distanceₙ` is a positive log2 distance, so at most 256.
    | .regtopic _ _ _ _ ds | .topicquery _ _ ds => ds.all fun d => 1 ≤ d ∧ d ≤ MAX_DISTANCE
    | _ => true

/-- The plaintext of a message: its type byte, then the RLP list of its fields. -/
def encode (m : Message) : Except RlpError ByteArray := do
  -- `message-pt = message-type || message-data`, with `message-data` an RLP list.
  return ⟨#[m.type]⟩ ++ (← Serialization.Rlp.encode (.list m.fields))

/-- The message that a plaintext writes, before the checks on sizes and distances. -/
def decodeFields (bytes : ByteArray) : Except MessageError Message := do
  -- `message-pt = message-type || message-data`.
  let type :: rest := bytes.data.toList | throw .empty
  -- The source defines the message types 0x01 to 0x0a.
  unless 1 ≤ type.toNat ∧ type.toNat ≤ 10 do throw (.unknownType type)
  -- `message-data` is one RLP list.
  let item ← (Serialization.Rlp.decode ⟨rest.toArray⟩).mapError .rlp
  let items ← item.toItems.mapError .rlp
  let some m ← (ofFields type items).mapError .rlp | throw (.fields type items.length)
  return m

/-- The message of a plaintext, or why it is not a valid message. -/
def decode (bytes : ByteArray) : Except MessageError Message := do
  let m ← decodeFields bytes
  -- Then the bounds of the wire format on the request ID, the address and the distances.
  unless m.valid do throw (.invalid m.type)
  return m

end Message

end EthLib.Networking.Discv5
