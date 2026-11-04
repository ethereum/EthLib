module

public import EthLib.Serialization.Rlp.Codec

/-!
# `Networking.Discv5.Message`

The messages of discv5, from "Protocol Messages" of `discv5-wire.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-wire.md>

A message is its type byte, then the RLP list of its fields.

The first field of every message is the request ID, a byte string of at most 8 bytes.

A node record in a message stays an RLP item, for the ENR decoder to read.
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
  /-- The message has more or fewer fields than its type. -/
  | fields (type : UInt8)
  /-- A request ID, an address or a distance is out of its range. -/
  | invalid
  deriving DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 101, since the packet errors share their Python class and use 1 to 7.

A new constructor takes a new code, so that each code keeps its meaning. -/
def MessageError.code : MessageError → UInt32
  | .empty => 101
  | .unknownType _ => 102
  | .rlp _ => 103
  | .fields _ => 104
  | .invalid => 105

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
  | .ping id seq => [Codec.toItem id, Codec.toItem seq]
  | .pong id seq ip port => [Codec.toItem id, Codec.toItem seq, Codec.toItem ip, portItem port]
  | .findnode id ds => [Codec.toItem id, Codec.toItem ds]
  | .nodes id total rs => [Codec.toItem id, Codec.toItem total, Codec.toItem rs]
  | .talkreq id p r => [Codec.toItem id, Codec.toItem p, Codec.toItem r]
  | .talkresp id r => [Codec.toItem id, Codec.toItem r]
  | .regtopic id t rec ticket ds =>
    [Codec.toItem id, Codec.toItem t, rec, Codec.toItem ticket, Codec.toItem ds]
  | .regconfirmation id total ticket wait =>
    [Codec.toItem id, Codec.toItem total, Codec.toItem ticket, Codec.toItem wait]
  | .topicquery id t ds => [Codec.toItem id, Codec.toItem t, Codec.toItem ds]
  | .topicnodes id total rs => [Codec.toItem id, Codec.toItem total, Codec.toItem rs]

/-- The message of a type, from its fields, without the checks on sizes and distances. -/
def ofFields (type : UInt8) (items : List Item) : Except RlpError (Option Message) :=
  match type.toNat, items with
  | 1, [id, seq] => do return some (.ping (← Codec.ofItem id) (← Codec.ofItem seq))
  | 2, [id, seq, ip, port] => do
    return some (.pong (← Codec.ofItem id) (← Codec.ofItem seq) (← Codec.ofItem ip)
      (← portOfItem port))
  | 3, [id, ds] => do return some (.findnode (← Codec.ofItem id) (← Codec.ofItem ds))
  | 4, [id, total, rs] => do
    return some (.nodes (← Codec.ofItem id) (← Codec.ofItem total) (← Codec.ofItem rs))
  | 5, [id, p, r] => do
    return some (.talkreq (← Codec.ofItem id) (← Codec.ofItem p) (← Codec.ofItem r))
  | 6, [id, r] => do return some (.talkresp (← Codec.ofItem id) (← Codec.ofItem r))
  | 7, [id, t, rec, ticket, ds] => do
    return some (.regtopic (← Codec.ofItem id) (← Codec.ofItem t) rec (← Codec.ofItem ticket)
      (← Codec.ofItem ds))
  | 8, [id, total, ticket, wait] => do
    return some (.regconfirmation (← Codec.ofItem id) (← Codec.ofItem total)
      (← Codec.ofItem ticket) (← Codec.ofItem wait))
  | 9, [id, t, ds] => do
    return some (.topicquery (← Codec.ofItem id) (← Codec.ofItem t) (← Codec.ofItem ds))
  | 10, [id, total, rs] => do
    return some (.topicnodes (← Codec.ofItem id) (← Codec.ofItem total) (← Codec.ofItem rs))
  | _, _ => return none

/-- The request ID of a message. -/
def requestId : Message → ByteArray
  | .ping id .. | .pong id .. | .findnode id .. | .nodes id .. | .talkreq id ..
  | .talkresp id .. | .regtopic id .. | .regconfirmation id .. | .topicquery id ..
  | .topicnodes id .. => id

/-- Whether the sizes and distances of a message are those that the wire format allows.

The request ID has at most 8 bytes, and an address 4 or 16 bytes.

A distance of FINDNODE is at most 256, and a distance from a topic is 1 to 256. -/
def valid (m : Message) : Bool :=
  m.requestId.size ≤ MAX_REQUEST_ID_SIZE &&
    match m with
    | .pong _ _ ip _ => ip.size == 4 || ip.size == 16
    | .findnode _ ds => ds.all (· ≤ MAX_DISTANCE)
    -- A topic distance is a positive integer.
    | .regtopic _ _ _ _ ds | .topicquery _ _ ds => ds.all fun d => 1 ≤ d ∧ d ≤ MAX_DISTANCE
    | _ => true

/-- The plaintext of a message: its type byte, then the RLP list of its fields. -/
def encode (m : Message) : Except RlpError ByteArray := do
  return ⟨#[m.type]⟩ ++ (← Serialization.Rlp.encode (.list m.fields))

/-- The message that a plaintext writes, before the checks on sizes and distances. -/
def decodeFields (bytes : ByteArray) : Except MessageError Message := do
  let type :: rest := bytes.data.toList | throw .empty
  unless 1 ≤ type.toNat ∧ type.toNat ≤ 10 do throw (.unknownType type)
  let item ← (Serialization.Rlp.decode ⟨rest.toArray⟩).mapError .rlp
  let items ← item.toItems.mapError .rlp
  let some m ← (ofFields type items).mapError .rlp | throw (.fields type)
  return m

/-- The message of a plaintext, or why it is not a valid message. -/
def decode (bytes : ByteArray) : Except MessageError Message := do
  let m ← decodeFields bytes
  unless m.valid do throw .invalid
  return m

end Message

end EthLib.Networking.Discv5
