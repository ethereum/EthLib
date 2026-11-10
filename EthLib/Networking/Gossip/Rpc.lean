module

public import EthLib.Networking.Encoding.Protobuf

/-!
# `Networking.Gossip.Rpc`

The RPC that carries gossip between two peers, from [pubsub, "The RPC"][rpc].

An RPC holds subscriptions, published messages and control messages.

The control messages follow the schemas of gossipsub [v1.0][v10], [v1.1][v11] and [v1.2][v12].

The consensus layer applies the `StrictNoSign` [signature policy][policy].

So a message must not hold the field `from`, `seqno`, `signature` or `key`, not even empty.

A message must hold a topic, since [the message schema][message] makes it required.

The consensus layer makes topics UTF-8 strings, so each topic must be valid UTF-8.

A field the schema does not name is skipped.

A field the schema names must have the wire type of its type.

A missing singular field reads as its default: false, zero or empty.

A singular field that occurs twice keeps its last value, as [the encoding guide][last] says.

Two control messages merge, so their lists join.

[rpc]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#the-rpc
[message]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#the-message
[policy]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#signature-policy-options
[v10]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#protobuf
[v11]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#protobuf
[v12]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.2.md#protobuf-extension
[last]: https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/encoding.md#last-one-wins
-/

@[expose] public section

namespace EthLib.Networking.Gossip.Rpc

open EthLib.Networking.Encoding.Protobuf

/-- A subscription change: subscribe to a topic, or unsubscribe from it. -/
structure SubOpts where
  subscribe : Bool := false
  topicId : String := ""
  deriving DecidableEq

/-- A published message, under the `StrictNoSign` policy. -/
structure Message where
  data : ByteArray := .empty
  topic : String
  deriving DecidableEq

/-- IHAVE: the IDs of messages the sender has seen on a topic. -/
structure IHave where
  topicId : String := ""
  messageIds : List ByteArray := []
  deriving DecidableEq

/-- IWANT: the IDs of messages the sender asks for. -/
structure IWant where
  messageIds : List ByteArray := []
  deriving DecidableEq

/-- GRAFT: the sender added the receiver to its mesh of a topic. -/
structure Graft where
  topicId : String := ""
  deriving DecidableEq

/-- A peer offered in a PRUNE, with its signed peer record when the sender has one. -/
structure PeerInfo where
  peerId : ByteArray := .empty
  signedPeerRecord : ByteArray := .empty
  deriving DecidableEq

/-- PRUNE: the sender removed the receiver from its mesh of a topic.

It may offer other peers, and a backoff in seconds before the receiver grafts again. -/
structure Prune where
  topicId : String := ""
  peers : List PeerInfo := []
  backoff : UInt64 := 0
  deriving DecidableEq

/-- IDONTWANT: the IDs of messages the sender does not want to receive. -/
structure IDontWant where
  messageIds : List ByteArray := []
  deriving DecidableEq

/-- The control messages of one RPC. -/
structure Control where
  ihave : List IHave := []
  iwant : List IWant := []
  graft : List Graft := []
  prune : List Prune := []
  idontwant : List IDontWant := []
  deriving DecidableEq

/-- One RPC: subscription changes, published messages and control messages. -/
structure Rpc where
  subscriptions : List SubOpts := []
  publish : List Message := []
  control : Control := {}
  deriving DecidableEq

/-- Every way an RPC can be rejected. -/
inductive RpcError where
  /-- The bytes are not a sequence of protobuf records. -/
  | protobuf (error : ProtobufError)
  /-- A message holds the field `from` (1), `seqno` (3), `signature` (5) or `key` (6). -/
  | signed (field : Nat)
  /-- A message holds no topic. -/
  | missingTopic
  /-- A field of the schema has another wire type than its type. -/
  | wireType (field wire : Nat)
  /-- A topic is not valid UTF-8. -/
  | utf8 (field : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports. -/
def RpcError.code : RpcError → UInt32
  | .protobuf _ => 1
  | .signed _ => 2
  | .missingTopic => 3
  | .wireType .. => 4
  | .utf8 _ => 5

/-- The field numbers that `StrictNoSign` forbids in a message. -/
def signedFields : List Nat := [1, 3, 5, 6]

/-! ## Decoding -/

/-- The values of one field, in the order of the records. -/
def valuesOf (rs : List Record) (field : Nat) : List Value :=
  rs.filterMap fun r => if r.field = field then some r.value else none

/-- The bytes of a length-delimited value. -/
def bytesOf (field : Nat) : Value → Except RpcError ByteArray
  | .len bytes => .ok bytes
  | v => .error (.wireType field v.wireType)

/-- The string of a length-delimited value, which must be valid UTF-8. -/
def stringOf (field : Nat) (v : Value) : Except RpcError String := do
  match String.fromUTF8? (← bytesOf field v) with
  | some s => return s
  | none => throw (.utf8 field)

/-- The number of a varint value. -/
def uint64Of (field : Nat) : Value → Except RpcError UInt64
  | .varint v => .ok v
  | v => .error (.wireType field v.wireType)

/-- Every value of a repeated field, each read by `read`. -/
def repeated (read : Nat → Value → Except RpcError α) (rs : List Record) (field : Nat) :
    Except RpcError (List α) :=
  (valuesOf rs field).mapM (read field)

/-- The last value of a singular field, or the default when it is missing.

Every occurrence must still be well formed. -/
def singular (read : Nat → Value → Except RpcError α) (default : α) (rs : List Record)
    (field : Nat) : Except RpcError α :=
  return (← repeated read rs field).getLastD default

/-- The records of a message. -/
def recordsOf (bytes : ByteArray) : Except RpcError (List Record) :=
  (records bytes.data.toList).mapError .protobuf

/-- A subscription change. -/
def decodeSubOpts (bytes : ByteArray) : Except RpcError SubOpts := do
  let rs ← recordsOf bytes
  -- A bool is a varint, and any value other than zero is true.
  let subscribe ← singular uint64Of 0 rs 1
  return { subscribe := subscribe != 0, topicId := ← singular stringOf "" rs 2 }

/-- A published message, which `StrictNoSign` forbids to hold any of four fields. -/
def decodeMessage (bytes : ByteArray) : Except RpcError Message := do
  let rs ← recordsOf bytes
  if let some r := rs.find? (·.field ∈ signedFields) then throw (.signed r.field)
  let data ← singular bytesOf .empty rs 2
  let some topic := (← repeated stringOf rs 4).getLast? | throw .missingTopic
  return { data, topic }

/-- An IHAVE message. -/
def decodeIHave (bytes : ByteArray) : Except RpcError IHave := do
  let rs ← recordsOf bytes
  return { topicId := ← singular stringOf "" rs 1, messageIds := ← repeated bytesOf rs 2 }

/-- An IWANT message. -/
def decodeIWant (bytes : ByteArray) : Except RpcError IWant := do
  return { messageIds := ← repeated bytesOf (← recordsOf bytes) 1 }

/-- A GRAFT message. -/
def decodeGraft (bytes : ByteArray) : Except RpcError Graft := do
  return { topicId := ← singular stringOf "" (← recordsOf bytes) 1 }

/-- A peer offered in a PRUNE. -/
def decodePeerInfo (bytes : ByteArray) : Except RpcError PeerInfo := do
  let rs ← recordsOf bytes
  return {
    peerId := ← singular bytesOf .empty rs 1
    signedPeerRecord := ← singular bytesOf .empty rs 2 }

/-- A PRUNE message. -/
def decodePrune (bytes : ByteArray) : Except RpcError Prune := do
  let rs ← recordsOf bytes
  let peers ← (← repeated bytesOf rs 2).mapM decodePeerInfo
  return { topicId := ← singular stringOf "" rs 1, peers, backoff := ← singular uint64Of 0 rs 3 }

/-- An IDONTWANT message. -/
def decodeIDontWant (bytes : ByteArray) : Except RpcError IDontWant := do
  return { messageIds := ← repeated bytesOf (← recordsOf bytes) 1 }

/-- The control messages of an RPC. -/
def decodeControl (bytes : ByteArray) : Except RpcError Control := do
  let rs ← recordsOf bytes
  return {
    ihave := ← (← repeated bytesOf rs 1).mapM decodeIHave
    iwant := ← (← repeated bytesOf rs 2).mapM decodeIWant
    graft := ← (← repeated bytesOf rs 3).mapM decodeGraft
    prune := ← (← repeated bytesOf rs 4).mapM decodePrune
    idontwant := ← (← repeated bytesOf rs 5).mapM decodeIDontWant }

/-- An RPC.

The control field is singular, and its occurrences merge, so their bytes are joined first. -/
def decodeRpc (bytes : ByteArray) : Except RpcError Rpc := do
  let rs ← recordsOf bytes
  let subscriptions ← (← repeated bytesOf rs 1).mapM decodeSubOpts
  let publish ← (← repeated bytesOf rs 2).mapM decodeMessage
  let control ← decodeControl ((← repeated bytesOf rs 3).foldl (· ++ ·) .empty)
  return { subscriptions, publish, control }

/-! ## Encoding

The encoder writes every singular field, and the control field only when it holds a message.
-/

/-- A length-delimited record. -/
def lenRecord (field : Nat) (bytes : ByteArray) : Record := ⟨field, .len bytes⟩

/-- A string record, in UTF-8. -/
def stringRecord (field : Nat) (s : String) : Record := lenRecord field s.toUTF8

/-- The bytes of a subscription change. -/
def SubOpts.encode (s : SubOpts) : ByteArray :=
  serialize [⟨1, .varint (if s.subscribe then 1 else 0)⟩, stringRecord 2 s.topicId]

/-- The bytes of a message: its data, then its topic. -/
def Message.encode (m : Message) : ByteArray :=
  serialize [lenRecord 2 m.data, stringRecord 4 m.topic]

/-- The bytes of an IHAVE message. -/
def IHave.encode (m : IHave) : ByteArray :=
  serialize (stringRecord 1 m.topicId :: m.messageIds.map (lenRecord 2))

/-- The bytes of an IWANT message. -/
def IWant.encode (m : IWant) : ByteArray :=
  serialize (m.messageIds.map (lenRecord 1))

/-- The bytes of a GRAFT message. -/
def Graft.encode (m : Graft) : ByteArray :=
  serialize [stringRecord 1 m.topicId]

/-- The bytes of a peer offered in a PRUNE. -/
def PeerInfo.encode (p : PeerInfo) : ByteArray :=
  serialize [lenRecord 1 p.peerId, lenRecord 2 p.signedPeerRecord]

/-- The bytes of a PRUNE message. -/
def Prune.encode (m : Prune) : ByteArray :=
  serialize (stringRecord 1 m.topicId :: m.peers.map (lenRecord 2 ∘ PeerInfo.encode) ++
    [⟨3, .varint m.backoff⟩])

/-- The bytes of an IDONTWANT message. -/
def IDontWant.encode (m : IDontWant) : ByteArray :=
  serialize (m.messageIds.map (lenRecord 1))

/-- The bytes of the control messages of an RPC. -/
def Control.encode (c : Control) : ByteArray :=
  serialize (c.ihave.map (lenRecord 1 ∘ IHave.encode) ++
    c.iwant.map (lenRecord 2 ∘ IWant.encode) ++ c.graft.map (lenRecord 3 ∘ Graft.encode) ++
    c.prune.map (lenRecord 4 ∘ Prune.encode) ++ c.idontwant.map (lenRecord 5 ∘ IDontWant.encode))

/-- The bytes of an RPC. -/
def Rpc.encode (rpc : Rpc) : ByteArray :=
  serialize (rpc.subscriptions.map (lenRecord 1 ∘ SubOpts.encode) ++
    rpc.publish.map (lenRecord 2 ∘ Message.encode) ++
    if rpc.control = {} then [] else [lenRecord 3 rpc.control.encode])

end EthLib.Networking.Gossip.Rpc
