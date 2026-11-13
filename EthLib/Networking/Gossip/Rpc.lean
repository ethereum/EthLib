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

Topics are UTF-8 strings, and [proto2][string] asks every string to be UTF-8.

An RPC is rejected when any topic or topic ID is not valid UTF-8, which is a choice of EthLib.

A field the schema does not name is skipped.

A field the schema names but with another wire type is rejected, which is a choice of EthLib.

The four forbidden fields are rejected whatever their wire type.

A missing optional field reads as its default: false, zero or empty.

A singular field that occurs twice keeps its last value, as [the encoding guide][last] says.

Each occurrence of the control field is decoded alone, then their lists are joined in order.

The extension fields come from the [v1.3 schema][v13] and the [partial messages schema][partial].

A singular message field that occurs twice keeps its last occurrence whole, a choice of EthLib.

Protobuf would merge the occurrences field by field instead.

The extensions of the control field keep their last occurrence too, across its occurrences.

The encoder writes the flags of the extensions only when true, and their messages only when present.

It writes the partial message and the parts metadata of a partial message only when present.

So an RPC without extensions encodes as it did before them.

The experimental extension fields are skipped, as every field the schema does not name.

[rpc]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#the-rpc
[message]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#the-message
[policy]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#signature-policy-options
[v10]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#protobuf
[v11]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#protobuf
[v12]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.2.md#protobuf-extension
[string]: https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/proto2.md#scalar-value-types-scalar
[v13]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.3.md#protobuf
[partial]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/partial-messages.md#protobuf
[last]: https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/encoding.md#last-one-wins-last-one-wins
-/

@[expose] public section

namespace EthLib.Networking.Gossip

open EthLib.Networking.Encoding.Protobuf

/-- A subscription change: subscribe to a topic, or unsubscribe from it. -/
structure SubOpts where
  subscribe : Bool := false
  topicId : String := ""
  /-- The sender asks for partial messages on the topic. -/
  requestsPartial : Bool := false
  /-- The sender can send partial messages on the topic. -/
  supportsSendingPartial : Bool := false
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

/-- The extensions that a peer supports, from gossipsub v1.3. -/
structure ControlExtensions where
  /-- The peer supports the partial message extension. -/
  partialMessages : Bool := false
  deriving DecidableEq

/-- The control messages of one RPC. -/
structure Control where
  ihave : List IHave := []
  iwant : List IWant := []
  graft : List Graft := []
  prune : List Prune := []
  idontwant : List IDontWant := []
  /-- The extensions that the sender supports, sent at most once, in its first RPC. -/
  extensions : Option ControlExtensions := none
  deriving DecidableEq

/-- A partial message: a part of a full message, or the parts that the sender has and wants. -/
structure PartialMessagesExtension where
  /-- The topic. -/
  topicId : ByteArray := .empty
  /-- The ID of the group that the full message belongs to. -/
  groupId : ByteArray := .empty
  /-- The encoded partial message; a peer that did not ask for it must get none. -/
  partialMessage : Option ByteArray := none
  /-- The encoded parts that the sender has and wants. -/
  partsMetadata : Option ByteArray := none
  deriving DecidableEq

/-- One RPC: subscription changes, published messages and control messages.

It may carry a partial message too. -/
structure Rpc where
  subscriptions : List SubOpts := []
  publish : List Message := []
  control : Control := {}
  /-- The field `partial` of the schema, renamed since `partial` is a keyword of Lean. -/
  partialMessage : Option PartialMessagesExtension := none
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

/-- The stable code of an error, one per constructor, for the C exports.

A protobuf error keeps one code; which one it is shows only in the message.

The codes start at 101, so they never collide with the codes 1 to 4 of the payload errors. -/
def RpcError.code : RpcError → UInt32
  | .protobuf _ => 101
  | .signed _ => 102
  | .missingTopic => 103
  | .wireType .. => 104
  | .utf8 _ => 105

/-- The field numbers that `StrictNoSign` forbids in a message. -/
def signedFields : List Nat := [1, 3, 5, 6]

/-! ## Decoding -/

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

/-- Every value of a repeated field, each read by the given reader. -/
def repeated (read : Nat → Value → Except RpcError α) (rs : List Record) (field : Nat) :
    Except RpcError (List α) :=
  (valuesOf rs field).mapM (read field)

/-- The last value of a singular field, or the default when it is missing.

Every occurrence must still be well formed. -/
def singular (read : Nat → Value → Except RpcError α) (default : α) (rs : List Record)
    (field : Nat) : Except RpcError α :=
  return (← repeated read rs field).getLastD default

/-- The last value of a singular message field, decoded, or none when it is missing.

Every occurrence must still decode. -/
def lastMessage (decode : ByteArray → Except RpcError α) (rs : List Record) (field : Nat) :
    Except RpcError (Option α) :=
  return (← (← repeated bytesOf rs field).mapM decode).getLast?

/-- The records of a message. -/
def recordsOf (bytes : ByteArray) : Except RpcError (List Record) :=
  (records bytes.data.toList).mapError .protobuf

/-- A subscription change. -/
def decodeSubOpts (bytes : ByteArray) : Except RpcError SubOpts := do
  let rs ← recordsOf bytes
  -- A bool is written as 0 or 1.
  --
  -- Reading any other value as true is a choice of EthLib.
  let subscribe ← singular uint64Of 0 rs 1
  let requestsPartial ← singular uint64Of 0 rs 3
  let supportsSendingPartial ← singular uint64Of 0 rs 4
  return {
    subscribe := subscribe != 0
    topicId := ← singular stringOf "" rs 2
    requestsPartial := requestsPartial != 0
    supportsSendingPartial := supportsSendingPartial != 0 }

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

/-- The extensions of a control message. -/
def decodeControlExtensions (bytes : ByteArray) : Except RpcError ControlExtensions := do
  return { partialMessages := (← singular uint64Of 0 (← recordsOf bytes) 10) != 0 }

/-- The control messages of an RPC. -/
def decodeControl (bytes : ByteArray) : Except RpcError Control := do
  let rs ← recordsOf bytes
  return {
    ihave := ← (← repeated bytesOf rs 1).mapM decodeIHave
    iwant := ← (← repeated bytesOf rs 2).mapM decodeIWant
    graft := ← (← repeated bytesOf rs 3).mapM decodeGraft
    prune := ← (← repeated bytesOf rs 4).mapM decodePrune
    idontwant := ← (← repeated bytesOf rs 5).mapM decodeIDontWant
    extensions := ← lastMessage decodeControlExtensions rs 6 }

/-- Merge two control messages: each list of the second follows that of the first.

The extensions of the second win, if it has some. -/
def Control.merge (a b : Control) : Control :=
  ⟨a.ihave ++ b.ihave, a.iwant ++ b.iwant, a.graft ++ b.graft, a.prune ++ b.prune,
    a.idontwant ++ b.idontwant, b.extensions.or a.extensions⟩

/-- A partial message. -/
def decodePartial (bytes : ByteArray) : Except RpcError PartialMessagesExtension := do
  let rs ← recordsOf bytes
  return {
    topicId := ← singular bytesOf .empty rs 1
    groupId := ← singular bytesOf .empty rs 2
    partialMessage := (← repeated bytesOf rs 3).getLast?
    partsMetadata := (← repeated bytesOf rs 4).getLast? }

/-- An RPC.

The control field is singular: each occurrence is decoded alone, then they merge. -/
def decodeRpc (bytes : ByteArray) : Except RpcError Rpc := do
  let rs ← recordsOf bytes
  let subscriptions ← (← repeated bytesOf rs 1).mapM decodeSubOpts
  let publish ← (← repeated bytesOf rs 2).mapM decodeMessage
  let control := (← (← repeated bytesOf rs 3).mapM decodeControl).foldl Control.merge {}
  return { subscriptions, publish, control, partialMessage := ← lastMessage decodePartial rs 10 }

/-! ## Encoding

The encoder writes every singular field, except the optional fields of the extensions.

It writes the control field only when a control list is not empty, or it has extensions.
-/

/-- The bytes of a subscription change. -/
def SubOpts.encode (s : SubOpts) : ByteArray :=
  serialize ([⟨1, .varint (if s.subscribe then 1 else 0)⟩, stringRecord 2 s.topicId] ++
    (if s.requestsPartial then [⟨3, .varint 1⟩] else []) ++
    if s.supportsSendingPartial then [⟨4, .varint 1⟩] else [])

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

/-- The bytes of the extensions of a control message. -/
def ControlExtensions.encode (e : ControlExtensions) : ByteArray :=
  serialize (if e.partialMessages then [⟨10, .varint 1⟩] else [])

/-- The bytes of the control messages of an RPC. -/
def Control.encode (c : Control) : ByteArray :=
  serialize (c.ihave.map (lenRecord 1 ∘ IHave.encode) ++
    c.iwant.map (lenRecord 2 ∘ IWant.encode) ++ c.graft.map (lenRecord 3 ∘ Graft.encode) ++
    c.prune.map (lenRecord 4 ∘ Prune.encode) ++ c.idontwant.map (lenRecord 5 ∘ IDontWant.encode) ++
    c.extensions.toList.map (lenRecord 6 ∘ ControlExtensions.encode))

/-- The bytes of a partial message. -/
def PartialMessagesExtension.encode (m : PartialMessagesExtension) : ByteArray :=
  serialize ([lenRecord 1 m.topicId, lenRecord 2 m.groupId] ++
    m.partialMessage.toList.map (lenRecord 3) ++ m.partsMetadata.toList.map (lenRecord 4))

/-- The bytes of an RPC. -/
def Rpc.encode (rpc : Rpc) : ByteArray :=
  serialize (rpc.subscriptions.map (lenRecord 1 ∘ SubOpts.encode) ++
    rpc.publish.map (lenRecord 2 ∘ Message.encode) ++
    (if rpc.control = {} then [] else [lenRecord 3 rpc.control.encode]) ++
    rpc.partialMessage.toList.map (lenRecord 10 ∘ PartialMessagesExtension.encode))

/-! ## Rules of the partial message extension -/

/-- Whether the sender asks for partial messages on the topic of a subscription change.

The flag counts only in a subscription: an unsubscription ignores it. -/
def SubOpts.asksPartial (s : SubOpts) : Bool :=
  s.subscribe && s.requestsPartial

/-- Whether the sender can send partial messages on the topic of a subscription change.

A sender that asks for partial messages can send them too.

The flags count only in a subscription: an unsubscription ignores them. -/
def SubOpts.sendsPartial (s : SubOpts) : Bool :=
  s.subscribe && (s.supportsSendingPartial || s.requestsPartial)

/-- Whether only the first RPC of a stream carries extensions, if any does.

Two extensions within one RPC are not seen here, since the decoder keeps the last one. -/
def checkExtensionsOrder (rpcs : List Rpc) : Bool :=
  rpcs.drop 1 |>.all (·.control.extensions.isNone)

end EthLib.Networking.Gossip
