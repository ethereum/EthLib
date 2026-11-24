module

public import EthLib.Networking.Encoding.Protobuf
public import EthLib.Networking.ReqResp.Encoding

/-!
# `Networking.Gossip.Rpc`

The RPC that carries gossip between two peers, from [pubsub, section The RPC][rpc].

Its control messages follow gossipsub [v1.0][v10], [v1.1][v11] and [v1.2][v12].

Its extension fields come from the [v1.3 schema][v13] and the [partial messages schema][partial].

The consensus layer applies the `StrictNoSign` [signature policy][policy].

[rpc]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/README.md#the-rpc
[policy]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/README.md#signature-policy-options
[v10]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.0.md#protobuf
[v11]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#protobuf
[v12]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.2.md#protobuf-extension
[v13]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.3.md#protobuf
[partial]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/partial-messages.md#protobuf
-/

@[expose] public section

namespace EthLib.Networking.Gossip

open EthLib.Networking.Encoding.Protobuf
open EthLib.Networking.ReqResp (maxMessageSize)

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
  /-- The RPC is longer than the largest gossip message. -/
  | tooLong (size : Nat)
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
  | .tooLong _ => 106

/-- The field numbers that `StrictNoSign` forbids in a message, even with an empty value.

They are the fields `from`, `seqno`, `signature` and `key`. -/
def signedFields : List Nat := [1, 3, 5, 6]

/-! ## Decoding -/

/-- The bytes of a length-delimited value. -/
def bytesOf (field : Nat) : Value → Except RpcError ByteArray
  | .len bytes => .ok bytes
  -- A field the schema names but with another wire type is rejected, a choice of EthLib.
  | v => .error (.wireType field v.wireType)

/-- The string of a length-delimited value, which must be valid UTF-8.

Topics are UTF-8 strings, and [proto2][string] asks every string to be UTF-8.

[string]: https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/proto2.md#scalar-value-types-scalar
-/
def stringOf (field : Nat) (v : Value) : Except RpcError String := do
  match String.fromUTF8? (← bytesOf field v) with
  | some s => return s
  -- An RPC is rejected when any topic or topic ID is not valid UTF-8, a choice of EthLib.
  | none => throw (.utf8 field)

/-- The number of a varint value. -/
def uint64Of (field : Nat) : Value → Except RpcError UInt64
  | .varint v => .ok v
  -- A field the schema names but with another wire type is rejected, a choice of EthLib.
  | v => .error (.wireType field v.wireType)

/-- Every value of a repeated field, each read by the given reader. -/
def repeated (read : Nat → Value → Except RpcError α) (rs : List Record) (field : Nat) :
    Except RpcError (List α) :=
  (valuesOf rs field).mapM (read field)

/-- The last value of a singular field, or the default when it is missing.

Every occurrence must still be well formed.

A field that occurs twice keeps its last value, as [the encoding guide][last] says.

[last]: https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/encoding.md#last-one-wins-last-one-wins
-/
def singular (read : Nat → Value → Except RpcError α) (default : α) (rs : List Record)
    (field : Nat) : Except RpcError α :=
  -- A missing optional field reads as its default: false, zero or empty.
  return (← repeated read rs field).getLastD default

/-- The last value of a singular message field, decoded, or none when it is missing.

Every occurrence must still decode. -/
def lastMessage (decode : ByteArray → Except RpcError α) (rs : List Record) (field : Nat) :
    Except RpcError (Option α) :=
  -- A field that occurs twice keeps its last occurrence whole, a choice of EthLib.
  --
  -- Protobuf would merge the occurrences field by field instead.
  return (← (← repeated bytesOf rs field).mapM decode).getLast?

/-- The records of a message.

A field the schema does not name is skipped, since each reader picks its fields by number. -/
def recordsOf (bytes : ByteArray) : Except RpcError (List Record) :=
  (records bytes.data.toList).mapError .protobuf

/-- A subscription change. -/
def decodeSubOpts (bytes : ByteArray) : Except RpcError SubOpts := do
  let rs ← recordsOf bytes
  -- SubOpts of the pubsub schema: `subscribe = 1` and `topicid = 2`.
  --
  -- The extensions schema adds `requestsPartial = 3` and `supportsSendingPartial = 4`.
  --
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

/-- A published message, which `StrictNoSign` forbids to hold any of four fields.

A message must hold a topic, since [the message schema][message] makes it required.

[message]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/README.md#the-message
-/
def decodeMessage (bytes : ByteArray) : Except RpcError Message := do
  let rs ← recordsOf bytes
  -- StrictNoSign, consuming side: `from`, `seqno`, `signature` and `key` are absent, else reject.
  --
  -- The four forbidden fields are rejected whatever their wire type.
  if let some r := rs.find? (·.field ∈ signedFields) then throw (.signed r.field)
  -- Message: `data = 2`, optional bytes.
  let data ← singular bytesOf .empty rs 2
  -- Message: `topic = 4`, a required string, so a message without it is rejected.
  let some topic := (← repeated stringOf rs 4).getLast? | throw .missingTopic
  return { data, topic }

/-- An IHAVE message. -/
def decodeIHave (bytes : ByteArray) : Except RpcError IHave := do
  let rs ← recordsOf bytes
  -- ControlIHave, v1.0: `topicID = 1`, optional string, and `messageIDs = 2`, repeated bytes.
  return { topicId := ← singular stringOf "" rs 1, messageIds := ← repeated bytesOf rs 2 }

/-- An IWANT message. -/
def decodeIWant (bytes : ByteArray) : Except RpcError IWant := do
  -- ControlIWant, v1.0: `messageIDs = 1`, repeated bytes.
  return { messageIds := ← repeated bytesOf (← recordsOf bytes) 1 }

/-- A GRAFT message. -/
def decodeGraft (bytes : ByteArray) : Except RpcError Graft := do
  -- ControlGraft, v1.0: `topicID = 1`, optional string.
  return { topicId := ← singular stringOf "" (← recordsOf bytes) 1 }

/-- A peer offered in a PRUNE. -/
def decodePeerInfo (bytes : ByteArray) : Except RpcError PeerInfo := do
  let rs ← recordsOf bytes
  -- PeerInfo, v1.1: `peerID = 1` and `signedPeerRecord = 2`, optional bytes.
  return {
    peerId := ← singular bytesOf .empty rs 1
    signedPeerRecord := ← singular bytesOf .empty rs 2 }

/-- A PRUNE message. -/
def decodePrune (bytes : ByteArray) : Except RpcError Prune := do
  let rs ← recordsOf bytes
  -- ControlPrune: `topicID = 1` of v1.0, then `peers = 2` and `backoff = 3`, in seconds, of v1.1.
  let peers ← (← repeated bytesOf rs 2).mapM decodePeerInfo
  return { topicId := ← singular stringOf "" rs 1, peers, backoff := ← singular uint64Of 0 rs 3 }

/-- An IDONTWANT message. -/
def decodeIDontWant (bytes : ByteArray) : Except RpcError IDontWant := do
  -- ControlIDontWant, v1.2: `messageIDs = 1`, repeated bytes.
  return { messageIds := ← repeated bytesOf (← recordsOf bytes) 1 }

/-- The extensions of a control message. -/
def decodeControlExtensions (bytes : ByteArray) : Except RpcError ControlExtensions := do
  -- ControlExtensions: `partialMessages = 10`, optional bool; the experimental fields are skipped.
  return { partialMessages := (← singular uint64Of 0 (← recordsOf bytes) 10) != 0 }

/-- The control messages of an RPC. -/
def decodeControl (bytes : ByteArray) : Except RpcError Control := do
  let rs ← recordsOf bytes
  -- ControlMessage: fields 1 to 4 of v1.0, `idontwant = 5` of v1.2, `extensions = 6` of v1.3.
  return {
    ihave := ← (← repeated bytesOf rs 1).mapM decodeIHave
    iwant := ← (← repeated bytesOf rs 2).mapM decodeIWant
    graft := ← (← repeated bytesOf rs 3).mapM decodeGraft
    prune := ← (← repeated bytesOf rs 4).mapM decodePrune
    idontwant := ← (← repeated bytesOf rs 5).mapM decodeIDontWant
    extensions := ← lastMessage decodeControlExtensions rs 6 }

/-- Merge two control messages: each list of the second follows that of the first.

The extensions of the second win, if it has some.

So the extensions keep their last occurrence, across the occurrences of the control field. -/
def Control.merge (a b : Control) : Control :=
  ⟨a.ihave ++ b.ihave, a.iwant ++ b.iwant, a.graft ++ b.graft, a.prune ++ b.prune,
    a.idontwant ++ b.idontwant, b.extensions.or a.extensions⟩

/-- A partial message. -/
def decodePartial (bytes : ByteArray) : Except RpcError PartialMessagesExtension := do
  let rs ← recordsOf bytes
  -- PartialMessagesExtension: `topicID = 1` and `groupID = 2`, optional bytes.
  --
  -- Then `partialMessage = 3` and `partsMetadata = 4`, optional bytes, kept only when present.
  return {
    topicId := ← singular bytesOf .empty rs 1
    groupId := ← singular bytesOf .empty rs 2
    partialMessage := (← repeated bytesOf rs 3).getLast?
    partsMetadata := (← repeated bytesOf rs 4).getLast? }

/-- Whether an encoded RPC fits the largest gossip message, for the payload cap of the network.

Clients must reject a longer one, by the gossip size limits of the phase 0 p2p interface. -/
def withinMessageSize (maxPayloadSize : UInt64) (bytes : ByteArray) : Bool :=
  -- The largest message is the worst-case compression of the cap plus 1024 bytes, at least 1 MiB.
  --
  -- A bound that overflows 64 bits admits no RPC.
  match maxMessageSize maxPayloadSize with
  -- The whole encoded RPC counts, with its control messages, framing and topics.
  | .ok limit => bytes.size ≤ limit.toNat
  | .error _ => false

/-- An RPC, for the payload cap of the network.

The control field is singular: each occurrence is decoded alone, then they merge. -/
def decodeRpc (maxPayloadSize : UInt64) (bytes : ByteArray) : Except RpcError Rpc := do
  -- Clients "MUST reject" a message whose encoded RPC exceeds the largest gossip message.
  unless withinMessageSize maxPayloadSize bytes do throw (.tooLong bytes.size)
  let rs ← recordsOf bytes
  -- The RPC: `subscriptions = 1` and `publish = 2`, repeated.
  let subscriptions ← (← repeated bytesOf rs 1).mapM decodeSubOpts
  let publish ← (← repeated bytesOf rs 2).mapM decodeMessage
  -- Protobuf of v1.0: `control = 3`, optional; each occurrence decodes alone, then the lists join.
  --
  -- The extensions schema: `partial = 10`, optional; the experimental RPC fields are skipped.
  --
  -- The experimental fields are skipped as every field the schema does not name.
  let control := (← (← repeated bytesOf rs 3).mapM decodeControl).foldl Control.merge {}
  return { subscriptions, publish, control, partialMessage := ← lastMessage decodePartial rs 10 }

/-! ## Encoding

The encoder writes every singular field, except the optional fields of the extensions.

It writes the control field only when a control list is not empty, or it has extensions.

So an RPC without extensions encodes as it did before them.
-/

/-- The bytes of a subscription change. -/
def SubOpts.encode (s : SubOpts) : ByteArray :=
  -- The two flags of the partial message extension only when true.
  serialize ([⟨1, .varint (if s.subscribe then 1 else 0)⟩, stringRecord 2 s.topicId] ++
    (if s.requestsPartial then [⟨3, .varint 1⟩] else []) ++
    if s.supportsSendingPartial then [⟨4, .varint 1⟩] else [])

/-- The bytes of a message: its data, then its topic. -/
def Message.encode (m : Message) : ByteArray :=
  -- StrictNoSign, producing side: no `from`, `seqno`, `signature` or `key`, not even empty.
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
  -- The flag only when true.
  serialize (if e.partialMessages then [⟨10, .varint 1⟩] else [])

/-- The bytes of the control messages of an RPC. -/
def Control.encode (c : Control) : ByteArray :=
  serialize (c.ihave.map (lenRecord 1 ∘ IHave.encode) ++
    c.iwant.map (lenRecord 2 ∘ IWant.encode) ++ c.graft.map (lenRecord 3 ∘ Graft.encode) ++
    c.prune.map (lenRecord 4 ∘ Prune.encode) ++ c.idontwant.map (lenRecord 5 ∘ IDontWant.encode) ++
    -- The extensions message only when present.
    c.extensions.toList.map (lenRecord 6 ∘ ControlExtensions.encode))

/-- The bytes of a partial message. -/
def PartialMessagesExtension.encode (m : PartialMessagesExtension) : ByteArray :=
  serialize ([lenRecord 1 m.topicId, lenRecord 2 m.groupId] ++
    -- The partial message and the parts metadata only when present.
    m.partialMessage.toList.map (lenRecord 3) ++ m.partsMetadata.toList.map (lenRecord 4))

/-- The bytes of an RPC. -/
def Rpc.encode (rpc : Rpc) : ByteArray :=
  serialize (rpc.subscriptions.map (lenRecord 1 ∘ SubOpts.encode) ++
    rpc.publish.map (lenRecord 2 ∘ Message.encode) ++
    -- The control field only when it holds a control message or extensions.
    (if rpc.control = {} then [] else [lenRecord 3 rpc.control.encode]) ++
    -- The partial message extension only when present.
    rpc.partialMessage.toList.map (lenRecord 10 ∘ PartialMessagesExtension.encode))

/-! ## Rules of the partial message extension -/

/-- Whether the sender asks for partial messages on the topic of a subscription change.

The flag counts only in a subscription: an unsubscription ignores it. -/
def SubOpts.asksPartial (s : SubOpts) : Bool :=
  -- Partial messages: the flags are ignored when the peer sends an unsubscribe.
  s.subscribe && s.requestsPartial

/-- Whether the sender can send partial messages on the topic of a subscription change.

A sender that asks for partial messages can send them too.

The flags count only in a subscription: an unsubscription ignores them. -/
def SubOpts.sendsPartial (s : SubOpts) : Bool :=
  -- Partial messages: a node that requests partial messages must support sending them.
  s.subscribe && (s.supportsSendingPartial || s.requestsPartial)

/-- Whether only the first RPC of a stream carries extensions, if any does.

Two extensions within one RPC are not seen here, since the decoder keeps the last one. -/
def checkExtensionsOrder (rpcs : List Rpc) : Bool :=
  -- v1.3: the Extensions control message is in the first message on the stream, and never again.
  rpcs.drop 1 |>.all (·.control.extensions.isNone)

end EthLib.Networking.Gossip
