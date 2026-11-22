module

public import EthLib.Networking.Rlpx.Handshake
public import EthLib.Networking.Snappy.Compress

/-!
# `Networking.Devp2p.P2p`

The messages Hello, Disconnect, Ping and Pong of the p2p capability, from [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/rlpx.md#capability-messaging

The module follows its sections Message Encoding, Message ID-based Multiplexing and p2p Capability.

The Snappy compression of every message after Hello comes from [EIP-706][eip706].

[eip706]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-706.md#specification
-/

@[expose] public section

namespace EthLib.Networking.Devp2p

open EthLib.Serialization.Rlp

/-- Every way a message can be rejected. -/
inductive P2pError where
  /-- The message ID or the message was not valid RLP of the expected shape. -/
  | rlp (error : RlpError)
  /-- The Snappy block of the message was not valid. -/
  | snappy (error : Snappy.SnappyError)
  /-- The message would decompress to `size` bytes, more than 16 MiB. -/
  | tooLarge (size : Nat)
  /-- The message ID did not name a message of the p2p capability. -/
  | unknownId (id : Nat)
deriving Repr

/--
The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.
-/
def P2pError.code : P2pError → UInt32
  | .rlp _ => 1
  | .snappy _ => 2
  | .tooLarge _ => 3
  | .unknownId _ => 4

/-- The version of the p2p capability in `rlpx.md`. -/
def PROTOCOL_VERSION : Nat := 5

/-- The first version that compresses messages with Snappy, from EIP-706. -/
def SNAPPY_VERSION : Nat := 5

/-- The largest decompressed message that a peer accepts, 16 MiB, from Message Encoding. -/
def MAX_MESSAGE_SIZE : Nat := 16 * 1024 * 1024

/-- The first message ID after the IDs `0x00` to `0x0f` of the p2p capability. -/
def BASE_PROTOCOL_LENGTH : Nat := 0x10

/-- A capability: a short ASCII name and a version. -/
structure Capability where
  /-- The name, compared byte by byte. -/
  name : ByteArray
  /-- The version. -/
  version : Nat
deriving DecidableEq

/-- A capability as the RLP list `[name, version]`. -/
instance : Codec Capability where
  -- Hello lists each capability as `[cap, capVersion]`.
  toItem c := .list [.bytes c.name, Codec.toItem c.version]
  ofItem item := do
    match ← item.fields 2 with
    -- The name is a byte string, and the version an RLP integer.
    --
    -- Not checked: the source limits the name to eight ASCII characters.
    | [n, v] => return ⟨← Codec.ofItem n, ← Codec.ofItem v⟩
    | items => throw (RlpError.wrongFieldCount 2 items.length)

/-- Hello: `[protocolVersion, clientId, capabilities, listenPort, nodeKey, ...]`. -/
structure Hello where
  /-- The version of the p2p capability. -/
  protocolVersion : Nat
  /-- The name of the client software. -/
  clientId : ByteArray
  /-- The capabilities of the sender, with their versions. -/
  capabilities : List Capability
  /-- The port the sender listens on, which the receiver ignores. -/
  listenPort : Nat
  /-- The sender's public key, as the 64 bytes `x || y`. -/
  nodeId : Vector UInt8 64
deriving DecidableEq

/--
Hello as an RLP list of five items.

A reader ignores any further items, as the section Hello (0x00) asks.
-/
instance : Codec Hello where
  -- `[protocolVersion: P, clientId: B, capabilities, listenPort: P, nodeKey: B_64, ...]`.
  --
  -- EthLib writes no further element.
  toItem h := .list [Codec.toItem h.protocolVersion, .bytes h.clientId,
    Codec.toItem h.capabilities, Codec.toItem h.listenPort, Codec.toItem h.nodeId]
  ofItem item := do
    -- Implementations must ignore any additional list elements in Hello.
    match ← Rlpx.leadingFields 5 item with
    -- `capabilities = [[cap1, capVersion1], [cap2, capVersion2], ...]`.
    --
    -- The list names the last field `nodeKey: B_64`, and the text calls it `nodeId`.
    | [v, c, caps, p, n] =>
      return ⟨← Codec.ofItem v, ← Codec.ofItem c, ← Codec.ofItem caps, ← Codec.ofItem p,
        ← Codec.ofItem n⟩
    | items => throw (RlpError.wrongFieldCount 5 items.length)

/-- A message of the p2p capability. -/
inductive Message where
  /-- Hello (0x00), the first message of each side. -/
  | hello (h : Hello)
  /-- Disconnect (0x01), with an optional reason. -/
  | disconnect (reason : Option Nat)
  /-- Ping (0x02), the empty list. -/
  | ping
  /-- Pong (0x03), the empty list. -/
  | pong
deriving DecidableEq

namespace Message

/-- The message ID. -/
def id : Message → Nat
  -- The IDs that the section titles of `rlpx.md` give.
  | hello _ => 0x00
  | disconnect _ => 0x01
  | ping => 0x02
  | pong => 0x03

/-- The message as an RLP list: Disconnect is `[reason]`, or `[]` without a reason. -/
def toItem : Message → Item
  | hello h => Codec.toItem h
  -- Disconnect: `[reason: P]`, where `reason` is optional, so no reason writes `[]`.
  | disconnect none => .list []
  | disconnect (some r) => .list [Codec.toItem r]
  -- Ping and Pong: `[]`.
  | ping => .list []
  | pong => .list []

/-- The message with the ID `id` that the RLP list `item` holds. -/
def ofItem (id : Nat) (item : Item) : Except P2pError Message :=
  match id with
  -- Hello (0x00).
  | 0x00 => (hello <$> Codec.ofItem item).mapError .rlp
  -- Disconnect (0x01): `[reason: P]`, with `reason` an optional integer.
  | 0x01 =>
    match item with
    -- EthLib reads the empty list as a Disconnect without a reason.
    | .list [] => .ok (disconnect none)
    -- Any integer is kept, whether or not the table of reasons lists it.
    | .list [r] => ((fun n => disconnect (some n)) <$> Codec.ofItem r).mapError .rlp
    | .list items => .error (.rlp (.wrongFieldCount 1 items.length))
    -- Not in the source: a reason sent as a bare integer, not in a list, fails.
    | .bytes _ => .error (.rlp .bytesAsList)
  -- Ping (0x02) and Pong (0x03): `[]`, so any other item fails.
  | 0x02 => if item = .list [] then .ok ping else .error (.rlp (.wrongFieldCount 0 1))
  | 0x03 => if item = .list [] then .ok pong else .error (.rlp (.wrongFieldCount 0 1))
  -- Any other ID fails: `0x04` to `0x0f` are reserved and unused, and `0x10` on are not p2p.
  | id => .error (.unknownId id)

end Message

/-- The frame data of a message, compressed when the flag says that the session uses Snappy. -/
def encodeMessage (snappy : Bool) (m : Message) : Except P2pError ByteArray := do
  -- `msg-id` is an RLP-encoded integer identifying the message.
  let id ← (encode (Item.scalar m.id)).mapError .rlp
  -- `msg-data` is an RLP list containing the message data.
  let data ← (encode m.toItem).mapError .rlp
  -- Hello: `frame-data = msg-id || msg-data`.
  --
  -- With Snappy, every message after Hello: `frame-data = msg-id || snappyCompress(msg-data)`.
  --
  -- EIP-706: the handshake message is never compressed, and Snappy framing is not used.
  return id ++ if snappy && m.id != 0x00 then Snappy.compress data else data

/-- The message ID at the start of the frame data `msg-id || msg-data`, and `msg-data`. -/
def splitFrame (frameData : ByteArray) : Except P2pError (Nat × ByteArray) := do
  -- `frame-data = msg-id || msg-data`: `msg-id` is the first RLP item, `msg-data` the rest.
  let (idItem, next) ← ((decodeItem frameData 0 frameData.size).map fun r => (r.1, r.2.1)).mapError
    .rlp
  -- `msg-id` is an RLP-encoded integer, so a list fails.
  let id ← idItem.toScalar.mapError .rlp
  return (id, frameData.extract next frameData.size)

/-- The bytes of `msg-data` before compression, given whether they are compressed. -/
def messageData (compressed : Bool) (rest : ByteArray) : Except P2pError ByteArray :=
  if compressed then do
    -- Check the uncompressed size before decoding: the Snappy preamble holds it.
    let (size, _) ← (Snappy.readPreamble rest.data.toList).mapError .snappy
    -- Messages carrying uncompressed data larger than 16 MiB should be rejected.
    --
    -- EIP-706 sets the same threshold, 16MB, and checks it without inflating the message.
    if MAX_MESSAGE_SIZE < size then throw (.tooLarge size)
    -- EIP-706: decompress the payload with Snappy, right after decrypting it.
    (Snappy.decompress rest).mapError .snappy
  else pure rest

/-- The message of the p2p capability with an ID and the bytes `msg-data`. -/
def decodeBody (snappy : Bool) (id : Nat) (rest : ByteArray) : Except P2pError Message := do
  -- With Snappy, every message after Hello is compressed, and Hello never is.
  let data ← messageData (snappy && id != 0x00) rest
  -- `msg-data` is one RLP item, read as the message of its ID.
  Message.ofItem id (← (decode data).mapError .rlp)

/--
The message in the frame data `msg-id || msg-data`.

A compressed message is rejected before decompression when its declared size exceeds 16 MiB.
-/
def decodeMessage (snappy : Bool) (frameData : ByteArray) : Except P2pError Message := do
  -- `frame-data = msg-id || msg-data`.
  let (id, rest) ← splitFrame frameData
  decodeBody snappy id rest

/-- Whether both peers use Snappy: both Hello messages carry version 5 or more, by EIP-706. -/
def snappyEnabled (ours theirs : Nat) : Bool :=
  -- EIP-706: compress when the remote side advertises a version `>= 5`.
  --
  -- EthLib asks it of its own Hello too, since a node of version 4 runs no compression.
  SNAPPY_VERSION ≤ ours && SNAPPY_VERSION ≤ theirs

/-! ## Message IDs of the shared capabilities -/

/-- Whether the name of `a` comes before the name of `b`, byte by byte. -/
def Capability.nameLe (a b : Capability) : Bool :=
  -- Capability names are case-sensitive.
  --
  -- EthLib reads alphabetic order as the lexicographic order of the bytes of the names.
  a.name.data.toList ≤ b.name.data.toList

/-- The capabilities that both peers support, from the section Message ID-based Multiplexing. -/
def sharedCapabilities (ours theirs : List Capability) : List Capability :=
  -- A shared capability has an equal name and an equal version in both lists.
  --
  -- Capabilities which are not shared are ignored.
  --
  -- EthLib keeps one copy of a capability that a list repeats.
  let shared := (ours.filter (· ∈ theirs)).eraseDups
  -- If multiple versions of one name are shared, the numerically highest wins.
  let best := shared.filter fun c => shared.all fun d => d.name ≠ c.name || d.version ≤ c.version
  -- The IDs go to the shared capabilities in alphabetic order.
  best.mergeSort Capability.nameLe

/-- The first message ID of each capability, given how many IDs each one needs. -/
def messageOffsets (length : Capability → Nat) : List Capability → Nat → List (Capability × Nat)
  | [], _ => []
  -- Message IDs are compact: each capability takes as many IDs as it needs, from the next free.
  | c :: cs, offset => (c, offset) :: messageOffsets length cs (offset + length c)

/-- The message ID offsets of the shared capabilities, from `0x10` on. -/
def negotiate (length : Capability → Nat) (ours theirs : List Capability) :
    List (Capability × Nat) :=
  -- IDs `0x00` to `0x0f` are reserved for the p2p capability, so the first one is `0x10`.
  messageOffsets length (sharedCapabilities ours theirs) BASE_PROTOCOL_LENGTH

end EthLib.Networking.Devp2p
