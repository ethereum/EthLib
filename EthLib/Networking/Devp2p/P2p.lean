module

public import EthLib.Networking.Rlpx.Handshake
public import EthLib.Networking.Snappy.Compress

/-!
# `Networking.Devp2p.P2p`

The messages Hello, Disconnect, Ping and Pong of the "p2p" capability, from [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#capability-messaging

The data of a frame is the message ID as an RLP integer, then the message as an RLP list.

From version 5 of the capability, every message after Hello is compressed with Snappy (EIP-706).

The capabilities that both peers share take the message IDs from `0x10` on.
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
  /-- The message ID did not name a message of the "p2p" capability. -/
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

/-- The version of the "p2p" capability in `rlpx.md`. -/
def PROTOCOL_VERSION : Nat := 5

/-- The first version that compresses messages with Snappy, from EIP-706. -/
def SNAPPY_VERSION : Nat := 5

/-- The largest decompressed message that a peer accepts, 16 MiB, from "Message Encoding". -/
def MAX_MESSAGE_SIZE : Nat := 16 * 1024 * 1024

/-- The first message ID after the IDs `0x00` to `0x0f` of the "p2p" capability. -/
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
  toItem c := .list [.bytes c.name, Codec.toItem c.version]
  ofItem item := do
    match ← item.fields 2 with
    | [n, v] => return ⟨← Codec.ofItem n, ← Codec.ofItem v⟩
    | items => throw (RlpError.wrongFieldCount 2 items.length)

/-- Hello: `[protocolVersion, clientId, capabilities, listenPort, nodeKey, ...]`. -/
structure Hello where
  /-- The version of the "p2p" capability. -/
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

A reader ignores any further items, as "Hello (0x00)" asks.
-/
instance : Codec Hello where
  toItem h := .list [Codec.toItem h.protocolVersion, .bytes h.clientId,
    Codec.toItem h.capabilities, Codec.toItem h.listenPort, Codec.toItem h.nodeId]
  ofItem item := do
    match ← Rlpx.leadingFields 5 item with
    | [v, c, caps, p, n] =>
      return ⟨← Codec.ofItem v, ← Codec.ofItem c, ← Codec.ofItem caps, ← Codec.ofItem p,
        ← Codec.ofItem n⟩
    | items => throw (RlpError.wrongFieldCount 5 items.length)

/-- A message of the "p2p" capability. -/
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
  | hello _ => 0x00
  | disconnect _ => 0x01
  | ping => 0x02
  | pong => 0x03

/-- The message as an RLP list: Disconnect is `[reason]`, or `[]` without a reason. -/
def toItem : Message → Item
  | hello h => Codec.toItem h
  | disconnect none => .list []
  | disconnect (some r) => .list [Codec.toItem r]
  | ping => .list []
  | pong => .list []

/-- The message with the ID `id` that the RLP list `item` holds. -/
def ofItem (id : Nat) (item : Item) : Except P2pError Message :=
  match id with
  | 0x00 => (hello <$> Codec.ofItem item).mapError .rlp
  | 0x01 =>
    match item with
    | .list [] => .ok (disconnect none)
    | .list [r] => ((fun n => disconnect (some n)) <$> Codec.ofItem r).mapError .rlp
    | .list items => .error (.rlp (.wrongFieldCount 1 items.length))
    | .bytes _ => .error (.rlp .bytesAsList)
  | 0x02 => if item = .list [] then .ok ping else .error (.rlp (.wrongFieldCount 0 1))
  | 0x03 => if item = .list [] then .ok pong else .error (.rlp (.wrongFieldCount 0 1))
  | id => .error (.unknownId id)

end Message

/--
The frame data of a message: `msg-id || msg-data`.

With `snappy`, every message but Hello is compressed, as "Message Encoding" asks from version 5.
-/
def encodeMessage (snappy : Bool) (m : Message) : Except P2pError ByteArray := do
  let id ← (encode (Item.scalar m.id)).mapError .rlp
  let data ← (encode m.toItem).mapError .rlp
  return id ++ if snappy && m.id != 0x00 then Snappy.compress data else data

/--
The message in the frame data `msg-id || msg-data`.

A compressed message is rejected before decompression when its declared size exceeds 16 MiB.
-/
def decodeMessage (snappy : Bool) (frameData : ByteArray) : Except P2pError Message := do
  -- The ID is one RLP item at the start, and the message is the bytes after it.
  let (idItem, next) ← ((decodeItem frameData 0 frameData.size).map fun r => (r.1, r.2.1)).mapError
    .rlp
  let id ← idItem.toScalar.mapError .rlp
  let rest := frameData.extract next frameData.size
  let data ← if snappy && id != 0x00 then do
      let (size, _) ← (Snappy.readPreamble rest.data.toList).mapError .snappy
      if MAX_MESSAGE_SIZE < size then throw (.tooLarge size)
      (Snappy.decompress rest).mapError .snappy
    else pure rest
  Message.ofItem id (← (decode data).mapError .rlp)

/-- Whether both peers use Snappy: both Hello messages carry version 5 or more, by EIP-706. -/
def snappyEnabled (ours theirs : Nat) : Bool :=
  SNAPPY_VERSION ≤ ours && SNAPPY_VERSION ≤ theirs

/-! ## Message IDs of the shared capabilities -/

/-- Whether the name of `a` comes before the name of `b`, byte by byte. -/
def Capability.nameLe (a b : Capability) : Bool :=
  a.name.data.toList ≤ b.name.data.toList

/--
The capabilities that both peers support, from "Message ID-based Multiplexing".

A capability is shared when both list the same name and version.

Of the shared versions of one name, the highest wins.

The result is in alphabetic order of the names.
-/
def sharedCapabilities (ours theirs : List Capability) : List Capability :=
  let shared := (ours.filter (· ∈ theirs)).eraseDups
  let best := shared.filter fun c => shared.all fun d => d.name ≠ c.name || d.version ≤ c.version
  best.mergeSort Capability.nameLe

/--
The first message ID of each capability, given how many IDs each one needs.

The IDs start at `0x10`, and each capability takes the next block.
-/
def messageOffsets (length : Capability → Nat) : List Capability → Nat → List (Capability × Nat)
  | [], _ => []
  | c :: cs, offset => (c, offset) :: messageOffsets length cs (offset + length c)

/-- The message ID offsets of the shared capabilities, from `0x10` on. -/
def negotiate (length : Capability → Nat) (ours theirs : List Capability) :
    List (Capability × Nat) :=
  messageOffsets length (sharedCapabilities ours theirs) BASE_PROTOCOL_LENGTH

end EthLib.Networking.Devp2p
