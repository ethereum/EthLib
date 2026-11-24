module

public import EthLib.Networking.Enr.V4
public import EthLib.Networking.Rlpx.Handshake

/-!
# `Networking.Discv4.Packet`

The packets of the Node Discovery Protocol v4.

The source is the section Wire Protocol of [`discv4.md`][discv4].

[discv4]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv4.md#wire-protocol

A packet is a header, then its data, an RLP list with one form for each packet type.

EIP-8 relaxes the reading of every packet.

EIP-868 adds the record packets, and the record sequence number of Ping and Pong.
-/

@[expose] public section

namespace EthLib.Networking.Discv4

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Serialization.Rlp

/-- The largest packet, in bytes. -/
def MAX_PACKET_SIZE : Nat := 1280

/-- The size of the hash, 32 bytes, and of the signature, 65 bytes, before the packet type. -/
def HEADER_SIZE : Nat := 97

/-- Every way a packet can be rejected. -/
inductive Discv4Error where
  /-- The packet has `size` bytes, more than 1280. -/
  | tooLarge (size : Nat)
  /-- The packet has `size` bytes, too few for the hash, the signature and the packet type. -/
  | tooShort (size : Nat)
  /-- The stored hash `stored` is not `computed`, the Keccak-256 hash of the bytes after it. -/
  | hashMismatch (stored computed : ByteArray)
  /-- No public key is recovered from the signature. -/
  | invalidSignature
  /-- Signing failed, which happens only for the private key zero. -/
  | secp256k1 (error : Secp256k1Error)
  /-- The packet type is not one of 1 to 6, so the packet is dropped. -/
  | unknownType (type : UInt8)
  /-- The data is not RLP of the shape that the packet type asks for. -/
  | rlp (error : RlpError)

/--
The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.
-/
def Discv4Error.code : Discv4Error → UInt32
  | .tooLarge _ => 1
  | .tooShort _ => 2
  | .hashMismatch .. => 3
  | .invalidSignature => 4
  | .secp256k1 _ => 5
  | .unknownType _ => 6
  | .rlp _ => 7

/-- A node's address: `[ip, udp-port, tcp-port]`.

`discv4.md` gives a port no width.

A UDP or TCP port is 16 bits, as [RFC 768] and [RFC 9293] fix it, so a larger port is refused.

[RFC 768]: https://www.rfc-editor.org/rfc/rfc768
[RFC 9293]: https://www.rfc-editor.org/rfc/rfc9293#section-3.1 -/
structure Endpoint where
  /-- The IP address: 4 bytes for IPv4, 16 for IPv6. -/
  ip : ByteArray
  /-- The UDP port of discovery. -/
  udpPort : UInt16
  /-- The TCP port of RLPx, or 0. -/
  tcpPort : UInt16
deriving DecidableEq

/-- An endpoint as the RLP list `[ip, udp-port, tcp-port]`. -/
def Endpoint.toItem (e : Endpoint) : Item :=
  -- Ping: `from = [sender-ip, sender-udp-port, sender-tcp-port]`.
  --
  -- And `to = [recipient-ip, recipient-udp-port, 0]`.
  --
  -- Not in the source: EthLib writes and reads any TCP port in `to`, so a nonzero one is kept.
  .list [Codec.toItem e.ip, Codec.toItem e.udpPort, Codec.toItem e.tcpPort]

/-- The endpoint in the RLP list `[ip, udp-port, tcp-port]`. -/
def Endpoint.ofItem (item : Item) : Except RlpError Endpoint := do
  -- Exactly the three items `[ip, udp-port, tcp-port]`, each port below 2^16.
  --
  -- EIP-8 ignores additional list elements in any packet, which may cover this nested list.
  --
  -- EthLib ignores them only in `packet-data`, as Wire Protocol writes, and refuses a fourth item.
  match ← item.fields 3 with
  | [ip, u, t] => return ⟨← Codec.ofItem ip, ← Codec.ofItem u, ← Codec.ofItem t⟩
  | items => throw (.wrongFieldCount 3 items.length)

instance : Codec Endpoint := ⟨Endpoint.toItem, Endpoint.ofItem⟩

/-- A node of a Neighbors packet: `[ip, udp-port, tcp-port, node-id]`. -/
structure Node where
  /-- The address of the node. -/
  endpoint : Endpoint
  /-- The node ID: the public key as the 64 bytes `x || y`. -/
  id : Vector UInt8 64
deriving DecidableEq

/-- A node as the RLP list `[ip, udp-port, tcp-port, node-id]`. -/
def Node.toItem (n : Node) : Item :=
  -- Neighbors: `nodes = [[ip, udp-port, tcp-port, node-id], ...]`, the endpoint flattened.
  .list [Codec.toItem n.endpoint.ip, Codec.toItem n.endpoint.udpPort,
    Codec.toItem n.endpoint.tcpPort, Codec.toItem n.id]

/-- The node in the RLP list `[ip, udp-port, tcp-port, node-id]`. -/
def Node.ofItem (item : Item) : Except RlpError Node := do
  -- Exactly the four items `[ip, udp-port, tcp-port, node-id]`, with a 64-byte `node-id`.
  match ← item.fields 4 with
  | [ip, u, t, id] =>
    return ⟨⟨← Codec.ofItem ip, ← Codec.ofItem u, ← Codec.ofItem t⟩, ← Codec.ofItem id⟩
  | items => throw (.wrongFieldCount 4 items.length)

instance : Codec Node := ⟨Node.toItem, Node.ofItem⟩

/-- A packet, by its type. -/
inductive Packet where
  /-- Ping (0x01): `[version, from, to, expiration, enr-seq]`, with an optional `enr-seq`.

  The version is 4, and the reader does not check it. -/
  | ping (version : Nat) (sender recipient : Endpoint) (expiration : Nat) (enrSeq : Option UInt64)
  /-- Pong (0x02): `[to, ping-hash, expiration, enr-seq]`, where `enr-seq` is optional. -/
  | pong (recipient : Endpoint) (pingHash : Vector UInt8 32) (expiration : Nat)
      (enrSeq : Option UInt64)
  /-- FindNode (0x03): `[target, expiration]`, with a 64-byte public key as the target. -/
  | findNode (target : Vector UInt8 64) (expiration : Nat)
  /-- Neighbors (0x04): `[nodes, expiration]`. -/
  | neighbors (nodes : List Node) (expiration : Nat)
  /-- ENRRequest (0x05) of EIP-868: `[expiration]`. -/
  | enrRequest (expiration : Nat)
  /-- ENRResponse (0x06) of EIP-868: `[request-hash, ENR]`, with the record as an RLP item. -/
  | enrResponse (requestHash : Vector UInt8 32) (record : Item)
deriving DecidableEq

namespace Packet

/-- The packet type. -/
def type : Packet → UInt8
  -- `packet-type` is a single byte, the number in the heading of each packet section.
  | ping .. => 0x01
  | pong .. => 0x02
  | findNode .. => 0x03
  | neighbors .. => 0x04
  -- EIP-868 adds the types 0x05 and 0x06.
  | enrRequest _ => 0x05
  | enrResponse .. => 0x06

/-- The item of an optional sequence number: one item when present, none when absent. -/
def enrSeqItems : Option UInt64 → List Item
  -- The `enr-seq` field is optional, so a packet without it ends at its expiration.
  | none => []
  | some n => [Codec.toItem n]

/-- The items of the packet data. -/
def fields : Packet → List Item
  -- Ping (0x01): `packet-data = [version, from, to, expiration, enr-seq ...]`.
  | ping v f t e s =>
    [Codec.toItem v, Codec.toItem f, Codec.toItem t, Codec.toItem e] ++ enrSeqItems s
  -- Pong (0x02): `packet-data = [to, ping-hash, expiration, enr-seq, ...]`.
  | pong t h e s => [Codec.toItem t, Codec.toItem h, Codec.toItem e] ++ enrSeqItems s
  -- FindNode (0x03): `packet-data = [target, expiration, ...]`.
  | findNode t e => [Codec.toItem t, Codec.toItem e]
  -- Neighbors (0x04): `packet-data = [nodes, expiration, ...]`.
  | neighbors ns e => [Codec.toItem ns, Codec.toItem e]
  -- ENRRequest (0x05): `packet-data = [expiration]`.
  | enrRequest e => [Codec.toItem e]
  -- ENRResponse (0x06): `packet-data = [request-hash, ENR]`.
  | enrResponse h r => [Codec.toItem h, r]

/-- The optional sequence number in the items after the fixed fields. -/
def readEnrSeq : List Item → Except RlpError (Option UInt64)
  -- The `enr-seq` field is optional.
  | [] => .ok none
  -- EIP-868: the first item after the fixed fields is `enr-seq`, the record sequence number.
  --
  -- EIP-778 makes that number a 64-bit unsigned integer, so it is below 2^64.
  --
  -- EIP-8 says that its Ping of version 555 and its Pong should be accepted.
  --
  -- In both, the first item after the fixed fields is a list.
  --
  -- EIP-868 later put the sequence number at that place.
  --
  -- EthLib reads that item as the sequence number, so it rejects both packets.
  --
  -- EIP-8: the reader ignores any additional list elements, here those after `enr-seq`.
  | item :: _ => some <$> Codec.ofItem item

/-- The packet of the type `type` whose data is the RLP list of the items `items`. -/
def ofItems (type : UInt8) (items : List Item) : Except Discv4Error Packet :=
  -- Each type reads its fixed fields first, in the order of its `packet-data`.
  --
  -- Wire Protocol and EIP-8: the reader ignores any additional elements in the `packet-data` list.
  --
  -- Ping (0x01): `[version, from, to, expiration, enr-seq ...]`.
  if type = 0x01 then
    match items with
    -- EIP-8: the reader does not validate the version, so any integer is kept.
    | v :: f :: t :: e :: rest => Except.mapError .rlp do
      return ping (← Codec.ofItem v) (← Codec.ofItem f) (← Codec.ofItem t) (← Codec.ofItem e)
        (← readEnrSeq rest)
    | _ => .error (.rlp (.wrongFieldCount 4 items.length))
  -- Pong (0x02): `[to, ping-hash, expiration, enr-seq, ...]`, with a 32-byte `ping-hash`.
  else if type = 0x02 then
    match items with
    | t :: h :: e :: rest => Except.mapError .rlp do
      return pong (← Codec.ofItem t) (← Codec.ofItem h) (← Codec.ofItem e) (← readEnrSeq rest)
    | _ => .error (.rlp (.wrongFieldCount 3 items.length))
  -- FindNode (0x03): `[target, expiration, ...]`, the `target` a 64-byte secp256k1 public key.
  --
  -- EthLib checks only its 64 bytes, not that it is a point of the curve.
  else if type = 0x03 then
    match items with
    | t :: e :: _ => Except.mapError .rlp do
      return findNode (← Codec.ofItem t) (← Codec.ofItem e)
    | _ => .error (.rlp (.wrongFieldCount 2 items.length))
  -- Neighbors (0x04): `[nodes, expiration, ...]`.
  else if type = 0x04 then
    match items with
    | ns :: e :: _ => Except.mapError .rlp do
      return neighbors (← Codec.ofItem ns) (← Codec.ofItem e)
    | _ => .error (.rlp (.wrongFieldCount 2 items.length))
  -- ENRRequest (0x05): `[expiration]`; by EIP-8, the items after it are ignored.
  else if type = 0x05 then
    match items with
    | e :: _ => Except.mapError .rlp do return enrRequest (← Codec.ofItem e)
    | _ => .error (.rlp (.wrongFieldCount 1 items.length))
  -- ENRResponse (0x06): `[request-hash, ENR]`, the record kept as an RLP item.
  else if type = 0x06 then
    match items with
    | h :: r :: _ => Except.mapError .rlp do return enrResponse (← Codec.ofItem h) r
    | _ => .error (.rlp (.wrongFieldCount 2 items.length))
  -- EIP-8: discovery packets with unknown packet type should be discarded silently.
  else .error (.unknownType type)

end Packet

/-- A packet that was read, with what the reader learns from its header. -/
structure Received where
  /-- The packet. -/
  packet : Packet
  /-- The sender's public key, recovered from the signature. -/
  sender : Point
  /-- The hash at the start of the packet, which Pong and ENRResponse echo. -/
  hash : Vector UInt8 32

/-- The Keccak-256 hash of a list of bytes. -/
def keccak (bytes : List UInt8) : Vector UInt8 32 :=
  Hash.Keccak.keccak256 ⟨bytes.toArray⟩

/--
The packet that the node with the private key `key` sends.

It fails when the packet would exceed 1280 bytes.
-/
def encode (key : Fn) (p : Packet) : Except Discv4Error ByteArray := do
  -- `packet-data` is the RLP list of the fields of the packet type.
  let data ← (Serialization.Rlp.encode (.list p.fields)).mapError .rlp
  -- The signed bytes are `packet-type || packet-data`.
  let signed := p.type :: data.data.toList
  -- `signature = sign(packet-type || packet-data)`, by the node's identity key.
  --
  -- The source writes only sign; EthLib signs `keccak256(packet-type || packet-data)`.
  --
  -- That is the hash from which the signed packets of EIP-8 recover their key.
  --
  -- Not in the source: the nonce is that of RFC 6979, and `s` is low, as EIP-2 asks.
  let sig ← (Ecdsa.sign key (keccak signed)).mapError .secp256k1
  -- The signature is 65 bytes, `r || s || v`, with the recovery id `v`.
  let body := (Rlpx.signatureBytes sig).toList ++ signed
  -- `packet = hash || signature || packet-type || packet-data`.
  --
  -- And `hash = keccak256(signature || packet-type || packet-data)`.
  let packet := (keccak body).toList ++ body
  -- The maximum size of any packet is 1280 bytes.
  if MAX_PACKET_SIZE < packet.length then throw (.tooLarge packet.length)
  return ⟨packet.toArray⟩

/-- The signature in a packet: its bytes 32 to 96. -/
def signatureOf (bytes : List UInt8) : Vector UInt8 65 :=
  Vector.ofFn fun i => bytes.getD (32 + i) 0

/--
The packet of the type `type` with the data `data`, signed by `sig`, under the hash `hash`.
-/
def readBody (hash : Vector UInt8 32) (sig : Vector UInt8 65) (type : UInt8)
    (data : List UInt8) : Except Discv4Error Received := do
  -- The sender is the key that `r || s || v` recovers from `keccak256(packet-type || data)`.
  --
  -- The signed bytes run to the end of the packet, with any data after the RLP list.
  let sender ← (Rlpx.recoverSigner (keccak (type :: data)) sig).mapError
    fun _ => .invalidSignature
  -- EIP-8: the reader ignores any data after the first RLP value in any packet.
  let (item, _) ← (decodeItem ⟨data.toArray⟩ 0 data.length (by simp [ByteArray.size])).mapError .rlp
  -- That value is an RLP list, whose items take the form of the packet type.
  let p ← Packet.ofItems type (← item.toItems.mapError .rlp)
  return ⟨p, sender, hash⟩

/--
The packet in the bytes `packet`, with its sender and its hash.

It fails on more than 1280 bytes, on a wrong hash and on a signature that recovers no key.

It does not check the expiration, which needs the reader's clock.
-/
def decode (packet : ByteArray) : Except Discv4Error Received :=
  let bytes := packet.data.toList
  -- The maximum size of any packet is 1280 bytes.
  if MAX_PACKET_SIZE < bytes.length then .error (.tooLarge bytes.length)
  else
    -- `packet-header = hash || signature || packet-type`: 32 bytes, 65 bytes, then one byte.
    match bytes.drop HEADER_SIZE with
    | [] => .error (.tooShort bytes.length)
    | type :: data =>
      -- `hash = keccak256(signature || packet-type || packet-data)`, over every byte after it.
      if bytes.take 32 = (keccak (bytes.drop 32)).toList then
        readBody (keccak (bytes.drop 32)) (signatureOf bytes) type data
      else .error (.hashMismatch ⟨(bytes.take 32).toArray⟩ ⟨(keccak (bytes.drop 32)).toArray⟩)

/-- Whether the record of an ENRResponse is signed by the sender of the packet. -/
def recordSignedBy (sender : Point) (record : Item) : Bool :=
  -- The recipient should verify that the record is signed by the key that signed the response.
  --
  -- The record is read back from its RLP bytes, in the form of EIP-778.
  match Serialization.Rlp.encode record with
  | .error _ => false
  | .ok bytes =>
    match Enr.decode bytes with
    | .error _ => false
    | .ok r =>
      -- Node Records: all records must use the identity scheme v4, with a secp256k1 key.
      match r.publicKeyV4 with
      | .error _ => false
      -- The record verifies under the scheme v4, and its key signed the packet.
      | .ok key => Enr.verifyV4 r && decide (key = sender)

end EthLib.Networking.Discv4
