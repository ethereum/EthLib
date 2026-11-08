module

public import EthLib.Networking.Enr.V4
public import EthLib.Networking.Rlpx.Handshake

/-!
# `Networking.Discv4.Packet`

The packets of the Node Discovery Protocol v4, from "Wire Protocol" of [`discv4.md`][discv4].

[discv4]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv4.md#wire-protocol

A packet is `hash || signature || packet-type || packet-data`, at most 1280 bytes.

The hash is the Keccak-256 hash of the bytes after it.

The signature is `r || s || v`, with the recovery id `v`.

It signs the Keccak-256 hash of `packet-type || packet-data`.

The spec writes only `sign`, and the packets of EIP-8 recover their key from that hash.

The data is an RLP list, one form for each packet type.

EIP-8 asks the reader to ignore the Ping version, extra list items and the bytes after the list.

EIP-868 adds the record packets, and the record sequence number of Ping and Pong.

EIP-8 says that its Ping of version 555 and its Pong should be accepted.

In both, the first item after the fixed fields is a list.

EIP-868 later put the sequence number at that place.

EthLib reads that item as the sequence number, so it rejects both packets.
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
  /-- The hash is not the Keccak-256 hash of the bytes after it. -/
  | hashMismatch
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
  | .hashMismatch => 3
  | .invalidSignature => 4
  | .secp256k1 _ => 5
  | .unknownType _ => 6
  | .rlp _ => 7

/-- A node's address: `[ip, udp-port, tcp-port]`. -/
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
  .list [Codec.toItem e.ip, Codec.toItem e.udpPort, Codec.toItem e.tcpPort]

/-- The endpoint in the RLP list `[ip, udp-port, tcp-port]`. -/
def Endpoint.ofItem (item : Item) : Except RlpError Endpoint := do
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
  .list [Codec.toItem n.endpoint.ip, Codec.toItem n.endpoint.udpPort,
    Codec.toItem n.endpoint.tcpPort, Codec.toItem n.id]

/-- The node in the RLP list `[ip, udp-port, tcp-port, node-id]`. -/
def Node.ofItem (item : Item) : Except RlpError Node := do
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
  | ping .. => 0x01
  | pong .. => 0x02
  | findNode .. => 0x03
  | neighbors .. => 0x04
  | enrRequest _ => 0x05
  | enrResponse .. => 0x06

/-- The item of an optional sequence number: one item when present, none when absent. -/
def enrSeqItems : Option UInt64 → List Item
  | none => []
  | some n => [Codec.toItem n]

/-- The items of the packet data. -/
def fields : Packet → List Item
  | ping v f t e s =>
    [Codec.toItem v, Codec.toItem f, Codec.toItem t, Codec.toItem e] ++ enrSeqItems s
  | pong t h e s => [Codec.toItem t, Codec.toItem h, Codec.toItem e] ++ enrSeqItems s
  | findNode t e => [Codec.toItem t, Codec.toItem e]
  | neighbors ns e => [Codec.toItem ns, Codec.toItem e]
  | enrRequest e => [Codec.toItem e]
  | enrResponse h r => [Codec.toItem h, r]

/--
The optional sequence number in the items after the fixed fields.

EIP-868 makes the first of them the sequence number, so it must be an integer below `2^64`.

The items after it are ignored, as EIP-8 asks.
-/
def readEnrSeq : List Item → Except RlpError (Option UInt64)
  | [] => .ok none
  | item :: _ => some <$> Codec.ofItem item

/--
The packet of the type `type` whose data is the RLP list of the items `items`.

The fixed fields come first, and the reader ignores the items after them.
-/
def ofItems (type : UInt8) (items : List Item) : Except Discv4Error Packet :=
  if type = 0x01 then
    match items with
    | v :: f :: t :: e :: rest => Except.mapError .rlp do
      return ping (← Codec.ofItem v) (← Codec.ofItem f) (← Codec.ofItem t) (← Codec.ofItem e)
        (← readEnrSeq rest)
    | _ => .error (.rlp (.wrongFieldCount 4 items.length))
  else if type = 0x02 then
    match items with
    | t :: h :: e :: rest => Except.mapError .rlp do
      return pong (← Codec.ofItem t) (← Codec.ofItem h) (← Codec.ofItem e) (← readEnrSeq rest)
    | _ => .error (.rlp (.wrongFieldCount 3 items.length))
  else if type = 0x03 then
    match items with
    | t :: e :: _ => Except.mapError .rlp do
      return findNode (← Codec.ofItem t) (← Codec.ofItem e)
    | _ => .error (.rlp (.wrongFieldCount 2 items.length))
  else if type = 0x04 then
    match items with
    | ns :: e :: _ => Except.mapError .rlp do
      return neighbors (← Codec.ofItem ns) (← Codec.ofItem e)
    | _ => .error (.rlp (.wrongFieldCount 2 items.length))
  else if type = 0x05 then
    match items with
    | e :: _ => Except.mapError .rlp do return enrRequest (← Codec.ofItem e)
    | _ => .error (.rlp (.wrongFieldCount 1 items.length))
  else if type = 0x06 then
    match items with
    | h :: r :: _ => Except.mapError .rlp do return enrResponse (← Codec.ofItem h) r
    | _ => .error (.rlp (.wrongFieldCount 2 items.length))
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

The signature is deterministic, by RFC 6979, with the low `s` of EIP-2.

It fails when the packet would exceed 1280 bytes.
-/
def encode (key : Fn) (p : Packet) : Except Discv4Error ByteArray := do
  let data ← (Serialization.Rlp.encode (.list p.fields)).mapError .rlp
  let signed := p.type :: data.data.toList
  let sig ← (Ecdsa.sign key (keccak signed)).mapError .secp256k1
  let body := (Rlpx.signatureBytes sig).toList ++ signed
  let packet := (keccak body).toList ++ body
  if MAX_PACKET_SIZE < packet.length then throw (.tooLarge packet.length)
  return ⟨packet.toArray⟩

/-- The signature in a packet: its bytes 32 to 96. -/
def signatureOf (bytes : List UInt8) : Vector UInt8 65 :=
  Vector.ofFn fun i => bytes.getD (32 + i) 0

/--
The packet of the type `type` with the data `data`, signed by `sig`, under the hash `hash`.

It reads one RLP item from the data and ignores the bytes after it, as EIP-8 asks.
-/
def readBody (hash : Vector UInt8 32) (sig : Vector UInt8 65) (type : UInt8)
    (data : List UInt8) : Except Discv4Error Received := do
  let sender ← (Rlpx.recoverSigner (keccak (type :: data)) sig).mapError
    fun _ => .invalidSignature
  let (item, _) ← (decodeItem data).mapError .rlp
  let p ← Packet.ofItems type (← item.toItems.mapError .rlp)
  return ⟨p, sender, hash⟩

/--
The packet in the bytes `packet`, with its sender and its hash.

It fails on more than 1280 bytes, on a wrong hash and on a signature that recovers no key.

It does not check the expiration, which needs the reader's clock.
-/
def decode (packet : ByteArray) : Except Discv4Error Received :=
  let bytes := packet.data.toList
  if MAX_PACKET_SIZE < bytes.length then .error (.tooLarge bytes.length)
  else
    match bytes.drop HEADER_SIZE with
    | [] => .error (.tooShort bytes.length)
    | type :: data =>
      if bytes.take 32 = (keccak (bytes.drop 32)).toList then
        readBody (keccak (bytes.drop 32)) (signatureOf bytes) type data
      else .error .hashMismatch

/--
Whether the record of an ENRResponse is signed by the sender of the packet.

The record must be a valid "v4" record, and its public key must be the sender's key.
-/
def recordSignedBy (sender : Point) (record : Item) : Bool :=
  match Serialization.Rlp.encode record with
  | .error _ => false
  | .ok bytes =>
    match Enr.decode bytes with
    | .error _ => false
    | .ok r =>
      match r.publicKeyV4 with
      | .error _ => false
      | .ok key => Enr.verifyV4 r && decide (key = sender)

end EthLib.Networking.Discv4
