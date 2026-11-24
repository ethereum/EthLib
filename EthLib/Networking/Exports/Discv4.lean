module

public import EthLib.Base.Exports.PyValue
public import EthLib.Base.Hex
public import EthLib.Networking.Discv4.Exchange
public import EthLib.Networking.Discv4.Packet
public import EthLib.Networking.Exports.Rlpx

/-!
# `Exports.Discv4`

C-ABI exports for the packets of discv4, callable from the Python C extension.

A packet's content crosses the boundary as `packet-type || packet-data`.

An input that the export rejects before the packet rules has code 0.
-/

public section

namespace EthLib.Networking.Discv4.Exports

open EthLib.Exports (ExportError Result PyValue UnreadArgument pyExport rejectArgument toResult)
open EthLib.Serialization.Rlp
open EthLib.Base (hexString)

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : Discv4Error → String
  | .tooLarge size => s!"packet has {size} bytes, more than {MAX_PACKET_SIZE}"
  | .tooShort size => s!"packet has {size} bytes, too few for a header and a packet type"
  | .hashMismatch stored computed =>
    s!"packet hash {hexString stored.data.toList} is not {hexString computed.data.toList}"
  | .invalidSignature => "no public key is recovered from the signature"
  | .secp256k1 e => s!"signing failed: {e.message}"
  | .unknownType type => s!"packet type {type} is unknown"
  | .rlp _ => "packet data is not RLP of the expected shape"

/-- A rejection reaches Python with its code, and its message names the fault. -/
instance : ExportError Discv4Error where
  code := Discv4Error.code
  message := message

/-- The content `packet-type || packet-data` of a packet, with only the fields it keeps.

Its data holds only the fields that the reader keeps. -/
def content (p : Packet) : Result ByteArray := do
  let data ← toResult none
    ((Serialization.Rlp.encode (.list p.fields)).mapError fun _ => UnreadArgument.mk "too large")
  return ⟨#[p.type]⟩ ++ data

/-- The packet with the content `packet-type || packet-data`. -/
def readContent (plain : ByteArray) : Result Packet :=
  match plain.data.toList with
  | [] => rejectArgument none "content is empty"
  | type :: data =>
    match Serialization.Rlp.decode ⟨data.toArray⟩ with
    | .error _ => rejectArgument none "packet data is not one RLP item"
    | .ok (.bytes _) => rejectArgument none "packet data is not an RLP list"
    | .ok (.list items) => toResult none (Packet.ofItems type items)

/-- The hash, the sender's key and the content of the packet in the bytes `packet`. -/
@[export eth_discv4_decode]
def decodeExport (packet : ByteArray) : Result ByteArray := do
  let r ← toResult none (decode packet)
  -- The sender's key crosses as the 64 bytes `x || y`.
  let sender := Rlpx.encodePublicKey r.sender
  -- A read packet comes back as its hash, the sender's key, then its content.
  return ⟨r.hash.toArray⟩ ++ ⟨sender.toArray⟩ ++ (← content r.packet)

/-- The packet with the content `plain`, signed with the private key `key`. -/
@[export eth_discv4_encode]
def encodeExport (key plain : ByteArray) : Result ByteArray := do
  -- A private key is 32 big-endian bytes.
  let k ← Rlpx.Exports.readPrivateKey key
  toResult none (encode k (← readContent plain))

/-- Whether the RLP record `record` of an ENRResponse is signed by the public key `sender`. -/
@[export eth_discv4_record_signed_by]
def recordSignedByExport (sender record : ByteArray) : Result Bool := do
  -- A public key is either SEC 1 encoding.
  let q ← Rlpx.Exports.readPublicKey sender
  match Serialization.Rlp.decode record with
  | .error _ => rejectArgument none "record is not one RLP item"
  | .ok item => return recordSignedBy q item

/-- The arguments of a received packet.

They are the time, the sender's address, what the node knows of it, and the packet.

Then comes what the node puts into its answers. -/
abbrev ReceiveArgs := Nat × ByteArray × UInt16 × Option (Vector UInt8 32) × Option Nat ×
  ByteArray × Nat × Option UInt64 × ByteArray × ByteArray

/-- What the node knows of the sender after a packet, and the contents of the packets it sends. -/
def receiveOf (args : ReceiveArgs) :
    Result ((Option (Vector UInt8 32) × Option Nat) × List ByteArray) := do
  -- The arguments are the time, the sender's IP and UDP port, and what the node knows of it.
  --
  -- That is the hash of the node's last Ping to it, and the time of the last Pong that carried it.
  --
  -- Then come the packet and the expiration of the answers.
  --
  -- Last come the node's record sequence number, its record and the nodes it gives for any target.
  --
  -- The record and the list of nodes are RLP bytes.
  let (now, ip, port, lastPing, lastPong, packet, expiration, enrSeq, record, nodes) := args
  let received ← toResult none (decode packet)
  let some record := (Serialization.Rlp.decode record).toOption
    | rejectArgument none "record is not one RLP item"
  let some item := (Serialization.Rlp.decode nodes).toOption
    | rejectArgument none "nodes are not one RLP item"
  let some nodes := (Codec.ofItem item : Except RlpError (List Node)).toOption
    | rejectArgument none "nodes are not a list of [ip, udp-port, tcp-port, node-id]"
  let node : Local := ⟨expiration, enrSeq, fun _ => nodes, record⟩
  let address : Address := ⟨ip, port⟩
  let (state, replies) := receive node now (fun _ => ⟨lastPing, lastPong⟩) address received
  return (((state address).lastPing, (state address).lastPong), ← replies.mapM content)

/-- What a node knows of the sender of a packet after it receives it, and what it sends back.

The arguments are the time, the sender's IP and UDP port, and what the node knows of it.

That is the hash of the node's last Ping to it, and the time of the last Pong that carried it.

Then come the packet and the expiration of the answers.

Last come the node's record sequence number, its record and the nodes it gives for any target.

The record and the list of nodes are RLP bytes.

The result is the new hash and time, and the content of each packet that the node sends. -/
@[export eth_discv4_receive]
def receiveExport (args : PyValue) : Result PyValue :=
  pyExport receiveOf args

/-- Whether an ENRResponse packet answers an ENRRequest packet that the node sent. -/
def acceptEnrResponseOf (args : ByteArray × ByteArray) : Result Bool := do
  let (request, response) := args
  return acceptEnrResponse (← toResult none (decode request)) (← toResult none (decode response))

/-- Whether an ENRResponse packet answers an ENRRequest packet that the node sent.

It must hold the hash of the request packet, and a record signed by the key of the response. -/
@[export eth_discv4_accept_enr_response]
def acceptEnrResponseExport (args : PyValue) : Result PyValue :=
  pyExport acceptEnrResponseOf args

end EthLib.Networking.Discv4.Exports
