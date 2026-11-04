module

public import EthLib.Networking.Discv4.Packet
public import EthLib.Networking.Exports.Rlpx

/-!
# `Exports.Discv4`

C-ABI exports for the packets of discv4, callable from the Python C extension.

A packet's content crosses the boundary as `packet-type || packet-data`.

Its data holds only the fields that the reader keeps.

A read packet comes back as its hash, the sender's key as the 64 bytes `x || y`, then its content.

A private key is 32 big-endian bytes, and a public key is either SEC 1 encoding.

An input that the export rejects before the packet rules has code 0.
-/

public section

namespace EthLib.Networking.Discv4.Exports

open EthLib.Exports (Result)
open EthLib.Serialization.Rlp

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : Discv4Error → String
  | .tooLarge size => s!"packet has {size} bytes, more than {MAX_PACKET_SIZE}"
  | .tooShort size => s!"packet has {size} bytes, too few for a header and a packet type"
  | .hashMismatch => "packet hash does not match"
  | .invalidSignature => "no public key is recovered from the signature"
  | .secp256k1 e => s!"signing failed: {e.message}"
  | .unknownType type => s!"packet type {type} is unknown"
  | .rlp _ => "packet data is not RLP of the expected shape"

/-- Run a fallible computation, with its error as a code and a message. -/
def runDiscv4 {α : Type} (act : Except Discv4Error α) : Result α :=
  act.mapError fun e => (e.code, message e)

/-- The content `packet-type || packet-data` of a packet, with only the fields it keeps. -/
def content (p : Packet) : Result ByteArray := do
  let data ← (Serialization.Rlp.encode (.list p.fields)).mapError fun _ => (0, "too large")
  return ⟨#[p.type]⟩ ++ data

/-- The packet with the content `packet-type || packet-data`. -/
def readContent (plain : ByteArray) : Result Packet :=
  match plain.data.toList with
  | [] => throw (0, "content is empty")
  | type :: data =>
    match Serialization.Rlp.decode ⟨data.toArray⟩ with
    | .error _ => throw (0, "packet data is not one RLP item")
    | .ok (.bytes _) => throw (0, "packet data is not an RLP list")
    | .ok (.list items) => runDiscv4 (Packet.ofItems type items)

/-- The hash, the sender's key and the content of the packet in the bytes `packet`. -/
@[export eth_discv4_decode]
def decodeExport (packet : ByteArray) : Result ByteArray := do
  let r ← runDiscv4 (decode packet)
  let sender := Rlpx.encodePublicKey r.sender
  return ⟨r.hash.toArray⟩ ++ ⟨sender.toArray⟩ ++ (← content r.packet)

/-- The packet with the content `plain`, signed with the private key `key`. -/
@[export eth_discv4_encode]
def encodeExport (key plain : ByteArray) : Result ByteArray := do
  let k ← Rlpx.Exports.readPrivateKey key
  runDiscv4 (encode k (← readContent plain))

/-- Whether the RLP record `record` of an ENRResponse is signed by the public key `sender`. -/
@[export eth_discv4_record_signed_by]
def recordSignedByExport (sender record : ByteArray) : Result Bool := do
  let q ← Rlpx.Exports.readPublicKey sender
  match Serialization.Rlp.decode record with
  | .error _ => throw (0, "record is not one RLP item")
  | .ok item => return recordSignedBy q item

end EthLib.Networking.Discv4.Exports
