module

public import EthLib.Networking.Encoding.Uvarint

/-!
# multistream-select 1.0

Two peers agree on a protocol by name: one proposes it, and the other echoes it or answers `na`.

Both peers first send the name of multistream-select itself.

Each message is a varint length, the bytes of the message, then a newline.

The length is read as a multiformats unsigned varint, the varint of libp2p.

The length counts the newline.

A protocol name is sent as its UTF-8 bytes, but the framing reads any bytes.

The optional listing of protocols is not modelled.

The source is [multistream-select, "Protocol"][mss].

[mss]: https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Multistream

open EthLib.Networking.Encoding

/-- The name of multistream-select 1.0, which both peers send first. -/
def protocolId : ByteArray := "/multistream/1.0.0".toUTF8

/-- The answer to a protocol that the peer does not support: "not available". -/
def notAvailable : ByteArray := "na".toUTF8

/-- The newline byte that ends every message. -/
def newline : UInt8 := 0x0a

/-- Why the message at the start of an input was refused. -/
inductive MultistreamError where
  /-- The length is not an unsigned varint. -/
  | length (error : Uvarint.UvarintError)
  /-- The length is zero, so it leaves no room for the newline. -/
  | empty
  /-- The input ends before the bytes that the length counts. -/
  | truncated (length available : Nat)
  /-- The last byte that the length counts is not a newline. -/
  | missingNewline
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def MultistreamError.code : MultistreamError → UInt32
  | .length _ => 1
  | .empty => 2
  | .truncated _ _ => 3
  | .missingNewline => 4

/-- The bytes of one message: its length, its bytes, then the newline.

The message must be shorter than `2^63 - 1` bytes, so that its length fits an unsigned varint. -/
def encode (message : ByteArray) : List UInt8 :=
  Uvarint.encode (message.size + 1) ++ message.data.toList ++ [newline]

/-- The message at the start of the input, without its newline, and the bytes after it. -/
def decode (bytes : List UInt8) : Except MultistreamError (ByteArray × List UInt8) := do
  let (length, rest) ← (Uvarint.decode bytes).mapError .length
  if length = 0 then throw .empty
  let body := rest.take length
  if body.length < length then throw (.truncated length body.length)
  if body[length - 1]? ≠ some newline then throw .missingNewline
  return (⟨(body.take (length - 1)).toArray⟩, rest.drop length)

/-- The answer to a proposed protocol: the protocol itself if supported, else `na`. -/
def respond (supported : List ByteArray) (proposal : ByteArray) : ByteArray :=
  if proposal.data ∈ supported.map (·.data) then proposal else notAvailable

end EthLib.Networking.Libp2p.Multistream
