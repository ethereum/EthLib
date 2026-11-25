module

public import EthLib.Networking.Encoding.ByteReader
public import EthLib.Base.ByteOrder

/-!
# yamux frames

yamux carries many streams over one connection, with flow control for each stream.

The source is the section Framing of [yamux][yamux].

[yamux]: https://github.com/libp2p/specs/blob/1a084b699d9d424ca7027edf350cf4184cd6f5bd/yamux/README.md#framing
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Yamux

/-- The name of yamux in multistream-select. -/
def protocolId : ByteArray :=
  -- Specification: the protocol string of yamux for multistream-select.
  "/yamux/1.0.0".toUTF8

/-- The size of a header in bytes. -/
def headerSize : Nat :=
  -- Framing: 8 + 8 + 16 + 32 + 32 bits, so each header has a 12 byte overhead.
  12

/-- The window of a new stream in bytes, from the section Flow Control. -/
def initialWindow : Nat :=
  -- Flow Control: each stream starts with a window of 256KiB, that is `2^18` bytes.
  262144

/-- The flag that starts a stream, from the section Flag Field. -/
def syn : UInt16 := 0x1

/-- The flag that acknowledges the start of a stream. -/
def ack : UInt16 := 0x2

/-- The flag that closes a stream for writing. -/
def fin : UInt16 := 0x4

/-- The flag that resets a stream. -/
def rst : UInt16 := 0x8

/-- The go-away code of a normal termination, from the section Session termination. -/
def goAwayNormal : UInt32 := 0

/-- The go-away code of a protocol error. -/
def goAwayProtocolError : UInt32 := 1

/-- The go-away code of an internal error. -/
def goAwayInternalError : UInt32 := 2

/-- The type of a frame, which says what its length means. -/
inductive Kind where
  /-- Data: the length counts the bytes after the header. -/
  | data
  /-- A window update: the length is added to the window of the stream. -/
  | windowUpdate
  /-- A ping: the length is an opaque value that the reply echoes. -/
  | ping
  /-- A go-away: the length is the code of the reason. -/
  | goAway
  deriving Repr, DecidableEq

/-- The byte of a type. -/
def Kind.toUInt8 : Kind → UInt8
  -- Type Field: 0x0 Data, 0x1 Window Update, 0x2 Ping, 0x3 Go Away.
  | .data => 0
  | .windowUpdate => 1
  | .ping => 2
  | .goAway => 3

/-- The type of a byte, if it names one. -/
def Kind.ofUInt8? : UInt8 → Option Kind
  | 0 => some .data
  | 1 => some .windowUpdate
  | 2 => some .ping
  | 3 => some .goAway
  -- The source supports no other type.
  | _ => none

/-- One frame: the header fields after the version, and the data of a data frame. -/
structure Frame where
  /-- The type. -/
  kind : Kind
  /-- The flags, of which the source defines the four low bits. -/
  flags : UInt16
  /-- The stream; 0 names the session. -/
  streamId : UInt32
  /-- The length of the data, the window delta, the ping value or the go-away code. -/
  length : UInt32
  /-- The data: as many bytes as the length for a data frame, else none. -/
  data : ByteArray

/-- The bytes that follow the header: the length of a data frame, else none. -/
def Frame.dataSize (frame : Frame) : Nat :=
  -- Length Field: for Data, the length of bytes following the header; other types carry no data.
  if frame.kind = .data then frame.length.toNat else 0

/-- A frame whose data has the size that its type and its length give.

It checks only that size: the stream ID, the flags and a go-away code are not checked. -/
def Frame.Valid (frame : Frame) : Prop :=
  frame.data.size = frame.dataSize

instance (frame : Frame) : Decidable frame.Valid := by
  unfold Frame.Valid; infer_instance

/-- Why the frame at the start of an input was refused. -/
inductive YamuxError where
  /-- The input ends within the header. -/
  | shortHeader (available : Nat)
  /-- The version is not 0. -/
  | version (version : UInt8)
  /-- The type is not 0 to 3. -/
  | unknownKind (kind : UInt8)
  /-- The input ends before the data of a data frame. -/
  | truncated (length available : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def YamuxError.code : YamuxError → UInt32
  | .shortHeader _ => 1
  | .version _ => 2
  | .unknownKind _ => 3
  | .truncated _ _ => 4

/-- The bytes of a frame.

The frame must be valid; the bytes of any other frame are not specified. -/
def encode (frame : Frame) : List UInt8 :=
  -- Framing: Version (8 bits), Type (8 bits), Flags (16 bits), StreamID and Length (32 bits each).
  --
  -- All fields are big endian, and the version is always 0, the initial version.
  --
  -- The data of a data frame follows the header.
  [0, frame.kind.toUInt8] ++ (Base.ByteOrder.toBE 2 frame.flags.toNat).toList ++
    (Base.ByteOrder.toBE 4 frame.streamId.toNat).toList
      ++ (Base.ByteOrder.toBE 4 frame.length.toNat).toList ++
    frame.data.data.toList

/-- The frame at the start of the input, and the bytes after it. -/
def decode (bytes : List UInt8) : Except YamuxError (Frame × List UInt8) := do
  -- Framing: the 12 bytes of the header.
  let header := bytes.take headerSize
  if header.length < headerSize then throw (.shortHeader header.length)
  let rest := bytes.drop headerSize
  -- Version Field: always set to 0.
  let version := header.getD 0 0
  if version ≠ 0 then throw (.version version)
  -- Type Field: one of 0x0 to 0x3.
  let kindByte := header.getD 1 0
  let some kind := Kind.ofUInt8? kindByte | throw (.unknownKind kindByte)
  -- Flags (16 bits), big endian; bits other than SYN, ACK, FIN and RST are kept, not checked.
  let flags := (Base.ByteOrder.ofBE ((header.drop 2).take 2)).toUInt16
  -- StreamID (32 bits), big endian.
  let streamId := (Base.ByteOrder.ofBE ((header.drop 4).take 4)).toUInt32
  -- Length (32 bits), big endian.
  let length := (Base.ByteOrder.ofBE (header.drop 8)).toUInt32
  -- Length Field: a Data frame has that many bytes after the header, and other types none.
  let size := if kind = .data then length.toNat else 0
  let (body, after) ← Encoding.ByteReader.bytes (.truncated size) size rest
  return (⟨kind, flags, streamId, length, ⟨body.toArray⟩⟩, after)

end EthLib.Networking.Libp2p.Yamux
