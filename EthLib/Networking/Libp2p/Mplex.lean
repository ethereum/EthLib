module

public import EthLib.Networking.Encoding.Uvarint

/-!
# mplex frames

mplex carries many streams over one connection, one frame at a time.

The source asks a sender to write at most 1 MiB in a message, and nothing in a close or a reset.

The decoder refuses a frame that breaks either rule, and applies the 1 MiB limit to every frame.

The source marks mplex as deprecated and recommends QUIC or yamux instead.

The source is the sections Message format and Protocol of [mplex][mplex].

[mplex]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/mplex/README.md#message-format
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Mplex

open EthLib.Networking.Encoding

/-- The name of mplex in multistream-select.

The networking specification of the consensus layer gives it, since the mplex source does not. -/
def protocolId : ByteArray := "/mplex/6.7.0".toUTF8

/-- What a frame does to its stream, from the section Flag Values. -/
inductive Flag where
  /-- Open a stream; the data is its name. -/
  | newStream
  /-- Data on a stream that the remote peer opened. -/
  | messageReceiver
  /-- Data on a stream that the sender opened. -/
  | messageInitiator
  /-- Close for writing a stream that the remote peer opened. -/
  | closeReceiver
  /-- Close for writing a stream that the sender opened. -/
  | closeInitiator
  /-- Reset a stream that the remote peer opened. -/
  | resetReceiver
  /-- Reset a stream that the sender opened. -/
  | resetInitiator
  deriving Repr, DecidableEq

/-- The value of a flag, from 0 to 6. -/
def Flag.toNat : Flag → Nat
  -- Flag Values: NewStream 0, MessageReceiver 1, MessageInitiator 2, CloseReceiver 3.
  --
  -- Then CloseInitiator 4, ResetReceiver 5 and ResetInitiator 6.
  | .newStream => 0
  | .messageReceiver => 1
  | .messageInitiator => 2
  | .closeReceiver => 3
  | .closeInitiator => 4
  | .resetReceiver => 5
  | .resetInitiator => 6

/-- The flag of a value, if it names one; 7 names none. -/
def Flag.ofNat? : Nat → Option Flag
  | 0 => some .newStream
  | 1 => some .messageReceiver
  | 2 => some .messageInitiator
  | 3 => some .closeReceiver
  | 4 => some .closeInitiator
  | 5 => some .resetReceiver
  | 6 => some .resetInitiator
  -- Not in the source: 7 fits three flag bits, but Flag Values gives it no meaning.
  | _ => none

/-- Whether a frame of this flag closes or resets its stream, so the source asks for no data. -/
def Flag.ends : Flag → Bool
  -- Closing a stream and Resetting a stream: flags 3 to 6 have a zero length body.
  | .closeReceiver | .closeInitiator | .resetReceiver | .resetInitiator => true
  | _ => false

/-- The first stream ID that does not fit a header.

A header holds 63 bits, and the flag takes three of them. -/
def streamIdBound : Nat :=
  -- Message format: a header has at most 9 bytes, so the maximum stream ID is `2^60 - 1`.
  2 ^ 60

/-- The most data in one message: 1 MiB, from the section Writing to a stream. -/
def maxData : Nat :=
  -- Up to 1 MiB per message, that is `2^20` bytes.
  1048576

/-- One frame: its stream, its flag and its data. -/
structure Frame where
  /-- The stream ID. -/
  streamId : Nat
  /-- What the frame does to its stream. -/
  flag : Flag
  /-- The data. -/
  data : ByteArray

/-- A frame that the decoder accepts and a sender may write.

Its stream ID fits the header, its data is at most 1 MiB, and a close or a reset has no data.

The last two are rules for the sender in the source, which the decoder also enforces. -/
def Frame.Valid (frame : Frame) : Prop :=
  frame.streamId < streamIdBound ∧ frame.data.size ≤ maxData ∧
    (frame.flag.ends → frame.data.size = 0)

instance (frame : Frame) : Decidable frame.Valid := by
  unfold Frame.Valid; infer_instance

/-- Why the frame at the start of an input was refused. -/
inductive MplexError where
  /-- The header is not an unsigned varint. -/
  | header (error : Uvarint.UvarintError)
  /-- The three low bits of the header are 7, which names no flag. -/
  | unknownFlag
  /-- The length is not an unsigned varint. -/
  | length (error : Uvarint.UvarintError)
  /-- The length is over 1 MiB. -/
  | tooLong (length : Nat)
  /-- A close or a reset declares a length other than zero. -/
  | dataOnEnd (length : Nat)
  /-- The input ends before the data that the length counts. -/
  | truncated (length available : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def MplexError.code : MplexError → UInt32
  | .header _ => 1
  | .unknownFlag => 2
  | .length _ => 3
  | .tooLong _ => 4
  | .dataOnEnd _ => 5
  | .truncated _ _ => 6

/-- The bytes of a frame.

The frame must be valid; the bytes of any other frame are not specified. -/
def encode (frame : Frame) : List UInt8 :=
  -- Message format: a header uvarint, a length uvarint, then length bytes of data.
  --
  -- The lower three bits of the header are the flag, and the rest the stream ID: `8 * id + flag`.
  Uvarint.encode (8 * frame.streamId + frame.flag.toNat) ++ Uvarint.encode frame.data.size ++
    frame.data.data.toList

/-- The frame at the start of the input, and the bytes after it. -/
def decode (bytes : List UInt8) : Except MplexError (Frame × List UInt8) := do
  -- Message format: the header is an unsigned varint.
  let (header, rest) ← (Uvarint.decode bytes).mapError .header
  -- `flag = header & 0x07`.
  --
  -- Not in the source: a value outside Flag Values is refused.
  let some flag := Flag.ofNat? (header % 8) | throw .unknownFlag
  -- The data segment is length prefixed by another unsigned varint.
  let (length, rest) ← (Uvarint.decode rest).mapError .length
  -- Writing to a stream: up to 1 MiB per message.
  --
  -- Not in the source: the decoder applies the limit to every flag, a stream name included.
  --
  -- It checks the length before it reads the data, to bound the memory a peer can make it use.
  if maxData < length then throw (.tooLong length)
  -- Closing a stream and Resetting a stream: a close or a reset has a zero length body.
  --
  -- The source asks this of the sender; the decoder also refuses a frame that breaks it.
  if flag.ends ∧ length ≠ 0 then throw (.dataOnEnd length)
  -- The data: `length` bytes.
  let body := rest.take length
  if body.length < length then throw (.truncated length body.length)
  -- `id = header >> 3`.
  return (⟨header / 8, flag, ⟨body.toArray⟩⟩, rest.drop length)

end EthLib.Networking.Libp2p.Mplex
