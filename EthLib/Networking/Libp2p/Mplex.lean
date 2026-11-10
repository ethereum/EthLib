module

public import EthLib.Networking.Encoding.Uvarint

/-!
# mplex frames

mplex carries many streams over one connection, one frame at a time.

A frame is an unsigned varint header, an unsigned varint length, then that many bytes of data.

The header holds the stream ID above three flag bits.

The source asks a sender to write at most 1 MiB in a message, and nothing in a close or a reset.

The decoder refuses a frame that breaks either rule, and applies the 1 MiB limit to every frame.

That bounds the memory a peer can make it use, a stream name included.

The source marks mplex as deprecated and recommends QUIC or yamux instead.

The source is [mplex, "Message format" and "Protocol"][mplex].

[mplex]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/mplex/README.md#message-format
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Mplex

open EthLib.Networking.Encoding

/-- What a frame does to its stream, "Flag Values". -/
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
  | _ => none

/-- Whether a frame of this flag closes or resets its stream, so the source asks for no data. -/
def Flag.ends : Flag → Bool
  | .closeReceiver | .closeInitiator | .resetReceiver | .resetInitiator => true
  | _ => false

/-- The first stream ID that does not fit a header.

A header holds 63 bits, and the flag takes three of them. -/
def streamIdBound : Nat := 2 ^ 60

/-- The most data in one message: 1 MiB, from "Writing to a stream". -/
def maxData : Nat := 1048576

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

/-- The bytes of a frame: header, length, then data.

The frame must be valid; the bytes of any other frame are not specified. -/
def encode (frame : Frame) : List UInt8 :=
  Uvarint.encode (8 * frame.streamId + frame.flag.toNat) ++ Uvarint.encode frame.data.size ++
    frame.data.data.toList

/-- The frame at the start of the input, and the bytes after it. -/
def decode (bytes : List UInt8) : Except MplexError (Frame × List UInt8) := do
  let (header, rest) ← (Uvarint.decode bytes).mapError .header
  let some flag := Flag.ofNat? (header % 8) | throw .unknownFlag
  let (length, rest) ← (Uvarint.decode rest).mapError .length
  if maxData < length then throw (.tooLong length)
  if flag.ends ∧ length ≠ 0 then throw (.dataOnEnd length)
  let body := rest.take length
  if body.length < length then throw (.truncated length body.length)
  return (⟨header / 8, flag, ⟨body.toArray⟩⟩, rest.drop length)

end EthLib.Networking.Libp2p.Mplex
