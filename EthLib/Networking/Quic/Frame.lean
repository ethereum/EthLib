module

public import EthLib.Networking.Quic.Packet

/-!
# QUIC frames

[RFC 9000 §19][frames] defines the fields of each version 1 frame.

The decoder checks their format constraints and the allowed packet types of [§12.4, Table 3][types].

Connection state, sender roles and flow-control credit belong to the transport state machine.

[frames]: https://www.rfc-editor.org/rfc/rfc9000#section-19
[types]: https://www.rfc-editor.org/rfc/rfc9000#section-12.4
-/

@[expose] public section

namespace EthLib.Networking.Quic.Frame

open Wire

/-- An additional ACK range: the gap and the range length, RFC 9000 §19.3.1. -/
abbrev AckRange := Varint × Varint

/-- Explicit congestion-notification counters: ECT(0), ECT(1), CE (§19.3.2). -/
abbrev EcnCounts := Varint × Varint × Varint

/-- The fields of an ACK frame (§19.3). -/
structure Ack where
  largest : Varint
  delay : Varint
  firstRange : Varint
  ranges : List AckRange
  ecn : Option EcnCounts
  deriving Repr, DecidableEq

/-- Each descending ACK range must leave a nonnegative packet number (§19.3.1). -/
def ackRangesValid : Nat → List AckRange → Prop
  | _, [] => True
  | previous, (gap, count) :: rest =>
    -- `largest = previous_smallest - gap - 2` and `smallest = largest - ack_range`.
    --
    -- If any computed packet number is negative, the frame is FRAME_ENCODING_ERROR.
    gap.val + 2 + count.val ≤ previous ∧
      -- The smallest packet number of this range is the previous smallest of the next one.
      ackRangesValid (previous - gap.val - 2 - count.val) rest

instance ackRangesValidDecidable (previous : Nat) (ranges : List AckRange) :
    Decidable (ackRangesValid previous ranges) :=
  match ranges with
  | [] => isTrue trivial
  | (gap, count) :: rest => by
    haveI := ackRangesValidDecidable (previous - gap.val - 2 - count.val) rest
    unfold ackRangesValid
    infer_instance

/-- Every version 1 frame, with the field order of RFC 9000 §§19.1–19.20. -/
inductive Frame where
  | padding
  | ping
  | ack (fields : Ack)
  | resetStream (streamId errorCode finalSize : Varint)
  | stopSending (streamId errorCode : Varint)
  | crypto (offset : Varint) (data : ByteArray)
  | newToken (token : ByteArray)
  | stream (streamId : Varint) (offset : Option Varint) (lengthPresent fin : Bool)
      (data : ByteArray)
  | maxData (maximum : Varint)
  | maxStreamData (streamId maximum : Varint)
  | maxStreams (unidirectional : Bool) (maximum : Varint)
  | dataBlocked (limit : Varint)
  | streamDataBlocked (streamId limit : Varint)
  | streamsBlocked (unidirectional : Bool) (limit : Varint)
  | newConnectionId (sequenceNumber retirePriorTo : Varint)
      (connectionId : ByteArray) (resetToken : Vector UInt8 16)
  | retireConnectionId (sequenceNumber : Varint)
  | pathChallenge (data : Vector UInt8 8)
  | pathResponse (data : Vector UInt8 8)
  | connectionClose (errorCode : Varint) (frameType : Option Varint) (reason : ByteArray)
  | handshakeDone
  deriving Repr, DecidableEq

/-- The numeric frame type, including the flags carried in the type (§12.4). -/
def Frame.type : Frame → Nat
  -- The Type Value column of §12.4, Table 3, written in decimal.
  | .padding => 0
  | .ping => 1
  -- §19.3.2: type 0x03 carries the ECN Counts, and type 0x02 does not.
  | .ack a => if a.ecn.isSome then 3 else 2
  | .resetStream .. => 4
  | .stopSending .. => 5
  | .crypto .. => 6
  | .newToken .. => 7
  -- §19.8: `0b00001XXX`, with the OFF bit 0x04, the LEN bit 0x02 and the FIN bit 0x01.
  | .stream _ offset lengthPresent fin _ =>
    8 + (if offset.isSome then 4 else 0) + (if lengthPresent then 2 else 0) +
      (if fin then 1 else 0)
  | .maxData .. => 16
  | .maxStreamData .. => 17
  -- §19.11: 0x12 for bidirectional streams, 0x13 for unidirectional streams.
  | .maxStreams u _ => if u then 19 else 18
  | .dataBlocked .. => 20
  | .streamDataBlocked .. => 21
  -- §19.14: 0x16 for the bidirectional limit, 0x17 for the unidirectional limit.
  | .streamsBlocked u _ => if u then 23 else 22
  | .newConnectionId .. => 24
  | .retireConnectionId .. => 25
  | .pathChallenge .. => 26
  | .pathResponse .. => 27
  -- §19.19: type 0x1c has the Frame Type field, and type 0x1d, the application variant, has not.
  | .connectionClose _ frameType _ => if frameType.isSome then 28 else 29
  | .handshakeDone => 30

/-- Format constraints that RFC 9000 §19 lets a receiver reject as FRAME_ENCODING_ERROR.

The count and length bounds also keep each encoded length below `2^62`.
-/
def Frame.Valid : Frame → Prop
  -- EthLib's bound: the ACK Range Count fits in a variable-length integer.
  --
  -- §19.3: `smallest = Largest Acknowledged - First ACK Range`, then §19.3.1 for each range.
  | .ack a => a.ranges.length < 2 ^ 62 ∧ a.firstRange.val ≤ a.largest.val ∧
      ackRangesValid (a.largest.val - a.firstRange.val) a.ranges
  -- §19.6: the sum of the offset and data length cannot exceed `2^62-1`.
  --
  -- Of FRAME_ENCODING_ERROR and CRYPTO_BUFFER_EXCEEDED, which §19.6 allows, EthLib takes the first.
  | .crypto offset data => offset.val + data.size < 2 ^ 62
  -- §19.7: the token MUST NOT be empty, and its length fits in a variable-length integer.
  --
  -- §19.7 gives this error to a client.
  --
  -- A server owes PROTOCOL_VIOLATION for any NEW_TOKEN, and EthLib gives it this error too.
  | .newToken token => token ≠ ByteArray.empty ∧ token.size < 2 ^ 62
  -- §19.8: the offset, 0 when absent, plus the data length cannot exceed `2^62-1`.
  --
  -- Of FRAME_ENCODING_ERROR and FLOW_CONTROL_ERROR, which §19.8 allows, EthLib takes the first.
  | .stream _ offset _ _ data => (offset.map Fin.val).getD 0 + data.size < 2 ^ 62
  -- §19.11 and §19.14: Maximum Streams cannot exceed `2^60`.
  --
  -- §19.14 also allows STREAM_LIMIT_ERROR, and EthLib takes FRAME_ENCODING_ERROR for both frames.
  | .maxStreams _ maximum | .streamsBlocked _ maximum => maximum.val ≤ 2 ^ 60
  -- §19.15: Length values less than 1 and greater than 20 are invalid.
  --
  -- §19.15: Retire Prior To MUST be less than or equal to Sequence Number.
  | .newConnectionId seq retire cid _ =>
      1 ≤ cid.size ∧ cid.size ≤ 20 ∧ retire.val ≤ seq.val
  -- EthLib's bound: the Reason Phrase Length fits in a variable-length integer.
  | .connectionClose _ _ reason => reason.size < 2 ^ 62
  -- §19 sets no format constraint on the other frames.
  | _ => True

instance (frame : Frame) : Decidable frame.Valid := by
  cases frame <;> unfold Frame.Valid <;> infer_instance

/-- Packet types that can carry this frame, RFC 9000 §12.4, Table 3. -/
def Frame.allowed (frame : Frame) (packet : Packet.PacketType) : Bool :=
  match frame with
  -- Pkts IH01, and ih01 for CONNECTION_CLOSE of type 0x1c: every packet type.
  | .padding | .ping | .connectionClose _ (some _) _ => true
  -- Pkts IH_1: Initial, Handshake and 1-RTT, not 0-RTT.
  | .ack _ | .crypto .. => packet != .zeroRtt
  -- Pkts ___1: 1-RTT only.
  | .newToken _ | .pathResponse _ | .handshakeDone => packet == .oneRtt
  -- Pkts ih01: only type 0x1c can appear in Initial or Handshake packets.
  --
  -- So type 0x1d takes 0-RTT and 1-RTT.
  | .connectionClose _ none _ => packet == .zeroRtt || packet == .oneRtt
  -- Pkts __01: 0-RTT and 1-RTT.
  --
  -- RETIRE_CONNECTION_ID falls here, as the published Table 3 lists it.
  --
  -- Departure: the verified erratum 7365 of RFC 9000 makes it ___1, as the end of §12.5 says.
  --
  -- EthLib keeps the published table, so it accepts RETIRE_CONNECTION_ID in 0-RTT.
  | _ => packet == .zeroRtt || packet == .oneRtt

/-- Reject a malformed frame as FRAME_ENCODING_ERROR, RFC 9000 §§19 and 20.1. -/
def validate (frame : Frame) : Except Error Unit :=
  if frame.Valid then .ok () else .error .frameEncoding

/-- Encode an optional integer without a presence marker. -/
def encodeOptional : Option Varint → List UInt8
  | none => []
  -- A field in brackets, such as `[Offset (i)]`, is written when present, with no marker.
  | some v => Varint.encodeList v

/-- Encode the additional ACK ranges in their wire order (§19.3). -/
def encodeRanges (ranges : List AckRange) : List UInt8 :=
  -- §19.3.1: `ACK Range { Gap (i), ACK Range Length (i) }`, in descending packet number order.
  ranges.flatMap fun (gap, length) => Varint.encodeList gap ++ Varint.encodeList length

/-- Encode the fields after the frame type (§19).

`encode` checks the format constraints before calling this helper. -/
def encodeBodyList : Frame → Except Error (List UInt8)
  -- §§19.1, 19.2 and 19.20: PADDING, PING and HANDSHAKE_DONE have no content.
  | .padding | .ping | .handshakeDone => .ok []
  | .ack a => do
    -- §19.3: ACK Range Count is the number of ACK Range fields.
    let count ← checkedVarint a.ranges.length
    -- §19.3.2: `[ECN Counts (..)]`: ECT0 Count (i), ECT1 Count (i), ECN-CE Count (i).
    let ecn := match a.ecn with
      | none => []
      | some (ect0, ect1, ce) =>
        Varint.encodeList ect0 ++ Varint.encodeList ect1 ++ Varint.encodeList ce
    -- §19.3: Largest Acknowledged (i), ACK Delay (i), ACK Range Count (i), First ACK Range (i).
    --
    -- Then `ACK Range (..) ...` and `[ECN Counts (..)]`.
    return Varint.encodeList a.largest ++ Varint.encodeList a.delay ++ Varint.encodeList count ++
      Varint.encodeList a.firstRange ++ encodeRanges a.ranges ++ ecn
  -- §19.4: Stream ID (i), Application Protocol Error Code (i), Final Size (i).
  | .resetStream id code size =>
    .ok (Varint.encodeList id ++ Varint.encodeList code ++ Varint.encodeList size)
  -- §19.5: Stream ID (i), Application Protocol Error Code (i).
  | .stopSending id code => .ok (Varint.encodeList id ++ Varint.encodeList code)
  -- §19.6: Offset (i), Length (i), Crypto Data (..).
  | .crypto offset data => do
    return Varint.encodeList offset ++ (← encodeBlob data.data.toList)
  -- §19.7: Token Length (i), Token (..).
  | .newToken token => encodeBlob token.data.toList
  | .stream id offset lengthPresent _ data => do
    -- §19.8: `[Length (i)]` only when the LEN bit is set, then Stream Data (..).
    let body ← if lengthPresent then encodeBlob data.data.toList else .ok data.data.toList
    -- §19.8: Stream ID (i), `[Offset (i)]` only when the OFF bit is set, then the data.
    return Varint.encodeList id ++ encodeOptional offset ++ body
  -- §§19.9 and 19.12: Maximum Data (i).
  --
  -- §§19.11 and 19.14: Maximum Streams (i).
  --
  -- §19.16: Sequence Number (i).
  | .maxData n | .maxStreams _ n | .dataBlocked n | .streamsBlocked _ n |
      .retireConnectionId n => .ok (Varint.encodeList n)
  -- §§19.10 and 19.13: Stream ID (i), Maximum Stream Data (i).
  | .maxStreamData id n | .streamDataBlocked id n =>
    .ok (Varint.encodeList id ++ Varint.encodeList n)
  -- §19.15: Sequence Number (i), Retire Prior To (i), Length (8), Connection ID (8..160).
  --
  -- Then Stateless Reset Token (128).
  --
  -- The validity check bounds the length by 20, so one byte holds it.
  | .newConnectionId seq retire cid token =>
    .ok (Varint.encodeList seq ++ Varint.encodeList retire ++ [UInt8.ofNat cid.size] ++
      cid.data.toList ++ token.toList)
  -- §§19.17 and 19.18: Data (64).
  | .pathChallenge data | .pathResponse data => .ok data.toList
  -- §19.19: Error Code (i), `[Frame Type (i)]`, Reason Phrase Length (i), Reason Phrase (..).
  | .connectionClose code frameType reason => do
    return Varint.encodeList code ++ encodeOptional frameType ++ (← encodeBlob reason.data.toList)

/-- Encode one well-formed frame with its shortest frame type (§12.4). -/
def encodeList (frame : Frame) : Except Error (List UInt8) := do
  -- The format constraints of §19 come first.
  validate frame
  let body ← encodeBodyList frame
  -- §12.4: a frame type MUST use the shortest possible encoding.
  --
  -- Every version 1 frame type is at most 0x1e, below 64, so it takes one byte.
  return UInt8.ofNat frame.type :: body

/-- Read an optional field when its flag is set. -/
def optional (present : Bool) : Reader (Option Varint) := do
  if present then return some (← varint) else return none

/-- Read the requested ACK ranges, stopping at the first incomplete field (§19.3). -/
def ranges : Nat → Reader (List AckRange)
  | 0 => pure []
  | n + 1 => do
    -- §19.3.1: Gap (i), then ACK Range Length (i).
    let gap ← varint
    let length ← varint
    let rest ← ranges n
    return (gap, length) :: rest

/-- Read the ACK fields, including congestion counters only for type 3 (§19.3). -/
def ack (ecnPresent : Bool) : Reader Ack := do
  -- §19.3: Largest Acknowledged (i), ACK Delay (i), ACK Range Count (i), First ACK Range (i).
  let largest ← varint
  let delay ← varint
  let count ← varint
  let firstRange ← varint
  -- §19.3.1: one Gap and one ACK Range Length for each value in the ACK Range Count field.
  let rs ← ranges count.val
  -- §19.3.2: ECN counts are only present when the ACK frame type is 0x03.
  let ecn ← if ecnPresent then do
      let ect0 ← varint
      let ect1 ← varint
      let ce ← varint
      pure (some (ect0, ect1, ce))
    else pure none
  return ⟨largest, delay, firstRange, rs, ecn⟩

/-- Read a frame's fields after its shortest one-byte type (§19). -/
def decodeBody (kind : Nat) : Reader Frame := do
  match kind with
  -- §§19.1 and 19.2: no content.
  | 0 => return .padding
  | 1 => return .ping
  -- §19.3: types 0x02 and 0x03.
  | 2 | 3 => return .ack (← ack (kind = 3))
  -- §19.4: Stream ID (i), Application Protocol Error Code (i), Final Size (i).
  | 4 =>
    let id ← varint
    let code ← varint
    return .resetStream id code (← varint)
  -- §19.5: Stream ID (i), Application Protocol Error Code (i).
  | 5 =>
    let id ← varint
    return .stopSending id (← varint)
  -- §19.6: Offset (i), then Length (i) and Crypto Data (..).
  | 6 =>
    let offset ← varint
    return .crypto offset (← blob).toByteArray
  -- §19.7: Token Length (i), Token (..).
  | 7 => return .newToken (← blob).toByteArray
  -- §19.8: types 0x08 to 0x0f.
  | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
    let id ← varint
    -- The OFF bit 0x04: the Offset field is present.
    let offset ← optional (kind / 4 % 2 = 1)
    -- The LEN bit 0x02: the Length field is present.
    --
    -- Without it, the Stream Data field consumes all the remaining bytes in the packet.
    let data ← if kind / 2 % 2 = 1 then blob else remainder
    -- The FIN bit 0x01 marks the end of the stream.
    return .stream id offset (kind / 2 % 2 = 1) (kind % 2 = 1) data.toByteArray
  -- §19.9: Maximum Data (i).
  | 16 => return .maxData (← varint)
  -- §19.10: Stream ID (i), Maximum Stream Data (i).
  | 17 =>
    let id ← varint
    return .maxStreamData id (← varint)
  -- §19.11: Maximum Streams (i), unidirectional for type 0x13.
  | 18 | 19 => return .maxStreams (kind = 19) (← varint)
  -- §19.12: Maximum Data (i).
  | 20 => return .dataBlocked (← varint)
  -- §19.13: Stream ID (i), Maximum Stream Data (i).
  | 21 =>
    let id ← varint
    return .streamDataBlocked id (← varint)
  -- §19.14: Maximum Streams (i), unidirectional for type 0x17.
  | 22 | 23 => return .streamsBlocked (kind = 23) (← varint)
  -- §19.15: Sequence Number (i), Retire Prior To (i), Length (8), Connection ID (8..160).
  --
  -- Then Stateless Reset Token (128).
  | 24 =>
    let seq ← varint
    let retire ← varint
    -- Length (8) admits up to 255 here; the validity check then requires 1 to 20.
    let cid ← Packet.connectionId 255
    return .newConnectionId seq retire cid (← vector 16)
  -- §19.16: Sequence Number (i).
  | 25 => return .retireConnectionId (← varint)
  -- §§19.17 and 19.18: Data (64).
  | 26 => return .pathChallenge (← vector 8)
  | 27 => return .pathResponse (← vector 8)
  -- §19.19: Error Code (i), `[Frame Type (i)]` for type 0x1c only, then the reason phrase.
  | 28 | 29 =>
    let code ← varint
    let frameType ← optional (kind = 28)
    return .connectionClose code frameType (← blob).toByteArray
  -- §19.20: no content.
  | 30 => return .handshakeDone
  -- §12.4: a frame of unknown type is FRAME_ENCODING_ERROR.
  | _ => throw .frameEncoding

/-- Read one frame and enforce its packet type (§12.4, Table 3). -/
def decodeList (packet : Packet.PacketType) : Reader Frame := do
  -- §12.4: Frame Type (i), in its shortest encoding.
  --
  -- Every version 1 frame type is at most 0x1e, below 64, so it takes one byte.
  --
  -- A longer encoding begins with a byte of 64 or more, which no type here has.
  --
  -- EthLib rejects it as an unknown type, where §12.4 allows PROTOCOL_VIOLATION.
  let kind ← byte
  -- A body that ends early is FRAME_ENCODING_ERROR (§20.1).
  let frame ← fun input => (decodeBody kind.toNat input).mapError fun _ => .frameEncoding
  -- A body that breaks a field bound of §19 is FRAME_ENCODING_ERROR.
  let _ ← StateT.lift (validate frame)
  -- §12.4: a frame in a packet type that is not permitted is PROTOCOL_VIOLATION.
  require (frame.allowed packet = true) (.protocolViolation kind.toNat)
  return frame


/-- Encode one well-formed frame as packed bytes. -/
def encode (frame : Frame) : Except Error ByteArray :=
  (encodeList frame).map List.toByteArray

/-- Read one frame and return its packed trailing bytes. -/
def decode (packet : Packet.PacketType) (input : ByteArray) : Except Error (Frame × ByteArray) :=
  (decodeList packet input.data.toList).map fun (frame, rest) => (frame, rest.toByteArray)

end EthLib.Networking.Quic.Frame
