module

public import EthLib.Networking.Quic.Packet

/-!
# QUIC frames

RFC 9000 §19 defines the fields of each version 1 frame.

Frame types use the shortest integer representation (§12.4).

The decoder checks format constraints and the allowed packet types in §12.4, Table 3.

Connection state, sender roles and flow-control credit belong to the transport state machine.
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
    gap.val + 2 + count.val ≤ previous ∧
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
  | .padding => 0
  | .ping => 1
  | .ack a => if a.ecn.isSome then 3 else 2
  | .resetStream .. => 4
  | .stopSending .. => 5
  | .crypto .. => 6
  | .newToken .. => 7
  | .stream _ offset lengthPresent fin _ =>
    8 + (if offset.isSome then 4 else 0) + (if lengthPresent then 2 else 0) +
      (if fin then 1 else 0)
  | .maxData .. => 16
  | .maxStreamData .. => 17
  | .maxStreams u _ => if u then 19 else 18
  | .dataBlocked .. => 20
  | .streamDataBlocked .. => 21
  | .streamsBlocked u _ => if u then 23 else 22
  | .newConnectionId .. => 24
  | .retireConnectionId .. => 25
  | .pathChallenge .. => 26
  | .pathResponse .. => 27
  | .connectionClose _ frameType _ => if frameType.isSome then 28 else 29
  | .handshakeDone => 30

/-- Format constraints that RFC 9000 §19 lets a receiver reject as FRAME_ENCODING_ERROR.

The count and length bounds also keep each encoded length below `2^62`.
-/
def Frame.Valid : Frame → Prop
  | .ack a => a.ranges.length < 2 ^ 62 ∧ a.firstRange.val ≤ a.largest.val ∧
      ackRangesValid (a.largest.val - a.firstRange.val) a.ranges
  | .crypto offset data => offset.val + data.size < 2 ^ 62
  | .newToken token => token ≠ ByteArray.empty ∧ token.size < 2 ^ 62
  | .stream _ offset _ _ data => (offset.map Fin.val).getD 0 + data.size < 2 ^ 62
  | .maxStreams _ maximum | .streamsBlocked _ maximum => maximum.val ≤ 2 ^ 60
  | .newConnectionId seq retire cid _ =>
      1 ≤ cid.size ∧ cid.size ≤ 20 ∧ retire.val ≤ seq.val
  | .connectionClose _ _ reason => reason.size < 2 ^ 62
  | _ => True

instance (frame : Frame) : Decidable frame.Valid := by
  cases frame <;> unfold Frame.Valid <;> infer_instance

/-- Packet types that can carry this frame, RFC 9000 §12.4, Table 3. -/
def Frame.allowed (frame : Frame) (packet : Packet.PacketType) : Bool :=
  match frame with
  | .padding | .ping | .connectionClose _ (some _) _ => true
  | .ack _ | .crypto .. => packet != .zeroRtt
  | .newToken _ | .pathResponse _ | .handshakeDone => packet == .oneRtt
  | .connectionClose _ none _ => packet == .zeroRtt || packet == .oneRtt
  | _ => packet == .zeroRtt || packet == .oneRtt

/-- Reject a malformed frame as FRAME_ENCODING_ERROR, RFC 9000 §§19 and 20.1. -/
def validate (frame : Frame) : Except Error Unit :=
  if frame.Valid then .ok () else .error .frameEncoding

/-- Encode an optional integer without a presence marker. -/
def encodeOptional : Option Varint → List UInt8
  | none => []
  | some v => Varint.encodeList v

/-- Encode the additional ACK ranges in their wire order (§19.3). -/
def encodeRanges (ranges : List AckRange) : List UInt8 :=
  ranges.flatMap fun (gap, length) => Varint.encodeList gap ++ Varint.encodeList length

/-- Encode the fields after the frame type (§19).

`encode` checks the format constraints before calling this helper. -/
def encodeBodyList : Frame → Except Error (List UInt8)
  | .padding | .ping | .handshakeDone => .ok []
  | .ack a => do
    let count ← checkedVarint a.ranges.length
    let ecn := match a.ecn with
      | none => []
      | some (ect0, ect1, ce) =>
        Varint.encodeList ect0 ++ Varint.encodeList ect1 ++ Varint.encodeList ce
    return Varint.encodeList a.largest ++ Varint.encodeList a.delay ++ Varint.encodeList count ++
      Varint.encodeList a.firstRange ++ encodeRanges a.ranges ++ ecn
  | .resetStream id code size =>
    .ok (Varint.encodeList id ++ Varint.encodeList code ++ Varint.encodeList size)
  | .stopSending id code => .ok (Varint.encodeList id ++ Varint.encodeList code)
  | .crypto offset data => do
    return Varint.encodeList offset ++ (← encodeBlob data.data.toList)
  | .newToken token => encodeBlob token.data.toList
  | .stream id offset lengthPresent _ data => do
    let body ← if lengthPresent then encodeBlob data.data.toList else .ok data.data.toList
    return Varint.encodeList id ++ encodeOptional offset ++ body
  | .maxData n | .maxStreams _ n | .dataBlocked n | .streamsBlocked _ n |
      .retireConnectionId n => .ok (Varint.encodeList n)
  | .maxStreamData id n | .streamDataBlocked id n =>
    .ok (Varint.encodeList id ++ Varint.encodeList n)
  | .newConnectionId seq retire cid token =>
    .ok (Varint.encodeList seq ++ Varint.encodeList retire ++ [UInt8.ofNat cid.size] ++
      cid.data.toList ++ token.toList)
  | .pathChallenge data | .pathResponse data => .ok data.toList
  | .connectionClose code frameType reason => do
    return Varint.encodeList code ++ encodeOptional frameType ++ (← encodeBlob reason.data.toList)

/-- Encode one well-formed frame with its shortest frame type (§12.4). -/
def encodeList (frame : Frame) : Except Error (List UInt8) := do
  validate frame
  let body ← encodeBodyList frame
  return UInt8.ofNat frame.type :: body

/-- Read an optional field when its flag is set. -/
def optional (present : Bool) : Reader (Option Varint) := do
  if present then return some (← varint) else return none

/-- Read the requested ACK ranges, stopping at the first incomplete field (§19.3). -/
def ranges : Nat → Reader (List AckRange)
  | 0 => pure []
  | n + 1 => do
    let gap ← varint
    let length ← varint
    let rest ← ranges n
    return (gap, length) :: rest

/-- Read the ACK fields, including congestion counters only for type 3 (§19.3). -/
def ack (ecnPresent : Bool) : Reader Ack := do
  let largest ← varint
  let delay ← varint
  let count ← varint
  let firstRange ← varint
  let rs ← ranges count.val
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
  | 0 => return .padding
  | 1 => return .ping
  | 2 | 3 => return .ack (← ack (kind = 3))
  | 4 =>
    let id ← varint
    let code ← varint
    return .resetStream id code (← varint)
  | 5 =>
    let id ← varint
    return .stopSending id (← varint)
  | 6 =>
    let offset ← varint
    return .crypto offset (← blob).toByteArray
  | 7 => return .newToken (← blob).toByteArray
  | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
    let id ← varint
    let offset ← optional (kind / 4 % 2 = 1)
    let data ← if kind / 2 % 2 = 1 then blob else remainder
    return .stream id offset (kind / 2 % 2 = 1) (kind % 2 = 1) data.toByteArray
  | 16 => return .maxData (← varint)
  | 17 =>
    let id ← varint
    return .maxStreamData id (← varint)
  | 18 | 19 => return .maxStreams (kind = 19) (← varint)
  | 20 => return .dataBlocked (← varint)
  | 21 =>
    let id ← varint
    return .streamDataBlocked id (← varint)
  | 22 | 23 => return .streamsBlocked (kind = 23) (← varint)
  | 24 =>
    let seq ← varint
    let retire ← varint
    let cid ← Packet.connectionId 255
    return .newConnectionId seq retire cid (← vector 16)
  | 25 => return .retireConnectionId (← varint)
  | 26 => return .pathChallenge (← vector 8)
  | 27 => return .pathResponse (← vector 8)
  | 28 | 29 =>
    let code ← varint
    let frameType ← optional (kind = 28)
    return .connectionClose code frameType (← blob).toByteArray
  | 30 => return .handshakeDone
  | _ => throw .frameEncoding

/-- Read one frame and enforce its packet type (§12.4, Table 3).

All version 1 frame types are below 64, so a type in a longer form is rejected as unknown.

A body that ends early or breaks a field bound is FRAME_ENCODING_ERROR (§20.1).

A STREAM frame without LEN consumes all remaining packet bytes (§19.8).
-/
def decodeList (packet : Packet.PacketType) : Reader Frame := do
  let kind ← byte
  let frame ← fun input => (decodeBody kind.toNat input).mapError fun _ => .frameEncoding
  let _ ← StateT.lift (validate frame)
  require (frame.allowed packet = true) (.protocolViolation kind.toNat)
  return frame


/-- Encode one well-formed frame as packed bytes. -/
def encode (frame : Frame) : Except Error ByteArray :=
  (encodeList frame).map List.toByteArray

/-- Read one frame and return its packed trailing bytes. -/
def decode (packet : Packet.PacketType) (input : ByteArray) : Except Error (Frame × ByteArray) :=
  (decodeList packet input.data.toList).map fun (frame, rest) => (frame, rest.toByteArray)

end EthLib.Networking.Quic.Frame
