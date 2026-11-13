module

public import EthLib.Networking.Quic.Frame
public import EthLib.Networking.Proofs.Quic.Packet

/-!
# Proofs: QUIC frames

The wire readers recover frame fields without consuming the following frame.

An ACK frame is well formed exactly when no packet number it acknowledges is negative.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Frame

open Wire

/-- Reading optional fields undoes writing them. -/
theorem optional_encode (value : Option Varint) (rest : List UInt8) :
    optional value.isSome (encodeOptional value ++ rest) = .ok (value, rest) := by
  cases value <;>
    simp only [optional, encodeOptional, Option.isSome, Bool.false_eq_true, ↓reduceIte,
      bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure,
      List.nil_append, varint_encode]

/-- Reading an opaque fixed-size field preserves its bytes exactly. -/
theorem vector_encode (n : Nat) (value : Vector UInt8 n) (rest : List UInt8) :
    vector n (value.toList ++ rest) = .ok (value, rest) := by
  have hl : value.toList.length = n := by simp
  simp only [vector, bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure,
    ← hl, bytes_append, ↓reduceDIte]
  simp only [Vector.toArray_toList, Vector.mk_toArray]

/-- The additional ACK ranges decode in the same order in which they were written. -/
theorem ranges_encode (values : List AckRange) (rest : List UInt8) :
    ranges values.length (encodeRanges values ++ rest) = .ok (values, rest) := by
  unfold encodeRanges
  induction values with
  | nil => rfl
  | cons value tail ih =>
    rcases value with ⟨gap, count⟩
    simp only [ranges, List.flatMap_cons, List.length_cons,
      List.append_assoc, bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure,
      varint_encode, ih]

/-- A forbidden frame cannot be accepted, regardless of its field bytes. -/
theorem allowed_of_decode {packet : Packet.PacketType} {input rest : List UInt8}
    {frame : Frame} (h : decode packet input = .ok (frame, rest)) :
    frame.allowed packet = true := by
  simp only [decode, bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure] at h
  cases hb : byte input with
  | error e => simp [hb] at h
  | ok first =>
    rcases first with ⟨kind, tail⟩
    simp only [hb] at h
    cases hd : decodeBody kind.toNat tail with
    | error e => simp [hd, Except.mapError] at h
    | ok decoded =>
      rcases decoded with ⟨f, tail'⟩
      simp only [hd, Except.mapError] at h
      cases hv : validate f with
      | error e =>
        simp only [StateT.lift, bind, hv, Except.bind] at h
        contradiction
      | ok u =>
        cases u
        simp only [StateT.lift, bind, pure, hv, Except.bind, Except.pure] at h
        by_cases allowed : f.allowed packet = true
        · simp only [require, allowed, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact allowed
        · simp only [require, allowed] at h
          contradiction

/-- A type that Table 3 forbids cannot be decoded as that frame. -/
theorem decode_ne_ok_of_not_allowed (packet : Packet.PacketType) (frame : Frame)
    (input rest : List UInt8) (h : frame.allowed packet = false) :
    decode packet input ≠ .ok (frame, rest) := by
  intro accepted
  have := allowed_of_decode accepted
  simp [h] at this

/-- A frame without an explicit data length ends its packet. -/
def permitsFollowing (frame : Frame) (rest : List UInt8) : Prop :=
  match frame with
  | .stream _ _ false _ _ => rest = []
  | _ => True

attribute [local simp] bind pure StateT.bind StateT.pure Except.bind Except.pure
attribute [local simp] List.append_assoc Frame.type encodeBody decodeBody checkedVarint
attribute [local simp] optional_encode vector_encode ranges_encode blob_encode

/-- Frame fields round trip, with trailing bytes except after a STREAM without LEN. -/
theorem decodeBody_encodeBody (frame : Frame) (rest : List UInt8) (valid : frame.Valid)
    (follows : permitsFollowing frame rest) :
    (encodeBody frame >>= fun data => decodeBody frame.type (data ++ rest)) =
      .ok (frame, rest) := by
  cases frame with
  | padding => rfl
  | ping => rfl
  | handshakeDone => rfl
  | ack a =>
    rcases a with ⟨largest, delay, firstRange, rs, ecn⟩
    have countBound : rs.length < 2 ^ 62 := valid.1
    cases ecn <;> simp [ack, countBound]
  | resetStream id code size => simp
  | stopSending id code => simp
  | crypto offset data =>
    have bound : data.length < 2 ^ 62 := by
      have := valid
      dsimp only [Frame.Valid] at this
      omega
    simp [encodeBlob, bound]
  | newToken token => simp [encodeBlob, valid.2]
  | stream id offset lengthPresent fin data =>
    have bound : data.length < 2 ^ 62 := by
      have := valid
      dsimp only [Frame.Valid] at this
      omega
    cases offset <;> cases lengthPresent <;> cases fin <;>
      simp_all [permitsFollowing, encodeOptional, optional, encodeBlob, blob, remainder]
  | maxData n => simp
  | maxStreamData id n => simp
  | maxStreams u n => cases u <;> simp
  | dataBlocked n => simp
  | streamDataBlocked id n => simp
  | streamsBlocked u n => cases u <;> simp
  | newConnectionId seq retire cid token =>
    simp only [encodeBody, Frame.type, decodeBody]
    have hcid : cid.length ≤ 255 := by have := valid.2.1; omega
    simp [Packet.connectionId_encode cid _ 255 hcid (by decide)]
  | retireConnectionId n => simp
  | pathChallenge data => simp
  | pathResponse data => simp
  | connectionClose code frameType reason =>
    have bound : reason.length < 2 ^ 62 := valid
    cases frameType <;> simp [encodeOptional, optional, encodeBlob, bound]

/-- Every version 1 frame type fits its required single-byte representation. -/
theorem type_lt (frame : Frame) : frame.type < 64 := by
  cases frame <;> simp only [Frame.type] <;> (try split_ifs) <;> omega

/-- Successful validation implies the frame's format constraints. -/
theorem valid_of_validate {frame : Frame} (accepted : validate frame = .ok ()) : frame.Valid := by
  by_cases valid : frame.Valid
  · exact valid
  · simp [validate, valid] at accepted

/-- A decoded frame meets every format constraint, RFC 9000 §19. -/
theorem valid_of_decode {packet : Packet.PacketType} {input rest : List UInt8}
    {frame : Frame} (h : decode packet input = .ok (frame, rest)) : frame.Valid := by
  simp only [decode, bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure] at h
  cases hb : byte input with
  | error e => simp [hb] at h
  | ok first =>
    rcases first with ⟨kind, tail⟩
    simp only [hb] at h
    cases hd : decodeBody kind.toNat tail with
    | error e =>
      simp only [hd, Except.mapError] at h
      simp at h
    | ok decoded =>
      rcases decoded with ⟨f, tail'⟩
      simp only [hd, Except.mapError] at h
      cases hv : validate f with
      | error e =>
        simp only [StateT.lift, bind, hv, Except.bind] at h
        contradiction
      | ok u =>
        cases u
        simp only [StateT.lift, bind, pure, hv, Except.bind, Except.pure] at h
        by_cases allowed : f.allowed packet = true
        · simp only [require, allowed, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact valid_of_validate hv
        · simp only [require, allowed] at h
          contradiction

/-- The ACK ranges after the first one, each as its largest and smallest packet number.

They start from the smallest packet number of the range before them.

The largest packet number of a range is its gap plus two below that smallest one.

Its smallest packet number is its range length below its largest, RFC 9000 §19.3.1.

The numbers are integers, so a range of an invalid frame can reach below 0.
-/
def ackedRangesFrom : Int → List AckRange → List (Int × Int)
  | _, [] => []
  | smallest, (gap, length) :: rest =>
    (smallest - gap.val - 2, smallest - gap.val - 2 - length.val) ::
      ackedRangesFrom (smallest - gap.val - 2 - length.val) rest

/-- The ranges an ACK frame acknowledges, each as its largest and smallest packet number.

The first range runs from Largest Acknowledged down by First ACK Range, RFC 9000 §19.3.1.
-/
def ackedRanges (a : Ack) : List (Int × Int) :=
  (a.largest.val, a.largest.val - a.firstRange.val) ::
    ackedRangesFrom (a.largest.val - a.firstRange.val) a.ranges

private theorem ackRangesValid_iff (previous : Nat) (ranges : List AckRange) :
    ackRangesValid previous ranges ↔
      ∀ range ∈ ackedRangesFrom previous ranges, 0 ≤ range.2 := by
  induction ranges generalizing previous with
  | nil => simp [ackRangesValid, ackedRangesFrom]
  | cons head rest ih =>
    rcases head with ⟨gap, count⟩
    simp only [ackRangesValid, ackedRangesFrom, List.mem_cons, forall_eq_or_imp]
    by_cases fits : gap.val + 2 + count.val ≤ previous
    · have cast : (previous : Int) - gap.val - 2 - count.val =
          ((previous - gap.val - 2 - count.val : Nat) : Int) := by omega
      rw [cast, ← ih]
      exact ⟨fun ⟨_, h⟩ => ⟨by omega, h⟩, fun ⟨_, h⟩ => ⟨fits, h⟩⟩
    · constructor
      · intro h
        omega
      · intro h
        omega

/-- Each additional range lowers the packet number by at least two. -/
private theorem two_mul_length_le_of_ackRangesValid (previous : Nat) (ranges : List AckRange)
    (h : ackRangesValid previous ranges) : 2 * ranges.length ≤ previous := by
  induction ranges generalizing previous with
  | nil => simp
  | cons head rest ih =>
    rcases head with ⟨gap, count⟩
    simp only [ackRangesValid] at h
    have := ih _ h.2
    simp only [List.length_cons]
    omega

/-- An ACK frame is well formed exactly when no acknowledged packet number is negative.

Each additional range lowers the packet number by at least two.

So their count stays below `2^62`, and is a QUIC integer.
-/
theorem valid_ack_iff (a : Ack) :
    (Frame.ack a).Valid ↔ ∀ range ∈ ackedRanges a, 0 ≤ range.2 := by
  simp only [Frame.Valid, ackedRanges, List.mem_cons, forall_eq_or_imp]
  have bound := a.largest.isLt
  by_cases fits : a.firstRange.val ≤ a.largest.val
  · have cast : (a.largest.val : Int) - a.firstRange.val =
        ((a.largest.val - a.firstRange.val : Nat) : Int) := by omega
    rw [cast, ← ackRangesValid_iff]
    refine ⟨fun ⟨_, _, h⟩ => ⟨by omega, h⟩, fun ⟨_, h⟩ => ⟨?_, fits, h⟩⟩
    have := two_mul_length_le_of_ackRangesValid _ _ h
    omega
  · constructor
    · intro h
      omega
    · intro h
      omega

/-- A decoded ACK frame acknowledges no negative packet number, RFC 9000 §19.3.1. -/
theorem ackedRanges_nonneg_of_decode {packet : Packet.PacketType} {input rest : List UInt8}
    {a : Ack} (h : decode packet input = .ok (.ack a, rest)) :
    ∀ range ∈ ackedRanges a, 0 ≤ range.2 :=
  (valid_ack_iff a).mp (valid_of_decode h)

/-- Decoding a permitted encoded frame recovers that frame and the following bytes.

A STREAM without LEN must be the last frame in the packet, as RFC 9000 §19.8 requires.
-/
theorem decode_encode (frame : Frame) (packet : Packet.PacketType) (encoded rest : List UInt8)
    (written : encode frame = .ok encoded) (allowed : frame.allowed packet = true)
    (follows : permitsFollowing frame rest) :
    decode packet (encoded ++ rest) = .ok (frame, rest) := by
  cases checked : validate frame with
  | error error =>
    simp only [encode, bind, Except.bind, checked] at written
    contradiction
  | ok u =>
    cases u
    have valid := valid_of_validate checked
    cases body : encodeBody frame with
    | error error =>
      simp only [encode, bind, Except.bind, checked, body] at written
      contradiction
    | ok data =>
      have fields := decodeBody_encodeBody frame rest valid follows
      simp only [bind, body, Except.bind] at fields
      simp only [encode, bind, pure, checked, body, Except.bind, Except.pure,
        Except.ok.injEq] at written
      subst encoded
      have kind : (UInt8.ofNat frame.type).toNat = frame.type :=
        UInt8.toNat_ofNat_of_lt' (by have := type_lt frame; simp only [UInt8.size]; omega)
      simp only [decode, bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure,
        List.cons_append, byte, kind, fields, Except.mapError, StateT.lift, checked,
        require, allowed, ↓reduceIte]

end EthLib.Networking.Quic.Frame
