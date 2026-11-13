module

public import EthLib.Networking.Quic.Frame
public import EthLib.Networking.Proofs.Quic.Packet

/-!
# Proofs: QUIC frames

The wire readers recover frame fields without consuming the following frame.
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
