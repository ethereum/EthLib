module

public import EthLib.Networking.Libp2p.Yamux
public import EthLib.Base.Proofs.ByteOrder
import EthLib.Base.Proofs.Bytes
import EthLib.Networking.Proofs.Encoding.ByteReader

/-!
# Proofs: yamux frames

- Every header is 12 bytes.
- Decoding reads back a valid frame from its encoding, whatever bytes follow it.
- The decoder accepts only these encodings, and only valid frames.
- Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.Yamux

open EthLib.Base
open EthLib.Networking.Libp2p.Yamux

/-- Reading back the byte of a type gives the type. -/
theorem Kind.ofUInt8?_toUInt8 (kind : Kind) : Kind.ofUInt8? kind.toUInt8 = some kind := by
  cases kind <;> rfl

/-- The byte of a type that a byte names is that byte. -/
theorem Kind.toUInt8_of_ofUInt8? {b : UInt8} {kind : Kind} (h : Kind.ofUInt8? b = some kind) :
    kind.toUInt8 = b := by
  unfold Kind.ofUInt8? at h
  split at h <;> simp at h <;> subst h <;> rfl

/-- The encoding of a frame is its 12-byte header, then its data. -/
theorem length_encode (frame : Frame) :
    (encode frame).length = headerSize + frame.data.size := by
  have hl : frame.data.data.toList.length = frame.data.size := Array.length_toList
  simp [encode, headerSize, hl]
  omega

/-- The bytes of a number on two bytes are two bytes. -/
private theorem toBE_two (n : Nat) : ∃ a b, (ByteOrder.toBE 2 n).toList = [a, b] := by
  have h := ByteOrder.length_toList_toBE 2 n
  match hl : (ByteOrder.toBE 2 n).toList, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- The bytes of a number on four bytes are four bytes. -/
private theorem toBE_four (n : Nat) : ∃ a b c d, (ByteOrder.toBE 4 n).toList = [a, b, c, d] := by
  have h := ByteOrder.length_toList_toBE 4 n
  match hl : (ByteOrder.toBE 4 n).toList, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- Two bytes survive reading them as a 16-bit value and writing that value back. -/
private theorem toBE_toUInt16 (a b : UInt8) :
    (ByteOrder.toBE 2 (ByteOrder.ofBE [a, b]).toUInt16.toNat).toList = [a, b] := by
  have hlt := ByteOrder.ofBE_lt [a, b]
  simp only [List.length_cons, List.length_nil] at hlt
  have hv : (ByteOrder.ofBE [a, b]).toUInt16.toNat = ByteOrder.ofBE [a, b] := by
    rw [Nat.toUInt16, UInt16.toNat_ofNat_of_lt' (by simp only [UInt16.size]; omega)]
  rw [hv]
  exact ByteOrder.toList_toBE_ofBE_of_length rfl

/-- Four bytes survive reading them as a 32-bit value and writing that value back. -/
private theorem toBE_toUInt32 (a b c d : UInt8) :
    (ByteOrder.toBE 4 (ByteOrder.ofBE [a, b, c, d]).toUInt32.toNat).toList = [a, b, c, d] := by
  have hlt := ByteOrder.ofBE_lt [a, b, c, d]
  simp only [List.length_cons, List.length_nil] at hlt
  have hv : (ByteOrder.ofBE [a, b, c, d]).toUInt32.toNat = ByteOrder.ofBE [a, b, c, d] := by
    rw [Nat.toUInt32, UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
  rw [hv]
  exact ByteOrder.toList_toBE_ofBE_of_length rfl

/-- Decoding the encoding of a valid frame, then any bytes, returns the frame and those bytes. -/
theorem decode_encode {frame : Frame} (h : frame.Valid) (rest : List UInt8) :
    decode (encode frame ++ rest) = .ok (frame, rest) := by
  obtain ⟨a0, a1, hA⟩ := toBE_two frame.flags.toNat
  obtain ⟨b0, b1, b2, b3, hB⟩ := toBE_four frame.streamId.toNat
  obtain ⟨c0, c1, c2, c3, hC⟩ := toBE_four frame.length.toNat
  have hl : frame.data.data.toList.length = frame.data.size :=
    Array.length_toList
  have hA' := ByteOrder.ofBE_toBE_of_lt (n := 2) (x := frame.flags.toNat)
    (by have := frame.flags.toNat_lt; simpa using this)
  have hB' := ByteOrder.ofBE_toBE_of_lt (n := 4) (x := frame.streamId.toNat)
    (by have := frame.streamId.toNat_lt; simpa using this)
  have hC' := ByteOrder.ofBE_toBE_of_lt (n := 4) (x := frame.length.toNat)
    (by have := frame.length.toNat_lt; simpa using this)
  rw [hA] at hA'
  rw [hB] at hB'
  rw [hC] at hC'
  have hv : frame.data.size = frame.dataSize := h
  have hba := Base.byteArray_mk_toArray_toList frame.data
  have hk := Kind.ofUInt8?_toUInt8 frame.kind
  have hread : Encoding.ByteReader.bytes (YamuxError.truncated frame.dataSize) frame.dataSize
      (frame.data.data.toList ++ rest) = .ok (frame.data.data.toList, rest) := by
    rw [← hv, ← hl]; exact Encoding.ByteReader.bytes_append _ _ _
  simp only [decode, encode, hA, hB, hC, headerSize]
  simp [hA', hB', hC', hk]
  simp only [Frame.dataSize] at hread
  rw [hread]
  simp only [Functor.map, Except.map, hba]

/-- A decoded frame is valid, and the input is its encoding followed by the rest. -/
theorem encode_decode {bytes rest : List UInt8} {frame : Frame}
    (h : decode bytes = .ok (frame, rest)) : frame.Valid ∧ encode frame ++ rest = bytes := by
  by_cases hs : bytes.length < 12
  · have hm : min 12 bytes.length < 12 := by omega
    simp [decode, headerSize, hm, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  have hlen : (bytes.take 12).length = 12 := by simp; omega
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, hx⟩ :
      ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt8,
        bytes.take 12 = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] := by
    match hm : bytes.take 12, hlen with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], _ =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  have hb : bytes = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] ++ bytes.drop 12 := by
    rw [← hx, List.take_append_drop]
  simp only [decode, headerSize, hx] at h
  have e0 : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11].getD 0 0 = x0 := rfl
  have e1 : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11].getD 1 0 = x1 := rfl
  have e2 : (List.take 2 (List.drop 2 [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11])) =
      [x2, x3] := rfl
  have e3 : (List.take 4 (List.drop 4 [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11])) =
      [x4, x5, x6, x7] := rfl
  have e4 : (List.drop 8 [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]) =
      [x8, x9, x10, x11] := rfl
  simp only [e0, e1, e2, e3, e4] at h
  have hv0 : x0 = 0 := Decidable.byContradiction fun hv0 => by
    simp [hv0, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  cases hk : Kind.ofUInt8? x1 with
  | none => simp [hv0, hk, throw, throwThe, MonadExceptOf.throw] at h
  | some kind =>
    have hk' := Kind.toUInt8_of_ofUInt8? hk
    simp only [hv0, hk, ne_eq, not_true_eq_false, ite_false] at h
    generalize hn : (if kind = Kind.data then
        (ByteOrder.ofBE [x8, x9, x10, x11]).toUInt32.toNat else 0) = n at h
    cases hread : Encoding.ByteReader.bytes (YamuxError.truncated n) n (List.drop 12 bytes) with
    | error err => simp [hread, Functor.map, Except.map] at h
    | ok p =>
      obtain ⟨field, after⟩ := p
      obtain ⟨hl, hsplit⟩ := (Encoding.ByteReader.bytes_ok_iff _ _ _ _ _).mp hread
      simp only [hread] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · show (⟨field.toArray⟩ : ByteArray).size = _
        show field.toArray.size = _
        rw [List.size_toArray, hl, ← hn]
        rfl
      · simp only [encode, hk', toBE_toUInt16, toBE_toUInt32]
        rw [hsplit] at hb
        rw [hb]
        simp [hv0]
