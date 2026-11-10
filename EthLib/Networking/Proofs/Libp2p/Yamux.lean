module

public import EthLib.Networking.Libp2p.Yamux
public import EthLib.Base.Proofs.BigEndian

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
  simp [encode, headerSize, natToBytes_length, hl]
  omega

/-- The bytes of a number on two bytes are two bytes. -/
private theorem natToBytes_two (n : Nat) : ∃ a b, natToBytes 2 n = [a, b] := by
  have h := natToBytes_length 2 n
  match hl : natToBytes 2 n, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- The bytes of a number on four bytes are four bytes. -/
private theorem natToBytes_four (n : Nat) : ∃ a b c d, natToBytes 4 n = [a, b, c, d] := by
  have h := natToBytes_length 4 n
  match hl : natToBytes 4 n, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- Two bytes survive reading them as a 16-bit value and writing that value back. -/
private theorem natToBytes_toUInt16 (a b : UInt8) :
    natToBytes 2 (bytesToNat [a, b]).toUInt16.toNat = [a, b] := by
  have hlt := bytesToNat_lt [a, b]
  simp only [List.length_cons, List.length_nil] at hlt
  have hv : (bytesToNat [a, b]).toUInt16.toNat = bytesToNat [a, b] := by
    rw [Nat.toUInt16, UInt16.toNat_ofNat_of_lt' (by simp only [UInt16.size]; omega)]
  rw [hv]
  simpa using natToBytes_bytesToNat [a, b]

/-- Four bytes survive reading them as a 32-bit value and writing that value back. -/
private theorem natToBytes_toUInt32 (a b c d : UInt8) :
    natToBytes 4 (bytesToNat [a, b, c, d]).toUInt32.toNat = [a, b, c, d] := by
  have hlt := bytesToNat_lt [a, b, c, d]
  simp only [List.length_cons, List.length_nil] at hlt
  have hv : (bytesToNat [a, b, c, d]).toUInt32.toNat = bytesToNat [a, b, c, d] := by
    rw [Nat.toUInt32, UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
  rw [hv]
  simpa using natToBytes_bytesToNat [a, b, c, d]

/-- Decoding the encoding of a valid frame, then any bytes, returns the frame and those bytes. -/
theorem decode_encode {frame : Frame} (h : frame.Valid) (rest : List UInt8) :
    decode (encode frame ++ rest) = .ok (frame, rest) := by
  obtain ⟨a0, a1, hA⟩ := natToBytes_two frame.flags.toNat
  obtain ⟨b0, b1, b2, b3, hB⟩ := natToBytes_four frame.streamId.toNat
  obtain ⟨c0, c1, c2, c3, hC⟩ := natToBytes_four frame.length.toNat
  have hl : frame.data.data.toList.length = frame.data.size :=
    Array.length_toList
  have hA' := bytesToNat_natToBytes_of_lt (len := 2) (n := frame.flags.toNat)
    (by have := frame.flags.toNat_lt; simpa using this)
  have hB' := bytesToNat_natToBytes_of_lt (len := 4) (n := frame.streamId.toNat)
    (by have := frame.streamId.toNat_lt; simpa using this)
  have hC' := bytesToNat_natToBytes_of_lt (len := 4) (n := frame.length.toNat)
    (by have := frame.length.toNat_lt; simpa using this)
  rw [hA] at hA'
  rw [hB] at hB'
  rw [hC] at hC'
  have hv : frame.data.size = frame.dataSize := h
  have hba : (⟨frame.data.data.toList.toArray⟩ : ByteArray) = frame.data := by
    cases frame.data
    rfl
  have hk := Kind.ofUInt8?_toUInt8 frame.kind
  have hr : (frame.data.data.toList ++ rest).take frame.dataSize = frame.data.data.toList := by
    rw [← hv, ← hl]; simp
  have hdr : (frame.data.data.toList ++ rest).drop frame.dataSize = rest := by
    rw [← hv, ← hl]; simp
  have hnr : ¬ (frame.data.data.toList ++ rest).length < frame.dataSize := by
    simp only [List.length_append, hl]; omega
  simp only [decode, encode, hA, hB, hC, headerSize]
  simp [hA', hB', hC', hk, hl, hv, hba, Frame.dataSize]
  rfl

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
        (bytesToNat [x8, x9, x10, x11]).toUInt32.toNat else 0) = n at h
    by_cases hr : (List.take n (List.drop 12 bytes)).length < n
    · simp only [hr, ↓reduceIte] at h; cases h
    simp only [hr, ↓reduceIte, pure, Except.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl : (List.take n (List.drop 12 bytes)).length = n := by
      have := List.length_take_le n (List.drop 12 bytes); omega
    refine ⟨?_, ?_⟩
    · show (⟨(List.take n (List.drop 12 bytes)).toArray⟩ : ByteArray).size = _
      show (List.take n (List.drop 12 bytes)).toArray.size = _
      rw [List.size_toArray, hl, ← hn]
      rfl
    · simp only [encode, hk', natToBytes_toUInt16, natToBytes_toUInt32]
      rw [List.append_assoc _ (List.take n _), List.take_append_drop]
      exact Eq.trans (by simp [hv0]) hb.symm
