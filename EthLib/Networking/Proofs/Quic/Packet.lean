module

public import EthLib.Networking.Quic.Packet
public import EthLib.Networking.Proofs.Quic.Wire
public import Mathlib.Tactic.SplitIfs

/-!
# Proofs: QUIC packet headers

The packet-number encoder keeps exactly the low bytes of the number.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Packet

open Wire

/-- The truncated packet number is the original number modulo the selected window. -/
theorem bytesToNat_encodePacketNumber (width : PacketNumberLength) (number : Varint) :
    Base.bytesToNat (encodePacketNumber width number) =
      number.val % 256 ^ numberLength width :=
  Base.bytesToNat_natToBytes _ _

/-- Packet-number encoding uses exactly the byte count selected by its two-bit length. -/
theorem length_encodePacketNumber (width : PacketNumberLength) (number : Varint) :
    (encodePacketNumber width number).length = numberLength width :=
  Base.natToBytes_length _ _

/-- Unsigned distance between packet numbers. -/
def distance (a b : Nat) : Nat := a - b + (b - a)

/-- Reading a length-prefixed connection ID recovers it and the following bytes. -/
theorem connectionId_encode (cid rest : List UInt8) (maximum : Nat)
    (hcid : cid.length ≤ maximum) (hmaximum : maximum < 256) :
    connectionId maximum (UInt8.ofNat cid.length :: (cid ++ rest)) = .ok (cid, rest) := by
  have hbyte : (UInt8.ofNat cid.length).toNat = cid.length := by
    exact UInt8.toNat_ofNat_of_lt' (by simpa only [UInt8.size] using (by omega : cid.length < 256))
  simp only [bind, connectionId, StateT.bind, Except.bind,
    byte, hbyte, require, hcid, ↓reduceIte, bytes, List.take_left, List.drop_left]

/-- Reading the length and packet number undoes their encoding. -/
theorem lengthAndNumber_encode (width : PacketNumberLength) (length : Varint)
    (number : Nat) (rest : List UInt8) (hl : numberLength width ≤ length.val)
    (hn : number < 256 ^ numberLength width) :
    lengthAndNumber width
      (Varint.encode length ++ (Base.natToBytes (numberLength width) number ++ rest)) =
      .ok ((length, number), rest) := by
  simp only [bind, pure, lengthAndNumber, StateT.bind, StateT.pure, Except.bind, Except.pure,
    varint_encode, require, hl, uint_encode, Nat.mod_eq_of_lt hn, ↓reduceIte]

/-- Reading an Initial header recovers its fields and leaves the payload untouched. -/
theorem decode_initial (d s t rest : List UInt8) (w : PacketNumberLength)
    (l : Varint) (n : Nat) (hd : d.length ≤ 20) (hs : s.length ≤ 20)
    (ht : t.length < 2 ^ 62) (hl : numberLength w ≤ l.val)
    (hn : n < 256 ^ numberLength w) (shortLength : Nat) :
    decode shortLength (longPrefix (UInt8.ofNat (192 + w.val)) 1 d s ++
      Varint.encode ⟨t.length, ht⟩ ++ t ++ Varint.encode l ++
        Base.natToBytes (numberLength w) n ++ rest) =
      .ok (.initial d s t w l n, rest) := by
  have hw := w.isLt
  have hf : (UInt8.ofNat (192 + w.val)).toNat = 192 + w.val :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have hm : (192 + w.val) % 4 = w.val := by omega
  have hf128 : ¬192 + w.val < 128 := by omega
  have hf64 : (192 + w.val) / 64 % 2 = 1 := by omega
  have hf16 : (192 + w.val) / 16 % 4 = 0 := by omega
  have hf4 : (192 + w.val) / 4 % 4 = 0 := by omega
  simp only [show (1 : Nat) ≠ 0 by decide, show (0 : Nat) ≠ 3 by decide,
    decode, widthOfFirst, longPrefix, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure,
    Except.bind, Except.pure, byte, hf, hm, hf128, ↓reduceIte,
    uint_encode, Nat.one_mod, connectionId_encode _ _ 20 hd (by decide),
    connectionId_encode _ _ 20 hs (by decide), require, hf64, hf16, hf4,
    Fin.eta, blob_encode, lengthAndNumber_encode _ _ _ _ hl hn]

/-- Reading a 0-RTT header recovers its fields and leaves the payload untouched. -/
theorem decode_zeroRtt (d s rest : List UInt8) (w : PacketNumberLength)
    (l : Varint) (n : Nat) (hd : d.length ≤ 20) (hs : s.length ≤ 20)
    (hl : numberLength w ≤ l.val)
    (hn : n < 256 ^ numberLength w) (shortLength : Nat) :
    decode shortLength (longPrefix (UInt8.ofNat (208 + w.val)) 1 d s ++
      Varint.encode l ++
        Base.natToBytes (numberLength w) n ++ rest) =
      .ok (.zeroRtt d s w l n, rest) := by
  have hw := w.isLt
  have hf : (UInt8.ofNat (208 + w.val)).toNat = 208 + w.val :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have hm : (208 + w.val) % 4 = w.val := by omega
  have hf128 : ¬208 + w.val < 128 := by omega
  have hf64 : (208 + w.val) / 64 % 2 = 1 := by omega
  have hf16 : (208 + w.val) / 16 % 4 = 1 := by omega
  have hf4 : (208 + w.val) / 4 % 4 = 0 := by omega
  simp only [show (1 : Nat) ≠ 0 by decide, show (1 : Nat) ≠ 3 by decide,
    decode, widthOfFirst, longPrefix, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure,
    Except.bind, Except.pure, byte, hf, hm, hf128, ↓reduceIte,
    uint_encode, Nat.one_mod, connectionId_encode _ _ 20 hd (by decide),
    connectionId_encode _ _ 20 hs (by decide), require, hf64, hf16, hf4,
    Fin.eta, lengthAndNumber_encode _ _ _ _ hl hn, ↓reduceIte]

/-- Reading a Handshake header recovers its fields and leaves the payload untouched. -/
theorem decode_handshake (d s rest : List UInt8) (w : PacketNumberLength)
    (l : Varint) (n : Nat) (hd : d.length ≤ 20) (hs : s.length ≤ 20)
    (hl : numberLength w ≤ l.val)
    (hn : n < 256 ^ numberLength w) (shortLength : Nat) :
    decode shortLength (longPrefix (UInt8.ofNat (224 + w.val)) 1 d s ++
      Varint.encode l ++
        Base.natToBytes (numberLength w) n ++ rest) =
      .ok (.handshake d s w l n, rest) := by
  have hw := w.isLt
  have hf : (UInt8.ofNat (224 + w.val)).toNat = 224 + w.val :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have hm : (224 + w.val) % 4 = w.val := by omega
  have hf128 : ¬224 + w.val < 128 := by omega
  have hf64 : (224 + w.val) / 64 % 2 = 1 := by omega
  have hf16 : (224 + w.val) / 16 % 4 = 2 := by omega
  have hf4 : (224 + w.val) / 4 % 4 = 0 := by omega
  simp only [show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 3 by decide,
    show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
    decode, widthOfFirst, longPrefix, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure,
    Except.bind, Except.pure, byte, hf, hm, hf128, ↓reduceIte,
    uint_encode, Nat.one_mod, connectionId_encode _ _ 20 hd (by decide),
    connectionId_encode _ _ 20 hs (by decide), require, hf64, hf16, hf4,
    Fin.eta, lengthAndNumber_encode _ _ _ _ hl hn, ↓reduceIte]

/-- Reading a short header recovers the spin bit, key phase and packet-number bytes. -/
theorem decode_oneRtt (d rest : List UInt8) (spin keyPhase : Bool)
    (w : PacketNumberLength) (n : Nat) (hd : d.length ≤ 20)
    (hn : n < 256 ^ numberLength w) :
    decode d.length ([UInt8.ofNat (64 + (if spin then 32 else 0) +
      (if keyPhase then 4 else 0) + w.val)] ++ d ++
      Base.natToBytes (numberLength w) n ++ rest) =
      .ok (.oneRtt d spin keyPhase w n, rest) := by
  let first := 64 + (if spin then 32 else 0) + (if keyPhase then 4 else 0) + w.val
  have hw := w.isLt
  have hfirst : (UInt8.ofNat first).toNat = first := by
    apply UInt8.toNat_ofNat_of_lt'
    simp only [UInt8.size]
    dsimp only [first]
    cases spin <;> cases keyPhase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hm : first % 4 = w.val := by
    dsimp only [first]
    cases spin <;> cases keyPhase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hf128 : first < 128 := by
    dsimp only [first]
    cases spin <;> cases keyPhase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hf64 : first / 64 = 1 := by
    dsimp only [first]
    cases spin <;> cases keyPhase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hf8 : first / 8 % 4 = 0 := by
    dsimp only [first]
    cases spin <;> cases keyPhase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hspin : decide (first / 32 % 2 = 1) = spin := by
    dsimp only [first]
    cases spin <;> cases keyPhase <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.false_eq_true, iff_false, iff_true]
      omega
  have hkey : decide (first / 4 % 2 = 1) = keyPhase := by
    dsimp only [first]
    cases spin <;> cases keyPhase <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.false_eq_true, iff_false, iff_true]
      omega
  change decode d.length ([UInt8.ofNat first] ++ d ++
    Base.natToBytes (numberLength w) n ++ rest) = _
  simp only [decode, widthOfFirst, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure, byte,
    hfirst, hm, hf128, ↓reduceIte, Fin.eta, require, hf64, hf8, hd,
    bytes_append, uint_encode, Nat.mod_eq_of_lt hn, hspin, hkey]

/-- Retry decoding separates the token from the final 16-byte integrity tag (§17.2.5). -/
theorem decode_retry (d s t : List UInt8) (tag : Vector UInt8 16) (unused : Fin 16)
    (hd : d.length ≤ 20) (hs : s.length ≤ 20) (ht : t ≠ []) (shortLength : Nat) :
    decode shortLength
      (longPrefix (UInt8.ofNat (240 + unused.val)) 1 d s ++ t ++ tag.toList) =
      .ok (.retry d s t tag unused, []) := by
  have hu := unused.isLt
  have hf : (UInt8.ofNat (240 + unused.val)).toNat = 240 + unused.val :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have hf128 : ¬240 + unused.val < 128 := by omega
  have hf64 : (240 + unused.val) / 64 % 2 = 1 := by omega
  have hf16 : (240 + unused.val) / 16 % 4 = 3 := by omega
  have hm : (240 + unused.val) % 16 = unused.val := by omega
  have htag : tag.toList.length = 16 := by simp
  have hlength : 16 < (t ++ tag.toList).length := by
    have : 0 < t.length := List.length_pos_iff.mpr ht
    simp only [List.length_append, htag]
    omega
  have hsplit : (t ++ tag.toList).length - 16 = t.length := by
    simp only [List.length_append, htag, Nat.add_sub_cancel]
  simp only [decode, longPrefix, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure, byte, hf,
    hf128, ↓reduceIte, uint_encode, Nat.one_mod, show (1 : Nat) ≠ 0 by decide,
    connectionId_encode _ _ 20 hd (by decide), connectionId_encode _ _ 20 hs (by decide),
    require, hf64, hf16, remainder, hlength, hsplit, List.take_left, List.drop_left,
    htag, ↓reduceDIte, hm, Fin.eta, Vector.toArray_toList, Vector.mk_toArray]

/-- Reading four version bytes recovers a version and then reads the remaining versions. -/
private theorem versions_word (version : UInt32) (rest : List UInt8) :
    versions (Base.natToBytes 4 version.toNat ++ rest) =
      (versions rest).map (version :: ·) := by
  have hword : UInt32.ofNat (Base.bytesToNat (Base.natToBytes 4 version.toNat)) = version := by
    rw [Base.bytesToNat_natToBytes, Nat.mod_eq_of_lt version.toNat_lt]
    exact UInt32.ofNat_toNat
  simp only [Base.natToBytes, Base.natToBytes.go, List.cons_append, List.nil_append,
    versions]
  cases result : versions rest with
  | error error => rfl
  | ok tail =>
    change Except.ok (UInt32.ofNat (Base.bytesToNat (Base.natToBytes 4 version.toNat)) :: tail) =
      Except.ok (version :: tail)
    rw [hword]

/-- A sequence of supported versions round trips (§17.2.1). -/
theorem versions_encode (values : List UInt32) :
    versions (values.flatMap fun v => Base.natToBytes 4 v.toNat) = .ok values := by
  induction values with
  | nil => rfl
  | cons value tail ih =>
    simp only [List.flatMap_cons, versions_word, ih, Except.map]

/-- Version Negotiation decoding preserves arbitrary unused bits and both connection IDs. -/
theorem decode_versionNegotiation (d s : List UInt8) (unused : Fin 128)
    (vs : List UInt32) (hd : d.length ≤ 255) (hs : s.length ≤ 255) (shortLength : Nat) :
    decode shortLength (longPrefix (UInt8.ofNat (128 + unused.val)) 0 d s ++
      vs.flatMap (fun v => Base.natToBytes 4 v.toNat)) =
      .ok (.versionNegotiation d s unused vs, []) := by
  have hu := unused.isLt
  have hf : (UInt8.ofNat (128 + unused.val)).toNat = 128 + unused.val :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have hf128 : ¬128 + unused.val < 128 := by omega
  have hm : (128 + unused.val) % 128 = unused.val := by omega
  simp only [decode, longPrefix, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure, byte, hf,
    hf128, ↓reduceIte, uint_encode, Nat.zero_mod, show (0 : Nat) ≠ 1 by decide,
    connectionId_encode _ _ 255 hd (by decide), connectionId_encode _ _ 255 hs (by decide),
    remainder, StateT.lift, versions_encode, hm, Fin.eta]

/-- The connection supplies only a short header's destination-ID length. -/
def shortConnectionIdLength : Header → Nat
  | .oneRtt destination _ _ _ _ => destination.length
  | _ => 0

/-- Retry and Version Negotiation exhaust their containing datagram. -/
def permitsFollowing (header : Header) (rest : List UInt8) : Prop :=
  match header with
  | .retry .. | .versionNegotiation .. => rest = []
  | _ => True

/-- Every well-formed header round trips, preserving bytes after a protected header. -/
theorem decode_encode (header : Header) (encoded rest : List UInt8)
    (valid : header.Valid) (written : encode header = .ok encoded)
    (follows : permitsFollowing header rest) :
    decode (shortConnectionIdLength header) (encoded ++ rest) = .ok (header, rest) := by
  have checked : ¬¬header.Valid := not_not_intro valid
  cases header with
  | initial d s t w l n =>
    rcases valid with ⟨hd, hs, ht, hl, hn⟩
    simp only [encode, checked, ↓reduceIte, checkedVarint, ht, ↓reduceDIte,
      bind, pure, Except.bind, Except.pure, Except.ok.injEq] at written
    subst encoded
    exact decode_initial d s t rest w l n hd hs ht hl hn 0
  | zeroRtt d s w l n =>
    rcases valid with ⟨hd, hs, hl, hn⟩
    simp only [encode, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    exact decode_zeroRtt d s rest w l n hd hs hl hn 0
  | handshake d s w l n =>
    rcases valid with ⟨hd, hs, hl, hn⟩
    simp only [encode, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    exact decode_handshake d s rest w l n hd hs hl hn 0
  | oneRtt d spin keyPhase w n =>
    rcases valid with ⟨hd, hn⟩
    simp only [encode, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    exact decode_oneRtt d rest spin keyPhase w n hd hn
  | retry d s t tag unused =>
    rcases valid with ⟨hd, hs, ht⟩
    simp only [encode, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    subst rest
    simpa only [List.append_nil, shortConnectionIdLength] using
      decode_retry d s t tag unused hd hs ht 0
  | versionNegotiation d s unused vs =>
    rcases valid with ⟨hd, hs⟩
    simp only [encode, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    subst rest
    simpa only [List.append_nil, shortConnectionIdLength] using
      decode_versionNegotiation d s unused vs hd hs 0

/-- A reconstructed number is at least as close to the expectation as any valid alternative.

The alternatives have the same truncated bytes and remain below the packet-number limit.
-/
theorem decodePacketNumber_closest (w : PacketNumberLength) (truncated expected result other : Nat)
    (decoded : decodePacketNumber w truncated expected = .ok result)
    (bounded : other < 2 ^ 62)
    (sameBytes : other % 256 ^ numberLength w = truncated) :
    distance result expected ≤ distance other expected := by
  rcases w with ⟨w, hw⟩
  have casesWidth : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  rcases casesWidth with rfl | rfl | rfl | rfl
  all_goals
    simp only [decodePacketNumber, numberLength, Nat.reduceAdd, Nat.reducePow,
      bind, pure, Except.bind, Except.pure] at decoded sameBytes
    repeat' (split_ifs at decoded <;> simp_all [throw, throwThe])
    all_goals unfold distance; omega

/-- A reconstructed packet number keeps the received low bytes (Appendix A.3). -/
theorem decodePacketNumber_mod (w : PacketNumberLength) (truncated expected result : Nat)
    (decoded : decodePacketNumber w truncated expected = .ok result) :
    result % 256 ^ numberLength w = truncated := by
  rcases w with ⟨w, hw⟩
  have casesWidth : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  rcases casesWidth with rfl | rfl | rfl | rfl
  all_goals
    simp only [decodePacketNumber, numberLength, Nat.reduceAdd, Nat.reducePow,
      bind, pure, Except.bind, Except.pure] at decoded ⊢
    repeat' (split_ifs at decoded <;> simp_all [throw, throwThe])
    all_goals omega

/-- A reconstructed packet number is below `2^62` (§12.3). -/
theorem decodePacketNumber_lt (w : PacketNumberLength) (truncated expected result : Nat)
    (decoded : decodePacketNumber w truncated expected = .ok result) : result < 2 ^ 62 := by
  simp only [decodePacketNumber, bind, pure, Except.bind, Except.pure] at decoded
  repeat' (split_ifs at decoded <;> simp_all)

end EthLib.Networking.Quic.Packet
