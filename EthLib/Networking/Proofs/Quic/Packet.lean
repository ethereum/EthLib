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
open EthLib.Networking.Encoding.ByteReader (bytes_append uint_encode require_true)

/-- The truncated packet number is the original number modulo the selected window. -/
theorem bytesToNat_encodePacketNumberList (width : PacketNumberLength) (number : Varint) :
    Base.bytesToNat (encodePacketNumberList width number) =
      number.val % 256 ^ numberLength width :=
  Base.bytesToNat_natToBytes _ _

/-- Packet-number encoding uses exactly the byte count selected by its two-bit length. -/
theorem length_encodePacketNumberList (width : PacketNumberLength) (number : Varint) :
    (encodePacketNumberList width number).length = numberLength width :=
  Base.natToBytes_length _ _

/-- A width's range holds the full number before any acknowledgement, or exceeds twice the gap. -/
def WidthSufficient (number : Varint) (largestAcked : Option Varint)
    (width : PacketNumberLength) : Prop :=
  match largestAcked with
  | none => number.val < 256 ^ numberLength width
  | some ack => ack.val < number.val ∧
      2 * (number.val - ack.val) < 256 ^ numberLength width

/-- Every width returned by the selector meets its packet-number bound. -/
theorem packetNumberWidth_sufficient (number : Varint) (largestAcked : Option Varint)
    (width : PacketNumberLength) (selected : packetNumberWidth number largestAcked = .ok width) :
    WidthSufficient number largestAcked width := by
  rcases width with ⟨w, hw⟩
  have casesWidth : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  rcases casesWidth with rfl | rfl | rfl | rfl
  all_goals
    cases largestAcked <;>
      simp [packetNumberWidth, WidthSufficient, numberLength, pure, Except.pure,
        bind, Except.bind, throw, throwThe] at selected ⊢
    all_goals split_ifs at selected <;> simp_all

/-- The selector returns no more bytes than any sufficient width. -/
theorem packetNumberWidth_minimal (number : Varint) (largestAcked : Option Varint)
    (width other : PacketNumberLength)
    (selected : packetNumberWidth number largestAcked = .ok width)
    (sufficient : WidthSufficient number largestAcked other) : width.val ≤ other.val := by
  rcases width with ⟨w, hw⟩
  rcases other with ⟨o, ho⟩
  have casesWidth : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  have casesOther : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
  rcases casesWidth with rfl | rfl | rfl | rfl
  all_goals rcases casesOther with rfl | rfl | rfl | rfl
  all_goals
    cases largestAcked <;>
      simp [packetNumberWidth, WidthSufficient, numberLength, pure, Except.pure,
        bind, Except.bind, throw, throwThe] at selected sufficient ⊢
    all_goals split_ifs at selected <;> simp_all

/-- Selection fails exactly when none of the four widths meets its packet-number bound. -/
theorem packetNumberWidth_error_iff (number : Varint) (largestAcked : Option Varint) :
    (∃ error, packetNumberWidth number largestAcked = .error error) ↔
      ∀ width, ¬WidthSufficient number largestAcked width := by
  constructor
  · rintro ⟨error, rejected⟩ width sufficient
    rcases width with ⟨w, hw⟩
    have casesWidth : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
    rcases casesWidth with rfl | rfl | rfl | rfl
    all_goals
      cases largestAcked <;>
        simp [packetNumberWidth, WidthSufficient, numberLength, pure, Except.pure,
        bind, Except.bind, throw, throwThe] at rejected sufficient
      all_goals split_ifs at rejected <;> solve | simp_all | omega
  · intro impossible
    cases selected : packetNumberWidth number largestAcked with
    | ok width => exact False.elim (impossible width
        (packetNumberWidth_sufficient number largestAcked width selected))
    | error error => exact ⟨error, rfl⟩

/-- An acknowledgement at or above the number being sent is rejected, with both numbers kept. -/
theorem packetNumberWidth_error_of_le (number ack : Varint) (order : number.val ≤ ack.val) :
    packetNumberWidth number (some ack) =
      .error (.acknowledgedNotEarlier number.val ack.val) := by
  simp [packetNumberWidth, order, throw, throwThe, bind, Except.bind]
  rfl

/-- Before any acknowledgement, the selected bytes retain the whole packet number. -/
theorem bytesToNat_encodePacketNumberList_of_packetNumberWidth_none (number : Varint)
    (width : PacketNumberLength) (selected : packetNumberWidth number none = .ok width) :
    Base.bytesToNat (encodePacketNumberList width number) = number.val := by
  rw [bytesToNat_encodePacketNumberList,
    Nat.mod_eq_of_lt (packetNumberWidth_sufficient number none width selected)]

/-- Unsigned distance between packet numbers. -/
def distance (a b : Nat) : Nat := a - b + (b - a)

/-- Reading a length-prefixed connection ID recovers it and the following bytes. -/
theorem connectionId_encode (cid : ByteArray) (rest : List UInt8) (maximum : Nat)
    (hcid : cid.size ≤ maximum) (hmaximum : maximum < 256) :
    connectionId maximum (UInt8.ofNat cid.size :: (cid.data.toList ++ rest)) = .ok (cid, rest) := by
  have hbyte : (UInt8.ofNat cid.size).toNat = cid.size := by
    exact UInt8.toNat_ofNat_of_lt' (by simpa only [UInt8.size] using (by omega : cid.size < 256))
  simp [connectionId, hbyte, hcid, bytes_byteArray_append,
    bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure,
    require, Encoding.ByteReader.require]


/-- Reading the length and packet number undoes their encoding. -/
theorem lengthAndNumber_encode (width : PacketNumberLength) (length : Varint)
    (number : Nat) (rest : List UInt8) (hl : numberLength width ≤ length.val)
    (hn : number < 256 ^ numberLength width) :
    lengthAndNumber width
      (Varint.encodeList length ++ (Base.natToBytes (numberLength width) number ++ rest)) =
      .ok ((length, number), rest) := by
  simp only [bind, pure, lengthAndNumber, StateT.bind, StateT.pure, Except.bind, Except.pure,
    varint_encode, require, Encoding.ByteReader.require, hl, uint_encode, Nat.mod_eq_of_lt hn,
    ↓reduceIte]

/-- Reading an Initial header recovers its fields and leaves the payload untouched. -/
theorem decodeList_initial (d s t : ByteArray) (rest : List UInt8) (w : PacketNumberLength)
    (l : Varint) (n : Nat) (hd : d.size ≤ 20) (hs : s.size ≤ 20)
    (ht : t.size < 2 ^ 62) (hl : numberLength w ≤ l.val)
    (hn : n < 256 ^ numberLength w) (shortLength : Nat) :
    decodeList shortLength (longPrefixList (UInt8.ofNat (192 + w.val)) 1 d s ++
      Varint.encodeList ⟨t.size, ht⟩ ++ t.data.toList ++ Varint.encodeList l ++
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
    decodeList, widthOfFirst, longPrefixList, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure,
    Except.bind, Except.pure, byte, hf, hm, hf128, ↓reduceIte,
    uint_encode, Nat.one_mod, connectionId_encode _ _ 20 hd (by decide),
    connectionId_encode _ _ 20 hs (by decide), require, Encoding.ByteReader.require, hf64, hf16,
    hf4, Fin.eta, blob_byteArray_encode, Base.toByteArray_data_toList,
    lengthAndNumber_encode _ _ _ _ hl hn]

/-- Reading a 0-RTT header recovers its fields and leaves the payload untouched. -/
theorem decodeList_zeroRtt (d s : ByteArray) (rest : List UInt8) (w : PacketNumberLength)
    (l : Varint) (n : Nat) (hd : d.size ≤ 20) (hs : s.size ≤ 20)
    (hl : numberLength w ≤ l.val)
    (hn : n < 256 ^ numberLength w) (shortLength : Nat) :
    decodeList shortLength (longPrefixList (UInt8.ofNat (208 + w.val)) 1 d s ++
      Varint.encodeList l ++
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
    decodeList, widthOfFirst, longPrefixList, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure,
    Except.bind, Except.pure, byte, hf, hm, hf128, ↓reduceIte,
    uint_encode, Nat.one_mod, connectionId_encode _ _ 20 hd (by decide),
    connectionId_encode _ _ 20 hs (by decide), require, Encoding.ByteReader.require, hf64, hf16,
    hf4, Fin.eta, lengthAndNumber_encode _ _ _ _ hl hn, ↓reduceIte]

/-- Reading a Handshake header recovers its fields and leaves the payload untouched. -/
theorem decodeList_handshake (d s : ByteArray) (rest : List UInt8) (w : PacketNumberLength)
    (l : Varint) (n : Nat) (hd : d.size ≤ 20) (hs : s.size ≤ 20)
    (hl : numberLength w ≤ l.val)
    (hn : n < 256 ^ numberLength w) (shortLength : Nat) :
    decodeList shortLength (longPrefixList (UInt8.ofNat (224 + w.val)) 1 d s ++
      Varint.encodeList l ++
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
    decodeList, widthOfFirst, longPrefixList, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure,
    Except.bind, Except.pure, byte, hf, hm, hf128, ↓reduceIte,
    uint_encode, Nat.one_mod, connectionId_encode _ _ 20 hd (by decide),
    connectionId_encode _ _ 20 hs (by decide), require, Encoding.ByteReader.require, hf64, hf16,
    hf4, Fin.eta, lengthAndNumber_encode _ _ _ _ hl hn, ↓reduceIte]

/-- Reading a short header recovers the spin bit, key phase and packet-number bytes. -/
theorem decodeList_oneRtt (d : ByteArray) (rest : List UInt8) (spin keyPhase : Bool)
    (w : PacketNumberLength) (n : Nat) (hd : d.size ≤ 20)
    (hn : n < 256 ^ numberLength w) :
    decodeList d.size ([UInt8.ofNat (64 + (if spin then 32 else 0) +
      (if keyPhase then 4 else 0) + w.val)] ++ d.data.toList ++
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
  change decodeList d.size ([UInt8.ofNat first] ++ d.data.toList ++
    Base.natToBytes (numberLength w) n ++ rest) = _
  simp only [decodeList, widthOfFirst, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure, byte,
    hfirst, hm, hf128, ↓reduceIte, Fin.eta, require, Encoding.ByteReader.require, hf64, hf8, hd,
    bytes_byteArray_append, Base.toByteArray_data_toList,
    uint_encode, Nat.mod_eq_of_lt hn, hspin, hkey]

/-- Retry decoding separates the token from the final 16-byte integrity tag (§17.2.5). -/
theorem decodeList_retry (d s t : ByteArray) (tag : Vector UInt8 16) (unused : Fin 16)
    (hd : d.size ≤ 20) (hs : s.size ≤ 20) (ht : t ≠ ByteArray.empty) (shortLength : Nat) :
    decodeList shortLength
      (longPrefixList (UInt8.ofNat (240 + unused.val)) 1 d s ++ t.data.toList ++ tag.toList) =
      .ok (.retry d s t tag unused, []) := by
  have hu := unused.isLt
  have hf : (UInt8.ofNat (240 + unused.val)).toNat = 240 + unused.val :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have hf128 : ¬240 + unused.val < 128 := by omega
  have hf64 : (240 + unused.val) / 64 % 2 = 1 := by omega
  have hf16 : (240 + unused.val) / 16 % 4 = 3 := by omega
  have hm : (240 + unused.val) % 16 = unused.val := by omega
  have htag : tag.toList.length = 16 := by simp
  have hlength : 16 < (t.data.toList ++ tag.toList).length := by
    have : 0 < t.size := by
      have nonempty : t.size ≠ 0 := fun empty => ht (ByteArray.size_eq_zero_iff.mp empty)
      omega
    simp only [List.length_append, Array.length_toList, htag]
    change 16 < t.size + 16
    omega
  have hsplit : (t.data.toList ++ tag.toList).length - 16 = t.size := by
    simp only [List.length_append, Array.length_toList, htag, Nat.add_sub_cancel]
    rfl
  have htake : (t.data.toList ++ tag.toList).take t.size = t.data.toList := by
    simp
  have hdrop : (t.data.toList ++ tag.toList).drop t.size = tag.toList := by
    simp
  simp only [decodeList, longPrefixList, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure, byte, hf,
    hf128, ↓reduceIte, uint_encode, Nat.one_mod, show (1 : Nat) ≠ 0 by decide,
    connectionId_encode _ _ 20 hd (by decide), connectionId_encode _ _ 20 hs (by decide),
    require, Encoding.ByteReader.require, hf64, hf16, remainder, hlength, hsplit, htake, hdrop,
    StateT.lift, Vector.toArray_toList, Base.exactArray_toArray, hm, Fin.eta,
    Base.toByteArray_data_toList]

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
theorem decodeList_versionNegotiation (d s : ByteArray) (unused : Fin 128)
    (vs : List UInt32) (hd : d.size ≤ 255) (hs : s.size ≤ 255) (shortLength : Nat) :
    decodeList shortLength (longPrefixList (UInt8.ofNat (128 + unused.val)) 0 d s ++
      vs.flatMap (fun v => Base.natToBytes 4 v.toNat)) =
      .ok (.versionNegotiation d s unused vs, []) := by
  have hu := unused.isLt
  have hf : (UInt8.ofNat (128 + unused.val)).toNat = 128 + unused.val :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have hf128 : ¬128 + unused.val < 128 := by omega
  have hm : (128 + unused.val) % 128 = unused.val := by omega
  simp only [decodeList, longPrefixList, List.append_assoc, List.cons_append, List.nil_append,
    bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure, byte, hf,
    hf128, ↓reduceIte, uint_encode, Nat.zero_mod, show (0 : Nat) ≠ 1 by decide,
    connectionId_encode _ _ 255 hd (by decide), connectionId_encode _ _ 255 hs (by decide),
    remainder, StateT.lift, versions_encode, hm, Fin.eta]

/-- The connection supplies only a short header's destination-ID length. -/
def shortConnectionIdLength : Header → Nat
  | .oneRtt destination _ _ _ _ => destination.size
  | _ => 0

/-- Retry and Version Negotiation exhaust their containing datagram. -/
def permitsFollowingList (header : Header) (rest : List UInt8) : Prop :=
  match header with
  | .retry .. | .versionNegotiation .. => rest = []
  | _ => True

/-- Every well-formed header round trips, preserving bytes after a protected header. -/
theorem decodeList_encodeList (header : Header) (encoded rest : List UInt8)
    (valid : header.Valid) (written : encodeList header = .ok encoded)
    (follows : permitsFollowingList header rest) :
    decodeList (shortConnectionIdLength header) (encoded ++ rest) = .ok (header, rest) := by
  have checked : ¬¬header.Valid := not_not_intro valid
  cases header with
  | initial d s t w l n =>
    rcases valid with ⟨hd, hs, ht, hl, hn⟩
    simp only [encodeList, checked, ↓reduceIte, checkedVarint, ht, ↓reduceDIte,
      bind, pure, Except.bind, Except.pure, Except.ok.injEq] at written
    subst encoded
    exact decodeList_initial d s t rest w l n hd hs ht hl hn 0
  | zeroRtt d s w l n =>
    rcases valid with ⟨hd, hs, hl, hn⟩
    simp only [encodeList, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    exact decodeList_zeroRtt d s rest w l n hd hs hl hn 0
  | handshake d s w l n =>
    rcases valid with ⟨hd, hs, hl, hn⟩
    simp only [encodeList, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    exact decodeList_handshake d s rest w l n hd hs hl hn 0
  | oneRtt d spin keyPhase w n =>
    rcases valid with ⟨hd, hn⟩
    simp only [encodeList, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    exact decodeList_oneRtt d rest spin keyPhase w n hd hn
  | retry d s t tag unused =>
    rcases valid with ⟨hd, hs, ht⟩
    simp only [encodeList, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    subst rest
    simpa only [List.append_nil, shortConnectionIdLength] using
      decodeList_retry d s t tag unused hd hs ht 0
  | versionNegotiation d s unused vs =>
    rcases valid with ⟨hd, hs⟩
    simp only [encodeList, checked, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at written
    subst encoded
    subst rest
    simpa only [List.append_nil, shortConnectionIdLength] using
      decodeList_versionNegotiation d s unused vs hd hs 0

/-- The packet-number bytes retain exactly the low bytes of the original number. -/
theorem bytesToNat_encodePacketNumber (width : PacketNumberLength) (number : Varint) :
    Base.bytesToNat (encodePacketNumber width number).data.toList =
      number.val % 256 ^ numberLength width := by
  simpa [encodePacketNumber] using bytesToNat_encodePacketNumberList width number

/-- Packet-number encoding uses exactly the selected byte count. -/
theorem size_encodePacketNumber (width : PacketNumberLength) (number : Varint) :
    (encodePacketNumber width number).size = numberLength width := by
  simpa [encodePacketNumber] using length_encodePacketNumberList width number

/-- Encoding to a byte array preserves the list encoder's result. -/
theorem encode_ok_iff (header : Header) (encoded : ByteArray) :
    encode header = .ok encoded ↔ encodeList header = .ok encoded.data.toList := by
  cases written : encodeList header with
  | error error => simp [encode, written, Except.map]
  | ok data =>
    simp only [encode, written, Except.map, Except.ok.injEq]
    constructor
    · intro same
      simpa using congrArg (fun bytes : ByteArray => bytes.data.toList) same
    · intro same
      rw [same, Base.toByteArray_data_toList]

/-- Decoding a byte array preserves the list reader's result and suffix. -/
theorem decode_ok_iff (shortLength : Nat) (input rest : ByteArray) (header : Header) :
    decode shortLength input = .ok (header, rest) ↔
      decodeList shortLength input.data.toList = .ok (header, rest.data.toList) := by
  cases read : decodeList shortLength input.data.toList with
  | error error => simp [decode, read, Except.map]
  | ok result =>
    rcases result with ⟨value, trailing⟩
    simp only [decode, read, Except.map, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, same⟩
      exact ⟨rfl, by simpa using congrArg (fun bytes : ByteArray => bytes.data.toList) same⟩
    · rintro ⟨rfl, same⟩
      exact ⟨rfl, by rw [same, Base.toByteArray_data_toList]⟩

/-- Retry and Version Negotiation exhaust their containing datagram. -/
def permitsFollowing (header : Header) (rest : ByteArray) : Prop :=
  match header with
  | .retry .. | .versionNegotiation .. => rest = ByteArray.empty
  | _ => True

/-- Every well-formed header round trips, preserving bytes after a protected header. -/
theorem decode_encode (header : Header) (encoded rest : ByteArray)
    (valid : header.Valid) (written : encode header = .ok encoded)
    (follows : permitsFollowing header rest) :
    decode (shortConnectionIdLength header) (encoded ++ rest) = .ok (header, rest) := by
  have writtenList := (encode_ok_iff header encoded).mp written
  have followsList : permitsFollowingList header rest.data.toList := by
    cases header <;> simp_all [permitsFollowing, permitsFollowingList]
  apply (decode_ok_iff _ _ _ _).mpr
  simpa [ByteArray.data_append] using
    decodeList_encodeList header encoded.data.toList rest.data.toList valid writtenList followsList

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

/-- A sufficient width recovers the number at every expectation its receiver can hold.

The receiver is assumed to hold the acknowledged packet, if any, and no packet from this number on.

Its expectation lies from one past the acknowledged number, or zero, through this number. -/
theorem decodePacketNumber_encodePacketNumberList_of_sufficient (number : Varint)
    (largestAcked : Option Varint) (width : PacketNumberLength)
    (sufficient : WidthSufficient number largestAcked width) (expected : Nat)
    (afterAcknowledged : largestAcked.elim 0 (fun ack => ack.val + 1) ≤ expected)
    (atMost : expected ≤ number.val) :
    decodePacketNumber width (Base.bytesToNat (encodePacketNumberList width number)) expected =
      .ok number.val := by
  rw [bytesToNat_encodePacketNumberList]
  have bounded := number.isLt
  rcases width with ⟨w, hw⟩
  have casesWidth : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  rcases casesWidth with rfl | rfl | rfl | rfl
  all_goals
    cases largestAcked <;>
      simp only [WidthSufficient, Option.elim, numberLength, Nat.reduceAdd, Nat.reducePow]
        at sufficient afterAcknowledged
    all_goals
      simp only [decodePacketNumber, numberLength, Nat.reduceAdd, Nat.reducePow,
        pure, Except.pure, bind, Except.bind]
      repeat' (split_ifs <;> simp_all [throw, throwThe])
      all_goals omega

/-- The selected width recovers the number at every expectation its receiver can hold. -/
theorem decodePacketNumber_encodePacketNumberList_of_packetNumberWidth (number : Varint)
    (largestAcked : Option Varint) (width : PacketNumberLength)
    (selected : packetNumberWidth number largestAcked = .ok width) (expected : Nat)
    (afterAcknowledged : largestAcked.elim 0 (fun ack => ack.val + 1) ≤ expected)
    (atMost : expected ≤ number.val) :
    decodePacketNumber width (Base.bytesToNat (encodePacketNumberList width number)) expected =
      .ok number.val :=
  decodePacketNumber_encodePacketNumberList_of_sufficient number largestAcked width
    (packetNumberWidth_sufficient number largestAcked width selected) expected
    afterAcknowledged atMost

/-- The packed bytes of the selected width recover the number at the same expectations. -/
theorem decodePacketNumber_encodePacketNumber_of_packetNumberWidth (number : Varint)
    (largestAcked : Option Varint) (width : PacketNumberLength)
    (selected : packetNumberWidth number largestAcked = .ok width) (expected : Nat)
    (afterAcknowledged : largestAcked.elim 0 (fun ack => ack.val + 1) ≤ expected)
    (atMost : expected ≤ number.val) :
    decodePacketNumber width (Base.bytesToNat (encodePacketNumber width number).data.toList)
      expected = .ok number.val := by
  simpa [encodePacketNumber] using
    decodePacketNumber_encodePacketNumberList_of_packetNumberWidth number largestAcked width
      selected expected afterAcknowledged atMost

end EthLib.Networking.Quic.Packet
