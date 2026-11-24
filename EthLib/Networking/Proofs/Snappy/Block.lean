module

public import EthLib.Networking.Snappy.Block
public import EthLib.Base.Proofs.ByteList
public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Networking.Encoding.Varint
public import EthLib.Networking.Proofs.Encoding.Varint

/-!
# `Networking.Proofs.Snappy.Block`

Properties of Snappy block decompression, against `format_description.txt` of `google/snappy`:
<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

- The preamble is a little-endian varint, and it reads back every length up to 2^32 - 1 (§1).
- A copy writes exactly the bytes §2.2 describes, overlapping copies included.
- A block cannot start with a copy (§2).
- A block that decompresses yields exactly the length it declared, at most 2^32 - 1.
- Its first five bytes alone declare that length.
- The fuel that bounds the element loop never changes the result.
- A literal element appends its data to the output (§2.1).
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Block

open EthLib.Base (ByteOrder.ofLE ByteOrder.toLE)
open EthLib.Networking.Snappy

/-! ## The preamble (§1) -/

/-- The preamble reads back the varint of every length up to 2^32 - 1, whatever follows it. -/
theorem readPreamble_encode {n : Nat} (rest : List UInt8) (hn : n ≤ maxUncompressedLength) :
    readPreamble (EthLib.Networking.Encoding.Varint.encodeAux n preambleMaxLength ++ rest) =
      .ok (n, rest) := by
  have hn' : n < Encoding.Varint.groupSize ^ preambleMaxLength := by
    simp only [maxUncompressedLength] at hn
    simp only [Encoding.Varint.groupSize, Encoding.Varint.payloadBits, preambleMaxLength]
    omega
  have hlen := Encoding.Varint.length_encodeAux_le n preambleMaxLength
  have hidx := Encoding.Varint.findIdx_encodeAux rest (by decide) hn' hlen
  have hpos : 0 < (Encoding.Varint.encodeAux n preambleMaxLength).length :=
    List.length_pos_iff.mpr (Encoding.Varint.encodeAux_ne_nil (by decide))
  -- The last byte of the encoding lies inside the five-byte window.
  have hw : ((Encoding.Varint.encodeAux n preambleMaxLength ++ rest).take
      preambleMaxLength).findIdx (·.toNat < Encoding.Varint.continuation) <
      ((Encoding.Varint.encodeAux n preambleMaxLength ++ rest).take preambleMaxLength).length := by
    rw [List.length_take, List.length_append]
    omega
  rw [readPreamble]
  dsimp only
  simp only [hw, ↓reduceIte]
  rw [hidx, List.take_left' rfl, List.drop_left' rfl, Encoding.Varint.valueOf_encodeAux hn']
  simp only [show ¬ maxUncompressedLength < n by omega, ↓reduceIte]

/-- An accepted preamble declares at most 2^32 - 1 bytes. -/
theorem readPreamble_le {bs rest : List UInt8} {len : Nat}
    (h : readPreamble bs = .ok (len, rest)) : len ≤ maxUncompressedLength := by
  simp only [readPreamble] at h
  split at h
  · split at h
    · cases h
    · cases h; omega
  · split at h <;> cases h

/-- An accepted preamble declares the same length when read from the first five bytes alone. -/
theorem readPreamble_take {bs rest : List UInt8} {len : Nat}
    (h : readPreamble bs = .ok (len, rest)) :
    ∃ rest', readPreamble (bs.take preambleMaxLength) = .ok (len, rest') := by
  simp only [readPreamble, List.take_take, Nat.min_self] at h ⊢
  split at h
  · rename_i hlt
    -- The varint ends inside the window, so the window holds all of it.
    have hk : (bs.take preambleMaxLength).findIdx (·.toNat < Encoding.Varint.continuation) + 1 ≤
        preambleMaxLength := by
      have := List.length_take_le preambleMaxLength bs
      omega
    rw [Nat.min_eq_left hk]
    simp only [hlt, ↓reduceIte]
    split at h
    · cases h
    · rename_i hle
      cases h
      simp only [hle, ↓reduceIte]
      exact ⟨_, rfl⟩
  · split at h <;> cases h

/-! ## Copies (§2.2) -/

/-- A successful copy of `n` bytes lengthens the output by `n`. -/
theorem copyBytes_size {out out' : ByteArray} {offset n : Nat}
    (h : copyBytes out offset n = .ok out') : out'.size = out.size + n := by
  induction n generalizing out with
  | zero => cases h; simp
  | succ n ih =>
      rw [copyBytes] at h
      split at h
      · have := ih h
        simp only [ByteArray.size_push] at this
        omega
      · cases h

/-- A copy that reaches back no further than the output succeeds, and writes what §2.2 describes.

The result `r`:

- starts with the output `o` it was given,
- is `n` bytes longer,
- has each new byte equal to the byte `offset` places before it.

The last rule is read on the bytes already written, so a copy longer than its offset repeats itself.
-/
theorem copyBytes_spec {o : List UInt8} {offset : Nat} (n : Nat)
    (hpos : 0 < offset) (hle : offset ≤ o.length) :
    ∃ r, copyBytes o.toByteArray offset n = .ok r.toByteArray ∧ r.length = o.length + n ∧ o <+: r ∧
      ∀ (j : Nat) (hj : o.length ≤ j) (hjr : j < r.length),
        r[j] = r[j - offset]'(by omega) := by
  induction n generalizing o with
  | zero => exact ⟨o, rfl, rfl, List.prefix_refl o, fun j hj hjr => by omega⟩
  | succ n ih =>
      have hidx : o.length - offset < o.length := by omega
      have hmax : max offset 1 = offset := by omega
      -- Writing the byte `offset` back is appending it.
      obtain ⟨r, hr, hlen, hpre, hrep⟩ :=
        ih (o := o ++ [o[o.length - offset]]) (by simp; omega)
      refine ⟨r, ?_, ?_, ?_, ?_⟩
      · rw [copyBytes, dite_eq_left (by simpa [hmax] using hle)]
        simpa only [List.size_toByteArray, hmax, List.getElem_toByteArray, List.toByteArray_append,
          ByteArray.append_toByteArray_singleton] using hr
      · simp at hlen; omega
      · exact (List.prefix_append o _).trans hpre
      · intro j hj hjr
        rcases Nat.lt_or_ge j (o.length + 1) with hlt | hge
        -- The byte just appended.
        · have hjeq : j = o.length := by omega
          subst hjeq
          -- Both bytes lie in the prefix, where the new byte is the one `offset` back.
          have h1 : r[o.length] = (o ++ [o[o.length - offset]])[o.length]'(by simp) :=
            (hpre.getElem (by simp)).symm
          have h2 : r[o.length - offset] = (o ++ [o[o.length - offset]])[o.length - offset]'(by simp; omega) :=
            (hpre.getElem (by simp; omega)).symm
          rw [h1, h2]
          simp [List.getElem_append_left hidx]
        -- A later byte, by the induction hypothesis.
        · exact hrep j (by simp; omega) hjr

/-- A copy into an empty output fails, whatever its offset. -/
theorem copyBytes_nil {offset len : Nat} (hlen : 0 < len) :
    copyBytes ByteArray.empty offset len = .error (.copyOffsetTooLarge offset 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
  rw [copyBytes, dite_eq_right (by simp)]; rfl

/-- A copy reaching past the start of the output fails. -/
theorem copyBytes_tooLarge {out : ByteArray} {offset n : Nat}
    (hout : out.size < offset) :
    copyBytes out offset (n + 1) = .error (.copyOffsetTooLarge offset out.size) := by
  rw [copyBytes, dite_eq_right (by omega)]

/-! ## The element loop -/

/-- One more unit of fuel changes nothing once the fuel covers the input. -/
theorem decompressElements_succ_fuel (declared : Nat) (input : List UInt8) (out : ByteArray)
    {fuel : Nat} (h : input.length ≤ fuel) :
    decompressElements declared input out (fuel + 1) =
      decompressElements declared input out fuel := by
  induction fuel generalizing input out with
  | zero =>
      cases input with
      | nil => rfl
      | cons _ _ => simp at h
  | succ fuel ih =>
      cases input with
      | nil => rfl
      | cons tag rest =>
          simp only [List.length_cons] at h
          have hr : rest.length ≤ fuel := by omega
          -- Every recursive call reads a suffix of the rest.
          simp (disch := simp only [List.length_drop]; omega) only [decompressElements, ih]
          congr

/-- The element loop gives the same result for every fuel that covers the input. -/
theorem decompressElements_fuel (declared : Nat) (input : List UInt8) (out : ByteArray)
    {fuel : Nat} (h : input.length ≤ fuel) :
    decompressElements declared input out fuel =
      decompressElements declared input out input.length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [← Nat.add_assoc, decompressElements_succ_fuel declared input out (by omega),
        ih (by omega)]

/-- A first element that is a copy has nothing to copy from, so it is rejected (§2). -/
theorem decompressElements_copy_first {declared : Nat} {tag : UInt8} {rest : List UInt8}
    {fuel : Nat} (hcopy : tag.toNat % 4 ≠ 0) :
    ∃ e, decompressElements declared (tag :: rest) ByteArray.empty (fuel + 1) = .error e := by
  simp only [decompressElements, beq_iff_eq, hcopy, ↓reduceIte, EthLib.Base.ByteOrder.ofLE_toVector]
  repeat' split
  -- Every branch is an error, since a copy of at least 1 byte cannot read an empty output.
  all_goals first
    | exact ⟨_, rfl⟩
    | (rename_i h; rw [copyBytes_nil (by omega)] at h; cases h)

/-- The element loop never takes the output past the declared length.

Each element checks its length before it writes, so this holds at every step, not only at the end.
-/
theorem decompressElements_size_le {declared : Nat} {input : List UInt8} {out out' : ByteArray}
    {fuel : Nat} (hout : out.size ≤ declared)
    (h : decompressElements declared input out fuel = .ok out') : out'.size ≤ declared := by
  revert hout h
  fun_induction decompressElements declared input out fuel <;> intro hout h
  all_goals first
    | (cases h; exact hout)
    | cases h
    -- A literal: its guard bounds the output it appends to.
    | (rename_i hlen hfit ih
       refine ih ?_ h
       simp only [ByteArray.size_append, List.size_toByteArray, List.length_take]
       omega)
    -- A copy: its guard bounds the output, which grows by exactly the copy length.
    | (rename_i hfit hc ih
       refine ih ?_ h
       rw [copyBytes_size hc]
       omega)

/-! ## The whole block -/

/-- Decoded to a byte array, a block yields exactly as many bytes as its preamble declared. -/
theorem decompressToArray_size_eq_declared {bs : List UInt8} {out : ByteArray}
    (h : decompressToArray bs = .ok out) :
    ∃ rest, readPreamble bs = .ok (out.size, rest) := by
  rw [decompressToArray] at h
  split at h
  · cases h
  · rename_i declared rest hpre
    split at h
    · cases h
    · split at h
      · rename_i hlen
        cases h
        exact ⟨rest, by rw [hpre, beq_iff_eq.mp hlen]⟩
      · cases h

/-- A block that decompresses yields exactly as many bytes as its preamble declared. -/
theorem decompressList_length_eq_declared {bs out : List UInt8}
    (h : decompressList bs = .ok out) :
    ∃ rest, readPreamble bs = .ok (out.length, rest) := by
  cases hd : decompressToArray bs with
  | error e => simp only [decompressList, hd, Except.map] at h; cases h
  | ok o =>
      simp only [decompressList, hd, Except.map] at h
      cases h
      simpa using decompressToArray_size_eq_declared hd

/-- A block that decompresses yields at most 2^32 - 1 bytes. -/
theorem decompressList_length_le {bs out : List UInt8}
    (h : decompressList bs = .ok out) : out.length ≤ maxUncompressedLength := by
  obtain ⟨_, hpre⟩ := decompressList_length_eq_declared h
  exact readPreamble_le hpre

/-- A block whose first element is a copy is rejected (§2). -/
theorem decompressList_copy_first {bs rest : List UInt8} {declared : Nat} {tag : UInt8}
    (hpre : readPreamble bs = .ok (declared, tag :: rest)) (hcopy : tag.toNat % 4 ≠ 0) :
    ∃ e, decompressList bs = .error e := by
  obtain ⟨e, he⟩ :=
    decompressElements_copy_first (declared := declared) (rest := rest) (fuel := rest.length) hcopy
  exact ⟨e, by simp [decompressList, decompressToArray, hpre, he, Except.map]⟩

/-- On bytes, a block that decompresses yields exactly as many bytes as its preamble declared. -/
theorem decompress_size_eq_declared {bs out : ByteArray}
    (h : decompress bs = .ok out) :
    ∃ rest, readPreamble bs.toList = .ok (out.size, rest) :=
  decompressToArray_size_eq_declared h

/-! ## Literals (§2.1) -/

/-- A literal, then any bytes: the literal appends its data to the output (§2.1).

The data holds 1 to 2^32 bytes.

The output, followed by the data, stays within the declared length.
-/
theorem decompressElements_literal_append {declared : Nat} {o data s : List UInt8}
    (hne : data ≠ []) (h : data.length ≤ 2 ^ 32) (hd : o.length + data.length ≤ declared)
    (fuel : Nat) :
    decompressElements declared (literal data ++ s) o.toByteArray (fuel + 1) =
      decompressElements declared s (o ++ data).toByteArray fuel := by
  have hpos : 0 < data.length := List.length_pos_iff.mpr hne
  simp only [literal, literalHeader]
  by_cases hn : data.length - 1 < 60
  -- The length sits in the tag.
  · have ht : (UInt8.ofNat ((data.length - 1) * 4)).toNat = (data.length - 1) * 4 := by
      rw [UInt8.toNat_ofNat']; omega
    simp only [hn, ↓reduceIte, List.cons_append, List.nil_append, decompressElements, ht]
    simp [hn, show data.length - 1 + 1 = data.length by omega,
      show ¬ declared < o.length + data.length by omega,
      show ¬ data.length + s.length < data.length by omega]
  -- The length takes 1 to 4 bytes after the tag.
  · have hk : 1 ≤ literalLengthBytes (data.length - 1) ∧ literalLengthBytes (data.length - 1) ≤ 4 ∧
        data.length - 1 < 256 ^ literalLengthBytes (data.length - 1) := by
      unfold literalLengthBytes
      split <;> (try split) <;> (try split) <;> simp only [Nat.reducePow] at * <;> omega
    obtain ⟨hk1, hk4, hlt⟩ := hk
    simp only [hn, ↓reduceIte]
    generalize literalLengthBytes (data.length - 1) = k at *
    have ht : (UInt8.ofNat ((59 + k) * 4)).toNat = (59 + k) * 4 := by
      rw [UInt8.toNat_ofNat']; omega
    have hv : (ByteOrder.toLE k (data.length - 1)).toList.foldr
        (fun byte acc => byte.toNat + 256 * acc) 0 = data.length - 1 := by
      simpa using EthLib.Base.ByteOrder.foldr_toLE_of_lt hlt
    have hk' : (ByteOrder.toLE k (data.length - 1)).toList.length = k := by simp
    simp only [List.cons_append, List.append_assoc]
    simp only [decompressElements, ht, EthLib.Base.ByteOrder.ofLE_toVector]
    simp [show ¬ 59 + k < 60 by omega, show 59 + k - 59 = k by omega, hv, hk',
      show data.length - 1 + 1 = data.length by omega,
      show ¬ declared < o.length + data.length by omega,
      show ¬ data.length + s.length < data.length by omega,
      show ¬ k + (data.length + s.length) < k by omega]

/-- The tag of a literal reads back as a literal, and its length as the data length (§2.1). -/
theorem decompressElements_literal {declared : Nat} {data : List UInt8} (hne : data ≠ [])
    (h : data.length ≤ 2 ^ 32) (hd : data.length ≤ declared) (fuel : Nat) :
    decompressElements declared (literal data) ByteArray.empty (fuel + 1) =
      .ok data.toByteArray := by
  have := decompressElements_literal_append (o := []) (s := []) hne h (by simpa using hd) fuel
  simpa [decompressElements] using this

/-- The length that the first bytes of a block declare is the length it decompresses to. -/
theorem declaredLength_of_decompress {bs out : ByteArray} (h : decompress bs = .ok out) :
    declaredLength bs = .ok out.size := by
  obtain ⟨rest, hpre⟩ := decompress_size_eq_declared h
  obtain ⟨rest', h'⟩ := readPreamble_take hpre
  have hl : (bs.extract 0 preambleMaxLength).toList = bs.toList.take preambleMaxLength := by
    rw [Base.toList_eq_data_toList, Base.toList_eq_data_toList, ByteArray.data_extract,
      Array.toList_extract]
    simp [List.extract]
  simp [declaredLength, hl, h', Except.map]

/-! ## Error codes -/

section

open EthLib.Networking.Snappy

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Snappy.SnappyError.code_injective
    (e₁ e₂ : SnappyError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [SnappyError.code] at h; exact absurd h (by decide))

end

end EthLib.Networking.Proofs.Snappy.Block
