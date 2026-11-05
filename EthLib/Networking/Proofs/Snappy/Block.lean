module

public import EthLib.Networking.Snappy.Block
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Networking.Encoding.Varint

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
- A block of one literal decompresses back to its data, for at most 2^32 - 1 bytes.

One byte string has many encodings, so the round trip goes one way only.

The kernel checks everything here, so no `native_decide` or `bv_decide` axiom appears.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Block

open EthLib.Base (bytesToUint uintToBytes)
open EthLib.Networking.Snappy

/-! ## The preamble (§1) -/

/-- Reading a varint written by the shared encoder gives back its value, at its place.

A budget of k bytes holds values below 128^k.
-/
theorem readPreambleAux_encodeAux {n fuel : Nat} (acc shift : Nat) (rest : List UInt8)
    (hfuel : 0 < fuel) (hn : n < 128 ^ fuel) :
    readPreambleAux (EthLib.Networking.Encoding.Varint.encodeAux n fuel ++ rest) acc shift fuel =
      .ok (acc + n * 2 ^ shift, rest) := by
  induction fuel generalizing n acc shift with
  | zero => omega
  | succ fuel ih =>
      rw [EthLib.Networking.Encoding.Varint.encodeAux]
      split
      -- A last byte: its value is the whole of n.
      · rename_i hlt
        have hlt' : n < 128 := hlt
        have hb : (UInt8.ofNat n).toNat = n := by rw [UInt8.toNat_ofNat']; omega
        simp only [List.cons_append, List.nil_append, readPreambleAux, hb, continuation]
        simp only [hlt', ↓reduceIte, Nat.mod_eq_of_lt hlt']
      -- A continued byte: n mod 128 here, and n / 128 one group higher.
      · rename_i hge
        have hge' : ¬ n < 128 := hge
        -- n is at least 128, so the budget has a second byte.
        have hfuel' : 0 < fuel := by
          rcases Nat.eq_zero_or_pos fuel with h | h
          · subst h; omega
          · exact h
        have hdiv : n / 128 < 128 ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm] at hn
          exact Nat.div_lt_of_lt_mul hn
        have hb : (UInt8.ofNat (n % EthLib.Networking.Encoding.Varint.groupSize +
            EthLib.Networking.Encoding.Varint.continuation)).toNat = n % 128 + 128 := by
          rw [UInt8.toNat_ofNat']
          show (n % 128 + 128) % 2 ^ 8 = n % 128 + 128
          omega
        have hq : n / EthLib.Networking.Encoding.Varint.groupSize = n / 128 := rfl
        simp only [List.cons_append, readPreambleAux, hb, continuation, hq,
          show ¬ n % 128 + 128 < 128 by omega, ↓reduceIte]
        rw [ih _ _ hfuel' hdiv]
        -- Recombine the two groups.
        --
        --     n = (n mod 128) + 128 * (n / 128)
        have hmod : (n % 128 + 128) % 128 = n % 128 := by omega
        have hn : n * 2 ^ shift = (n % 128 + 128 * (n / 128)) * 2 ^ shift := by
          rw [Nat.mod_add_div]
        rw [hmod, hn, Nat.pow_add, Nat.add_mul, Nat.add_assoc]
        congr 3
        rw [show (2 : Nat) ^ 7 = 128 from rfl]
        ac_rfl

/-- The preamble reads back the varint of every length up to 2^32 - 1, whatever follows it. -/
theorem readPreamble_encode {n : Nat} (rest : List UInt8) (hn : n ≤ maxUncompressedLength) :
    readPreamble (EthLib.Networking.Encoding.Varint.encodeAux n preambleMaxLength ++ rest) =
      .ok (n, rest) := by
  have hn' : n < 128 ^ preambleMaxLength := by
    simp only [maxUncompressedLength] at hn
    simp only [preambleMaxLength]
    omega
  rw [readPreamble, readPreambleAux_encodeAux 0 0 rest (by decide) hn']
  simp only [Nat.zero_add, Nat.pow_zero, Nat.mul_one, show ¬ maxUncompressedLength < n by omega,
    ↓reduceIte]

/-- An accepted preamble declares at most 2^32 - 1 bytes. -/
theorem readPreamble_le {bs rest : List UInt8} {len : Nat}
    (h : readPreamble bs = .ok (len, rest)) : len ≤ maxUncompressedLength := by
  rw [readPreamble] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; omega

/-- A preamble read within its fuel reads the same length from the first bytes alone. -/
theorem readPreambleAux_take {l rest : List UInt8} {acc shift fuel len : Nat} (n : Nat)
    (hn : fuel ≤ n) (h : readPreambleAux l acc shift fuel = .ok (len, rest)) :
    ∃ rest', readPreambleAux (l.take n) acc shift fuel = .ok (len, rest') := by
  induction fuel generalizing l acc shift n with
  | zero => cases l <;> simp [readPreambleAux] at h
  | succ fuel ih =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      cases l with
      | nil => simp [readPreambleAux] at h
      | cons b bs =>
          rw [List.take_succ_cons]
          rw [readPreambleAux] at h ⊢
          split at h
          · rename_i hb
            simp only [hb, ↓reduceIte]
            cases h
            exact ⟨_, rfl⟩
          · rename_i hb
            simp only [hb, ↓reduceIte]
            exact ih m (by omega) h

/-- An accepted preamble declares the same length when read from the first five bytes alone. -/
theorem readPreamble_take {bs rest : List UInt8} {len : Nat}
    (h : readPreamble bs = .ok (len, rest)) :
    ∃ rest', readPreamble (bs.take preambleMaxLength) = .ok (len, rest') := by
  rw [readPreamble] at h ⊢
  cases haux : readPreambleAux bs 0 0 preambleMaxLength with
  | error e => rw [haux] at h; cases h
  | ok p =>
      obtain ⟨len', rest''⟩ := p
      rw [haux] at h
      obtain ⟨rest', h'⟩ := readPreambleAux_take preambleMaxLength (Nat.le_refl _) haux
      rw [h']
      dsimp only at h ⊢
      by_cases hl : maxUncompressedLength < len'
      · simp only [hl, ↓reduceIte] at h; cases h
      · simp only [hl, ↓reduceIte] at h ⊢
        cases h
        exact ⟨_, rfl⟩

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
    copyBytes ByteArray.empty offset len = .error (.copyOffsetTooLarge offset) := by
  obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
  rw [copyBytes, dite_eq_right (by simp)]

/-- A copy reaching past the start of the output fails. -/
theorem copyBytes_tooLarge {out : ByteArray} {offset n : Nat}
    (hout : out.size < offset) :
    copyBytes out offset (n + 1) = .error (.copyOffsetTooLarge offset) := by
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
  simp only [decompressElements, beq_iff_eq, hcopy, ↓reduceIte, EthLib.Base.bytesToUint_toVector]
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

/-! ## The literal encoder -/

/-- The bytes of a byte array, read one by one, are the bytes of its array. -/
theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have hs : bs.data.toList.length = bs.size := Array.length_toList
  -- From index i on, the loop puts the bytes it has read back in order, then the rest.
  have loop : ∀ i r, i ≤ bs.size →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r hlt ih =>
        rw [ih (by omega)]
        have hget : bs.get! i = bs.data.toList[i]'(by omega) := by
          obtain ⟨a⟩ := bs
          exact (getElem!_pos a i hlt).trans (Array.getElem_toList _).symm
        rw [hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          ← List.drop_eq_getElem_cons]
    | case2 i r hge =>
        rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  unfold ByteArray.toList
  simpa using loop 0 [] (Nat.zero_le _)

/-- The tag of a literal reads back as a literal, and its length as the data length (§2.1). -/
theorem decompressElements_literal {declared : Nat} {data : List UInt8} (hne : data ≠ [])
    (h : data.length ≤ 2 ^ 32) (hd : data.length ≤ declared) (fuel : Nat) :
    decompressElements declared (literal data) ByteArray.empty (fuel + 1) =
      .ok data.toByteArray := by
  have hpos : 0 < data.length := List.length_pos_iff.mpr hne
  dsimp only [literal]
  split
  -- The length sits in the tag.
  · rename_i hn
    have ht : (UInt8.ofNat ((data.length - 1) * 4)).toNat = (data.length - 1) * 4 := by
      rw [UInt8.toNat_ofNat']; omega
    simp only [decompressElements, ht]
    simp [hn, show data.length - 1 + 1 = data.length by omega, decompressElements,
      show ¬ declared < data.length by omega]
  -- The length takes 1 to 4 bytes after the tag.
  · rename_i hn
    have hk : 1 ≤ literalLengthBytes (data.length - 1) ∧ literalLengthBytes (data.length - 1) ≤ 4 ∧
        data.length - 1 < 256 ^ literalLengthBytes (data.length - 1) := by
      unfold literalLengthBytes
      split <;> (try split) <;> (try split) <;> simp only [Nat.reducePow] at * <;> omega
    obtain ⟨hk1, hk4, hlt⟩ := hk
    generalize literalLengthBytes (data.length - 1) = k at *
    have ht : (UInt8.ofNat ((59 + k) * 4)).toNat = (59 + k) * 4 := by
      rw [UInt8.toNat_ofNat']; omega
    have hv : (uintToBytes k (data.length - 1)).toList.foldr
        (fun byte acc => byte.toNat + 256 * acc) 0 = data.length - 1 := by
      simpa using EthLib.Base.foldr_uintToBytes_of_lt hlt
    rw [List.cons_append]
    simp only [decompressElements, ht, EthLib.Base.bytesToUint_toVector]
    simp [show ¬ 59 + k < 60 by omega, show 59 + k - 59 = k by omega, hv,
      show data.length - 1 + 1 = data.length by omega, decompressElements,
      show ¬ declared < data.length by omega]

/-- A block of one literal decompresses to its data as a byte array, for up to 2^32 - 1 bytes. -/
theorem decompressToArray_compressLiteralList {data : List UInt8}
    (h : data.length ≤ maxUncompressedLength) :
    decompressToArray (compressLiteralList data) = .ok data.toByteArray := by
  rw [decompressToArray, compressLiteralList, readPreamble_encode _ h]
  cases data with
  | nil => rfl
  | cons b bs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨f, hf⟩ : ∃ f, (literal (b :: bs)).length = f + 1 := by
        dsimp only [literal]; split <;> exact ⟨_, rfl⟩
      rw [hf, decompressElements_literal (List.cons_ne_nil b bs)
        (by simp [maxUncompressedLength] at h ⊢; omega) (Nat.le_refl _)]
      simp

/-- A block of one literal decompresses to its data, for data of at most 2^32 - 1 bytes. -/
theorem decompressList_compressLiteralList {data : List UInt8}
    (h : data.length ≤ maxUncompressedLength) :
    decompressList (compressLiteralList data) = .ok data := by
  simp [decompressList, decompressToArray_compressLiteralList h, Except.map]

/-- The literal block of a byte array decompresses back to it, for at most 2^32 - 1 bytes. -/
theorem decompress_compressLiteral {d : ByteArray} (h : d.size ≤ maxUncompressedLength) :
    decompress (compressLiteral d) = .ok d := by
  have hl : d.data.toList.length ≤ maxUncompressedLength := by simpa using h
  rw [decompress, compressLiteral, toList_eq_data_toList]
  simp only [decompressToArray_compressLiteralList hl]
  exact congrArg Except.ok (ByteArray.ext (by simp))

/-- The length that the first bytes of a block declare is the length it decompresses to. -/
theorem declaredLength_of_decompress {bs out : ByteArray} (h : decompress bs = .ok out) :
    declaredLength bs = .ok out.size := by
  obtain ⟨rest, hpre⟩ := decompress_size_eq_declared h
  obtain ⟨rest', h'⟩ := readPreamble_take hpre
  have hl : (bs.extract 0 preambleMaxLength).toList = bs.toList.take preambleMaxLength := by
    rw [toList_eq_data_toList, toList_eq_data_toList, ByteArray.data_extract,
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
