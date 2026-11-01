module

public import EthLib.Networking.Snappy.Block
public import EthLib.Networking.Encoding.Varint

/-!
# `Networking.Proofs.Snappy.Block`

Properties of Snappy block decompression, against [`format_description.txt`](https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt).

- The preamble is a little-endian varint: it reads back every encoding of a length up to 2^32 - 1 (§1).
- A copy writes exactly the bytes §2.2 describes, overlapping copies included.
- A block cannot start with a copy (§2).
- A block that decompresses yields exactly the length it declared, at most 2^32 - 1.
- The fuel that bounds the element loop never changes the result.

There is no round trip: one byte string has many encodings, and compression is out of scope.

The kernel checks everything here, so no `native_decide` or `bv_decide` axiom appears.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Block

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

/-- The preamble reads back the varint encoding of every length up to 2^32 - 1, whatever follows it. -/
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

/-! ## Copies (§2.2)

The output is held most recent byte first, so a forward list `o` is stored as its reverse.
-/

/-- A successful copy of `n` bytes lengthens the output by `n`. -/
theorem copyBytes_length {out out' : List UInt8} {offset n : Nat}
    (h : copyBytes out offset n = .ok out') : out'.length = out.length + n := by
  induction n generalizing out with
  | zero => rw [copyBytes] at h; cases h; simp
  | succ n ih =>
      rw [copyBytes] at h
      split at h
      · cases h
      · have := ih h
        simp only [List.length_cons] at this
        omega

/-- A copy that reaches back no further than the output succeeds, and writes what §2.2 describes.

In forward order, the result `r`:

- starts with the output `o` it was given,
- is `n` bytes longer,
- has each new byte equal to the byte `offset` places before it.

The last rule is read on the bytes already written, so a copy longer than its offset repeats itself.
-/
theorem copyBytes_spec {o : List UInt8} {offset : Nat} (n : Nat)
    (hpos : 0 < offset) (hle : offset ≤ o.length) :
    ∃ r, copyBytes o.reverse offset n = .ok r.reverse ∧ r.length = o.length + n ∧ o <+: r ∧
      ∀ (j : Nat) (hj : o.length ≤ j) (hjr : j < r.length),
        r[j] = r[j - offset]'(by omega) := by
  induction n generalizing o with
  | zero => exact ⟨o, rfl, rfl, List.prefix_refl o, fun j hj hjr => by omega⟩
  | succ n ih =>
      -- The byte `offset` back in forward order.
      have hidx : o.length - offset < o.length := by omega
      have hread : o.reverse[offset - 1]? = some o[o.length - offset] := by
        have hi : o.length - 1 - (offset - 1) = o.length - offset := by omega
        rw [List.getElem?_reverse (by omega), hi, List.getElem?_eq_getElem hidx]
      -- Writing it is appending it in forward order.
      obtain ⟨r, hr, hlen, hpre, hrep⟩ :=
        ih (o := o ++ [o[o.length - offset]]) (by simp; omega)
      refine ⟨r, ?_, ?_, ?_, ?_⟩
      · rw [copyBytes, hread]
        simpa using hr
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
    copyBytes [] offset len = .error (.copyOffsetTooLarge offset) := by
  obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
  rfl

/-- A copy reaching past the start of the output fails. -/
theorem copyBytes_tooLarge {out : List UInt8} {offset n : Nat}
    (hout : out.length < offset) :
    copyBytes out offset (n + 1) = .error (.copyOffsetTooLarge offset) := by
  rw [copyBytes, List.getElem?_eq_none (by omega)]

/-! ## The element loop -/

/-- One more unit of fuel changes nothing once the fuel covers the input. -/
theorem decompressElements_succ_fuel (input out : List UInt8) {fuel : Nat}
    (h : input.length ≤ fuel) :
    decompressElements input out (fuel + 1) = decompressElements input out fuel := by
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

/-- The element loop gives the same result for every fuel that covers the input. -/
theorem decompressElements_fuel (input out : List UInt8) {fuel : Nat}
    (h : input.length ≤ fuel) :
    decompressElements input out fuel = decompressElements input out input.length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [← Nat.add_assoc, decompressElements_succ_fuel input out (by omega), ih (by omega)]

/-- A first element that is a copy has nothing to copy from, so it is rejected (§2). -/
theorem decompressElements_copy_first {tag : UInt8} {rest : List UInt8} {fuel : Nat}
    (hcopy : tag.toNat % 4 ≠ 0) :
    ∃ e, decompressElements (tag :: rest) [] (fuel + 1) = .error e := by
  simp only [decompressElements, beq_iff_eq, hcopy, ↓reduceIte]
  repeat' split
  -- Every branch is an error, except a successful copy, which cannot happen.
  -- Every copy length is at least 1, and the output is empty.
  all_goals first
    | exact ⟨_, rfl⟩
    | (rename_i h; rw [copyBytes_nil (by omega)] at h; cases h)

/-! ## The whole block -/

/-- A block that decompresses yields exactly as many bytes as its preamble declared. -/
theorem decompressList_length_eq_declared {bs out : List UInt8}
    (h : decompressList bs = .ok out) :
    ∃ rest, readPreamble bs = .ok (out.length, rest) := by
  rw [decompressList] at h
  split at h
  · cases h
  · rename_i declared rest hpre
    split at h
    · cases h
    · split at h
      · rename_i hlen
        cases h
        exact ⟨rest, by rw [hpre, List.length_reverse, beq_iff_eq.mp hlen]⟩
      · cases h

/-- A block that decompresses yields at most 2^32 - 1 bytes. -/
theorem decompressList_length_le {bs out : List UInt8}
    (h : decompressList bs = .ok out) : out.length ≤ maxUncompressedLength := by
  obtain ⟨_, hpre⟩ := decompressList_length_eq_declared h
  exact readPreamble_le hpre

/-- A block whose first element is a copy is rejected (§2). -/
theorem decompressList_copy_first {bs rest : List UInt8} {declared : Nat} {tag : UInt8}
    (hpre : readPreamble bs = .ok (declared, tag :: rest)) (hcopy : tag.toNat % 4 ≠ 0) :
    ∃ e, decompressList bs = .error e := by
  obtain ⟨e, he⟩ := decompressElements_copy_first (rest := rest) (fuel := rest.length) hcopy
  exact ⟨e, by simp [decompressList, hpre, he]⟩

/-- On bytes, a block that decompresses yields exactly as many bytes as its preamble declared. -/
theorem decompress_size_eq_declared {bs out : ByteArray}
    (h : decompress bs = .ok out) :
    ∃ rest, readPreamble bs.toList = .ok (out.size, rest) := by
  rw [decompress] at h
  cases hd : decompressList bs.toList with
  | error e => simp [hd] at h; cases h
  | ok o =>
      simp [hd] at h
      cases h
      exact decompressList_length_eq_declared hd

/-! ## Known answers

Each block is built by hand from the format description.

Each comment says what the block pins.
-/

/-- A literal of two bytes, its length in the tag. -/
example : decompressList [0x02, 0x04, 0x41, 0x42] = .ok [0x41, 0x42] := rfl

/-- Two literals in a row, which §2 permits. -/
example : decompressList [0x02, 0x00, 0x41, 0x00, 0x42] = .ok [0x41, 0x42] := rfl

/-- A literal of 61 bytes, the shortest whose length takes one extra byte (tag 60). -/
example : decompressList ([0x3d, 0xf0, 0x3c] ++ List.replicate 61 0x41) =
    .ok (List.replicate 61 0x41) := rfl

/-- A literal of one byte whose length is written in four extra bytes (tag 63). -/
example : decompressList [0x01, 0xfc, 0x00, 0x00, 0x00, 0x00, 0x41] = .ok [0x41] := rfl

/-- A copy with a one-byte offset: offset 1, length 4. -/
example : decompressList [0x05, 0x00, 0x41, 0x01, 0x01] =
    .ok [0x41, 0x41, 0x41, 0x41, 0x41] := rfl

set_option maxRecDepth 4000 in
/-- A copy with a one-byte offset whose offset is 256, so its top bits sit in the tag. -/
example : decompressList ([0x84, 0x02, 0xf0, 0xff] ++ (List.range 256).map UInt8.ofNat ++ [0x21, 0x00]) =
    .ok ((List.range 256).map UInt8.ofNat ++ [0x00, 0x01, 0x02, 0x03]) := rfl

/-- A copy with a two-byte offset: offset 4, length 4. -/
example : decompressList [0x08, 0x0c, 0x41, 0x42, 0x43, 0x44, 0x0e, 0x04, 0x00] =
    .ok [0x41, 0x42, 0x43, 0x44, 0x41, 0x42, 0x43, 0x44] := rfl

/-- A copy with a four-byte offset: offset 4, length 4. -/
example : decompressList [0x08, 0x0c, 0x41, 0x42, 0x43, 0x44, 0x0f, 0x04, 0x00, 0x00, 0x00] =
    .ok [0x41, 0x42, 0x43, 0x44, 0x41, 0x42, 0x43, 0x44] := rfl

/-- The example of §2.2: "xab" then a copy of offset 2 and length 4 gives "xababab". -/
example : decompressList [0x07, 0x08, 0x78, 0x61, 0x62, 0x0e, 0x02, 0x00] =
    .ok [0x78, 0x61, 0x62, 0x61, 0x62, 0x61, 0x62] := rfl

/-- An overlapping copy of offset 1 and length 10: a run of one byte. -/
example : decompressList [0x0b, 0x00, 0x41, 0x19, 0x01] =
    .ok (List.replicate 11 0x41) := rfl

/-- An empty block: a preamble of zero and no elements. -/
example : decompressList [0x00] = .ok [] := rfl

/-- A preamble of one that is not minimally encoded, which §1 allows. -/
example : decompressList [0x81, 0x00, 0x00, 0x41] = .ok [0x41] := rfl

/-! ## Rejected blocks

One per error.
-/

/-- No bytes at all. -/
example : decompressList [] = .error .preambleTruncated := rfl

/-- A preamble whose last byte still carries the continuation bit. -/
example : decompressList [0x80] = .error .preambleTruncated := rfl

/-- A preamble that does not end within five bytes. -/
example : decompressList [0x80, 0x80, 0x80, 0x80, 0x80, 0x00] =
    .error .preambleTooLong := rfl

/-- A preamble declaring 2^32 bytes, one more than allowed. -/
example : decompressList [0x80, 0x80, 0x80, 0x80, 0x10] =
    .error (.preambleTooLarge 4294967296) := rfl

/-- A literal of three bytes with one byte left in the input. -/
example : decompressList [0x05, 0x08, 0x41] = .error .literalPastEnd := rfl

/-- A literal whose two length bytes are cut off after one. -/
example : decompressList [0x05, 0xf4, 0x00] = .error .literalPastEnd := rfl

/-- A copy with a two-byte offset and no offset bytes. -/
example : decompressList [0x05, 0x00, 0x41, 0x0e] = .error .copyPastEnd := rfl

/-- A copy with offset zero. -/
example : decompressList [0x05, 0x00, 0x41, 0x01, 0x00] =
    .error .copyOffsetZero := rfl

/-- A copy of offset 5 after one byte of output. -/
example : decompressList [0x05, 0x00, 0x41, 0x01, 0x05] =
    .error (.copyOffsetTooLarge 5) := rfl

/-- A block that starts with a copy. -/
example : decompressList [0x04, 0x01, 0x01] = .error (.copyOffsetTooLarge 1) := rfl

/-- An output of one byte where the preamble declared two. -/
example : decompressList [0x02, 0x00, 0x41] = .error (.lengthMismatch 2 1) := rfl

/-- An output of two bytes where the preamble declared one. -/
example : decompressList [0x01, 0x04, 0x41, 0x42] = .error (.lengthMismatch 1 2) := rfl

end EthLib.Networking.Proofs.Snappy.Block
