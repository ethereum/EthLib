module

public import EthLib.Execution.Trie.HexPrefix

/-!
# Proofs: `HexPrefix`

- Decoding undoes the encoding, for every path and flag, so the encoding is injective.
- The decoder accepts exactly the encodings, and rejects an empty input, a first nibble above 3 and a padding nibble other than 0.
- Known answers: the leaf examples of #72, worked by hand, and every case of `BasicTests/hexencodetest.json` in `ethereum/tests`.
-/

@[expose] public section

namespace EthLib.Execution.Trie

/-! ## Nibbles and bytes -/

/-- The empty byte string has no nibbles. -/
theorem bytesToNibbleList_nil : bytesToNibbleList ⟨⟨[]⟩⟩ = [] := rfl

/-- The nibbles of a byte string start with the high and the low nibble of its first byte. -/
theorem bytesToNibbleList_cons (byte : UInt8) (rest : List UInt8) :
    bytesToNibbleList ⟨⟨byte :: rest⟩⟩ = highNibble byte :: lowNibble byte :: bytesToNibbleList ⟨⟨rest⟩⟩ := rfl

/-- A byte string has two nibbles per byte. -/
theorem length_bytesToNibbleList (bytes : ByteArray) : (bytesToNibbleList bytes).length = 2 * bytes.size := by
  obtain ⟨⟨bytes⟩⟩ := bytes
  show (bytesToNibbleList ⟨⟨bytes⟩⟩).length = 2 * bytes.length
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    rw [bytesToNibbleList_cons, List.length_cons, List.length_cons, ih, List.length_cons]
    omega

/-- The high nibble of a packed byte is the first nibble packed into it. -/
theorem highNibble_pack (high low : Nibble) : highNibble (UInt8.ofNat (16 * high.val + low.val)) = high := by
  have := high.isLt
  have := low.isLt
  apply Fin.ext
  simp only [highNibble, UInt8.toNat_ofNat']
  omega

/-- The low nibble of a packed byte is the second nibble packed into it. -/
theorem lowNibble_pack (high low : Nibble) : lowNibble (UInt8.ofNat (16 * high.val + low.val)) = low := by
  have := high.isLt
  have := low.isLt
  apply Fin.ext
  simp only [lowNibble, UInt8.toNat_ofNat']
  omega

/-- A byte is its high nibble and its low nibble, packed. -/
theorem pack_highNibble_lowNibble (byte : UInt8) :
    UInt8.ofNat (16 * (highNibble byte).val + (lowNibble byte).val) = byte := by
  simp only [highNibble, lowNibble, Nat.div_add_mod, UInt8.ofNat_toNat]

/-- Unpacking packed nibbles gives them back. -/
theorem bytesToNibbleList_packNibbles :
    ∀ (x : List Nibble) (h : x.length % 2 = 0), bytesToNibbleList ⟨⟨packNibbles x h⟩⟩ = x
  | [], _ => rfl
  -- One nibble is not an even number of nibbles.
  | [_], h => by simp at h
  | high :: low :: rest, h => by
    rw [packNibbles, bytesToNibbleList_cons, highNibble_pack, lowNibble_pack, bytesToNibbleList_packNibbles rest]

/-- Byte strings with the same nibbles are equal. -/
theorem bytesToNibbleList_injective {a b : ByteArray} (h : bytesToNibbleList a = bytesToNibbleList b) : a = b := by
  obtain ⟨⟨a⟩⟩ := a
  obtain ⟨⟨b⟩⟩ := b
  suffices a = b by rw [this]
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp [bytesToNibbleList_nil, bytesToNibbleList_cons] at h
  | cons x xs ih =>
    cases b with
    | nil => simp [bytesToNibbleList_nil, bytesToNibbleList_cons] at h
    | cons y ys =>
      simp only [bytesToNibbleList_cons, List.cons.injEq] at h
      obtain ⟨hhigh, hlow, hrest⟩ := h
      -- Each byte is its two nibbles, packed.
      have hxy : x = y := by
        rw [← pack_highNibble_lowNibble x, ← pack_highNibble_lowNibble y, hhigh, hlow]
      rw [hxy, ih ys hrest]

/-! ## Decoding -/

/-- The nibbles of the encoding of an even path: the first nibble, a 0 nibble of padding, then the path. -/
theorem bytesToNibbleList_nibbleListToCompact_even {x : List Nibble} (h : x.length % 2 = 0) (isLeaf : Bool) :
    bytesToNibbleList (nibbleListToCompact x isLeaf) = (if isLeaf then 2 else 0) :: 0 :: x := by
  rw [nibbleListToCompact, dite_eq_left h, bytesToNibbleList_packNibbles]

/-- The nibbles of the encoding of an odd path: the first nibble, then the path. -/
theorem bytesToNibbleList_nibbleListToCompact_odd {x : List Nibble} (h : x.length % 2 = 1) (isLeaf : Bool) :
    bytesToNibbleList (nibbleListToCompact x isLeaf) = (if isLeaf then 3 else 1) :: x := by
  rw [nibbleListToCompact, dite_eq_right (by omega), bytesToNibbleList_packNibbles]

/-- Decoding undoes the encoding, for every path and flag. -/
theorem compactToNibbleList_nibbleListToCompact (x : List Nibble) (isLeaf : Bool) :
    compactToNibbleList (nibbleListToCompact x isLeaf) = .ok (x, isLeaf) := by
  unfold compactToNibbleList
  by_cases heven : x.length % 2 = 0
  -- An even path: the first nibble is 2 or 0, and the padding 0 follows it.
  · rw [bytesToNibbleList_nibbleListToCompact_even heven]
    cases isLeaf <;> rfl
  -- An odd path is not empty: the first nibble is 3 or 1, and `x[0]` follows it.
  · match x, heven with
    | first :: rest, heven =>
      rw [bytesToNibbleList_nibbleListToCompact_odd (by omega)]
      cases isLeaf <;> rfl

/-- Different paths or flags have different encodings. -/
theorem nibbleListToCompact_injective {x y : List Nibble} {s t : Bool}
    (h : nibbleListToCompact x s = nibbleListToCompact y t) : x = y ∧ s = t := by
  have hx := compactToNibbleList_nibbleListToCompact x s
  rw [h, compactToNibbleList_nibbleListToCompact] at hx
  cases hx
  exact ⟨rfl, rfl⟩

/-- An odd first nibble up to 3 is 3 when it is at least 2, and 1 otherwise. -/
private theorem oddFirstNibble_eq {n : Nibble} (hle : n.val ≤ 3) (hodd : n.val % 2 = 1) :
    (if decide (2 ≤ n.val) = true then (3 : Nibble) else 1) = n := by
  apply Fin.ext
  split <;> simp_all <;> omega

/-- An even first nibble up to 3 is 2 when it is at least 2, and 0 otherwise. -/
private theorem evenFirstNibble_eq {n : Nibble} (hle : n.val ≤ 3) (heven : n.val % 2 = 0) :
    (if decide (2 ≤ n.val) = true then (2 : Nibble) else 0) = n := by
  apply Fin.ext
  split <;> simp_all <;> omega

/-- The decoder accepts only encodings: an accepted byte string is the encoding of what it returns. -/
theorem nibbleListToCompact_of_compactToNibbleList {compact : ByteArray} {x : List Nibble} {isLeaf : Bool}
    (h : compactToNibbleList compact = .ok (x, isLeaf)) : nibbleListToCompact x isLeaf = compact := by
  -- It is enough that the encoding has the nibbles of `compact`.
  apply bytesToNibbleList_injective
  have hlen := length_bytesToNibbleList compact
  unfold compactToNibbleList at h
  split at h
  · rename_i firstNibble secondNibble rest hnibbles
    rw [hnibbles] at hlen ⊢
    simp only [List.length_cons] at hlen
    split at h
    -- A first nibble above 3 is rejected.
    · simp at h
    · rename_i hle
      split at h
      -- An odd path: the encoding writes the first nibble, then the whole path.
      · rename_i hodd
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [bytesToNibbleList_nibbleListToCompact_odd (by simp only [List.length_cons]; omega),
          oddFirstNibble_eq (Nat.le_of_not_lt hle) hodd]
      · rename_i hnotodd
        split at h
        -- An even path: the encoding writes the first nibble, the padding 0, then the path.
        · rename_i hpad
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [bytesToNibbleList_nibbleListToCompact_even (by omega),
            evenFirstNibble_eq (Nat.le_of_not_lt hle) (by omega), hpad]
        -- A padding nibble other than 0 is rejected.
        · simp at h
  -- Fewer than two nibbles is rejected.
  · simp at h

/-- A byte string decodes to a path and a flag exactly when it is their encoding. -/
theorem compactToNibbleList_eq_ok_iff (compact : ByteArray) (x : List Nibble) (isLeaf : Bool) :
    compactToNibbleList compact = .ok (x, isLeaf) ↔ nibbleListToCompact x isLeaf = compact :=
  ⟨nibbleListToCompact_of_compactToNibbleList, fun h => by
    subst h
    exact compactToNibbleList_nibbleListToCompact x isLeaf⟩

/-! ## Rejection -/

/-- The empty byte string is rejected. -/
theorem compactToNibbleList_empty : compactToNibbleList ByteArray.empty = .error .empty := rfl

/-- A first nibble above 3 is rejected, whatever follows it. -/
theorem compactToNibbleList_invalidFirstNibble (first : UInt8) (rest : List UInt8)
    (h : 3 < (highNibble first).val) :
    compactToNibbleList ⟨⟨first :: rest⟩⟩ = .error .invalidFirstNibble := by
  simp [compactToNibbleList, bytesToNibbleList_cons, h]

/-- An even path whose padding nibble is not 0 is rejected, whatever follows it. -/
theorem compactToNibbleList_nonZeroPadding (first : UInt8) (rest : List UInt8)
    (hflag : (highNibble first).val = 0 ∨ (highNibble first).val = 2) (hpad : lowNibble first ≠ 0) :
    compactToNibbleList ⟨⟨first :: rest⟩⟩ = .error .nonZeroPadding := by
  rcases hflag with h | h <;> simp [compactToNibbleList, bytesToNibbleList_cons, h, hpad]

/-! ## Known answers

The leaf examples of #72, worked by hand from `HP`.

Its extension examples are the cases `nz,odd,open` and `z,even,open` of `BasicTests/hexencodetest.json` below. -/

/-- An even leaf path that starts with a 0 nibble: the 0 follows the padding. -/
theorem nibbleListToCompact_leaf_even :
    nibbleListToCompact [0, 0xf, 1, 0xc, 0xb, 8] true = ⟨#[0x20, 0x0f, 0x1c, 0xb8]⟩ := by
  decide +kernel

/-- An odd leaf path: the first nibble 3 and `x[0]` share the first byte. -/
theorem nibbleListToCompact_leaf_odd :
    nibbleListToCompact [0xf, 1, 0xc, 0xb, 8] true = ⟨#[0x3f, 0x1c, 0xb8]⟩ := by
  decide +kernel

/-! ## `BasicTests/hexencodetest.json`

Every case of `BasicTests/hexencodetest.json` in `ethereum/tests`, at commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`, in the file's order.

Each claim is named after its case, with `_` for `,`.

A case gives the path `seq`, the leaf flag `term` and the output in hex.

The cases between the two markers are material from `ethereum/tests`, by the Ethereum Foundation.

They keep its licence, the MIT License, under this notice:

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
-/

-- Start of material from `ethereum/tests` (`BasicTests/hexencodetest.json`), by the Ethereum Foundation, under the MIT License.

theorem nibbleListToCompact_zz_odd_open :
    nibbleListToCompact [0, 0, 1, 2, 3, 4, 5] false = ⟨#[0x10, 0x01, 0x23, 0x45]⟩ := by
  decide +kernel

theorem nibbleListToCompact_z_even_open :
    nibbleListToCompact [0, 1, 2, 3, 4, 5] false = ⟨#[0x00, 0x01, 0x23, 0x45]⟩ := by
  decide +kernel

theorem nibbleListToCompact_nz_odd_open :
    nibbleListToCompact [1, 2, 3, 4, 5] false = ⟨#[0x11, 0x23, 0x45]⟩ := by
  decide +kernel

theorem nibbleListToCompact_zz_even_open :
    nibbleListToCompact [0, 0, 1, 2, 3, 4] false = ⟨#[0x00, 0x00, 0x12, 0x34]⟩ := by
  decide +kernel

theorem nibbleListToCompact_z_odd_open :
    nibbleListToCompact [0, 1, 2, 3, 4] false = ⟨#[0x10, 0x12, 0x34]⟩ := by
  decide +kernel

theorem nibbleListToCompact_nz_even_open :
    nibbleListToCompact [1, 2, 3, 4] false = ⟨#[0x00, 0x12, 0x34]⟩ := by
  decide +kernel

theorem nibbleListToCompact_zz_odd_term :
    nibbleListToCompact [0, 0, 1, 2, 3, 4, 5] true = ⟨#[0x30, 0x01, 0x23, 0x45]⟩ := by
  decide +kernel

theorem nibbleListToCompact_z_even_term :
    nibbleListToCompact [0, 1, 2, 3, 4, 5] true = ⟨#[0x20, 0x01, 0x23, 0x45]⟩ := by
  decide +kernel

theorem nibbleListToCompact_nz_odd_term :
    nibbleListToCompact [1, 2, 3, 4, 5] true = ⟨#[0x31, 0x23, 0x45]⟩ := by
  decide +kernel

theorem nibbleListToCompact_zz_even_term :
    nibbleListToCompact [0, 0, 1, 2, 3, 4] true = ⟨#[0x20, 0x00, 0x12, 0x34]⟩ := by
  decide +kernel

theorem nibbleListToCompact_z_odd_term :
    nibbleListToCompact [0, 1, 2, 3, 4] true = ⟨#[0x30, 0x12, 0x34]⟩ := by
  decide +kernel

theorem nibbleListToCompact_nz_even_term :
    nibbleListToCompact [1, 2, 3, 4] true = ⟨#[0x20, 0x12, 0x34]⟩ := by
  decide +kernel

-- End of material from `ethereum/tests`.

end EthLib.Execution.Trie
