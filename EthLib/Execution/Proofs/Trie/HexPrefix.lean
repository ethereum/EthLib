module

public import EthLib.Execution.Trie.HexPrefix

/-!
# Proofs: `HexPrefix`

- Decoding undoes the encoding, for every path and flag, so the encoding is injective.
- The decoder accepts exactly the encodings.
- It rejects an empty input, a first nibble above 3 and a padding nibble other than 0.
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

end EthLib.Execution.Trie
