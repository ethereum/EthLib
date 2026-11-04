module

public import EthLib.Cryptography.Proofs.Hash.Hmac
public import EthLib.Cryptography.Hash.Hkdf

/-!
# Proofs: HKDF-SHA-256

A successful expansion has exactly the requested length.

The expansion computes the blocks `T(1), T(2), ...` of [RFC 5869 §2.3][rfc5869].

[rfc5869]: https://www.rfc-editor.org/rfc/rfc5869#section-2.3

`T(0)` is empty, and `T(i)` is `HMAC-Hash(PRK, T(i - 1) | info | i)`.

The output is the first `L` bytes of their concatenation.

So a shorter output is a prefix of a longer one, for one key and one `info`.

An empty salt gives the same pseudorandom key as `HashLen` zero bytes, the salt of RFC 5869 §2.2.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Hkdf

open EthLib.Cryptography.Hash.Hmac

/-! ## Lengths -/

/-- The blocks of the expansion are 32 bytes each. -/
theorem expandBlocks_size (prk info previous : ByteArray) (i count : Nat) :
    (expandBlocks prk info previous i count).size = HASH_LEN * count := by
  induction count generalizing previous i with
  | zero => rfl
  | succ count ih =>
    simp only [expandBlocks, ByteArray.size_append, hmac_size, ih, HASH_LEN]
    omega

/-- A successful expansion has exactly the requested length. -/
theorem expand_size {prk info okm : ByteArray} {length : Nat}
    (h : expand prk info length = .ok okm) : okm.size = length := by
  unfold expand at h
  by_cases short : prk.size < HASH_LEN
  · simp [short] at h
  by_cases long : 255 * HASH_LEN < length
  · simp [short, long] at h
  simp only [short, long, ite_false] at h
  -- The blocks cover the output, so the extraction keeps the requested length.
  obtain rfl := Except.ok.inj h
  simp only [ByteArray.size_extract, expandBlocks_size, HASH_LEN]
  omega

/-- The pseudorandom key is 32 bytes, so HKDF fails only on an output longer than `255 * 32`. -/
theorem hkdf_error {salt ikm info : ByteArray} {length : Nat} {e : HkdfError}
    (h : hkdf salt ikm info length = .error e) :
    e = .outputTooLong length ∧ 255 * HASH_LEN < length := by
  unfold hkdf expand extract at h
  simp only [hmac_size, HASH_LEN, show ¬ 32 < 32 by decide, ite_false] at h
  by_cases long : 255 * 32 < length
  · simp only [long, ite_true] at h
    exact ⟨(Except.error.inj h).symm, long⟩
  · simp [long] at h

/-! ## The blocks of RFC 5869 -/

/-- The block `T(i)` of RFC 5869 §2.3.

`T(0)` is empty, and `T(i)` is `HMAC(PRK, T(i - 1) | info | i)`. -/
def block (prk info : ByteArray) : Nat → ByteArray
  | 0 => ByteArray.empty
  | i + 1 => hmac prk (block prk info i ++ info ++ ⟨#[UInt8.ofNat (i + 1)]⟩)

/-- The concatenation `T(1) | ... | T(n)` of the first `n` blocks. -/
def blocks (prk info : ByteArray) : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 => blocks prk info n ++ block prk info (n + 1)

/-- After the first `i` blocks, the expansion from `T(i)` appends the next `count` blocks. -/
theorem blocks_append_expandBlocks (prk info : ByteArray) (i count : Nat) :
    blocks prk info i ++ expandBlocks prk info (block prk info i) (i + 1) count =
      blocks prk info (i + count) := by
  induction count generalizing i with
  | zero => simp [expandBlocks]
  | succ count ih =>
    rw [expandBlocks,
      show hmac prk (block prk info i ++ info ++ ⟨#[UInt8.ofNat (i + 1)]⟩) = block prk info (i + 1)
        from rfl, ← ByteArray.append_assoc,
      show blocks prk info i ++ block prk info (i + 1) = blocks prk info (i + 1) from rfl, ih,
      Nat.add_right_comm, Nat.add_assoc]

/-- The expansion from the empty block, with the counter at 1, gives the first `n` blocks. -/
theorem expandBlocks_empty (prk info : ByteArray) (n : Nat) :
    expandBlocks prk info ByteArray.empty 1 n = blocks prk info n := by
  simpa [blocks, block] using blocks_append_expandBlocks prk info 0 n

/-- The first `n` blocks have `HashLen * n` bytes. -/
theorem blocks_size (prk info : ByteArray) (n : Nat) :
    (blocks prk info n).size = HASH_LEN * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blocks, ByteArray.size_append, ih, block, hmac_size, Nat.mul_succ]
    rfl

/-- The first `n` blocks begin the first `n + k` blocks. -/
theorem blocks_add (prk info : ByteArray) (n k : Nat) :
    ∃ tail, blocks prk info (n + k) = blocks prk info n ++ tail := by
  induction k with
  | zero => exact ⟨ByteArray.empty, by simp⟩
  | succ k ih =>
    obtain ⟨tail, h⟩ := ih
    refine ⟨tail ++ block prk info (n + k + 1), ?_⟩
    rw [← Nat.add_assoc, blocks, h, ByteArray.append_assoc]

/-! ## Expansion -/

/-- HKDF-Expand, RFC 5869 §2.3: the first `L` bytes of `T(1) | ... | T(N)`.

Here `N = ceil(L / HashLen)`, the key has at least `HashLen` bytes, and `L <= 255 * HashLen`. -/
theorem expand_eq {prk info : ByteArray} {length : Nat} (hprk : HASH_LEN ≤ prk.size)
    (hlength : length ≤ 255 * HASH_LEN) :
    expand prk info length =
      .ok ((blocks prk info ((length + HASH_LEN - 1) / HASH_LEN)).extract 0 length) := by
  unfold expand
  simp only [Nat.not_lt.mpr hprk, Nat.not_lt.mpr hlength, ↓reduceIte, expandBlocks_empty]

/-- An accepted expansion has a key of at least `HashLen` bytes, and `L <= 255 * HashLen`. -/
theorem expand_ok_bounds {prk info okm : ByteArray} {length : Nat}
    (h : expand prk info length = .ok okm) :
    HASH_LEN ≤ prk.size ∧ length ≤ 255 * HASH_LEN := by
  unfold expand at h
  by_cases h₁ : prk.size < HASH_LEN
  · simp [h₁] at h
  by_cases h₂ : 255 * HASH_LEN < length
  · simp [h₁, h₂] at h
  exact ⟨Nat.not_lt.mp h₁, Nat.not_lt.mp h₂⟩

/-- For one key and one `info`, a shorter output of HKDF-Expand is a prefix of a longer one. -/
theorem expand_prefix {prk info okm okm' : ByteArray} {length length' : Nat}
    (h : expand prk info length = .ok okm) (h' : expand prk info length' = .ok okm')
    (hle : length ≤ length') : okm = okm'.extract 0 length := by
  obtain ⟨hprk, hL⟩ := expand_ok_bounds h
  obtain ⟨-, hL'⟩ := expand_ok_bounds h'
  rw [expand_eq hprk hL, Except.ok.injEq] at h
  rw [expand_eq hprk hL', Except.ok.injEq] at h'
  subst h h'
  have hn : (length + HASH_LEN - 1) / HASH_LEN ≤ (length' + HASH_LEN - 1) / HASH_LEN :=
    Nat.div_le_div_right (by omega)
  obtain ⟨tail, ht⟩ := blocks_add prk info ((length + HASH_LEN - 1) / HASH_LEN)
    ((length' + HASH_LEN - 1) / HASH_LEN - (length + HASH_LEN - 1) / HASH_LEN)
  rw [Nat.add_sub_cancel' hn] at ht
  -- The first blocks cover the shorter output, so the tail adds none of its bytes.
  have hsize : length ≤ (blocks prk info ((length + HASH_LEN - 1) / HASH_LEN)).size := by
    rw [blocks_size, HASH_LEN]
    omega
  rw [ht, ByteArray.extract_extract, ByteArray.extract_append, Nat.zero_add, Nat.zero_add,
    Nat.min_eq_left hle, Nat.sub_eq_zero_of_le hsize]
  simp

/-! ## Extraction -/

/-- An empty salt gives the key of `HashLen` zero bytes, the salt that RFC 5869 §2.2 sets. -/
theorem extract_empty (ikm : ByteArray) :
    extract ByteArray.empty ikm = extract ⟨Array.replicate HASH_LEN 0⟩ ikm := by
  unfold extract
  rw [← hmac_append_zeros (key := ByteArray.empty) (n := HASH_LEN) (by decide),
    ByteArray.empty_append]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem HkdfError.code_injective (e₁ e₂ : HkdfError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [HkdfError.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Hash.Hkdf
