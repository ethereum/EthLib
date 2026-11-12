module

public import EthLib.Cryptography.Hash.Scrypt
public import EthLib.Cryptography.Proofs.Hash.Pbkdf2
public import EthLib.Base.Proofs.LittleEndian

/-!
# Proofs: scrypt

Each step and the derivation succeed exactly for the parameters and block sizes of RFC 7914.

The derivation also needs a password and a salt that SHA-256 admits.

So within these bounds, the inner ROMix calls of a derivation succeed.

The steps preserve their block sizes, and a derivation returns the requested key length.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Scrypt

/-- A successful Salsa20/8 call returns one 64-byte block. -/
theorem salsa208_size {input output : ByteArray} (h : salsa208 input = .ok output) :
    output.size = 64 := by
  unfold salsa208 at h
  split at h
  · obtain rfl := Except.ok.inj h
    exact State.bytes_size _
  · contradiction

/-- A successful BlockMix call returns `128 * r` bytes. -/
theorem blockMix_size {input output : ByteArray} {r : Nat}
    (h : blockMix input r = .ok output) : output.size = 128 * r := by
  unfold blockMix at h
  split at h
  · split at h
    · obtain rfl := Except.ok.inj h
      exact (blockMixCore _ _ _).property
    · contradiction
  · contradiction

/-- A successful ROMix call returns `128 * r` bytes. -/
theorem romix_size {input output : ByteArray} {n r : Nat}
    (h : romix input n r = .ok output) : output.size = 128 * r := by
  unfold romix at h
  split at h
  · split at h
    · split at h
      · obtain rfl := Except.ok.inj h
        exact (romixCore _ _ _ _ _).property
      · contradiction
    · contradiction
  · contradiction

/-- A successful scrypt call returns the requested number of bytes. -/
theorem scrypt_size {password salt key : ByteArray} {n r p length : Nat}
    (h : scrypt password salt n r p length = .ok key) : key.size = length := by
  unfold scrypt at h
  simp only [bind, Except.bind, MonadExcept.throw, Except.mapError] at h
  repeat first | contradiction | split at h
  obtain rfl := Except.ok.inj h
  exact Pbkdf2.pbkdf2_size (by assumption)

/-- The cost test is the bound of RFC 7914 §2: a power of two above 1 and below `2^(16 * r)`. -/
theorem validCost_iff {n r : Nat} :
    validCost n r = true ↔ 1 < n ∧ n.isPowerOfTwo ∧ n < 2 ^ (16 * r) := by
  simp only [validCost, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨one, pow⟩, log⟩
    exact ⟨one, (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mp pow,
      (Nat.log2_lt (by omega)).mp log⟩
  · rintro ⟨one, pow, lt⟩
    exact ⟨⟨one, (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mpr pow⟩,
      (Nat.log2_lt (by omega)).mpr lt⟩

/-- Salsa20/8 succeeds exactly on 64 bytes. -/
theorem salsa208_ok_iff {input : ByteArray} :
    (∃ output, salsa208 input = .ok output) ↔ input.size = 64 := by
  unfold salsa208
  by_cases whole : input.size = 64 <;> simp [whole]

/-- BlockMix succeeds exactly for a positive `r` and `128 * r` bytes. -/
theorem blockMix_ok_iff {input : ByteArray} {r : Nat} :
    (∃ output, blockMix input r = .ok output) ↔ 0 < r ∧ input.size = 128 * r := by
  unfold blockMix
  by_cases positive : 0 < r <;> by_cases whole : input.size = 128 * r <;> simp [positive, whole]

/-- ROMix succeeds exactly for a positive `r`, a cost within RFC 7914 §2 and `128 * r` bytes. -/
theorem romix_ok_iff {input : ByteArray} {n r : Nat} :
    (∃ output, romix input n r = .ok output) ↔
      0 < r ∧ (1 < n ∧ n.isPowerOfTwo ∧ n < 2 ^ (16 * r)) ∧ input.size = 128 * r := by
  rw [← validCost_iff]
  unfold romix
  by_cases positive : 0 < r <;> by_cases cost : validCost n r = true <;>
    by_cases whole : input.size = 128 * r <;> simp [positive, cost, whole]

/-- With valid parameters and enough input, mixing succeeds with `128 * r` bytes per block. -/
theorem mixBlocks_ok {input : ByteArray} {n r : Nat} (positive : 0 < r)
    (cost : validCost n r = true) (count offset : Nat) (out : ByteArray)
    (whole : offset + 128 * r * count ≤ input.size) :
    ∃ mixed, mixBlocks input n r count offset out = .ok mixed ∧
      mixed.size = out.size + 128 * r * count := by
  induction count generalizing offset out with
  | zero => exact ⟨out, rfl, by simp⟩
  | succ count ih =>
    have size : (input.extract offset (offset + 128 * r)).size = 128 * r := by
      simp only [ByteArray.size_extract]
      rw [Nat.mul_succ] at whole
      omega
    obtain ⟨block, hblock⟩ :=
      romix_ok_iff.mpr ⟨positive, validCost_iff.mp cost, size⟩
    obtain ⟨mixed, hmixed, hsize⟩ :=
      ih (offset + 128 * r) (out ++ block) (by rw [Nat.mul_succ] at whole; omega)
    refine ⟨mixed, ?_, ?_⟩
    · simp only [mixBlocks, hblock, bind, Except.bind, hmixed]
    · rw [hsize, ByteArray.size_append, romix_size hblock, Nat.mul_succ]
      omega

/--
scrypt succeeds exactly for the parameters of RFC 7914 §2 and inputs that PBKDF2 admits.

The cost is a power of two above 1 and below `2^(16 * r)`.

The expanded password, `p * 128 * r` bytes, is at most `(2^32 - 1) * 32` bytes long.
-/
theorem scrypt_ok_iff {password salt : ByteArray} {n r p length : Nat} :
    (∃ key, scrypt password salt n r p length = .ok key) ↔
      0 < r ∧ (1 < n ∧ n.isPowerOfTwo ∧ n < 2 ^ (16 * r)) ∧
        0 < p ∧ p * 128 * r ≤ Pbkdf2.MAX_LENGTH ∧ 0 < length ∧ length ≤ Pbkdf2.MAX_LENGTH ∧
        password.size < 2 ^ 61 ∧ 64 + salt.size + 4 < 2 ^ 61 := by
  rw [← validCost_iff]
  constructor
  · rintro ⟨key, h⟩
    unfold scrypt at h
    simp only [bind, Except.bind, MonadExcept.throw, Except.mapError] at h
    by_cases hr : r = 0
    · simp [hr] at h
    cases hc : validCost n r
    · simp [hr, hc] at h
    by_cases hp : p = 0 ∨ Pbkdf2.MAX_LENGTH < p * 128 * r
    · simp [hr, hc, hp] at h
    by_cases hl : length = 0
    · simp [hr, hc, hp, hl] at h
    by_cases hL : Pbkdf2.MAX_LENGTH < length
    · simp [hr, hc, hp, hl, hL] at h
    simp only [hr, hc, hp, hl, hL] at h
    cases h1 : Pbkdf2.pbkdf2 password salt 1 (p * 128 * r) with
    | error e => simp [h1] at h
    | ok expanded =>
      obtain ⟨-, -, -, hpw, hs⟩ := Pbkdf2.pbkdf2_ok_iff.mp ⟨_, h1⟩
      exact ⟨by omega, rfl, by omega, by omega, by omega, by omega, hpw, hs⟩
  · rintro ⟨hr, hc, hp, hpm, hl, hL, hpw, hs⟩
    -- The expanded password holds `p` blocks of `128 * r` bytes.
    have order : p * 128 * r = 128 * r * p := by
      rw [Nat.mul_comm p 128, Nat.mul_assoc, Nat.mul_comm p r, Nat.mul_assoc]
    have expandedPos : 0 < p * 128 * r := Nat.mul_pos (Nat.mul_pos hp (by decide)) hr
    obtain ⟨expanded, h1⟩ := Pbkdf2.pbkdf2_ok_iff.mpr ⟨Nat.one_pos, expandedPos, hpm, hpw, hs⟩
    obtain ⟨mixed, h2, hsize⟩ := mixBlocks_ok hr hc p 0 ByteArray.empty (by
      rw [Pbkdf2.pbkdf2_size h1, order]
      omega)
    obtain ⟨key, h3⟩ := Pbkdf2.pbkdf2_ok_iff.mpr ⟨Nat.one_pos, hl, hL, hpw, by
      rw [hsize, ByteArray.size_empty, ← order]
      simp only [Pbkdf2.MAX_LENGTH, Pbkdf2.HASH_LEN] at hpm
      omega⟩
    refine ⟨key, ?_⟩
    unfold scrypt
    simp only [bind, Except.bind, MonadExcept.throw, Except.mapError]
    simp [Nat.ne_of_gt hr, hc, Nat.ne_of_gt hp, Nat.not_lt.mpr hpm, Nat.ne_of_gt hl,
      Nat.not_lt.mpr hL, h1, h2, h3]

/-! ## The values the steps compute

The theorems above fix the sizes each step returns and the inputs each step accepts.

A step that returned a constant block of the right size would satisfy all of them.

The theorems below fix the values.

They state the index that ROMix reads, the table that it fills and the order of the mixed blocks.
-/

/-- Repeating a step on one application of it is one more application of the repeated step. -/
private theorem repeat_succ {α : Type} (f : α → α) (count : Nat) (a : α) :
    Nat.repeat f count (f a) = f (Nat.repeat f count a) := by
  induction count generalizing a with
  | zero => rfl
  | succ count ih => show f (Nat.repeat f count (f a)) = f (f (Nat.repeat f count a)); rw [ih]

/-- `Integerify` reads the last 64 bytes of its value as a little-endian number, RFC 7914 §5. -/
theorem integerify_eq (r : Nat) (x : MixBlock r) :
    integerify r x
      = Base.bytesToUint (x.val.extract (128 * r - 64) (128 * r)).data.toVector := by
  unfold integerify
  rw [Base.bytesToUint_eq_foldr]
  simp only [Vector.toList, ← Array.foldr_toList]
  -- The two folds differ only in the order of the sum at each byte.
  induction (x.val.extract (128 * r - 64) (128 * r)).data.toList with
  | nil => rfl
  | cons byte rest ih => simp only [List.foldr_cons, ih]; omega

/-- The fill leaves every entry below the index it starts from, RFC 7914 §5, step 2. -/
theorem romixFill_fst_get_lt (r : Nat) (positive : 0 < r) {n : Nat} (count i : Nat)
    (whole : i + count = n) (table : Vector (MixBlock r) n) (x : MixBlock r) (j : Nat)
    (below : j < i) (within : j < n) :
    (romixFill r positive count i whole table x).1[j] = table[j] := by
  induction count generalizing i table x with
  | zero => rfl
  | succ count ih =>
    rw [romixFill, ih (i + 1) (by omega) _ _ (by omega), Vector.getElem_set_ne (by omega) within
      (by omega)]

/-- The fill stores `BlockMix` applied `j - i` times at entry `j`, RFC 7914 §5, step 2.

So each entry is the value that the next BlockMix step reads.
-/
theorem romixFill_fst_get (r : Nat) (positive : 0 < r) {n : Nat} (count i : Nat)
    (whole : i + count = n) (table : Vector (MixBlock r) n) (x : MixBlock r) (j : Nat)
    (from_ : i ≤ j) (before : j < i + count) :
    (romixFill r positive count i whole table x).1[j]'(by omega)
      = Nat.repeat (blockMixCore r positive) (j - i) x := by
  induction count generalizing i table x with
  | zero => omega
  | succ count ih =>
    rw [romixFill]
    rcases Nat.eq_or_lt_of_le from_ with rfl | gt
    · -- Entry `i` is written first, and the later steps leave it alone.
      rw [romixFill_fst_get_lt r positive count (i + 1) (by omega) _ _ i (by omega) (by omega),
        Vector.getElem_set_self, Nat.sub_self]
      rfl
    · obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
      have step : i + 1 + d - (i + 1) = d := by omega
      have total : i + 1 + d - i = d + 1 := by omega
      rw [ih (i + 1) (by omega) _ _ (by omega) (by omega), step, repeat_succ, total]
      rfl

/-- The fill carries `BlockMix` applied `count` times, RFC 7914 §5, step 2. -/
theorem romixFill_snd (r : Nat) (positive : 0 < r) {n : Nat} (count i : Nat)
    (whole : i + count = n) (table : Vector (MixBlock r) n) (x : MixBlock r) :
    (romixFill r positive count i whole table x).2
      = Nat.repeat (blockMixCore r positive) count x := by
  induction count generalizing i table x with
  | zero => rfl
  | succ count ih => rw [romixFill, ih (i + 1) (by omega), repeat_succ]; rfl

/-- The table that ROMix reads holds `BlockMix` applied `j` times at entry `j`, RFC 7914 §5.

ROMix reads this table at indices that the password decides, so each entry decides an output.
-/
theorem romixFill_replicate_fst_get (r : Nat) (positive : 0 < r) (n : Nat) (input : MixBlock r)
    (j : Nat) (within : j < n) :
    (romixFill r positive n 0 (by omega) (Vector.replicate n input) input).1[j]
      = Nat.repeat (blockMixCore r positive) j input := by
  rw [romixFill_fst_get r positive n 0 (by omega) _ _ j (by omega) (by omega), Nat.sub_zero]

/-- Mixing appends to what it is given, so a block never reads the blocks already mixed. -/
theorem mixBlocks_append (input : ByteArray) (n r count offset : Nat)
    (out extra mixed : ByteArray) (h : mixBlocks input n r count offset out = .ok mixed) :
    mixBlocks input n r count offset (extra ++ out) = .ok (extra ++ mixed) := by
  induction count generalizing offset out mixed with
  | zero => simp only [mixBlocks] at h ⊢; rw [Except.ok.inj h]
  | succ count ih =>
    simp only [mixBlocks, bind, Except.bind] at h ⊢
    cases hr : romix (input.extract offset (offset + 128 * r)) n r with
    | error e => rw [hr] at h; exact absurd h (by simp)
    | ok block =>
      rw [hr] at h
      replace h : mixBlocks input n r count (offset + 128 * r) (out ++ block) = .ok mixed := h
      show mixBlocks input n r count (offset + 128 * r) (extra ++ out ++ block)
        = .ok (extra ++ mixed)
      rw [ByteArray.append_assoc]
      exact ih (offset + 128 * r) (out ++ block) mixed h

/-- The `p` blocks of a derivation are mixed independently, RFC 7914 §6, step 2. -/
theorem mixBlocks_eq_append (input : ByteArray) (n r count offset : Nat) (out mixed : ByteArray)
    (h : mixBlocks input n r count offset ByteArray.empty = .ok mixed) :
    mixBlocks input n r count offset out = .ok (out ++ mixed) := by
  have := mixBlocks_append input n r count offset ByteArray.empty out mixed h
  rwa [ByteArray.append_empty] at this

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem ScryptError.code_injective (e₁ e₂ : ScryptError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ScryptError.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Hash.Scrypt
