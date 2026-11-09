module

public import EthLib.Cryptography.Hash.Scrypt
public import EthLib.Cryptography.Proofs.Hash.Pbkdf2

/-!
# Proofs: scrypt

Each step and the derivation succeed exactly for the parameters and block sizes of RFC 7914.

So the inner ROMix calls of a derivation never fail.

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
    have nonzero : p * 128 * r ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hp (by decide)) hr)
    obtain ⟨expanded, h1⟩ := Pbkdf2.pbkdf2_ok_iff.mpr ⟨Nat.one_ne_zero, nonzero, hpm, hpw, hs⟩
    obtain ⟨mixed, h2, hsize⟩ := mixBlocks_ok hr hc p 0 ByteArray.empty (by
      rw [Pbkdf2.pbkdf2_size h1, order]
      omega)
    obtain ⟨key, h3⟩ := Pbkdf2.pbkdf2_ok_iff.mpr ⟨Nat.one_ne_zero, by omega, hL, hpw, by
      rw [hsize, ByteArray.size_empty, ← order]
      simp only [Pbkdf2.MAX_LENGTH, Pbkdf2.HASH_LEN] at hpm
      omega⟩
    refine ⟨key, ?_⟩
    unfold scrypt
    simp only [bind, Except.bind, MonadExcept.throw, Except.mapError]
    simp [Nat.ne_of_gt hr, hc, Nat.ne_of_gt hp, Nat.not_lt.mpr hpm, Nat.ne_of_gt hl,
      Nat.not_lt.mpr hL, h1, h2, h3]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem ScryptError.code_injective (e₁ e₂ : ScryptError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ScryptError.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Hash.Scrypt
