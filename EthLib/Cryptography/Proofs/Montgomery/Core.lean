module

public import EthLib.Cryptography.Montgomery

/-!
# Proofs: Montgomery arithmetic helpers
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

open Internal

variable {n : Nat} [Words n]

/-- An empty sequence of words writes `0`. -/
theorem Internal.num_zero (f : Nat → UInt64) (k : Nat) : num 0 f k = 0 := rfl

/-- An empty sequence of words fits. -/
theorem Internal.fits_zero (f : Nat → UInt64) (k : Nat) : Fits 0 f k := trivial

/-- The `n + 1` words fit exactly when the first `n` fit and the last is below `2 ^ 32`. -/
theorem Internal.fits_snoc {n : Nat} {f : Nat → UInt64} {k : Nat} :
    Fits (n + 1) f k ↔ Fits n f k ∧ (f (k + n)).toNat < 2 ^ 32 := by
  induction n generalizing k with
  | zero => simp [Fits]
  | succ n ih =>
    rw [fits_succ, ih, fits_succ, Nat.add_right_comm k 1 n]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- Fitting words with the same integer are the same words. -/
theorem Internal.eq_of_num_eq {n : Nat} {f g : Nat → UInt64} {k : Nat} (hf : Fits n f k)
    (hg : Fits n g k) (h : num n f k = num n g k) : ∀ i < n, f (k + i) = g (k + i) := by
  induction n generalizing k with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [num_succ, num_succ] at h
    have := hf.1
    have := hg.1
    have h0 : (f k).toNat = (g k).toNat := by omega
    have h1 : num n f (k + 1) = num n g (k + 1) := by omega
    intro i hi
    rcases i with _ | i
    · exact UInt64.toNat_inj.mp h0
    · have e := ih hf.2 hg.2 h1 i (by omega)
      rwa [Nat.add_right_comm k 1 i, Nat.add_assoc] at e

/-- The words of a fixed count are the words of a pair of a low word and the rest. -/
theorem Internal.word_succ {n : Nat} [Words n] (t : Words.W (n + 1)) :
    Words.word t = cons (t : UInt64 × Words.W n).1 (Words.word (t : UInt64 × Words.W n).2) := rfl

/-- The comparison of words is the comparison of their integers. -/
theorem Internal.ltWords_iff {t : Words.W n} {p : Nat → UInt64} (ht : Fits n (Words.word t) 0)
    (hp : Fits n p 0) : ltWords t p = true ↔ num n (Words.word t) 0 < num n p 0 := by
  have z : (0 : UInt64).toNat ≤ 1 := by decide
  obtain ⟨fd, bd, ed⟩ := Words.subb_spec t p 0 0 ht hp z
  have := num_lt fd
  have := num_lt ht
  have := num_lt hp
  simp only [ltWords, bne_iff_ne, ne_eq, UInt64.toNat_zero, Nat.add_zero] at ed ⊢
  rw [← UInt64.toNat_inj, UInt64.toNat_zero]
  generalize Words.subb t p 0 0 = d at *
  generalize 2 ^ (32 * n) = R at *
  have hb : d.2.toNat = 0 ∨ d.2.toNat = 1 := by omega
  rcases hb with hb | hb <;> rw [hb] at ed ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one] at ed <;>
    omega

namespace Limbs

variable [Limbs n]

/-- The integer of the limbs is below `2 ^ (32 n)`. -/
theorem val_lt (a : T n) : val a < 2 ^ (32 * n) := num_lt (fits a 0)

/-- Limbs with the same integer are equal. -/
theorem val_injective : Function.Injective (val : T n → Nat) := by
  intro a b h
  apply ext
  intro k hk
  simpa using eq_of_num_eq (fits a 0) (fits b 0) h k hk

/-- A digit is the integer of 32 bits at its place. -/
theorem Internal.digit_toNat (x i : Nat) : (digit x i).toNat = x / 2 ^ (32 * i) % 2 ^ 32 := by
  have := Nat.mod_lt (x / 2 ^ (32 * i)) (Nat.two_pow_pos 32)
  rw [digit, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- The digits of `x` from place `k` write `x / 2 ^ (32 k)` mod `2 ^ (32 m)`. -/
theorem Internal.num_digit (x : Nat) (m k : Nat) :
    num m (digit x) k = x / 2 ^ (32 * k) % 2 ^ (32 * m) := by
  induction m generalizing k with
  | zero => simp [num, Nat.mod_one]
  | succ m ih =>
    rw [num_succ, ih, radix_succ m, Nat.mod_mul, radix_succ k, Nat.mul_comm (2 ^ 32) (2 ^ (32 * k)),
      ← Nat.div_div_eq_div_mul, digit_toNat]

/-- The digits fit. -/
theorem Internal.fits_digit (x : Nat) (m k : Nat) : Fits m (digit x) k :=
  fits_of_lt fun _ _ => by
    rw [digit_toNat]
    exact Nat.mod_lt _ (by decide)

/-- The limbs of `x` write `x mod 2 ^ (32 n)`. -/
theorem val_ofNat (x : Nat) : val (ofNat (n := n) x) = x % 2 ^ (32 * n) := by
  rw [ofNat, val_pack ((load_spec _ _).1.mpr (Internal.fits_digit x n 0)), (load_spec _ _).2,
    Internal.num_digit]
  simp

end Limbs

end EthLib.Cryptography.Montgomery
