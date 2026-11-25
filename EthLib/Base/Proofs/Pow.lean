module

public import EthLib.Base.Pow
public import Mathlib.Algebra.Group.Defs

/-!
# Proofs: square and multiply

Square and multiply computes the power `a^e`, for `e < 2^fuel`.
-/

@[expose] public section

namespace EthLib.Base

/-- A map that keeps products and one sends square and multiply to the power, for `e < 2^fuel`.

The product need not be associative before the map, as for residues read at a point. -/
theorem map_powBits {α M : Type} [Mul α] [One α] [Monoid M] (f : α → M)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hone : f 1 = 1) (fuel : Nat) (a : α) (e : Nat)
    (he : e < 2 ^ fuel) : f (powBits fuel a e) = f a ^ e := by
  induction fuel generalizing a e with
  | zero =>
    obtain rfl : e = 0 := by simpa using he
    simp [powBits, hone]
  | succ fuel ih =>
    have h2 : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at he; omega
    -- `a^e = a^(e mod 2) * (a^2)^(e / 2)`.
    simp only [powBits]
    split
    · rw [hmul, ih _ _ h2, hmul, ← pow_two, ← pow_mul, ← pow_succ']
      congr 1
      omega
    · rw [ih _ _ h2, hmul, ← pow_two, ← pow_mul]
      congr 1
      omega

/-- Square and multiply computes `a^e` in a monoid, for `e < 2^fuel`. -/
theorem powBits_eq_pow {M : Type} [Monoid M] (fuel : Nat) (a : M) (e : Nat) (he : e < 2 ^ fuel) :
    powBits fuel a e = a ^ e :=
  map_powBits id (fun _ _ => rfl) rfl fuel a e he

/-- Square and multiply reads only the low `fuel` bits of the exponent. -/
theorem powBits_mod {α : Type} [Mul α] [One α] (fuel : Nat) (a : α) (e : Nat) :
    powBits fuel a e = powBits fuel a (e % 2 ^ fuel) := by
  induction fuel generalizing a e with
  | zero => rfl
  | succ fuel ih =>
    -- The halves agree on their low `fuel` bits, and both exponents have the same low bit.
    have hhalf : e % 2 ^ (fuel + 1) / 2 % 2 ^ fuel = e / 2 % 2 ^ fuel := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self, Nat.mod_mod]
    have hbit : e % 2 ^ (fuel + 1) % 2 = e % 2 :=
      Nat.mod_mod_of_dvd e (Nat.dvd_of_mod_eq_zero (by simp [Nat.pow_succ, Nat.mul_mod_left]))
    rw [powBits, powBits, ih _ (e / 2), ih _ (e % 2 ^ (fuel + 1) / 2), hhalf, hbit]

end EthLib.Base
