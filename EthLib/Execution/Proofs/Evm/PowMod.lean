module

public import EthLib.Execution.Evm.PowMod

/-!
# Proofs: square-and-multiply

The square-and-multiply loop of the specification computes `b ^ e % m`.

It links the executable form, which takes one step per bit of `e`, to the mathematical definition.

The mathematical form could not run on a 1024-byte exponent.

The statement holds for every modulus, including `0`, where `% 0` leaves the number unchanged.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- The square-and-multiply loop computes `b ^ e % m`. -/
theorem powMod_eq (b e m : Nat) : powMod b e m = b ^ e % m := by
  induction e using Nat.strongRecOn generalizing b with
  | _ e ih =>
    rw [powMod]
    by_cases h0 : e = 0
    · -- `b ^ 0 % m = 1 % m`.
      subst h0
      simp
    · rw [dite_eq_right h0]
      -- The loop on the squared base and the halved exponent.
      have hrec := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)) (b * b % m)
      -- Squaring modulo `m` first changes nothing, so the half is `b ^ (2 * (e / 2)) % m`.
      have hhalf : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rw [hrec, hhalf]
      by_cases h1 : e % 2 = 1
      · -- An odd exponent: `e = 2 * (e / 2) + 1`.
        rw [ite_eq_left h1, Nat.mod_mul_mod, ← Nat.pow_succ, show (2 * (e / 2)).succ = e by omega]
      · -- An even exponent: `e = 2 * (e / 2)`.
        rw [ite_eq_right h1, show 2 * (e / 2) = e by omega]

end EthLib.Execution.Evm
