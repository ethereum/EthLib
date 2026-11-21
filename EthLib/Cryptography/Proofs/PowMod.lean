module

public import Mathlib.Data.ZMod.Basic

/-!
# Proofs: powers in `ZMod m` from one modular power

Lean core's modular power computes `b ^ e % m` by square-and-multiply.

Every step is a GMP-accelerated `Nat` operation, so the kernel evaluates it by `decide`.

It does so even for exponents hundreds of bits wide.

The two lemmas below turn such a computation into `(b : ZMod m) ^ e = 1` or its negation.

Lucas primality certificates consume these facts.
-/

@[expose] public section

namespace EthLib.Cryptography.PowMod

/-- `(b : ZMod m) ^ e = 1` is decided by one modular power. -/
theorem natCast_pow_eq_one_iff (m b e : Nat) :
    ((b : ZMod m) ^ e = 1) ↔ Nat.powMod b e m = 1 % m := by
  rw [Nat.powMod_def, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod m),
      ZMod.natCast_eq_natCast_iff]
  exact Iff.rfl

/-- The `≠ 1` half of a Lucas certificate.

It refutes `(b : ZMod m) ^ ((m - 1) / q) = 1` by one modular power. -/
theorem natCast_pow_div_ne_one (m b q : Nat)
    (hne : Nat.powMod b ((m - 1) / q) m ≠ 1 % m) :
    ((b : ZMod m) ^ ((m - 1) / q)) ≠ 1 := fun h =>
  hne ((natCast_pow_eq_one_iff m b _).mp h)

end EthLib.Cryptography.PowMod
