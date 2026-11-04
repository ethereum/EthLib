module

/-!
# `Evm.PowMod`

Modular exponentiation by square-and-multiply.

The MODEXP precompile and the EXP instruction both compute a power modulo a number.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- `b ^ e mod m` by square-and-multiply.

It takes one step per bit of `e`, at most 8192 for a 1024-byte exponent.

The direct `b ^ e % m` would first build `b ^ e`, a number of up to about `2 ^ 8205` bits.

Here `f(b, e)` stands for the result modulo 7:

```text
    f(3, 5)   e odd    = f(2, 2) * 3 mod 7     (3 * 3 mod 7 = 2)
    f(2, 2)   e even   = f(4, 1)               (2 * 2 mod 7 = 4)
    f(4, 1)   e odd    = f(2, 0) * 4 mod 7     (4 * 4 mod 7 = 2)
    f(2, 0)   e = 0    = 1

    unwinding:  1 * 4 mod 7 = 4,  then 4,  then 4 * 3 mod 7 = 5
    check:      3 ^ 5 = 243 = 34 * 7 + 5
```

A proof in the proofs library shows it equals `b ^ e % m` for every `m`. -/
def powMod (b e m : Nat) : Nat :=
  if h : e = 0 then 1 % m
  else
    -- The result for the exponent `e / 2` and the squared base.
    let half := powMod (b * b % m) (e / 2) m
    -- An odd exponent leaves one factor of `b` over.
    if e % 2 = 1 then half * b % m else half
termination_by e
decreasing_by omega

end EthLib.Execution.Evm
