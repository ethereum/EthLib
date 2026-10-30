/-!
# `Secp256k1.Field`

The two prime fields of secp256k1, from SEC 2 v2 §2.4.1.

- `Fp` is the base field, integers mod `p = 2^256 - 2^32 - 977`.
  The coordinates of a point live there.

- `Fn` is the scalar field, integers mod the order `n` of the generator.
  Private keys and the integers `r` and `s` of a signature live there.

Each field is `Fin` of its modulus, so every element is below the modulus by construction.

Core gives `Fin` its `+`, `-`, `*` and negation, all reduced mod the modulus.

An inverse is a power, by Fermat's little theorem: `a^(m - 2) = a^(-1)` when `a != 0` and `m` is prime.

A square root is a power too, because `p = 3 mod 4`.

No division is defined.
Core's `/` on `Fin` divides the integers, so the specification never writes it.
-/

namespace EthLib.Cryptography.Secp256k1

/-- `p`, the modulus of the base field, from SEC 2 v2 §2.4.1.

It is `2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1`, which SEC 2 also writes. -/
def Fp.modulus : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- `n`, the order of the generator, from SEC 2 v2 §2.4.1. -/
def Fn.modulus : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

-- Named explicitly, since both anonymous instances would get the same name.
instance Fp.instNeZeroModulus : NeZero Fp.modulus := ⟨by decide⟩

instance Fn.instNeZeroModulus : NeZero Fn.modulus := ⟨by decide⟩

/-- An element of the base field. -/
abbrev Fp := Fin Fp.modulus

/-- An element of the scalar field. -/
abbrev Fn := Fin Fn.modulus

/-- `a^e` in `Fin m`, for `e < 2^fuel`, by square and multiply.

Each step reads the low bit of `e`, then squares the base for the next bit.

It recurses on `fuel`, so the kernel can run it. -/
def Fin.powBits {m : Nat} [NeZero m] : Nat → Fin m → Nat → Fin m
  | 0, _, _ => 1
  | fuel + 1, a, e =>
    -- `a^e = a^(e mod 2) * (a^2)^(e / 2)`.
    let half := Fin.powBits fuel (a * a) (e / 2)
    if e % 2 = 1 then a * half else half

namespace Fp

/-- `a^e`, for an exponent below `2^256`. -/
def pow (a : Fp) (e : Nat) : Fp := Fin.powBits 256 a e

/-- The inverse of `a`, by Fermat's little theorem: `a^(p - 2)`.

It sends `0` to `0`. -/
def inv (a : Fp) : Fp := a.pow (modulus - 2)

/-- A square root of `a`, or `none` when `a` is not a square.

Since `p = 3 mod 4`, a square `a` has the root `c = a^((p + 1) / 4)`:
`c^2 = a^((p + 1) / 2) = a * a^((p - 1) / 2) = a`, by Euler's criterion.

When `a` is not a square, `c^2 != a`, so the check rejects it. -/
def sqrt (a : Fp) : Option Fp :=
  let c := a.pow ((modulus + 1) / 4)
  if c * c = a then some c else none

end Fp

namespace Fn

/-- `a^e`, for an exponent below `2^256`. -/
def pow (a : Fn) (e : Nat) : Fn := Fin.powBits 256 a e

/-- The inverse of `a`, by Fermat's little theorem: `a^(n - 2)`.

It sends `0` to `0`. -/
def inv (a : Fn) : Fn := a.pow (modulus - 2)

end Fn

end EthLib.Cryptography.Secp256k1
