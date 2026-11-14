module

public import EthLib.Cryptography.Inverse
public import EthLib.Cryptography.Montgomery

/-!
# `Secp256k1.Field`

The two prime fields of secp256k1, from SEC 2 v2 §2.4.1.

- `Fp` is the base field, integers mod `p = 2^256 - 2^32 - 977`, for the coordinates.
- `Fn` is the scalar field, integers mod the order `n` of the generator.

The private key and the integers `r` and `s` of a signature live in `Fn`.

Each field is `Fin` of its modulus, so every element is below the modulus by construction.

Core gives `Fin` its `+`, `-`, `*` and negation, all reduced mod the modulus.

Exponentiation in `Fp` and scalar multiplication keep intermediate values in Montgomery limbs.

An inverse is a power, by Fermat's little theorem.

A square root is a power too, because `p = 3 mod 4`.

No division is defined.

Core's `/` on `Fin` divides the integers, so the specification never writes it.
-/

@[expose] public section

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

/-- The base modulus of SEC 2 v2 §2.4.1, with radix `R = 2^256`.

Each constant is checked against its defining equation. -/
@[inline] def params : Montgomery.Modulus 8 where
  p := modulus
  pLimbs := ⟨0xfffffc2f, 0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff⟩
  r1 := ⟨0x3d1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0⟩
  r2 := ⟨0xe90a1, 0x7a2, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0⟩
  pm2 := ⟨0xfffffc2d, 0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff⟩
  pinv := 0xd2253531
  pLimbs_spec := by decide
  pinv_spec := by decide
  r1_spec := by decide
  r2_spec := by decide
  pm2_spec := by decide

/-- A base-field element held in eight Montgomery limbs. -/
abbrev Montgomery := EthLib.Cryptography.Montgomery params

instance (k : Nat) : OfNat Montgomery k := ⟨Montgomery.ofNat k⟩

/-- Convert a coordinate to Montgomery form once before a chain of curve operations. -/
@[no_expose, inline] def toMontgomery (a : Fp) : Montgomery := Montgomery.ofNat a.val

/-- Read a Montgomery coordinate as the same element of `Fin p`.

The conversion laws keep proof checking from expanding symbolic limb arithmetic. -/
@[no_expose, inline] def ofMontgomery (a : Montgomery) : Fp :=
  ⟨a.toNat, by
    rw [EthLib.Cryptography.Montgomery.toNat_eq_val]
    exact (EthLib.Cryptography.Montgomery.mulLimbs params a.limbs a.lt _).lt⟩

/-- `a^e`, for an exponent below `2^256`. -/
def pow (a : Fp) (e : Nat) : Fp :=
  ofMontgomery (Montgomery.powLimbs (toMontgomery a) (Montgomery.Limbs.ofNat e))

/-- The inverse of `a`, as `a^(p - 2)` by Fermat's little theorem.

It sends `0` to `0`. -/
def inv (a : Fp) : Fp := ofMontgomery (Montgomery.inv (toMontgomery a))

/-- A square root of `a`, or `none` when `a` is not a square.

Since `p = 3 mod 4`, a square `a` has the root `c = a^((p + 1) / 4)`.

By Euler's criterion, `c^2 = a^((p + 1) / 2) = a * a^((p - 1) / 2) = a`.

When `a` is not a square, `c^2 != a`, so the check rejects it. -/
def sqrt (a : Fp) : Option Fp :=
  let c := a.pow ((modulus + 1) / 4)
  if c * c = a then some c else none

end Fp

namespace Fn

/-- The scalar modulus of SEC 2 v2 §2.4.1, with radix `R = 2^256`.

Each constant is checked against its defining equation. -/
@[inline] def params : Montgomery.Modulus 8 where
  p := modulus
  pLimbs := ⟨0xd0364141, 0xbfd25e8c, 0xaf48a03b, 0xbaaedce6, 0xfffffffe, 0xffffffff,
    0xffffffff, 0xffffffff⟩
  r1 := ⟨0x2fc9bebf, 0x402da173, 0x50b75fc4, 0x45512319, 0x1, 0x0, 0x0, 0x0⟩
  r2 := ⟨0x67d7d140, 0x896cf214, 0x0e7cf878, 0x741496c2, 0x5bcd07c6, 0xe697f5e4,
    0x81c69bc5, 0x9d671cd5⟩
  pm2 := ⟨0xd036413f, 0xbfd25e8c, 0xaf48a03b, 0xbaaedce6, 0xfffffffe, 0xffffffff,
    0xffffffff, 0xffffffff⟩
  pinv := 0x5588b13f
  pLimbs_spec := by decide
  pinv_spec := by decide
  r1_spec := by decide
  r2_spec := by decide
  pm2_spec := by decide

/-- A scalar-field element held in eight Montgomery limbs. -/
abbrev Montgomery := EthLib.Cryptography.Montgomery params

/-- Convert a scalar to Montgomery form before inversion. -/
@[no_expose, inline] def toMontgomery (a : Fn) : Montgomery := Montgomery.ofNat a.val

/-- Read a Montgomery scalar as the same element of `Fin n`.

The conversion laws keep proof checking from expanding symbolic limb arithmetic. -/
@[no_expose, inline] def ofMontgomery (a : Montgomery) : Fn :=
  ⟨a.toNat, by
    rw [EthLib.Cryptography.Montgomery.toNat_eq_val]
    exact (EthLib.Cryptography.Montgomery.mulLimbs params a.limbs a.lt _).lt⟩

/-- `a^e`, for an exponent below `2^256`. -/
def pow (a : Fn) (e : Nat) : Fn := Fin.powBits 256 a e

/-- The inverse of `a`, as `a^(n - 2)` in Montgomery form, by Fermat's little theorem.

It sends `0` to `0`. -/
def inv (a : Fn) : Fn := ofMontgomery (Montgomery.inv (toMontgomery a))

end Fn

end EthLib.Cryptography.Secp256k1
