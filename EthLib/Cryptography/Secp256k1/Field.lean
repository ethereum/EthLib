module

public import EthLib.Base.Pow

/-!
# `Secp256k1.Field`

The two prime fields of secp256k1, from SEC 2 v2 §2.4.1.

- `Fp` is the base field, integers mod `p = 2^256 - 2^32 - 977`, for the coordinates.
- `Fn` is the scalar field, integers mod the order `n` of the generator.

Other files of this module give the Montgomery form of `Fp`, the inverses and the square root.

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

/-- An element of the base field, for the coordinates. -/
abbrev Fp :=
  -- Each field is `Fin` of its modulus, so every element is below the modulus by construction.
  --
  -- Core gives `Fin` its `+`, `-`, `*` and negation, all reduced mod the modulus.
  Fin Fp.modulus

/-- An element of the scalar field.

The private key and the integers `r` and `s` of a signature live in it. -/
abbrev Fn := Fin Fn.modulus

namespace Fp

/-- `a^e`, for an exponent below `2^256`. -/
def pow (a : Fp) (e : Nat) : Fp := Base.powBits 256 a e

end Fp

namespace Fn

/-- `a^e`, for an exponent below `2^256`. -/
def pow (a : Fn) (e : Nat) : Fn := Base.powBits 256 a e

end Fn

end EthLib.Cryptography.Secp256k1
