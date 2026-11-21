module

public import EthLib.Cryptography.Inverse

/-!
# `Secp256r1.Field`

The two prime fields of secp256r1, from SEC 2 v2 §2.4.2.

- `Fp` is the base field, integers mod the prime `p`.
- `Fn` is the scalar field, integers mod the prime order `n` of the generator.

Each field is `Fin` of its modulus, so every element is below the modulus by construction.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- `p`, the modulus of the base field, from SEC 2 v2 §2.4.2. -/
def Fp.modulus : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

/-- `n`, the order of the generator, from SEC 2 v2 §2.4.2. -/
def Fn.modulus : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

-- Named explicitly, since both anonymous instances would get the same name.
instance Fp.instNeZeroModulus : NeZero Fp.modulus := ⟨by decide⟩
instance Fn.instNeZeroModulus : NeZero Fn.modulus := ⟨by decide⟩

/-- An element of the base field. -/
abbrev Fp := Fin Fp.modulus

/-- An element of the scalar field. -/
abbrev Fn := Fin Fn.modulus

/-- The inverse in `Fp`, by the extended Euclidean algorithm, and 0 for 0. -/
def Fp.inv (a : Fp) : Fp := Fin.inverse a

/-- The inverse in `Fn`, by the extended Euclidean algorithm, and 0 for 0. -/
def Fn.inv (a : Fn) : Fn := Fin.inverse a

end EthLib.Cryptography.Secp256r1
