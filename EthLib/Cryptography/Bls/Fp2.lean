module

public import EthLib.Cryptography.Bls.Fp
public import EthLib.Cryptography.Fp2

/-!
# `Fp2`

The quadratic extension `Fp2 = Fp[i] / (i^2 + 1)` of BLS12-381, with elements `c0 + c1 i`.

It is the generic quadratic extension, at the base field `Fp` unless stated.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- An element of the quadratic extension of `F`, written `c0 + c1 · i` with `i^2 = −1`.

The base field is `Fp` unless stated, so `Fp2` alone is the extension of BLS12-381. -/
abbrev Fp2 (F : Type := Fp) : Type := Cryptography.Fp2 F

namespace Fp2

-- The constants and operations of the generic extension keep their names here.
--
-- The ones read with field notation are left out, since an alias would hide the generic one.
export Cryptography.Fp2 (mk zero i ofFp ofNats add sub neg mul powNat)

variable {F : Type} [FieldOps F]

/-- The element 1.

It is a constant rather than an alias, since other modules name it through the type alone. -/
abbrev one : Fp2 F := Cryptography.Fp2.one

/-- Multiply by `1 + i`, the cubic-extension non-residue `ξ`. -/
@[inline] def mulByOnePlusI (a : Fp2 F) : Fp2 F :=
  -- `(c0 + c1 i)(1 + i) = (c0 - c1) + (c0 + c1) i`, since `i^2 = -1`.
  ⟨a.c0 - a.c1, a.c0 + a.c1⟩

end Fp2

end EthLib.Cryptography.Bls
