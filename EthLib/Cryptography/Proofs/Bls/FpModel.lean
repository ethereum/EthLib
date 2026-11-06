module

public import EthLib.Cryptography.Bls.Fp
public import EthLib.Cryptography.Proofs.BaseField

/-!
# Proofs: the base field that the kernel computes in

The extensions, curves and pairing of BLS12-381 are written once, generic in the base field.

Proofs instantiate them at the model of this file, `Fin p` with the operations of `Fin`.

The kernel evaluates those operations on natural numbers, so a concrete check stays cheap.

The map from `Fp` to the model respects every operation of a base field.

So the lemmas that commute a map with each definition carry a check from the model to `Fp`.

A proof states its check at the model, then transfers it, and never makes the kernel run `Fp`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- The integers mod `p` as `Fin p`, the base field of the kernel checks. -/
def Fp.Model : Type := Fin Fp.modulus

namespace Fp.Model

/-- The integer below `p` that an element of the model stands for. -/
def val (a : Model) : Nat := Fin.val (n := modulus) a

/-- The operations of `Fin p`: the sum, difference, product and negation reduce mod `p`.

The inverse is the extended Euclidean algorithm, and the square root is `a ^ ((p + 1) / 4)`. -/
instance : BaseField Model where
  toAdd := inferInstanceAs (Add (Fin modulus))
  toSub := inferInstanceAs (Sub (Fin modulus))
  toMul := inferInstanceAs (Mul (Fin modulus))
  toNeg := inferInstanceAs (Neg (Fin modulus))
  zero := (⟨0, Fp.modulus_pos⟩ : Fin modulus)
  one := (⟨1, by decide⟩ : Fin modulus)
  ofNat n := Fin.ofNat modulus n
  beq a b := a.val == b.val
  isZero a := a.val == 0
  inverse a := Fin.inverse (a : Fin modulus)
  powNat := Fp.powNat
  sqrt a := match Fp.sqrt a with
    | .ok s => some s
    | .error _ => none
  sgn0 a := a.val % 2 == 1

end Fp.Model

/-- The map from `Fp` to the model of the kernel checks. -/
def Fp.toModel : BaseField.Hom Fp Fp.Model where
  toFun a := a
  map_add _ _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl
  map_neg _ := rfl
  map_zero := rfl
  map_one := rfl
  map_ofNat _ := rfl
  map_beq _ _ := rfl
  map_isZero _ := rfl
  map_inverse _ := rfl
  map_powNat _ _ := rfl
  map_sqrt a := by
    change (match Fp.sqrt a with | .ok s => some s | .error _ => none) =
      (match Fp.sqrt a with | .ok s => some s | .error _ => none).map id
    cases Fp.sqrt a <;> rfl
  map_sgn0 _ := rfl

namespace Fp

/-- The image of an element in the model stands for the same integer. -/
theorem val_toModel (a : Fp) : (toModel a).val = a.val := rfl

end Fp

end EthLib.Cryptography.Bls
