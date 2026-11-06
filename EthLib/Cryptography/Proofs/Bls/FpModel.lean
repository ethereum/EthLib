module

public import EthLib.Cryptography.Bls.Fp
public import EthLib.Cryptography.Proofs.BaseField
public import EthLib.Cryptography.Proofs.Bls.FpZMod

/-!
# Proofs: the base field that the kernel computes in

The extensions, curves and pairing of BLS12-381 are written once, generic in the base field.

Proofs instantiate them at the model of this file, `Fin p` with the operations of `Fin`.

The kernel evaluates those operations on natural numbers, so a concrete check stays cheap.

The map from `Fp` to the model respects every operation of a base field.

So the lemmas that commute a map with each definition carry a check from the model to `Fp`.

A proof can state its check at the model and transfer it, so that the kernel does not run `Fp`.
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

/-- The image of the element of `n` is the element of `n` in the model. -/
theorem toModel_ofNat (n : Nat) : toModel (Fp.ofNat n) = BaseField.ofNat n := toModel.map_ofNat n

/-- The image of zero is the zero of the model. -/
theorem toModel_zero : toModel Fp.zero = BaseField.zero := toModel.map_zero

/-- The image of one is the one of the model. -/
theorem toModel_one : toModel Fp.one = BaseField.one := toModel.map_one

/-- The image of the numeral `0` is the zero of the model. -/
theorem toModel_zero' : toModel (0 : Fp) = BaseField.zero := toModel.map_zero

/-- The image of the numeral `1` is the one of the model. -/
theorem toModel_one' : toModel (1 : Fp) = BaseField.one := toModel.map_one

/-- The image of a numeral is the element of the same integer in the model. -/
theorem toModel_numeral (n : Nat) :
    toModel (no_index (OfNat.ofNat n : Fp)) = BaseField.ofNat n :=
  toModel.map_ofNat n

/-- The image of a sum is the sum of the images. -/
theorem toModel_add (a b : Fp) : toModel (a + b) = toModel a + toModel b := toModel.map_add a b

/-- The image of a difference is the difference of the images. -/
theorem toModel_sub (a b : Fp) : toModel (a - b) = toModel a - toModel b := toModel.map_sub a b

/-- The image of a product is the product of the images. -/
theorem toModel_mul (a b : Fp) : toModel (a * b) = toModel a * toModel b := toModel.map_mul a b

/-- The image of a negation is the negation of the image. -/
theorem toModel_neg (a : Fp) : toModel (-a) = -toModel a := toModel.map_neg a

/-- The image of an inverse is the inverse of the image. -/
theorem toModel_inverse (a : Fp) : toModel a.inverse = BaseField.inverse (toModel a) :=
  toModel.map_inverse a

/-- The image of a power is the power of the image. -/
theorem toModel_powNat (a : Fp) (n : Nat) :
    toModel (a.powNat n) = BaseField.powNat (toModel a) n :=
  toModel.map_powNat a n

/-- Two elements are equal when their images in the model are. -/
theorem eq_of_model {a b : Fp} (h : BaseField.beq (toModel a) (toModel b) = true) : a = b := by
  rw [toModel.map_beq, baseField_beq, beq, beq_iff_eq] at h
  exact ext h

/-- Two elements differ when their images in the model do. -/
theorem ne_of_model {a b : Fp} (h : BaseField.beq (toModel a) (toModel b) = false) : a ≠ b := by
  rintro rfl
  rw [toModel.map_beq, baseField_beq, beq, beq_self_eq_true] at h
  exact Bool.noConfusion h

end Fp

end EthLib.Cryptography.Bls
