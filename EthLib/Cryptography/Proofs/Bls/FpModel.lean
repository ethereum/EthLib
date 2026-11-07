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

/-- Square-and-multiply exponentiation in the model. -/
def powNat (base : Fin modulus) (e : Nat) : Fin modulus :=
  if e = 0 then ⟨1, by decide⟩
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
termination_by e
decreasing_by omega

/-- The square root in the model, `a ^ ((p + 1) / 4)` when its square is `a`. -/
def sqrt (a : Fin modulus) : Option (Fin modulus) :=
  let cand := powNat a ((modulus + 1) / 4)
  if (cand * cand).val == a.val then some cand else none

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
  powNat := powNat
  sqrt := sqrt
  sgn0 a := a.val % 2 == 1

end Fp.Model

/-- The element of the model with the integer of `a`. -/
def Fp.toModelFun (a : Fp) : Fin Fp.modulus := ⟨a.val, Fp.val_lt a⟩

/-- The model's product of two images is the image of the product. -/
theorem Fp.toModelFun_mul (x y : Fp) :
    Fp.toModelFun x * Fp.toModelFun y = Fp.toModelFun (x * y) :=
  Fin.ext (Fp.val_mul x y).symm

/-- Two elements have equal integers exactly when they pass the test of `Fp`. -/
theorem Fp.val_beq_val (a b : Fp) : (a.val == b.val) = a.beq b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Fp.beq_iff]
  exact ⟨Fp.ext, fun h => h ▸ rfl⟩

open scoped EthLib.Cryptography.Bls.Fp in
/-- The model's power of an image is the image of the power. -/
theorem Fp.powNat_toModelFun (a : Fp) (n : Nat) :
    Fp.Model.powNat (Fp.toModelFun a) n = Fp.toModelFun (a.powNat n) := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    rw [Fp.Model.powNat.eq_1]
    by_cases h0 : n = 0
    · subst h0
      rw [ite_eq_left rfl, Fp.powNat_eq_pow, pow_zero]
      exact Fin.ext Fp.val_one.symm
    rw [ite_eq_right h0]
    dsimp only
    rw [Fp.toModelFun_mul, ih (n / 2) (by omega), Fp.powNat_eq_pow, Fp.powNat_eq_pow,
      show a * a = a ^ 2 from (sq a).symm]
    by_cases h2 : n % 2 = 1
    · rw [ite_eq_left h2, Fp.toModelFun_mul, ← pow_mul,
        show a * a ^ (2 * (n / 2)) = a ^ (2 * (n / 2) + 1) from (pow_succ' a _).symm]
      congr 2
      omega
    · rw [ite_eq_right h2, ← pow_mul]
      congr 2
      omega

/-- The map from `Fp` to the model of the kernel checks. -/
def Fp.toModel : BaseField.Hom Fp Fp.Model where
  toFun := Fp.toModelFun
  map_add a b := Fin.ext (Fp.val_add a b)
  map_sub a b := Fin.ext (Fp.val_sub a b)
  map_mul a b := Fin.ext (Fp.val_mul a b)
  map_neg a := Fin.ext (Fp.val_neg a)
  map_zero := Fin.ext Fp.val_zero
  map_one := Fin.ext Fp.val_one
  map_ofNat n := Fin.ext (Fp.val_ofNat n)
  map_beq a b := Fp.val_beq_val a b
  map_isZero a := (Fp.isZero_eq a).symm
  map_inverse a := by
    -- Both integers are below `p`, and both stand for the inverse of `a` in `ZMod p`.
    apply Fin.ext
    change a.inverse.val = (Fin.inverse (Fp.toModelFun a)).val
    rw [← ZMod.val_natCast_of_lt (Fp.val_lt a.inverse),
      ← ZMod.val_natCast_of_lt (Fin.inverse (Fp.toModelFun a)).isLt, Fin.inverse_val,
      Fp.val_eq, ZMod.natCast_zmod_val, Fp.toZMod_inverse]
    change _ = ((a.val : ZMod Fp.modulus)⁻¹).val
    rw [Fp.val_eq, ZMod.natCast_zmod_val]
  map_powNat a n := (Fp.powNat_toModelFun a n).symm
  map_sqrt a := by
    change Fp.Model.sqrt (Fp.toModelFun a) = (Fp.sqrt a).toOption.map Fp.toModelFun
    rw [Fp.Model.sqrt, Fp.sqrt, Fp.powLimbs_sqrtExponent, Fp.powNat_toModelFun]
    generalize Fp.powNat a ((modulus + 1) / 4) = c
    rw [Fp.toModelFun_mul]
    change (if ((c * c).val == a.val) = true then _ else _) = _
    rw [Fp.val_beq_val]
    -- Splitting on the test itself would make the kernel compute it.
    by_cases h : (c * c).beq a = true
    · rw [ite_eq_left h, ite_eq_left h]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
      rfl
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
theorem toModel_numeral (n : Nat) [n.AtLeastTwo] :
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
  rw [toModel.map_beq, baseField_beq] at h
  exact Fp.beq_iff.mp h

/-- Two elements differ when their images in the model do. -/
theorem ne_of_model {a b : Fp} (h : BaseField.beq (toModel a) (toModel b) = false) : a ≠ b := by
  rintro rfl
  rw [toModel.map_beq, baseField_beq, beq, beq_self_eq_true] at h
  exact Bool.noConfusion h

/-- The square root succeeds in `Fp` exactly when it succeeds in the model. -/
theorem sqrt_isOk_eq (a : Fp) : (Fp.sqrt a).isOk = (BaseField.sqrt (toModel a)).isSome := by
  rw [toModel.map_sqrt, Option.isSome_map, baseField_sqrt]
  cases Fp.sqrt a <;> rfl

end Fp

end EthLib.Cryptography.Bls
