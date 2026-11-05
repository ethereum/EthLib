module

public import EthLib.Cryptography.Bls.Fp2
public import EthLib.Cryptography.Proofs.BaseField

/-!
# Proofs: the BLS12-381 extensions under a map of base fields

A map of base fields acts on each coordinate of an extension element.

When it respects the operations of the base fields, it commutes with each extension operation.

So a computation on one base field gives the same result on the other, once mapped.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open EthLib.Cryptography.BaseField (Hom)

variable {F G : Type} [BaseField F] [BaseField G]

namespace Fp2

/-- The map of base fields, applied to both coordinates. -/
def map (f : Hom F G) (a : Fp2 F) : Fp2 G := ⟨f a.c0, f a.c1⟩

theorem map_zero (f : Hom F G) : map f zero = zero := by
  simp only [map, zero, f.map_zero]

theorem map_one (f : Hom F G) : map f one = one := by
  simp only [map, one, f.map_zero, f.map_one]

theorem map_i (f : Hom F G) : map f i = i := by
  simp only [map, i, f.map_zero, f.map_one]

theorem map_ofFp (f : Hom F G) (x : F) : map f (ofFp x) = ofFp (f x) := by
  simp only [map, ofFp, f.map_zero]

theorem map_add (f : Hom F G) (a b : Fp2 F) : map f (a + b) = map f a + map f b := by
  show map f (add a b) = add (map f a) (map f b)
  simp only [map, add, f.map_add]

theorem map_sub (f : Hom F G) (a b : Fp2 F) : map f (a - b) = map f a - map f b := by
  show map f (sub a b) = sub (map f a) (map f b)
  simp only [map, sub, f.map_sub]

theorem map_neg (f : Hom F G) (a : Fp2 F) : map f (-a) = -map f a := by
  show map f (neg a) = neg (map f a)
  simp only [map, neg, f.map_neg]

theorem map_mul (f : Hom F G) (a b : Fp2 F) : map f (a * b) = map f a * map f b := by
  show map f (mul a b) = mul (map f a) (map f b)
  simp only [map, mul, f.map_add, f.map_sub, f.map_mul]

theorem map_beq (f : Hom F G) (a b : Fp2 F) : (map f a).beq (map f b) = a.beq b := by
  simp only [map, beq, f.map_beq]

theorem map_isZero (f : Hom F G) (a : Fp2 F) : (map f a).isZero = a.isZero := by
  simp only [map, isZero, f.map_isZero]

theorem map_mulByOnePlusI (f : Hom F G) (a : Fp2 F) :
    map f a.mulByOnePlusI = (map f a).mulByOnePlusI := by
  simp only [map, mulByOnePlusI, f.map_add, f.map_sub]

theorem map_conjugate (f : Hom F G) (a : Fp2 F) : map f a.conjugate = (map f a).conjugate := by
  simp only [map, conjugate, f.map_neg]

theorem map_inverse (f : Hom F G) (a : Fp2 F) : map f a.inverse = (map f a).inverse := by
  simp only [map, inverse, f.map_mul, f.map_neg, f.map_inverse, f.map_add]

theorem map_div (f : Hom F G) (a b : Fp2 F) : map f (a / b) = map f a / map f b := by
  show map f (a * b.inverse) = map f a * (map f b).inverse
  rw [map_mul, map_inverse]

theorem map_powNat (f : Hom F G) (a : Fp2 F) (e : Nat) :
    map f (powNat a e) = powNat (map f a) e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [powNat.eq_1 a e, powNat.eq_1 (map f a) e]
    split
    · exact map_one f
    · have h := ih (e / 2) (by omega) (a * a)
      rw [map_mul] at h
      split <;> simp only [map_mul, h]

end Fp2

end EthLib.Cryptography.Bls
