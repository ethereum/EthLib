module

public import EthLib.Cryptography.Bls.Fp12
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

namespace Fp6

/-- The map of base fields, applied to the three coordinates in `Fp2`. -/
def map (f : Hom F G) (a : Fp6 F) : Fp6 G := ⟨a.c0.map f, a.c1.map f, a.c2.map f⟩

theorem map_zero (f : Hom F G) : map f zero = zero := by
  simp only [map, zero, Fp2.map_zero]

theorem map_one (f : Hom F G) : map f one = one := by
  simp only [map, one, Fp2.map_zero, Fp2.map_one]

theorem map_v (f : Hom F G) : map f v = v := by
  simp only [map, v, Fp2.map_zero, Fp2.map_one]

theorem map_ofFp2 (f : Hom F G) (x : Fp2 F) : map f (ofFp2 x) = ofFp2 (x.map f) := by
  simp only [map, ofFp2, Fp2.map_zero]

theorem map_add (f : Hom F G) (a b : Fp6 F) : map f (a + b) = map f a + map f b := by
  show map f (add a b) = add (map f a) (map f b)
  simp only [map, add, Fp2.map_add]

theorem map_sub (f : Hom F G) (a b : Fp6 F) : map f (a - b) = map f a - map f b := by
  show map f (sub a b) = sub (map f a) (map f b)
  simp only [map, sub, Fp2.map_sub]

theorem map_neg (f : Hom F G) (a : Fp6 F) : map f (-a) = -map f a := by
  show map f (neg a) = neg (map f a)
  simp only [map, neg, Fp2.map_neg]

theorem map_mul (f : Hom F G) (a b : Fp6 F) : map f (a * b) = map f a * map f b := by
  show map f (mul a b) = mul (map f a) (map f b)
  simp only [map, mul, Fp2.map_add, Fp2.map_sub, Fp2.map_mul, Fp2.map_mulByOnePlusI]

theorem map_beq (f : Hom F G) (a b : Fp6 F) : (map f a).beq (map f b) = a.beq b := by
  simp only [map, beq, Fp2.map_beq]

theorem map_isZero (f : Hom F G) (a : Fp6 F) : (map f a).isZero = a.isZero := by
  simp only [map, isZero, Fp2.map_isZero]

theorem map_mulByV (f : Hom F G) (a : Fp6 F) : map f a.mulByV = (map f a).mulByV := by
  simp only [map, mulByV, Fp2.map_mulByOnePlusI]

theorem map_inverse (f : Hom F G) (a : Fp6 F) : map f a.inverse = (map f a).inverse := by
  simp only [map, inverse, Fp2.map_add, Fp2.map_sub, Fp2.map_mul, Fp2.map_mulByOnePlusI,
    Fp2.map_inverse]

theorem map_div (f : Hom F G) (a b : Fp6 F) : map f (a / b) = map f a / map f b := by
  show map f (a * b.inverse) = map f a * (map f b).inverse
  rw [map_mul, map_inverse]

end Fp6

namespace Fp12

/-- The map of base fields, applied to the two coordinates in `Fp6`. -/
def map (f : Hom F G) (a : Fp12 F) : Fp12 G := ⟨a.c0.map f, a.c1.map f⟩

theorem map_zero (f : Hom F G) : map f zero = zero := by
  simp only [map, zero, Fp6.map_zero]

theorem map_one (f : Hom F G) : map f one = one := by
  simp only [map, one, Fp6.map_zero, Fp6.map_one]

theorem map_add (f : Hom F G) (a b : Fp12 F) : map f (a + b) = map f a + map f b := by
  show map f (add a b) = add (map f a) (map f b)
  simp only [map, add, Fp6.map_add]

theorem map_sub (f : Hom F G) (a b : Fp12 F) : map f (a - b) = map f a - map f b := by
  show map f (sub a b) = sub (map f a) (map f b)
  simp only [map, sub, Fp6.map_sub]

theorem map_neg (f : Hom F G) (a : Fp12 F) : map f (-a) = -map f a := by
  show map f (neg a) = neg (map f a)
  simp only [map, neg, Fp6.map_neg]

theorem map_mul (f : Hom F G) (a b : Fp12 F) : map f (a * b) = map f a * map f b := by
  show map f (mul a b) = mul (map f a) (map f b)
  simp only [map, mul, Fp6.map_add, Fp6.map_sub, Fp6.map_mul, Fp6.map_mulByV]

theorem map_beq (f : Hom F G) (a b : Fp12 F) : (map f a).beq (map f b) = a.beq b := by
  simp only [map, beq, Fp6.map_beq]

theorem map_isOne (f : Hom F G) (a : Fp12 F) : (map f a).isOne = a.isOne := by
  simp only [isOne, map, ← Fp6.map_one f, Fp6.map_beq, Fp6.map_isZero]

theorem map_square (f : Hom F G) (a : Fp12 F) : map f a.square = (map f a).square := by
  simp only [square, map_mul]

theorem map_inverse (f : Hom F G) (a : Fp12 F) : map f a.inverse = (map f a).inverse := by
  simp only [map, inverse, Fp6.map_sub, Fp6.map_mul, Fp6.map_mulByV, Fp6.map_inverse,
    Fp6.map_neg]

theorem map_conjugate (f : Hom F G) (a : Fp12 F) : map f a.conjugate = (map f a).conjugate := by
  simp only [map, conjugate, Fp6.map_neg]

theorem map_frobeniusCoeff (f : Hom F G) :
    (frobeniusCoeff : Fp2 F).map f = frobeniusCoeff := by
  rw [frobeniusCoeff, frobeniusCoeff, Fp2.map_powNat]
  congr 1
  simp only [Fp2.map, f.map_one]

theorem map_frobenius (f : Hom F G) (a : Fp12 F) : map f a.frobenius = (map f a).frobenius := by
  simp only [map, frobenius, Fp6.map, Fp2.map_mul, Fp2.map_conjugate, map_frobeniusCoeff]

theorem map_powNat (f : Hom F G) (a : Fp12 F) (e : Nat) :
    map f (powNat a e) = powNat (map f a) e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [powNat.eq_1 a e, powNat.eq_1 (map f a) e]
    split
    · exact map_one f
    · have h := ih (e / 2) (by omega) (a * a)
      rw [map_mul] at h
      split <;> simp only [map_mul, h]

end Fp12

end EthLib.Cryptography.Bls
