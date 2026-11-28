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

open Cryptography.Fp2 (c0 c1 beq isZero conjugate inverse)

/-- The map of base fields, applied to both coordinates. -/
def map (f : Hom F G) (a : Fp2 F) : Fp2 G := ⟨f a.c0, f a.c1⟩

/-- The map of an element given by its two coordinates. -/
theorem map_mk (f : Hom F G) (c0 c1 : F) : map f ⟨c0, c1⟩ = ⟨f c0, f c1⟩ := rfl

theorem map_zero (f : Hom F G) : map f zero = zero := by
  simp only [map, zero, f.map_zero]

theorem map_one (f : Hom F G) : map f one = one := by
  simp only [map, one, Cryptography.Fp2.one, f.map_zero, f.map_one]

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

theorem map_square (f : Hom F G) (a : Fp2 F) :
    map f (FieldOps.square a) = FieldOps.square (map f a) := by
  show map f (Cryptography.Fp2.square a) = Cryptography.Fp2.square (map f a)
  simp only [map, Cryptography.Fp2.square, f.map_add, f.map_sub, f.map_mul]

theorem map_mulFp (f : Hom F G) (a : Fp2 F) (x : F) :
    map f (a.mulFp x) = (map f a).mulFp (f x) := by
  simp only [map, Cryptography.Fp2.mulFp, f.map_mul]

theorem map_beq (f : Hom F G) (a b : Fp2 F) : (map f a).beq (map f b) = a.beq b := by
  simp only [map, beq, f.map_beq]

theorem map_isZero (f : Hom F G) (a : Fp2 F) : (map f a).isZero = a.isZero := by
  simp only [map, isZero, f.map_isZero]

theorem map_mulByOnePlusI (f : Hom F G) (a : Fp2 F) :
    map f a.mulByOnePlusI = (map f a).mulByOnePlusI := by
  simp only [map, mulByOnePlusI, f.map_add, f.map_sub]

theorem map_conjugate (f : Hom F G) (a : Fp2 F) : map f a.conjugate = (map f a).conjugate := by
  simp only [map, conjugate, f.map_neg]

/-- The square root from a root of the norm commutes with a map of base fields. -/
theorem map_sqrtOfNormRoot (f : Hom F G) (a : Fp2 F) (s : F) :
    Cryptography.Fp2.sqrtOfNormRoot (map f a) (f s) =
      map f (Cryptography.Fp2.sqrtOfNormRoot a s) := by
  obtain ⟨a0, a1⟩ := a
  simp only [Cryptography.Fp2.sqrtOfNormRoot, map, f.map_isZero, ← f.map_add, ← f.map_ofNat,
    ← f.map_inverse, ← f.map_mul, f.map_invSqrtCandidate, f.map_beq]
  cases BaseField.isZero a1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split <;> simp only [f.map_mul, f.map_inverse, f.map_ofNat]
  · simp only [↓reduceIte]
    split <;> simp only [f.map_zero]

/-- The square root commutes with a map of base fields. -/
theorem map_sqrt (f : Hom F G) (a : Fp2 F) :
    Cryptography.Fp2.sqrt (map f a) = (Cryptography.Fp2.sqrt a).map (map f) := by
  have h0 : (map f a).c0 = f a.c0 := rfl
  have h1 : (map f a).c1 = f a.c1 := rfl
  simp only [Cryptography.Fp2.sqrt, h0, h1, f.map_isZero, ← f.map_mul, ← f.map_add, f.map_sqrt]
  cases BaseField.isZero a.c1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases BaseField.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | none => rfl
    | some s => simp only [Option.map_some, map_sqrtOfNormRoot]
  · simp only [↓reduceIte, Option.map_some, ← map_sqrtOfNormRoot, f.map_zero]

/-- The sign `sgn0` is kept by a map of base fields. -/
theorem map_sgn0 (f : Hom F G) (x : Fp2 F) : (map f x).sgn0 = x.sgn0 := by
  simp only [Cryptography.Fp2.sgn0, map, f.map_sgn0, f.map_isZero]

theorem map_inverse (f : Hom F G) (a : Fp2 F) : map f a.inverse = (map f a).inverse := by
  simp only [map, inverse, f.map_mul, f.map_neg, f.map_inverse, f.map_add]

theorem map_div (f : Hom F G) (a b : Fp2 F) : map f (a / b) = map f a / map f b := by
  show map f (a * b.inverse) = map f a * (map f b).inverse
  rw [map_mul, map_inverse]

theorem map_powNat (f : Hom F G) (a : Fp2 F) (e : Nat) :
    map f (powNat a e) = powNat (map f a) e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [Cryptography.Fp2.powNat.eq_1 a e, Cryptography.Fp2.powNat.eq_1 (map f a) e]
    split
    · exact map_one f
    · have h := ih (e / 2) (by omega) (a * a)
      rw [map_mul] at h
      split <;> simp only [map_mul, h]

/-- The map of base fields on both coordinates respects the field operations of the extension. -/
def hom (f : Hom F G) : FieldOps.Hom (Fp2 F) (Fp2 G) where
  toFun := map f
  map_add := map_add f
  map_sub := map_sub f
  map_mul := map_mul f
  map_neg := map_neg f
  map_zero := map_zero f
  map_one := map_one f
  map_beq := map_beq f
  map_isZero := map_isZero f
  map_inverse := map_inverse f
  map_square := map_square f

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

theorem map_mulBy01 (f : Hom F G) (a : Fp6 F) (b0 b1 : Fp2 F) :
    map f (a.mulBy01 b0 b1) = (map f a).mulBy01 (b0.map f) (b1.map f) := by
  simp only [map, mulBy01, Fp2.map_add, Fp2.map_sub, Fp2.map_mul, Fp2.map_mulByOnePlusI]

theorem map_mulBy1 (f : Hom F G) (a : Fp6 F) (b1 : Fp2 F) :
    map f (a.mulBy1 b1) = (map f a).mulBy1 (b1.map f) := by
  simp only [map, mulBy1, Fp2.map_mul, Fp2.map_mulByOnePlusI]

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
  simp only [map, square, Fp6.map_add, Fp6.map_sub, Fp6.map_mul, Fp6.map_mulByV]

theorem map_cyclotomicSquare (f : Hom F G) (a : Fp12 F) :
    map f a.cyclotomicSquare = (map f a).cyclotomicSquare := by
  simp only [cyclotomicSquare, map, Fp6.map, Fp2.map_add, Fp2.map_sub, Fp2.map_mul,
    Fp2.map_mulByOnePlusI]

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

theorem map_cyclotomicPow (f : Hom F G) (a : Fp12 F) (e : Nat) :
    map f (cyclotomicPow a e) = cyclotomicPow (map f a) e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [cyclotomicPow.eq_1 a e, cyclotomicPow.eq_1 (map f a) e]
    split
    · exact map_one f
    · have h := ih (e / 2) (by omega) a.cyclotomicSquare
      rw [map_cyclotomicSquare] at h
      split <;> simp only [map_mul, h]

/-- The map of base fields, applied to the four kept coefficients. -/
private def Compressed.map (f : Hom F G) (g : Compressed F) : Compressed G :=
  ⟨g.a1.map f, g.a2.map f, g.a4.map f, g.a5.map f⟩

/-- The map of base fields, applied to the numerators and the denominator. -/
private def mapTriple (f : Hom F G) (n : Fp2 F × Fp2 F × Fp2 F) : Fp2 G × Fp2 G × Fp2 G :=
  (n.1.map f, n.2.1.map f, n.2.2.map f)

/-- The square of the shared `Fp2` definition commutes with the map. -/
private theorem map_fp2Square (f : Hom F G) (a : Fp2 F) :
    Fp2.map f (Cryptography.Fp2.square a) = Cryptography.Fp2.square (Fp2.map f a) :=
  Fp2.map_square f a

private theorem map_compress (f : Hom F G) (a : Fp12 F) :
    (compress a).map f = compress (map f a) := rfl

private theorem map_compressedSquare (f : Hom F G) (g : Compressed F) :
    g.square.map f = (g.map f).square := by
  simp only [Compressed.square, Compressed.map, Fp2.map_add, Fp2.map_sub, map_fp2Square,
    Fp2.map_mulByOnePlusI]

private theorem map_squares (f : Hom F G) (g : Compressed F) (e : Nat) :
    (g.squares e).map (Compressed.map f) = (g.map f).squares e := by
  induction e using Nat.strongRecOn generalizing g with
  | _ e ih =>
    rw [Compressed.squares.eq_1 g e, Compressed.squares.eq_1 (g.map f) e]
    split
    · rfl
    · split
      · rfl
      · have h := ih (e / 2) (by omega) g.square
        rw [map_compressedSquare] at h
        split <;> simp only [List.map_cons, h]

private theorem map_numerators (f : Hom F G) (g : Compressed F) :
    mapTriple f g.numerators = (g.map f).numerators := by
  simp only [Compressed.numerators, mapTriple, Compressed.map, Fp2.map_add, Fp2.map_sub,
    Fp2.map_mul, map_fp2Square, Fp2.map_mulByOnePlusI]

private theorem map_suffixProducts (f : Hom F G) (xs : List (Fp2 F)) :
    ((suffixProducts xs).1.map (Prod.map (Fp2.map f) (Fp2.map f)),
      (suffixProducts xs).2.map f) = suffixProducts (xs.map (Fp2.map f)) := by
  induction xs with
  | nil => simp only [suffixProducts, List.foldr_nil, List.map_nil, Fp2.map_one]
  | cons x xs ih =>
    simp only [suffixProducts, List.foldr_cons, List.map_cons] at ih ⊢
    rw [← ih]
    simp only [Prod.map, Fp2.map_mul]

private theorem map_batchInverse (f : Hom F G) (ps : List (Fp2 F × Fp2 F)) (inv : Fp2 F) :
    (batchInverse ps inv).map (Fp2.map f) =
      batchInverse (ps.map (Prod.map (Fp2.map f) (Fp2.map f))) (inv.map f) := by
  induction ps generalizing inv with
  | nil => rfl
  | cons p ps ih =>
    simp only [batchInverse, List.map_cons, Prod.map, ih, Fp2.map_mul]

private theorem map_foldl_mul (f : Hom F G) (xs : List (Fp12 F)) (a : Fp12 F) :
    map f (xs.foldl (· * ·) a) = (xs.map (map f)).foldl (· * ·) (map f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, map_mul]

private theorem map_decompress (f : Hom F G) (g : Compressed F) (n : Fp2 F × Fp2 F × Fp2 F)
    (d : Fp2 F) : map f (g.decompress n d) = (g.map f).decompress (mapTriple f n) (d.map f) := by
  simp only [Compressed.decompress, map, Fp6.map, Compressed.map, mapTriple, Fp2.map_mul]

private theorem map_zipWith_decompress (f : Hom F G) (sel : List (Compressed F))
    (nums : List (Fp2 F × Fp2 F × Fp2 F)) (invs : List (Fp2 F)) :
    (List.zipWith (fun x d => x.1.decompress x.2 d) (sel.zip nums) invs).map (map f) =
      List.zipWith (fun x d => x.1.decompress x.2 d)
        ((sel.map (Compressed.map f)).zip (nums.map (mapTriple f))) (invs.map (Fp2.map f)) := by
  induction sel generalizing nums invs with
  | nil => rfl
  | cons g sel ih =>
    cases nums with
    | nil => rfl
    | cons n nums =>
      cases invs with
      | nil => rfl
      | cons d invs =>
        simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons, map_decompress, ih]

/-- The power with compressed squares commutes with the map. -/
theorem map_compressedPow (f : Hom F G) (a : Fp12 F) (e : Nat) :
    map f (compressedPow a e) = compressedPow (map f a) e := by
  have hsel : (compress (map f a)).square.squares (e / 2) =
      ((compress a).square.squares (e / 2)).map (Compressed.map f) := by
    rw [map_squares, map_compressedSquare, map_compress]
  have hnum : ∀ sel : List (Compressed F),
      (sel.map (Compressed.map f)).map Compressed.numerators =
        (sel.map Compressed.numerators).map (mapTriple f) := fun sel => by
    simp only [List.map_map]
    exact List.map_congr_left fun g _ => (map_numerators f g).symm
  unfold compressedPow
  dsimp only
  rw [hsel, hnum]
  generalize (compress a).square.squares (e / 2) = sel
  generalize sel.map Compressed.numerators = nums
  have hden : (nums.map (mapTriple f)).map (fun n => n.2.2) =
      (nums.map fun n => n.2.2).map (Fp2.map f) := by
    simp only [List.map_map]
    rfl
  obtain ⟨hp, ht⟩ := Prod.ext_iff.mp (map_suffixProducts f (nums.map fun n => n.2.2))
  rw [hden, ← hp, ← ht, Fp2.map_isZero, ← Fp2.map_inverse, ← map_batchInverse,
    ← map_zipWith_decompress]
  generalize List.zipWith _ _ _ = powers
  split_ifs
  · exact map_cyclotomicPow f a e
  · exact map_foldl_mul f powers a
  · cases powers with
    | nil => exact map_one f
    | cons p rest => exact map_foldl_mul f rest p

end Fp12

end EthLib.Cryptography.Bls
