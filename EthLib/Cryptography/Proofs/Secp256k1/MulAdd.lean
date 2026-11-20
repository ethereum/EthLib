module

public import EthLib.Cryptography.Secp256k1.MulAdd
public import EthLib.Cryptography.Proofs.Secp256k1.Inverse
-- The proofs read the bodies of the joint chain and of the field operations.
import all EthLib.Cryptography.Secp256k1.MulAdd
import all EthLib.Cryptography.Secp256k1.Montgomery
public import EthLib.Cryptography.Proofs.Secp256k1.Order
import EthLib.Cryptography.Proofs.Secp256k1.Montgomery

/-!
# Proofs: the double scalar multiplication of secp256k1

The endomorphism scales the affine x coordinate by a cube root of unity.

Since the generator spans the group, the map's effect on the generator determines its action.

The signed digits preserve the four scalar products as they share the doubling chain.

So on a point of the curve, the joint chain computes `k P + l G`.

The shared chain gives the same point.

The double scalar multiplication then equals the shared chain on `Fp` for every input.
-/

@[expose] public section

open EthLib.Cryptography EthLib.Cryptography.Secp256k1 WeierstrassCurve

namespace EthLib.Cryptography.Secp256k1

namespace MulAdd

/-- The scalar by which the endomorphism acts on the generator.

It is `3^((n - 1) / 3) mod n`, the root that pairs with `beta`. -/
def lambda : Fn := 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

/-- The first coordinate of the first vector in the scalar lattice.

It is the first remainder below `sqrt(n)` in Euclid's algorithm on `n` and `lambda`. -/
def basisA : Int := 0x3086d221a7d46bcde86c90e49284eb15

/-- The coefficient of `lambda` for that remainder.

The first basis vector is `(basisA, -basisB)`. -/
def basisB : Int := 0xe4437ed6010e88286f547fa90abfe4c3

/-- Read the scalar represented by the two words. -/
def WordPair.toNat (pair : WordPair) : Nat := pair.lo.toNat + pair.hi.toNat * 2^64

/-- A canonical residue is zero exactly when all four words are zero. -/
theorem zeroElement_eq_true (x : Montgomery) : zeroElement x = true ↔ x = 0 := by
  obtain ⟨⟨a,b,c,d⟩, h⟩ := x
  rw [show (0 : Montgomery) = ⟨⟨0,0,0,0⟩, by decide⟩ from rfl]
  simp only [zeroElement, Bool.and_eq_true, beq_iff_eq, and_assoc,
    Montgomery.mk.injEq, Montgomery.Raw.mk.injEq]


/-! ## The endomorphism and its action on the group -/

private abbrev F := ZMod Fp.modulus

private noncomputable def β : F := Fp.toZMod beta

private theorem beta_cube : β ^ 3 = 1 := by decide +kernel

private theorem beta_ne : β ≠ 0 := by
  intro h
  have := beta_cube
  simp [h] at this

private theorem beta_sq_inv : β ^ 2 = β⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact beta_cube

private theorem beta_sq_sq : (β ^ 2) ^ 2 = β := by
  calc
    (β ^ 2) ^ 2 = β ^ 3 * β := by ring
    _ = β := by rw [beta_cube, one_mul]

private theorem scale_valid {x y : F} (h : curve.Nonsingular x y) :
    curve.Nonsingular (β*x) y := by
  apply nonsingular_of
  rw [show β * x * (β * x) * (β * x) = β ^ 3 * (x*x*x) by ring, beta_cube, one_mul]
  exact (equation_iff _ _).mp h.1

private noncomputable def scale : curve.Point → curve.Point
  | .zero => .zero
  | .some x y h => .some (β*x) y (scale_valid h)

private theorem slope_scaled (x1 x2 y1 y2 : F)
    (hn : ¬ (x1 = x2 ∧ y1 = -y2)) :
    curve.slope (β*x1) (β*x2) y1 y2 = β^2 * curve.slope x1 x2 y1 y2 := by
  by_cases hx : x1 = x2
  · subst x2
    have hy : y1 ≠ -y2 := fun h => hn ⟨rfl, h⟩
    rw [Affine.slope_of_Y_ne rfl (by simpa [Affine.negY, curve] using hy),
      Affine.slope_of_Y_ne rfl (by simpa [Affine.negY, curve] using hy)]
    simp only [Affine.negY, curve, mul_zero, zero_mul, add_zero, sub_zero, div_eq_mul_inv]
    ring
  · have hx' : β*x1 ≠ β*x2 := fun h => hx (mul_left_cancel₀ beta_ne h)
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx']
    rw [show β*x1-β*x2 = β*(x1-x2) by ring, beta_sq_inv]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

private theorem addX_scaled (x1 x2 t : F) :
    curve.addX (β*x1) (β*x2) (β^2*t) = β * curve.addX x1 x2 t := by
  simp only [Affine.addX, curve, zero_mul, add_zero, sub_zero, mul_pow, beta_sq_sq]
  ring

private theorem addY_scaled (x1 x2 y1 t : F) :
    curve.addY (β*x1) (β*x2) y1 (β^2*t) = curve.addY x1 x2 y1 t := by
  simp only [Affine.addY, Affine.negAddY, negY_eq, addX_scaled, ← mul_sub]
  have h : β ^ 2 * t * (β * (curve.addX x1 x2 t - x1)) =
      β^3 * (t * (curve.addX x1 x2 t - x1)) := by ring
  rw [h, beta_cube, one_mul]

private theorem scale_add (P Q : curve.Point) : scale (P+Q) = scale P + scale Q := by
  cases P with
  | zero => exact by simp [← Affine.Point.zero_def, scale]
  | some x1 y1 h1 =>
    cases Q with
    | zero => simp [← Affine.Point.zero_def, scale]
    | some x2 y2 h2 =>
      by_cases h : x1 = x2 ∧ y1 = -y2
      · rw [Affine.Point.add_of_Y_eq h.1 (by simpa [Affine.negY, curve] using h.2)]
        simp only [scale]
        rw [Affine.Point.add_of_Y_eq (by rw [h.1]) (by simpa [Affine.negY, curve] using h.2)]
        rfl
      · have h1x : ¬(x1 = x2 ∧ y1 = curve.negY x2 y2) := by simpa [Affine.negY, curve] using h
        have h2x : ¬(β*x1 = β*x2 ∧ y1 = curve.negY (β*x2) y2) :=
          fun ⟨a,b⟩ => h ⟨mul_left_cancel₀ beta_ne a, by simpa [Affine.negY, curve] using b⟩
        rw [Affine.Point.add_some h1x]
        simp only [scale]
        rw [Affine.Point.add_some h2x]
        congr 1
        · rw [slope_scaled _ _ _ _ h, addX_scaled]
        · rw [slope_scaled _ _ _ _ h, addY_scaled]

private noncomputable def scaleHom : curve.Point →+ curve.Point where
  toFun := scale
  map_zero' := rfl
  map_add' := scale_add

private theorem scale_generator :
    scaleHom (Point.toPoint .generator) = lambda.val • Point.toPoint .generator := by
  let x : Fp := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
  let y : Fp := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
  have hs : (Point.affine (beta * x) y).isOnCurve = true := by decide +kernel
  have he : Point.mul lambda .generator = Point.affine (beta * x) y := by
    rw [Point.mul, Point.mulBits_eq_jacobian]
    decide +kernel
  rw [← Point.toPoint_mul lambda Point.isOnCurve_generator, he, Point.toPoint_affine hs]
  change scale (Point.toPoint (.affine x y)) = _
  rw [Point.toPoint_affine Point.isOnCurve_generator]
  simp only [scale, β, map_mul, x, y]

private theorem scale_eq_nsmul (X : curve.Point) : scale X = lambda.val • X := by
  obtain ⟨p, hp, hpX⟩ := Point.toPoint_surjective X
  obtain ⟨k, hk⟩ := Point.exists_eq_mul_generator hp
  rw [← hpX, hk, Point.toPoint_mul k Point.isOnCurve_generator]
  change scaleHom (k.val • Point.toPoint .generator) = _
  rw [map_nsmul, scale_generator, smul_smul, smul_smul, Nat.mul_comm]

private theorem readOfFin (a : Fp) : Montgomery.toFin (Montgomery.ofFin a) = a :=
  Montgomery.toFin_ofFin a

private theorem toFin_embedding : Jacobian.Coords.Embedding Montgomery.toFin :=
  Point.toFin_embedding

private theorem map_map_eq {A B C : Type} (f : A → B) (g : B → C) (h : A → C)
    (hh : ∀ x, g (f x) = h x) (p : Jacobian.Coords A) :
    (p.map f).map g = p.map h := by
  simp only [Jacobian.Coords.map, hh]

private noncomputable def readCoords (p : Coordinates) : Jacobian Fp.modulus :=
  Jacobian.ofCoords (p.map Montgomery.toFin)

private theorem read_toMontgomeryCoords (p : Point) :
    readCoords (Point.toMontgomeryCoords p) = Point.toJacobian p := by
  exact congrArg (Jacobian.ofCoords : Jacobian.Coords Fp → _)
    (map_map_eq Montgomery.ofFin Montgomery.toFin id readOfFin
      (Point.toJacobian p).toCoords)

private theorem ofMontgomeryCoords_eq_read (p : Coordinates) :
    Point.ofMontgomeryCoords p = Point.ofJacobian (readCoords p) :=
  Point.ofMontgomeryCoords_eq p

/-- A Montgomery form is on the curve when its read-back form is on the curve. -/
private abbrev OnCurve (p : Coordinates) : Prop := Jacobian.OnCurve 0 7 (readCoords p)

/-- The secp256k1 group element represented by a Montgomery form. -/
private noncomputable def groupValue (p : Coordinates) : curve.Point :=
  Jacobian.toPoint 0 7 (readCoords p)

private theorem coordinateToZ_eq (x : Fp) : Jacobian.toZ x = Fp.toZMod x :=
  ZMod.natCast_zmod_val (Fp.toZMod x)

private theorem affX_of_scaleX {p q : Jacobian Fp.modulus} {s : Fp}
    (hx : q.x = s * p.x) (hz : q.z = p.z) :
    Jacobian.affX q = Fp.toZMod s * Jacobian.affX p := by
  unfold Jacobian.affX
  rw [hx, hz, Jacobian.toZ_mul, coordinateToZ_eq s, mul_div_assoc]

private theorem scaleX_z {F : Type} [Mul F] (factor : F) (p : Jacobian.Coords F) :
    (scaleX factor p).z = p.z := rfl

private theorem scaleX_y {F : Type} [Mul F] (factor : F) (p : Jacobian.Coords F) :
    (scaleX factor p).y = p.y := rfl

private theorem scaleX_x {F : Type} [Mul F] (factor : F) (p : Jacobian.Coords F) :
    (scaleX factor p).x = factor * p.x := rfl

private theorem scaleX_read_z (factor : Montgomery) (p : Coordinates) :
    (readCoords (scaleX factor p)).z = (readCoords p).z :=
  congrArg Montgomery.toFin (scaleX_z factor p)

private theorem endomorphism_read_z (p : Coordinates) :
    (readCoords (endomorphism p)).z = (readCoords p).z :=
  scaleX_read_z (Montgomery.ofFin beta) p

private theorem scaleX_affY (factor : Montgomery) (p : Coordinates) :
    Jacobian.affY (readCoords (scaleX factor p)) = Jacobian.affY (readCoords p) := by
  have hy : (readCoords (scaleX factor p)).y = (readCoords p).y :=
    congrArg Montgomery.toFin (scaleX_y factor p)
  unfold Jacobian.affY
  rw [hy, scaleX_read_z]

private theorem endomorphism_affY (p : Coordinates) :
    Jacobian.affY (readCoords (endomorphism p)) = Jacobian.affY (readCoords p) :=
  scaleX_affY (Montgomery.ofFin beta) p

private theorem scaleX_affX (factor : Montgomery) (p : Coordinates) :
    Jacobian.affX (readCoords (scaleX factor p)) =
      Fp.toZMod (Montgomery.toFin factor) * Jacobian.affX (readCoords p) :=
  affX_of_scaleX (p := readCoords p) (q := readCoords (scaleX factor p))
    ((congrArg Montgomery.toFin (scaleX_x factor p)).trans
      (toFin_embedding.map_mul factor p.x)) (scaleX_read_z factor p)

private theorem endomorphism_affX (p : Coordinates) :
    Jacobian.affX (readCoords (endomorphism p)) = β * Jacobian.affX (readCoords p) :=
  (scaleX_affX (Montgomery.ofFin beta) p).trans
    (congrArg (fun x : Fp => Fp.toZMod x * Jacobian.affX (readCoords p))
      (readOfFin beta))

/-- The endomorphism in Montgomery coordinates preserves the curve and acts as `lambda`. -/
private theorem endomorphism_spec {p : Coordinates} (hp : OnCurve p) :
    OnCurve (endomorphism p) ∧ groupValue (endomorphism p) = lambda.val • groupValue p := by
  by_cases hz : (readCoords p).z = 0
  · have hzend : (readCoords (endomorphism p)).z = 0 := (endomorphism_read_z p).trans hz
    refine ⟨fun hz' => False.elim (hz' hzend), ?_⟩
    have hzero : groupValue p = 0 := Jacobian.toPoint_of_z_eq_zero hz
    calc
      groupValue (endomorphism p) = 0 := Jacobian.toPoint_of_z_eq_zero hzend
      _ = lambda.val • groupValue p := by rw [hzero, nsmul_zero]
  · have hzend : (readCoords (endomorphism p)).z ≠ 0 :=
      fun h => hz ((endomorphism_read_z p).symm.trans h)
    have hvalid : curve.Nonsingular (Jacobian.affX (readCoords p)) (Jacobian.affY (readCoords p)) :=
      Jacobian.nonsingular (hp hz)
    have h := Jacobian.spec_of_eq (r := readCoords (endomorphism p))
      (scale_valid hvalid) hzend (endomorphism_affX p) (endomorphism_affY p)
    refine ⟨h.1, ?_⟩
    have hpval : groupValue p = .some _ _ hvalid :=
      Jacobian.toPoint_of_z_ne_zero hp hz
    calc
      groupValue (endomorphism p) = .some _ _ (scale_valid hvalid) := h.2
      _ = scale (groupValue p) := by rw [hpval]; rfl
      _ = lambda.val • groupValue p := scale_eq_nsmul _

private theorem negate_x {F : Type} [OfNat F 0] [Sub F] (p : Jacobian.Coords F) :
    (negate p).x = p.x := rfl

private theorem negate_y {F : Type} [OfNat F 0] [Sub F] (p : Jacobian.Coords F) :
    (negate p).y = 0 - p.y := rfl

private theorem negate_z {F : Type} [OfNat F 0] [Sub F] (p : Jacobian.Coords F) :
    (negate p).z = p.z := rfl

private theorem negate_read_z (p : Coordinates) :
    (readCoords (negate p)).z = (readCoords p).z :=
  congrArg Montgomery.toFin (negate_z p)

private theorem negate_affX (p : Coordinates) :
    Jacobian.affX (readCoords (negate p)) = Jacobian.affX (readCoords p) := by
  have hX : (readCoords (negate p)).x = (readCoords p).x :=
    congrArg Montgomery.toFin (negate_x p)
  unfold Jacobian.affX
  rw [hX, negate_read_z]

private theorem negate_affY (p : Coordinates) :
    Jacobian.affY (readCoords (negate p)) = -Jacobian.affY (readCoords p) := by
  have hm := congrArg Montgomery.toFin (negate_y p)
  have hY : (readCoords (negate p)).y = 0 - (readCoords p).y :=
    hm.trans ((toFin_embedding.map_sub 0 p.y).trans
      (congrArg (fun y : Fp => y - (readCoords p).y) toFin_embedding.map_zero))
  unfold Jacobian.affY
  rw [hY, negate_read_z, Jacobian.toZ_sub, Jacobian.toZ_zero, zero_sub, neg_div]

/-- Negating Montgomery coordinates preserves the curve and negates the group element. -/
private theorem negate_spec {p : Coordinates} (hp : OnCurve p) :
    OnCurve (negate p) ∧ groupValue (negate p) = -groupValue p := by
  by_cases hz : (readCoords p).z = 0
  · have hzn : (readCoords (negate p)).z = 0 := (negate_read_z p).trans hz
    have hzero : groupValue p = 0 := Jacobian.toPoint_of_z_eq_zero hz
    refine ⟨fun hz' => False.elim (hz' hzn), ?_⟩
    rw [hzero, neg_zero]
    exact Jacobian.toPoint_of_z_eq_zero hzn
  · have hzn : (readCoords (negate p)).z ≠ 0 :=
      fun h => hz ((negate_read_z p).symm.trans h)
    have hp' :
        curve.Nonsingular (Jacobian.affX (readCoords p)) (-Jacobian.affY (readCoords p)) := by
      apply nonsingular_of
      simpa using hp hz
    have hvalid : curve.Nonsingular (Jacobian.affX (readCoords p)) (Jacobian.affY (readCoords p)) :=
      Jacobian.nonsingular (hp hz)
    have h := Jacobian.spec_of_eq hp' hzn (negate_affX p) (negate_affY p)
    refine ⟨h.1, ?_⟩
    have hpval : groupValue p = .some _ _ hvalid :=
      Jacobian.toPoint_of_z_ne_zero hp hz
    calc
      groupValue (negate p) = .some _ _ hp' := h.2
      _ = -(.some _ _ hvalid : curve.Point) := by
        rw [Affine.Point.neg_some hvalid, Affine.Point.some.injEq]
        exact ⟨rfl, (negY_eq _ _).symm⟩
      _ = -groupValue p := congrArg Neg.neg hpval.symm

/-! ## Arithmetic on the Montgomery coordinates -/

open Jacobian

private theorem two_ne_zero : (2 : ZMod Fp.modulus) ≠ 0 := by decide

private theorem point_spec {p : Point} (hp : p.isOnCurve = true) :
    OnCurve (Point.toMontgomeryCoords p) ∧
      groupValue (Point.toMontgomeryCoords p) = Point.toPoint p := by
  change Jacobian.OnCurve 0 7 (readCoords (Point.toMontgomeryCoords p)) ∧
    Jacobian.toPoint 0 7 (readCoords (Point.toMontgomeryCoords p)) = _
  rw [read_toMontgomeryCoords]
  exact Point.toJacobian_spec hp

private theorem infinity_spec :
    OnCurve (Coords.infinity : Coordinates) ∧ groupValue (Coords.infinity : Coordinates) = 0 := by
  change Jacobian.OnCurve 0 7 (readCoords Coords.infinity) ∧
    Jacobian.toPoint 0 7 (readCoords Coords.infinity) = 0
  erw [readCoords, Coords.map_infinity toFin_embedding]
  exact ⟨Jacobian.onCurve_infinity, Jacobian.toPoint_of_z_eq_zero rfl⟩

private theorem read_double (p : Coordinates) :
    readCoords (Coords.double 0 p) = Jacobian.double 0 (readCoords p) := by
  have h := Coords.map_double toFin_embedding (0 : Montgomery) p
  rw [toFin_embedding.map_zero] at h
  exact congrArg (Jacobian.ofCoords : Coords Fp → _) h

private theorem read_add (p q : Coordinates) :
    readCoords (Coords.add 0 p q) = Jacobian.add 0 (readCoords p) (readCoords q) := by
  have h := Coords.map_add toFin_embedding (0 : Montgomery) p q
  rw [toFin_embedding.map_zero] at h
  exact congrArg (Jacobian.ofCoords : Coords Fp → _) h

private theorem double_spec {p : Coordinates} (hp : OnCurve p) :
    OnCurve (Coords.double 0 p) ∧ groupValue (Coords.double 0 p) = groupValue p + groupValue p := by
  unfold OnCurve groupValue
  rw [read_double]
  exact Jacobian.double_spec (Jacobian.toZ_zero (m := Fp.modulus)) two_ne_zero hp

private theorem double_coordinates (p : Coordinates) :
    let u := readCoords (Coords.double 0 p)
    let v := readCoords (double p)
    Jacobian.toZ u.x = 4 * Jacobian.toZ v.x ∧
      Jacobian.toZ u.y = 8 * Jacobian.toZ v.y ∧
      Jacobian.toZ u.z = 2 * Jacobian.toZ v.z := by
  let r := Jacobian.toZ ∘ Montgomery.toFin
  have hh := congrArg r (Montgomery.halve_add_self (p.x * p.x))
  simp only [r, Function.comp_apply, toFin_embedding.map_add, toFin_embedding.map_mul,
    Jacobian.toZ_add, Jacobian.toZ_mul] at hh
  simp only [readCoords, double, doubleCore, Montgomery.productSubSquare_eq,
    Montgomery.square_eq_mul, Coords.double, ite_true,
    Coords.map, Jacobian.ofCoords, toFin_embedding.map_add,
    toFin_embedding.map_mul, toFin_embedding.map_sub, Jacobian.toZ_add, Jacobian.toZ_mul,
    Jacobian.toZ_sub]
  refine ⟨?_, ?_, by ring⟩ <;> rw [← hh] <;> ring

private theorem fastDouble_spec {p : Coordinates} (hp : OnCurve p) :
    OnCurve (double p) ∧
      groupValue (double p) = groupValue p + groupValue p := by
  let u := readCoords (Coords.double 0 p)
  let v := readCoords (double p)
  obtain ⟨hx, hy, hz⟩ := double_coordinates p
  change Jacobian.toZ u.x = 4 * Jacobian.toZ v.x at hx
  change Jacobian.toZ u.y = 8 * Jacobian.toZ v.y at hy
  change Jacobian.toZ u.z = 2 * Jacobian.toZ v.z at hz
  have hu : Jacobian.OnCurve 0 7 u := (double_spec hp).1
  have hg : Jacobian.toPoint 0 7 u = groupValue p + groupValue p := (double_spec hp).2
  change Jacobian.OnCurve 0 7 v ∧ Jacobian.toPoint 0 7 v = _
  rw [← hg]
  have hzero : u.z = 0 ↔ v.z = 0 := by
    rw [← Jacobian.toZ_eq_zero, hz, mul_eq_zero, or_iff_right two_ne_zero, Jacobian.toZ_eq_zero]
  have hax : Jacobian.affX u = Jacobian.affX v := by
    simp only [Jacobian.affX, hx, hz, mul_pow, show (4 : F) = 2^2 by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)
  have hay : Jacobian.affY u = Jacobian.affY v := by
    simp only [Jacobian.affY, hy, hz, mul_pow, show (8 : F) = 2^3 by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)
  have hv : Jacobian.OnCurve 0 7 v := by
    intro hvz
    have hc := hu (mt hzero.mp hvz)
    rwa [hax, hay] at hc
  refine ⟨hv, ?_⟩
  by_cases hvz : v.z = 0
  · rw [Jacobian.toPoint_of_z_eq_zero hvz, Jacobian.toPoint_of_z_eq_zero (hzero.mpr hvz)]
  · rw [Jacobian.toPoint_of_z_ne_zero hv hvz, Jacobian.toPoint_of_z_ne_zero hu (mt hzero.mp hvz)]
    simp only [hax, hay]

private theorem add_spec {p q : Coordinates} (hp : OnCurve p) (hq : OnCurve q) :
    OnCurve (Coords.add 0 p q) ∧ groupValue (Coords.add 0 p q) = groupValue p + groupValue q := by
  unfold OnCurve groupValue
  rw [read_add]
  exact Jacobian.add_spec (Jacobian.toZ_zero (m := Fp.modulus)) two_ne_zero hp hq

private abbrev Represents (p : Coordinates) (P : curve.Point) : Prop :=
  OnCurve p ∧ groupValue p = P

private theorem Represents.double {p : Coordinates} {P : curve.Point}
    (hp : Represents p P) : Represents (Coords.double 0 p) (P + P) :=
  ⟨(double_spec hp.1).1, by rw [(double_spec hp.1).2, hp.2]⟩

private theorem Represents.add {p q : Coordinates} {P Q : curve.Point}
    (hp : Represents p P) (hq : Represents q Q) :
    Represents (Coords.add 0 p q) (P + Q) :=
  ⟨(add_spec hp.1 hq.1).1, by rw [(add_spec hp.1 hq.1).2, hp.2, hq.2]⟩

private noncomputable def TableSpec {n : Nat} (t : Vector Coordinates n) (P : curve.Point) : Prop :=
  ∀ i : Fin n, Represents t[i.val] ((2 * i.val + 1) • P)

private theorem prepared_mul (a b : Montgomery) :
    a * ((b * b) * b) = (a * b) * (b * b) := by
  apply toFin_embedding.injective
  apply Jacobian.toZ_injective
  simp only [toFin_embedding.map_mul, Jacobian.toZ_mul]
  ring

/-! ## Signed digits and the doubling chain -/

/-! ## Models of the recoding

The proofs read the packed recoding through these unpacked forms.
-/

/-- The index of an odd multiple and whether to subtract it. -/
private abbrev Digit (n : Nat) := Fin n × Bool

/-- Shift both words right by one bit. -/
private noncomputable def WordPair.half (w : WordPair) : WordPair :=
  ⟨(w.lo >>> 1) + (w.hi <<< 63), w.hi >>> 1⟩

/-- Round down to a multiple of the pivot. -/
private noncomputable def WordPair.roundDown (w : WordPair) (pivot : UInt64) : WordPair :=
  ⟨w.lo - w.lo % pivot, w.hi⟩

/-- Add a word with carry. -/
private noncomputable def WordPair.addWord (w : WordPair) (increment : UInt64) : WordPair :=
  let lo := w.lo + increment
  ⟨lo, w.hi + (if lo < increment then 1 else 0)⟩

/-- Read one signed digit from the two-word scalar. -/
private noncomputable def recodeWords (window : Window) (w : WordPair) :
    WordPair × Option (Digit window.entries) :=
  let low := (w.lo &&& window.mask).toNat
  let half := w.half
  if he : low % 2 = 0 then (half, none)
  else
    have hlow : low < 4 * window.entries := by
      change (w.lo &&& window.mask).toNat < 4 * window.entries
      rw [UInt64.toNat_and]
      cases window with
      | width5 =>
        change w.lo.toNat &&& (2^5 - 1) < 2^5
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      | width14 =>
        change w.lo.toNat &&& (2^14 - 1) < 2^14
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
    let down := half.roundDown window.pivot
    if hr : low < 2 * window.entries then (down, some (⟨low / 2, by omega⟩, false))
    else
      (down.addWord window.pivot, some (⟨(4 * window.entries - low) / 2, by omega⟩, true))

/-- Add or subtract the selected odd multiple. -/
private noncomputable def addDigit {n : Nat} (p : Coordinates) (table : Vector Coordinates n) :
    Option (Digit n) → Coordinates
  | none => p
  | some (i, negative) =>
    let q := table[i.val]
    Coords.add 0 p (if negative then negate q else q)

/-- Add a generator table entry using mixed addition when its Z coordinate is one. -/
private noncomputable def addGenerator (p : Coordinates) (q : @& Coordinates) (negative : Bool) :
    Coordinates :=
  let y := if negative then (0 : Montgomery) - q.y else q.y
  if q.z = 1 then
    if p.z = 0 then ⟨q.x, y, q.z⟩ else
      let zz := Montgomery.square p.z
      let h := q.x * zz - p.x
      let r := y * (p.z * zz) - p.y
      if h = 0 then
        if r = 0 then Coords.double 0 p else Coords.infinity
      else
        let hh := Montgomery.square h
        let hhh := h * hh
        let v := p.x * hh
        let x := Montgomery.square r - hhh - (v + v)
        ⟨x, r * (v - x) - p.y * hhh, p.z * h⟩
  else Coords.add 0 p ⟨q.x, y, q.z⟩

/-- Add the selected generator multiple with the digit's sign. -/
private noncomputable def addPacked (p : Coordinates) (window : Window)
    (table : Vector Coordinates window.entries) (digit : UInt64) : Coordinates :=
  if digit == 0 then p else
    let i := packedIndex window digit
    let q := table[i.val]
    addGenerator p q (digit >= window.pivot)


/-- Add a point when the square and cube of the second denominator are available. -/
private noncomputable def addCached (p q : Coordinates) (qz2 qz3 : Montgomery) :
    Coordinates :=
  if p.z = 0 then q
  else if q.z = 0 then p
  else
    let zz := Montgomery.square p.z
    let (u1, s1, z) := if q.z = 1 then (p.x, p.y, p.z) else
      (p.x * qz2, p.y * qz3, p.z * q.z)
    let h := q.x * zz - u1
    let r := q.y * p.z * zz - s1
    if h = 0 then
      if r = 0 then Coords.double 0 p else Coords.infinity
    else
      let hh := Montgomery.square h
      let hhh := h * hh
      let v := u1 * hh
      let x := Montgomery.square r - hhh - (v + v)
      ⟨x, r * (v - x) - s1 * hhh, z * h⟩

/-- Apply a fixed step to build eight consecutive odd multiples. -/
private noncomputable def oddMultiplesBy (p : Coordinates) (next : Coordinates → Coordinates) :
    Vector Coordinates 8 :=
  let p3 := next p
  let p5 := next p3
  let p7 := next p5
  let p9 := next p7
  let p11 := next p9
  let p13 := next p11
  let p15 := next p13
  #v[p, p3, p5, p7, p9, p11, p13, p15]

/-- The odd multiples from `P` to `15 P`, indexed by `(multiple - 1) / 2`. -/
private noncomputable def oddMultiples (p : Coordinates) : Vector Coordinates 8 :=
  let d := Coords.double 0 p
  let z2 := Montgomery.square d.z
  let z3 := z2 * d.z
  oddMultiplesBy p fun q => addCached q d z2 z3

/-- One scalar and its odd-multiple table. -/
private structure Stream (n : Nat) where
  /-- The scalar bits still to read. -/
  scalar : WordPair
  /-- The odd multiples of the point for this scalar. -/
  table : Vector Coordinates n

/-- Run the doubling chain with the given recoder for the fixed generator. -/
private noncomputable def chainWordsFor (window : Window)
    (pt qt : Vector Coordinates 8) (rt st : Vector Coordinates window.entries) :
    Nat → WordPair → WordPair → WordPair → WordPair → Coordinates
  | 0, _, _, _, _ => Coords.infinity
  | fuel + 1, p, q, r, s =>
    let (a, da) := recodeWords .width5 p
    let (b, db) := recodeWords .width5 q
    let (c, dc) := recodeWords window r
    let (d, dd) := recodeWords window s
    let rest := chainWordsFor window pt qt rt st fuel a b c d
    let acc := double rest
    addDigit (addDigit (addDigit (addDigit acc pt da) qt db) rt dc) st dd

/-- Run the chain with the selected window for the generator. -/
private noncomputable def chainFor (window : Window) (fuel : Nat) (p q : Stream 8)
    (r s : Stream window.entries) : Coordinates :=
  chainWordsFor window p.table q.table r.table s.table
    fuel p.scalar q.scalar r.scalar s.scalar

/-- Negate the entries when a scalar from the lattice split is negative. -/
private noncomputable def signedTable (scalar : Int) (table : Vector Coordinates 8) :
    Vector Coordinates 8 :=
  if scalar < 0 then table.map negate else table

/-- One odd multiple and the data shared by its two scalar streams. -/
private structure Prepared where
  /-- The original X coordinate. -/
  x : Montgomery
  /-- The X coordinate after applying the endomorphism. -/
  phiX : Montgomery
  /-- The Y coordinate of both points. -/
  y : Montgomery
  /-- The projective denominator of both points. -/
  z : Montgomery
  /-- The square of the projective denominator. -/
  z2 : Montgomery
  /-- The cube of the projective denominator. -/
  z3 : Montgomery

/-- Compute the shared denominator powers once for each odd multiple. -/
private noncomputable def prepare (p : Coordinates) : Prepared :=
  let z2 := p.z * p.z
  ⟨p.x, (endomorphism p).x, p.y, p.z, z2, z2 * p.z⟩

/-- Add a signed odd multiple using its cached denominator powers.

The field products use the same scaled coordinates as `Coords.add 0`.
-/
private noncomputable def addPrepared (p : Coordinates) (q : @& Prepared) (phi negative : Bool) :
    Coordinates :=
  let qx := if phi then q.phiX else q.x
  let qy := if negative then (0 : Montgomery) - q.y else q.y
  if p.z = 0 then ⟨qx, qy, q.z⟩
  else if q.z = 0 then p
  else
    let z1z1 := p.z * p.z
    let (u1, s1, z1z2) := if q.z = 1 then (p.x, p.y, p.z) else
      (p.x * q.z2, p.y * q.z3, p.z * q.z)
    let u2 := qx * z1z1
    let s2 := qy * p.z * z1z1
    let h := u2 - u1
    let r := s2 - s1
    if h = 0 then
      if r = 0 then Coords.double 0 p else Coords.infinity
    else
      let hh := h * h
      let hhh := h * hh
      let v := u1 * hh
      let x3 := r * r - hhh - (v + v)
      ⟨x3, r * (v - x3) - s1 * hhh, z1z2 * h⟩

/-- Combine the scalar sign and digit sign before selecting the odd multiple. -/
private noncomputable def addPreparedDigit (p : Coordinates) (table : Vector Prepared 8)
    (phi negative : Bool) : Option (Digit 8) → Coordinates
  | none => p
  | some (i, neg) => addPrepared p table[i.val] phi (negative != neg)

/-- Read both variable digits from one table during the shared doubling chain. -/
private noncomputable def preparedChain (window : Window) (table : Vector Prepared 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries) :
    Nat → WordPair → WordPair → WordPair → WordPair → Coordinates
  | 0, _, _, _, _ => Coords.infinity
  | fuel + 1, p, q, r, s =>
    let (a, da) := recodeWords .width5 p
    let (b, db) := recodeWords .width5 q
    let (c, dc) := recodeWords window r
    let (d, dd) := recodeWords window s
    let rest := preparedChain window table pn qn rt st fuel a b c d
    let acc := double rest
    let acc := addPreparedDigit acc table false pn da
    let acc := addPreparedDigit acc table true qn db
    addDigit (addDigit acc rt dc) st dd

/-- Add the selected variable point after combining the scalar and digit signs. -/
private noncomputable def addPackedPrepared (p : Coordinates) (table : Vector Prepared 8)
    (phi negative : Bool) (digit : UInt64) : Coordinates :=
  if digit == 0 then p else
    let i := packedIndex .width5 digit
    addPrepared p table[i.val] phi (negative != (digit >= Window.pivot .width5))

/-- Combine adjacent doublings when the intervening digits are zero. -/
private noncomputable def packedChain (window : Window) (table : Vector Prepared 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → UInt64 → UInt64 → Coordinates
  | 0, _, _, _, _, _, _, _, _ => Coords.infinity
  | fuel + 1, xa0, xa1, xb0, xb1, xc0, xc1, xd0, xd1 =>
    let ⟨al,ah,da⟩ := recodeRaw .width5 xa0 xa1
    let ⟨bl,bh,db⟩ := recodeRaw .width5 xb0 xb1
    let ⟨cl,ch,dc⟩ := recodeRaw window xc0 xc1
    let ⟨dl,dh,dd⟩ := recodeRaw window xd0 xd1
    let acc :=
      match fuel with
      | 0 => double Coords.infinity
      | next + 1 =>
        if ((al ||| bl ||| cl ||| dl) &&& 1) == 0 then
          let al' := (al >>> 1) + (ah <<< 63)
          let bl' := (bl >>> 1) + (bh <<< 63)
          let cl' := (cl >>> 1) + (ch <<< 63)
          let dl' := (dl >>> 1) + (dh <<< 63)
          doubleTwice (packedChain window table pn qn rt st next
            al' (ah >>> 1) bl' (bh >>> 1) cl' (ch >>> 1) dl' (dh >>> 1))
        else
          double (packedChain window table pn qn rt st (next + 1) al ah bl bh cl ch dl dh)
    let acc := addPackedPrepared acc table false pn da
    let acc := addPackedPrepared acc table true qn db
    addPacked (addPacked acc window rt dc) window st dd

/-- Split each scalar into the two words used by `packedChain`. -/
private noncomputable def preparedChainPacked (window : Window) (table : Vector Prepared 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries) (fuel : Nat)
    (p q r s : WordPair) : Coordinates :=
  packedChain window table pn qn rt st fuel p.lo p.hi q.lo q.hi r.lo r.hi s.lo s.hi


/-- The signed value of an odd-multiple index, or zero when no multiple is selected. -/
private noncomputable def digitValue {n : Nat} : Option (Digit n) → Int
  | none => 0
  | some (i, negative) =>
    let magnitude := 2 * (i.val : Int) + 1
    if negative then -magnitude else magnitude

/-- The signed digit with natural-number quotient and remainder. -/
private noncomputable def recode (window : Window) (k : Nat) : Nat × Option (Digit window.entries) :=
  if he : k % 2 = 0 then (k / 2, none)
  else
    let r := k % (4 * window.entries)
    have hpar : r % 2 = k % 2 := Nat.mod_mod_of_dvd k (by cases window <;> decide)
    if hr : r < 2 * window.entries then ((k - r) / 2, some (⟨r / 2, by omega⟩, false))
    else ((k + (4 * window.entries - r)) / 2,
      some (⟨(4 * window.entries - r) / 2, by
        have hstrict : 2 * window.entries < r := by
          by_contra! h
          have hr' : r = 2 * window.entries := by omega
          rw [hr'] at hpar
          omega
        have hsize : 0 < window.entries := by cases window <;> decide
        omega⟩, true))

private theorem WordPair.toNat_ofNat (k : Nat) (hk : k < 2^128) : (WordPair.ofNat k).toNat = k := by
  unfold WordPair.ofNat WordPair.toNat
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have h : k / 2^64 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt h]
  omega

private theorem word_shift_right (x : UInt64) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem word_shift_left63 (x : UInt64) :
    (x <<< 63).toNat = x.toNat % 2 * 2^63 := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
  change x.toNat * 2^63 % 2^64 = x.toNat % 2 * 2^63
  omega

private theorem word_half_lo (w : WordPair) :
    ((w.lo >>> 1) + (w.hi <<< 63)).toNat = w.lo.toNat / 2 + w.hi.toNat % 2 * 2^63 := by
  rw [UInt64.toNat_add, word_shift_right, word_shift_left63]
  have h := UInt64.toNat_lt_size w.lo
  change w.lo.toNat < 2^64 at h
  apply Nat.mod_eq_of_lt
  omega

private theorem window_pivot (window : Window) :
    window.pivot.toNat = 2 * window.entries := by
  cases window <;> decide

private theorem word_round_down (lo pivot : UInt64) :
    (lo - lo % pivot).toNat = lo.toNat - lo.toNat % pivot.toNat := by
  rw [UInt64.toNat_sub_of_le, UInt64.toNat_mod]
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
  exact Nat.mod_le _ _

private theorem mul_mod_radix (a b k : Nat) (hd : k ∣ 2^64) :
    (a + b * 2^64) % k = a % k := by
  obtain ⟨t, ht⟩ := hd
  rw [ht, Nat.mul_left_comm b, Nat.add_mul_mod_self_left]

private theorem word_low (window : Window) (w : WordPair) :
    (w.lo &&& window.mask).toNat = w.toNat % (4 * window.entries) := by
  have h := UInt64.toNat_and w.lo window.mask
  cases window with
  | width5 =>
    calc
      _ = w.lo.toNat &&& (2^5 - 1) := h
      _ = w.lo.toNat % 32 := Nat.and_two_pow_sub_one_eq_mod _ 5
      _ = _ := (mul_mod_radix w.lo.toNat w.hi.toNat 32 (by decide)).symm
  | width14 =>
    calc
      _ = w.lo.toNat &&& (2^14 - 1) := h
      _ = w.lo.toNat % 16384 := Nat.and_two_pow_sub_one_eq_mod _ 14
      _ = _ := (mul_mod_radix w.lo.toNat w.hi.toNat 16384 (by decide)).symm

private theorem WordPair.half_toNat (w : WordPair) : w.half.toNat = w.toNat / 2 := by
  change ((w.lo >>> 1) + (w.hi <<< 63)).toNat + (w.hi >>> 1).toNat * 2^64 =
    (w.lo.toNat + w.hi.toNat * 2^64) / 2
  rw [word_half_lo w, word_shift_right w.hi]
  omega

private theorem WordPair.half_hi_bound (w : WordPair) : w.half.hi.toNat + 1 < 2^64 := by
  change (w.hi >>> 1).toNat + 1 < 2^64
  rw [word_shift_right]
  have h : w.hi.toNat < 2^64 := UInt64.toNat_lt_size w.hi
  omega

private theorem WordPair.roundDown_toNat (window : Window) (w : WordPair) :
    (w.roundDown window.pivot).toNat = w.toNat - w.toNat % (2 * window.entries) := by
  change (w.lo - w.lo % window.pivot).toNat + w.hi.toNat * 2^64 =
    w.lo.toNat + w.hi.toNat * 2^64 - (w.lo.toNat + w.hi.toNat * 2^64) % (2 * window.entries)
  rw [word_round_down, window_pivot, mul_mod_radix _ _ _ (by cases window <;> decide)]
  have := Nat.mod_le w.lo.toNat (2 * window.entries)
  omega

private theorem WordPair.addWord_toNat (w : WordPair) (a : UInt64)
    (hhi : w.hi.toNat + 1 < 2^64) :
    (w.addWord a).toNat = w.toNat + a.toNat := by
  let lo : UInt64 := w.lo + a
  have hlo : lo.toNat = (w.lo.toNat + a.toNat) % 2^64 := UInt64.toNat_add w.lo a
  have hw : w.lo.toNat < 2^64 := UInt64.toNat_lt_size w.lo
  have ha : a.toNat < 2^64 := UInt64.toNat_lt_size a
  change lo.toNat + (w.hi + (if lo < a then 1 else 0)).toNat * 2^64 =
    w.lo.toNat + w.hi.toNat * 2^64 + a.toNat
  split
  · rename_i h
    have hlt := UInt64.lt_iff_toNat_lt.mp h
    rw [UInt64.toNat_add]
    change lo.toNat + (w.hi.toNat + 1) % 2^64 * 2^64 = _
    rw [Nat.mod_eq_of_lt hhi]
    omega
  · rename_i h
    have hle : a.toNat ≤ lo.toNat := Nat.le_of_not_gt fun hlt => h (UInt64.lt_iff_toNat_lt.mpr hlt)
    rw [UInt64.add_zero]
    omega

/-- Reading the next scalar and digit gives the same step as natural-number recoding. -/
private theorem recodeWords_eq (window : Window) (w : WordPair) :
    Prod.map WordPair.toNat id (recodeWords window w) = recode window w.toNat := by
  unfold recodeWords recode
  have hdiv : 2 ∣ 4 * window.entries := by cases window <;> decide
  simp only [word_low, Nat.mod_mod_of_dvd w.toNat hdiv]
  split
  · simp only [Prod.map, id, WordPair.half_toNat]
  · split
    · simp only [Prod.map, id, WordPair.roundDown_toNat, WordPair.half_toNat]
      congr 1
      cases window <;> simp only [Window.entries] at * <;> omega
    · have hb : (w.half.roundDown window.pivot).hi.toNat + 1 < 2^64 := w.half_hi_bound
      simp only [Prod.map, id, WordPair.addWord_toNat _ _ hb, WordPair.roundDown_toNat,
        WordPair.half_toNat, window_pivot]
      congr 1
      cases window <;> simp only [Window.entries] at * <;> omega

private theorem recodeWords_scalar (window : Window) (w : WordPair) :
    (recodeWords window w).1.toNat = (recode window w.toNat).1 :=
  congrArg Prod.fst (recodeWords_eq window w)

private theorem recodeWords_digit (window : Window) (w : WordPair) :
    (recodeWords window w).2 = (recode window w.toNat).2 :=
  congrArg Prod.snd (recodeWords_eq window w)

/-- One recoding step removes a signed digit and divides the rest by two. -/
private theorem recode_eq (window : Window) (k : Nat) :
    (k : Int) = 2 * (recode window k).1 + digitValue (recode window k).2 := by
  have hmod : (k % (4 * window.entries)) % 2 = k % 2 :=
    Nat.mod_mod_of_dvd k (by cases window <;> decide)
  cases window <;> simp only [Window.entries] at hmod
  all_goals
    unfold recode
    split
    · simp only [digitValue]
      omega
    · dsimp only
      split <;> simp only [digitValue, Bool.false_eq_true, ↓reduceIte, Window.entries] <;> omega

/-- Recoding reduces a bound by a power of two by one bit. -/
private theorem recode_next_le (window : Window) (k m : Nat) (hk : k ≤ 2 ^ (m + 1)) :
    (recode window k).1 ≤ 2 ^ m := by
  rw [Nat.pow_succ] at hk
  unfold recode
  split
  · dsimp only
    omega
  · rename_i he
    dsimp only
    split
    · dsimp only
      omega
    · rename_i hr
      cases window
      · simp only [Window.entries] at hr ⊢
        by_cases hm : 4 ≤ m
        · have hpow : 2 ^ m = 16 * 2 ^ (m - 4) := calc
            _ = 2 ^ (4 + (m - 4)) := congrArg (2 ^ ·) (by omega)
            _ = _ := Nat.pow_add 2 4 (m - 4)
          rw [hpow] at hk ⊢
          omega
        · have hsmall : 2 ^ m ≤ 8 := Nat.pow_le_pow_right (by decide) (show m ≤ 3 by omega)
          omega
      · simp only [Window.entries] at hr ⊢
        by_cases hm : 13 ≤ m
        · have hpow : 2 ^ m = 8192 * 2 ^ (m - 13) := calc
            _ = 2 ^ (13 + (m - 13)) := congrArg (2 ^ ·) (by omega)
            _ = _ := Nat.pow_add 2 13 (m - 13)
          rw [hpow] at hk ⊢
          omega
        · have hsmall : 2 ^ m ≤ 4096 := Nat.pow_le_pow_right (by decide) (show m ≤ 12 by omega)
          omega

/-- A scalar at most one has no bits left after its first digit. -/
private theorem recode_next_eq_zero (window : Window) (k : Nat) (hk : k ≤ 1) :
    (recode window k).1 = 0 := by
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl <;> cases window <;> decide

private theorem digitMagnitude_cast {n : Nat} (i : Fin n) :
    (2 * (i.val : Int) + 1) = ((2 * i.val + 1 : Nat) : Int) := by omega

private theorem addDigit_spec
    {n : Nat} {p : Coordinates} {P Q : curve.Point} (hp : Represents p P)
    {table : Vector Coordinates n} (ht : TableSpec table Q) (d : Option (Digit n)) :
    Represents (addDigit p table d) (P + digitValue d • Q) := by
  cases d with
  | none => simpa only [addDigit, digitValue, zero_zsmul, add_zero] using hp
  | some d =>
    obtain ⟨i, b⟩ := d
    have hi := ht i
    cases b
    · simpa only [addDigit, digitValue, Bool.false_eq_true, ↓reduceIte,
        digitMagnitude_cast, natCast_zsmul] using hp.add hi
    · have hh := negate_spec hi.1
      have he : Represents (negate table[i.val]) (-((2 * i.val + 1) • Q)) :=
        ⟨hh.1, by rw [hh.2, hi.2]⟩
      simpa only [addDigit, digitValue, ↓reduceIte, digitMagnitude_cast, neg_zsmul,
        natCast_zsmul] using hp.add he

private theorem recode_smul (window : Window) (k : Nat) (P : curve.Point) :
    k • P = ((recode window k).1 • P + (recode window k).1 • P) +
      digitValue (recode window k).2 • P := by
  have h := congrArg (fun z : Int => z • P) (recode_eq window k)
  simpa only [add_zsmul, mul_zsmul, natCast_zsmul, two_zsmul] using h

private noncomputable def scalarBound : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ n

private theorem recode_bound (window : Window) (k n : Nat) (hk : k ≤ scalarBound (n + 1)) :
    (recode window k).1 ≤ scalarBound n := by
  cases n with
  | zero => exact (recode_next_eq_zero window k hk).le
  | succ n => exact recode_next_le window k n hk

/-! ## The lattice split -/

private abbrev order : Int := Fn.modulus

private theorem order_pos : 0 < order := by decide

/-- Round `x / n` to the nearest integer. -/
private noncomputable def roundQuotient (x : Int) : Int := (x + (Fn.modulus : Int) / 2) / (Fn.modulus : Int)

/-- Split a scalar using the lattice with basis `(a, -b)` and `(a + b, a)`.

Both vectors give zero under `(u, v) -> u + lambda v` modulo `n`.

The second vector comes from the preceding Euclidean remainder.

Subtract the nearest basis multiples, as in Algorithm 3.74. -/
private noncomputable def splitScalar (k : Nat) : Int × Int :=
  let u := roundQuotient (basisA * k)
  let v := roundQuotient (basisB * k)
  (k - u * basisA - v * (basisA + basisB), u * basisB - v * basisA)

private theorem roundQuotient_error (x : Int) :
    -(order / 2) ≤ x - order * roundQuotient x ∧ x - order * roundQuotient x ≤ order / 2 := by
  have h := Int.mul_ediv_add_emod (x + order / 2) order
  have hlow := Int.emod_nonneg (x + order / 2) (Int.ne_of_gt order_pos)
  have hhigh := Int.emod_lt_of_pos (x + order / 2) order_pos
  have hn : order = 2 * (order / 2) + 1 := by decide
  change -(order / 2) ≤ x - order * ((x + order / 2) / order) ∧
    x - order * ((x + order / 2) / order) ≤ order / 2
  omega

private theorem basis_determinant : basisA * basisA + (basisA + basisB) * basisB = order := by
  decide

private theorem basisA_congr : order ∣ basisA - (lambda.val : Int) * basisB :=
  Int.dvd_iff_emod_eq_zero.mpr (by decide +kernel)

private theorem basisB_congr : order ∣ basisA + basisB + (lambda.val : Int) * basisA :=
  Int.dvd_iff_emod_eq_zero.mpr (by decide +kernel)

private theorem displacedScalar_congr (k : Nat) (u v : Int) :
    order ∣ ((k : Int) - u*basisA - v*(basisA+basisB)) +
      (lambda.val : Int)*(u*basisB - v*basisA) - k := by
  have h1 := Int.dvd_mul_of_dvd_right (b := u) basisA_congr
  have h2 := Int.dvd_mul_of_dvd_right (b := v) basisB_congr
  suffices h : ((k : Int) - u*basisA - v*(basisA+basisB)) +
      (lambda.val : Int)*(u*basisB - v*basisA) - k =
      -(u * (basisA - (lambda.val : Int) * basisB) +
        v * (basisA + basisB + (lambda.val : Int) * basisA)) by
    rw [h]
    exact Int.dvd_neg.mpr (Int.dvd_add h1 h2)
  ring

private theorem displacedScalar_zmod_smul {A : Type} [AddCommGroup A]
    [Module (ZMod Fn.modulus) A] (k : Nat) (u v : Int) (p : A) :
    ((k : Int) - u*basisA - v*(basisA+basisB)) • p +
      (u*basisB - v*basisA) • ((lambda.val : Int) • p) =
      (k : ZMod Fn.modulus) • p := by
  let a : Int := (k : Int) - u*basisA - v*(basisA+basisB)
  let b : Int := u*basisB - v*basisA
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (displacedScalar_congr k u v)
  push_cast at h
  change a • p + b • ((lambda.val : Int) • p) = _
  rw [← Int.cast_smul_eq_zsmul (ZMod Fn.modulus) a,
    ← Int.cast_smul_eq_zsmul (ZMod Fn.modulus) b,
    ← Int.cast_smul_eq_zsmul (ZMod Fn.modulus) (lambda.val : Int), smul_smul,
    mul_comm (b : ZMod Fn.modulus), ← add_smul]
  exact congrArg (fun scalar : ZMod Fn.modulus => scalar • p) (by
    change ((a : ZMod Fn.modulus) + lambda.val * (b : ZMod Fn.modulus)) = _
    dsimp only [a, b]
    push_cast
    exact sub_eq_zero.mp h)

private theorem displacedScalar_smul (k : Fn) (u v : Nat) (p : curve.Point) :
    ((k.val : Int) - u*basisA - v*(basisA+basisB)) • p +
      ((u : Int)*basisB - v*basisA) • (lambda.val • p) = k.val • p := by
  have h := displacedScalar_zmod_smul k.val (u : Int) (v : Int) p
  rw [natCast_zsmul, smul_eq_val_nsmul, ZMod.val_natCast_of_lt k.isLt] at h
  exact h

/-- Splitting preserves the scalar's action on a group of exponent `n`. -/
private theorem splitScalar_smul {A : Type} [AddCommGroup A] [Module (ZMod Fn.modulus) A]
    (k : Nat) (p : A) :
    (splitScalar k).1 • p + (splitScalar k).2 • ((lambda.val : Int) • p) =
      (k : ZMod Fn.modulus) • p :=
  displacedScalar_zmod_smul k (roundQuotient (basisA * k)) (roundQuotient (basisB * k)) p

private theorem natAbs_le_of_bounds {x y : Int} (hlo : -y ≤ x) (hhi : x ≤ y) :
    x.natAbs ≤ y.natAbs := by omega

private theorem component_bound {component c d x y : Int} {radius : Nat}
    (h : order * component = c * x + d * y)
    (hx : x.natAbs ≤ radius) (hy : y.natAbs ≤ radius)
    (hcoeff : (c.natAbs + d.natAbs) * radius < order.natAbs * 2^128) :
    component.natAbs < 2^128 := by
  apply Nat.lt_of_mul_lt_mul_left (a := order.natAbs)
  calc
    order.natAbs * component.natAbs = (order * component).natAbs := (Int.natAbs_mul _ _).symm
    _ = (c * x + d * y).natAbs := congrArg Int.natAbs h
    _ ≤ (c * x).natAbs + (d * y).natAbs := Int.natAbs_add_le _ _
    _ = c.natAbs * x.natAbs + d.natAbs * y.natAbs := by rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ c.natAbs * radius + d.natAbs * radius :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hx) (Nat.mul_le_mul_left _ hy)
    _ = (c.natAbs + d.natAbs) * radius := (Nat.add_mul _ _ _).symm
    _ < order.natAbs * 2^128 := hcoeff

/-- Both signed components fit in 128 bits in magnitude. -/
private theorem splitScalar_bound (k : Nat) :
    (splitScalar k).1.natAbs < 2^128 ∧ (splitScalar k).2.natAbs < 2^128 := by
  let x : Int := k
  let u := roundQuotient (basisA * x)
  let v := roundQuotient (basisB * x)
  let d1 := basisA * x - order * u
  let d2 := basisB * x - order * v
  have hd1 := roundQuotient_error (basisA * x)
  have hd2 := roundQuotient_error (basisB * x)
  have hfirst : order * (splitScalar k).1 = basisA * d1 + (basisA + basisB) * d2 := by
    change order * (x - u * basisA - v * (basisA + basisB)) =
      basisA * (basisA * x - order * u) + (basisA + basisB) * (basisB * x - order * v)
    rw [← basis_determinant]
    ring
  have hsecond : order * (splitScalar k).2 = -basisB * d1 + basisA * d2 := by
    change order * (u * basisB - v * basisA) =
      -basisB * (basisA * x - order * u) + basisA * (basisB * x - order * v)
    ring
  have hd1' : d1.natAbs ≤ (order / 2).natAbs := natAbs_le_of_bounds hd1.1 hd1.2
  have hd2' : d2.natAbs ≤ (order / 2).natAbs := natAbs_le_of_bounds hd2.1 hd2.2
  exact ⟨component_bound hfirst hd1' hd2' (by decide +kernel),
    component_bound hsecond hd1' hd2' (by decide +kernel)⟩


private theorem split_components_bound (k u v : Nat)
    (ha : ((k : Int)*basisA - order*u).natAbs ≤ (3*order/4).natAbs)
    (hb : ((k : Int)*basisB - order*v).natAbs ≤ (3*order/4).natAbs) :
    ((k : Int) - u*basisA - v*(basisA+basisB)).natAbs < 2^128 ∧
      ((u : Int)*basisB - v*basisA).natAbs < 2^128 := by
  let d1 : Int := (k : Int)*basisA - order*u
  let d2 : Int := (k : Int)*basisB - order*v
  have first :
      order * ((k : Int) - u*basisA - v*(basisA+basisB)) =
        basisA*d1 + (basisA+basisB)*d2 := by
    dsimp only [d1, d2]
    rw [← basis_determinant]
    ring
  have second : order * ((u : Int)*basisB - v*basisA) =
      -basisB*d1 + basisA*d2 := by
    dsimp only [d1, d2]
    ring
  exact ⟨component_bound first ha hb (by decide +kernel),
    component_bound second ha hb (by decide +kernel)⟩

section SplitWords

open Montgomery

/-- Interpret a scalar magnitude and its sign as an integer. -/
def componentValue (w : WordPair × Bool) : Int :=
  if w.2 then -(w.1.toNat : Int) else (w.1.toNat : Int)

private abbrev splitRadix : Nat := 2^64
private abbrev splitLimit : Nat := 2^128
private abbrev splitModulus : Nat := 2^129
private abbrev SplitResidue := ZMod splitModulus

private noncomputable def splitLow192 (a : Raw) : Nat :=
  a.w0.toNat + splitRadix*a.w1.toNat + splitRadix^2*a.w2.toNat

private theorem split_product_model (r x y a b c : Nat) :
    (x+y*r)*(a+r*b+r^2*c) =
      x*a+r*(x*b+y*a)+r^2*(x*c+y*b)+r^3*(y*c) := by ring

private theorem split_lowProduct_value (a : WordPair) (b : Raw) :
    ∃ q : Nat, splitLow192 (lowProduct a b.w0 b.w1 b.w2) + splitRadix^3*q =
      a.toNat * splitLow192 b := by
  let w0 := wordProduct a.lo b.w0
  let c0 : ProductColumn := ⟨w0.hi, 0, 0⟩
  let c1 := c0.add (wordProduct a.lo b.w1)
  let w1 := c1.add (wordProduct a.hi b.w0)
  let t := w1.mid.toNat + a.hi.toNat*b.w1.toNat + a.lo.toNat*b.w2.toNat
  have h0 : w0.lo.toNat + splitRadix*w0.hi.toNat = a.lo.toNat*b.w0.toNat :=
    wordProduct_value _ _
  have hc0 : c0.hi.toNat < 16 := by
    change (0 : UInt64).toNat < 16
    decide
  obtain ⟨hc, hb⟩ := ProductColumn.product_spec c0 a.lo b.w1 hc0
  change c1.val = c0.val + a.lo.toNat*b.w1.toNat at hc
  change c1.hi.toNat ≤ 2 at hb
  have hw : w1.val = c1.val + a.hi.toNat*b.w0.toNat :=
    (ProductColumn.product_spec c1 a.hi b.w0 (by omega)).1
  have hval : w1.val = w0.hi.toNat + a.lo.toNat*b.w1.toNat + a.hi.toNat*b.w0.toNat := by
    rw [hw,hc]
    rfl
  have ht : (w1.mid + a.hi*b.w1 + a.lo*b.w2).toNat = t % splitRadix := by
    simp only [t, splitRadix, UInt64.toNat_add, UInt64.toNat_mul,
      Nat.mod_add_mod, Nat.add_mod_mod]
  have hr := Nat.mod_add_div t splitRadix
  refine ⟨w1.hi.toNat + t / splitRadix + a.hi.toNat*b.w2.toNat, ?_⟩
  change w0.lo.toNat + splitRadix*w1.lo.toNat +
      splitRadix^2*(w1.mid + a.hi*b.w1 + a.lo*b.w2).toNat + _ = _
  rw [ht]
  unfold WordPair.toNat splitLow192
  rw [split_product_model]
  simp only [ProductColumn.val, wordRadix, splitRadix] at hval h0 hr ⊢
  dsimp only [t] at hr
  omega

private theorem split_lowSub_value (a b : Raw) :
    ∃ q : Nat, splitLow192 (lowSub a b) + splitLow192 b =
      splitLow192 a + splitRadix^3*q := by
  let d0 := minus a.w0 b.w0 0
  let d1 := minus a.w1 b.w1 d0.hi
  let d2 := minus a.w2 b.w2 d1.hi
  obtain ⟨h0,hb0⟩ := minus_spec a.w0 b.w0 0 (by decide)
  change d0.lo.toNat + b.w0.toNat + 0 = a.w0.toNat + splitRadix*d0.hi.toNat at h0
  change d0.hi.toNat ≤ 1 at hb0
  obtain ⟨h1,hb1⟩ := minus_spec a.w1 b.w1 d0.hi hb0
  change d1.hi.toNat ≤ 1 at hb1
  obtain ⟨h2,_⟩ := minus_spec a.w2 b.w2 d1.hi hb1
  change d1.lo.toNat + b.w1.toNat + d0.hi.toNat =
    a.w1.toNat + splitRadix*d1.hi.toNat at h1
  change d2.lo.toNat + b.w2.toNat + d1.hi.toNat =
    a.w2.toNat + splitRadix*d2.hi.toNat at h2
  have e0 : d0.hi = yes (a.w0 < b.w0) := by simp [d0, minus, yes, Bool.toUInt64]
  have e1 : d1.hi = subtractBorrow a.w1 b.w1 d0.hi := (subtractBorrow_eq _ _ _ hb0).symm
  have he : lowSub a b = ⟨d0.lo,d1.lo,d2.lo,0⟩ := by
    unfold lowSub
    dsimp only
    rw [← e0, ← e1]
    simp [d0, d1, d2, minus]
  refine ⟨d2.hi.toNat, ?_⟩
  rw [he]
  simp only [splitLow192, splitRadix] at *
  omega

private theorem split_radix3_cast : ((splitRadix^3 : Nat) : SplitResidue) = 0 := by
  rw [show splitRadix^3 = splitModulus*2^63 by decide, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private theorem split_lowProduct_cast (a : WordPair) (b : Raw) :
    (splitLow192 (lowProduct a b.w0 b.w1 b.w2) : SplitResidue) =
      (a.toNat : SplitResidue) * (splitLow192 b : SplitResidue) := by
  obtain ⟨q,h⟩ := split_lowProduct_value a b
  simpa only [Nat.cast_add, Nat.cast_mul, split_radix3_cast, zero_mul, add_zero] using
    congrArg (fun n : Nat => (n : SplitResidue)) h

private theorem split_lowSub_cast (a b : Raw) :
    (splitLow192 (lowSub a b) : SplitResidue) =
      (splitLow192 a : SplitResidue) - (splitLow192 b : SplitResidue) := by
  obtain ⟨q,h⟩ := split_lowSub_value a b
  apply eq_sub_iff_add_eq.mpr
  simpa only [Nat.cast_add, Nat.cast_mul, split_radix3_cast, zero_mul, add_zero] using
    congrArg (fun n : Nat => (n : SplitResidue)) h

private theorem split_low192_cast (a : Raw) :
    (splitLow192 a : SplitResidue) = (a.val : SplitResidue) := by
  have h : a.val = splitLow192 a + splitRadix^3*a.w3.toNat := rfl
  rw [h, Nat.cast_add, Nat.cast_mul, split_radix3_cast, zero_mul, add_zero]

private theorem split_pair_lt (a : WordPair) : a.toNat < splitLimit := by
  have h0 := a.lo.toNat_lt
  have h1 := a.hi.toNat_lt
  simp only [WordPair.toNat, splitLimit]
  omega

private theorem split_signBit (a : UInt64) : (a &&& 1).toNat = a.toNat % 2 := by
  rw [UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

private theorem split_low192_mod (a : Raw) :
    splitLow192 a % splitModulus =
      (⟨a.w0,a.w1⟩ : WordPair).toNat + splitLimit * (a.w2 &&& 1).toNat := by
  rw [split_signBit]
  have h := Nat.mod_add_div a.w2.toNat 2
  have hh := split_pair_lt ⟨a.w0,a.w1⟩
  have hb : a.w2.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have hh' : splitLow192 a =
      (⟨a.w0,a.w1⟩ : WordPair).toNat + splitLimit*(a.w2.toNat%2) +
        (a.w2.toNat/2)*splitModulus := by
    simp [splitLow192, WordPair.toNat, splitRadix, splitLimit, splitModulus]
    omega
  rw [hh', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  simp only [splitLimit, splitModulus] at hh ⊢
  omega

private theorem split_negate_pair (a : WordPair) (ha : 0 < a.toNat) :
    (⟨0-a.lo,0-a.hi-yes (a.lo != 0)⟩ : WordPair).toNat = splitLimit-a.toNat := by
  let e0 := minus 0 a.lo 0
  let e1 := minus 0 a.hi e0.hi
  obtain ⟨h0,hb0⟩ := minus_spec 0 a.lo 0 (by decide)
  obtain ⟨h1,hb1⟩ := minus_spec 0 a.hi e0.hi hb0
  have er : e0.hi = yes (a.lo != 0) := by
    by_cases h : a.lo = 0
    · simp [e0, h, minus, yes, Bool.toUInt64]
    · have hn : a.lo.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp hz)
      have hp : (0 : UInt64) < a.lo := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
        omega
      simp [e0, h, hp, minus, yes, Bool.toUInt64]
  have he : (⟨0-a.lo,0-a.hi-yes (a.lo != 0)⟩ : WordPair) = ⟨e0.lo,e1.lo⟩ := by
    rw [← er]
    simp [e0,e1,minus]
  have ht := split_pair_lt ⟨e0.lo,e1.lo⟩
  change e0.lo.toNat + a.lo.toNat + 0 = 0 + splitRadix*e0.hi.toNat at h0
  change e1.lo.toNat+a.hi.toNat+e0.hi.toNat = 0+splitRadix*e1.hi.toNat at h1
  change e1.hi.toNat ≤ 1 at hb1
  rw [he]
  simp only [WordPair.toNat, splitLimit, splitRadix] at ha ht h0 h1 ⊢
  omega

private theorem split_signedMagnitude_spec (a : Raw) (x : Int)
    (h : (splitLow192 a : SplitResidue) = (x : SplitResidue)) (hb : x.natAbs < splitLimit) :
    (signedMagnitude a).1.toNat = x.natAbs ∧ (signedMagnitude a).2 = decide (x < 0) := by
  let w : WordPair := ⟨a.w0,a.w1⟩
  let bit := a.w2 &&& 1
  have hw := split_pair_lt w
  have hbit : bit.toNat < 2 := by
    rw [show bit.toNat = a.w2.toNat % 2 from split_signBit _]
    exact Nat.mod_lt _ (by decide)
  have hm := congrArg (fun z : SplitResidue => (z.val : Int)) h
  rw [ZMod.val_natCast, ZMod.val_intCast, split_low192_mod] at hm
  change ((w.toNat + splitLimit * bit.toNat : Nat) : Int) =
    x % (splitModulus : Int) at hm
  have hspan : (splitLimit : Int) ≤ (splitModulus : Int) := by decide
  have hmag : (x.natAbs : Int) < (splitLimit : Int) := Int.ofNat_lt.mpr hb
  by_cases hx : x < 0
  · have ha : (x.natAbs : Int) = -x := by omega
    have hd := Int.ediv_eq_neg_one_of_neg_of_le hx (b := (splitModulus : Int)) (by omega)
    have hr := Int.emod_add_mul_ediv x (splitModulus : Int)
    rw [hd] at hr
    have he : bit.toNat = 1 ∧ w.toNat = splitLimit - x.natAbs ∧ 0 < w.toNat := by
      simp only [Nat.cast_add, Nat.cast_mul, splitLimit, splitModulus] at hm hr hw hb ⊢
      omega
    have hn : bit ≠ 0 := by
      intro hz
      rw [hz, UInt64.toNat_zero] at he
      omega
    have hn' : a.w2 &&& 1 ≠ 0 := hn
    have hneg := split_negate_pair w he.2.2
    have hs : signedMagnitude a = (⟨0-a.w0,0-a.w1-yes (a.w0 != 0)⟩, true) := by
      unfold signedMagnitude
      rw [show ((a.w2 &&& 1) != (0 : UInt64)) = true from bne_iff_ne.mpr hn']
      rfl
    rw [hs, show decide (x < 0) = true from decide_eq_true hx]
    have hcalc : splitLimit - w.toNat = x.natAbs := by omega
    exact ⟨hneg.trans hcalc, rfl⟩
  · have ha : (x.natAbs : Int) = x := Int.natAbs_of_nonneg (by omega)
    have hr : x % (splitModulus : Int) = x := Int.emod_eq_of_lt (by omega) (by omega)
    have he : bit.toNat = 0 ∧ w.toNat = x.natAbs := by
      rw [hr] at hm
      simp only [Nat.cast_add, Nat.cast_mul, splitLimit] at hm hb ⊢
      omega
    have hz : a.w2 &&& 1 = 0 := UInt64.toNat_inj.mp he.1
    simp only [signedMagnitude, hz, bne_self_eq_false, hx, decide_false]
    exact ⟨he.2,rfl⟩

private theorem split_pair_injective : Function.Injective WordPair.toNat := by
  intro x y he
  have hx := x.lo.toNat_lt
  have hy := y.lo.toNat_lt
  simp only [WordPair.toNat] at he
  have hlo : x.lo.toNat = y.lo.toNat := by omega
  have hhi : x.hi.toNat = y.hi.toNat := by omega
  cases x
  cases y
  cases UInt64.toNat_inj.mp hlo
  cases UInt64.toNat_inj.mp hhi
  rfl

private theorem split_pair_ofNat (x : Nat) (h : x < splitLimit) :
    (WordPair.ofNat x).toNat = x := by
  unfold WordPair.ofNat WordPair.toNat
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have hdiv : x / 2^64 < 2^64 := by
    simp only [splitLimit] at h
    omega
  rw [Nat.mod_eq_of_lt hdiv]
  omega

private theorem split_signedMagnitude_eq (a : Raw) (x : Int)
    (h : (splitLow192 a : SplitResidue) = (x : SplitResidue)) (hb : x.natAbs < splitLimit) :
    signedMagnitude a = (WordPair.ofNat x.natAbs, decide (x < 0)) := by
  have hs := split_signedMagnitude_spec a x h hb
  exact Prod.ext (split_pair_injective (hs.1.trans (split_pair_ofNat _ hb).symm)) hs.2

private theorem split_basis_sum :
    (splitLow192 splitConstants.sum : Int) = basisA + basisB := by decide

/-- With bounded lattice differences, the low-word split retains both magnitudes and signs. -/
theorem splitScalarWords_eq (k : Raw) :
    let u := (approximateWeight k splitConstants.aRecip).toNat
    let v := (approximateWeight k splitConstants.bRecip).toNat
    let a : Int := (k.val : Int) - (u : Int)*basisA - (v : Int)*(basisA+basisB)
    let b : Int := (u : Int)*basisB - (v : Int)*basisA
    a.natAbs < 2^128 → b.natAbs < 2^128 →
      splitScalarWords k = ((WordPair.ofNat a.natAbs, decide (a < 0)),
        (WordPair.ofNat b.natAbs, decide (b < 0))) := by
  dsimp only
  intro ha hb
  let c := splitConstants
  let u := approximateWeight k c.aRecip
  let v := approximateWeight k c.bRecip
  let aw : Raw := ⟨c.a.lo,c.a.hi,0,0⟩
  let bw : Raw := ⟨c.b.lo,c.b.hi,0,0⟩
  let ua := lowProduct u aw.w0 aw.w1 aw.w2
  let vb := lowProduct v c.sum.w0 c.sum.w1 c.sum.w2
  let ub := lowProduct u bw.w0 bw.w1 bw.w2
  let va := lowProduct v aw.w0 aw.w1 aw.w2
  let a : Int := (k.val : Int) - (u.toNat : Int)*basisA - (v.toNat : Int)*(basisA+basisB)
  let b : Int := (u.toNat : Int)*basisB - (v.toNat : Int)*basisA
  have hA : (splitLow192 aw : Int) = basisA := by decide
  have hB : (splitLow192 bw : Int) = basisB := by decide
  have hsum : (splitLow192 c.sum : Int) = basisA+basisB := split_basis_sum
  have ac := congrArg (fun x : Int => (x : SplitResidue)) hA
  have bc := congrArg (fun x : Int => (x : SplitResidue)) hB
  have sc := congrArg (fun x : Int => (x : SplitResidue)) hsum
  simp only [Int.cast_natCast, Int.cast_add] at ac bc sc
  have h1 : (splitLow192 (lowSub (lowSub k ua) vb) : SplitResidue) = (a : SplitResidue) := by
    rw [split_lowSub_cast (lowSub k ua) vb, split_lowSub_cast k ua, split_low192_cast k]
    rw [show (splitLow192 ua : SplitResidue) = _ from split_lowProduct_cast u aw,
      show (splitLow192 vb : SplitResidue) = _ from split_lowProduct_cast v c.sum, ac, sc]
    simp only [a, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_add]
  have h2 : (splitLow192 (lowSub ub va) : SplitResidue) = (b : SplitResidue) := by
    rw [split_lowSub_cast ub va]
    rw [show (splitLow192 ub : SplitResidue) = _ from split_lowProduct_cast u bw,
      show (splitLow192 va : SplitResidue) = _ from split_lowProduct_cast v aw, ac, bc]
    simp only [b, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  change (signedMagnitude (lowSub (lowSub k ua) vb), signedMagnitude (lowSub ub va)) =
    ((WordPair.ofNat a.natAbs, decide (a < 0)), (WordPair.ofNat b.natAbs, decide (b < 0)))
  rw [split_signedMagnitude_eq _ _ h1 ha, split_signedMagnitude_eq _ _ h2 hb]

private theorem componentValue_ofNatAbs (x : Int) (hx : x.natAbs < splitLimit) :
    componentValue (WordPair.ofNat x.natAbs, decide (x < 0)) = x := by
  simp only [componentValue, split_pair_ofNat _ hx, decide_eq_true_eq]
  split <;> omega

/-- Each bounded word component equals its lattice difference. -/
theorem splitScalarWords_components_of_bounds (k : Raw) :
    let u := (approximateWeight k splitConstants.aRecip).toNat
    let v := (approximateWeight k splitConstants.bRecip).toNat
    let a : Int := (k.val : Int) - (u : Int)*basisA - (v : Int)*(basisA+basisB)
    let b : Int := (u : Int)*basisB - (v : Int)*basisA
    a.natAbs < 2^128 → b.natAbs < 2^128 →
      componentValue (splitScalarWords k).1 = a ∧ componentValue (splitScalarWords k).2 = b := by
  dsimp only
  intro ha hb
  rw [splitScalarWords_eq k ha hb]
  exact ⟨componentValue_ofNatAbs _ ha, componentValue_ofNatAbs _ hb⟩

end SplitWords

section WeightProof

open Montgomery


private noncomputable def upperProduct (k c : Raw) : Nat :=
  (k.w1.toNat*c.w2.toNat + k.w2.toNat*c.w1.toNat + k.w3.toNat*c.w0.toNat)*2^192 +
  (k.w2.toNat*c.w2.toNat + k.w3.toNat*c.w1.toNat)*2^256 +
    k.w3.toNat*c.w2.toNat*(2^64*2^256)

private noncomputable def lowerProduct (k c : Raw) : Nat :=
  k.w0.toNat*c.w0.toNat +
  (k.w0.toNat*c.w1.toNat + k.w1.toNat*c.w0.toNat)*2^64 +
  (k.w0.toNat*c.w2.toNat + k.w1.toNat*c.w1.toNat + k.w2.toNat*c.w0.toNat)*2^128

private theorem upper_add_lower (k c : Raw) (hc : c.w3 = 0) :
    upperProduct k c + lowerProduct k c = k.val * c.val := by
  simp only [upperProduct, lowerProduct, Raw.val, Raw.words, lowValue, hc, UInt64.toNat_zero,
    Nat.mul_zero, Nat.add_zero]
  change _ = (_ + (2^64)*k.w1.toNat + (2^64)^2*k.w2.toNat + (2^64)^3*k.w3.toNat) *
    (c.w0.toNat + (2^64)*c.w1.toNat + (2^64)^2*c.w2.toNat)
  change (_ * (2^64)^3 + _ * (2^64)^4 + _ * (2^64)^5) +
    (_ + _ * (2^64) + _ * (2^64)^2) = _
  generalize (2^64 : Nat) = r
  simp only [Nat.add_mul, Nat.mul_add, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  ac_rfl

private theorem lowerProduct_lt (k c : Raw) : lowerProduct k c < 6*2^256 := by
  have small (x y : UInt64) : x.toNat*y.toNat < 2^128 := by
    have h : x.toNat*y.toNat < 2^64*2^64 := Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt
    exact h
  have h00 := small k.w0 c.w0
  have h01 := small k.w0 c.w1
  have h10 := small k.w1 c.w0
  have h02 := small k.w0 c.w2
  have h11 := small k.w1 c.w1
  have h20 := small k.w2 c.w0
  unfold lowerProduct
  omega

private theorem upperProduct_limit (k c : Raw) (hc : c.w3 = 0)
    (hc2 : c.w2.toNat < 65535) : upperProduct k c < (2^144*2^256) - (2^128*2^256) := by
  have hk : k.val < 2^256 := lowValue_lt k.words
  have hc0 := c.w0.toNat_lt
  have hc1 := c.w1.toNat_lt
  have hcval : c.val < 2^144 - 2^128 := by
    simp only [Raw.val, Raw.words, lowValue, wordRadix, hc, UInt64.toNat_zero, Nat.mul_zero,
      Nat.add_zero]
    omega
  have htotal : k.val*c.val < 2^256 * (2^144-2^128) := Nat.mul_lt_mul'' hk hcval
  change k.val*c.val < (2^144*2^256) - (2^128*2^256) at htotal
  have h := upper_add_lower k c hc
  omega

private theorem approximateColumns (k c : Raw) :
    let zero : ProductColumn := ⟨0, 0, 0⟩
    let c3 := ((zero.add (wordProduct k.w1 c.w2)).add (wordProduct k.w2 c.w1)).add
      (wordProduct k.w3 c.w0)
    let c4 := (c3.next.add (wordProduct k.w2 c.w2)).add (wordProduct k.w3 c.w1)
    let c5 := c4.next.add (wordProduct k.w3 c.w2)
    upperProduct k c = c3.lo.toNat*2^192 + c4.lo.toNat*2^256 + c5.val*(2^64*2^256) := by
  let zero : ProductColumn := ⟨0, 0, 0⟩
  let k3 := [(k.w1,c.w2),(k.w2,c.w1),(k.w3,c.w0)]
  let c3 := addProducts zero k3
  let k4 := [(k.w2,c.w2),(k.w3,c.w1)]
  let c4 := addProducts c3.next k4
  let c5 := c4.next.add (wordProduct k.w3 c.w2)
  change upperProduct k c = c3.lo.toNat*2^192 + c4.lo.toNat*2^256 + c5.val*(2^64*2^256)
  have h3 := (addProducts_spec zero k3 (by dsimp [zero,k3]; decide)).1
  have h4 := (addProducts_spec c3.next k4 (by change (0:UInt64).toNat + 2*2 < 16; decide)).1
  have h5 := (ProductColumn.product_spec c4.next k.w3 c.w2
    (by change (0:UInt64).toNat < 16; decide)).1
  change c3.val = zero.val + sumProducts k3 at h3
  change c4.val = c3.next.val + sumProducts k4 at h4
  change c5.val = c4.next.val + k.w3.toNat*c.w2.toNat at h5
  have hn3 := c3.next_spec
  have hn4 := c4.next_spec
  have hz : zero.val = 0 := rfl
  simp only [upperProduct]
  simp only [hz, k3, k4, sumProducts, Nat.add_zero] at h3 h4
  simp only [wordRadix] at hn3 hn4
  omega

private theorem shiftWord16 (x : UInt64) : (x >>> 16).toNat = x.toNat / 2^16 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem shiftWord48 (x : UInt64) :
    (x <<< 48).toNat = (x.toNat % 2^16)*2^48 := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (x.toNat*2^48)%2^64 = _
  omega

private theorem weightWord (x y : UInt64) :
    ((x >>> 16) ||| (y <<< 48)).toNat = x.toNat/2^16 + (y.toNat % 2^16)*2^48 := by
  rw [UInt64.toNat_or, shiftWord16, shiftWord48, Nat.or_comm]
  have hx := x.toNat_lt
  rw [Nat.mul_comm _ (2^48), ← Nat.two_pow_add_eq_or_of_lt (i:=48) (b:= x.toNat/2^16) (by omega)]
  ac_rfl

private theorem weightRound (x : UInt64) :
    ((x >>> 15) &&& 1).toNat = x.toNat / 2^15 % 2 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

private theorem roundWordPair (lo hi flag : UInt64)
    (hbound : lo.toNat + 2^64*hi.toNat + flag.toNat < 2^128) :
    (⟨lo + flag, hi + yes (lo + flag < lo)⟩ : WordPair).toNat =
      lo.toNat + 2^64*hi.toNat + flag.toNat := by
  let b := yes (lo+flag < lo)
  have hs := add_with_carry lo flag
  change (lo+flag).toNat + 2^64*b.toNat = lo.toNat + flag.toNat at hs
  have h := add_exact (a:=hi) (b:=b) (by omega)
  change (lo+flag).toNat + (hi+b).toNat *2^64 = _
  rw [h]
  omega

private theorem approximateWeight_value (k c : Raw) (hc : c.w3 = 0)
    (hc2 : c.w2.toNat < 65535) :
    (approximateWeight k c).toNat = (upperProduct k c + (2^15*2^256)) / (2^16*2^256) := by
  let zero : ProductColumn := ⟨0, 0, 0⟩
  let c3 := ((zero.add (wordProduct k.w1 c.w2)).add (wordProduct k.w2 c.w1)).add
    (wordProduct k.w3 c.w0)
  let c4 := (c3.next.add (wordProduct k.w2 c.w2)).add (wordProduct k.w3 c.w1)
  let c5 := c4.next.add (wordProduct k.w3 c.w2)
  let lo := (c4.lo >>> 16) ||| (c5.lo <<< 48)
  let hi := (c5.lo >>> 16) ||| (c5.mid <<< 48)
  let flag := (c4.lo >>> 15) &&& 1
  have hv := approximateColumns k c
  change upperProduct k c = c3.lo.toNat*2^192 + c4.lo.toNat*2^256 + c5.val*(2^64*2^256) at hv
  have ht := upperProduct_limit k c hc hc2
  have h0 := c3.lo.toNat_lt
  have h1 := c4.lo.toNat_lt
  have h2 := c5.lo.toNat_lt
  have h3 := c5.mid.toNat_lt
  simp only [ProductColumn.val, wordRadix] at hv
  have hc5 : c5.mid.toNat < 2^16 ∧ c5.hi.toNat = 0 := by omega
  have hLo : lo.toNat = c4.lo.toNat/2^16 + (c5.lo.toNat % 2^16)*2^48 :=
    weightWord c4.lo c5.lo
  have hHi : hi.toNat = c5.lo.toNat/2^16 + c5.mid.toNat*2^48 := by
    dsimp only [hi]
    rw [weightWord, Nat.mod_eq_of_lt hc5.1]
  have hFlag := weightRound c4.lo
  change flag.toNat = _ at hFlag
  have hquot : lo.toNat + 2^64*hi.toNat + flag.toNat =
      (upperProduct k c + (2^15*2^256)) / (2^16*2^256) := by
    rw [hLo,hHi,hFlag]
    omega
  change (⟨lo+flag, hi+yes (lo+flag < lo)⟩ : WordPair).toNat = _
  exact (roundWordPair lo hi flag (by rw [hquot]; omega)).trans hquot

private theorem weight_balance (radix half k a c n q hi lo remK remQ : Nat)
    (hRec : c*n + remK = a*radix) (hDiv : q*radix + remQ = hi + half)
    (hFull : hi + lo = k*c) :
    radix*(k*a) + half*n = radix*(q*n) + (remQ+lo)*n + k*remK := calc
  _ = k*(a*radix) + half*n := by ac_rfl
  _ = k*(c*n + remK) + half*n := by rw [hRec]
  _ = ((hi+lo)+half)*n + k*remK := by
    rw [Nat.mul_add, ← Nat.mul_assoc k c n, ← hFull]
    simp only [Nat.add_mul]
    ac_rfl
  _ = ((hi+half)+lo)*n + k*remK := by ac_rfl
  _ = ((q*radix+remQ)+lo)*n + k*remK := by rw [hDiv]
  _ = _ := by simp only [Nat.add_mul]; ac_rfl

private theorem abs_difference_le (x y bound : Nat) (hx : x ≤ y+bound) (hy : y ≤ x+bound) :
    ((x : Int)-(y : Int)).natAbs ≤ bound := by omega

private theorem weight_error_interval (a b remQ lo extra : Nat)
    (h : (2^16*2^256)*a + (2^15*2^256)*Fn.modulus =
      (2^16*2^256)*b + (remQ+lo)*Fn.modulus + extra)
    (hq : remQ < (2^16*2^256)) (hl : lo < 6*2^256) (he : extra < 2^256*Fn.modulus) :
    a ≤ b + 3*Fn.modulus/4 ∧ b ≤ a + 3*Fn.modulus/4 := by
  have hUpper : ((2^15*2^256) + 7*2^256)*Fn.modulus ≤ (2^16*2^256)*(3*Fn.modulus/4) := by decide
  have hLower : (2^15*2^256)*Fn.modulus ≤ (2^16*2^256)*(3*Fn.modulus/4) := by decide
  have hn : 0 < Fn.modulus := by decide
  -- The digits `remQ` and `lo` bound their product with `n`, so every remaining term is linear.
  have hX : (remQ + lo) * Fn.modulus < ((2^16*2^256) + 6*2^256) * Fn.modulus :=
    Nat.mul_lt_mul_of_pos_right (by omega) hn
  constructor
  · by_contra hc
    have hm := Nat.mul_le_mul_left ((2^16*2^256)) (show b + 3*Fn.modulus/4 + 1 ≤ a by omega)
    linarith
  · by_contra hc
    have hm := Nat.mul_le_mul_left ((2^16*2^256)) (show a + 3*Fn.modulus/4 + 1 ≤ b by omega)
    have h0 : 0 ≤ (remQ + lo) * Fn.modulus := Nat.zero_le _
    linarith

private theorem reciprocalWeight_error (w c : Raw) (a : Nat)
    (hw : w.val < Fn.modulus) (hc : c.w3 = 0) (hc2 : c.w2.toNat < 65535)
    (hrecip : c.val = (a*(2^16*2^256))/Fn.modulus) :
    (((w.val : Int) * (a : Int)) -
      (Fn.modulus : Int) * ((approximateWeight w c).toNat : Int)).natAbs ≤
      (3*(Fn.modulus : Int)/4).natAbs := by
  let n := Fn.modulus
  let q := (approximateWeight w c).toNat
  let top := upperProduct w c
  let low := lowerProduct w c
  let remK := (a*(2^16*2^256)) % n
  let remQ := (top + (2^15*2^256)) % (2^16*2^256)
  have hrec : c.val*n + remK = a*(2^16*2^256) := by
    change c.val*Fn.modulus + (a*(2^16*2^256))%Fn.modulus = _
    rw [hrecip]
    exact Nat.div_add_mod' _ _
  have hdiv : q*(2^16*2^256) + remQ = top + (2^15*2^256) := by
    change (approximateWeight w c).toNat*(2^16*2^256) + (top + (2^15*2^256))%(2^16*2^256) = _
    rw [approximateWeight_value w c hc hc2]
    exact Nat.div_add_mod' _ _
  have hfull : top + low = w.val*c.val := upper_add_lower w c hc
  have hbalance := weight_balance ((2^16*2^256)) ((2^15*2^256)) w.val a c.val n q top low remK remQ
    hrec hdiv hfull
  have hlow : low < 6*2^256 := lowerProduct_lt w c
  have hremK : remK < n := Nat.mod_lt _ (by decide)
  have hremQ : remQ < (2^16*2^256) := Nat.mod_lt _ (by decide)
  have hwide : w.val < 2^256 := Nat.lt_trans hw (by decide)
  have hpr : w.val*remK < 2^256*n := Nat.mul_lt_mul'' hwide hremK
  obtain ⟨h1, h2⟩ := weight_error_interval (w.val*a) (q*n) remQ low (w.val*remK)
    hbalance hremQ hlow hpr
  rw [show (3*(Fn.modulus : Int)/4).natAbs = 3*Fn.modulus/4 by decide]
  change ((w.val : Int) * (a : Int) - (n : Int) * (q : Int)).natAbs ≤ _
  rw [Int.mul_comm (n:Int) (q:Int), ← Int.natCast_mul, ← Int.natCast_mul]
  exact abs_difference_le _ _ _ h1 h2

end WeightProof

section

open Montgomery

private theorem splitScalarWords_components_raw (w : Raw) (hw : w.val < Fn.modulus) :
    let u := (approximateWeight w splitConstants.aRecip).toNat
    let v := (approximateWeight w splitConstants.bRecip).toNat
    componentValue (splitScalarWords w).1 = (w.val : Int)-u*basisA-v*(basisA+basisB) ∧
      componentValue (splitScalarWords w).2 = (u : Int)*basisB-v*basisA := by
  let u := (approximateWeight w splitConstants.aRecip).toNat
  let v := (approximateWeight w splitConstants.bRecip).toNat
  have ha := reciprocalWeight_error w splitConstants.aRecip basisA.toNat hw
    (by decide) (by decide) (by decide)
  have hb := reciprocalWeight_error w splitConstants.bRecip basisB.toNat hw
    (by decide) (by decide) (by decide)
  rw [show (basisA.toNat : Int) = basisA by decide] at ha
  rw [show (basisB.toNat : Int) = basisB by decide] at hb
  have hbnds := split_components_bound w.val u v ha hb
  exact splitScalarWords_components_of_bounds w hbnds.1 hbnds.2

end

private abbrev zValue (x : Montgomery) := Jacobian.toZ (Montgomery.toFin x)

private theorem zValue_mul (x y : Montgomery) : zValue (x * y) = zValue x * zValue y := by
  simp only [zValue, toFin_embedding.map_mul, Jacobian.toZ_mul]

private theorem zValue_one : zValue 1 = 1 := by
  simp only [zValue, toFin_embedding.map_one, Jacobian.toZ_one]

private theorem zValue_ne_zero {x : Montgomery} (h : x ≠ 0) : zValue x ≠ 0 := by
  intro hx
  apply h
  apply toFin_embedding.injective
  rw [toFin_embedding.map_zero]
  exact Jacobian.toZ_eq_zero.mp hx

private theorem batchInverse_mul (x : Montgomery) (h : x ≠ 0) :
    zValue (Montgomery.inv x) * zValue x = 1 := by
  have hneg := zValue_ne_zero h
  simp only [zValue] at hneg ⊢
  rw [Montgomery.toFin_inv, Jacobian.toZ_inverse, inv_mul_cancel₀ hneg]

private theorem affineWithInverse_spec {p : Coordinates} {iv : Montgomery}
    (hp : OnCurve p) (hi : zValue iv * zValue p.z = 1) :
    Represents (affineWithInverse iv p) (groupValue p) := by
  have hz : (readCoords p).z ≠ 0 := by
    intro h
    change Montgomery.toFin p.z = 0 at h
    simp only [zValue, h, Jacobian.toZ_zero, mul_zero, zero_ne_one] at hi
  have hInv := eq_inv_of_mul_eq_one_left hi
  let q := readCoords (affineWithInverse iv p)
  have hqz : q.z ≠ 0 := by
    change Montgomery.toFin 1 ≠ (0 : Fp)
    rw [toFin_embedding.map_one]
    decide
  have hx : Jacobian.affX q = Jacobian.affX (readCoords p) := by
    change zValue (p.x * (iv * iv)) / (zValue 1)^2 = zValue p.x / (zValue p.z)^2
    simp only [zValue_mul, zValue_one, one_pow, hInv, div_eq_mul_inv, ← inv_pow]
    ring
  have hy : Jacobian.affY q = Jacobian.affY (readCoords p) := by
    change zValue (p.y * (iv * iv * iv)) / (zValue 1)^3 = zValue p.y / (zValue p.z)^3
    simp only [zValue_mul, zValue_one, one_pow, hInv, div_eq_mul_inv, ← inv_pow]
    ring
  have hq : Jacobian.OnCurve 0 7 q := by
    intro _
    rw [hx, hy]
    exact hp hz
  refine ⟨hq, ?_⟩
  change Jacobian.toPoint 0 7 q = Jacobian.toPoint 0 7 (readCoords p)
  rw [Jacobian.toPoint_of_z_ne_zero hq hqz, Jacobian.toPoint_of_z_ne_zero hp hz]
  simp only [hx, hy]

private abbrev SamePoint (p q : Coordinates) : Prop :=
  OnCurve p → Represents q (groupValue p)

private theorem prepareBatch_spec (ps : List Coordinates) (iv : Montgomery)
    (hi : zValue iv * zValue (prepareBatch ps).1 = 1) :
    List.Forall₂ SamePoint ps ((prepareBatch ps).2 iv).val := by
  induction ps generalizing iv with
  | nil => exact .nil
  | cons p ps ih =>
    let prep := prepareBatch ps
    change zValue iv * zValue (p.z * prep.1) = 1 at hi
    rw [zValue_mul] at hi
    have hfirst : zValue (iv * prep.1) * zValue p.z = 1 := by
      rw [zValue_mul, mul_assoc, mul_comm (zValue prep.1)]
      exact hi
    have hrest : zValue (p.z * iv) * zValue prep.1 = 1 := by
      rw [zValue_mul, mul_comm (zValue p.z), mul_assoc]
      exact hi
    exact .cons (fun hp => affineWithInverse_spec hp hfirst) (ih _ hrest)

private theorem batchNormalize_spec (ps : List Coordinates) :
    List.Forall₂ SamePoint ps (batchNormalize ps).val := by
  have self : ∀ xs, List.Forall₂ SamePoint xs xs := by
    intro xs
    induction xs with
    | nil => exact .nil
    | cons p ps ih => exact .cons (fun h => ⟨h, rfl⟩) ih
  unfold batchNormalize
  dsimp only
  split
  · exact self ps
  · rename_i h
    exact prepareBatch_spec ps _ (batchInverse_mul _ h)

private theorem oddSequence_spec {step current : Coordinates} {R Q : curve.Point}
    (hr : Represents step R) (hq : Represents current Q) (count : Nat) (i : Fin count) :
    Represents ((oddSequence step current count).val[i.val]'(by
      rw [(oddSequence step current count).property]
      exact i.isLt)) (Q + i.val • R) := by
  induction count generalizing current Q with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [oddSequence, List.getElem_cons_zero, Fin.val_zero, zero_nsmul, add_zero] using hq
    · have h := ih (hq.add hr) j
      have he : (Q + R) + j.val • R = Q + (j.val + 1) • R := by
        rw [add_nsmul, one_nsmul]
        abel
      simpa only [oddSequence, Fin.val_succ, List.getElem_cons_succ] using he ▸ h

private theorem generatedMultiples_spec (count : Nat) {p : Point} (hp : p.isOnCurve = true) :
    TableSpec (generatedMultiples count p) (Point.toPoint p) := by
  intro i
  let first := Point.toMontgomeryCoords p
  let step := double first
  let ps := oddSequence step first count
  let table := batchNormalize ps.val
  have hfirst : Represents first (Point.toPoint p) := point_spec hp
  have hd := fastDouble_spec hfirst.1
  have hstep : Represents step (Point.toPoint p + Point.toPoint p) :=
    ⟨hd.1, by rw [hd.2, hfirst.2]⟩
  have hraw := oddSequence_spec hstep hfirst count i
  have hps : i.val < ps.val.length := ps.property.symm ▸ i.isLt
  have htable : i.val < table.val.length := table.property.symm ▸ hps
  have hnorm := (batchNormalize_spec ps.val).get (i := i.val) hps htable hraw.1
  change Represents table.val.toArray[i.val] _
  rw [List.getElem_toArray]
  refine ⟨hnorm.1, hnorm.2.trans ?_⟩
  change groupValue ps.val[i.val] = _
  rw [hraw.2, ← two_nsmul, smul_smul]
  calc
    _ = (1 : Nat) • Point.toPoint p + (i.val * 2) • Point.toPoint p := by rw [one_nsmul]
    _ = _ := by
      rw [← add_nsmul]
      congr 1
      omega

private theorem generatorTable_spec : TableSpec generatorTable14 (Point.toPoint .generator) :=
  generatedMultiples_spec 4096 Point.isOnCurve_generator

private theorem generatorHighTable_spec :
    TableSpec generatorHighTable14 ((2^128 : Nat) • Point.toPoint .generator) := by
  have h := generatedMultiples_spec 4096
    (Point.isOnCurve_mulBits 129 (2^128) Point.isOnCurve_generator)
  rw [Point.toPoint_mulBits 129 (2^128) Point.isOnCurve_generator (by decide)] at h
  exact h

private theorem endomorphismTable_spec
    {t : Vector Coordinates 8} {P : curve.Point} (ht : TableSpec t P) :
    TableSpec (t.map endomorphism) (lambda.val • P) := by
  intro i
  rw [Vector.getElem_map]
  have h := endomorphism_spec (ht i).1
  refine ⟨h.1, ?_⟩
  rw [h.2, (ht i).2, smul_smul, smul_smul, Nat.mul_comm]

private theorem signed_smul (k : Int) (P : curve.Point) :
    k.natAbs • (if k < 0 then -P else P) = k • P := by
  by_cases h : k < 0
  · rw [ite_eq_left h, neg_nsmul, ← natCast_zsmul, ← neg_zsmul]
    congr 1
    omega
  · rw [ite_eq_right h, ← natCast_zsmul, Int.ofNat_natAbs_of_nonneg (by omega)]

private theorem generator_split_smul (l : Nat) (G : curve.Point) :
    (l % 2^128) • G + (l / 2^128) • ((2^128 : Nat) • G) = l • G := by
  rw [smul_smul, ← add_nsmul, Nat.mul_comm (l / 2^128), Nat.mod_add_div]
private theorem ofMontgomeryCoords_eq_of_represents {r : Coordinates} {q : Point}
    (hr : Represents r (Point.toPoint q)) (hq : q.isOnCurve = true) :
    Point.ofMontgomeryCoords r = q := by
  rw [ofMontgomeryCoords_eq_read]
  have hs := Point.ofJacobian_spec hr.1
  exact (Point.toPoint_inj hs.1 hq).mp (hs.2.trans hr.2)

private noncomputable def signedPoint (negative : Bool) (p : Coordinates) : Coordinates :=
  if negative then negate p else p

private noncomputable def selectedPoint (phi : Bool) (p : Coordinates) : Coordinates :=
  if phi then endomorphism p else p

private theorem negate_negate (p : Coordinates) : negate (negate p) = p := by
  have hh : (0 : Montgomery) - (0 - p.y) = p.y := by
    apply toFin_embedding.injective
    apply Jacobian.toZ_injective
    simp only [toFin_embedding.map_sub, toFin_embedding.map_zero, Jacobian.toZ_sub,
      Jacobian.toZ_zero]
    ring
  change ⟨p.x, 0 - (0 - p.y), p.z⟩ = p
  rw [hh]

private theorem signedPoint_twice (a b : Bool) (p : Coordinates) :
    signedPoint a (signedPoint b p) = signedPoint (b != a) p := by
  cases a <;> cases b <;> simp [signedPoint, negate_negate]

private noncomputable def selectedTable (table : Vector Coordinates 8) (phi negative : Bool) :
    Vector Coordinates 8 :=
  table.map (fun p => signedPoint negative (selectedPoint phi p))

private noncomputable def decodeDigit (window : Window) (digit : UInt64) : Option (Digit window.entries) :=
  if digit == 0 then none else some (packedIndex window digit, digit >= window.pivot)

private theorem low_bit_eq (word : UInt64) : (word &&& 1 == 0) = decide (word.toNat % 2 = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_and]
  change word.toNat &&& (2^1 - 1) = 0 ↔ _
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem window_mask_succ (window : Window) :
    (window.mask + 1).toNat = 4 * window.entries := by
  cases window <;> decide

private theorem packedIndex_pos (window : Window) (digit : UInt64)
    (h : digit < window.pivot) : (packedIndex window digit).val = digit.toNat / 2 := by
  unfold packedIndex
  simp only [h, ↓reduceIte, word_shift_right]
  have hp := UInt64.lt_iff_toNat_lt.mp h
  rw [window_pivot] at hp
  exact Nat.mod_eq_of_lt (by omega)

private theorem packedIndex_neg (window : Window) (digit : UInt64)
    (h : ¬ digit < window.pivot) (hlt : digit.toNat < 4 * window.entries)
    (ho : digit.toNat % 2 ≠ 0) :
    (packedIndex window digit).val = (4 * window.entries - digit.toNat) / 2 := by
  unfold packedIndex
  simp only [h, ↓reduceIte, word_shift_right]
  have hd : digit ≤ window.mask + 1 := UInt64.le_iff_toNat_le.mpr (by
    rw [window_mask_succ]; omega)
  rw [UInt64.toNat_sub_of_le _ _ hd, window_mask_succ]
  have hp : window.pivot.toNat ≤ digit.toNat :=
    Nat.le_of_not_gt (mt UInt64.lt_iff_toNat_lt.mpr h)
  rw [window_pivot] at hp
  exact Nat.mod_eq_of_lt (by omega)

private theorem recodeRaw_eq (window : Window) (w : WordPair) :
    let raw := recodeRaw window w.lo w.hi
    let old := recodeWords window w
    raw.lo = old.1.lo ∧ raw.hi = old.1.hi ∧ decodeDigit window raw.digit = old.2 := by
  have hlt : (w.lo &&& window.mask).toNat < 4 * window.entries := by
    rw [word_low window w]; exact Nat.mod_lt _ (by cases window <;> decide)
  unfold recodeRaw recodeWords
  dsimp only
  have hp : (w.lo &&& window.mask) < window.pivot ↔
      (w.lo &&& window.mask).toNat < 2 * window.entries := by
    rw [UInt64.lt_iff_toNat_lt, window_pivot]
  simp only [low_bit_eq]
  by_cases he : (w.lo &&& window.mask).toNat % 2 = 0
  · simp only [he, decide_true, ↓reduceIte, WordPair.half, decodeDigit]
    exact ⟨rfl, rfl, rfl⟩
  · have hd : (w.lo &&& window.mask) ≠ 0 := fun h => he (by rw [h]; decide)
    by_cases hs : (w.lo &&& window.mask) < window.pivot
    · have hn := hp.mp hs
      have hsign : ¬ window.pivot ≤ (w.lo &&& window.mask) := by
        rw [UInt64.le_iff_toNat_le, window_pivot]
        omega
      simp only [he, hs, hn, decide_false, Bool.false_eq_true, ↓reduceIte,
        WordPair.half, WordPair.roundDown, decodeDigit, beq_iff_eq, hd, hsign]
      refine ⟨rfl, rfl, congrArg some (Prod.ext (Fin.ext ?_) rfl)⟩
      exact packedIndex_pos window (w.lo &&& window.mask) hs
    · have hn : ¬ (w.lo &&& window.mask).toNat < 2 * window.entries := mt hp.mpr hs
      have hsign : window.pivot ≤ (w.lo &&& window.mask) := UInt64.le_iff_toNat_le.mpr (by
        rw [window_pivot]; omega)
      simp only [he, hs, hn, decide_false, Bool.false_eq_true, ↓reduceIte,
        WordPair.half, WordPair.roundDown, WordPair.addWord, decodeDigit, beq_iff_eq, hd, hsign,
        decide_true]
      refine ⟨rfl, rfl, congrArg some (Prod.ext (Fin.ext ?_) rfl)⟩
      exact packedIndex_neg window (w.lo &&& window.mask) hs hlt he

private theorem addGenerator_eq (p q : Coordinates) (negative : Bool) :
    addGenerator p q negative = Coords.add 0 p (if negative then negate q else q) := by
  have hassoc (a b c : Montgomery) : a * (b * c) = a * b * c := by
    apply toFin_embedding.injective
    apply Jacobian.toZ_injective
    simp only [toFin_embedding.map_mul, Jacobian.toZ_mul, mul_assoc]
  have hone : (1 : Montgomery) ≠ 0 := by decide
  cases q
  cases negative <;> simp only [addGenerator, negate, Bool.false_eq_true, ↓reduceIte] <;> split
  all_goals first
    | rfl
    | rename_i hz
      subst hz
      simp only [Coords.add, hone, ↓reduceIte, Montgomery.square_eq_mul, hassoc]

private theorem addPacked_eq (p : Coordinates) (window : Window)
    (table : Vector Coordinates window.entries) (digit : UInt64) :
    addPacked p window table digit = addDigit p table (decodeDigit window digit) := by
  unfold addPacked decodeDigit
  simp only [addGenerator_eq]
  split
  · rfl
  · by_cases h : digit ≥ window.pivot <;> simp [addDigit, h]

private theorem recodeRaw_even (window : Window) (lo hi : UInt64) (h : lo &&& 1 = 0) :
    recodeRaw window lo hi = ⟨(lo >>> 1) + (hi <<< 63), hi >>> 1, 0⟩ := by
  have hm : window.mask &&& 1 = 1 := by cases window <;> decide
  simp only [recodeRaw, UInt64.and_assoc, hm, h, beq_self_eq_true, ↓reduceIte]

private theorem and_distrib (a b c : UInt64) : (a ||| b) &&& c = (a &&& c) ||| (b &&& c) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, UInt64.toNat_or, Nat.and_or_distrib_right]

/-! ## Shared denominators -/

/-! ## A shared denominator for the variable-point table -/

private theorem zValue_zero : zValue 0 = 0 := by
  simp only [zValue, toFin_embedding.map_zero, Jacobian.toZ_zero]

private theorem zValue_add (x y : Montgomery) : zValue (x + y) = zValue x + zValue y := by
  simp only [zValue, toFin_embedding.map_add, Jacobian.toZ_add]

private theorem zValue_sub (x y : Montgomery) : zValue (x - y) = zValue x - zValue y := by
  simp only [zValue, toFin_embedding.map_sub, Jacobian.toZ_sub]

private theorem zValue_injective : Function.Injective zValue :=
  Jacobian.toZ_injective.comp toFin_embedding.injective

private theorem zValue_eq_zero (x : Montgomery) : zValue x = 0 ↔ x = 0 := by
  rw [← zValue_zero]
  exact zValue_injective.eq_iff

private theorem coords_ext_read {p q : Coordinates}
    (hx : zValue p.x = zValue q.x) (hy : zValue p.y = zValue q.y)
    (hz : zValue p.z = zValue q.z) : p = q := by
  have hx' := zValue_injective hx
  have hy' := zValue_injective hy
  have hz' := zValue_injective hz
  cases p
  cases q
  simp only [Coords.mk.injEq]
  exact ⟨hx', hy', hz'⟩

private theorem montgomery_one_ne_zero : (1 : Montgomery) ≠ 0 := by
  intro h
  have hm := congrArg zValue h
  rw [zValue_one, zValue_zero] at hm
  exact one_ne_zero hm

private theorem montgomery_mul_one (x : Montgomery) : x * 1 = x := by
  apply zValue_injective
  calc
    _ = zValue x * zValue 1 := zValue_mul _ _
    _ = zValue x * 1 := congrArg (zValue x * ·) zValue_one
    _ = _ := mul_one _

private theorem montgomery_mul_assoc (x y z : Montgomery) : (x * y) * z = x * (y * z) := by
  apply toFin_embedding.injective
  apply Jacobian.toZ_injective
  simp only [toFin_embedding.map_mul, Jacobian.toZ_mul, mul_assoc]

section

attribute [local irreducible] Montgomery.square Montgomery.halve
  Montgomery.productSubSquare Montgomery.mul Montgomery.add
  Montgomery.sub

private theorem restore_double (z : Montgomery) (p : Coordinates) :
    restoreZ z (double p) = double (restoreZ z p) := by
  have hx : (restoreZ z (double p)).x = (double (restoreZ z p)).x := by
    unfold restoreZ double doubleCore
    rfl
  have hy : (restoreZ z (double p)).y = (double (restoreZ z p)).y := by
    unfold restoreZ double doubleCore
    rfl
  have hz : (restoreZ z (double p)).z = (double (restoreZ z p)).z := by
    unfold restoreZ double doubleCore
    exact montgomery_mul_assoc p.y p.z z
  exact @coords_ext_read (restoreZ z (double p)) (double (restoreZ z p))
    (congrArg zValue hx) (congrArg zValue hy) (congrArg zValue hz)

end

private theorem montgomery_zero_mul (z : Montgomery) : (0 : Montgomery) * z = 0 := by
  apply zValue_injective
  calc
    _ = zValue 0 * zValue z := zValue_mul _ _
    _ = 0 * zValue z := congrArg (· * zValue z) zValue_zero
    _ = 0 := zero_mul _
    _ = _ := zValue_zero.symm

private theorem restore_infinity (z : Montgomery) :
    restoreZ z Coords.infinity = Coords.infinity := by
  change (⟨1, 1, (0 : Montgomery) * z⟩ : Coordinates) = ⟨1, 1, 0⟩
  rw [montgomery_zero_mul]

private theorem restore_zero_iff (p : Coordinates) {z : Montgomery} (hz : z ≠ 0) :
    (restoreZ z p).z = 0 ↔ p.z = 0 := by
  rw [← zValue_eq_zero (restoreZ z p).z, ← zValue_eq_zero p.z]
  change (zValue (p.z * z) = 0 ↔ zValue p.z = 0)
  rw [zValue_mul, mul_eq_zero, or_iff_left (zValue_ne_zero hz)]

private theorem scale_spec {p q : Coordinates} {P : curve.Point} {u : F}
    (hp : Represents p P) (hu : u ≠ 0)
    (hx : zValue q.x = u^2 * zValue p.x)
    (hy : zValue q.y = u^3 * zValue p.y)
    (hz : zValue q.z = u * zValue p.z) : Represents q P := by
  let p' := readCoords p
  let q' := readCoords q
  have hzero : q'.z = 0 ↔ p'.z = 0 := by
    rw [← Jacobian.toZ_eq_zero, show Jacobian.toZ q'.z = zValue q.z from rfl, hz,
      mul_eq_zero, or_iff_right hu]
    exact Jacobian.toZ_eq_zero
  have hax : Jacobian.affX q' = Jacobian.affX p' := by
    change zValue q.x / (zValue q.z)^2 = zValue p.x / (zValue p.z)^2
    rw [hx, hz, mul_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hu)
  have hay : Jacobian.affY q' = Jacobian.affY p' := by
    change zValue q.y / (zValue q.z)^3 = zValue p.y / (zValue p.z)^3
    rw [hy, hz, mul_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hu)
  have hq : Jacobian.OnCurve 0 7 q' := by
    intro hqz
    rw [hax, hay]
    exact hp.1 (mt hzero.mpr hqz)
  refine ⟨hq, ?_⟩
  rw [← hp.2]
  change Jacobian.toPoint 0 7 q' = Jacobian.toPoint 0 7 p'
  by_cases hqz : q'.z = 0
  · rw [Jacobian.toPoint_of_z_eq_zero hqz, Jacobian.toPoint_of_z_eq_zero (hzero.mp hqz)]
  · rw [Jacobian.toPoint_of_z_ne_zero hq hqz, Jacobian.toPoint_of_z_ne_zero hp.1 (mt hzero.mpr hqz)]
    rw [Affine.Point.some.injEq]
    exact ⟨hax, hay⟩

private theorem restore_scaleNumerators {p : Coordinates} {P : curve.Point} (hp : Represents p P)
    {z : Montgomery} (hz : z ≠ 0) : Represents (restoreZ z (scaleNumerators z p)) P := by
  apply scale_spec hp (zValue_ne_zero hz)
  · simp only [restoreZ, scaleNumerators, zValue_mul, Montgomery.square_eq_mul]
    ring
  · simp only [restoreZ, scaleNumerators, zValue_mul, Montgomery.square_eq_mul]
    ring
  · simp only [restoreZ, scaleNumerators, zValue_mul, Montgomery.square_eq_mul]
    ring

private theorem signedPoint_eq_fields (q : Coordinates) (neg : Bool) :
    signedPoint neg q = ⟨q.x, if neg then 0 - q.y else q.y, q.z⟩ := by
  cases q
  cases neg <;> simp only [signedPoint, negate, Bool.false_eq_true, ↓reduceIte]

private theorem sign_fixed_eq (z : Montgomery) (p q : Coordinates) (negative : Bool) :
    addFixed z p q negative = addFixed z p (signedPoint negative q) false := by
  rw [signedPoint_eq_fields]
  simp only [addFixed, zeroElement_eq_true, Bool.false_eq_true, ↓reduceIte]

section

attribute [local irreducible] Montgomery.square Montgomery.halve
  Montgomery.productSubSquare Montgomery.productDiff Montgomery.mul
  Montgomery.add Montgomery.sub


private theorem restore_doubleStd (z : Montgomery) (p : Coordinates) :
    restoreZ z (Coords.double 0 p) = Coords.double 0 (restoreZ z p) := by
  apply @coords_ext_read (restoreZ z (Coords.double 0 p)) (Coords.double 0 (restoreZ z p))
  · have e : (restoreZ z (Coords.double 0 p)).x = (Coords.double 0 (restoreZ z p)).x := by
      unfold restoreZ Coords.double
      simp only [ite_true]
    exact congrArg zValue e
  · have e : (restoreZ z (Coords.double 0 p)).y = (Coords.double 0 (restoreZ z p)).y := by
      unfold restoreZ Coords.double
      simp only [ite_true]
    exact congrArg zValue e
  · change zValue ((p.y * p.z + p.y * p.z) * z) =
      zValue (p.y * (p.z * z) + p.y * (p.z * z))
    simp only [zValue_add, zValue_mul]
    ring

private noncomputable def addWeighted (p : Coordinates) (x y d h r : Montgomery) : Coordinates :=
  if h = 0 then
    if r = 0 then Coords.double 0 p else Coords.infinity
  else addFromDifferences x y d h r

private theorem addWeighted_restore (z : Montgomery) (p : Coordinates)
    (x y d h r : Montgomery) :
    restoreZ z (addWeighted p x y d h r) =
      addWeighted (restoreZ z p) x y (d * z) h r := by
  by_cases hh : h = 0
  · by_cases hr : r = 0
    · simp only [addWeighted, ite_eq_left hh, ite_eq_left hr, restore_doubleStd]
    · simp only [addWeighted, ite_eq_left hh, ite_eq_right hr, restore_infinity]
  · have hz : (d * h) * z = (d * z) * h := by
      apply zValue_injective
      simp only [zValue_mul]
      ring
    simp only [addWeighted, ite_eq_right hh, addFromDifferences, restoreZ, hz]

private theorem weightedLeft_full (p q : Coordinates) :
    (if q.z = 1 then (p.x, p.y, p.z) else
      (p.x * (q.z * q.z), p.y * q.z * (q.z * q.z), p.z * q.z)) =
        (p.x * (q.z * q.z), p.y * q.z * (q.z * q.z), p.z * q.z) := by
  split
  · rename_i hz
    simp only [hz, montgomery_mul_one]
  · rfl

private theorem coords_add_eq_addWeighted {p q : Coordinates} (hp : p.z ≠ 0) (hq : q.z ≠ 0) :
    Coords.add 0 p q = addWeighted p
      (p.x * (q.z * q.z)) (p.y * q.z * (q.z * q.z)) (p.z * q.z)
      (q.x * (p.z * p.z) - p.x * (q.z * q.z))
      (q.y * p.z * (p.z * p.z) - p.y * q.z * (q.z * q.z)) := by
  simp only [Coords.add, ite_eq_right hp, ite_eq_right hq, weightedLeft_full]
  unfold addWeighted addFromDifferences
  simp only [Montgomery.square_eq_mul, Montgomery.productDiff_eq]

private theorem addCommon_eq_addWeighted {p : Coordinates}
    (hp : p.z ≠ 0) (qx qy : Montgomery) :
    addCommon p qx qy = addWeighted p p.x p.y p.z
      (qx * (p.z * p.z) - p.x) (qy * p.z * (p.z * p.z) - p.y) := by
  simp only [addCommon, zeroElement_eq_true, ite_eq_right hp, Montgomery.square_eq_mul,
    addWeighted]

private theorem montgomery_one_mul (x : Montgomery) : (1 : Montgomery) * x = x := by
  apply zValue_injective
  simp only [zValue_mul, zValue_one, one_mul]

private theorem restore_eq_zero {z : Montgomery} {p : Coordinates} (hp : p.z = 0) :
    (restoreZ z p).z = 0 := by
  change p.z * z = 0
  rw [hp, montgomery_zero_mul]

private theorem restore_eq_of_one {z : Montgomery} {p : Coordinates} (hp : p.z = 1) :
    (restoreZ z p).z = z := by
  change p.z * z = z
  rw [hp, montgomery_one_mul]

private theorem addFixed_eq_addWeighted {z : Montgomery} {p q : Coordinates}
    (hp : p.z ≠ 0) (hq : q.z ≠ 0) :
    addFixed z p q false = addWeighted p
      (p.x * (q.z * q.z)) (p.y * q.z * (q.z * q.z)) (p.z * q.z)
      (q.x * ((p.z * z) * (p.z * z)) - p.x * (q.z * q.z))
      (q.y * (p.z * z) * ((p.z * z) * (p.z * z)) - p.y * q.z * (q.z * q.z)) := by
  by_cases hq1 : q.z = 1
  · simp only [addFixed, zeroElement_eq_true, Bool.false_eq_true, ite_false, ite_eq_right hp,
      hq1, ite_eq_right montgomery_one_ne_zero, ite_true, Montgomery.square_eq_mul,
      addWeighted, montgomery_mul_one, montgomery_mul_assoc]
  · simp only [addFixed, zeroElement_eq_true, Bool.false_eq_true, ite_false, ite_eq_right hp,
      ite_eq_right hq, ite_eq_right hq1, Montgomery.square_eq_mul,
      addWeighted, montgomery_mul_assoc]

private theorem groupValue_of_z_zero {p : Coordinates} (h : p.z = 0) : groupValue p = 0 := by
  have h' : (readCoords p).z = 0 :=
    (congrArg Montgomery.toFin h).trans toFin_embedding.map_zero
  exact Jacobian.toPoint_of_z_eq_zero h'

end

section
attribute [local irreducible] Montgomery.square Montgomery.halve
  Montgomery.productSubSquare Montgomery.productDiff Montgomery.mul
  Montgomery.add Montgomery.sub

private theorem unscale_spec {p q : Coordinates} {P : curve.Point} {u : F}
    (hp : Represents p P) (hu : u ≠ 0)
    (hx : zValue p.x = u^2 * zValue q.x)
    (hy : zValue p.y = u^3 * zValue q.y)
    (hz : zValue p.z = u * zValue q.z) : Represents q P := by
  apply scale_spec hp (inv_ne_zero hu)
  · rw [hx, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]
  · rw [hy, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]
  · rw [hz, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

private theorem addWeighted_spec_of_scale (p : Coordinates)
    {x y d h r X Y D H R : Montgomery} {T : curve.Point} {s : F}
    (hs : s ≠ 0)
    (hx : zValue X = zValue x * s^2) (hy : zValue Y = zValue y * s^3)
    (hd : zValue D = zValue d * s)
    (hh : zValue H = zValue h * s^2) (hr : zValue R = zValue r * s^3)
    (href : Represents (addWeighted p X Y D H R) T) :
    Represents (addWeighted p x y d h r) T := by
  have hzero : H = 0 ↔ h = 0 := by
    rw [← zValue_eq_zero H, hh, mul_eq_zero, or_iff_left (pow_ne_zero _ hs), zValue_eq_zero]
  have rzero : R = 0 ↔ r = 0 := by
    rw [← zValue_eq_zero R, hr, mul_eq_zero, or_iff_left (pow_ne_zero _ hs), zValue_eq_zero]
  by_cases h0 : h = 0
  · simpa only [addWeighted, hzero, rzero, ite_eq_left h0] using href
  · simp only [addWeighted, hzero, ite_eq_right h0] at href
    simp only [addWeighted, ite_eq_right h0]
    apply unscale_spec href (pow_ne_zero 3 hs)
    · simp only [addFromDifferences, zValue_mul, zValue_sub, zValue_add,
        Montgomery.square_eq_mul, hx, hh, hr]
      ring
    · simp only [addFromDifferences, Montgomery.productDiff_eq, zValue_mul, zValue_sub,
        zValue_add, Montgomery.square_eq_mul, hx, hy, hh, hr]
      ring
    · simp only [addFromDifferences, zValue_mul, hd, hh]
      ring

private theorem addCommon_spec_of_z_zero
    {p q : Coordinates} {P Q : curve.Point}
    {z : Montgomery} (hpz : p.z = 0) (hqz : q.z = 1)
    (hp : Represents (restoreZ z p) P) (hq : Represents (restoreZ z q) Q) :
    Represents (restoreZ z (addCommon p q.x q.y)) (P + Q) := by
  have hpz' := restore_eq_zero (z := z) hpz
  have hP : P = 0 := hp.2.symm.trans (@groupValue_of_z_zero (restoreZ z p) hpz')
  rw [hP, zero_add]
  have hq' : (⟨q.x, q.y, 1⟩ : Coordinates) = q := by
    cases q with
    | mk x y v =>
      change v = 1 at hqz
      rw [hqz]
  have he : addCommon p q.x q.y = (⟨q.x, q.y, 1⟩ : Coordinates) := by
    simp only [addCommon, zeroElement_eq_true]
    exact ite_eq_left hpz
  rw [he, hq']
  exact hq

private theorem restore_common_weighted_eq
    (z : Montgomery) {p : Coordinates} (hp : p.z ≠ 0) (x y : Montgomery) :
    restoreZ z (addCommon p x y) =
      addWeighted (restoreZ z p) p.x p.y (p.z * z)
        (x * (p.z * p.z) - p.x) (y * p.z * (p.z * p.z) - p.y) :=
  (congrArg (restoreZ z) (addCommon_eq_addWeighted hp x y)).trans
    (addWeighted_restore z p p.x p.y p.z _ _)

private theorem coords_add_weighted_with_z
    {z : Montgomery} {p q : Coordinates} (hp : p.z ≠ 0)
    (hq : q.z ≠ 0) (hqz : q.z = z) :
    Coords.add 0 p q =
      addWeighted p (p.x * (z * z)) (p.y * z * (z * z)) (p.z * z)
        (q.x * (p.z * p.z) - p.x * (z * z))
        (q.y * p.z * (p.z * p.z) - p.y * z * (z * z)) := by
  let weighted := fun w => addWeighted p
    (p.x * (w * w)) (p.y * w * (w * w)) (p.z * w)
    (q.x * (p.z * p.z) - p.x * (w * w))
    (q.y * p.z * (p.z * p.z) - p.y * w * (w * w))
  have hmodel : Coords.add 0 p q = weighted q.z := @coords_add_eq_addWeighted p q hp hq
  exact hmodel.trans (congrArg weighted hqz)

private theorem addShared_compat
    (p : Coordinates) {f g : Coordinates} {T : curve.Point} {v : F}
    {x y d h r X Y D H R : Montgomery}
    (he : f = addWeighted p x y d h r) (hE : g = addWeighted p X Y D H R)
    (hz : v ≠ 0)
    (hx : zValue X = zValue x * v^2) (hy : zValue Y = zValue y * v^3)
    (hd : zValue D = zValue d * v)
    (hh : zValue H = zValue h * v^2) (hr : zValue R = zValue r * v^3)
    (hg : Represents g T) : Represents f T := by
  rw [he]
  apply addWeighted_spec_of_scale p (X := X) (Y := Y) (D := D) (H := H) (R := R)
    hz hx hy hd hh hr
  rwa [← hE]

private theorem addCommon_spec_of_z_ne_zero
    {p q : Coordinates} {P Q : curve.Point} {z : Montgomery}
    (hz : z ≠ 0) (hpz : p.z ≠ 0) (hqz : q.z = 1) (hp : Represents (restoreZ z p) P)
    (hq : Represents (restoreZ z q) Q) : Represents (restoreZ z (addCommon p q.x q.y)) (P + Q) := by
  have hqz' : (restoreZ z q).z = z := restore_eq_of_one hqz
  have hpz' := mt (restore_zero_iff p hz).1 hpz
  have hq0 : (restoreZ z q).z ≠ 0 := by
    rw [hqz']
    exact hz
  let dp := restoreZ z p
  let dq := restoreZ z q
  let h := q.x * (p.z * p.z) - p.x
  let r := q.y * p.z * (p.z * p.z) - p.y
  let hb := dq.x * (dp.z * dp.z) - dp.x * (z * z)
  let rb := dq.y * dp.z * (dp.z * dp.z) - dp.y * z * (z * z)
  have hx : zValue (dp.x * (z * z)) = zValue p.x * (zValue z)^2 := by
    simp only [dp, restoreZ, zValue_mul, pow_two]
  have hy : zValue (dp.y * z * (z * z)) = zValue p.y * (zValue z)^3 := by
    simp only [dp, restoreZ, zValue_mul]
    ring
  have hh : zValue hb = zValue h * (zValue z)^2 := by
    simp only [h, hb, dp, dq, restoreZ, zValue_sub, zValue_mul]
    ring
  have hr : zValue rb = zValue r * (zValue z)^3 := by
    simp only [r, rb, dp, dq, restoreZ, zValue_sub, zValue_mul]
    ring
  exact @addShared_compat dp _ _ (P + Q) (zValue z)
    p.x p.y dp.z h r (dp.x * (z * z)) (dp.y * z * (z * z)) (dp.z * z) hb rb
    (restore_common_weighted_eq z hpz q.x q.y)
    (coords_add_weighted_with_z hpz' hq0 hqz')
    (zValue_ne_zero hz) hx hy (zValue_mul dp.z z) hh hr (hp.add hq)

private theorem addCommon_spec
    {p q : Coordinates} {P Q : curve.Point} {z : Montgomery}
    (hz : z ≠ 0) (hqz : q.z = 1) (hp : Represents (restoreZ z p) P)
    (hq : Represents (restoreZ z q) Q) : Represents (restoreZ z (addCommon p q.x q.y)) (P + Q) := by
  by_cases hpz : p.z = 0
  · exact addCommon_spec_of_z_zero hpz hqz hp hq
  · exact addCommon_spec_of_z_ne_zero hz hpz hqz hp hq

end

section

attribute [local irreducible] Montgomery.square Montgomery.halve
  Montgomery.productSubSquare Montgomery.productDiff Montgomery.mul
  Montgomery.add Montgomery.sub

private theorem restore_fixed_weighted_eq {z : Montgomery} {p q : Coordinates}
    (hp : p.z ≠ 0) (hq : q.z ≠ 0) :
    restoreZ z (addFixed z p q false) = addWeighted (restoreZ z p)
      (p.x * (q.z * q.z)) (p.y * q.z * (q.z * q.z)) ((p.z * q.z) * z)
      (q.x * ((p.z * z) * (p.z * z)) - p.x * (q.z * q.z))
      (q.y * (p.z * z) * ((p.z * z) * (p.z * z)) - p.y * q.z * (q.z * q.z)) :=
  (congrArg (restoreZ z) (@addFixed_eq_addWeighted z p q hp hq)).trans
    (addWeighted_restore z p _ _ _ _ _)

private theorem addFixed_spec_of_z_ne_zero
    {p q : Coordinates} {P Q : curve.Point} {z : Montgomery}
    (hz : z ≠ 0) (hpz : p.z ≠ 0) (hqz : q.z ≠ 0)
    (hp : Represents (restoreZ z p) P) (hq : Represents q Q) :
    Represents (restoreZ z (addFixed z p q false)) (P + Q) := by
  let qz2 := q.z * q.z
  let dp := restoreZ z p
  let az := p.z * z
  let ax := p.x * qz2
  let ay := p.y * q.z * qz2
  let d := (p.z * q.z) * z
  let h := q.x * (az * az) - ax
  let r := q.y * az * (az * az) - ay
  let axb := dp.x * qz2
  let ayb := dp.y * q.z * qz2
  let db := dp.z * q.z
  let hb := q.x * (dp.z * dp.z) - axb
  let rb := q.y * dp.z * (dp.z * dp.z) - ayb
  have hpz' : dp.z ≠ 0 := mt (restore_zero_iff p hz).1 hpz
  have hx : zValue axb = zValue ax * (1 : F)^2 := by
    simp only [axb, ax, dp, restoreZ, one_pow, mul_one]
  have hy : zValue ayb = zValue ay * (1 : F)^3 := by
    simp only [ayb, ay, dp, restoreZ, one_pow, mul_one]
  have hd : zValue db = zValue d * (1 : F) := by
    simp only [db, d, dp, restoreZ, zValue_mul, mul_one]
    ring
  have hh : zValue hb = zValue h * (1 : F)^2 := by
    simp only [hb, h, axb, ax, dp, az, restoreZ, one_pow, mul_one]
  have hr : zValue rb = zValue r * (1 : F)^3 := by
    simp only [rb, r, ayb, ay, dp, az, restoreZ, one_pow, mul_one]
  exact @addShared_compat dp _ _ (P + Q) 1 ax ay d h r axb ayb db hb rb
    (restore_fixed_weighted_eq hpz hqz)
    (@coords_add_eq_addWeighted dp q hpz' hqz) one_ne_zero hx hy hd hh hr (hp.add hq)

private theorem addFixed_spec {z : Montgomery} {p q : Coordinates} {P Q : curve.Point}
    (hz : z ≠ 0) (hp : Represents (restoreZ z p) P) (hq : Represents q Q) (neg : Bool) :
    Represents (restoreZ z (addFixed z p q neg)) (P + if neg then -Q else Q) := by
  rw [sign_fixed_eq]
  let qs := signedPoint neg q
  have hqs : Represents qs (if neg then -Q else Q) := by
    cases neg
    · exact hq
    · obtain ⟨ha, he⟩ := negate_spec hq.1
      exact ⟨ha, he.trans (congrArg Neg.neg hq.2)⟩
  change Represents (restoreZ z (addFixed z p qs false)) _
  by_cases hpz : p.z = 0
  · have hP : P = 0 := hp.2.symm.trans (groupValue_of_z_zero ((restore_zero_iff p hz).2 hpz))
    rw [hP, zero_add]
    simp only [addFixed, zeroElement_eq_true, Bool.false_eq_true, ↓reduceIte, ite_eq_left hpz]
    have he : (⟨qs.x, qs.y, qs.z⟩ : Coordinates) = qs := by cases qs; rfl
    rw [he]
    exact restore_scaleNumerators hqs hz
  · by_cases hqz : qs.z = 0
    · have hQ := hqs.2.symm.trans (groupValue_of_z_zero hqz)
      rw [hQ, add_zero]
      have he : addFixed z p qs false = p := by
        simp only [addFixed, zeroElement_eq_true, ite_eq_right hpz, ite_eq_left hqz]
      rw [he]
      exact hp
    · exact addFixed_spec_of_z_ne_zero hz hpz hqz hp hqs

end

section
attribute [local irreducible] Montgomery.mul Montgomery.sub
  Montgomery.add Montgomery.square Montgomery.halve
  Montgomery.productDiff Montgomery.productSubSquare

private theorem restore_scale_swap (z f : Montgomery) (p : Coordinates) :
    restoreZ (f * z) (scaleNumerators f p) = restoreZ f (scaleNumerators f (restoreZ z p)) := by
  cases p with
  | mk x y w =>
    let f2 := Montgomery.square f
    change (⟨x * f2, y * f2 * f, w * (f * z)⟩ : Coordinates) =
      ⟨x * f2, y * f2 * f, (w * z) * f⟩
    apply congrArg (Coords.mk (x * f2) (y * f2 * f))
    apply zValue_injective
    calc
      _ = zValue w * zValue (f * z) := zValue_mul _ _
      _ = zValue w * (zValue f * zValue z) := congrArg (zValue w * ·) (zValue_mul f z)
      _ = (zValue w * zValue z) * zValue f := by rw [mul_comm (zValue f), mul_assoc]
      _ = zValue (w * z) * zValue f := congrArg (· * zValue f) (zValue_mul w z).symm
      _ = _ := (zValue_mul _ _).symm

private theorem coAdd_x_coordinate (a b c : Montgomery) :
    c - (a+b) - a = c - b - (a+a) := by
  apply zValue_injective
  simp only [zValue_add, zValue_sub]
  ring

private theorem coAdd_retained_x (a b : Montgomery) :
    let h := b - a
    let h2 := Montgomery.square h
    zValue (a*h2 + h*h2) = zValue h ^ 2 * zValue b := by
  dsimp only
  simp only [Montgomery.square_eq_mul, zValue_add, zValue_mul, zValue_sub]
  ring

private theorem coAdd_retained_y (y h : Montgomery) :
    zValue (y*(h*Montgomery.square h)) = zValue h ^ 3 * zValue y := by
  simp only [Montgomery.square_eq_mul, zValue_mul]
  ring

private theorem coAdd_sum_eq (px py qx qy z : Montgomery) (hh : qx-px ≠ 0) :
    let p : Coordinates := ⟨px, py, 1⟩
    let q : Coordinates := ⟨qx, qy, 1⟩
    restoreZ ((coAdd p q).2.2*z) (coAdd p q).1 = restoreZ z (addCommon p qx qy) := by
  let p : Coordinates := ⟨px, py, 1⟩
  let q : Coordinates := ⟨qx, qy, 1⟩
  let h := qx-px
  let r := qy-py
  let h2 := Montgomery.square h
  let h3 := h*h2
  let v := px*h2
  let x' := Montgomery.square r - (v+h3) - v
  let x := Montgomery.square r - h3 - (v+v)
  have hd : addCommon p qx qy = addFromDifferences px py 1 h r := by
    dsimp only [addCommon, zeroElement_eq_true, p, Coords.x, Coords.y, Coords.z]
    simp only [zeroElement_eq_true, ite_eq_right montgomery_one_ne_zero,
      Montgomery.square_eq_mul,
      montgomery_mul_one, h, r, ite_eq_right hh]
  change restoreZ ((coAdd p q).2.2*z) (coAdd p q).1 = restoreZ z (addCommon p qx qy)
  rw [hd]
  change (⟨x', r*(v-x') - py*h3, (1 : Montgomery)*(h*z)⟩ : Coordinates) =
    ⟨x, Montgomery.productDiff r (v-x) py h3, ((1 : Montgomery)*h)*z⟩
  have hx : x' = x := coAdd_x_coordinate v h3 (Montgomery.square r)
  rw [Montgomery.productDiff_eq, hx, montgomery_one_mul, montgomery_one_mul]

private theorem coAdd_spec
    {z : Montgomery} {p q : Coordinates} {P Q : curve.Point}
    (hz : z ≠ 0) (hpz : p.z = 1) (hqz : q.z = 1)
    (hp : Represents (restoreZ z p) P) (hq : Represents (restoreZ z q) Q)
    (hh : (coAdd p q).2.2 ≠ 0) :
    let out := coAdd p q
    Represents (restoreZ (out.2.2 * z) out.1) (P + Q) ∧
      Represents (restoreZ (out.2.2 * z) out.2.1) Q := by
  cases p with
  | mk px py pz =>
    cases q with
    | mk qx qy qz =>
      change pz = 1 at hpz
      change qz = 1 at hqz
      subst pz
      subst qz
      let p : Coordinates := ⟨px, py, 1⟩
      let q : Coordinates := ⟨qx, qy, 1⟩
      let h := qx-px
      let q' := restoreZ ((coAdd p q).2.2 * z) (coAdd p q).2.1
      have hh0 : h ≠ 0 := hh
      have hx : zValue q'.x = zValue h ^ 2 * zValue (restoreZ z q).x :=
        coAdd_retained_x px qx
      have hy : zValue q'.y = zValue h ^ 3 * zValue (restoreZ z q).y :=
        coAdd_retained_y qy h
      have hz' : zValue q'.z = zValue h * zValue (restoreZ z q).z := by
        change zValue ((1 : Montgomery)*(h*z)) = zValue h * zValue ((1 : Montgomery)*z)
        simp only [montgomery_one_mul, zValue_mul]
      change Represents (restoreZ ((coAdd p q).2.2*z) (coAdd p q).1) (P+Q) ∧ Represents q' Q
      constructor
      · rw [coAdd_sum_eq px py qx qy z hh0]
        exact @addCommon_spec p q P Q z hz rfl hp hq
      · exact @scale_spec (restoreZ z q) q' Q (zValue h) hq (zValue_ne_zero hh0) hx hy hz'

private theorem coAdd_unit_first (p q : Coordinates) : (coAdd p q).1.z = 1 := rfl

private theorem coAdd_unit_second (p q : Coordinates) : (coAdd p q).2.1.z = 1 := rfl

private theorem table_factors_ne_zero {a b : Montgomery} (h : a * b ≠ 0) :
    a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha
    apply h
    apply zValue_injective
    rw [zValue_mul, ha, zValue_zero, zero_mul]
  · intro hb
    apply h
    apply zValue_injective
    rw [zValue_mul, hb, zValue_zero, mul_zero]

private theorem table_mul_ne_zero {a b : Montgomery} (ha : a ≠ 0) (hb : b ≠ 0) :
    a*b ≠ 0 := by
  intro hz
  have h := congrArg zValue hz
  rw [zValue_mul, zValue_zero] at h
  exact mul_ne_zero (zValue_ne_zero ha) (zValue_ne_zero hb) h

private theorem collectOdd_prepend_spec
    {d z : Montgomery} {p entry : Coordinates} {P : curve.Point}
    (hd : d ≠ 0) (hpz : p.z = 1) (hp : Represents (restoreZ z p) P)
    (he : scaleNumerators d p = entry) :
    entry.z = 1 ∧ Represents (restoreZ (d*z) entry) P := by
  cases p with
  | mk px py pz =>
    let p : Coordinates := ⟨px, py, pz⟩
    have hz : (scaleNumerators d p).z = p.z := rfl
    have hez : entry.z = 1 := ((congrArg Coords.z he.symm).trans hz).trans hpz
    have hcoords : restoreZ (d*z) entry = restoreZ d (scaleNumerators d (restoreZ z p)) :=
      (congrArg (restoreZ (d*z)) he.symm).trans (restore_scale_swap z d p)
    have hs : Represents (restoreZ d (scaleNumerators d (restoreZ z p))) P :=
      @restore_scaleNumerators (restoreZ z p) P hp d hd
    exact ⟨hez, Eq.mpr (congrArg (fun q => Represents q P) hcoords) hs⟩

private theorem restore_unit_z (p : Coordinates) : restoreZ p.z {p with z := 1} = p := by
  cases p
  simp only [restoreZ, montgomery_one_mul]

private theorem commonTable_seed_first
    {p : Coordinates} {P : curve.Point} (hpz : p.z = 1) (hp : Represents p P)
    {z : Montgomery} (hz : z ≠ 0) :
    Represents (restoreZ z { scaleNumerators z p with z := 1 }) P := by
  cases p with
  | mk x y w =>
    change w = 1 at hpz
    subst w
    exact @restore_scaleNumerators ⟨x, y, 1⟩ P hp z hz

private theorem commonTable_seed_second {p : Coordinates} {P : curve.Point}
    (hp : Represents p P) : Represents (restoreZ p.z {p with z := 1}) P := by
  rw [restore_unit_z]
  exact hp

end

/-- Two on-curve Jacobian forms represent the same group point. -/
private abbrev PointAgreement (p q : Coordinates) : Prop :=
  OnCurve p ∧ OnCurve q ∧ groupValue p = groupValue q

private theorem PointAgreement.of_represents {p q : Coordinates} {P : curve.Point}
    (hp : Represents p P) (hq : Represents q P) : PointAgreement p q :=
  ⟨hp.1, hq.1, hp.2.trans hq.2.symm⟩

private theorem PointAgreement.double {p q : Coordinates} (h : PointAgreement p q) :
    PointAgreement (double p) (double q) := by
  have hp := fastDouble_spec h.1
  have hq := fastDouble_spec h.2.1
  exact ⟨hp.1, hq.1, by rw [hp.2, hq.2, h.2.2]⟩

private theorem selected_signed_onCurve {p : Coordinates} (hp : OnCurve p)
    (phi neg : Bool) : OnCurve (signedPoint neg (selectedPoint phi p)) := by
  have he : OnCurve (selectedPoint phi p) := by
    cases phi
    · exact hp
    · exact (endomorphism_spec hp).1
  cases neg
  · exact he
  · exact (negate_spec he).1

private theorem restoreZ_selected_signed (z : Montgomery) (p : Coordinates)
    (phi neg : Bool) :
    restoreZ z (signedPoint neg (selectedPoint phi p)) =
      signedPoint neg (selectedPoint phi (restoreZ z p)) := by
  cases p
  cases phi <;> cases neg <;>
    simp only [restoreZ, signedPoint, selectedPoint, endomorphism, scaleX, negate,
      Bool.false_eq_true, ↓reduceIte]

private theorem selected_signed_z (p : Coordinates) (phi neg : Bool) :
    (signedPoint neg (selectedPoint phi p)).z = p.z := by
  cases p
  cases phi <;> cases neg <;>
    simp only [signedPoint, selectedPoint, endomorphism, scaleX, negate,
      Bool.false_eq_true, ↓reduceIte]

private theorem signedPoint_represents (neg : Bool) {v : Coordinates} (hv : OnCurve v) :
    Represents (signedPoint neg v) (if neg then -groupValue v else groupValue v) := by
  cases neg
  · simpa only [signedPoint, Bool.false_eq_true, ↓reduceIte] using
      (show Represents v (groupValue v) from ⟨hv, rfl⟩)
  · simpa only [signedPoint, ↓reduceIte] using negate_spec hv

private theorem addGenerator_eq_signedPoint (p q : Coordinates) (neg : Bool) :
    addGenerator p q neg = Coords.add 0 p (signedPoint neg q) := by
  simpa only [signedPoint] using addGenerator_eq p q neg

private theorem addPackedFixed_agrees
    {z : Montgomery} (hz : z ≠ 0) (window : Window)
    {t : Vector Coordinates window.entries}
    (ht : ∀ i : Fin window.entries, OnCurve t[i.val])
    {p q : Coordinates} (hp : PointAgreement (restoreZ z p) q) (digit : UInt64) :
    PointAgreement (restoreZ z (addPackedFixed z p window t digit))
      (addPacked q window t digit) := by
  by_cases hd : digit = 0
  · simpa only [addPackedFixed, addPacked, beq_iff_eq, hd, ↓reduceIte] using hp
  · let i := packedIndex window digit
    let neg : Bool := digit >= window.pivot
    let v := t[i.val]
    have hv : Represents v (groupValue v) := ⟨ht i, rfl⟩
    have hq : Represents q (groupValue q) := ⟨hp.2.1, rfl⟩
    have ho := @addFixed_spec z p v (groupValue q) (groupValue v)
      hz ⟨hp.1, hp.2.2⟩ hv neg
    have hr := hq.add (signedPoint_represents neg hv.1)
    simp only [addPackedFixed, addPacked, beq_iff_eq, hd, ↓reduceIte, addGenerator_eq_signedPoint]
    exact PointAgreement.of_represents ho hr

private theorem doubleTwice_eq (p : Coordinates) : doubleTwice p = double (double p) := rfl

private theorem shiftWords_nat (lo hi : UInt64) :
    ((lo >>> 1) + (hi <<< 63)).toNat = lo.toNat / 2 + hi.toNat % 2 * 2^63 :=
  word_half_lo ⟨lo, hi⟩

private theorem shiftHigh_two (hi : UInt64) : (hi >>> 1) >>> 1 = hi >>> 2 := by
  apply UInt64.toNat_inj.mp
  rw [word_shift_right, word_shift_right, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  change hi.toNat / 2 / 2 = hi.toNat / 4
  omega

private theorem shiftWords_two (lo hi : UInt64) :
    (((lo >>> 1) + (hi <<< 63)) >>> 1) + ((hi >>> 1) <<< 63) =
      (lo >>> 2) + (hi <<< 62) := by
  apply UInt64.toNat_inj.mp
  rw [shiftWords_nat, shiftWords_nat, word_shift_right, UInt64.toNat_add,
    UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (lo.toNat / 2 + hi.toNat % 2 * 2^63) / 2 + hi.toNat / 2 % 2 * 2^63 =
    (lo.toNat / 4 + hi.toNat * 2^62 % 2^64) % 2^64
  have hl := UInt64.toNat_lt_size lo
  change lo.toNat < 2^64 at hl
  have hh : hi.toNat * 2^62 % 2^64 = hi.toNat % 4 * 2^62 := by omega
  have hlt : lo.toNat / 4 + hi.toNat % 4 * 2^62 < 2^64 := by omega
  rw [hh, Nat.mod_eq_of_lt hlt]
  have hsplit : (lo.toNat / 2 + hi.toNat % 2 * 2^63) / 2 =
      lo.toNat / 4 + hi.toNat % 2 * 2^62 := by
    rw [show hi.toNat % 2 * 2^63 = hi.toNat % 2 * 2^62 * 2 by omega,
      Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
    omega
  rw [hsplit]
  omega

private theorem packedLowTwoZero (al ah bl bh cl ch dl dh : UInt64)
    (h : ((al ||| bl ||| cl ||| dl) &&& 3) == 0) :
    (((al ||| bl ||| cl ||| dl) &&& 1) == 0) ∧
      (((((al >>> 1) + (ah <<< 63)) ||| ((bl >>> 1) + (bh <<< 63)) |||
        ((cl >>> 1) + (ch <<< 63)) ||| ((dl >>> 1) + (dh <<< 63))) &&& 1) == 0) := by
  have low (lo hi : UInt64) (hz : lo &&& 3 = 0) :
      lo &&& 1 = 0 ∧ ((lo >>> 1) + (hi <<< 63)) &&& 1 = 0 := by
    have hmod := UInt64.toNat_inj.mpr hz
    rw [UInt64.toNat_and] at hmod
    change lo.toNat &&& (2^2 - 1) = 0 at hmod
    rw [Nat.and_two_pow_sub_one_eq_mod] at hmod
    simp only [← UInt64.toNat_inj, UInt64.toNat_and]
    change lo.toNat &&& (2^1 - 1) = 0 ∧
      ((lo >>> 1) + (hi <<< 63)).toNat &&& (2^1 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, shiftWords_nat]
    omega
  simp only [beq_iff_eq, and_distrib, UInt64.or_eq_zero_iff] at h ⊢
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  have ha := low al ah ha
  have hb := low bl bh hb
  have hc := low cl ch hc
  have hd := low dl dh hd
  exact ⟨⟨⟨⟨ha.1, hb.1⟩, hc.1⟩, hd.1⟩, ⟨⟨⟨ha.2, hb.2⟩, hc.2⟩, hd.2⟩⟩

private theorem component_nsmul (w : WordPair × Bool) (P : curve.Point) :
    w.1.toNat • (if w.2 then -P else P) = componentValue w • P := by
  obtain ⟨words, sign⟩ := w
  cases sign <;> simp [componentValue, natCast_zsmul, neg_nsmul]

private theorem wordPair_bound (w : WordPair) : w.toNat ≤ 2^128 := by
  have hlo := w.lo.toNat_lt_size
  have hhi := w.hi.toNat_lt_size
  change w.lo.toNat < 2^64 at hlo
  change w.hi.toNat < 2^64 at hhi
  change w.lo.toNat + w.hi.toNat * 2^64 ≤ 2^128
  omega

private theorem raw_fixed_words (l : Montgomery.Raw) :
    (⟨l.w0,l.w1⟩ : WordPair).toNat = l.val % 2^128 ∧
      (⟨l.w2,l.w3⟩ : WordPair).toNat = l.val / 2^128 := by
  have h0 := l.w0.toNat_lt_size
  have h1 := l.w1.toNat_lt_size
  have h2 := l.w2.toNat_lt_size
  have h3 := l.w3.toNat_lt_size
  change l.w0.toNat < 2^64 at h0
  change l.w1.toNat < 2^64 at h1
  change l.w2.toNat < 2^64 at h2
  change l.w3.toNat < 2^64 at h3
  simp only [WordPair.toNat, Montgomery.Raw.val, Montgomery.Raw.words,
    Montgomery.lowValue, Montgomery.wordRadix]
  omega

private noncomputable def signedValue (w : WordPair) : Int :=
  (w.lo.toNat : Int) + w.hi.toInt64.toInt * 2^64

private theorem joint_word_shift_right (x : UInt64) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem joint_word_shift_left63 (x : UInt64) :
    (x <<< 63).toNat = x.toNat % 2 * 2^63 := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
  change x.toNat * 2^63 % 2^64 = x.toNat % 2 * 2^63
  omega

private theorem joint_word_half_lo (w : WordPair) :
    ((w.lo >>> 1) + (w.hi <<< 63)).toNat = w.lo.toNat / 2 + w.hi.toNat % 2 * 2^63 := by
  rw [UInt64.toNat_add, joint_word_shift_right, joint_word_shift_left63]
  have h := UInt64.toNat_lt_size w.lo
  change w.lo.toNat < 2^64 at h
  apply Nat.mod_eq_of_lt
  omega

private theorem arithmeticShiftRight_int (h : UInt64) :
    ((h.toInt64 >>> 1).toUInt64.toInt64).toInt = h.toInt64.toInt / 2 := by
  simp only [Int64.toInt64_toUInt64]
  change (h.toBitVec.sshiftRight 1).toInt = h.toBitVec.toInt / 2
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  rfl

private theorem int64_word_eq_cond (w : UInt64) :
    w.toInt64.toInt = if w.toNat < 2^63 then (w.toNat : Int) else (w.toNat : Int) - 2^64 := by
  change w.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : w.toNat < 2^63
  · have h' : 2 * w.toBitVec.toNat < 2^64 := by exact_mod_cast (show 2 * w.toNat < 2^64 by omega)
    rw [ite_eq_left h, ite_eq_left h']
    rfl
  · have h' : ¬ 2 * w.toBitVec.toNat < 2^64 := by
      exact_mod_cast (show ¬ 2 * w.toNat < 2^64 by omega)
    rw [ite_eq_right h, ite_eq_right h']
    rfl

private theorem signedHalf_eq (lo hi : UInt64) :
    signedValue (signedHalf lo hi) = signedValue ⟨lo, hi⟩ / 2 := by
  unfold signedValue signedHalf
  dsimp only
  rw [arithmeticShiftRight_int, show ((lo >>> 1) + (hi <<< 63)).toNat =
      lo.toNat / 2 + hi.toNat % 2 * 2^63 from joint_word_half_lo ⟨lo, hi⟩]
  rw [int64_word_eq_cond]
  split <;> omega

private theorem highSub_toNat (hi digit : UInt64) (borrow : Bool) :
    (hi + (digit >>> 63) - borrow.toUInt64).toNat =
      (2^64 - (if borrow then 1 else 0) + (hi.toNat + digit.toNat / 2^63) % 2^64) % 2^64 := by
  rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  change (2^64 - borrow.toUInt64.toNat +
    (hi.toNat + digit.toNat / 2^63) % 2^64) % 2^64 = _
  cases borrow <;> rfl

private theorem signedWord_mod (w : UInt64) :
    w.toInt64.toInt % (2^64 : Int) = w.toNat := by
  have hw : w.toNat < 2^64 := w.toNat_lt_size
  rw [int64_word_eq_cond]
  split <;> omega

private theorem signedSub_eq (lo hi digit : UInt64)
    (bound : -(2^127 : Int) ≤ signedValue ⟨lo, hi⟩ - digit.toInt64.toInt ∧
      signedValue ⟨lo, hi⟩ - digit.toInt64.toInt < 2^127) :
    let l := lo - digit
    let h := hi + (digit >>> 63) - (decide (l > lo)).toUInt64
    signedValue ⟨l, h⟩ = signedValue ⟨lo, hi⟩ - digit.toInt64.toInt := by
  let l := lo - digit
  let b : Int := if lo.toNat < digit.toNat then 1 else 0
  let n : Int := if digit.toNat < 2^63 then 0 else 1
  let h := hi + (digit >>> 63) - (decide (l > lo)).toUInt64
  let target := hi.toInt64.toInt + n - b
  have hlo : lo.toNat < 2^64 := lo.toNat_lt_size
  have hhi : hi.toNat < 2^64 := hi.toNat_lt_size
  have hdi : digit.toNat < 2^64 := digit.toNat_lt_size
  have hlt : l.toNat < 2^64 := l.toNat_lt_size
  have hborrow : decide (l > lo) = decide (lo.toNat < digit.toNat) := by
    rw [decide_eq_decide]
    change lo < lo - digit ↔ _
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub]
    omega
  have hl : (l.toNat : Int) = (lo.toNat : Int) - digit.toNat + b * 2^64 := by
    simp only [l, b, UInt64.toNat_sub]
    split <;> omega
  have hn : digit.toInt64.toInt = digit.toNat - n * 2^64 := by
    rw [int64_word_eq_cond]
    unfold n
    split <;> omega
  have htarget : -(2^63 : Int) ≤ target ∧ target < 2^63 := by
    simp only [signedValue] at bound
    unfold target
    omega
  have hmod : h.toInt64.toInt % (2^64 : Int) = target % (2^64 : Int) := by
    rw [signedWord_mod]
    simp only [h, hborrow, highSub_toNat, decide_eq_true_eq, target]
    have hhiMod := signedWord_mod hi
    unfold b n
    by_cases hb : lo.toNat < digit.toNat <;> by_cases hd : digit.toNat < 2^63 <;>
      simp only [hb, hd, ite_true, ite_false] <;> omega
  have hactual : h.toInt64.toInt = target := by
    have hmin := h.toInt64.le_toInt
    have hmax := h.toInt64.toInt_lt
    change -(2^63 : Int) ≤ h.toInt64.toInt at hmin
    change h.toInt64.toInt < 2^63 at hmax
    omega
  change signedValue ⟨l, h⟩ = _
  simp only [signedValue, hactual]
  unfold target
  omega

private theorem signedHalfAfter_eq (lo hi digit : UInt64)
    (bound : -(2^127 : Int) ≤ signedValue ⟨lo, hi⟩ - digit.toInt64.toInt ∧
      signedValue ⟨lo, hi⟩ - digit.toInt64.toInt < 2^127) :
    signedValue (signedHalfAfter lo hi digit) =
      (signedValue ⟨lo, hi⟩ - digit.toInt64.toInt) / 2 := by
  change signedValue (signedHalf (lo-digit)
      (hi+(digit>>>63)-(decide (lo-digit>lo)).toUInt64)) = _
  rw [signedHalf_eq, signedSub_eq lo hi digit bound]

private noncomputable def jointDigitIndex (a b : Int) : Fin 64 :=
  ⟨(a % 8).toNat + 8 * (b % 8).toNat, by
    have ha := Int.emod_lt_of_pos a (by decide : (0 : Int) < 8)
    have hb := Int.emod_lt_of_pos b (by decide : (0 : Int) < 8)
    omega⟩

private noncomputable def jointDigit (a b : Int) : UInt64 := jointDigits[(jointDigitIndex a b).val].toUInt64

private noncomputable def jointDecoded (digit : UInt64) : Int × Int :=
  if digit == 0 then (0, 0)
  else (((digit &&& 63) - 32).toInt64.toInt, (((digit >>> 6) &&& 63) - 32).toInt64.toInt)

private noncomputable def jointStep (s : Int × Int) : Int × Int :=
  let d := jointDecoded (jointDigit s.1 s.2)
  ((s.1 - d.1) / 2, (s.2 - d.2) / 2)

private theorem decode_lut : ∀ i : Fin 64,
    let a : Int := (i.val % 8 : Nat)
    let b : Int := (i.val / 8 : Nat)
    let digit := jointDigits[i.val].toUInt64
    let d := jointDecoded digit
    (digit = 0 ↔ a % 2 = 0 ∧ b % 2 = 0) ∧
      (a - d.1) % 2 = 0 ∧ (b - d.2) % 2 = 0 ∧
      -5 ≤ d.1 ∧ d.1 ≤ 5 ∧ -5 ≤ d.2 ∧ d.2 ≤ 5 := by
  decide +kernel

private theorem jointDigit_valid (a b : Int) :
    let digit := jointDigit a b
    let d := jointDecoded digit
    (digit = 0 ↔ a % 2 = 0 ∧ b % 2 = 0) ∧
      (a - d.1) % 2 = 0 ∧ (b - d.2) % 2 = 0 ∧
      -5 ≤ d.1 ∧ d.1 ≤ 5 ∧ -5 ≤ d.2 ∧ d.2 ≤ 5 := by
  have ha : (a % 8).toNat < 8 := by omega
  have hb : (b % 8).toNat < 8 := by omega
  have hx : ((jointDigitIndex a b).val % 8 : Nat) = (a % 8).toNat := by
    change ((a % 8).toNat + 8 * (b % 8).toNat) % 8 = _
    omega
  have hy : ((jointDigitIndex a b).val / 8 : Nat) = (b % 8).toNat := by
    change ((a % 8).toNat + 8 * (b % 8).toNat) / 8 = _
    omega
  have h := decode_lut (jointDigitIndex a b)
  dsimp only at h ⊢
  rw [hx, hy, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))] at h
  unfold jointDigit
  have ha2 : a % 8 % 2 = a % 2 := by omega
  have hb2 : b % 8 % 2 = b % 2 := by omega
  rw [ha2, hb2] at h
  exact ⟨h.1, by omega, by omega, h.2.2.2⟩

private theorem word_mask_value (w : WordPair) (k : Nat) (hk : k ≤ 3) :
    ((w.lo &&& UInt64.ofNat (2^k-1)).toNat : Int) = signedValue w % (2^k : Nat) := by
  rw [UInt64.toNat_and, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    omega : (2 : Nat)^k-1 < 2^64)]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have he : (2^k : Nat) ∣ 2^64 := Nat.pow_dvd_pow _ (by omega)
  obtain ⟨r, hr⟩ := he
  have hm : (2^64 : Int) = (2^k : Nat) * (r : Int) := by exact_mod_cast hr
  simp only [signedValue, hm, mul_left_comm (w.hi.toInt64.toInt), Int.add_mul_emod_self_left]
  norm_cast

private theorem jointDigitIndex_words (al ah bl bh : UInt64) :
    (((al &&& (7 : UInt64)) + ((bl &&& (7 : UInt64)) <<< (3 : UInt64))).toNat % 64) =
      (jointDigitIndex (signedValue ⟨al, ah⟩) (signedValue ⟨bl, bh⟩)).val := by
  have ha := word_mask_value ⟨al, ah⟩ 3 (by decide)
  have hb := word_mask_value ⟨bl, bh⟩ 3 (by decide)
  change ((al &&& 7).toNat : Int) = signedValue ⟨al, ah⟩ % 8 at ha
  change ((bl &&& 7).toNat : Int) = signedValue ⟨bl, bh⟩ % 8 at hb
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (((al &&& 7).toNat + ((bl &&& 7).toNat * 8) % 2^64) % 2^64) % 64 =
     ((signedValue ⟨al, ah⟩ % 8).toNat + 8 * (signedValue ⟨bl, bh⟩ % 8).toNat)
  omega

private theorem low_bit_zero_iff (w : WordPair) :
    w.lo &&& 1 = 0 ↔ signedValue w % 2 = 0 := by
  have h := word_mask_value w 1 (by decide)
  change ((w.lo &&& 1).toNat : Int) = signedValue w % 2 at h
  rw [← UInt64.toNat_inj]
  change (w.lo &&& 1).toNat = 0 ↔ signedValue w % 2 = 0
  omega

private theorem joint_and_distrib (a b c : UInt64) : (a ||| b) &&& c = (a &&& c) ||| (b &&& c) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, UInt64.toNat_or, Nat.and_or_distrib_right]

private noncomputable def signedRange (a : Int) : Prop := -(2^127 : Int) + 8 ≤ a ∧ a < 2^127 - 8

private theorem recodeJoint_eq (a b : WordPair) (ha : signedRange (signedValue a))
    (hb : signedRange (signedValue b)) :
    let r := recodeJoint a.lo a.hi b.lo b.hi
    let s := (signedValue a, signedValue b)
    r.digit = jointDigit s.1 s.2 ∧
      (signedValue ⟨r.a0, r.a1⟩, signedValue ⟨r.b0, r.b1⟩) = jointStep s := by
  dsimp only
  have hl := jointDigit_valid (signedValue a) (signedValue b)
  dsimp only at hl
  have hz : ((a.lo ||| b.lo) &&& 1 == 0) ↔ signedValue a % 2 = 0 ∧ signedValue b % 2 = 0 := by
    simp only [beq_iff_eq, joint_and_distrib, UInt64.or_eq_zero_iff, low_bit_zero_iff]
  unfold recodeJoint
  split
  · rename_i he
    have hd := hl.1.mpr (hz.mp he)
    change 0 = jointDigit (signedValue a) (signedValue b) ∧
      (signedValue (signedHalf a.lo a.hi), signedValue (signedHalf b.lo b.hi)) =
        jointStep (signedValue a, signedValue b)
    simp only [hd, jointStep, jointDecoded, beq_self_eq_true, ↓reduceIte, sub_zero,
      signedHalf_eq, true_and]
  · rename_i he
    have hd : jointDigit (signedValue a) (signedValue b) ≠ 0 := fun h => he (hz.mpr (hl.1.mp h))
    let index := (((a.lo &&& (7 : UInt64)) + ((b.lo &&& (7 : UInt64)) <<< (3 : UInt64))).toNat % 64)
    let ix : Fin 64 := ⟨index, Nat.mod_lt _ (by decide)⟩
    have hdigit := congrArg (fun i : Fin 64 => jointDigits[i.val].toUInt64)
      (Fin.ext (jointDigitIndex_words a.lo a.hi b.lo b.hi) :
        ix = jointDigitIndex (signedValue a) (signedValue b))
    dsimp only at hdigit ⊢
    rw [hdigit]
    let d := jointDigit (signedValue a) (signedValue b)
    let da := (d &&& 63) - 32
    let db := ((d >>> 6) &&& 63) - 32
    change d = d ∧ (signedValue (signedHalfAfter a.lo a.hi da),
      signedValue (signedHalfAfter b.lo b.hi db)) = jointStep (signedValue a, signedValue b)
    have hd' : ¬ d == 0 := by simpa only [beq_iff_eq] using hd
    have hda : (jointDecoded d).1 = da.toInt64.toInt := by
      simp only [jointDecoded, ite_eq_right hd', da]
    have hdb : (jointDecoded d).2 = db.toInt64.toInt := by
      simp only [jointDecoded, ite_eq_right hd', db]
    rw [hda, hdb] at hl
    unfold signedRange at *
    have ha' : -(2^127 : Int) ≤ signedValue a - da.toInt64.toInt ∧
        signedValue a - da.toInt64.toInt < 2^127 := by omega
    have hb' : -(2^127 : Int) ≤ signedValue b - db.toInt64.toInt ∧
        signedValue b - db.toInt64.toInt < 2^127 := by omega
    refine ⟨rfl, ?_⟩
    change _ = ((signedValue a - (jointDecoded d).1) / 2,
      (signedValue b - (jointDecoded d).2) / 2)
    rw [hda, hdb, signedHalfAfter_eq _ _ _ ha', signedHalfAfter_eq _ _ _ hb']

private noncomputable def pairBound (m : Int) (s : Int × Int) : Prop :=
  -m ≤ s.1 ∧ s.1 ≤ m ∧ -m ≤ s.2 ∧ s.2 ≤ m

private theorem jointStep_add (s : Int × Int) :
    let d := jointDecoded (jointDigit s.1 s.2)
    2 * (jointStep s).1 + d.1 = s.1 ∧ 2 * (jointStep s).2 + d.2 = s.2 := by
  obtain ⟨a,b⟩ := s
  have h := jointDigit_valid a b
  dsimp only at h
  simp only [jointStep]
  exact ⟨by omega, by omega⟩

private theorem jointStep_bound (s : Int × Int) (m : Int) (hs : pairBound (2*m + 5) s) :
    pairBound (m+5) (jointStep s) := by
  obtain ⟨a,b⟩ := s
  have h := jointDigit_valid a b
  dsimp only at h
  simp only [jointStep, pairBound] at hs ⊢
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem jointStep_range {s : Int × Int} (ha : signedRange s.1) (hb : signedRange s.2) :
    signedRange (jointStep s).1 ∧ signedRange (jointStep s).2 := by
  have h := jointDigit_valid s.1 s.2
  simp only [jointStep, signedRange] at ha hb ⊢
  dsimp only at h
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

private noncomputable def jointN : Nat → (Int × Int) → Int × Int
  | 0, s => s
  | n+1, s => jointN n (jointStep s)

private theorem jointN_add (m n : Nat) (s : Int × Int) :
    jointN (m+n) s = jointN m (jointN n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    exact ih (jointStep s)

private theorem jointN_bound (s : Int × Int) (p n : Nat)
    (hs : pairBound (2^(p+n)+5) s) : pairBound (2^p+5) (jointN n s) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    apply ih
    have he : (2^(p+(n+1)) : Int) = 2*2^(p+n) := by
      rw [Nat.add_succ, pow_succ, mul_comm]
    rw [he] at hs
    exact jointStep_bound s _ hs

private theorem jointN_small : ∀ x y : Fin 13,
    jointN 5 ((x.val : Int)-6, (y.val : Int)-6) = (0,0) := by
  decide +kernel

private theorem jointN_132 (s : Int × Int) (ha : signedRange s.1) (hb : signedRange s.2) :
    jointN 132 s = (0,0) := by
  have hbnd : pairBound (2^(0+127)+5) s := by
    simp only [signedRange] at ha hb
    norm_num [pairBound]
    omega
  have h := jointN_bound s 0 127 hbnd
  let t := jointN 127 s
  change pairBound 6 t at h
  simp only [pairBound] at h
  let u : Fin 13 := ⟨(t.1+6).toNat, by omega⟩
  let v : Fin 13 := ⟨(t.2+6).toNat, by omega⟩
  have hv := jointN_small u v
  have he : ((u.val : Int)-6, (v.val : Int)-6) = t := by
    apply Prod.ext <;> simp only [u, v] <;> omega
  rw [he] at hv
  change jointN (5+127) s = (0,0)
  rw [jointN_add]
  exact hv

private theorem joint_even (s : Int × Int) (ha : s.1 % 2 = 0) (hb : s.2 % 2 = 0) :
    jointDigit s.1 s.2 = 0 ∧ jointStep s = (s.1 / 2, s.2 / 2) := by
  have hd := (jointDigit_valid s.1 s.2).1.mpr ⟨ha, hb⟩
  exact ⟨hd, by simp only [jointStep, hd, jointDecoded, beq_self_eq_true, ↓reduceIte, sub_zero]⟩

private theorem signedQuarter_eq (lo hi : UInt64) :
    signedValue ⟨(lo >>> 2) + (hi <<< 62), (hi.toInt64 >>> 2).toUInt64⟩ =
      signedValue ⟨lo, hi⟩ / 4 := by
  have hhigh : (hi.toInt64 >>> 2).toUInt64.toInt64.toInt = hi.toInt64.toInt / 4 := by
    simp only [Int64.toInt64_toUInt64]
    change (hi.toBitVec.sshiftRight 2).toInt = hi.toBitVec.toInt / 4
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    rfl
  have hlow := UInt64.toNat_lt_size lo
  have hleft : (hi <<< 62).toNat = hi.toNat % 4 * 2^62 := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    change hi.toNat * 2^62 % 2^64 = hi.toNat % 4 * 2^62
    omega
  have hright : (lo >>> 2).toNat = lo.toNat / 4 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  have hsum : lo.toNat / 4 + hi.toNat % 4 * 2^62 < 2^64 := by
    change lo.toNat < 2^64 at hlow
    omega
  simp only [signedValue, hhigh, UInt64.toNat_add, hleft, hright, Nat.mod_eq_of_lt hsum]
  rw [int64_word_eq_cond]
  split <;> omega

private theorem decode_lut_active : ∀ i : Fin 64,
    let a : Int := (i.val % 8 : Nat)
    let b : Int := (i.val / 8 : Nat)
    let digit := jointDigits[i.val].toUInt64
    let d := jointDecoded digit
    digit ≠ 0 → (a - d.1) % 4 = 0 ∧ (b - d.2) % 4 = 0 := by
  decide +kernel

private theorem jointDigit_active (a b : Int) (hd : jointDigit a b ≠ 0) :
    let d := jointDecoded (jointDigit a b)
    (a - d.1) % 4 = 0 ∧ (b - d.2) % 4 = 0 := by
  have hx : ((jointDigitIndex a b).val % 8 : Nat) = (a % 8).toNat := by
    change ((a % 8).toNat + 8 * (b % 8).toNat) % 8 = _
    omega
  have hy : ((jointDigitIndex a b).val / 8 : Nat) = (b % 8).toNat := by
    change ((a % 8).toNat + 8 * (b % 8).toNat) / 8 = _
    omega
  have h := decode_lut_active (jointDigitIndex a b) hd
  dsimp only at h ⊢
  rw [hx, hy, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))] at h
  unfold jointDigit
  exact ⟨by omega, by omega⟩

private theorem jointN_active (s : Int × Int) (hd : jointDigit s.1 s.2 ≠ 0) :
    let d := jointDecoded (jointDigit s.1 s.2)
    jointN 2 s = ((s.1 - d.1) / 4, (s.2 - d.2) / 4) := by
  dsimp only
  have hs := jointDigit_active s.1 s.2 hd
  let a := s.1 - (jointDecoded (jointDigit s.1 s.2)).1
  let b := s.2 - (jointDecoded (jointDigit s.1 s.2)).2
  change a % 4 = 0 ∧ b % 4 = 0 at hs
  have h := joint_even (a/2, b/2) (by dsimp only; omega) (by dsimp only; omega)
  change jointStep (a/2,b/2) = (a/4,b/4)
  rw [h.2]
  apply Prod.ext <;> dsimp only <;> omega

private theorem jointN_finish_step (m : Int) (n : Nat) (s : Int × Int)
    (hs : pairBound m s)
    (he : ∀ t, pairBound (m/2) t → jointN (n+1) t = (0,0))
    (hn : ∀ t, pairBound ((m+5)/4) t → jointN n t = (0,0)) :
    jointN (n+2) s = (0,0) := by
  by_cases hd : jointDigit s.1 s.2 = 0
  · have hpar := (jointDigit_valid s.1 s.2).1.mp hd
    have hhalf := (joint_even s hpar.1 hpar.2).2
    change jointN (n+1) (jointStep s) = _
    rw [hhalf]
    apply he
    simp only [pairBound] at hs ⊢
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rw [jointN_add, jointN_active s hd]
    apply hn
    have hmod := jointDigit_active s.1 s.2 hd
    have hr := (jointDigit_valid s.1 s.2).2.2.2
    simp only [pairBound] at hs ⊢
    exact ⟨by omega, by omega, by omega, by omega⟩

private theorem jointN_of_small (r k : Nat)
    (h : ∀ u v : Fin (2*r+1), jointN k ((u.val : Int)-r, (v.val : Int)-r) = (0,0))
    (s : Int × Int) (hs : pairBound r s) : jointN k s = (0,0) := by
  simp only [pairBound] at hs
  let u : Fin (2*r+1) := ⟨(s.1+r).toNat, by omega⟩
  let v : Fin (2*r+1) := ⟨(s.2+r).toNat, by omega⟩
  have hp := h u v
  have he : ((u.val : Int)-r, (v.val : Int)-r) = s := by
    apply Prod.ext <;> simp only [u, v] <;> omega
  rwa [he] at hp

private theorem jointN_three_small : ∀ u v : Fin 7,
    jointN 3 ((u.val : Int)-3, (v.val : Int)-3) = (0,0) := by decide +kernel

private theorem jointN_four_small : ∀ u v : Fin 15,
    jointN 4 ((u.val : Int)-7, (v.val : Int)-7) = (0,0) := by decide +kernel

private theorem pairBound_mono {l m : Int} {s : Int × Int} (h : l ≤ m) (hs : pairBound l s) :
    pairBound m s := by
  simp only [pairBound] at hs ⊢
  omega

private theorem jointN_five_of_ten (s : Int × Int) (hs : pairBound 10 s) :
    jointN 5 s = (0,0) :=
  jointN_finish_step 10 3 s hs
    (fun t ht => jointN_of_small 7 4 jointN_four_small t (pairBound_mono (by decide) ht))
    (jointN_of_small 3 3 jointN_three_small)

private theorem jointN_six_of_eighteen (s : Int × Int) (hs : pairBound 18 s) :
    jointN 6 s = (0,0) :=
  jointN_finish_step 18 4 s hs
    (fun t ht => jointN_five_of_ten t (pairBound_mono (by decide) ht))
    (fun t ht => jointN_of_small 7 4 jointN_four_small t (pairBound_mono (by decide) ht))

private theorem jointN_seven_of_thirty_seven (s : Int × Int) (hs : pairBound 37 s) :
    jointN 7 s = (0,0) :=
  jointN_finish_step 37 5 s hs
    jointN_six_of_eighteen (jointN_five_of_ten)

private theorem jointN_129 (s : Int × Int) (ha : signedRange s.1) (hb : signedRange s.2) :
    jointN 129 s = (0,0) := by
  have hbnd : pairBound (2^(5+122)+5) s := by
    simp only [signedRange] at ha hb
    norm_num [pairBound]
    omega
  have h := jointN_bound s 5 122 hbnd
  change jointN (7+122) s = (0,0)
  rw [jointN_add]
  exact jointN_seven_of_thirty_seven _ h

private noncomputable def jointBasis (i : Fin 6) : Int × Int :=
  (#v[(1,0),(2,1),(3,2),(3,1),(3,0),(3,-1)])[i.val]

private noncomputable def jointTurn (c : Int × Int) : Int × Int := (-c.2, c.1 - c.2)

private noncomputable def jointNeg (c : Int × Int) : Int × Int := (-c.1, -c.2)

private noncomputable def jointAdd (a b : Int × Int) : Int × Int := (a.1+b.1, a.2+b.2)

private noncomputable def jointAction (P : curve.Point) (c : Int × Int) : curve.Point :=
  c.1 • P + c.2 • (lambda.val • P)

private noncomputable def jointOriented (rotation : UInt64) (negative : Bool) (c : Int × Int) : Int × Int :=
  let d := if rotation == 0 then c else if rotation == 1 then jointTurn c
    else jointTurn (jointTurn c)
  if negative then jointNeg d else d

private theorem jointAction_add (P : curve.Point) (a b : Int × Int) :
    jointAction P (jointAdd a b) = jointAction P a + jointAction P b := by
  simp only [jointAction, jointAdd, add_zsmul]
  abel

private theorem jointAction_neg (P : curve.Point) (a : Int × Int) :
    jointAction P (jointNeg a) = -jointAction P a := by
  simp only [jointAction, jointNeg, neg_zsmul]
  abel

private theorem jointBeta_relation : β*β + β + 1 = 0 := by
  have hne : β ≠ 1 := by decide
  apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr hne)
  calc
    (β*β + β + 1) * (β-1) = β^3 - 1 := by ring
    _ = 0 := by rw [beta_cube, sub_self]

private theorem jointLambda_relation :
    let l : ZMod Fn.modulus := ((lambda.val : Int) : ZMod Fn.modulus)
    l*l = ((-1 : Int) : ZMod Fn.modulus) + ((-1 : Int) : ZMod Fn.modulus)*l := by
  decide +kernel

private theorem jointLambda_sq_smul (P : curve.Point) :
    (lambda.val : Int) • ((lambda.val : Int) • P) =
      (-1 : Int) • P + (-1 : Int) • ((lambda.val : Int) • P) := by
  let l := (lambda.val : Int)
  let R := ZMod Fn.modulus
  change l • (l • P) = (-1 : Int) • P + (-1 : Int) • (l • P)
  rw [← Int.cast_smul_eq_zsmul R l (l • P), ← Int.cast_smul_eq_zsmul R l P,
    ← Int.cast_smul_eq_zsmul R (-1) P, ← Int.cast_smul_eq_zsmul R (-1) ((l : R) • P),
    smul_smul, smul_smul]
  rw [← add_smul, jointLambda_relation]

private theorem jointAction_turn (P : curve.Point) (c : Int × Int) :
    lambda.val • jointAction P c = jointAction P (jointTurn c) := by
  let l := (lambda.val : Int)
  obtain ⟨a,b⟩ := c
  simp only [jointAction, jointTurn, ← natCast_zsmul]
  change l • (a • P + b • (l • P)) = (-b) • P + (a-b) • (l • P)
  rw [zsmul_add, smul_comm l a P, smul_comm l b (l • P), jointLambda_sq_smul]
  rw [zsmul_add, smul_smul b (-1) P, smul_smul b (-1) (l • P), mul_neg, mul_one]
  simp only [neg_zsmul, sub_zsmul]
  abel

private theorem jointZValue_ofFin (a : Fp) : zValue (Montgomery.ofFin a) = Fp.toZMod a :=
  (congrArg Jacobian.toZ (readOfFin a)).trans (coordinateToZ_eq a)

section
attribute [local irreducible] Montgomery.square Montgomery.mul
  Montgomery.add Montgomery.sub

private theorem ofFin_mul_assoc (a b : Fp) (c : Montgomery) :
    Montgomery.ofFin (a * b) * c =
      Montgomery.ofFin a * (Montgomery.ofFin b * c) := by
  apply zValue_injective
  simp only [zValue_mul, jointZValue_ofFin, map_mul, mul_assoc]

private theorem endomorphismSquared_eq (p : Coordinates) :
    endomorphismSquared p = endomorphism (endomorphism p) := by
  cases p with
  | mk x y z =>
    exact congrArg (fun u => (⟨u,y,z⟩ : Coordinates)) (ofFin_mul_assoc beta beta x)

end

private theorem restoreZ_endomorphism (z : Montgomery) (p : Coordinates) :
    restoreZ z (endomorphism p) = endomorphism (restoreZ z p) := by
  cases p
  rfl

private theorem restoreZ_negate (z : Montgomery) (p : Coordinates) :
    restoreZ z (negate p) = negate (restoreZ z p) := by
  cases p
  rfl

private theorem jointRep_turn {z : Montgomery} {p : Coordinates}
    {P : curve.Point} {c : Int × Int} (h : Represents (restoreZ z p) (jointAction P c)) :
    Represents (restoreZ z (endomorphism p)) (jointAction P (jointTurn c)) := by
  rw [restoreZ_endomorphism]
  have he := endomorphism_spec h.1
  exact ⟨he.1, by rw [he.2, h.2, jointAction_turn]⟩

private theorem jointRep_turnTwice {z : Montgomery} {p : Coordinates}
    {P : curve.Point} {c : Int × Int} (h : Represents (restoreZ z p) (jointAction P c)) :
    Represents (restoreZ z (endomorphismSquared p)) (jointAction P (jointTurn (jointTurn c))) := by
  rw [endomorphismSquared_eq]
  exact jointRep_turn (jointRep_turn h)

private theorem jointRep_neg {z : Montgomery} {p : Coordinates}
    {P : curve.Point} {c : Int × Int} (h : Represents (restoreZ z p) (jointAction P c)) :
    Represents (restoreZ z (negate p)) (jointAction P (jointNeg c)) := by
  rw [restoreZ_negate]
  have he := negate_spec h.1
  exact ⟨he.1, by rw [he.2, h.2, jointAction_neg]⟩

private theorem jointRep_coAdd {z : Montgomery} {p q : Coordinates}
    {P : curve.Point} {a b : Int × Int} (hz : z ≠ 0) (hpz : p.z = 1) (hqz : q.z = 1)
    (hp : Represents (restoreZ z p) (jointAction P a))
    (hq : Represents (restoreZ z q) (jointAction P b)) (hh : (coAdd p q).2.2 ≠ 0) :
    let out := coAdd p q
    Represents (restoreZ (out.2.2*z) out.1) (jointAction P (jointAdd a b)) ∧
    Represents (restoreZ (out.2.2*z) out.2.1) (jointAction P b) := by
  rw [jointAction_add]
  exact coAdd_spec hz hpz hqz hp hq hh

private theorem jointEntry_phi2X (p : Coordinates) :
    (JointEntry.ofCoords p).phi2X = (endomorphismSquared p).x := by
  apply zValue_injective
  change zValue (0 - (p.x + (endomorphism p).x)) = zValue (endomorphismSquared p).x
  simp only [endomorphism, endomorphismSquared, scaleX_x, zValue_sub, zValue_zero,
    zValue_add, zValue_mul, jointZValue_ofFin, map_mul]
  change 0 - (zValue p.x + β*zValue p.x) = β*β*zValue p.x
  apply sub_eq_zero.mp
  linear_combination -zValue p.x * jointBeta_relation

private noncomputable def jointEntryCoords (q : JointEntry) (rotation : UInt64) (negative : Bool) : Coordinates :=
  let x := if rotation == 0 then q.x else if rotation == 1 then q.phiX else q.phi2X
  let y := if negative then (0 : Montgomery) - q.y else q.y
  ⟨x, y, 1⟩

private noncomputable def jointPower (p : Coordinates) (rotation : UInt64) : Coordinates :=
  if rotation == 0 then p else if rotation == 1 then endomorphism p else endomorphismSquared p

private theorem jointEntryCoords_eq (p : Coordinates) (hp : p.z = 1)
    (r : UInt64) (n : Bool) :
    jointEntryCoords (JointEntry.ofCoords p) r n = signedPoint n (jointPower p r) := by
  rw [signedPoint_eq_fields]
  have h2 := jointEntry_phi2X p
  cases p with
  | mk px py pz =>
    change pz = 1 at hp
    subst pz
    by_cases h0 : r = 0
    · simp only [jointEntryCoords, jointPower, beq_iff_eq, h0, ↓reduceIte, JointEntry.ofCoords]
    · by_cases h1 : r = 1
      · have hone : (1 : UInt64) ≠ 0 := by decide
        simp only [jointEntryCoords, jointPower, beq_iff_eq, h1, hone, ↓reduceIte,
          JointEntry.ofCoords, endomorphism, scaleX]
      · have he :
            (JointEntry.ofCoords (⟨px, py, 1⟩ : Coordinates)).phi2X =
              (endomorphismSquared (⟨px, py, 1⟩ : Coordinates)).x := h2
        simp only [jointEntryCoords, jointPower, beq_iff_eq, h0, h1, ↓reduceIte, he]
        rfl

private theorem jointPower_represents {z : Montgomery} {p : Coordinates}
    {P : curve.Point} {c : Int × Int} (h : Represents (restoreZ z p) (jointAction P c))
    (r : UInt64) :
    Represents (restoreZ z (jointPower p r)) (jointAction P (jointOriented r false c)) := by
  by_cases h0 : r = 0
  · simpa only [jointPower, jointOriented, beq_iff_eq, h0, Bool.false_eq_true, ↓reduceIte] using h
  · by_cases h1 : r = 1
    · have hone : (1 : UInt64) ≠ 0 := by decide
      simpa only [jointPower, jointOriented, beq_iff_eq, h1, hone, Bool.false_eq_true, ↓reduceIte]
        using jointRep_turn h
    · simpa only [jointPower, jointOriented, beq_iff_eq, h0, h1, Bool.false_eq_true, ↓reduceIte]
        using jointRep_turnTwice h

private theorem jointEntry_represents {z : Montgomery} {p : Coordinates}
    {P : curve.Point} {c : Int × Int} (hp : p.z = 1)
    (h : Represents (restoreZ z p) (jointAction P c)) (r : UInt64) (n : Bool) :
    Represents (restoreZ z (jointEntryCoords (JointEntry.ofCoords p) r n))
      (jointAction P (jointOriented r n c)) := by
  rw [jointEntryCoords_eq p hp]
  cases n
  · simpa only [signedPoint, Bool.false_eq_true, ↓reduceIte] using jointPower_represents h r
  · have ho : jointNeg (jointOriented r false c) = jointOriented r true c := by
      simp only [jointOriented, Bool.false_eq_true, ↓reduceIte]
    rw [signedPoint, ite_eq_left rfl, ← ho]
    exact jointRep_neg (jointPower_represents h r)

private abbrev JointTableSpec (z : Montgomery) (table : Vector JointEntry 6)
    (P : curve.Point) : Prop :=
  ∀ (i : Fin 6) (r : UInt64) (n : Bool),
    Represents (restoreZ z (jointEntryCoords table[i.val] r n))
      (jointAction P (jointOriented r n (jointBasis i)))

private noncomputable def jointDescriptorIndex (d : UInt64) : Fin 6 :=
  ⟨((d >>> 12) &&& 31).toNat % 6, Nat.mod_lt _ (by decide)⟩

private noncomputable def jointDigitRotation (d : UInt64) : UInt64 := (d >>> 17) &&& 3

private noncomputable def jointDigitNegative (d : UInt64) : Bool := d &&& 524288 != 0

private noncomputable def jointDigitCoefficients (d : UInt64) : Int × Int :=
  if d == 0 then (0,0)
  else jointOriented (jointDigitRotation d) (jointDigitNegative d)
    (jointBasis (jointDescriptorIndex d))

private theorem addPackedJoint_represents {p : Coordinates} {P B : curve.Point}
    {z : Montgomery} {t : Vector JointEntry 6} (hz : z ≠ 0)
    (hp : Represents (restoreZ z p) P) (ht : JointTableSpec z t B) (d : UInt64) :
    Represents (restoreZ z (addPackedJoint p t d))
      (P + jointAction B (jointDigitCoefficients d)) := by
  by_cases hd : d = 0
  · simpa only [jointDigitCoefficients, addPackedJoint, beq_iff_eq, hd, ↓reduceIte,
      jointAction, zero_zsmul, add_zero] using hp
  · let i := jointDescriptorIndex d
    let r := jointDigitRotation d
    let n := jointDigitNegative d
    let q := jointEntryCoords t[i.val] r n
    have hq := ht i r n
    have ha : addPackedJoint p t d = addCommon p q.x q.y := by
      have hd' : ¬(d == 0) = true := fun h => hd (beq_iff_eq.mp h)
      have hflip (b : Bool) (y : Montgomery) :
          (if b then y else 0 - y) = (if !b then 0 - y else y) := by
        cases b <;> rfl
      simp only [addPackedJoint, ite_eq_right hd', q, jointEntryCoords, i, r, n,
        jointDescriptorIndex, jointDigitRotation, jointDigitNegative, bne, ← hflip]
    rw [ha]
    simp only [jointDigitCoefficients, beq_iff_eq, hd, ↓reduceIte]
    exact @addCommon_spec p q P _ z hz rfl hp hq


private theorem descriptor_coefficients_eq : ∀ i : Fin 64,
    jointDigitCoefficients jointDigits[i.val].toUInt64 =
      jointDecoded jointDigits[i.val].toUInt64 := by
  decide +kernel

section
attribute [local irreducible] coAdd scaleNumerators jointAction jointEntryCoords
  Montgomery.square Montgomery.mul Montgomery.add Montgomery.sub

private theorem commonJointTable_shape (p : Coordinates) :
  let p0 : Coordinates := {p with z := 1}
  let q0 := negate (endomorphismSquared p0)
  let s1 := coAdd p0 (q0)
  let p1 := s1.1
  let h1 := s1.2.2
  let q1 := s1.2.1
  let s2 := coAdd p1 (q1)
  let p2 := s2.1
  let h2 := s2.2.2
  let q2 := s2.2.1
  let s3 := coAdd p2 (endomorphismSquared q2)
  let p3 := s3.1
  let h3 := s3.2.2
  let q3 := s3.2.1
  let s4 := coAdd p3 (q3)
  let p4 := s4.1
  let h4 := s4.2.2
  let q4 := s4.2.1
  let s5 := coAdd p4 (q4)
  let p5 := s5.1
  let h5 := s5.2.2
  let z5 := h5
  let z4 := z5 * h4
  let z3 := z4 * h3
  let z2 := z3 * h2
  let z1 := z2 * h1
  commonJointTable p = (#v[
    JointEntry.ofCoords (scaleNumerators z1 p0),
    JointEntry.ofCoords (scaleNumerators z2 p1),
    JointEntry.ofCoords (scaleNumerators z3 p2),
    JointEntry.ofCoords (scaleNumerators z4 p3),
    JointEntry.ofCoords (scaleNumerators z5 p4),
    JointEntry.ofCoords p5], z1) := by
  dsimp only
  rw [commonJointTable]

private theorem commonJointTable_spec {p : Coordinates} {P : curve.Point}
    (hpz : p.z = 1) (hp : Represents p P) (hz : (commonJointTable p).2 ≠ 0) :
    JointTableSpec (commonJointTable p).2 (commonJointTable p).1 P := by
  let p0 : Coordinates := {p with z := 1}
  let q0 := negate (endomorphismSquared p0)
  let s1 := coAdd p0 (q0)
  let p1 := s1.1
  let h1 := s1.2.2
  let q1 := s1.2.1
  let s2 := coAdd p1 (q1)
  let p2 := s2.1
  let h2 := s2.2.2
  let q2 := s2.2.1
  let s3 := coAdd p2 (endomorphismSquared q2)
  let p3 := s3.1
  let h3 := s3.2.2
  let q3 := s3.2.1
  let s4 := coAdd p3 (q3)
  let p4 := s4.1
  let h4 := s4.2.2
  let q4 := s4.2.1
  let s5 := coAdd p4 (q4)
  let p5 := s5.1
  let h5 := s5.2.2
  let z5 := h5
  let z4 := z5 * h4
  let z3 := z4 * h3
  let z2 := z3 * h2
  let z1 := z2 * h1
  have hShape := commonJointTable_shape p
  dsimp only at hShape
  rw [hShape] at hz ⊢
  change z1 ≠ 0 at hz
  intro i r n
  obtain ⟨nz2, nh1⟩ : z2 ≠ 0 ∧ h1 ≠ 0 := table_factors_ne_zero hz
  obtain ⟨nz3, nh2⟩ : z3 ≠ 0 ∧ h2 ≠ 0 := table_factors_ne_zero nz2
  obtain ⟨nz4, nh3⟩ : z4 ≠ 0 ∧ h3 ≠ 0 := table_factors_ne_zero nz3
  obtain ⟨nz5, nh4⟩ : z5 ≠ 0 ∧ h4 ≠ 0 := table_factors_ne_zero nz4
  have nh5 : h5 ≠ 0 := nz5
  let u0 : Montgomery := 1
  have nu0 : u0 ≠ 0 := montgomery_one_ne_zero
  have hp0 : Represents (restoreZ u0 p0) (jointAction P (1, 0)) := by
    have he : restoreZ u0 p0 = p := by
      cases p with
      | mk x y z =>
        change z = 1 at hpz
        subst z
        change (⟨x, y, (1 : Montgomery) * 1⟩ : Coordinates) = ⟨x, y, 1⟩
        rw [montgomery_mul_one]
    rw [he]
    simpa only [jointAction, one_zsmul, zero_zsmul, add_zero] using hp
  have hq0 : Represents (restoreZ u0 q0) (jointAction P (1, 1)) :=
    jointRep_neg (jointRep_turnTwice hp0)
  have zp0 : p0.z = 1 := rfl
  have zq0 : q0.z = 1 := rfl
  let u1 := h1 * u0
  have zp1 : p1.z = 1 := coAdd_unit_first _ _
  have hstep1 := @jointRep_coAdd u0 p0 (q0) P (1, 0) (1, 1)
    nu0 zp0 zq0 hp0 hq0 nh1
  have hp1 : Represents (restoreZ u1 p1) (jointAction P (2, 1)) := hstep1.1
  have nu1 : u1 ≠ 0 := table_mul_ne_zero nh1 nu0
  have zq1 : q1.z = 1 := coAdd_unit_second _ _
  have hq1 : Represents (restoreZ u1 q1) (jointAction P (1, 1)) := hstep1.2
  let u2 := h2 * u1
  have zp2 : p2.z = 1 := coAdd_unit_first _ _
  have hstep2 := @jointRep_coAdd u1 p1 (q1) P (2, 1) (1, 1)
    nu1 zp1 zq1 hp1 hq1 nh2
  have hp2 : Represents (restoreZ u2 p2) (jointAction P (3, 2)) := hstep2.1
  have nu2 : u2 ≠ 0 := table_mul_ne_zero nh2 nu1
  have zq2 : q2.z = 1 := coAdd_unit_second _ _
  have hq2 : Represents (restoreZ u2 q2) (jointAction P (1, 1)) := hstep2.2
  have hqT : Represents (restoreZ u2 (endomorphismSquared q2)) (jointAction P (0, -1)) :=
    jointRep_turnTwice hq2
  have zqT : (endomorphismSquared q2).z = 1 := zq2
  let u3 := h3 * u2
  have zp3 : p3.z = 1 := coAdd_unit_first _ _
  have hstep3 := @jointRep_coAdd u2 p2 (endomorphismSquared q2) P (3, 2) (0, -1)
    nu2 zp2 zqT hp2 hqT nh3
  have hp3 : Represents (restoreZ u3 p3) (jointAction P (3, 1)) := hstep3.1
  have nu3 : u3 ≠ 0 := table_mul_ne_zero nh3 nu2
  have zq3 : q3.z = 1 := coAdd_unit_second _ _
  have hq3 : Represents (restoreZ u3 q3) (jointAction P (0, -1)) := hstep3.2
  let u4 := h4 * u3
  have zp4 : p4.z = 1 := coAdd_unit_first _ _
  have hstep4 := @jointRep_coAdd u3 p3 (q3) P (3, 1) (0, -1)
    nu3 zp3 zq3 hp3 hq3 nh4
  have hp4 : Represents (restoreZ u4 p4) (jointAction P (3, 0)) := hstep4.1
  have nu4 : u4 ≠ 0 := table_mul_ne_zero nh4 nu3
  have zq4 : q4.z = 1 := coAdd_unit_second _ _
  have hq4 : Represents (restoreZ u4 q4) (jointAction P (0, -1)) := hstep4.2
  let u5 := h5 * u4
  have zp5 : p5.z = 1 := coAdd_unit_first _ _
  have hstep5 := @jointRep_coAdd u4 p4 (q4) P (3, 0) (0, -1)
    nu4 zp4 zq4 hp4 hq4 nh5
  have hp5 : Represents (restoreZ u5 p5) (jointAction P (3, -1)) := hstep5.1
  fin_cases i
  · change Represents
      (restoreZ z1 (jointEntryCoords (JointEntry.ofCoords (scaleNumerators z1 p0)) r n))
      (jointAction P (jointOriented r n (1, 0)))
    have h := @collectOdd_prepend_spec z1 u0 p0 (scaleNumerators z1 p0)
      (jointAction P (1, 0)) hz zp0 hp0 rfl
    have hden : z1 * u0 = z1 := by
      simp only [u0, montgomery_mul_one]
    let moved := jointEntryCoords (JointEntry.ofCoords (scaleNumerators z1 p0)) r n
    have hm := @jointEntry_represents (z1 * u0) (scaleNumerators z1 p0) P (1, 0) h.1 h.2 r n
    exact (congrArg (fun z => Represents (restoreZ z moved)
      (jointAction P (jointOriented r n (1, 0)))) hden).mp hm
  · change Represents
      (restoreZ z1 (jointEntryCoords (JointEntry.ofCoords (scaleNumerators z2 p1)) r n))
      (jointAction P (jointOriented r n (2, 1)))
    have h := @collectOdd_prepend_spec z2 u1 p1 (scaleNumerators z2 p1)
      (jointAction P (2, 1)) nz2 zp1 hp1 rfl
    have hden : z2 * u1 = z1 := by
      simp only [z1, u1, u0, montgomery_mul_one]
    let moved := jointEntryCoords (JointEntry.ofCoords (scaleNumerators z2 p1)) r n
    have hm := @jointEntry_represents (z2 * u1) (scaleNumerators z2 p1) P (2, 1) h.1 h.2 r n
    exact (congrArg (fun z => Represents (restoreZ z moved)
      (jointAction P (jointOriented r n (2, 1)))) hden).mp hm
  · change Represents
      (restoreZ z1 (jointEntryCoords (JointEntry.ofCoords (scaleNumerators z3 p2)) r n))
      (jointAction P (jointOriented r n (3, 2)))
    have h := @collectOdd_prepend_spec z3 u2 p2 (scaleNumerators z3 p2)
      (jointAction P (3, 2)) nz3 zp2 hp2 rfl
    have hden : z3 * u2 = z1 := by
      simp only [z1, z2, u2, u1, u0, montgomery_mul_one, ← montgomery_mul_assoc]
    let moved := jointEntryCoords (JointEntry.ofCoords (scaleNumerators z3 p2)) r n
    have hm := @jointEntry_represents (z3 * u2) (scaleNumerators z3 p2) P (3, 2) h.1 h.2 r n
    exact (congrArg (fun z => Represents (restoreZ z moved)
      (jointAction P (jointOriented r n (3, 2)))) hden).mp hm
  · change Represents
      (restoreZ z1 (jointEntryCoords (JointEntry.ofCoords (scaleNumerators z4 p3)) r n))
      (jointAction P (jointOriented r n (3, 1)))
    have h := @collectOdd_prepend_spec z4 u3 p3 (scaleNumerators z4 p3)
      (jointAction P (3, 1)) nz4 zp3 hp3 rfl
    have hden : z4 * u3 = z1 := by
      simp only [z1, z2, z3, u3, u2, u1, u0, montgomery_mul_one, ← montgomery_mul_assoc]
    let moved := jointEntryCoords (JointEntry.ofCoords (scaleNumerators z4 p3)) r n
    have hm := @jointEntry_represents (z4 * u3) (scaleNumerators z4 p3) P (3, 1) h.1 h.2 r n
    exact (congrArg (fun z => Represents (restoreZ z moved)
      (jointAction P (jointOriented r n (3, 1)))) hden).mp hm
  · change Represents
      (restoreZ z1 (jointEntryCoords (JointEntry.ofCoords (scaleNumerators z5 p4)) r n))
      (jointAction P (jointOriented r n (3, 0)))
    have h := @collectOdd_prepend_spec z5 u4 p4 (scaleNumerators z5 p4)
      (jointAction P (3, 0)) nz5 zp4 hp4 rfl
    have hden : z5 * u4 = z1 := by
      simp only [z1, z2, z3, z4, u4, u3, u2, u1, u0, montgomery_mul_one, ← montgomery_mul_assoc]
    let moved := jointEntryCoords (JointEntry.ofCoords (scaleNumerators z5 p4)) r n
    have hm := @jointEntry_represents (z5 * u4) (scaleNumerators z5 p4) P (3, 0) h.1 h.2 r n
    exact (congrArg (fun z => Represents (restoreZ z moved)
      (jointAction P (jointOriented r n (3, 0)))) hden).mp hm
  · change Represents
      (restoreZ z1 (jointEntryCoords (JointEntry.ofCoords p5) r n))
      (jointAction P (jointOriented r n (3, -1)))
    have hden : u5 = z1 := by
      simp only [u5, u4, u3, u2, u1, u0, z1, z2, z3, z4, z5,
        montgomery_mul_one, ← montgomery_mul_assoc]
    let moved := jointEntryCoords (JointEntry.ofCoords p5) r n
    have hm := @jointEntry_represents u5 p5 P (3, -1) zp5 hp5 r n
    exact (congrArg (fun z => Represents (restoreZ z moved)
      (jointAction P (jointOriented r n (3, -1)))) hden).mp hm

end

private noncomputable def jointChainSingle (window : Window) (z : Montgomery)
    (table : Vector JointEntry 6) (rt st : Vector Coordinates window.entries) :
    Nat → WordPair → WordPair → WordPair → WordPair → Coordinates
  | 0, _, _, _, _ => Coords.infinity
  | n+1, a, b, c, d =>
    let j := recodeJoint a.lo a.hi b.lo b.hi
    let r := recodeRaw window c.lo c.hi
    let s := recodeRaw window d.lo d.hi
    let next := jointChainSingle window z table rt st n
      ⟨j.a0,j.a1⟩ ⟨j.b0,j.b1⟩ ⟨r.lo,r.hi⟩ ⟨s.lo,s.hi⟩
    let v := addPackedJoint (double next) table j.digit
    addPackedFixed z (addPackedFixed z v window rt r.digit) window st s.digit

private theorem recodeJoint_even (a b : WordPair)
    (ha : a.lo &&& 1 = 0) (hb : b.lo &&& 1 = 0) :
    recodeJoint a.lo a.hi b.lo b.hi =
      ⟨(signedHalf a.lo a.hi).lo, (signedHalf a.lo a.hi).hi,
        (signedHalf b.lo b.hi).lo, (signedHalf b.lo b.hi).hi, 0⟩ := by
  have h : ((a.lo ||| b.lo) &&& 1 == 0) = true := by
    rw [and_distrib, ha, hb]
    rfl
  simp only [recodeJoint, h, ↓reduceIte]

private theorem jointChainSingle_even (window : Window) (z : Montgomery)
    (table : Vector JointEntry 6) (rt st : Vector Coordinates window.entries)
    (n : Nat) (a b c d : WordPair) (h : ((a.lo ||| b.lo ||| c.lo ||| d.lo) &&& 1) == 0) :
    jointChainSingle window z table rt st (n+1) a b c d =
      double (jointChainSingle window z table rt st n
        (signedHalf a.lo a.hi) (signedHalf b.lo b.hi) c.half d.half) := by
  simp only [beq_iff_eq, and_distrib, UInt64.or_eq_zero_iff] at h
  obtain ⟨⟨⟨ha,hb⟩,hc⟩,hd⟩ := h
  rw [jointChainSingle, recodeJoint_even _ _ ha hb, recodeRaw_even _ _ _ hc,
    recodeRaw_even _ _ _ hd]
  simp only [addPackedJoint, addPackedFixed, beq_self_eq_true, ↓reduceIte]
  rfl

private theorem signedValue_injective : Function.Injective signedValue := by
  intro a b h
  have hal := a.lo.toNat_lt_size
  have hbl := b.lo.toNat_lt_size
  change a.lo.toNat < 2^64 at hal
  change b.lo.toNat < 2^64 at hbl
  simp only [signedValue] at h
  have hl : a.lo = b.lo := UInt64.toNat_inj.mp (by omega)
  have ht : a.hi.toInt64.toInt = b.hi.toInt64.toInt := by omega
  have hh : a.hi = b.hi := by
    apply UInt64.toNat_inj.mp
    have ha := signedWord_mod a.hi
    have hb := signedWord_mod b.hi
    omega
  cases a
  cases b
  simp_all

private theorem signedHalf_twice (lo hi : UInt64) :
    signedHalf (signedHalf lo hi).lo (signedHalf lo hi).hi =
      ⟨(lo >>> 2) + (hi <<< 62), (hi.toInt64 >>> 2).toUInt64⟩ := by
  apply signedValue_injective
  rw [signedQuarter_eq, signedHalf_eq]
  change signedValue (signedHalf lo hi) / 2 = _
  rw [signedHalf_eq]
  omega

private theorem addPackedFixed_represents {z : Montgomery} (hz : z ≠ 0)
    (window : Window) {t : Vector Coordinates window.entries}
    {p : Coordinates} {P Q : curve.Point} (hp : Represents (restoreZ z p) P)
    (ht : TableSpec t Q) (d : UInt64) :
    Represents (restoreZ z (addPackedFixed z p window t d))
      (P + digitValue (decodeDigit window d) • Q) := by
  have h := addPackedFixed_agrees hz window (fun i => (ht i).1)
    (PointAgreement.of_represents hp hp) d
  have hAdd : Represents (addPacked (restoreZ z p) window t d)
      (P + digitValue (decodeDigit window d) • Q) := by
    rw [addPacked_eq]
    exact addDigit_spec hp ht _
  exact ⟨h.1, h.2.2.trans hAdd.2⟩

private theorem jointAction_step (P : curve.Point) (s : Int × Int) :
    let t := jointStep s
    let d := jointDecoded (jointDigit s.1 s.2)
    jointAction P s = (jointAction P t + jointAction P t) + jointAction P d := by
  dsimp only
  let t := jointStep s
  let d := jointDecoded (jointDigit s.1 s.2)
  have h := jointStep_add s
  change 2 * t.1 + d.1 = s.1 ∧ 2 * t.2 + d.2 = s.2 at h
  have he : jointAdd (jointAdd t t) d = s := by
    apply Prod.ext <;> simp only [jointAdd] <;> omega
  calc
    _ = jointAction P (jointAdd (jointAdd t t) d) := congrArg (jointAction P) he.symm
    _ = _ := by rw [jointAction_add,jointAction_add]

private theorem fixedRecode_model (window : Window) (c : WordPair) :
    let d := recodeRaw window c.lo c.hi
    (⟨d.lo,d.hi⟩ : WordPair).toNat = (recode window c.toNat).1 ∧
      decodeDigit window d.digit = (recode window c.toNat).2 := by
  dsimp only
  have h := recodeRaw_eq window c
  dsimp only at h
  rw [h.1,h.2.1,h.2.2,recodeWords_scalar,recodeWords_digit]
  exact ⟨rfl,rfl⟩

private theorem jointChainSingle_represents (window : Window) {z : Montgomery} (hz : z ≠ 0)
    {table : Vector JointEntry 6} {rt st : Vector Coordinates window.entries}
    {P G H : curve.Point} (ht : JointTableSpec z table P)
    (hr : TableSpec rt G) (hs : TableSpec st H)
    (fuel : Nat) (a b c d : WordPair)
    (ha : signedRange (signedValue a)) (hb : signedRange (signedValue b))
    (hj : jointN fuel (signedValue a, signedValue b) = (0,0))
    (hc : c.toNat ≤ scalarBound fuel) (hd : d.toNat ≤ scalarBound fuel) :
    Represents (restoreZ z (jointChainSingle window z table rt st fuel a b c d))
      (jointAction P (signedValue a,signedValue b) + c.toNat • G + d.toNat • H) := by
  induction fuel generalizing a b c d with
  | zero =>
    have h1 : signedValue a = 0 := congrArg Prod.fst hj
    have h2 : signedValue b = 0 := congrArg Prod.snd hj
    have h3 : c.toNat = 0 := Nat.eq_zero_of_le_zero hc
    have h4 : d.toNat = 0 := Nat.eq_zero_of_le_zero hd
    simpa only [jointChainSingle, restore_infinity, jointAction, h1, h2, h3, h4,
      zero_zsmul, zero_nsmul, add_zero] using infinity_spec
  | succ fuel ih =>
    let j := recodeJoint a.lo a.hi b.lo b.hi
    let r := recodeRaw window c.lo c.hi
    let s := recodeRaw window d.lo d.hi
    let a' : WordPair := ⟨j.a0,j.a1⟩
    let b' : WordPair := ⟨j.b0,j.b1⟩
    let c' : WordPair := ⟨r.lo,r.hi⟩
    let d' : WordPair := ⟨s.lo,s.hi⟩
    let u := (signedValue a, signedValue b)
    have hstep := recodeJoint_eq a b ha hb
    change j.digit = jointDigit u.1 u.2 ∧
        (signedValue a',signedValue b') = jointStep u at hstep
    have hrs := fixedRecode_model window c
    change c'.toNat = (recode window c.toNat).1 ∧
      decodeDigit window r.digit = (recode window c.toNat).2 at hrs
    have hss := fixedRecode_model window d
    change d'.toNat = (recode window d.toNat).1 ∧
      decodeDigit window s.digit = (recode window d.toNat).2 at hss
    have hu : signedRange u.1 ∧ signedRange u.2 := ⟨ha,hb⟩
    have hNext : signedRange (signedValue a') ∧ signedRange (signedValue b') := by
      change signedRange (signedValue a',signedValue b').1 ∧
        signedRange (signedValue a',signedValue b').2
      rw [hstep.2]
      exact jointStep_range hu.1 hu.2
    have hRest : jointN fuel (signedValue a',signedValue b') = (0,0) := by
      rw [hstep.2]
      exact hj
    have hbC : c'.toNat ≤ scalarBound fuel := hrs.1 ▸ recode_bound window c.toNat fuel hc
    have hbD : d'.toNat ≤ scalarBound fuel := hss.1 ▸ recode_bound window d.toNat fuel hd
    have hn := ih a' b' c' d' hNext.1 hNext.2 hRest hbC hbD
    let v := jointAction P (signedValue a',signedValue b') + c'.toNat • G + d'.toNat • H
    let out := jointChainSingle window z table rt st fuel a' b' c' d'
    have hDbl : Represents (restoreZ z (double out)) (v+v) := by
      rw [restore_double]
      have h := fastDouble_spec hn.1
      exact ⟨h.1, by rw [h.2,hn.2]⟩
    have hJoint := addPackedJoint_represents hz hDbl ht j.digit
    have hFixed1 := addPackedFixed_represents hz window hJoint hr r.digit
    have hFixed2 := addPackedFixed_represents hz window hFixed1 hs s.digit
    have hA : jointDigitCoefficients j.digit = jointDecoded (jointDigit u.1 u.2) := by
      rw [hstep.1]
      exact descriptor_coefficients_eq (jointDigitIndex u.1 u.2)
    have he : (v+v) + jointAction P (jointDigitCoefficients j.digit) +
        digitValue (decodeDigit window r.digit) • G + digitValue (decodeDigit window s.digit) • H =
        jointAction P u + c.toNat • G + d.toNat • H := by
      rw [hA, hrs.2, hss.2]
      unfold v
      rw [hstep.2, hrs.1, hss.1, jointAction_step P u, recode_smul window c.toNat G,
        recode_smul window d.toNat H]
      abel
    exact ⟨hFixed2.1, hFixed2.2.trans he⟩
private theorem wordHalf_twice (w : WordPair) :
    w.half.half = ⟨(w.lo >>> 2) + (w.hi <<< 62), w.hi >>> 2⟩ := by
  cases w
  simp only [WordPair.half, shiftWords_two, shiftHigh_two]

private theorem jointSkip_agrees {z : Montgomery} (hz : z ≠ 0)
    {p p' q : Coordinates} (h : PointAgreement (restoreZ z p') q)
    (hp : p.z = 0 → p'.z = 0) :
    PointAgreement
      (restoreZ z (if p.z.raw.w0 == 0 && decide (p.z = 0) then Coords.infinity else p')) q := by
  split
  · next ht =>
    have ht' : (p.z.raw.w0 == 0) ∧ p.z = 0 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht
    have hzero := groupValue_of_z_zero ((restore_zero_iff p' hz).2 (hp ht'.2))
    rw [restore_infinity]
    exact ⟨infinity_spec.1, h.2.1, infinity_spec.2.trans (hzero.symm.trans h.2.2)⟩
  · exact h

private theorem jointDouble_zero {p : Coordinates} (hp : p.z = 0) : (double p).z = 0 := by
  change p.y * p.z = 0
  apply toFin_embedding.injective
  rw [toFin_embedding.map_mul, hp, toFin_embedding.map_zero, mul_zero]

private theorem jointDouble_agrees {z : Montgomery} {p q : Coordinates}
    (h : PointAgreement (restoreZ z p) (restoreZ z q)) :
    PointAgreement (restoreZ z (double p)) (restoreZ z (double q)) := by
  simp only [restore_double]
  exact PointAgreement.double h

private theorem jointAdd_agrees (window : Window) {z : Montgomery} (hz : z ≠ 0)
    {t : Vector JointEntry 6} {rt st : Vector Coordinates window.entries}
    {B R S : curve.Point} (ht : JointTableSpec z t B) (hr : TableSpec rt R) (hs : TableSpec st S)
    {p q : Coordinates} (h : PointAgreement (restoreZ z p) (restoreZ z q)) (dv dr ds : UInt64) :
    PointAgreement
      (restoreZ z (addPackedFixed z
        (addPackedFixed z (addPackedJoint p t dv) window rt dr) window st ds))
      (restoreZ z (addPackedFixed z
        (addPackedFixed z (addPackedJoint q t dv) window rt dr) window st ds)) := by
  have hp : Represents (restoreZ z p) (groupValue (restoreZ z q)) := ⟨h.1,h.2.2⟩
  have hq : Represents (restoreZ z q) (groupValue (restoreZ z q)) := ⟨h.2.1,rfl⟩
  have ha := addPackedJoint_represents hz hp ht dv
  have hb := addPackedJoint_represents hz hq ht dv
  exact PointAgreement.of_represents
    (addPackedFixed_represents hz window (addPackedFixed_represents hz window ha hr dr) hs ds)
    (addPackedFixed_represents hz window (addPackedFixed_represents hz window hb hr dr) hs ds)

private theorem packedJointChain_agrees (window : Window) {z : Montgomery} (hz : z ≠ 0)
    {t : Vector JointEntry 6} {rt st : Vector Coordinates window.entries}
    {B R S : curve.Point} (ht : JointTableSpec z t B) (hr : TableSpec rt R) (hs : TableSpec st S)
    (fuel : Nat) (a b c d : WordPair) :
    PointAgreement
      (restoreZ z (packedJointChain window z t rt st fuel a.lo a.hi b.lo b.hi c.lo c.hi d.lo d.hi))
      (restoreZ z (jointChainSingle window z t rt st fuel a b c d)) := by
  have hstart : PointAgreement (restoreZ z (Coords.infinity : Coordinates))
      (restoreZ z (double Coords.infinity)) := by
    rw [restore_double, restore_infinity]
    obtain ⟨hc,hv⟩ := fastDouble_spec infinity_spec.1
    exact ⟨infinity_spec.1,hc,by rw [hv,infinity_spec.2,add_zero]⟩
  have hsingle {p q : Coordinates} (h : PointAgreement (restoreZ z p) (restoreZ z q)) :
      PointAgreement (restoreZ z (doubleUnlessInfinity double p)) (restoreZ z (double q)) :=
    jointSkip_agrees hz (jointDouble_agrees h) jointDouble_zero
  have htwice {p q : Coordinates} (h : PointAgreement (restoreZ z p) (restoreZ z q)) :
      PointAgreement (restoreZ z (doubleUnlessInfinity doubleTwice p))
        (restoreZ z (double (double q))) :=
    jointSkip_agrees hz (jointDouble_agrees (jointDouble_agrees h))
      (fun hp => jointDouble_zero (jointDouble_zero hp))
  have hthrice {p q : Coordinates} (h : PointAgreement (restoreZ z p) (restoreZ z q)) :
      PointAgreement (restoreZ z (doubleUnlessInfinity doubleThrice p))
        (restoreZ z (double (double (double q)))) :=
    jointSkip_agrees hz (jointDouble_agrees (jointDouble_agrees (jointDouble_agrees h)))
      (fun hp => jointDouble_zero (jointDouble_zero (jointDouble_zero hp)))
  induction fuel using Nat.strongRecOn generalizing a b c d with
  | _ fuel ih =>
    cases fuel with
    | zero =>
      simp only [jointChainSingle, packedJointChain, restore_infinity]
      exact ⟨infinity_spec.1,infinity_spec.1,rfl⟩
    | succ fuel =>
      cases hj : recodeJoint a.lo a.hi b.lo b.hi with | mk al ah bl bh dv =>
        cases hc : recodeRaw window c.lo c.hi with | mk cl ch dr =>
          cases hd : recodeRaw window d.lo d.hi with | mk dl dh ds =>
            rw [packedJointChain, jointChainSingle]
            simp only [hj,hc,hd]
            apply jointAdd_agrees window hz ht hr hs
            cases fuel with
            | zero => exact hstart
            | succ next =>
              let a' : WordPair := ⟨al,ah⟩
              let b' : WordPair := ⟨bl,bh⟩
              let c' : WordPair := ⟨cl,ch⟩
              let d' : WordPair := ⟨dl,dh⟩
              by_cases htwo : decide (0 < next) && (((al ||| bl ||| cl ||| dl) &&& 3) == 0)
              · have htwo' : 0 < next ∧ ((al ||| bl ||| cl ||| dl) &&& 3) == 0 := by
                  simpa only [Bool.and_eq_true,decide_eq_true_eq] using htwo
                obtain ⟨he,he'⟩ := packedLowTwoZero al ah bl bh cl ch dl dh htwo'.2
                cases next with
                | zero => omega
                | succ n =>
                  simp only [ite_eq_left htwo,Nat.succ_sub_one]
                  have h1 := jointChainSingle_even window z t rt st (n+1) a' b' c' d' he
                  have h2 := jointChainSingle_even window z t rt st n
                    (signedHalf al ah) (signedHalf bl bh) c'.half d'.half he'
                  rw [h1,h2,signedHalf_twice,signedHalf_twice,wordHalf_twice,wordHalf_twice]
                  exact hthrice (ih n (by omega)
                    ⟨(al >>> 2) + (ah <<< 62), (ah.toInt64 >>> 2).toUInt64⟩
                    ⟨(bl >>> 2) + (bh <<< 62), (bh.toInt64 >>> 2).toUInt64⟩
                    ⟨(cl >>> 2) + (ch <<< 62), ch >>> 2⟩
                    ⟨(dl >>> 2) + (dh <<< 62), dh >>> 2⟩)
              · by_cases he : ((al ||| bl ||| cl ||| dl) &&& 1) == 0
                · simp only [ite_eq_right htwo,ite_eq_left he]
                  have h := jointChainSingle_even window z t rt st next a' b' c' d' he
                  rw [h]
                  exact htwice (ih next (by omega) (signedHalf al ah) (signedHalf bl bh)
                    c'.half d'.half)
                · simp only [ite_eq_right htwo,ite_eq_right he]
                  exact hsingle (ih (next+1) (by omega) a' b' c' d')

private theorem signedValue_interval (w : WordPair) :
    -(2^127 : Int) ≤ signedValue w ∧ signedValue w < 2^127 := by
  have hl := w.lo.toNat_lt
  have hh := w.hi.toNat_lt
  rw [signedValue, int64_word_eq_cond]
  split <;> omega

private theorem signedValue_mod (w : WordPair) :
    signedValue w % (2^128 : Int) = w.toNat := by
  have hl := w.lo.toNat_lt
  have hh := w.hi.toNat_lt
  rw [signedValue, WordPair.toNat, int64_word_eq_cond]
  push_cast
  split <;> omega

private theorem unsignedNegWords_val (w : WordPair) :
    (w.neg.toNat : Int) = -(w.toNat : Int) % 2^128 := by
  have hl := w.lo.toNat_lt
  have hh := w.hi.toNat_lt
  by_cases h : w.lo = 0
  · have hBorrow : (w.lo != 0).toUInt64 = 0 := by rw [h]; rfl
    rw [WordPair.neg, hBorrow]
    simp only [WordPair.toNat, h, UInt64.sub_zero, UInt64.toNat_zero, zero_add, UInt64.toNat_sub]
    push_cast
    omega
  · have hlPos : 0 < w.lo.toNat := by
      apply Nat.pos_of_ne_zero
      intro hzero
      exact h (UInt64.toNat_inj.mp hzero)
    have hBorrow : (w.lo != 0).toUInt64 = 1 := by
      rw [show (w.lo != 0) = true from bne_iff_ne.mpr h]
      rfl
    simp only [WordPair.neg, WordPair.toNat, hBorrow, UInt64.toNat_sub, UInt64.toNat_zero,
      UInt64.toNat_one, add_zero]
    push_cast
    omega

private noncomputable def signedComponent (w : WordPair × Bool) : WordPair :=
  if w.2 then w.1.neg else w.1

private theorem signedComponent_spec (w : WordPair × Bool)
    (h : w.1.hi < 0x7fffffffffffffff) :
    signedValue (signedComponent w) = componentValue w ∧
      signedRange (signedValue (signedComponent w)) := by
  have hlo := w.1.lo.toNat_lt
  have hhi : w.1.hi.toNat < 2^63 - 1 := by
    exact UInt64.lt_iff_toNat_lt.mp h
  have hNat : w.1.toNat < 2^127 - 8 := by
    rw [WordPair.toNat]
    omega
  have hComp : -(2^127 : Int) + 8 ≤ componentValue w ∧ componentValue w < 2^127 - 8 := by
    rw [componentValue]
    split <;> omega
  have hInt := signedValue_interval (signedComponent w)
  have heq : signedValue (signedComponent w) % (2^128 : Int) = componentValue w % 2^128 := by
    rw [signedValue_mod]
    unfold signedComponent componentValue
    split
    · exact unsignedNegWords_val w.1
    · omega
  have hv : signedValue (signedComponent w) = componentValue w := by omega
  exact ⟨hv, hv ▸ hComp⟩

private theorem packedJointWords_represents {z : Montgomery}
    (hz : z ≠ 0) {table : Vector JointEntry 6} {P : curve.Point}
    (ht : JointTableSpec z table P) (k l : Montgomery.Raw) (a b : WordPair × Bool)
    (ha : a.1.hi < 0x7fffffffffffffff) (hb : b.1.hi < 0x7fffffffffffffff)
    (hvar : componentValue a • P + componentValue b • (lambda.val • P) = k.val • P) :
    let aw := signedComponent a
    let bw := signedComponent b
    Represents (restoreZ z (packedJointChain .width14 z table
      generatorTable14 generatorHighTable14 129 aw.lo aw.hi bw.lo bw.hi l.w0 l.w1 l.w2 l.w3))
      (k.val • P + l.val • Point.toPoint .generator) := by
  dsimp only
  let aw := signedComponent a
  let bw := signedComponent b
  let c : WordPair := ⟨l.w0,l.w1⟩
  let d : WordPair := ⟨l.w2,l.w3⟩
  let G := Point.toPoint .generator
  let H := (2^128 : Nat) • G
  obtain ⟨hav, har⟩ := signedComponent_spec a ha
  obtain ⟨hbv, hbr⟩ := signedComponent_spec b hb
  have hj := jointN_129 (signedValue aw, signedValue bw) har hbr
  have hRep := jointChainSingle_represents .width14 hz ht
    generatorTable_spec generatorHighTable_spec
    129 aw bw c d har hbr hj (wordPair_bound c) (wordPair_bound d)
  have hAgree := packedJointChain_agrees .width14 hz ht generatorTable_spec generatorHighTable_spec
    129 aw bw c d
  have hFixed : c.toNat • G + d.toNat • H = l.val • G := by
    have h := raw_fixed_words l
    change c.toNat = l.val % 2^128 ∧ d.toNat = l.val / 2^128 at h
    rw [h.1,h.2,generator_split_smul]
  have hGroup : jointAction P (signedValue aw,signedValue bw) + c.toNat • G + d.toNat • H =
      k.val • P + l.val • G := by
    rw [jointAction, hav, hbv, hvar, add_assoc, hFixed]
  exact ⟨hAgree.1, hAgree.2.2.trans (hRep.2.trans hGroup)⟩

private theorem addCached_eq (p q : Coordinates) :
    addCached p q (Montgomery.square q.z) (Montgomery.square q.z * q.z) =
      Coords.add 0 p q := by
  simp only [addCached, Coords.add, Montgomery.square_eq_mul, prepared_mul]

private theorem oddMultiples_eq (p : Coordinates) :
    oddMultiples p = oddMultiplesBy p (fun q => Coords.add 0 q (Coords.double 0 p)) := by
  unfold oddMultiples
  exact congrArg (oddMultiplesBy p) (funext fun q => addCached_eq q (Coords.double 0 p))

private theorem oddMultiplesBy_spec {p twice : Coordinates} {P : curve.Point}
    (hp : Represents p P) (hd : Represents twice (P + P)) :
    TableSpec (oddMultiplesBy p (fun q => Coords.add 0 q twice)) P := by
  have h1 : Represents p ((1 : Nat) • P) := by simpa only [one_nsmul] using hp
  have d : Represents twice ((2 : Nat) • P) := by simpa only [two_nsmul] using hd
  have h3 := h1.add d
  have h5 := h3.add d
  have h7 := h5.add d
  have h9 := h7.add d
  have h11 := h9.add d
  have h13 := h11.add d
  have h15 := h13.add d
  intro i
  fin_cases i <;> simp only [oddMultiplesBy, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceMul, Nat.reduceAdd]
  · exact h1
  · simpa only [← add_nsmul, Nat.reduceAdd] using h3
  · simpa only [← add_nsmul, Nat.reduceAdd] using h5
  · simpa only [← add_nsmul, Nat.reduceAdd] using h7
  · simpa only [← add_nsmul, Nat.reduceAdd] using h9
  · simpa only [← add_nsmul, Nat.reduceAdd] using h11
  · simpa only [← add_nsmul, Nat.reduceAdd] using h13
  · simpa only [← add_nsmul, Nat.reduceAdd] using h15

private theorem oddMultiples_spec {p : Coordinates} {P : curve.Point} (hp : Represents p P) :
    TableSpec (oddMultiples p) P := by
  rw [oddMultiples_eq]
  exact oddMultiplesBy_spec hp hp.double

private theorem signedTable_spec
    {t : Vector Coordinates 8} {P : curve.Point} (ht : TableSpec t P) (k : Int) :
    TableSpec (signedTable k t) (if k < 0 then -P else P) := by
  unfold signedTable
  split
  · intro i
    rw [Vector.getElem_map]
    have h := negate_spec (ht i).1
    exact ⟨h.1, by rw [h.2, (ht i).2, neg_nsmul]⟩
  · exact ht

private theorem addPrepared_eq (p q : Coordinates) (phi negative : Bool) :
    addPrepared p (prepare q) phi negative =
      Coords.add 0 p (signedPoint negative (selectedPoint phi q)) := by
  cases q
  cases phi <;> cases negative <;> simp only [addPrepared, prepare, signedPoint, selectedPoint,
    endomorphism, scaleX, negate, Bool.false_eq_true, ↓reduceIte, Coords.add, prepared_mul]

private theorem addPreparedDigit_eq (p : Coordinates) (table : Vector Coordinates 8)
    (phi negative : Bool) (digit : Option (Digit 8)) :
    addPreparedDigit p (table.map prepare) phi negative digit =
      addDigit p (selectedTable table phi negative) digit := by
  cases digit with
  | none => rfl
  | some digit =>
    obtain ⟨i, sign⟩ := digit
    simp only [addPreparedDigit, addDigit, selectedTable, Vector.getElem_map, addPrepared_eq]
    change _ = Coords.add 0 p (signedPoint sign (signedPoint negative (selectedPoint phi _)))
    rw [signedPoint_twice]

private theorem preparedChain_eq (window : Window) (table : Vector Coordinates 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries)
    (fuel : Nat) (a b c d : WordPair) :
    preparedChain window (table.map prepare) pn qn rt st fuel a b c d =
      chainWordsFor window (selectedTable table false pn) (selectedTable table true qn)
        rt st fuel a b c d := by
  induction fuel generalizing a b c d with
  | zero => rfl
  | succ fuel ih =>
    simp only [preparedChain, chainWordsFor, ih]
    erw [addPreparedDigit_eq _ table true qn, addPreparedDigit_eq _ table false pn]

private theorem selectedTable_sgn (t : Vector Coordinates 8) (phi : Bool) (n : Int) :
    selectedTable t phi (n < 0) = signedTable n (if phi then t.map endomorphism else t) := by
  cases phi <;> by_cases h : n < 0 <;>
    simp [selectedTable, selectedPoint, signedPoint, signedTable, h, Vector.map_map, Function.comp]

private theorem addPackedPrepared_eq (p : Coordinates) (table : Vector Prepared 8)
    (phi negative : Bool) (digit : UInt64) :
    addPackedPrepared p table phi negative digit =
      addPreparedDigit p table phi negative (decodeDigit .width5 digit) := by
  unfold addPackedPrepared decodeDigit
  split <;> rfl

-- The single-step chain models each grouped doubling.

private noncomputable def packedChainSingle (window : Window) (table : Vector Prepared 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → UInt64 → UInt64 → Coordinates
  | 0, _, _, _, _, _, _, _, _ => Coords.infinity
  | fuel + 1, xa0, xa1, xb0, xb1, xc0, xc1, xd0, xd1 =>
    let ⟨al,ah,da⟩ := recodeRaw .width5 xa0 xa1
    let ⟨bl,bh,db⟩ := recodeRaw .width5 xb0 xb1
    let ⟨cl,ch,dc⟩ := recodeRaw window xc0 xc1
    let ⟨dl,dh,dd⟩ := recodeRaw window xd0 xd1
    let rest := packedChainSingle window table pn qn rt st fuel al ah bl bh cl ch dl dh
    let acc := double rest
    let acc := addPackedPrepared acc table false pn da
    let acc := addPackedPrepared acc table true qn db
    addPacked (addPacked acc window rt dc) window st dd

private theorem packedChainSingle_eq (window : Window) (table : Vector Prepared 8) (pn qn : Bool)
    (rt st : Vector Coordinates window.entries) (fuel : Nat) (a b c d : WordPair) :
    packedChainSingle window table pn qn rt st fuel a.lo a.hi b.lo b.hi c.lo c.hi d.lo d.hi =
      preparedChain window table pn qn rt st fuel a b c d := by
  induction fuel generalizing a b c d with
  | zero => rfl
  | succ fuel ih =>
    have ha := recodeRaw_eq .width5 a
    have hb := recodeRaw_eq .width5 b
    have hc := recodeRaw_eq window c
    have hd := recodeRaw_eq window d
    dsimp only at ha hb hc hd
    simp only [packedChainSingle, preparedChain, addPacked_eq]
    erw [addPackedPrepared_eq, addPackedPrepared_eq]
    rw [ha.1, ha.2.1, hb.1, hb.2.1, hc.1, hc.2.1, hd.1, hd.2.1,
      ha.2.2, hb.2.2, hc.2.2, hd.2.2]
    erw [ih]

private theorem packedChain_even (window : Window) (table : Vector Prepared 8) (pn qn : Bool)
    (rt st : Vector Coordinates window.entries) (n : Nat)
    (a b c d : Recoded) (h : ((a.lo ||| b.lo ||| c.lo ||| d.lo) &&& 1) == 0) :
    packedChainSingle window table pn qn rt st (n + 1) a.lo a.hi b.lo b.hi c.lo c.hi d.lo d.hi =
      double (packedChainSingle window table pn qn rt st n
        ((a.lo >>> 1) + (a.hi <<< 63)) (a.hi >>> 1)
        ((b.lo >>> 1) + (b.hi <<< 63)) (b.hi >>> 1)
        ((c.lo >>> 1) + (c.hi <<< 63)) (c.hi >>> 1)
        ((d.lo >>> 1) + (d.hi <<< 63)) (d.hi >>> 1)) := by
  simp only [beq_iff_eq, and_distrib, UInt64.or_eq_zero_iff] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  rw [packedChainSingle]
  simp only [recodeRaw_even .width5 _ _ ha, recodeRaw_even .width5 _ _ hb,
    recodeRaw_even window _ _ hc, recodeRaw_even window _ _ hd, addPackedPrepared,
    addPacked, beq_self_eq_true, ↓reduceIte]

private theorem packedChain_eq_single (window : Window) (table : Vector Prepared 8) (pn qn : Bool)
    (rt st : Vector Coordinates window.entries) (fuel : Nat)
    (a0 a1 b0 b1 c0 c1 d0 d1 : UInt64) :
    packedChain window table pn qn rt st fuel a0 a1 b0 b1 c0 c1 d0 d1 =
      packedChainSingle window table pn qn rt st fuel a0 a1 b0 b1 c0 c1 d0 d1 := by
  induction fuel using Nat.twoStepInduction generalizing a0 a1 b0 b1 c0 c1 d0 d1 with
  | zero => rfl
  | one => rfl
  | more n ih0 ih1 =>
    rw [packedChain, packedChainSingle]
    generalize recodeRaw .width5 a0 a1 = a
    generalize recodeRaw .width5 b0 b1 = b
    generalize recodeRaw window c0 c1 = c
    generalize recodeRaw window d0 d1 = d
    cases a with | mk al ah da =>
      cases b with | mk bl bh db =>
        cases c with | mk cl ch dc =>
          cases d with | mk dl dh dd =>
            dsimp only
            split
            · rename_i h
              rw [ih0, packedChain_even window table pn qn rt st n
                ⟨al, ah, da⟩ ⟨bl, bh, db⟩ ⟨cl, ch, dc⟩ ⟨dl, dh, dd⟩ h]
              rfl
            · rw [ih1]

private theorem collectOdd_step (p q : Coordinates) (n : Nat) :
    let step := coAdd p q
    let rest := collectOdd step.1 step.2.1 n
    let d := rest.2 * step.2.2
    collectOdd p q (n + 1) =
      (⟨scaleNumerators d p :: rest.1.val, congrArg Nat.succ rest.1.property⟩, d) := by
  rw [collectOdd]

private abbrev CollectOddValid (more : Nat) (Q : curve.Point) : Prop :=
  ∀ {z : Montgomery} {p q : Coordinates} {P : curve.Point},
    z ≠ 0 → p.z = 1 → q.z = 1 →
    Represents (restoreZ z p) P → Represents (restoreZ z q) Q →
    (collectOdd p q more).2 ≠ 0 → ∀ (i : Nat) (entry : Coordinates),
      (collectOdd p q more).1.val[i]? = some entry →
      entry.z = 1 ∧ Represents (restoreZ ((collectOdd p q more).2 * z) entry) (P + i • Q)

private theorem collectOdd_zero_spec (Q : curve.Point) : CollectOddValid 0 Q := by
  intro z p q P hz hpz hqz hp hq hf i entry hentry
  cases i with
  | zero =>
    simp only [collectOdd, List.getElem?_cons_zero, Option.some.injEq] at hentry
    subst entry
    change p.z = 1 ∧ Represents (restoreZ ((1 : Montgomery) * z) p) (P + (0 : Nat) • Q)
    rw [montgomery_one_mul, zero_nsmul, add_zero]
    exact ⟨hpz, hp⟩
  | succ i =>
    simp only [collectOdd, List.getElem?_cons_succ, List.getElem?_nil] at hentry
    cases hentry

private theorem collectOdd_succ_spec
    (more : Nat) (Q : curve.Point) (ih : CollectOddValid more Q) :
    CollectOddValid (more + 1) Q := by
  intro z p q P hz hpz hqz hp hq hf i entry hentry
  generalize hstep : coAdd p q = step
  rcases step with ⟨p', q', h⟩
  generalize hrest : collectOdd p' q' more = rest
  let d := rest.2 * h
  have hout : collectOdd p q (more + 1) =
      (⟨scaleNumerators d p :: rest.1.val, congrArg Nat.succ rest.1.property⟩, d) := by
    have ho := collectOdd_step p q more
    dsimp only at ho
    rw [hstep] at ho
    exact ho.trans (by rw [hrest])
  have hden : (collectOdd p q (more + 1)).2 = d := congrArg Prod.snd hout
  have hlook (j : Nat) :
      (collectOdd p q (more+1)).1.val[j]? = (scaleNumerators d p :: rest.1.val)[j]? :=
    congrArg (fun o => o.1.val[j]?) hout
  have hd : d ≠ 0 := hden ▸ hf
  rw [hden]
  have hf' := @table_factors_ne_zero rest.2 h hd
  cases i with
  | zero =>
    have hlookup : (scaleNumerators d p :: rest.1.val)[0]? = some (scaleNumerators d p) :=
      List.getElem?_cons_zero
    have he : scaleNumerators d p = entry := Option.some.inj
      ((hlookup.symm.trans (hlook 0).symm).trans hentry)
    rw [zero_nsmul, add_zero]
    exact @collectOdd_prepend_spec d z p entry P hd hpz hp he
  | succ i =>
    have ha : (coAdd p q).2.2 ≠ 0 := by rw [hstep]; exact hf'.2
    have hh := @coAdd_spec z p q P Q hz hpz hqz hp hq ha
    rw [hstep] at hh
    have hp1 : p'.z = 1 := by
      have h := coAdd_unit_first p q
      rw [hstep] at h
      exact h
    have hq1 : q'.z = 1 := by
      have h := coAdd_unit_second p q
      rw [hstep] at h
      exact h
    have hf0 : (collectOdd p' q' more).2 ≠ 0 := by rw [hrest]; exact hf'.1
    have hentry' : (collectOdd p' q' more).1.val[i]? = some entry := by
      rw [hrest]
      exact List.getElem?_cons_succ.symm.trans ((hlook (i+1)).symm.trans hentry)
    have hrec := @ih (h*z) p' q' (P+Q) (@table_mul_ne_zero h z hf'.2 hz)
      hp1 hq1 hh.1 hh.2 hf0 i entry hentry'
    rw [hrest] at hrec
    rw [show d*z = rest.2*(h*z) from montgomery_mul_assoc _ _ _, succ_nsmul]
    have hgroup : (P+Q)+i • Q = P+(i • Q+Q) := by
      rw [add_assoc, add_comm Q (i • Q)]
    rw [← hgroup]
    exact hrec

private theorem collectOdd_valid
    (more : Nat) (Q : curve.Point) : CollectOddValid more Q := by
  induction more with
  | zero => exact collectOdd_zero_spec Q
  | succ n ih => exact collectOdd_succ_spec n Q ih

private theorem collectOdd_spec
    (more : Nat) {z : Montgomery} {p q : Coordinates}
    {P Q : curve.Point} (hz : z ≠ 0) (hpz : p.z = 1) (hqz : q.z = 1)
    (hp : Represents (restoreZ z p) P) (hq : Represents (restoreZ z q) Q)
    (hf : (collectOdd p q more).2 ≠ 0)
    (i : Nat) (hi : i < (collectOdd p q more).1.val.length) :
    let out := collectOdd p q more
    let entry := out.1.val[i]'hi
    entry.z = 1 ∧ Represents (restoreZ (out.2 * z) entry) (P + i • Q) :=
  @collectOdd_valid more Q z p q P hz hpz hqz hp hq hf i _
    (List.getElem?_eq_getElem hi)

private theorem commonTable_scale (p : Coordinates) :
    let d := double p
    let p' : Coordinates := { scaleNumerators d.z p with z := 1 }
    let q' : Coordinates := { d with z := 1 }
    (commonTable p).2 = (collectOdd p' q' 7).2 * d.z :=
  rfl

private theorem commonTable_array (p : Coordinates) :
    let d := double p
    let p' : Coordinates := { scaleNumerators d.z p with z := 1 }
    let q' : Coordinates := { d with z := 1 }
    (commonTable p).1.toArray = (collectOdd p' q' 7).1.val.toArray :=
  rfl

private theorem collectOdd_vector_spec
    (more : Nat) {z : Montgomery} {p q : Coordinates}
    {P Q : curve.Point} (hz : z ≠ 0) (hpz : p.z = 1) (hqz : q.z = 1)
    (hp : Represents (restoreZ z p) P) (hq : Represents (restoreZ z q) Q)
    (hf : (collectOdd p q more).2 ≠ 0)
    (table : Vector Coordinates (more + 1)) (den : Montgomery)
    (harray : table.toArray = (collectOdd p q more).1.val.toArray)
    (hden : den = (collectOdd p q more).2*z)
    (i : Fin (more + 1)) :
    table[i.val].z = 1 ∧ Represents (restoreZ den table[i.val]) (P + i.val • Q) := by
  have hi : i.val < (collectOdd p q more).1.val.length := by
    rw [(collectOdd p q more).1.property]
    exact i.isLt
  have hentry : table[i.val] = (collectOdd p q more).1.val[i.val]'hi := by
    have hb : i.val < table.toArray.size := table.size_toArray.symm ▸ i.isLt
    calc
      _ = table.toArray[i.val]'hb := (Vector.getElem_toArray hb).symm
      _ = _ := by simp only [harray, List.getElem_toArray]
  rw [hden, hentry]
  exact @collectOdd_spec more z p q P Q hz hpz hqz hp hq hf i.val hi

private theorem commonTable_spec_with_double
    {p d : Coordinates} {P : curve.Point} (hpz : p.z = 1)
    (hp : Represents p P) (hd : Represents d (P + P))
    (table : Vector Coordinates 8) (den : Montgomery) (hz : den ≠ 0)
    (hden :
      den = (collectOdd { scaleNumerators d.z p with z := 1 } {d with z := 1} 7).2 * d.z)
    (harray :
      table.toArray =
        (collectOdd { scaleNumerators d.z p with z := 1 } {d with z := 1} 7).1.val.toArray) :
    ∀ i : Fin 8, table[i.val].z = 1 ∧
      Represents (restoreZ den table[i.val]) ((2*i.val+1) • P) := by
  let p' : Coordinates := { scaleNumerators d.z p with z := 1 }
  let q' : Coordinates := { d with z := 1 }
  let out := collectOdd p' q' 7
  have hnonzero : out.2*d.z ≠ 0 :=
    Eq.mp (congrArg (fun w : Montgomery => w ≠ 0) hden) hz
  have hz' := @table_factors_ne_zero out.2 d.z hnonzero
  have h1 : Represents (restoreZ d.z p') P :=
    @commonTable_seed_first p P hpz hp d.z hz'.2
  have h2 : Represents (restoreZ d.z q') (P + P) := @commonTable_seed_second d (P + P) hd
  intro i
  have hgroup : ((2*i.val+1) • P) = P + i.val • (P + P) := by
    rw [Nat.mul_comm 2 i.val, add_nsmul, mul_nsmul, one_nsmul, two_nsmul, add_comm, nsmul_add]
  have h := @collectOdd_vector_spec 7 d.z p' q' P (P+P)
    hz'.2 rfl rfl h1 h2 hz'.1 table den harray hden i
  exact ⟨h.1, Eq.mpr (congrArg (fun P' => Represents (restoreZ den table[i.val]) P')
    hgroup) h.2⟩

private theorem commonTable_spec
    {p : Coordinates} {P : curve.Point} (hpz : p.z = 1)
    (hp : Represents p P) (hz : (commonTable p).2 ≠ 0) :
    ∀ i : Fin 8, (commonTable p).1[i.val].z = 1 ∧
      Represents (restoreZ (commonTable p).2 (commonTable p).1[i.val]) ((2*i.val+1) • P) := by
  have hd := @fastDouble_spec p hp.1
  have hdRep : Represents (double p) (P+P) := ⟨hd.1, hd.2.trans (congrArg₂ (·+·) hp.2 hp.2)⟩
  exact @commonTable_spec_with_double p (double p) P hpz hp hdRep
    (commonTable p).1 (commonTable p).2 hz (commonTable_scale p) (commonTable_array p)

private theorem addCommon_eq_selected (p t : Coordinates) (phi neg : Bool) :
    addCommon p
      (if phi then (prepareCommon t).phiX else (prepareCommon t).point.x)
      (if neg then (0 : Montgomery) - (prepareCommon t).point.y
        else (prepareCommon t).point.y) =
    addCommon p (signedPoint neg (selectedPoint phi t)).x
      (signedPoint neg (selectedPoint phi t)).y := by
  cases t
  cases phi <;> cases neg <;>
    simp only [prepareCommon, signedPoint, selectedPoint, endomorphism, scaleX, negate,
      Bool.false_eq_true, ↓reduceIte]

private theorem addPackedCommon_agrees
    {z : Montgomery} (hz : z ≠ 0) {t : Vector Coordinates 8}
    (ht : ∀ i : Fin 8, t[i.val].z = 1 ∧ OnCurve (restoreZ z t[i.val]))
    {p q : Coordinates} (hp : PointAgreement (restoreZ z p) q)
    (phi neg : Bool) (digit : UInt64) :
    PointAgreement (restoreZ z (addPackedCommon p (t.map prepareCommon) phi neg digit))
      (addPackedPrepared q ((t.map (restoreZ z)).map prepare) phi neg digit) := by
  by_cases hd : digit = 0
  · simpa only [addPackedCommon, addPackedPrepared, beq_iff_eq, hd, ↓reduceIte] using hp
  · let i : Fin 8 := packedIndex .width5 digit
    let flip : Bool := neg != (digit >= Window.pivot .width5)
    let v := signedPoint flip (selectedPoint phi t[i.val])
    have hvz : v.z = 1 := (selected_signed_z t[i.val] phi flip).trans (ht i).1
    have hv : OnCurve (restoreZ z v) := by
      change OnCurve (restoreZ z (signedPoint flip (selectedPoint phi t[i.val])))
      rw [restoreZ_selected_signed]
      exact selected_signed_onCurve (ht i).2 phi flip
    have ho := @addCommon_spec p v (groupValue q) (groupValue (restoreZ z v)) z
      hz hvz ⟨hp.1, hp.2.2⟩ ⟨hv, rfl⟩
    have hr := @add_spec q (restoreZ z v) hp.2.1 hv
    simp only [addPackedCommon, addPackedPrepared, beq_iff_eq, hd, ↓reduceIte, Vector.getElem_map]
    rw [addCommon_eq_selected, addPrepared_eq, ← restoreZ_selected_signed]
    exact PointAgreement.of_represents ho hr

private theorem packedChain_even_step (window : Window) (table : Vector Prepared 8) (pn qn : Bool)
    (rt st : Vector Coordinates window.entries) (n : Nat)
    (a b c d : WordPair) (h : ((a.lo ||| b.lo ||| c.lo ||| d.lo) &&& 1) == 0) :
    packedChain window table pn qn rt st (n + 1) a.lo a.hi b.lo b.hi c.lo c.hi d.lo d.hi =
      double (packedChain window table pn qn rt st n
        ((a.lo >>> 1) + (a.hi <<< 63)) (a.hi >>> 1)
        ((b.lo >>> 1) + (b.hi <<< 63)) (b.hi >>> 1)
        ((c.lo >>> 1) + (c.hi <<< 63)) (c.hi >>> 1)
        ((d.lo >>> 1) + (d.hi <<< 63)) (d.hi >>> 1)) := by
  simp only [packedChain_eq_single]
  exact packedChain_even window table pn qn rt st n
    ⟨a.lo, a.hi, 0⟩ ⟨b.lo, b.hi, 0⟩ ⟨c.lo, c.hi, 0⟩ ⟨d.lo, d.hi, 0⟩ h

private theorem packedCommonChain_agrees
    (window : Window) {z : Montgomery} (hz : z ≠ 0)
    {t : Vector Coordinates 8}
    (ht : ∀ i : Fin 8, t[i.val].z = 1 ∧ OnCurve (restoreZ z t[i.val]))
    (pn qn : Bool) (rt st : Vector Coordinates window.entries)
    (hr : ∀ i : Fin window.entries, OnCurve rt[i.val])
    (hs : ∀ i : Fin window.entries, OnCurve st[i.val])
    (fuel : Nat) (a0 a1 b0 b1 c0 c1 d0 d1 : UInt64) :
    PointAgreement
      (restoreZ z (packedCommonChain window z (t.map prepareCommon) pn qn rt st fuel
        a0 a1 b0 b1 c0 c1 d0 d1))
      (packedChain window ((t.map (restoreZ z)).map prepare) pn qn rt st fuel
        a0 a1 b0 b1 c0 c1 d0 d1) := by
  have hinf : PointAgreement (Coords.infinity : Coordinates) Coords.infinity :=
    ⟨infinity_spec.1, infinity_spec.1, rfl⟩
  have hdouble {p q : Coordinates} (h : PointAgreement (restoreZ z p) q) :
      PointAgreement (restoreZ z (double p)) (double q) := by
    rw [restore_double]
    exact PointAgreement.double h
  have double_z_zero {p : Coordinates} (hp : p.z = 0) : (double p).z = 0 := by
    change p.y * p.z = 0
    apply toFin_embedding.injective
    rw [toFin_embedding.map_mul, hp, toFin_embedding.map_zero, mul_zero]
  have hskip {p p' q : Coordinates} (h : PointAgreement (restoreZ z p') q)
      (hz' : p.z = 0 → p'.z = 0) :
      PointAgreement
        (restoreZ z (if p.z.raw.w0 == 0 && decide (p.z = 0) then Coords.infinity else p')) q := by
    split
    · next htest =>
      have htest' : (p.z.raw.w0 == 0) ∧ p.z = 0 := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using htest
      have hp := htest'.2
      have hzero := groupValue_of_z_zero ((restore_zero_iff p' hz).2 (hz' hp))
      rw [restore_infinity]
      exact ⟨infinity_spec.1, h.2.1, infinity_spec.2.trans (hzero.symm.trans h.2.2)⟩
    · exact h
  have hsingle {p q : Coordinates} (h : PointAgreement (restoreZ z p) q) :
      PointAgreement (restoreZ z (doubleUnlessInfinity double p)) (double q) :=
    hskip (hdouble h) double_z_zero
  have htwice {p q : Coordinates} (h : PointAgreement (restoreZ z p) q) :
      PointAgreement (restoreZ z (doubleUnlessInfinity doubleTwice p)) (double (double q)) :=
    hskip (hdouble (hdouble h)) (fun hp => double_z_zero (double_z_zero hp))
  have hthrice {p q : Coordinates} (h : PointAgreement (restoreZ z p) q) :
      PointAgreement (restoreZ z (doubleUnlessInfinity doubleThrice p))
        (double (double (double q))) :=
    hskip (hdouble (hdouble (hdouble h)))
      (fun hp => double_z_zero (double_z_zero (double_z_zero hp)))
  have hstart : PointAgreement (restoreZ z Coords.infinity) (double Coords.infinity) := by
    rw [restore_infinity]
    obtain ⟨hc, hv⟩ := fastDouble_spec infinity_spec.1
    exact ⟨infinity_spec.1, hc, by rw [hv, infinity_spec.2, add_zero]⟩
  have hadd {p q : Coordinates} (h : PointAgreement (restoreZ z p) q)
      (da db dc dd : UInt64) :
      PointAgreement
        (restoreZ z (addPackedFixed z
          (addPackedFixed z (addPackedCommon (addPackedCommon p (t.map prepareCommon) false pn da)
            (t.map prepareCommon) true qn db) window rt dc) window st dd))
        (addPacked (addPacked (addPackedPrepared
          (addPackedPrepared q ((t.map (restoreZ z)).map prepare) false pn da)
          ((t.map (restoreZ z)).map prepare) true qn db) window rt dc) window st dd) :=
    addPackedFixed_agrees hz window hs
      (addPackedFixed_agrees hz window hr
        (addPackedCommon_agrees hz ht
          (addPackedCommon_agrees hz ht h false pn da) true qn db) dc) dd
  induction fuel using Nat.strongRecOn generalizing a0 a1 b0 b1 c0 c1 d0 d1 with
  | _ fuel ih =>
    cases fuel with
    | zero =>
      simpa only [packedCommonChain, packedChain, restore_infinity] using hinf
    | succ fuel =>
      cases ha : recodeRaw .width5 a0 a1 with | mk al ah da =>
        cases hb : recodeRaw .width5 b0 b1 with | mk bl bh db =>
          cases hc : recodeRaw window c0 c1 with | mk cl ch dc =>
            cases hd : recodeRaw window d0 d1 with | mk dl dh dd =>
              rw [packedCommonChain, packedChain]
              simp only [ha, hb, hc, hd]
              apply hadd
              cases fuel with
              | zero => exact hstart
              | succ next =>
                by_cases ht : decide (0 < next) && (((al ||| bl ||| cl ||| dl) &&& 3) == 0)
                · have ht' : 0 < next ∧ ((al ||| bl ||| cl ||| dl) &&& 3) == 0 := by
                    simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht
                  obtain ⟨he, he'⟩ := packedLowTwoZero al ah bl bh cl ch dl dh ht'.2
                  cases next with
                  | zero => omega
                  | succ n =>
                    simp only [ite_eq_left ht, ite_eq_left he,
                      doubleTwice_eq, Nat.succ_sub_one]
                    have step := packedChain_even_step window ((t.map (restoreZ z)).map prepare)
                      pn qn rt st n
                      ⟨(al >>> 1) + (ah <<< 63), ah >>> 1⟩
                      ⟨(bl >>> 1) + (bh <<< 63), bh >>> 1⟩
                      ⟨(cl >>> 1) + (ch <<< 63), ch >>> 1⟩
                      ⟨(dl >>> 1) + (dh <<< 63), dh >>> 1⟩ he'
                    rw [step]
                    simp only [shiftWords_two, shiftHigh_two]
                    exact hthrice (ih n (by omega) _ _ _ _ _ _ _ _)
                · by_cases he : ((al ||| bl ||| cl ||| dl) &&& 1) == 0
                  · simp only [ite_eq_right ht, ite_eq_left he, doubleTwice_eq]
                    exact htwice (ih next (by omega) _ _ _ _ _ _ _ _)
                  · simp only [ite_eq_right ht, ite_eq_right he]
                    exact hsingle (ih (next + 1) (by omega) _ _ _ _ _ _ _ _)

private theorem chain_spec
    (window : Window) (fuel : Nat) (p q : Stream 8) (r s : Stream window.entries)
    (P Q R S : curve.Point) (hp : TableSpec p.table P) (hq : TableSpec q.table Q)
    (hr : TableSpec r.table R) (hs : TableSpec s.table S)
    (hpb : p.scalar.toNat ≤ scalarBound fuel) (hqb : q.scalar.toNat ≤ scalarBound fuel)
    (hrb : r.scalar.toNat ≤ scalarBound fuel) (hsb : s.scalar.toNat ≤ scalarBound fuel) :
    Represents (chainFor window fuel p q r s)
      (p.scalar.toNat • P + q.scalar.toNat • Q + r.scalar.toNat • R + s.scalar.toNat • S) := by
  induction fuel generalizing p q r s with
  | zero =>
    have hp0 : p.scalar.toNat = 0 := Nat.eq_zero_of_le_zero hpb
    have hq0 : q.scalar.toNat = 0 := Nat.eq_zero_of_le_zero hqb
    have hr0 : r.scalar.toNat = 0 := Nat.eq_zero_of_le_zero hrb
    have hs0 : s.scalar.toNat = 0 := Nat.eq_zero_of_le_zero hsb
    simpa only [chainFor, chainWordsFor, hp0, hq0, hr0, hs0, zero_nsmul, add_zero]
      using infinity_spec
  | succ fuel ih =>
    let a := recodeWords .width5 p.scalar
    let b := recodeWords .width5 q.scalar
    let c := recodeWords window r.scalar
    let d := recodeWords window s.scalar
    have h := ih ⟨a.1, p.table⟩ ⟨b.1, q.table⟩ ⟨c.1, r.table⟩ ⟨d.1, s.table⟩ hp hq hr hs
      (by simpa only [Stream.scalar, a, recodeWords_scalar] using recode_bound .width5 _ _ hpb)
      (by simpa only [Stream.scalar, b, recodeWords_scalar] using recode_bound .width5 _ _ hqb)
      (by simpa only [Stream.scalar, c, recodeWords_scalar] using recode_bound window _ _ hrb)
      (by simpa only [Stream.scalar, d, recodeWords_scalar] using recode_bound window _ _ hsb)
    let V := a.1.toNat • P + b.1.toNat • Q + c.1.toNat • R + d.1.toNat • S
    have hd := fastDouble_spec h.1
    have hdbl : Represents (double _) (V + V) := ⟨hd.1, by rw [hd.2, h.2]⟩
    have h1 := addDigit_spec hdbl hp a.2
    have h2 := addDigit_spec h1 hq b.2
    have h3 := addDigit_spec h2 hr c.2
    have h4 := addDigit_spec h3 hs d.2
    have he :
        V + V + digitValue a.2 • P + digitValue b.2 • Q +
            digitValue c.2 • R + digitValue d.2 • S =
          p.scalar.toNat • P + q.scalar.toNat • Q + r.scalar.toNat • R + s.scalar.toNat • S := by
      rw [recode_smul .width5 p.scalar.toNat P, recode_smul .width5 q.scalar.toNat Q,
        recode_smul window r.scalar.toNat R, recode_smul window s.scalar.toNat S]
      dsimp only [V, a, b, c, d]
      simp only [recodeWords_scalar, recodeWords_digit]
      abel
    have : Represents (chainFor window (fuel + 1) p q r s) _ := h4
    exact he ▸ this
private theorem packedRecovery_represents {t : Vector Coordinates 8} {P : curve.Point}
    (ht : TableSpec t P) (k l : Fn) :
    let (a, b) := splitScalar k.val
    let aw := WordPair.ofNat a.natAbs
    let bw := WordPair.ofNat b.natAbs
    let rw := WordPair.ofNat (l.val % 2^128)
    let sw := WordPair.ofNat (l.val / 2^128)
    Represents
      (packedChain .width14 (t.map prepare) (a < 0) (b < 0) generatorTable14 generatorHighTable14
        129 aw.lo aw.hi bw.lo bw.hi rw.lo rw.hi sw.lo sw.hi)
      (k.val • P + l.val • Point.toPoint .generator) := by
  let a := (splitScalar k.val).1
  let b := (splitScalar k.val).2
  let aw := WordPair.ofNat a.natAbs
  let bw := WordPair.ofNat b.natAbs
  let rw := WordPair.ofNat (l.val % 2^128)
  let sw := WordPair.ofNat (l.val / 2^128)
  change Represents
    (packedChain .width14 (t.map prepare) (a < 0) (b < 0) generatorTable14 generatorHighTable14
      129 aw.lo aw.hi bw.lo bw.hi rw.lo rw.hi sw.lo sw.hi) _
  have hb := splitScalar_bound k.val
  have hm : l.val % 2^128 < 2^128 := Nat.mod_lt _ (by decide)
  have hq : l.val / 2^128 < 2^128 :=
    Nat.div_lt_of_lt_mul (Nat.lt_trans l.isLt (by decide))
  have haNat : aw.toNat = a.natAbs := WordPair.toNat_ofNat _ hb.1
  have hbNat : bw.toNat = b.natAbs := WordPair.toNat_ofNat _ hb.2
  have hmNat : rw.toNat = l.val % 2^128 := WordPair.toNat_ofNat _ hm
  have hqNat : sw.toNat = l.val / 2^128 := WordPair.toNat_ofNat _ hq
  have h := chain_spec .width14 129
    ⟨aw, signedTable a t⟩
    ⟨bw, signedTable b (t.map endomorphism)⟩
    ⟨rw, generatorTable14⟩
    ⟨sw, generatorHighTable14⟩ _ _ _ _
    (signedTable_spec ht a)
    (signedTable_spec (endomorphismTable_spec ht) b)
    generatorTable_spec generatorHighTable_spec
    (by simp only [haNat]; exact hb.1.le)
    (by simp only [hbNat]; exact hb.2.le)
    (by simp only [hmNat]; exact hm.le)
    (by simp only [hqNat]; exact hq.le)
  dsimp only [Stream.scalar] at h
  have hv := h.2
  rw [haNat, hbNat, hmNat, hqNat, signed_smul, signed_smul, add_assoc (_ + _),
    generator_split_smul] at hv
  have he := splitScalar_smul k.val P
  rw [natCast_zsmul, smul_eq_val_nsmul, ZMod.val_natCast_of_lt k.isLt] at he
  rw [he] at hv
  erw [packedChain_eq_single, packedChainSingle_eq, preparedChain_eq,
    selectedTable_sgn, selectedTable_sgn]
  exact ⟨h.1, hv⟩

private theorem selectedTable_component_spec
    {t : Vector Coordinates 8} {P : curve.Point} (ht : TableSpec t P) (phi neg : Bool) :
    TableSpec (selectedTable t phi neg)
      (if neg then -(if phi then lambda.val • P else P) else
        (if phi then lambda.val • P else P)) := by
  let r : Int := if neg then -1 else 0
  have hsgn : decide (r < 0) = neg := by cases neg <;> rfl
  have ht' : TableSpec (if phi then t.map endomorphism else t)
      (if phi then lambda.val • P else P) := by
    cases phi
    · exact ht
    · exact endomorphismTable_spec ht
  have htable := selectedTable_sgn t phi r
  rw [hsgn] at htable
  rw [htable]
  have h := signedTable_spec ht' r
  cases neg <;> simpa [r] using h

private theorem packedComponents_represents {t : Vector Coordinates 8} {P : curve.Point}
    (ht : TableSpec t P) (a b : WordPair × Bool) (c d : WordPair) :
    Represents
      (packedChain .width14 (t.map prepare) a.2 b.2 generatorTable14 generatorHighTable14
        129 a.1.lo a.1.hi b.1.lo b.1.hi c.lo c.hi d.lo d.hi)
      (componentValue a • P + componentValue b • (lambda.val • P) +
        c.toNat • Point.toPoint .generator +
          d.toNat • ((2^128 : Nat) • Point.toPoint .generator)) := by
  have ha : TableSpec (selectedTable t false a.2) (if a.2 then -P else P) :=
    selectedTable_component_spec ht false a.2
  have hb : TableSpec (selectedTable t true b.2)
      (if b.2 then -(lambda.val • P) else lambda.val • P) :=
    selectedTable_component_spec ht true b.2
  have h := chain_spec .width14 129 ⟨a.1, selectedTable t false a.2⟩
    ⟨b.1, selectedTable t true b.2⟩ ⟨c, generatorTable14⟩ ⟨d, generatorHighTable14⟩
    _ _ _ _ ha hb generatorTable_spec generatorHighTable_spec
    (wordPair_bound a.1) (wordPair_bound b.1) (wordPair_bound c) (wordPair_bound d)
  erw [packedChain_eq_single, packedChainSingle_eq, preparedChain_eq]
  simpa only [chainFor, Stream.scalar, component_nsmul] using h

private theorem packedCommonComponents_represents {t : Vector Coordinates 8}
    {z : Montgomery} {P : curve.Point} (hz : z ≠ 0)
    (ht : ∀ i : Fin 8, t[i.val].z = 1 ∧ OnCurve (restoreZ z t[i.val]))
    (hv : TableSpec (t.map (restoreZ z)) P) (a b : WordPair × Bool) (c d : WordPair) :
    Represents
      (restoreZ z (packedCommonChain .width14 z (t.map prepareCommon) a.2 b.2
        generatorTable14 generatorHighTable14 129 a.1.lo a.1.hi b.1.lo b.1.hi c.lo c.hi d.lo d.hi))
      (componentValue a • P + componentValue b • (lambda.val • P) +
        c.toNat • Point.toPoint .generator +
          d.toNat • ((2^128 : Nat) • Point.toPoint .generator)) := by
  have h := packedCommonChain_agrees .width14 hz ht a.2 b.2 generatorTable14 generatorHighTable14
    (fun i => (generatorTable_spec i).1) (fun i => (generatorHighTable_spec i).1)
    129 a.1.lo a.1.hi b.1.lo b.1.hi c.lo c.hi d.lo d.hi
  have hRef := packedComponents_represents hv a b c d
  exact ⟨h.1, h.2.2.trans hRef.2⟩

private theorem packedApproxRawComponents_represents
    {t : Vector Coordinates 8} {z : Montgomery} {P : curve.Point} (hz : z ≠ 0)
    (ht : ∀ i : Fin 8, t[i.val].z = 1 ∧ OnCurve (restoreZ z t[i.val]))
    (hv : TableSpec (t.map (restoreZ z)) P) (k l : Montgomery.Raw) (a b : WordPair × Bool)
    (hVar : componentValue a • P + componentValue b • (lambda.val • P) = k.val • P) :
    Represents (restoreZ z (packedCommonChain .width14 z (t.map prepareCommon) a.2 b.2
      generatorTable14 generatorHighTable14 129 a.1.lo a.1.hi b.1.lo b.1.hi
      l.w0 l.w1 l.w2 l.w3)) (k.val • P + l.val • Point.toPoint .generator) := by
  let c : WordPair := ⟨l.w0,l.w1⟩
  let d : WordPair := ⟨l.w2,l.w3⟩
  let G := Point.toPoint .generator
  have hFixed : c.toNat • G + d.toNat • ((2^128 : Nat) • G) = l.val • G := by
    have h := raw_fixed_words l
    change c.toNat = l.val % 2^128 ∧ d.toNat = l.val / 2^128 at h
    rw [h.1,h.2,generator_split_smul]
  have hGroup : componentValue a • P + componentValue b • (lambda.val • P) +
      c.toNat • G + d.toNat • ((2^128 : Nat) • G) = k.val • P + l.val • G := by
    rw [hVar, add_assoc, hFixed]
  change Represents (restoreZ z (packedCommonChain .width14 z (t.map prepareCommon) a.2 b.2
    generatorTable14 generatorHighTable14 129 a.1.lo a.1.hi b.1.lo b.1.hi c.lo c.hi d.lo d.hi))
      (k.val • P + l.val • G)
  rw [← hGroup]
  exact packedCommonComponents_represents hz ht hv a b c d

private theorem splitScalarWords_smul_raw
    (k : Montgomery.Raw) (hk : k.val < Fn.modulus) (P : curve.Point) :
    componentValue (splitScalarWords k).1 • P +
      componentValue (splitScalarWords k).2 • (lambda.val • P) = k.val • P := by
  let u := (approximateWeight k splitConstants.aRecip).toNat
  let v := (approximateWeight k splitConstants.bRecip).toNat
  have hComp := splitScalarWords_components_raw k hk
  dsimp only at hComp
  rw [hComp.1, hComp.2]
  exact displacedScalar_smul ⟨k.val, hk⟩ u v P

/-- The shared chain of doublings computes `k P + l G` on a form of `P`. -/
private theorem fallback_represents (k l : Fn) {p : Coordinates} {P : curve.Point}
    (hp : Represents p P) :
    Represents (Coords.mulAdd 0 256 k.val p l.val (Point.toMontgomeryCoords .generator))
      (k.val • P + l.val • Point.toPoint .generator) := by
  have hg := point_spec Point.isOnCurve_generator
  have hread : readCoords (Coords.mulAdd 0 256 k.val p l.val
      (Point.toMontgomeryCoords .generator)) = Jacobian.mulAdd 0 256 k.val (readCoords p) l.val
        (readCoords (Point.toMontgomeryCoords .generator)) := by
    have h := Coords.map_mulAdd toFin_embedding (0 : Montgomery) 256 k.val p l.val
      (Point.toMontgomeryCoords .generator)
    rw [toFin_embedding.map_zero] at h
    exact congrArg (Jacobian.ofCoords : Coords Fp → _) h
  unfold Represents OnCurve groupValue
  rw [hread]
  refine ⟨Jacobian.onCurve_mulAdd (Jacobian.toZ_zero (m := Fp.modulus)) two_ne_zero 256 k.val
    l.val hp.1 hg.1, ?_⟩
  rw [Jacobian.toPoint_mulAdd (Jacobian.toZ_zero (m := Fp.modulus)) two_ne_zero 256 k.val l.val
    hp.1 hg.1 (Nat.lt_trans k.isLt (by decide)) (Nat.lt_trans l.isLt (by decide))]
  exact congrArg₂ (k.val • · + l.val • ·) hp.2 hg.2

private theorem rawOfNat_val_of_lt (k : Fn) : (Montgomery.rawOfNat k.val).val = k.val :=
  Montgomery.rawOfNat_val _ (Nat.lt_trans k.isLt (by decide))

section
attribute [local irreducible] splitScalarWords commonTable

/-- On an affine form with a nonzero table denominator, the common chain runs. -/
private theorem mulCommon_affine_eq
    (k l : Fn) (p : Coordinates) {t : Vector Coordinates 8}
    {z : Montgomery} (hp : p.z = 1) (ht : commonTable p = (t,z)) (hz : z ≠ 0) :
    let a := (splitScalarWords (Montgomery.rawOfNat k.val)).1
    let b := (splitScalarWords (Montgomery.rawOfNat k.val)).2
    let lw := Montgomery.rawOfNat l.val
    mulCommon k p l =
      restoreZ z (packedCommonChain .width14 z (t.map prepareCommon) a.2 b.2
        generatorTable14 generatorHighTable14 129 a.1.lo a.1.hi b.1.lo b.1.hi
        lw.w0 lw.w1 lw.w2 lw.w3) := by
  dsimp only
  rw [mulCommon, ite_eq_left hp, ht]
  simp only [ite_eq_right hz]

/-- The common chain computes `k P + l G` on a form of a point `P`, on every branch. -/
private theorem mulCommon_represents
    (k l : Fn) {p : Coordinates} {P : curve.Point} (hp : Represents p P) :
    Represents (mulCommon k p l) (k.val • P + l.val • Point.toPoint .generator) := by
  have hFallback := fallback_represents k l hp
  have hk := rawOfNat_val_of_lt k
  have hl := rawOfNat_val_of_lt l
  by_cases hpz : p.z = 1
  · cases hTable : commonTable p with
    | mk t z =>
      by_cases hz : z = 0
      · simpa only [mulCommon, ite_eq_left hpz, hTable, ite_eq_left hz] using hFallback
      · have hzn : (commonTable p).2 ≠ 0 := by rw [hTable]; exact hz
        have ht := commonTable_spec hpz hp hzn
        rw [hTable] at ht
        have ht' (i : Fin 8) : t[i.val].z = 1 ∧ OnCurve (restoreZ z t[i.val]) :=
          ⟨(ht i).1, (ht i).2.1⟩
        have htable : TableSpec (t.map (restoreZ z)) P := by
          intro i
          rw [Vector.getElem_map]
          exact (ht i).2
        rw [mulCommon_affine_eq k l p hpz hTable hz]
        have h := packedApproxRawComponents_represents hz ht' htable
          (Montgomery.rawOfNat k.val) (Montgomery.rawOfNat l.val)
          (splitScalarWords (Montgomery.rawOfNat k.val)).1
          (splitScalarWords (Montgomery.rawOfNat k.val)).2
          (splitScalarWords_smul_raw (Montgomery.rawOfNat k.val) (by rw [hk]; exact k.isLt) P)
        rw [hk, hl] at h
        exact h
  · simpa only [mulCommon, ite_eq_right hpz] using hFallback

end

section
attribute [local irreducible] splitScalarWords commonJointTable

/-- On the joint branch, the multiplication is the joint chain with its denominator restored. -/
private theorem mulProjective_joint_eq
    (k l : Fn) (p : Coordinates) {t : Vector JointEntry 6}
    {z : Montgomery} (hp : p.z = 1)
    (ht : commonJointTable p = (t,z)) (hz : z ≠ 0)
    (ha : (splitScalarWords (Montgomery.rawOfNat k.val)).1.1.hi < 0x7fffffffffffffff)
    (hb : (splitScalarWords (Montgomery.rawOfNat k.val)).2.1.hi < 0x7fffffffffffffff) :
    let a := signedComponent (splitScalarWords (Montgomery.rawOfNat k.val)).1
    let b := signedComponent (splitScalarWords (Montgomery.rawOfNat k.val)).2
    let lw := Montgomery.rawOfNat l.val
    mulProjective k p l = restoreZ z (packedJointChain .width14 z t
      generatorTable14 generatorHighTable14 129 a.lo a.hi b.lo b.hi lw.w0 lw.w1 lw.w2 lw.w3) := by
  have hguard : (decide ((splitScalarWords (Montgomery.rawOfNat k.val)).1.1.hi <
      0x7fffffffffffffff) && decide ((splitScalarWords (Montgomery.rawOfNat k.val)).2.1.hi <
        0x7fffffffffffffff)) = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true ha, decide_eq_true hb⟩
  dsimp only
  simp only [mulProjective, ite_eq_left hp, hguard, ↓reduceIte, ht, ite_eq_right hz,
    signedComponent]

/-- The multiplication computes `k P + l G` on a form of a point `P`, on every branch. -/
private theorem mulProjective_represents
    (k l : Fn) {p : Coordinates} {P : curve.Point} (hp : Represents p P) :
    Represents (mulProjective k p l) (k.val • P + l.val • Point.toPoint .generator) := by
  have hFallback := mulCommon_represents k l hp
  have hk := rawOfNat_val_of_lt k
  have hl := rawOfNat_val_of_lt l
  by_cases hpz : p.z = 1
  · by_cases ha : (splitScalarWords (Montgomery.rawOfNat k.val)).1.1.hi < 0x7fffffffffffffff
    · by_cases hb : (splitScalarWords (Montgomery.rawOfNat k.val)).2.1.hi < 0x7fffffffffffffff
      · have hguard : (decide ((splitScalarWords (Montgomery.rawOfNat k.val)).1.1.hi <
            0x7fffffffffffffff) && decide ((splitScalarWords (Montgomery.rawOfNat k.val)).2.1.hi <
              0x7fffffffffffffff)) = true :=
          Bool.and_eq_true_iff.mpr ⟨decide_eq_true ha, decide_eq_true hb⟩
        cases hTable : commonJointTable p with
        | mk t z =>
          by_cases hz : z = 0
          · simpa only [mulProjective, ite_eq_left hpz, hguard, ↓reduceIte,
              hTable, ite_eq_left hz] using hFallback
          · have hzn : (commonJointTable p).2 ≠ 0 := by rw [hTable]; exact hz
            have hTableSpec := commonJointTable_spec hpz hp hzn
            rw [hTable] at hTableSpec
            rw [mulProjective_joint_eq k l p hpz hTable hz ha hb]
            have h := packedJointWords_represents hz hTableSpec (Montgomery.rawOfNat k.val)
              (Montgomery.rawOfNat l.val) (splitScalarWords (Montgomery.rawOfNat k.val)).1
              (splitScalarWords (Montgomery.rawOfNat k.val)).2 ha hb
              (splitScalarWords_smul_raw (Montgomery.rawOfNat k.val) (by rw [hk]; exact k.isLt) P)
            rw [hk, hl] at h
            exact h
      · simpa only [mulProjective, ite_eq_left hpz, decide_eq_false hb,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte] using hFallback
    · simpa only [mulProjective, ite_eq_left hpz, decide_eq_false ha,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte] using hFallback
  · simpa only [mulProjective, ite_eq_right hpz] using hFallback

end

/-- The joint chain computes `k P + l G`, for a point `P` on the curve. -/
private theorem toPoint_mulAddGenerator {k l : Fn} {p : Point} (hp : p.isOnCurve = true) :
    (mulAddGenerator k p l).isOnCurve = true ∧
      Point.toPoint (mulAddGenerator k p l) =
        k.val • Point.toPoint p + l.val • Point.toPoint .generator := by
  have h := mulProjective_represents k l (p := Point.toMontgomeryCoords p)
    (P := Point.toPoint p) (point_spec hp)
  rw [mulAddGenerator, ofMontgomeryCoords_eq_read]
  have hs := Point.ofJacobian_spec h.1
  exact ⟨hs.1, hs.2.trans h.2⟩

theorem isOnCurve_mulAddGenerator {k l : Fn} {p : Point} (hp : p.isOnCurve = true) :
    (mulAddGenerator k p l).isOnCurve = true :=
  (toPoint_mulAddGenerator hp).1

end MulAdd

namespace Point

/-- The shared chain of doublings, as a point. -/
private abbrev sharedChain (k : Fn) (p : Point) (l : Fn) (q : Point) : Point :=
  ofJacobian (Jacobian.mulAdd 0 256 k.val (toJacobian p) l.val (toJacobian q))

/-- The shared chain on Montgomery form is the shared chain on `Fp`, for every input. -/
private theorem general_eq (k : Fn) (p : Point) (l : Fn) (q : Point) :
    ofMontgomeryCoords
        (Jacobian.Coords.mulAdd 0 256 k.val (toMontgomeryCoords p) l.val (toMontgomeryCoords q)) =
      sharedChain k p l q := by
  rw [ofMontgomeryCoords_eq]
  have h := Jacobian.Coords.map_mulAdd toFin_embedding 0 256 k.val (toMontgomeryCoords p) l.val
    (toMontgomeryCoords q)
  rw [toFin_embedding.map_zero, map_toMontgomeryCoords, map_toMontgomeryCoords] at h
  exact congrArg (fun c => ofJacobian (Jacobian.ofCoords c)) h

/-- On points of the curve, the shared chain lies on the curve and computes `k P + l Q`. -/
private theorem sharedChain_spec (k l : Fn) {p q : Point} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) :
    (sharedChain k p l q).isOnCurve = true ∧
      toPoint (sharedChain k p l q) = k.val • toPoint p + l.val • toPoint q := by
  have hJp := toJacobian_spec hp
  have hJq := toJacobian_spec hq
  have hon := Jacobian.onCurve_mulAdd (Jacobian.toZ_zero (m := Fp.modulus)) MulAdd.two_ne_zero 256
    k.val l.val hJp.1 hJq.1
  refine ⟨(ofJacobian_spec hon).1, ?_⟩
  rw [(ofJacobian_spec hon).2, Jacobian.toPoint_mulAdd (Jacobian.toZ_zero (m := Fp.modulus))
    MulAdd.two_ne_zero 256 k.val l.val hJp.1 hJq.1 (Nat.lt_trans k.isLt (by decide))
    (Nat.lt_trans l.isLt (by decide))]
  exact congrArg₂ (k.val • · + l.val • ·) hJp.2 hJq.2

/-- The joint chain, which the generator selects, gives the point of the shared chain. -/
private theorem mul_eq_chain (k l : Fn) {p : Point} (hp : p.isOnCurve = true) :
    MulAdd.mulAddGenerator k p l = sharedChain k p l generator := by
  have h := MulAdd.toPoint_mulAddGenerator (k := k) (l := l) hp
  have hc := sharedChain_spec k l hp isOnCurve_generator
  exact (toPoint_inj h.1 hc.1).mp (h.2.trans hc.2.symm)

/-- `k P + l Q` is the shared chain of doublings on `Fp`, for every input.

The joint chain that the generator selects gives the same point, by the group law. -/
theorem mulAdd_eq_jacobian (k : Fn) (p : Point) (l : Fn) (q : Point) :
    mulAdd k p l q =
      ofJacobian (Jacobian.mulAdd 0 256 k.val (toJacobian p) l.val (toJacobian q)) := by
  unfold mulAdd
  split
  · rename_i h
    obtain ⟨rfl, hp⟩ := h
    exact mul_eq_chain k l hp
  · split
    · rename_i h
      obtain ⟨rfl, hq⟩ := h
      -- `l Q + k G` and `k G + l Q` are one point, by commutativity in the group.
      have h1 := MulAdd.toPoint_mulAddGenerator (k := l) (l := k) hq
      have h2 := sharedChain_spec k l isOnCurve_generator hq
      refine (toPoint_inj h1.1 h2.1).mp (h1.2.trans (h2.2.trans ?_).symm)
      exact add_comm _ _
    · exact general_eq k p l q

theorem isOnCurve_mulAdd (k l : Fn) {p q : Point} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) : (mulAdd k p l q).isOnCurve = true := by
  rw [mulAdd_eq_jacobian]
  exact (sharedChain_spec k l hp hq).1

/-- The shared chain computes `k P + l Q`, with the values of `k` and `l` below `n`. -/
theorem toPoint_mulAdd (k l : Fn) {p q : Point} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) :
    toPoint (mulAdd k p l q) = k.val • toPoint p + l.val • toPoint q := by
  rw [mulAdd_eq_jacobian]
  exact (sharedChain_spec k l hp hq).2

/-- On points of the curve, the shared chain gives the sum of the two products. -/
theorem mulAdd_eq (k l : Fn) {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    mulAdd k p l q = mul k p + mul l q := by
  rw [← toPoint_inj (isOnCurve_mulAdd k l hp hq) (isOnCurve_add (isOnCurve_mul k hp)
    (isOnCurve_mul l hq)), toPoint_mulAdd k l hp hq, toPoint_add (isOnCurve_mul k hp)
    (isOnCurve_mul l hq), toPoint_mul k hp, toPoint_mul l hq]

end Point

end EthLib.Cryptography.Secp256k1
