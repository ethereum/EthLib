module

public import EthLib.Cryptography.Proofs.Bls.TwistFrobenius
public import EthLib.Cryptography.Proofs.Bls.G1SubgroupSpan

/-!
# Proofs: the rotation `(x, y) ↦ (β * x, y)` of `G1`

`β` is a cube root of unity in `Fp`, so the rotation keeps a point on `y^2 = x^3 + 4`.

In `E(Fp12)` the rotation is a scaling of coordinates, so it is a group homomorphism.

Let `P` have prime order `q`, and let `Q` and `R` be its rotation and its double rotation.

If `Q = [i] P`, then `R = [i^2] P`, so `P + Q + R = 0` gives `q ∣ 1 + i + i^2`.

That divisibility fails for every `i` when `-3` is not a square modulo `q`.

Otherwise it leaves only the two roots of `1 + i + i^2`, which a computation excludes.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1Rotation

open WeierstrassCurve TwistFrobenius G1

local notation "F" => ZMod Fp.modulus

/-! ## Two homomorphisms into `E(Fp12)` -/

theorem beta_ne_zero : fpToFp12 betaZ ≠ 0 :=
  (map_ne_zero fpToFp12).mpr (by decide)

theorem map_four {u : Fp12} (hu : u ^ 6 = 1) : fpToFp12 (4 : F) * u ^ 6 = 4 := by
  rw [hu, mul_one, map_ofNat]

theorem beta_sq_pow_six : (fpToFp12 betaZ ^ 2) ^ 6 = 1 := by
  rw [← pow_mul, show 2 * 6 = 3 * 4 from rfl, pow_mul, ← map_pow, betaZ_cube, map_one, one_pow]

/-- The inclusion of `E(Fp)` in `E(Fp12)`. -/
noncomputable def embed : curve.toAffine.Point →+ ambientCurve.Point :=
  ShortWeierstrass.scaledHom fpToFp12 one_ne_zero (map_four (one_pow 6))

/-- The rotation `(x, y) ↦ (β * x, y)`, with values in `E(Fp12)`. -/
noncomputable def rotate : curve.toAffine.Point →+ ambientCurve.Point :=
  ShortWeierstrass.scaledHom fpToFp12 (pow_ne_zero 2 beta_ne_zero) (map_four beta_sq_pow_six)

theorem embed_injective : Function.Injective embed :=
  ShortWeierstrass.scaledHom_injective _ _ _

/-- The rotation of an affine point is the inclusion of the point `(β * x, y)`. -/
theorem rotate_toPoint {x y x' : Fp} (hv : Valid ⟨x, y, Fp.one⟩) (hv' : Valid ⟨x', y, Fp.one⟩)
    (hx : Fp.toZMod x' = betaZ * Fp.toZMod x) :
    rotate (toPoint ⟨x, y, Fp.one⟩) = embed (toPoint ⟨x', y, Fp.one⟩) := by
  have hb : fpToFp12 betaZ ^ 3 = 1 := by rw [← map_pow, betaZ_cube, map_one]
  have hr (a : Fp) : rep ⟨a, y, Fp.one⟩ = ![Fp.toZMod a, Fp.toZMod y, 1] := by
    rw [rep, Fp.one_def, Fp.toZMod_one]
  rw [Valid, hr] at hv hv'
  have e1 : toPoint ⟨x, y, Fp.one⟩ = _ :=
    (congrArg (Jacobian.Point.toAffine curve) (hr x)).trans (Jacobian.Point.toAffine_some hv)
  have e2 : toPoint ⟨x', y, Fp.one⟩ = _ :=
    (congrArg (Jacobian.Point.toAffine curve) (hr x')).trans (Jacobian.Point.toAffine_some hv')
  rw [e1, e2]
  show Affine.Point.some _ _ _ = Affine.Point.some _ _ _
  rw [Affine.Point.some.injEq, hx, _root_.map_mul, one_pow, one_pow, mul_one, mul_one]
  constructor
  · linear_combination fpToFp12 (Fp.toZMod x) * fpToFp12 betaZ * hb
  · linear_combination fpToFp12 (Fp.toZMod y) * (fpToFp12 betaZ ^ 3 + 1) * hb

/-- An equation of `Fp` elements, decided by comparing their values. -/
theorem eq_of_decide {a b : F} (h : @decide (a = b) (instDecidableEqFin _ a b) = true) : a = b :=
  of_decide_eq_true h

/-! ## Dependence forces a root of `1 + i + i^2` -/

/-- If `Q = [i] P`, the relations of a rotation give `[1 + i + i^2] P = 0`. -/
theorem nsmul_eq_zero_of_rotation {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ι σ : A →+ B) (hι : Function.Injective ι) {P Q R : A} (h1 : σ P = ι Q) (h2 : σ Q = ι R)
    (hsum : P + Q + R = 0) {i : Nat} (hi : Q = i • P) : (1 + i + i * i) • P = 0 := by
  have hR : R = (i * i) • P := by
    apply hι
    rw [← h2, hi, map_nsmul, h1, ← map_nsmul, hi, ← mul_nsmul']
  rw [add_nsmul, add_nsmul, one_nsmul, ← hi, ← hR]
  exact hsum

/-- If `-3` is not a square modulo the prime `q`, then `q` never divides `1 + i + i^2`.

The computation shows `(-3)^((q - 1) / 2) ≠ 1`, which is Euler's criterion for a non-square. -/
theorem not_dvd_of_nonresidue {q fuel : Nat} (hq : q.Prime) (h3 : 3 < q) (hodd : q % 2 = 1)
    (hfuel : q - 1 < 2 ^ fuel)
    (hne : PowMod.powModAux fuel q (q - 3) ((q - 1) / 2) ≠ 1 % q) (i : Nat) :
    ¬ q ∣ 1 + i + i * i := by
  intro hd
  have : Fact q.Prime := ⟨hq⟩
  have h0 : ((1 + i + i * i : Nat) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at h0
  have hneg3 : ((q - 3 : Nat) : ZMod q) = -3 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    push_cast
    ring
  have hz : ((2 * i + 1 : Nat) : ZMod q) ^ 2 = ((q - 3 : Nat) : ZMod q) := by
    rw [hneg3]
    push_cast
    linear_combination 4 * h0
  have hz0 : ((2 * i + 1 : Nat) : ZMod q) ≠ 0 := by
    intro h
    rw [h, hneg3] at hz
    have h3' : ((3 : Nat) : ZMod q) = 0 := by push_cast; linear_combination hz
    have := (ZMod.natCast_eq_zero_iff _ _).mp h3'
    exact absurd (Nat.le_of_dvd (by decide) this) (by omega)
  apply PowMod.natCast_pow_div_ne_one q fuel (q - 3) 2 hfuel hne
  rw [← hz, ← pow_mul, Nat.mul_div_cancel' (by omega)]
  exact ZMod.pow_card_sub_one_eq_one hz0

/-- If `l1` and `l2` are roots of `1 + i + i^2` modulo the prime `q`, there is no other root. -/
theorem eq_root_of_dvd {q l1 l2 : Nat} (hq : q.Prime) (hsum : (l1 + l2 + 1) % q = 0)
    (hprod : l1 * l2 % q = 1) (hl1 : l1 < q) (hl2 : l2 < q) {i : Nat} (hi : i < q)
    (hd : q ∣ 1 + i + i * i) : i = l1 ∨ i = l2 := by
  have : Fact q.Prime := ⟨hq⟩
  have h0 : ((1 + i + i * i : Nat) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have e1 : ((l1 + l2 + 1 : Nat) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hsum)
  have e2 : ((l1 * l2 : Nat) : ZMod q) = 1 := by
    rw [← ZMod.natCast_mod, hprod, Nat.cast_one]
  push_cast at h0 e1 e2
  have hp : ((i : ZMod q) - l1) * ((i : ZMod q) - l2) = 0 := by
    linear_combination h0 - (i : ZMod q) * e1 + e2
  rcases mul_eq_zero.mp hp with h | h
  · left
    have := (ZMod.natCast_eq_natCast_iff' i l1 q).mp (sub_eq_zero.mp h)
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hl1] at this
  · right
    have := (ZMod.natCast_eq_natCast_iff' i l2 q).mp (sub_eq_zero.mp h)
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hl2] at this

/-! ## Computations on points -/

/-- A computation of `[n] P = 0` gives the same fact in the curve group. -/
theorem nsmul_zero_cert {P : G1} (hp : Valid P) (n fuel : Nat) (hn : n < 2 ^ fuel)
    (hc : (mulNatAux fuel P n).isInfinity = true) : n • toPoint P = 0 := by
  rw [← toPoint_mulNat hp]
  apply (isInfinity_eq_true_iff_toPoint_eq_zero (valid_mulNat hp n)).mp
  rwa [← mulNatAux_eq fuel P n hn]

/-- A computation of `Q - [n] P ≠ 0` gives `Q ≠ [n] P` in the curve group. -/
theorem nsmul_ne_cert {P Q : G1} (hp : Valid P) (hq : Valid Q) (n fuel : Nat)
    (hn : n < 2 ^ fuel) (hc : (add Q (neg (mulNatAux fuel P n))).isInfinity = false) :
    toPoint Q ≠ n • toPoint P := by
  intro he
  rw [mulNatAux_eq fuel P n hn] at hc
  have hv := valid_add hq (valid_neg (valid_mulNat hp n))
  have hz : (add Q (neg (mulNatAux fuel P n))).isInfinity = true := by
    rw [mulNatAux_eq fuel P n hn]
    apply (isInfinity_eq_true_iff_toPoint_eq_zero hv).mpr
    rw [toPoint_add hq (valid_neg (valid_mulNat hp n)), toPoint_neg (valid_mulNat hp n),
      toPoint_mulNat hp, he, add_neg_cancel]
  rw [mulNatAux_eq fuel P n hn, hc] at hz
  exact Bool.noConfusion hz

/-- A computation of `P + Q + R = 0` gives the same fact in the curve group. -/
theorem sum_zero_cert {P Q R : G1} (hp : Valid P) (hq : Valid Q) (hr : Valid R)
    (hc : (add (add P Q) R).isInfinity = true) : toPoint P + toPoint Q + toPoint R = 0 := by
  rw [← toPoint_add hp hq, ← toPoint_add (valid_add hp hq) hr]
  exact (isInfinity_eq_true_iff_toPoint_eq_zero (valid_add (valid_add hp hq) hr)).mp hc

/-- A point with `z = 1` is not the identity. -/
theorem toPoint_ne_zero {x y : Fp} (hv : Valid ⟨x, y, Fp.one⟩) : toPoint ⟨x, y, Fp.one⟩ ≠ 0 :=
  fun h => Bool.noConfusion ((isInfinity_eq_true_iff_toPoint_eq_zero hv).mpr h)

/-- A point `P` of prime order `q` and its rotation `Q` are independent.

The hypothesis says that no `i` below `q` both is a root of `1 + i + i^2` and has `Q = [i] P`. -/
theorem not_nsmul_of_rotation {q : Nat} (hq : q.Prime) {x y bx bbx : Fp}
    (hp : Valid ⟨x, y, Fp.one⟩) (hq' : Valid ⟨bx, y, Fp.one⟩) (hr : Valid ⟨bbx, y, Fp.one⟩)
    (hbx : Fp.toZMod bx = betaZ * Fp.toZMod x) (hbbx : Fp.toZMod bbx = betaZ * Fp.toZMod bx)
    (hP : q • toPoint ⟨x, y, Fp.one⟩ = 0)
    (hsum : toPoint ⟨x, y, Fp.one⟩ + toPoint ⟨bx, y, Fp.one⟩ + toPoint ⟨bbx, y, Fp.one⟩ = 0)
    (hroots : ∀ i < q, q ∣ 1 + i + i * i →
      toPoint ⟨bx, y, Fp.one⟩ ≠ i • toPoint ⟨x, y, Fp.one⟩)
    (i : Fin q) : toPoint ⟨bx, y, Fp.one⟩ ≠ i.val • toPoint ⟨x, y, Fp.one⟩ := by
  intro he
  have : Fact q.Prime := ⟨hq⟩
  have hd := addOrderOf_dvd_of_nsmul_eq_zero (nsmul_eq_zero_of_rotation embed rotate
    embed_injective (rotate_toPoint hp hq' hbx) (rotate_toPoint hq' hr hbbx) hsum he)
  rw [addOrderOf_eq_prime hP (toPoint_ne_zero hp)] at hd
  exact hroots i.val i.isLt hd he

end EthLib.Cryptography.Bls.G1Rotation
