module

public import EthLib.Cryptography.Proofs.AltBn128.MillerChain
public import EthLib.Cryptography.Proofs.AltBn128.PairingBilinear
public import EthLib.Cryptography.Proofs.AltBn128.Order
public import EthLib.Cryptography.Proofs.AltBn128.G2Order
public import EthLib.Cryptography.Proofs.MillerAte

/-!
# Proofs: the pairing of alt_bn128 is bilinear

The optimal ate pairing of EIP-197 multiplies three values at `P`.

Then it applies the final exponentiation.

Let `Q'` be the untwist of `Q`, and let `s = 6 u + 2`.

Let `pi` be the map `(x, y) -> (x^p, y^p)` on `E : y^2 = x^3 + 3` over `Fp12`.

The first value is Miller's function of `s` and `Q'`.

The second is the line through `s Q'` and `pi(Q')`.

The third is the line through their sum and `-pi(pi(Q'))`.

With the verticals through the two sums, these values form one quotient of products of lines, `f`.

- The group `G` is the untwist of `G_2`: the multiples of the untwist of `P2`.
- The untwist of `P2` has the order `q`.
- The kernel computes `pi(P2) = p P2` on the twist, so `pi` acts on `G` as `p`.
- In `G`, `pi` fixes only `O`, because `q` does not divide `p - 1`.
- On `G`, `-pi^2` acts as `pi^8`, because `q` divides `p^6 + 1`.
- On `G`, `s + p - p^2` acts as `pi^9`, because `q` divides `s + p - p^2 + p^3`.
- So `f` has the ate divisor `sum_j c_j ((pi^j Q') - (O))`.
- Its coefficients `c_j` are `s`, 1, 1 and -1 at `j` = 0, 1, 8 and 9.
- Its exponent `n = s + p + p^8 - p^9` is a multiple of `q`.
- So `z^(N n) = 1` for every nonzero `z`, with `N = (p^12 - 1) / q`.

The ate value of `P` and `Q'` is `f(P)^N`.

It is linear in `P` among the points that `pi` fixes, by the linearity of an ate-type pairing.

It is linear in `Q'` in `G` too.

The points of `G_1` lie on `E` over `Fp12`.

`pi` fixes them, because their coordinates lie in `Fp`.

Take a finite point `P` on the curve and a point `Q` on the twist whose untwist lies in `G`.

Their pairing is the ate value of their points.

The final exponentiation sends the two verticals to 1, so they do not change it.

So `e(a P1, b P2) = e(P1, P2)^(a b)` for all `a` and `b`.

The pairing law of EIP-197 follows, with no hypothesis.

See [Vercauteren](https://eprint.iacr.org/2008/096), "Optimal pairings", Section 2.2.

See also [Beuchat et al.](https://eprint.iacr.org/2010/354), §2, on the optimal ate pairing.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

open WeierstrassCurve WeierstrassCurve.Affine Miller Fp12

open scoped Fin.CommRing

namespace Ate

set_option maxRecDepth 8000 in
/-- The kernel computes `pi(P2) = p P2` on the twist, with `p` reduced modulo `q`. -/
theorem frobenius_generator :
    AltBn128.frobenius Point2.generator =
      Point2.mulBits 256 (Fp.modulus % Fr.modulus) Point2.generator := by
  decide +kernel

/-- The `p`-th power map fixes the coefficients of `y^2 = x^3 + 3` over `Fp12`. -/
theorem ambientCurve_map : ambientCurve.map primeFrobenius = ambientCurve := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;> simp [ShortWeierstrass.curve, map_ofNat]

/-- The map `(x, y) -> (x^p, y^p)` on the points of `y^2 = x^3 + 3` over `Fp12`. -/
noncomputable abbrev frobenius : ambientCurve.Point →+ ambientCurve.Point :=
  Miller.mapPoint primeFrobenius ambientCurve_map

/-- It is the Frobenius map of the untwist proofs. -/
theorem frobenius_eq_frobeniusHom : frobenius = frobeniusHom := by
  ext P
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp [mapPoint_some, frobeniusHom, ShortWeierstrass.scaledHom_apply,
      ShortWeierstrass.scaledPoint]

/-- The untwist of the generator `P2` of `G_2`. -/
noncomputable def g2Point : ambientCurve.Point := untwist Point2.generator.toPoint

/-- The untwist of `P2` has the order `q`, because the untwist is injective. -/
theorem addOrderOf_g2Point : addOrderOf g2Point = Fr.modulus := by
  rw [g2Point, addOrderOf_injective untwist untwist_injective, Point2.addOrderOf_generator]

/-- The untwist of `G_2`: the multiples of the untwist of `P2`. -/
noncomputable def g2Subgroup : AddSubgroup ambientCurve.Point := AddSubgroup.zmultiples g2Point

/-- The order of each point of the untwist of `G_2` divides `q`. -/
theorem addOrderOf_dvd_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) :
    addOrderOf R ∣ Fr.modulus :=
  addOrderOf_g2Point ▸ addOrderOf_dvd_of_mem_zmultiples hR

/-- On the untwist of `G_2`, two multiples agree when their scalars agree modulo `q`. -/
theorem zsmul_eq_of_modEq {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) {a b : ℤ}
    (h : a ≡ b [ZMOD Fr.modulus]) : a • R = b • R := by
  rw [← sub_eq_zero, ← sub_smul]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).mp
    ((Int.natCast_dvd_natCast.mpr (addOrderOf_dvd_of_mem hR)).trans h.symm.dvd)

/-- On the untwist of `G_2`, a scalar coprime to `q` sends a nonzero point to a nonzero point. -/
theorem zsmul_ne_zero_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) (h0 : R ≠ 0)
    {a : ℤ} (ha : Nat.gcd a.natAbs Fr.modulus = 1) : a • R ≠ 0 := by
  intro h
  have h1 := Int.natCast_dvd.mp ((addOrderOf_dvd_iff_zsmul_eq_zero).mpr h)
  have hd := Nat.dvd_gcd h1 (addOrderOf_dvd_of_mem hR)
  rw [ha, Nat.dvd_one] at hd
  exact h0 (AddMonoid.addOrderOf_eq_one_iff.mp hd)

/-- On the untwist of `P2`, the Frobenius map acts as `p`. -/
theorem frobenius_g2Point : frobenius g2Point = (Fp.modulus : ℤ) • g2Point := by
  rw [frobenius_eq_frobeniusHom, g2Point, ← (untwist_frobenius Point2.isOnCurve_generator).2,
    frobenius_generator, Point2.toPoint_mulBits 256 _ Point2.isOnCurve_generator (by decide),
    map_nsmul, ← g2Point, ← natCast_zsmul]
  exact zsmul_eq_of_modEq (AddSubgroup.mem_zmultiples _) (by decide +kernel)

/-- On each point of the untwist of `G_2`, the Frobenius map acts as `p`. -/
theorem frobenius_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) :
    frobenius R = (Fp.modulus : ℤ) • R := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
  rw [map_zsmul, frobenius_g2Point, smul_comm]

/-- The Frobenius map sends the untwist of `G_2` into itself. -/
theorem frobenius_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) :
    frobenius R ∈ g2Subgroup := by
  rw [frobenius_of_mem hR]
  exact g2Subgroup.zsmul_mem hR _

/-- In the untwist of `G_2`, the Frobenius map fixes only `O`, because `p - 1` is coprime to `q`. -/
theorem eq_zero_of_frobenius_eq {R : ambientCurve.Point} (hR : R ∈ g2Subgroup)
    (h : frobenius R = R) : R = 0 := by
  by_contra h0
  apply zsmul_ne_zero_of_mem hR h0 (a := (Fp.modulus : ℤ) - 1) (by decide +kernel)
  rw [sub_smul, ← frobenius_of_mem hR, h, one_smul, sub_self]

/-- On the untwist of `G_2`, the `j`-th power of the Frobenius map acts as `p^j`. -/
theorem frobenius_iterate_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) (j : ℕ) :
    frobenius^[j] R = ((Fp.modulus : ℤ) ^ j) • R := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_zsmul, frobenius_of_mem hR, smul_smul, pow_succ]

/-! ## The divisor of the optimal ate function -/

/-- The pairs `(j, c_j)` of the ate divisor of the optimal ate function. -/
def ateCoeffs : List (ℕ × ℤ) := [(0, ATE_LOOP_COUNT), (1, 1), (8, 1), (9, -1)]

/-- The lines of the optimal ate function of EIP-197, with their verticals.

They are Miller's function of `s = 6 u + 2` and `Q`, then `g_{s Q, pi Q}`.

The last is `g_{s Q + pi Q, -pi^2 Q}`. -/
noncomputable def ateLines (Q : ambientCurve.Point) : LineRatio ambientCurve :=
  lines ambientCurve ATE_LOOP_COUNT Q + chordRatio (ATE_LOOP_COUNT • Q) (frobenius Q) +
    chordRatio (ATE_LOOP_COUNT • Q + frobenius Q) (-frobenius (frobenius Q))

/-- On the untwist of `G_2`, `-pi^2` is `pi^8`, because `q` divides `p^6 + 1`. -/
theorem neg_frobenius_frobenius {Q : ambientCurve.Point} (hQ : Q ∈ g2Subgroup) :
    -frobenius (frobenius Q) = frobenius^[8] Q := by
  rw [frobenius_iterate_of_mem hQ, frobenius_of_mem (frobenius_mem hQ), frobenius_of_mem hQ,
    smul_smul, ← neg_zsmul]
  exact zsmul_eq_of_modEq hQ (by decide +kernel)

/-- On the untwist of `G_2`, `s + pi - pi^2` is `pi^9`, because `q` divides `s + p - p^2 + p^3`. -/
theorem ateLines_sum {Q : ambientCurve.Point} (hQ : Q ∈ g2Subgroup) :
    ATE_LOOP_COUNT • Q + frobenius Q + -frobenius (frobenius Q) = frobenius^[9] Q := by
  rw [frobenius_iterate_of_mem hQ, frobenius_of_mem (frobenius_mem hQ), frobenius_of_mem hQ]
  have e : ATE_LOOP_COUNT • Q + (Fp.modulus : ℤ) • Q + -((Fp.modulus : ℤ) • (Fp.modulus : ℤ) • Q) =
      ((ATE_LOOP_COUNT : ℤ) + Fp.modulus - Fp.modulus * Fp.modulus) • Q := by
    module
  rw [e]
  exact zsmul_eq_of_modEq hQ (by decide +kernel)

/-- The optimal ate function of a point `Q` of the untwist of `G_2` has the ate divisor.

The divisor is `s ((Q) - (O)) + ((pi Q) - (O)) + ((pi^8 Q) - (O)) - ((pi^9 Q) - (O))`. -/
theorem ratioDivisor_ateLines {Q : ambientCurve.Point} (hQ : Q ∈ g2Subgroup) :
    ratioDivisor (ateLines Q) = ateDivisor frobenius Q ateCoeffs := by
  rw [ateLines, ratioDivisor_add, ratioDivisor_add, ratioDivisor_chordRatio,
    ratioDivisor_chordRatio, ateLines_sum hQ, neg_frobenius_frobenius hQ, ratioDivisor,
    linesDivisor_lines, millerDivisor, ateDivisor, ateCoeffs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.iterate_zero,
    id_eq, Function.iterate_one, add_zero]
  module

/-- For every nonzero `z` in `Fp12`, `z^(N n) = 1`.

Here `n = s + p + p^8 - p^9` and `N = (p^12 - 1) / q`.

`q` divides `p^9 - p^8 - p - s`, so `p^12 - 1` divides `N n`. -/
theorem pow_ateExponent {z : Fp12} (hz : z ≠ 0) :
    z ^ ((FINAL_EXPONENT : ℤ) * ateExponent Fp.modulus ateCoeffs) = 1 := by
  have he : (FINAL_EXPONENT : ℤ) * ateExponent Fp.modulus ateCoeffs =
      ((Fp.modulus ^ 12 - 1 : ℕ) : ℤ) *
        -(((Fp.modulus ^ 9 - Fp.modulus ^ 8 - Fp.modulus - ATE_LOOP_COUNT) / Fr.modulus : ℕ) :
          ℤ) := by
    decide +kernel
  have h1 : z ^ (Fp.modulus ^ 12 - 1) = 1 := by
    rw [← card_eq]
    exact FiniteField.pow_card_sub_one_eq_one z hz
  rw [he, zpow_mul, zpow_natCast, h1, one_zpow]

/-- The exponent `(p^12 - 1) / q` of the final exponentiation is even. -/
theorem even_finalExponent : Even FINAL_EXPONENT :=
  Nat.even_iff.mpr (by decide +kernel)

/-- Take a point `Q` of the untwisted `G_2`.

Each line of the optimal ate function of `Q` passes through two points of that group. -/
theorem LinesIn.ateLines {Q : ambientCurve.Point} (hQ : Q ∈ g2Subgroup) :
    LinesIn g2Subgroup (ateLines Q) := by
  have h1 := frobenius_mem hQ
  have hs := g2Subgroup.nsmul_mem hQ ATE_LOOP_COUNT
  exact ((LinesIn.lines hQ _).add (LinesIn.chordRatio hs h1)).add
    (LinesIn.chordRatio (g2Subgroup.add_mem hs h1) (g2Subgroup.neg_mem (frobenius_mem h1)))

/-! ## Linearity -/

/-- The optimal ate function of `Q`, at `P`, raised to the exponent `(p^12 - 1) / q`. -/
noncomputable def ateValue (P Q : ambientCurve.Point) : Fp12 :=
  ratioAt (ateLines Q) P ^ FINAL_EXPONENT

/-- The ate value is linear in a point `P` that the Frobenius map fixes. -/
theorem ateValue_add_left {P₁ P₂ Q : ambientCurve.Point} (hP₁ : frobenius P₁ = P₁)
    (hP₂ : frobenius P₂ = P₂) (hQ : Q ∈ g2Subgroup) :
    ateValue (P₁ + P₂) Q = ateValue P₁ Q * ateValue P₂ Q :=
  pow_ratioAt_add_left primeFrobenius_apply (fun _ hR => eq_zero_of_frobenius_eq hR) hQ
    (LinesIn.ateLines hQ) (ratioDivisor_ateLines hQ) hP₁ hP₂ even_finalExponent
    fun _ hz => pow_ateExponent hz

/-- The ate value is linear in a point `Q` of the untwist of `G_2`. -/
theorem ateValue_add_right {P Q₁ Q₂ : ambientCurve.Point} (hP : frobenius P = P)
    (h₁ : Q₁ ∈ g2Subgroup) (h₂ : Q₂ ∈ g2Subgroup) :
    ateValue P (Q₁ + Q₂) = ateValue P Q₁ * ateValue P Q₂ :=
  pow_ratioAt_add_right primeFrobenius_apply (fun _ hR => frobenius_mem hR)
    (fun _ hR => eq_zero_of_frobenius_eq hR) h₁ h₂ (LinesIn.ateLines h₁)
    (LinesIn.ateLines h₂) (LinesIn.ateLines (g2Subgroup.add_mem h₁ h₂))
    (ratioDivisor_ateLines h₁) (ratioDivisor_ateLines h₂)
    (ratioDivisor_ateLines (g2Subgroup.add_mem h₁ h₂)) hP fun _ hz => pow_ateExponent hz

/-- The ate value of `n P` is the `n`-th power of that of `P`, when the Frobenius map fixes `P`. -/
theorem ateValue_nsmul_left {P Q : ambientCurve.Point} (hP : frobenius P = P)
    (hQ : Q ∈ g2Subgroup) (n : ℕ) : ateValue (n • P) Q = ateValue P Q ^ n := by
  induction n with
  | zero => simp [ateValue]
  | succ n ih =>
    rw [succ_nsmul, ateValue_add_left (by rw [map_nsmul, hP]) hP hQ, ih, pow_succ]

/-- The ate value at `Q = O` is 1, when the Frobenius map fixes `P`.

It is its own square.

It is not zero, since the only point of the untwist of `G_2` that the Frobenius map fixes is `O`. -/
theorem ateValue_zero_right {P : ambientCurve.Point} (hP : frobenius P = P) :
    ateValue P 0 = 1 := by
  have h := ateValue_add_right hP g2Subgroup.zero_mem g2Subgroup.zero_mem
  rw [add_zero] at h
  have hne : ateValue P 0 ≠ 0 := pow_ne_zero _
    ((LinesIn.ateLines g2Subgroup.zero_mem).ratioAt_ne_zero fun hR =>
      eq_zero_of_frobenius_eq hR hP)
  exact (mul_eq_left₀ hne).mp h.symm

/-- The ate value of `n Q` is the `n`-th power of that of `Q`, when the Frobenius map fixes `P`. -/
theorem ateValue_nsmul_right {P Q : ambientCurve.Point} (hP : frobenius P = P)
    (hQ : Q ∈ g2Subgroup) (n : ℕ) : ateValue P (n • Q) = ateValue P Q ^ n := by
  induction n with
  | zero => rw [zero_nsmul, ateValue_zero_right hP, pow_zero]
  | succ n ih =>
    rw [succ_nsmul, ateValue_add_right hP (g2Subgroup.nsmul_mem hQ n) hQ, ih, pow_succ]

/-! ## `G1` and the pairing -/

/-- The inclusion of `ZMod p`, the field of the curve, into `Fp12`. -/
noncomputable def ofZModHom : ZMod Fp.modulus →+* Fp12 where
  toFun a := ofFpHom (Fp.toZMod.symm a)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add]

/-- The inclusion agrees with that of `Fp`. -/
theorem ofZModHom_toZMod (a : Fp) : ofZModHom (Fp.toZMod a) = ofFpHom a :=
  congrArg ofFpHom (Fp.toZMod.symm_apply_apply a)

/-- The inclusion of the points of `G_1`, over `Fp`, into the points over `Fp12`. -/
noncomputable def g1Hom : curve.Point →+ ambientCurve.Point :=
  ShortWeierstrass.scaledHom ofZModHom one_ne_zero (by rw [one_pow, mul_one, map_ofNat])

/-- The inclusion keeps the coordinates of a finite point. -/
theorem g1Hom_some {x y : ZMod Fp.modulus} (h : curve.Nonsingular x y) {X Y : Fp12}
    (hX : ofZModHom x = X) (hY : ofZModHom y = Y) : ∃ h', g1Hom (.some x y h) = .some X Y h' := by
  subst hX hY
  have e : g1Hom (.some x y h) = .some (ofZModHom x * 1 ^ 2) (ofZModHom y * 1 ^ 3)
      (ShortWeierstrass.scaled_nonsingular ofZModHom 1 one_ne_zero
        (by rw [one_pow, mul_one, map_ofNat]) h) := rfl
  simp only [one_pow, mul_one] at e
  exact ⟨_, e⟩

/-- The Frobenius map fixes the points of `G_1`, because their coordinates lie in `Fp`. -/
theorem frobenius_g1Hom (P : curve.Point) : frobenius (g1Hom P) = g1Hom P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · have hf (a : ZMod Fp.modulus) : primeFrobenius (ofZModHom a) = ofZModHom a := by
      rw [primeFrobenius_apply, ← map_pow, ZMod.pow_card]
    obtain ⟨h', e⟩ := g1Hom_some h rfl rfl
    rw [e, mapPoint_some]
    simp only [hf]

/-- The final exponentiation sends to 1 the vertical through a nonzero point of the untwisted `G_2`.
-/
theorem finalExponentiation_line_neg_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup)
    (h0 : R ≠ 0) (xp yp : Fp) :
    finalExponentiation (Miller.line ambientCurve R (-R) (ofFpHom xp) (ofFpHom yp)) = 1 := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
  have hq : (0 : ℤ) < Fr.modulus := by decide
  set n := (k % Fr.modulus).toNat
  have hnk : (n : ℤ) = k % Fr.modulus := Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')
  have hn' : n < Fr.modulus := by
    have := Int.emod_lt_of_pos k hq
    omega
  have hkn : k • g2Point = n • g2Point := by
    rw [← natCast_zsmul, hnk]
    exact zsmul_eq_of_modEq (AddSubgroup.mem_zmultiples _) (Int.mod_modEq k _).symm
  rw [hkn] at h0 ⊢
  have hT := Point2.isOnCurve_mulBits 256 n Point2.isOnCurve_generator
  have hTp := Point2.toPoint_mulBits 256 n Point2.isOnCurve_generator
    (lt_trans hn' (by decide))
  have he : n • g2Point = untwist (Point2.mulBits 256 n Point2.generator).toPoint := by
    rw [hTp, map_nsmul]
    rfl
  rw [he] at h0 ⊢
  refine finalExponentiation_line_neg hT ?_ (fun h => h0 (by rw [h, map_zero])) xp yp
  rw [hTp, smul_comm, ← Point2.addOrderOf_generator, addOrderOf_nsmul_eq_zero, nsmul_zero]

/-- Take a finite point `P` on the curve, and a point `Q` on the twist whose untwist lies in `G_2`.

Their pairing is the ate value of their points over `Fp12`. -/
theorem pairing_eq_ateValue {xp yp : Fp} (hP : (Point.affine xp yp).isOnCurve = true)
    {Q : Point2} (hQ : Q.isOnCurve = true) (hG : untwist Q.toPoint ∈ g2Subgroup) :
    pairing (.affine xp yp) Q =
      ateValue (g1Hom (Point.affine xp yp).toPoint) (untwist Q.toPoint) := by
  by_cases h0 : untwist Q.toPoint = 0
  · have hQ0 : Q = .infinity := (Point2.toPoint_eq_zero hQ).mp
      (untwist_injective (by rw [h0, map_zero]))
    subst hQ0
    rw [h0, ateValue_zero_right (frobenius_g1Hom _)]
    rfl
  have hQr : Fr.modulus • Q.toPoint = 0 := by
    apply untwist_injective
    rw [map_nsmul, map_zero, ← addOrderOf_dvd_iff_nsmul_eq_zero]
    exact addOrderOf_dvd_of_mem hG
  rw [Point.toPoint_affine hP]
  obtain ⟨h, e⟩ := g1Hom_some (nonsingular_of ((Point.isOnCurve_affine xp yp).mp hP))
    (X := ofFpHom xp) (Y := ofFpHom yp) (ofZModHom_toZMod xp) (ofZModHom_toZMod yp)
  set Q' := untwist Q.toPoint
  have h1 : ATE_LOOP_COUNT • Q' + frobenius Q' ≠ 0 := by
    rw [frobenius_of_mem hG, ← natCast_zsmul, ← add_zsmul]
    exact zsmul_ne_zero_of_mem hG h0 (by decide +kernel)
  have h2 : ATE_LOOP_COUNT • Q' + frobenius Q' + -frobenius (frobenius Q') ≠ 0 := by
    rw [ateLines_sum hG, frobenius_iterate_of_mem hG]
    exact zsmul_ne_zero_of_mem hG h0 (by decide +kernel)
  have hm1 : ATE_LOOP_COUNT • Q' + frobenius Q' ∈ g2Subgroup :=
    g2Subgroup.add_mem (g2Subgroup.nsmul_mem hG _) (frobenius_mem hG)
  have hm2 : ATE_LOOP_COUNT • Q' + frobenius Q' + -frobenius (frobenius Q') ∈ g2Subgroup :=
    g2Subgroup.add_mem hm1 (g2Subgroup.neg_mem (frobenius_mem (frobenius_mem hG)))
  have hV1 := finalExponentiation_line_neg_of_mem hm1 h1 xp yp
  have hV2 := finalExponentiation_line_neg_of_mem hm2 h2 xp yp
  rw [finalExponentiation_eq_pow] at hV1 hV2
  rw [pairing_eq_finalExponentiation_loop hQ hQr xp yp, ← frobenius_eq_frobeniusHom, e, ateValue,
    ateLines, ratioAt_add, ratioAt_add, ratioAt_chordRatio, ratioAt_chordRatio, ratioAt,
    ← loop_eq_linesAt _ _ h, finalExponentiation_eq_pow]
  simp only [lineAt, mul_pow, div_pow, hV1, hV2, div_one]
  rfl

end Ate

open Ate

/-- A multiple `k g` of a point of order `q`, with `k < q`, is `O` only for `k = 0`. -/
private theorem val_eq_zero_of_nsmul {G : Type*} [AddCommGroup G] {g : G}
    (hg : addOrderOf g = Fr.modulus) (a : ZMod Fr.modulus) (h : a.val • g = 0) : a = 0 := by
  have hd := addOrderOf_dvd_of_nsmul_eq_zero h
  rw [hg] at hd
  exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt a))

/-- The pairing of alt_bn128 is bilinear on the multiples of the generators.

For all `a` and `b`, `e(a P1, b P2) = e(P1, P2)^(a b)`. -/
theorem pairingBilinear : PairingBilinear := by
  intro a b
  have hg1 := Point.isOnCurve_generator
  have hg2 := Point2.isOnCurve_generator
  have hP : Ate.frobenius (g1Hom Point.generator.toPoint) = g1Hom Point.generator.toPoint :=
    frobenius_g1Hom _
  have hQ : g2Point ∈ g2Subgroup := AddSubgroup.mem_zmultiples _
  have hG0 : g2Point ≠ 0 := fun h => by
    have h' := addOrderOf_g2Point
    rw [h, addOrderOf_zero] at h'
    exact absurd h' (by decide)
  have hPc := Point.isOnCurve_mulBits 256 a.val hg1
  have hPp := Point.toPoint_mulBits 256 a.val hg1 (lt_trans (ZMod.val_lt a) (by decide))
  have hQc := Point2.isOnCurve_mulBits 256 b.val hg2
  have hQp := Point2.toPoint_mulBits 256 b.val hg2 (lt_trans (ZMod.val_lt b) (by decide))
  by_cases ha : a = 0
  · subst ha
    have hi : Point.mulBits 256 (0 : ZMod Fr.modulus).val Point.generator = .infinity := by
      rw [← Point.toPoint_eq_zero hPc, hPp, ZMod.val_zero, zero_nsmul]
    rw [hi, ZMod.val_zero, zero_mul, pow_zero]
    rfl
  by_cases hb : b = 0
  · subst hb
    have hi : Point2.mulBits 256 (0 : ZMod Fr.modulus).val Point2.generator = .infinity := by
      rw [← Point2.toPoint_eq_zero hQc, hQp, ZMod.val_zero, zero_nsmul]
    rw [hi, ZMod.val_zero, mul_zero, pow_zero]
    cases Point.mulBits 256 a.val Point.generator <;> rfl
  obtain ⟨xp, yp, hxy⟩ : ∃ xp yp, Point.mulBits 256 a.val Point.generator = .affine xp yp := by
    cases h : Point.mulBits 256 a.val Point.generator with
    | infinity =>
      refine absurd (val_eq_zero_of_nsmul Point.addOrderOf_generator a ?_) ha
      rw [← hPp, h]
      rfl
    | affine x y => exact ⟨x, y, rfl⟩
  have hQ' : untwist (Point2.mulBits 256 b.val Point2.generator).toPoint = b.val • g2Point := by
    rw [hQp, map_nsmul]
    rfl
  have hQ0 : b.val • g2Point ≠ 0 := fun h =>
    hb (val_eq_zero_of_nsmul addOrderOf_g2Point b h)
  have hgg : pairing Point.generator Point2.generator =
      ateValue (g1Hom Point.generator.toPoint) g2Point :=
    pairing_eq_ateValue (xp := 1) (yp := 2) hg1 hg2 hQ
  rw [hxy, pairing_eq_ateValue (hxy ▸ hPc) hQc (hQ' ▸ g2Subgroup.nsmul_mem hQ _),
    ← hxy, hPp, map_nsmul, hQ', ateValue_nsmul_left hP (g2Subgroup.nsmul_mem hQ _),
    ateValue_nsmul_right hP hQ, hgg, ← pow_mul, mul_comm]

/-- The pairing law of EIP-197 holds with no hypothesis.

The check of the pairs `(a_i P1, b_i P2)` passes exactly when `sum_i a_i b_i = 0`. -/
theorem pairingLaws : PairingLaws :=
  PairingLaws.of_bilinear pairingBilinear

end EthLib.Cryptography.AltBn128
