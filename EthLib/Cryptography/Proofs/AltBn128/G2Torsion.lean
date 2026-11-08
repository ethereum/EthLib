module

public import EthLib.Cryptography.Proofs.AltBn128.G2Order
public import Mathlib.Data.Fintype.Option

/-!
# Proofs: the points of order `q` on the twist form `G_2`

[EIP-197][eip197] says that `G_2` is the only group of order `q` on the twist over `Fp2`.

This file proves it: a point `Q` of the twist has `q Q = O` exactly when it is a multiple of `P2`.

The proof does not count the points of the twist.

A point is fixed by its `x` and a sign of its `y`, so the twist has at most `2 p^2 + 1` points.

The kernel checks a point of prime order `10069` on the twist, and `P2` has order `q`.

So the number of points is a multiple of `10069 q`.

If `q^2` divided it, then `10069 q^2` would too, but `10069 q^2 > 2 p^2 + 1`.

The points killed by `q` form a group, and its order is a power of `q` that divides that number.

So that group has at most `q` elements, and it holds the `q` multiples of `P2`.

Source: [EIP-197][eip197], section Definition of the groups.

[eip197]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-197.md#definition-of-the-groups
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

open WeierstrassCurve

/-! ## At most `2 p^2 + 1` points -/

namespace Fp2

/-- `Fp2` as the pairs of its two coefficients. -/
def equivProd : Fp2 ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Finite Fp2 := Finite.of_equiv _ equivProd.symm

theorem card_eq : Nat.card Fp2 = Fp.modulus * Fp.modulus := by
  rw [Nat.card_congr equivProd, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- A sign of an element: the parity of `c0`, or of `c1` when `c0 = 0`. -/
def sign (y : Fp2) : Bool :=
  if y.c0 = 0 then y.c1.val % 2 == 1 else y.c0.val % 2 == 1

/-- `a` and `-a` have opposite parities in `Fp`, unless `a = 0`, since `p` is odd. -/
private theorem val_neg_mod_two {a : Fp} (ha : a ≠ 0) : (-a).val % 2 ≠ a.val % 2 := by
  have hpos : 0 < a.val := Nat.pos_of_ne_zero fun h => ha (Fin.ext h)
  have hval : (-a).val = Fp.modulus - a.val := by
    rw [Fin.val_neg', Nat.mod_eq_of_lt]
    omega
  have hlt := a.isLt
  have hodd : Fp.modulus % 2 = 1 := by decide
  omega

/-- Two numbers of opposite parities give opposite tests of oddness. -/
private theorem beq_one_ne {a b : Nat} (h : a % 2 ≠ b % 2) : (a % 2 == 1) ≠ (b % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all

/-- A nonzero element and its negation have opposite signs. -/
theorem sign_neg {y : Fp2} (hy : y ≠ 0) : sign (-y) ≠ sign y := by
  have hc0 : (-y).c0 = -y.c0 := rfl
  have hc1 : (-y).c1 = -y.c1 := rfl
  unfold sign
  rw [hc0, hc1]
  by_cases h0 : y.c0 = 0
  · have h1 : y.c1 ≠ 0 := fun h1 => hy (ext h0 h1)
    rw [ite_eq_left (neg_eq_zero.mpr h0), ite_eq_left h0]
    exact beq_one_ne (val_neg_mod_two h1)
  · rw [ite_eq_right (mt neg_eq_zero.mp h0), ite_eq_right h0]
    exact beq_one_ne (val_neg_mod_two h0)

end Fp2

namespace Point2

/-- A group element of the twist as its `x` and the sign of its `y`, or `none` for `0`. -/
def pointCode : twist.Point → Option (Fp2 × Bool)
  | 0 => none
  | .some x y _ => some (x, Fp2.sign y)

theorem pointCode_injective : Function.Injective pointCode := by
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some => cases h
  | some x1 y1 h1 => cases Q with
    | zero => cases h
    | some x2 y2 h2 =>
      simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hs⟩ := h
      -- Two roots of one `x^3 + b2` are equal or opposite, and opposite roots differ in sign.
      have e1 := (twist_equation_iff _ _).mp h1.1
      have e2 := (twist_equation_iff _ _).mp h2.1
      have hy : y1 = y2 := by
        rcases mul_self_eq_mul_self_iff.mp (e1.trans e2.symm) with h | h
        · exact h
        · by_cases hz : y2 = 0
          · rw [h, hz, neg_zero]
          · exact absurd (h ▸ hs) (Fp2.sign_neg hz)
      subst hy
      rfl

instance : Finite twist.Point := Finite.of_injective _ pointCode_injective

/-- The twist over `Fp2` has at most `2 p^2 + 1` points. -/
theorem card_point_le : Nat.card twist.Point ≤ 2 * (Fp.modulus * Fp.modulus) + 1 := by
  have := Nat.card_le_card_of_injective _ pointCode_injective
  rwa [Finite.card_option, Nat.card_prod, Fp2.card_eq, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, mul_comm] at this

/-! ## A point of order `10069` -/

/-- A point of the twist of prime order `10069`.

Any point of that order would do, and the kernel checks this one. -/
def torsionWitness : Point2 :=
  affine
    ⟨15149523961633404972988025896028320971714458845511211917740067536580146327169,
      1735419755277546621153711394301804950753311953601132873852953942981222781231⟩
    ⟨19708715795314625321786836131027732252052916014094444083338561104342248597196,
      9594937902945310003264004071077143592487355200882289385935083565717474466459⟩

theorem isOnCurve_torsionWitness : torsionWitness.isOnCurve = true := by decide +kernel

theorem torsionWitness_ne_infinity : torsionWitness ≠ infinity := by decide

/-- `10069 R = O`, as the kernel computes it by double and add. -/
theorem mulBits_torsionWitness : mulBits 14 10069 torsionWitness = infinity := by
  decide +kernel

theorem prime_10069 : Nat.Prime 10069 := by norm_num

/-- The witness has order `10069`. -/
theorem addOrderOf_torsionWitness : addOrderOf (toPoint torsionWitness) = 10069 := by
  have : Fact (Nat.Prime 10069) := ⟨prime_10069⟩
  refine addOrderOf_eq_prime ?_ fun h =>
    torsionWitness_ne_infinity ((toPoint_eq_zero isOnCurve_torsionWitness).mp h)
  rw [← toPoint_mulBits 14 _ isOnCurve_torsionWitness (by decide), mulBits_torsionWitness]
  rfl

/-! ## The points killed by `q` -/

/-- `q^2` does not divide the number of points of the twist. -/
theorem not_sq_dvd_card_point : ¬Fr.modulus * Fr.modulus ∣ Nat.card twist.Point := by
  intro hsq
  have h1 : 10069 ∣ Nat.card twist.Point :=
    addOrderOf_torsionWitness ▸ addOrderOf_dvd_natCard _
  -- `q^2` and `10069` are coprime, so their product divides the number of points.
  have hcop1 : Nat.Coprime Fr.modulus 10069 := by decide
  have hcop : Nat.Coprime (Fr.modulus * Fr.modulus) 10069 :=
    Nat.coprime_mul_iff_left.mpr ⟨hcop1, hcop1⟩
  have hdvd := hcop.mul_dvd_of_dvd_of_dvd hsq h1
  have hle := Nat.le_of_dvd Nat.card_pos hdvd
  have hmax := card_point_le
  have hlt : 2 * (Fp.modulus * Fp.modulus) + 1 < Fr.modulus * Fr.modulus * 10069 := by decide
  omega

/-- The points killed by `q`. -/
def torsion : AddSubgroup twist.Point := (nsmulAddMonoidHom (α := twist.Point) Fr.modulus).ker

theorem mem_torsion {X : twist.Point} : X ∈ torsion ↔ Fr.modulus • X = 0 := by
  simp [torsion]

theorem zmultiples_generator_le_torsion : AddSubgroup.zmultiples (toPoint generator) ≤ torsion :=
  (AddSubgroup.zmultiples_le_of_mem (mem_torsion.mpr
    (addOrderOf_generator ▸ addOrderOf_nsmul_eq_zero _)))

/-- The points killed by `q` are the multiples of `P2`. -/
theorem torsion_eq_zmultiples_generator : torsion = AddSubgroup.zmultiples (toPoint generator) := by
  have hq : Fr.modulus.Prime := Fr.modulus_prime
  -- Each prime factor of the order of the group is the order of one of its points, so it is `q`.
  have hpow : ∀ {d : Nat}, d.Prime → d ∣ Nat.card torsion → d = Fr.modulus := by
    intro d hd hdvd
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨X, hX⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    have hdq : d ∣ Fr.modulus := by
      rw [← hX, addOrderOf_dvd_iff_nsmul_eq_zero]
      exact Subtype.ext (mem_torsion.mp X.2)
    exact (Nat.prime_dvd_prime_iff_eq hd hq).mp hdq
  obtain ⟨k, hk⟩ : ∃ k, Nat.card torsion = Fr.modulus ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hpow⟩
  -- The order divides the number of points, so it is not a multiple of `q^2`.
  have hk1 : k ≤ 1 := by
    by_contra hc
    have hdvd : Fr.modulus * Fr.modulus ∣ Nat.card torsion :=
      hk ▸ (Nat.pow_two Fr.modulus ▸ Nat.pow_dvd_pow _ (by omega))
    exact not_sq_dvd_card_point (hdvd.trans (AddSubgroup.card_addSubgroup_dvd_card _))
  have hcard : Nat.card torsion ≤ Nat.card (AddSubgroup.zmultiples (toPoint generator)) := by
    rw [Nat.card_zmultiples, addOrderOf_generator, hk]
    calc Fr.modulus ^ k ≤ Fr.modulus ^ 1 := Nat.pow_le_pow_right hq.pos hk1
      _ = Fr.modulus := pow_one _
  exact (AddSubgroup.eq_of_le_of_card_ge zmultiples_generator_le_torsion hcard).symm

/-- A group element of the twist is killed by `q` exactly when it is a multiple of `P2`. -/
theorem nsmul_order_eq_zero_iff (X : twist.Point) :
    Fr.modulus • X = 0 ↔ X ∈ AddSubgroup.zmultiples (toPoint generator) := by
  rw [← mem_torsion, torsion_eq_zmultiples_generator]

/-- A point on the twist passes the subgroup check of ECPAIRING exactly when it is `k P2`, `k < q`.

So the check accepts exactly the points of `G_2`. -/
theorem mulBits_order_eq_infinity_iff_exists {p : Point2} (hp : p.isOnCurve = true) :
    mulBits 256 Fr.modulus p = infinity ↔ ∃ k < Fr.modulus, p = mulBits 256 k generator := by
  rw [mulBits_order_eq_infinity_iff hp, nsmul_order_eq_zero_iff]
  constructor
  · intro hmem
    -- An integer multiple of `P2` is a natural multiple, and the scalar reduces mod `q`.
    obtain ⟨n, hn⟩ := (isOfFinAddOrder_of_finite _).mem_multiples_iff_mem_zmultiples.mpr hmem
    have hpos : 0 < Fr.modulus := Fr.modulus_prime.pos
    have hlt : n % Fr.modulus < Fr.modulus := Nat.mod_lt _ hpos
    refine ⟨n % Fr.modulus, hlt, (toPoint_inj hp (isOnCurve_mulBits _ _ isOnCurve_generator)).mp ?_⟩
    rw [toPoint_mulBits _ _ isOnCurve_generator (lt_trans hlt (by decide)), ← addOrderOf_generator,
      mod_addOrderOf_nsmul]
    exact hn.symm
  · rintro ⟨k, hk, rfl⟩
    rw [toPoint_mulBits _ _ isOnCurve_generator (lt_trans hk (by decide))]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) k

end Point2

end EthLib.Cryptography.AltBn128
