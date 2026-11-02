module

public import EthLib.Execution.Fees.BaseFee

/-!
# Proofs: `BaseFee`

How far the base fee can move in one block.

The scaled distance is `base_fee * |used - target| / target`, and the fee moves by one eighth of it.

- At the target the fee stays.
- At or below the target it does not rise.
- Whatever the parent used, the fee falls by at most `base_fee / 8`.
- Above the target it rises, by at least 1.
- If the parent used at most twice its target, the fee rises by at most `max (base_fee / 8) 1`.
- An odd gas limit lets the parent use `2 * target + 1`, one more than twice its target.
  Up to the gas limit, the fee then rises by at most `max ((base_fee + base_fee / target) / 8) 1`.
- For a positive target, an empty parent, a parent at twice its target and a full parent with an odd gas limit reach these three upper bounds.
- With the same gas limit and base fee, a parent that used more gas never gives a lower fee.
- With the same gas limit and gas used, a parent with a higher base fee never gives a lower fee.
- A positive fee stays positive.

The known answers at the end are worked by hand, and each says what it pins.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BaseFee

/-! ## The three cases -/

/-- At the target, the base fee stays. -/
theorem calculateBaseFeePerGas_of_eq {parentGasLimit parentGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (h : parentGasUsed = parentGasLimit / ELASTICITY_MULTIPLIER) :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas = parentBaseFeePerGas := by
  simp [calculateBaseFeePerGas, h]

/-- Above the target, the base fee rises by the larger of one eighth of the scaled distance and 1. -/
theorem calculateBaseFeePerGas_of_gt {parentGasLimit parentGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (h : parentGasLimit / ELASTICITY_MULTIPLIER < parentGasUsed) :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas
      = parentBaseFeePerGas
        + max (parentBaseFeePerGas * (parentGasUsed - parentGasLimit / ELASTICITY_MULTIPLIER)
            / (parentGasLimit / ELASTICITY_MULTIPLIER) / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1 := by
  have hne : parentGasUsed ≠ parentGasLimit / ELASTICITY_MULTIPLIER := Nat.ne_of_gt h
  simp only [calculateBaseFeePerGas, hne, h, ↓reduceIte]

/-- Below the target, the base fee falls by one eighth of the scaled distance. -/
theorem calculateBaseFeePerGas_of_lt {parentGasLimit parentGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (h : parentGasUsed < parentGasLimit / ELASTICITY_MULTIPLIER) :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas
      = parentBaseFeePerGas
        - parentBaseFeePerGas * (parentGasLimit / ELASTICITY_MULTIPLIER - parentGasUsed)
            / (parentGasLimit / ELASTICITY_MULTIPLIER) / BASE_FEE_MAX_CHANGE_DENOMINATOR := by
  have hne : parentGasUsed ≠ parentGasLimit / ELASTICITY_MULTIPLIER := Nat.ne_of_lt h
  have hng : ¬ parentGasUsed > parentGasLimit / ELASTICITY_MULTIPLIER := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp only [calculateBaseFeePerGas, hne, hng, ↓reduceIte]

/-- At or below the target, the base fee does not rise. -/
theorem calculateBaseFeePerGas_le_self {parentGasLimit parentGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (h : parentGasUsed ≤ parentGasLimit / ELASTICITY_MULTIPLIER) :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas ≤ parentBaseFeePerGas := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · rw [calculateBaseFeePerGas_of_lt _ hlt]
    exact Nat.sub_le _ _
  · rw [calculateBaseFeePerGas_of_eq _ heq]
    exact Nat.le_refl _

/-! ## How far the fee moves -/

/-- `max x 1` grows with `x`. -/
private theorem max_one_le_max_one {x y : Nat} (h : x ≤ y) : max x 1 ≤ max y 1 :=
  Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

/-- A scaled distance is at most the fee if the distance is at most the target. -/
private theorem mul_div_le_of_le {fee delta target : Nat} (h : delta ≤ target) : fee * delta / target ≤ fee := by
  rcases Nat.eq_zero_or_pos target with h0 | hpos
  · simp [h0]
  · calc fee * delta / target ≤ fee * target / target := Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
      _ = fee := Nat.mul_div_cancel _ hpos

/-- The base fee falls by at most `base_fee / 8`, whatever the parent used. -/
theorem sub_calculateBaseFeePerGas_le (parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) :
    parentBaseFeePerGas - calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas
      ≤ parentBaseFeePerGas / BASE_FEE_MAX_CHANGE_DENOMINATOR := by
  rcases Nat.lt_or_ge parentGasUsed (parentGasLimit / ELASTICITY_MULTIPLIER) with hlt | hge
  · rw [calculateBaseFeePerGas_of_lt _ hlt]
    -- The distance below the target is at most the target, so the fall is at most one eighth of the fee.
    have hfall := Nat.div_le_div_right (c := BASE_FEE_MAX_CHANGE_DENOMINATOR)
      (mul_div_le_of_le (fee := parentBaseFeePerGas) (Nat.sub_le (parentGasLimit / ELASTICITY_MULTIPLIER) parentGasUsed))
    rw [Nat.sub_sub_self (Nat.le_trans hfall (Nat.div_le_self _ _))]
    exact hfall
  · rcases Nat.lt_or_eq_of_le hge with hgt | heq
    · rw [calculateBaseFeePerGas_of_gt _ hgt, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _)]
      exact Nat.zero_le _
    · rw [calculateBaseFeePerGas_of_eq _ heq.symm]
      simp

/-- Above the target, the base fee rises by at least 1. -/
theorem lt_calculateBaseFeePerGas {parentGasLimit parentGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (h : parentGasLimit / ELASTICITY_MULTIPLIER < parentGasUsed) :
    parentBaseFeePerGas < calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas := by
  rw [calculateBaseFeePerGas_of_gt _ h]
  exact Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))

/-- If the parent used at most twice its target, the base fee rises by at most `max (base_fee / 8) 1`. -/
theorem calculateBaseFeePerGas_le_of_le_two_mul {parentGasLimit parentGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (h : parentGasUsed ≤ 2 * (parentGasLimit / ELASTICITY_MULTIPLIER)) :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas
      ≤ parentBaseFeePerGas + max (parentBaseFeePerGas / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1 := by
  rcases Nat.lt_or_ge (parentGasLimit / ELASTICITY_MULTIPLIER) parentGasUsed with hgt | hle
  · rw [calculateBaseFeePerGas_of_gt _ hgt]
    -- The distance above the target is at most the target.
    have hrise := Nat.div_le_div_right (c := BASE_FEE_MAX_CHANGE_DENOMINATOR)
      (mul_div_le_of_le (fee := parentBaseFeePerGas)
        (show parentGasUsed - parentGasLimit / ELASTICITY_MULTIPLIER ≤ parentGasLimit / ELASTICITY_MULTIPLIER by omega))
    exact Nat.add_le_add_left (max_one_le_max_one hrise) _
  · exact Nat.le_trans (calculateBaseFeePerGas_le_self _ hle) (Nat.le_add_right _ _)

/-- For a positive target, the distance `target + 1` of a parent that used `2 * target + 1` gives the scaled distance `fee + fee / target`. -/
private theorem mul_succ_div {fee target : Nat} (h : 0 < target) : fee * (target + 1) / target = fee + fee / target := by
  rw [Nat.mul_succ, Nat.add_comm, Nat.add_mul_div_right _ _ h, Nat.add_comm]

/-- Up to the gas limit, the base fee rises by at most `max ((base_fee + base_fee / target) / 8) 1`.

An odd gas limit `2 * target + 1` lets the parent use one more than twice its target.

That extra unit of gas can add `base_fee / target` to the scaled distance.

For an even gas limit, `calculateBaseFeePerGas_le_of_le_two_mul` gives the tighter `max (base_fee / 8) 1`. -/
theorem calculateBaseFeePerGas_le_of_le_gasLimit {parentGasLimit parentGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (h : parentGasUsed ≤ parentGasLimit) :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas
      ≤ parentBaseFeePerGas
        + max ((parentBaseFeePerGas + parentBaseFeePerGas / (parentGasLimit / ELASTICITY_MULTIPLIER))
            / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1 := by
  rcases Nat.lt_or_ge (parentGasLimit / ELASTICITY_MULTIPLIER) parentGasUsed with hgt | hle
  · rw [calculateBaseFeePerGas_of_gt _ hgt]
    apply Nat.add_le_add_left
    apply max_one_le_max_one
    apply Nat.div_le_div_right
    rcases Nat.eq_zero_or_pos (parentGasLimit / ELASTICITY_MULTIPLIER) with h0 | hpos
    · -- A target of 0 makes the scaled distance 0, since `x / 0 = 0`.
      simp [h0]
    · -- The gas limit is at most `2 * target + 1`, so the distance is at most `target + 1`.
      have hdist : parentGasUsed - parentGasLimit / ELASTICITY_MULTIPLIER
          ≤ parentGasLimit / ELASTICITY_MULTIPLIER + 1 := by
        unfold ELASTICITY_MULTIPLIER at *
        omega
      calc parentBaseFeePerGas * (parentGasUsed - parentGasLimit / ELASTICITY_MULTIPLIER)
            / (parentGasLimit / ELASTICITY_MULTIPLIER)
          ≤ parentBaseFeePerGas * (parentGasLimit / ELASTICITY_MULTIPLIER + 1)
            / (parentGasLimit / ELASTICITY_MULTIPLIER) :=
            Nat.div_le_div_right (Nat.mul_le_mul_left _ hdist)
        _ = parentBaseFeePerGas + parentBaseFeePerGas / (parentGasLimit / ELASTICITY_MULTIPLIER) :=
            mul_succ_div hpos
  · exact Nat.le_trans (calculateBaseFeePerGas_le_self _ hle) (Nat.le_add_right _ _)

/-! ## The bounds are reached -/

/-- For a positive target, an empty parent lowers the base fee by exactly `base_fee / 8`. -/
theorem calculateBaseFeePerGas_empty {parentGasLimit : Nat} (parentBaseFeePerGas : Nat)
    (h : 0 < parentGasLimit / ELASTICITY_MULTIPLIER) :
    calculateBaseFeePerGas parentGasLimit 0 parentBaseFeePerGas
      = parentBaseFeePerGas - parentBaseFeePerGas / BASE_FEE_MAX_CHANGE_DENOMINATOR := by
  rw [calculateBaseFeePerGas_of_lt _ h, Nat.sub_zero, Nat.mul_div_cancel _ h]

/-- For a positive target, a parent at twice its target raises the base fee by exactly `max (base_fee / 8) 1`. -/
theorem calculateBaseFeePerGas_two_mul {parentGasLimit : Nat} (parentBaseFeePerGas : Nat)
    (h : 0 < parentGasLimit / ELASTICITY_MULTIPLIER) :
    calculateBaseFeePerGas parentGasLimit (2 * (parentGasLimit / ELASTICITY_MULTIPLIER)) parentBaseFeePerGas
      = parentBaseFeePerGas + max (parentBaseFeePerGas / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1 := by
  rw [calculateBaseFeePerGas_of_gt _ (by omega)]
  rw [show 2 * (parentGasLimit / ELASTICITY_MULTIPLIER) - parentGasLimit / ELASTICITY_MULTIPLIER
      = parentGasLimit / ELASTICITY_MULTIPLIER by omega, Nat.mul_div_cancel _ h]

/-- For a positive target, a full parent with an odd gas limit raises the base fee by exactly `max ((base_fee + base_fee / target) / 8) 1`. -/
theorem calculateBaseFeePerGas_odd_full {parentGasLimit : Nat} (parentBaseFeePerGas : Nat)
    (hodd : parentGasLimit % 2 = 1) (h : 0 < parentGasLimit / ELASTICITY_MULTIPLIER) :
    calculateBaseFeePerGas parentGasLimit parentGasLimit parentBaseFeePerGas
      = parentBaseFeePerGas
        + max ((parentBaseFeePerGas + parentBaseFeePerGas / (parentGasLimit / ELASTICITY_MULTIPLIER))
            / BASE_FEE_MAX_CHANGE_DENOMINATOR) 1 := by
  -- An odd gas limit is `2 * target + 1`, so a full parent is `target + 1` above its target.
  have hdist : parentGasLimit - parentGasLimit / ELASTICITY_MULTIPLIER
      = parentGasLimit / ELASTICITY_MULTIPLIER + 1 := by
    unfold ELASTICITY_MULTIPLIER at *
    omega
  rw [calculateBaseFeePerGas_of_gt _ (by omega), hdist, mul_succ_div h]

/-! ## Monotonicity and positivity -/

/-- With the same gas limit and base fee, a parent that used more gas never gives a lower base fee. -/
theorem calculateBaseFeePerGas_mono (parentGasLimit : Nat) {parentGasUsed parentGasUsed' : Nat}
    (parentBaseFeePerGas : Nat) (h : parentGasUsed ≤ parentGasUsed') :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas
      ≤ calculateBaseFeePerGas parentGasLimit parentGasUsed' parentBaseFeePerGas := by
  rcases Nat.lt_or_ge (parentGasLimit / ELASTICITY_MULTIPLIER) parentGasUsed' with hgt' | hle'
  · rcases Nat.lt_or_ge (parentGasLimit / ELASTICITY_MULTIPLIER) parentGasUsed with hgt | hle
    · -- Both above the target: the larger distance gives the larger rise.
      rw [calculateBaseFeePerGas_of_gt _ hgt, calculateBaseFeePerGas_of_gt _ hgt']
      apply Nat.add_le_add_left
      apply max_one_le_max_one
      apply Nat.div_le_div_right
      apply Nat.div_le_div_right
      exact Nat.mul_le_mul_left _ (by omega)
    · -- Only the second is above the target.
      exact Nat.le_trans (calculateBaseFeePerGas_le_self _ hle)
        (Nat.le_of_lt (lt_calculateBaseFeePerGas _ hgt'))
  · rcases Nat.lt_or_eq_of_le hle' with hlt' | heq'
    · -- Both below the target: the smaller distance gives the smaller fall.
      rw [calculateBaseFeePerGas_of_lt _ (Nat.lt_of_le_of_lt h hlt'), calculateBaseFeePerGas_of_lt _ hlt']
      apply Nat.sub_le_sub_left
      apply Nat.div_le_div_right
      apply Nat.div_le_div_right
      exact Nat.mul_le_mul_left _ (by omega)
    · -- The second is at the target.
      rw [calculateBaseFeePerGas_of_eq _ heq']
      exact calculateBaseFeePerGas_le_self _ (by omega)

/-- With the same gas limit and gas used, a parent with a higher base fee never gives a lower base fee.

Below the target, each extra unit of the parent's fee adds at most 1 to the scaled distance, so at most 1 to the fall. -/
theorem calculateBaseFeePerGas_mono_baseFee (parentGasLimit parentGasUsed : Nat)
    {parentBaseFeePerGas parentBaseFeePerGas' : Nat} (h : parentBaseFeePerGas ≤ parentBaseFeePerGas') :
    calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas
      ≤ calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas' := by
  rcases Nat.lt_or_ge parentGasUsed (parentGasLimit / ELASTICITY_MULTIPLIER) with hlt | hge
  · rw [calculateBaseFeePerGas_of_lt _ hlt, calculateBaseFeePerGas_of_lt _ hlt]
    have hpos : 0 < parentGasLimit / ELASTICITY_MULTIPLIER := by omega
    generalize parentGasLimit / ELASTICITY_MULTIPLIER = target at hlt hpos ⊢
    have hdist : target - parentGasUsed ≤ target := Nat.sub_le _ _
    -- The scaled distance of the higher fee exceeds the other by at most the difference of the fees.
    have hstep : parentBaseFeePerGas' * (target - parentGasUsed) / target
        ≤ parentBaseFeePerGas * (target - parentGasUsed) / target + (parentBaseFeePerGas' - parentBaseFeePerGas) := by
      calc parentBaseFeePerGas' * (target - parentGasUsed) / target
          = (parentBaseFeePerGas * (target - parentGasUsed)
              + (parentBaseFeePerGas' - parentBaseFeePerGas) * (target - parentGasUsed)) / target := by
            rw [← Nat.add_mul, Nat.add_sub_cancel' h]
        _ ≤ (parentBaseFeePerGas * (target - parentGasUsed)
              + (parentBaseFeePerGas' - parentBaseFeePerGas) * target) / target :=
            Nat.div_le_div_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hdist) _)
        _ = parentBaseFeePerGas * (target - parentGasUsed) / target + (parentBaseFeePerGas' - parentBaseFeePerGas) :=
            Nat.add_mul_div_right _ _ hpos
    -- Each scaled distance is at most its fee.
    have hle := mul_div_le_of_le (fee := parentBaseFeePerGas) hdist
    have hle' := mul_div_le_of_le (fee := parentBaseFeePerGas') hdist
    generalize parentBaseFeePerGas * (target - parentGasUsed) / target = scaled at hstep hle ⊢
    generalize parentBaseFeePerGas' * (target - parentGasUsed) / target = scaled' at hstep hle' ⊢
    unfold BASE_FEE_MAX_CHANGE_DENOMINATOR
    omega
  · rcases Nat.lt_or_eq_of_le hge with hgt | heq
    · -- Above the target, the higher fee gives the larger rise.
      rw [calculateBaseFeePerGas_of_gt _ hgt, calculateBaseFeePerGas_of_gt _ hgt]
      exact Nat.add_le_add h (max_one_le_max_one
        (Nat.div_le_div_right (Nat.div_le_div_right (Nat.mul_le_mul_right _ h))))
    · rw [calculateBaseFeePerGas_of_eq _ heq.symm, calculateBaseFeePerGas_of_eq _ heq.symm]
      exact h

/-- A positive base fee stays positive. -/
theorem calculateBaseFeePerGas_pos (parentGasLimit parentGasUsed : Nat) {parentBaseFeePerGas : Nat}
    (h : 0 < parentBaseFeePerGas) :
    0 < calculateBaseFeePerGas parentGasLimit parentGasUsed parentBaseFeePerGas := by
  -- The fall is at most `base_fee / 8`, which is below a positive fee.
  have hfall := sub_calculateBaseFeePerGas_le parentGasLimit parentGasUsed parentBaseFeePerGas
  have heighth : parentBaseFeePerGas / BASE_FEE_MAX_CHANGE_DENOMINATOR < parentBaseFeePerGas :=
    Nat.div_lt_self h (by decide)
  omega

/-! ## Known answers

The first eight are worked by hand from the formula of EIP-1559.

The last pins this definition at a target of 0, where that formula divides by zero.

The first five use a gas limit of 30,000,000, so a target of 15,000,000, and a base fee of 10 gwei. -/

/-- A parent at its target keeps the base fee. -/
example : calculateBaseFeePerGas 30000000 15000000 10000000000 = 10000000000 := by decide +kernel

/-- A full parent, twice its target: `10^10 * 15000000 / 15000000 / 8 = 1250000000`. -/
example : calculateBaseFeePerGas 30000000 30000000 10000000000 = 11250000000 := by decide +kernel

/-- An empty parent: the fee falls by the same 1,250,000,000. -/
example : calculateBaseFeePerGas 30000000 0 10000000000 = 8750000000 := by decide +kernel

/-- 20,000,000 gas used: `10^10 * 5000000 / 15000000 = 3333333333`, and `/ 8` gives 416,666,666. -/
example : calculateBaseFeePerGas 30000000 20000000 10000000000 = 10416666666 := by decide +kernel

/-- 10,000,000 gas used: the fall is the same 416,666,666. -/
example : calculateBaseFeePerGas 30000000 10000000 10000000000 = 9583333334 := by decide +kernel

/-- A fee of 7, with gas used one unit above the target: `7 * 1 / 15000000 / 8 = 0`, so `max 0 1` raises it by 1. -/
example : calculateBaseFeePerGas 30000000 15000001 7 = 8 := by decide +kernel

/-- A fee of 7, with gas used one unit below the target: the fall rounds down to 0, so the fee stays. -/
example : calculateBaseFeePerGas 30000000 14999999 7 = 7 := by decide +kernel

/-- An odd gas limit of 30,000,001, full: the parent used 15,000,001 over its target of 15,000,000.

With a fee of `120000000 = 8 * 15000000`, the rise is `120000000 * 15000001 / 15000000 / 8`.

That is `120000008 / 8 = 15000001`, one more than `120000000 / 8`. -/
example : calculateBaseFeePerGas 30000001 30000001 120000000 = 135000001 := by decide +kernel

/-- A gas limit of 1, so a target of 0: `x / 0 = 0` makes the rise `max (0 / 8) 1 = 1`.

In execution-specs, `check_gas_limit` rejects every block whose parent has this gas limit, before `calculate_base_fee_per_gas` divides by the target. -/
example : calculateBaseFeePerGas 1 1 100 = 101 := by decide +kernel

end EthLib.Execution.Fees.BaseFee
