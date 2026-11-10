module

public import EthLib.Execution.Fees.GasLimit
public import EthLib.Base.Proofs.Fork
public import EthLib.Base.Proofs.GasLimit

/-!
# Proofs: the gas limit rule

The rule holds exactly when the gas limit is within a 1024th of the parent's, and at least 5000.

Each block then multiplies the gas limit by less than `1025 / 1024`, and by more than `1023 / 1024`.

So `k` blocks multiply it by at most `(1025 / 1024)^k`.

At the first London block, the rule reads twice the parent's gas limit.

So that block may double the gas limit, which no other block may do.

A gas limit that moves toward a target of at least 5000 follows the rule.

A target that the rule allows is the gas limit itself.
-/

@[expose] public section

namespace EthLib.Execution.Fees.GasLimit

/-- The rule, in plain inequalities. -/
theorem checkGasLimit_iff (gasLimit parentGasLimit : Nat) :
    checkGasLimit gasLimit parentGasLimit = true ↔
      gasLimit < parentGasLimit + parentGasLimit / 1024 ∧
        parentGasLimit - parentGasLimit / 1024 < gasLimit ∧ 5000 ≤ gasLimit := by
  unfold checkGasLimit LIMIT_ADJUSTMENT_FACTOR LIMIT_MINIMUM
  simp only [Bool.and_eq_true, and_assoc]
  exact ⟨fun ⟨a, b, c⟩ => ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c⟩,
    fun ⟨a, b, c⟩ => ⟨decide_eq_true a, decide_eq_true b, decide_eq_true c⟩⟩

/-- One block multiplies the gas limit by less than `1025 / 1024`. -/
theorem mul_lt_of_checkGasLimit {gasLimit parentGasLimit : Nat}
    (h : checkGasLimit gasLimit parentGasLimit = true) :
    1024 * gasLimit < 1025 * parentGasLimit := by
  have hUp := ((checkGasLimit_iff _ _).mp h).1
  have hDiv := Nat.div_mul_le_self parentGasLimit 1024
  omega

/-- One block multiplies the gas limit by more than `1023 / 1024`. -/
theorem lt_mul_of_checkGasLimit {gasLimit parentGasLimit : Nat}
    (h : checkGasLimit gasLimit parentGasLimit = true) :
    1023 * parentGasLimit < 1024 * gasLimit := by
  have hDown := ((checkGasLimit_iff _ _).mp h).2.1
  have hDiv := Nat.div_mul_le_self parentGasLimit 1024
  omega

/-- After `k` blocks that each follow the rule, the gas limit grows by `(1025 / 1024)^k` at most. -/
theorem pow_mul_le_of_checkGasLimit (limit : Nat → Nat) :
    ∀ k : Nat, (∀ i < k, checkGasLimit (limit (i + 1)) (limit i) = true) →
      1024 ^ k * limit k ≤ 1025 ^ k * limit 0
  | 0, _ => by simp
  | k + 1, h => by
    have ih := pow_mul_le_of_checkGasLimit limit k fun i hi => h i (by omega)
    have hStep := mul_lt_of_checkGasLimit (h k (by omega))
    -- One more block: `1024 * limit (k + 1) < 1025 * limit k`, scaled by `1024^k`.
    calc 1024 ^ (k + 1) * limit (k + 1)
        = 1024 ^ k * (1024 * limit (k + 1)) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 1024 ^ k * (1025 * limit k) := Nat.mul_le_mul_left _ (Nat.le_of_lt hStep)
      _ = 1025 * (1024 ^ k * limit k) := by rw [Nat.mul_left_comm]
      _ ≤ 1025 * (1025 ^ k * limit 0) := Nat.mul_le_mul_left _ ih
      _ = 1025 ^ (k + 1) * limit 0 := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm 1025]

/-! ## The first London block -/

open EthLib.Base

variable {parentFork fork : Fork}

/-- At the first London block, the rule reads twice the parent's gas limit. -/
theorem parentGasLimitForCheck_of_first_london (hParent : parentFork < .london)
    (hFork : .london ≤ fork) (parentGasLimit : Nat) :
    parentGasLimitForCheck parentFork fork parentGasLimit = 2 * parentGasLimit := by
  simp [parentGasLimitForCheck, hParent, hFork, BaseFee.ELASTICITY_MULTIPLIER, Nat.mul_comm]

/-- At any other block, the rule reads the parent's gas limit. -/
theorem parentGasLimitForCheck_of_not_first_london
    (h : ¬(parentFork < .london ∧ .london ≤ fork)) (parentGasLimit : Nat) :
    parentGasLimitForCheck parentFork fork parentGasLimit = parentGasLimit := by
  simp only [parentGasLimitForCheck, h, ↓reduceIte]

/-- Once the parent is at London or later, the rule is the plain rule. -/
theorem checkGasLimitAcross_of_london_le (h : .london ≤ parentFork)
    (gasLimit parentGasLimit : Nat) :
    checkGasLimitAcross parentFork fork gasLimit parentGasLimit =
      checkGasLimit gasLimit parentGasLimit := by
  rw [checkGasLimitAcross, parentGasLimitForCheck_of_not_first_london]
  exact fun ⟨hlt, _⟩ => absurd h (Nat.not_le_of_lt hlt)

/-- The first London block may double the gas limit of a parent of at least 2500. -/
theorem checkGasLimitAcross_double (hParent : parentFork < .london) (hFork : .london ≤ fork)
    {parentGasLimit : Nat} (h : 2500 ≤ parentGasLimit) :
    checkGasLimitAcross parentFork fork (2 * parentGasLimit) parentGasLimit = true := by
  rw [checkGasLimitAcross, parentGasLimitForCheck_of_first_london hParent hFork,
    checkGasLimit_iff]
  -- A 1024th of twice the limit is at least 4, so the doubled limit is strictly inside.
  have : 4 ≤ 2 * parentGasLimit / 1024 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  omega

/-- No block after a London parent may double a positive gas limit. -/
theorem checkGasLimitAcross_double_of_london_le (h : .london ≤ parentFork)
    {parentGasLimit : Nat} (hPos : 0 < parentGasLimit) :
    checkGasLimitAcross parentFork fork (2 * parentGasLimit) parentGasLimit = false := by
  rw [checkGasLimitAcross_of_london_le h]
  -- A 1024th of the limit is below the limit, so twice the limit is too far above it.
  have : parentGasLimit / 1024 < parentGasLimit := Nat.div_lt_self hPos (by decide)
  cases hc : checkGasLimit (2 * parentGasLimit) parentGasLimit
  · rfl
  · have := ((checkGasLimit_iff _ _).mp hc).1
    omega

/-! ## The gas limit toward a target -/

/-- The gas limit toward a target of at least 5000 follows the rule, after a parent of 5000 or more.
-/
theorem checkGasLimit_gasLimitToward {parentGasLimit target : Nat}
    (hParent : LIMIT_MINIMUM ≤ parentGasLimit) (hTarget : LIMIT_MINIMUM ≤ target) :
    checkGasLimit (Base.gasLimitToward parentGasLimit target) parentGasLimit = true := by
  rw [checkGasLimit_iff]
  unfold LIMIT_MINIMUM at hParent hTarget
  have := Base.gasLimitToward_bounds parentGasLimit target
  -- A parent of at least 5000 has a 1024th of at least 4, so one step stays strictly inside.
  have : 4 ≤ parentGasLimit / 1024 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  refine ⟨by omega, by omega, ?_⟩
  unfold Base.gasLimitToward
  dsimp only
  split
  · omega
  · split <;> omega

/-- A target that the rule allows after the parent is the gas limit toward it. -/
theorem gasLimitToward_of_checkGasLimit {parentGasLimit target : Nat}
    (h : checkGasLimit target parentGasLimit = true) :
    Base.gasLimitToward parentGasLimit target = target := by
  have := (checkGasLimit_iff _ _).mp h
  exact Base.gasLimitToward_of_le_of_le (by omega) (by omega)

end EthLib.Execution.Fees.GasLimit
