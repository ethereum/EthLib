module

public import EthLib.Execution.Fees.GasLimit

/-!
# Proofs: the gas limit rule

The rule holds exactly when the gas limit is within a 1024th of the parent's, and at least 5000.

Each block then multiplies the gas limit by less than `1025 / 1024`, and by more than `1023 / 1024`.

So `k` blocks multiply it by at most `(1025 / 1024)^k`.
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

end EthLib.Execution.Fees.GasLimit
