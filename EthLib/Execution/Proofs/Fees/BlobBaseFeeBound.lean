module

public import EthLib.Execution.Proofs.Fees.BlobBaseFee
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proofs: the size and the steps of the blob fee exponential

Write `c` for `⌈numerator / denominator⌉`, which is `(numerator + denominator - 1) / denominator`.

- From step `⌈2 * numerator / denominator⌉` on, each step at least halves the accumulator.
- The result is at most `factor * 3^c`, since the Taylor series of `e^x` stays below `3^⌈x⌉`.
- Every accumulator is at most `factor * denominator * 3^c`.
- Up to 46 update fractions of at most `2^24`, the accumulators, products and sums fit 128 bits.

The bounds read the integer loop through the real exponential, so this file imports Mathlib.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

open EthLib.Base

variable {factor numerator denominator : Nat}

/-- Once the divisor `denominator * (k + 1)` is at least twice the numerator, a step halves.

That holds by step `⌈2 * numerator / denominator⌉`, at or before step `2 * numerator`. -/
theorem accum_succ_le_half_of_le_mul {k : Nat} (hk : 2 * numerator ≤ denominator * (k + 1)) :
    accum factor numerator denominator (k + 1) ≤ accum factor numerator denominator k / 2 := by
  rcases Nat.eq_zero_or_pos numerator with hn | hn
  · -- A numerator of 0 makes the next accumulator 0.
    simp [accum, hn]
  show accum factor numerator denominator k * numerator / (denominator * (k + 1))
    ≤ accum factor numerator denominator k / 2
  calc accum factor numerator denominator k * numerator / (denominator * (k + 1))
      ≤ accum factor numerator denominator k * numerator / (2 * numerator) :=
        Nat.div_le_div_left hk (by omega)
    _ = accum factor numerator denominator k / 2 := Nat.mul_div_mul_right _ _ hn

/-- After `k` steps, the accumulator is at most `f * d * n^k / (d^k * k!)`.

Here `n`, `d` and `f` are the numerator, the denominator and the factor.

Each step divides by `denominator * (k + 1)` and rounds down, which only lowers it. -/
theorem accum_mul_le (factor numerator denominator k : Nat) :
    accum factor numerator denominator k * (denominator ^ k * k.factorial) ≤
      factor * denominator * numerator ^ k := by
  induction k with
  | zero => simp [accum]
  | succ k ih =>
    -- The divisor of the step is the ratio of the two weights `d^k * k!`.
    have hw : denominator ^ (k + 1) * (k + 1).factorial =
        denominator * (k + 1) * (denominator ^ k * k.factorial) := by
      rw [Nat.pow_succ, Nat.factorial_succ]; ring
    rw [hw, ← Nat.mul_assoc]
    calc accum factor numerator denominator (k + 1) * (denominator * (k + 1)) *
          (denominator ^ k * k.factorial)
        ≤ accum factor numerator denominator k * numerator * (denominator ^ k * k.factorial) :=
          Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = accum factor numerator denominator k * (denominator ^ k * k.factorial) * numerator := by
          ring
      _ ≤ factor * denominator * numerator ^ k * numerator := Nat.mul_le_mul_right _ ih
      _ = factor * denominator * numerator ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]

/-- The sum of any number of accumulators is at most `factor * denominator * 3^c`.

Here `c` is `⌈numerator / denominator⌉`.

It is at most `factor * denominator` times the Taylor series of `e^(numerator / denominator)`. -/
theorem partialSum_le (hd : 0 < denominator) (m : Nat) :
    partialSum factor numerator denominator m ≤
      factor * denominator * 3 ^ ((numerator + denominator - 1) / denominator) := by
  set c := (numerator + denominator - 1) / denominator
  have hdR : (0 : ℝ) < denominator := by exact_mod_cast hd
  -- The ceiling `c` is at least `numerator / denominator`.
  have hc : numerator ≤ c * denominator := by
    have : numerator + denominator - 1 < c * denominator + denominator :=
      Nat.lt_div_mul_add hd
    omega
  have hcR : (numerator : ℝ) / denominator ≤ c := by
    rw [div_le_iff₀ hdR]; exact_mod_cast hc
  -- Each accumulator is at most `f * d` times a Taylor term of `e^(n / d)`.
  have hterm (k : Nat) : (accum factor numerator denominator k : ℝ) ≤
      factor * denominator * (((numerator : ℝ) / denominator) ^ k / k.factorial) := by
    have hpos : (0 : ℝ) < denominator ^ k * k.factorial := by positivity
    have h := accum_mul_le factor numerator denominator k
    have hR : (accum factor numerator denominator k : ℝ) * (denominator ^ k * k.factorial) ≤
        factor * denominator * numerator ^ k := by exact_mod_cast h
    rw [div_pow, div_div, mul_div_assoc', le_div_iff₀ hpos]
    exact hR
  -- `e^(n / d) ≤ e^c = (e^1)^c ≤ 3^c`.
  have hexp : Real.exp ((numerator : ℝ) / denominator) ≤ 3 ^ c := by
    calc Real.exp ((numerator : ℝ) / denominator) ≤ Real.exp c := Real.exp_le_exp.mpr hcR
      _ = Real.exp 1 ^ c := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 3 ^ c := pow_le_pow_left₀ (Real.exp_pos 1).le
          (Real.exp_one_lt_d9.le.trans (by norm_num)) _
  have hsum : (partialSum factor numerator denominator m : ℝ) =
      ∑ k ∈ Finset.range m, (accum factor numerator denominator k : ℝ) := by
    induction m with
    | zero => simp [partialSum]
    | succ m ih => rw [partialSum, Finset.sum_range_succ, ← ih]; push_cast; rfl
  have hR : (partialSum factor numerator denominator m : ℝ) ≤ factor * denominator * 3 ^ c := by
    rw [hsum]
    calc ∑ k ∈ Finset.range m, (accum factor numerator denominator k : ℝ)
        ≤ ∑ k ∈ Finset.range m,
            factor * denominator * (((numerator : ℝ) / denominator) ^ k / k.factorial) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = factor * denominator *
            ∑ k ∈ Finset.range m, ((numerator : ℝ) / denominator) ^ k / k.factorial := by
          rw [Finset.mul_sum]
      _ ≤ factor * denominator * Real.exp ((numerator : ℝ) / denominator) :=
          mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) m) (by positivity)
      _ ≤ factor * denominator * 3 ^ c := mul_le_mul_of_nonneg_left hexp (by positivity)
  exact_mod_cast hR

/-- The blob fee exponential is at most `factor * 3^c`, where `c` is `⌈numerator / denominator⌉`. -/
theorem fakeExponential_le (hd : 0 < denominator) :
    fakeExponential factor numerator denominator ≤
      factor * 3 ^ ((numerator + denominator - 1) / denominator) := by
  -- At the bound of the loop the accumulator is 0, so the result is that sum over the denominator.
  rw [fakeExponential_eq_partialSum
    (accum_eq_zero_of_fuel_le (Nat.le_succ (fakeExponentialFuel factor numerator denominator)))]
  calc partialSum factor numerator denominator (fakeExponentialFuel factor numerator denominator) /
        denominator
      ≤ factor * denominator * 3 ^ ((numerator + denominator - 1) / denominator) / denominator :=
        Nat.div_le_div_right (partialSum_le hd _)
    _ = factor * 3 ^ ((numerator + denominator - 1) / denominator) := by
        rw [Nat.mul_right_comm, Nat.mul_div_cancel _ hd]

/-- The loop of the blob fee exponential stops within `⌈2n/d⌉ + ⌊log2(f * d)⌋ + 1 + 2c` steps.

Here `n`, `d` and `f` are the numerator, the denominator and the factor, and `c` is `⌈n/d⌉`.

- The accumulator is never above `f * d * 3^c`, which is below `2^(⌊log2(f * d)⌋ + 1 + 2c)`.
- From there each step at least halves it, so that many more steps reach 0. -/
theorem accum_eq_zero_of_steps_le (hd : 0 < denominator) {k : Nat}
    (hk : (2 * numerator + denominator - 1) / denominator + Nat.log2 (factor * denominator) + 1 +
      2 * ((numerator + denominator - 1) / denominator) ≤ k) :
    accum factor numerator denominator k = 0 := by
  set c := (numerator + denominator - 1) / denominator
  set k0 := (2 * numerator + denominator - 1) / denominator
  set L := Nat.log2 (factor * denominator) + 1 + 2 * c
  -- From step `k0` on, every step halves the accumulator.
  have hk0 : 2 * numerator ≤ denominator * k0 := by
    have : 2 * numerator + denominator - 1 < k0 * denominator + denominator :=
      Nat.lt_div_mul_add hd
    rw [Nat.mul_comm denominator]
    omega
  have hhalf (j : Nat) : accum factor numerator denominator (k0 + j) ≤
      accum factor numerator denominator k0 / 2 ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc accum factor numerator denominator (k0 + (j + 1))
          = accum factor numerator denominator (k0 + j + 1) := rfl
        _ ≤ accum factor numerator denominator (k0 + j) / 2 :=
          accum_succ_le_half_of_le_mul
            (hk0.trans (Nat.mul_le_mul_left _ (by omega)))
        _ ≤ accum factor numerator denominator k0 / 2 ^ j / 2 := Nat.div_le_div_right ih
        _ = accum factor numerator denominator k0 / 2 ^ (j + 1) := by
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  -- The accumulator at step `k0` is at most `f * d * 3^c`, which is below `2^L`.
  have hlt : accum factor numerator denominator k0 < 2 ^ L := by
    have hacc : accum factor numerator denominator k0 ≤ factor * denominator * 3 ^ c := by
      calc accum factor numerator denominator k0
          ≤ partialSum factor numerator denominator (k0 + 1) := Nat.le_add_left _ _
        _ ≤ factor * denominator * 3 ^ c := partialSum_le hd _
    have h3 : 3 ^ c ≤ 2 ^ (2 * c) := by
      rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
    calc accum factor numerator denominator k0 ≤ factor * denominator * 3 ^ c := hacc
      _ < 2 ^ (Nat.log2 (factor * denominator) + 1) * 3 ^ c :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.pow_pos (by norm_num))
      _ ≤ 2 ^ (Nat.log2 (factor * denominator) + 1) * 2 ^ (2 * c) := Nat.mul_le_mul_left _ h3
      _ = 2 ^ L := (Nat.pow_add _ _ _).symm
  have hzero : accum factor numerator denominator (k0 + L) = 0 := by
    have := hhalf L
    rw [Nat.div_eq_of_lt hlt] at this
    exact Nat.le_zero.mp this
  exact accum_eq_zero_of_le hzero (by omega)

/-- Under any blob schedule, an excess of at most 161 update fractions gives a fee below `2^256`.

The fee is then at most `3^161`, which is below `2^256`. -/
theorem getBaseFeePerBlobGas_lt_of_le (schedule : BlobSchedule) {excessBlobGas : Nat}
    (h : excessBlobGas ≤ 161 * schedule.baseFeeUpdateFraction) :
    getBaseFeePerBlobGas schedule excessBlobGas < 2 ^ 256 := by
  have hF := schedule.baseFeeUpdateFraction_pos
  -- The ceiling of the excess over the update fraction is at most 161.
  have hc : (excessBlobGas + schedule.baseFeeUpdateFraction - 1) /
      schedule.baseFeeUpdateFraction ≤ 161 := by
    rw [Nat.div_le_iff_le_mul_add_pred hF]
    omega
  unfold getBaseFeePerBlobGas
  calc fakeExponential MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas schedule.baseFeeUpdateFraction
      ≤ MIN_BASE_FEE_PER_BLOB_GAS * 3 ^ ((excessBlobGas + schedule.baseFeeUpdateFraction - 1) /
          schedule.baseFeeUpdateFraction) := fakeExponential_le hF
    _ ≤ 1 * 3 ^ 161 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hc)
    _ < 2 ^ 256 := by decide

/-! ## The values of the loop -/

/-- Every accumulator is at most `factor * denominator * 3^c`, for `c = ⌈numerator / denominator⌉`.

The loop multiplies it by the numerator, so its product is at most that times the numerator. -/
theorem accum_le (hd : 0 < denominator) (k : Nat) :
    accum factor numerator denominator k ≤
      factor * denominator * 3 ^ ((numerator + denominator - 1) / denominator) :=
  -- The accumulator is one term of the sum of the first `k + 1` accumulators.
  Nat.le_trans (Nat.le_add_left _ _) (partialSum_le hd (k + 1))

/-- Up to 46 update fractions, the values of the blob fee exponential fit 128 bits.

The update fraction must be at most `2^24`; every mainnet schedule's is.

The values are each accumulator, its product with the excess, each partial sum and the fee.

The accumulators and sums are at most `F * 3^46`, and the fee at most `3^46`.

The products are at most `46 * F^2 * 3^46`. -/
theorem lt_two_pow_128_of_le (schedule : BlobSchedule) {excessBlobGas : Nat}
    (fraction : schedule.baseFeeUpdateFraction ≤ 2 ^ 24)
    (h : excessBlobGas ≤ 46 * schedule.baseFeeUpdateFraction) :
    (∀ k, accum MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas schedule.baseFeeUpdateFraction k <
        2 ^ 128) ∧
      (∀ k, accum MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas schedule.baseFeeUpdateFraction k *
        excessBlobGas < 2 ^ 128) ∧
      (∀ k, partialSum MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas schedule.baseFeeUpdateFraction k <
        2 ^ 128) ∧
      getBaseFeePerBlobGas schedule excessBlobGas < 2 ^ 128 := by
  have hF := schedule.baseFeeUpdateFraction_pos
  unfold getBaseFeePerBlobGas
  generalize schedule.baseFeeUpdateFraction = F at hF fraction h ⊢
  -- The ceiling of the excess over the update fraction is at most 46.
  have hc : (excessBlobGas + F - 1) / F ≤ 46 := by
    rw [Nat.div_le_iff_le_mul_add_pred hF]
    omega
  have h3 : 3 ^ ((excessBlobGas + F - 1) / F) ≤ 3 ^ 46 := Nat.pow_le_pow_right (by norm_num) hc
  have hsum (k : Nat) : partialSum MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas F k ≤ F * 3 ^ 46 := by
    have := partialSum_le (factor := MIN_BASE_FEE_PER_BLOB_GAS) (numerator := excessBlobGas) hF k
    simp only [MIN_BASE_FEE_PER_BLOB_GAS, Nat.one_mul] at this
    exact Nat.le_trans this (Nat.mul_le_mul_left _ h3)
  -- The bounds at the largest update fraction, `2^24`, are below `2^128`.
  have big : 2 ^ 24 * 3 ^ 46 < 2 ^ 128 := by decide
  have bigger : 46 * 2 ^ 24 * 2 ^ 24 * 3 ^ 46 < 2 ^ 128 := by decide
  have hF3 : F * 3 ^ 46 ≤ 2 ^ 24 * 3 ^ 46 := Nat.mul_le_mul_right _ fraction
  -- Each accumulator is at most `F * 3^46`.
  have hacc (k : Nat) : accum MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas F k ≤ F * 3 ^ 46 := by
    have := accum_le (factor := MIN_BASE_FEE_PER_BLOB_GAS) (numerator := excessBlobGas) hF k
    simp only [MIN_BASE_FEE_PER_BLOB_GAS, Nat.one_mul] at this
    exact Nat.le_trans this (Nat.mul_le_mul_left F h3)
  refine ⟨fun k => Nat.lt_of_le_of_lt ((hacc k).trans hF3) big, fun k => ?_,
    fun k => Nat.lt_of_le_of_lt ((hsum k).trans hF3) big, ?_⟩
  · -- The excess is at most `46 * F`.
    have hacc' := hacc k
    calc accum MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas F k * excessBlobGas
        ≤ (F * 3 ^ 46) * (46 * F) := Nat.mul_le_mul hacc' h
      _ ≤ (2 ^ 24 * 3 ^ 46) * (46 * 2 ^ 24) :=
          Nat.mul_le_mul hF3 (Nat.mul_le_mul_left _ fraction)
      _ = 46 * 2 ^ 24 * 2 ^ 24 * 3 ^ 46 := by ring
      _ < 2 ^ 128 := bigger
  · -- The fee is at most `3^46`.
    calc fakeExponential MIN_BASE_FEE_PER_BLOB_GAS excessBlobGas F
        ≤ MIN_BASE_FEE_PER_BLOB_GAS * 3 ^ ((excessBlobGas + F - 1) / F) := fakeExponential_le hF
      _ ≤ 1 * 3 ^ 46 := Nat.mul_le_mul_left _ h3
      _ < 2 ^ 128 := by decide

end EthLib.Execution.Fees.BlobBaseFee
