module

public import EthLib.Execution.Fees.BlobBaseFee
public import EthLib.Base.Proofs.Fork

/-!
# Proofs: `BlobBaseFee`

- The loop of `fake_exponential` stops before its bound.
- The base fee per blob gas is monotone in the excess, and at least 1.
- At every fork, the excess rises by at most `GAS_PER_BLOB * (max - target)` per block.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

open EthLib.Base

/-! ## The accumulator -/

/-- The accumulator of `fake_exponential` after `k` steps of its loop.

It is the `k`-th Taylor term times `factor * denominator`, rounded down at each step. -/
def accum (factor numerator denominator : Nat) : Nat → Nat
  | 0 => factor * denominator
  | k + 1 => accum factor numerator denominator k * numerator / (denominator * (k + 1))

/-- The sum of the first `k` accumulators: the output of the loop after `k` steps. -/
def partialSum (factor numerator denominator : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => partialSum factor numerator denominator k + accum factor numerator denominator k

/-- Once the accumulator is 0, it stays 0. -/
theorem accum_eq_zero_of_le {factor numerator denominator k m : Nat}
    (h : accum factor numerator denominator k = 0) (hkm : k ≤ m) : accum factor numerator denominator m = 0 := by
  induction m with
  | zero =>
    rw [Nat.le_zero.mp hkm] at h
    exact h
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hkm with hlt | heq
    · rw [accum, ih (Nat.le_of_lt_succ hlt), Nat.zero_mul, Nat.zero_div]
    · rw [← heq]
      exact h

/-- Once the accumulator is 0, the sum stops growing. -/
theorem partialSum_eq_of_le {factor numerator denominator k m : Nat}
    (h : accum factor numerator denominator k = 0) (hkm : k ≤ m) :
    partialSum factor numerator denominator m = partialSum factor numerator denominator k := by
  induction m with
  | zero => rw [Nat.le_zero.mp hkm]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hkm with hlt | heq
    · rw [partialSum, ih (Nat.le_of_lt_succ hlt), accum_eq_zero_of_le h (Nat.le_of_lt_succ hlt), Nat.add_zero]
    · rw [heq]

/-- From step `k + 1`, `fuel` more steps of the loop give the sum of the first `k + fuel` accumulators.

The loop stops early only at an accumulator of 0, and from there on the sum does not grow. -/
theorem fakeExponentialLoop_eq (factor numerator denominator fuel k : Nat) :
    fakeExponentialLoop numerator denominator fuel (k + 1) (accum factor numerator denominator k)
        (partialSum factor numerator denominator k)
      = partialSum factor numerator denominator (k + fuel) := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    by_cases hk : accum factor numerator denominator k = 0
    · -- The accumulator is already 0: the loop stops, and the sum has stopped growing.
      simp only [fakeExponentialLoop, hk, ↓reduceIte]
      exact (partialSum_eq_of_le hk (Nat.le_add_right _ _)).symm
    · -- One step of the loop is one more accumulator in the sum.
      simp only [fakeExponentialLoop, hk, ↓reduceIte]
      rw [show k + (fuel + 1) = k + 1 + fuel by omega]
      exact ih (k + 1)

/-! ## Termination -/

/-- Each step multiplies the accumulator by at most `numerator`. -/
theorem accum_succ_le (factor numerator denominator k : Nat) :
    accum factor numerator denominator (k + 1) ≤ accum factor numerator denominator k * numerator :=
  Nat.div_le_self _ _

/-- After `k` steps, the accumulator is at most `factor * denominator * numerator^k`. -/
theorem accum_le_pow (factor numerator denominator k : Nat) :
    accum factor numerator denominator k ≤ factor * denominator * numerator ^ k := by
  induction k with
  | zero => simp [accum]
  | succ k ih =>
    calc accum factor numerator denominator (k + 1)
        ≤ accum factor numerator denominator k * numerator := accum_succ_le _ _ _ _
      _ ≤ factor * denominator * numerator ^ k * numerator := Nat.mul_le_mul_right _ ih
      _ = factor * denominator * numerator ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]

/-- From step `2 * numerator` on, each step at least halves the accumulator.

For a positive denominator, the divisor `denominator * (k + 1)` is then at least twice the numerator.

A denominator of 0 makes the next accumulator 0. -/
theorem accum_succ_le_half {factor numerator denominator k : Nat} (hk : 2 * numerator ≤ k) :
    accum factor numerator denominator (k + 1) ≤ accum factor numerator denominator k / 2 := by
  rcases Nat.eq_zero_or_pos numerator with hn | hn
  · -- A numerator of 0 makes the next accumulator 0.
    simp [accum, hn]
  rcases Nat.eq_zero_or_pos denominator with hd | hd
  · -- So does a denominator of 0, since `x / 0 = 0`.
    simp [accum, hd]
  show accum factor numerator denominator k * numerator / (denominator * (k + 1))
    ≤ accum factor numerator denominator k / 2
  calc accum factor numerator denominator k * numerator / (denominator * (k + 1))
      ≤ accum factor numerator denominator k * numerator / (2 * numerator) := by
        apply Nat.div_le_div_left _ (by omega)
        calc 2 * numerator ≤ k + 1 := by omega
          _ ≤ denominator * (k + 1) := Nat.le_mul_of_pos_left _ hd
    _ = accum factor numerator denominator k / 2 := Nat.mul_div_mul_right _ _ hn

/-- After `2 * numerator + j` steps, the accumulator has been halved at least `j` times. -/
theorem accum_add_le (factor numerator denominator j : Nat) :
    accum factor numerator denominator (2 * numerator + j)
      ≤ accum factor numerator denominator (2 * numerator) / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc accum factor numerator denominator (2 * numerator + (j + 1))
        = accum factor numerator denominator (2 * numerator + j + 1) := rfl
      _ ≤ accum factor numerator denominator (2 * numerator + j) / 2 := accum_succ_le_half (Nat.le_add_right _ _)
      _ ≤ accum factor numerator denominator (2 * numerator) / 2 ^ j / 2 := Nat.div_le_div_right ih
      _ = accum factor numerator denominator (2 * numerator) / 2 ^ (j + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- `a * n^(2 * n) < 2^(a + 2 * n * n)`, since `a < 2^a` and `n < 2^n`. -/
private theorem mul_pow_lt_two_pow (a n : Nat) : a * n ^ (2 * n) < 2 ^ (a + 2 * n * n) := by
  have hpow : n ^ (2 * n) ≤ 2 ^ (2 * n * n) := by
    calc n ^ (2 * n) ≤ (2 ^ n) ^ (2 * n) := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
      _ = 2 ^ (2 * n * n) := by rw [← Nat.pow_mul, Nat.mul_comm n (2 * n)]
  calc a * n ^ (2 * n) ≤ a * 2 ^ (2 * n * n) := Nat.mul_le_mul_left _ hpow
    _ < 2 ^ a * 2 ^ (2 * n * n) := Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
    _ = 2 ^ (a + 2 * n * n) := (Nat.pow_add _ _ _).symm

/-- The loop of `fake_exponential` terminates: from step `fakeExponentialFuel - 1` on, the accumulator is 0.

So the loop stops on its own before the bound runs out. -/
theorem accum_eq_zero_of_fuel_le {factor numerator denominator k : Nat}
    (h : fakeExponentialFuel factor numerator denominator ≤ k + 1) : accum factor numerator denominator k = 0 := by
  -- Let `j = factor * denominator + 2 * numerator^2`: at step `2 * numerator + j` the accumulator is 0.
  have hzero : accum factor numerator denominator
      (2 * numerator + (factor * denominator + 2 * numerator * numerator)) = 0 := by
    -- From step `2 * numerator`, the next `j` steps divide the accumulator by at least `2^j`.
    have hle := accum_add_le factor numerator denominator (factor * denominator + 2 * numerator * numerator)
    -- The accumulator of step `2 * numerator` is below `2^j`, so the quotient is 0.
    have hlt := Nat.lt_of_le_of_lt (accum_le_pow factor numerator denominator (2 * numerator))
      (mul_pow_lt_two_pow (factor * denominator) numerator)
    rw [Nat.div_eq_of_lt hlt] at hle
    exact Nat.le_zero.mp hle
  -- Step `k` comes no earlier, and an accumulator of 0 stays 0.
  exact accum_eq_zero_of_le hzero (by unfold fakeExponentialFuel at h; omega)

/-! ## The value -/

/-- The loop of `fake_exponential`, run for `fuel` steps, gives the sum of the first `fuel` accumulators. -/
theorem fakeExponentialLoop_eq_partialSum (factor numerator denominator fuel : Nat) :
    fakeExponentialLoop numerator denominator fuel 1 (factor * denominator) 0
      = partialSum factor numerator denominator fuel := by
  have hloop := fakeExponentialLoop_eq factor numerator denominator fuel 0
  rw [Nat.zero_add fuel] at hloop
  exact hloop

/-- `fake_exponential` is the sum of the accumulators, divided by the denominator.

Any `m` at which the accumulator is 0 gives the whole sum. -/
theorem fakeExponential_eq_partialSum {factor numerator denominator m : Nat}
    (h : accum factor numerator denominator m = 0) :
    fakeExponential factor numerator denominator = partialSum factor numerator denominator m / denominator := by
  have hfuel : accum factor numerator denominator (fakeExponentialFuel factor numerator denominator) = 0 :=
    accum_eq_zero_of_fuel_le (by omega)
  unfold fakeExponential
  rw [fakeExponentialLoop_eq_partialSum]
  -- The sum has stopped growing both at the bound and at `m`, so the two sums are equal.
  rcases Nat.le_total m (fakeExponentialFuel factor numerator denominator) with hle | hle
  · rw [partialSum_eq_of_le h hle]
  · rw [partialSum_eq_of_le hfuel hle]

/-- At least `fakeExponentialFuel` steps give the same result: the bound never changes `fake_exponential`. -/
theorem fakeExponential_eq_loop {factor numerator denominator fuel : Nat}
    (h : fakeExponentialFuel factor numerator denominator ≤ fuel) :
    fakeExponential factor numerator denominator
      = fakeExponentialLoop numerator denominator fuel 1 (factor * denominator) 0 / denominator := by
  have hacc : accum factor numerator denominator fuel = 0 := accum_eq_zero_of_fuel_le (by omega)
  rw [fakeExponential_eq_partialSum hacc, fakeExponentialLoop_eq_partialSum]

/-- For a positive denominator, a numerator of 0 makes `fake_exponential` return its factor. -/
theorem fakeExponential_zero (factor : Nat) {denominator : Nat} (hd : 0 < denominator) :
    fakeExponential factor 0 denominator = factor := by
  -- The accumulators are `factor * denominator`, then 0.
  rw [fakeExponential_eq_partialSum (m := 1) (by simp [accum])]
  simp [partialSum, accum, Nat.mul_div_cancel _ hd]

/-! ## Monotonicity -/

/-- A larger numerator never lowers an accumulator. -/
theorem accum_mono {factor numerator numerator' denominator : Nat} (h : numerator ≤ numerator') (k : Nat) :
    accum factor numerator denominator k ≤ accum factor numerator' denominator k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact Nat.div_le_div_right (Nat.mul_le_mul ih h)

/-- A larger numerator never lowers the sum of the first `k` accumulators. -/
theorem partialSum_mono {factor numerator numerator' denominator : Nat} (h : numerator ≤ numerator') (k : Nat) :
    partialSum factor numerator denominator k ≤ partialSum factor numerator' denominator k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact Nat.add_le_add ih (accum_mono h k)

/-- `fake_exponential` is monotone in its numerator.

Both values are sums up to the later of the two bounds, and each term grows with the numerator. -/
theorem fakeExponential_mono {factor numerator numerator' denominator : Nat} (h : numerator ≤ numerator') :
    fakeExponential factor numerator denominator ≤ fakeExponential factor numerator' denominator := by
  -- At the later of the two bounds, both accumulators are 0.
  have h1 : fakeExponentialFuel factor numerator denominator
      ≤ max (fakeExponentialFuel factor numerator denominator) (fakeExponentialFuel factor numerator' denominator) + 1 :=
    Nat.le_succ_of_le (Nat.le_max_left _ _)
  have h2 : fakeExponentialFuel factor numerator' denominator
      ≤ max (fakeExponentialFuel factor numerator denominator) (fakeExponentialFuel factor numerator' denominator) + 1 :=
    Nat.le_succ_of_le (Nat.le_max_right _ _)
  rw [fakeExponential_eq_partialSum (accum_eq_zero_of_fuel_le h1),
    fakeExponential_eq_partialSum (accum_eq_zero_of_fuel_le h2)]
  exact Nat.div_le_div_right (partialSum_mono h _)

/-! ## The base fee per blob gas -/

/-- The base fee per blob gas is monotone in the excess blob gas. -/
theorem getBaseFeePerBlobGas_mono (schedule : BlobSchedule) {excessBlobGas excessBlobGas' : Nat}
    (h : excessBlobGas ≤ excessBlobGas') :
    getBaseFeePerBlobGas schedule excessBlobGas ≤ getBaseFeePerBlobGas schedule excessBlobGas' :=
  fakeExponential_mono h

/-- With an excess of 0, the base fee per blob gas is `MIN_BASE_FEE_PER_BLOB_GAS`. -/
theorem getBaseFeePerBlobGas_zero (schedule : BlobSchedule) :
    getBaseFeePerBlobGas schedule 0 = MIN_BASE_FEE_PER_BLOB_GAS :=
  fakeExponential_zero _ schedule.baseFeeUpdateFraction_pos

/-- The base fee per blob gas is never below `MIN_BASE_FEE_PER_BLOB_GAS`. -/
theorem le_getBaseFeePerBlobGas (schedule : BlobSchedule) (excessBlobGas : Nat) :
    MIN_BASE_FEE_PER_BLOB_GAS ≤ getBaseFeePerBlobGas schedule excessBlobGas := by
  rw [← getBaseFeePerBlobGas_zero schedule]
  exact getBaseFeePerBlobGas_mono schedule (Nat.zero_le _)

/-! ## The excess blob gas -/

/-- The reserve condition of EIP-7918: a blob costs less than `BLOB_BASE_COST` execution gas. -/
abbrev BelowReserve (schedule : BlobSchedule) (parentExcessBlobGas parentBaseFeePerGas : Nat) :
    Prop :=
  BLOB_BASE_COST * parentBaseFeePerGas >
    GAS_PER_BLOB * getBaseFeePerBlobGas schedule parentExcessBlobGas

variable {fork : Fork} {schedule : BlobSchedule}

/-- Below the target, the excess is 0 at every fork, whatever the reserve price. -/
theorem calcExcessBlobGas_of_lt {parentExcessBlobGas parentBlobGasUsed : Nat}
    (parentBaseFeePerGas : Nat)
    (h : parentExcessBlobGas + parentBlobGasUsed < GAS_PER_BLOB * schedule.target) :
    calcExcessBlobGas fork schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      = 0 := by
  simp only [calcExcessBlobGas, h, ↓reduceIte]

/-- Without the reserve price, the excess is the parent's excess and blob gas, minus the target.

It is at least 0.

That is the rule before Fusaka, and the rule from Fusaka at or above the reserve price. -/
theorem calcExcessBlobGas_eq_sub {parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat}
    (h : ¬(fork ≥ .fusaka ∧ BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas)) :
    calcExcessBlobGas fork schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      = parentExcessBlobGas + parentBlobGasUsed - GAS_PER_BLOB * schedule.target := by
  unfold BelowReserve at h
  simp only [calcExcessBlobGas, h, ↓reduceIte]
  -- Below the target both sides are 0, and from the target up they are the same subtraction.
  split <;> omega

/-- Before Fusaka, the excess is the parent's excess plus its blob gas, minus the target. -/
theorem calcExcessBlobGas_of_lt_fusaka
    {parentExcessBlobGas parentBlobGasUsed : Nat} (parentBaseFeePerGas : Nat)
    (hFork : fork < .fusaka) :
    calcExcessBlobGas fork schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      = parentExcessBlobGas + parentBlobGasUsed - GAS_PER_BLOB * schedule.target :=
  calcExcessBlobGas_eq_sub fun h => absurd h.1 (Nat.not_le_of_lt hFork)

/-- From Fusaka, below the reserve price and from the target, the excess grows more slowly.

It grows by `parentBlobGasUsed * (max - target) / max`. -/
theorem calcExcessBlobGas_of_below
    {parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat} (hFork : fork ≥ .fusaka)
    (ht : GAS_PER_BLOB * schedule.target ≤ parentExcessBlobGas + parentBlobGasUsed)
    (h : BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas) :
    calcExcessBlobGas fork schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      = parentExcessBlobGas
        + parentBlobGasUsed * (schedule.max - schedule.target) / schedule.max := by
  unfold BelowReserve at h
  simp only [calcExcessBlobGas, Nat.not_lt.mpr ht, hFork, h, and_self, ↓reduceIte]

/-- From Fusaka, below the reserve price and at the target or above, the excess does not fall. -/
theorem le_calcExcessBlobGas_of_below
    {parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat} (hFork : fork ≥ .fusaka)
    (ht : GAS_PER_BLOB * schedule.target ≤ parentExcessBlobGas + parentBlobGasUsed)
    (h : BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas) :
    parentExcessBlobGas ≤
      calcExcessBlobGas fork schedule parentExcessBlobGas parentBlobGasUsed
        parentBaseFeePerGas := by
  rw [calcExcessBlobGas_of_below hFork ht h]
  exact Nat.le_add_right _ _

/-- A parent within its maximum raises the excess by at most `GAS_PER_BLOB * (max - target)`. -/
theorem calcExcessBlobGas_le (parentExcessBlobGas parentBaseFeePerGas : Nat)
    {parentBlobGasUsed : Nat} (h : parentBlobGasUsed ≤ GAS_PER_BLOB * schedule.max) :
    calcExcessBlobGas fork schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      ≤ parentExcessBlobGas + GAS_PER_BLOB * (schedule.max - schedule.target) := by
  by_cases hReserve :
      fork ≥ .fusaka ∧ BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas
  · rcases Nat.lt_or_ge (parentExcessBlobGas + parentBlobGasUsed)
        (GAS_PER_BLOB * schedule.target) with hlt | hge
    · rw [calcExcessBlobGas_of_lt _ hlt]
      exact Nat.zero_le _
    · rw [calcExcessBlobGas_of_below hReserve.1 hge hReserve.2]
      apply Nat.add_le_add_left
      -- The parent's blob gas is at most `GAS_PER_BLOB * max`, and the `max` cancels.
      calc parentBlobGasUsed * (schedule.max - schedule.target) / schedule.max
          ≤ GAS_PER_BLOB * schedule.max * (schedule.max - schedule.target) / schedule.max :=
            Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
        _ = GAS_PER_BLOB * (schedule.max - schedule.target) := by
            rw [Nat.mul_right_comm, Nat.mul_div_cancel _ schedule.max_pos]
  · -- `GAS_PER_BLOB * (max - target)` is `GAS_PER_BLOB * max - GAS_PER_BLOB * target`.
    rw [calcExcessBlobGas_eq_sub hReserve, Nat.mul_sub]
    omega

end EthLib.Execution.Fees.BlobBaseFee
