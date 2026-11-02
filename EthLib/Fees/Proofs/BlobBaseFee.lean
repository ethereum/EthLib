module

public import EthLib.Fees.BlobBaseFee

/-!
# Proofs: `BlobBaseFee`

What the blob fee rules guarantee.

- The loop of `fake_exponential` terminates: its accumulator reaches 0 within `fakeExponentialFuel` steps.
- So the bound never changes the result, and the result is the sum of the accumulators, divided by the denominator.
- `fake_exponential` is monotone in its numerator, so the base fee per blob gas is monotone in the excess blob gas.
- With an excess of 0 the fee is `MIN_BASE_FEE_PER_BLOB_GAS`, and it is never lower.
- Before EIP-7918, the excess is the parent's excess plus its blob gas, minus the target, at least 0.
- Below the reserve price of EIP-7918, the excess does not fall, once the parent's excess plus its blob gas reaches the target.
- Under both rules, a parent with at most `GAS_PER_BLOB * max` blob gas raises the excess by at most `GAS_PER_BLOB * (max - target)`.

The known answers at the end are worked by hand from the formulas.
-/

@[expose] public section

namespace EthLib.Fees.BlobBaseFee

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

/-- The loop adds up the accumulators: from step `k + 1`, `fuel` more steps give the sum of the first `k + fuel`.

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

/-- After `2 * numerator + j` steps, the accumulator is at most the one of step `2 * numerator`, over `2^j`. -/
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

namespace Cancun

/-- Before EIP-7918, the excess is the parent's excess plus its blob gas, minus the target, at least 0.

`Nat` subtraction already stops at 0. -/
theorem calcExcessBlobGas_eq (schedule : BlobSchedule) (parentExcessBlobGas parentBlobGasUsed : Nat) :
    calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed
      = parentExcessBlobGas + parentBlobGasUsed - GAS_PER_BLOB * schedule.target := by
  simp only [calcExcessBlobGas]
  -- Below the target both sides are 0, and from the target up they are the same subtraction.
  split <;> omega

/-- A parent with at most `GAS_PER_BLOB * max` blob gas raises the excess by at most `GAS_PER_BLOB * (max - target)`. -/
theorem calcExcessBlobGas_le (schedule : BlobSchedule) (parentExcessBlobGas : Nat) {parentBlobGasUsed : Nat}
    (h : parentBlobGasUsed ≤ GAS_PER_BLOB * schedule.max) :
    calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed
      ≤ parentExcessBlobGas + GAS_PER_BLOB * (schedule.max - schedule.target) := by
  -- `GAS_PER_BLOB * (max - target)` is `GAS_PER_BLOB * max - GAS_PER_BLOB * target`.
  rw [calcExcessBlobGas_eq, Nat.mul_sub]
  omega

end Cancun

namespace Osaka

/-- The reserve condition of EIP-7918: a blob costs less than `BLOB_BASE_COST` units of execution gas. -/
abbrev BelowReserve (schedule : BlobSchedule) (parentExcessBlobGas parentBaseFeePerGas : Nat) : Prop :=
  BLOB_BASE_COST * parentBaseFeePerGas > GAS_PER_BLOB * getBaseFeePerBlobGas schedule parentExcessBlobGas

/-- When the parent's excess plus its blob gas is below the target, the excess is 0, whatever the reserve price. -/
theorem calcExcessBlobGas_of_lt {schedule : BlobSchedule} {parentExcessBlobGas parentBlobGasUsed : Nat}
    (parentBaseFeePerGas : Nat) (h : parentExcessBlobGas + parentBlobGasUsed < GAS_PER_BLOB * schedule.target) :
    calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas = 0 := by
  simp only [calcExcessBlobGas, h, ↓reduceIte]

/-- At or above the reserve price, EIP-7918 gives the same excess as EIP-4844. -/
theorem calcExcessBlobGas_of_not_below {schedule : BlobSchedule} {parentExcessBlobGas parentBaseFeePerGas : Nat}
    (parentBlobGasUsed : Nat) (h : ¬ BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas) :
    calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      = Cancun.calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed := by
  unfold BelowReserve at h
  simp only [calcExcessBlobGas, Cancun.calcExcessBlobGas, h, ↓reduceIte]

/-- Below the reserve price, once the parent's excess plus its blob gas reaches the target, the excess grows by `parentBlobGasUsed * (max - target) / max`. -/
theorem calcExcessBlobGas_of_below {schedule : BlobSchedule} {parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat}
    (ht : GAS_PER_BLOB * schedule.target ≤ parentExcessBlobGas + parentBlobGasUsed)
    (h : BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas) :
    calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      = parentExcessBlobGas + parentBlobGasUsed * (schedule.max - schedule.target) / schedule.max := by
  unfold BelowReserve at h
  simp only [calcExcessBlobGas, Nat.not_lt.mpr ht, h, ↓reduceIte]

/-- Below the reserve price, once the parent's excess plus its blob gas reaches the target, the excess does not fall. -/
theorem le_calcExcessBlobGas_of_below {schedule : BlobSchedule}
    {parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas : Nat}
    (ht : GAS_PER_BLOB * schedule.target ≤ parentExcessBlobGas + parentBlobGasUsed)
    (h : BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas) :
    parentExcessBlobGas ≤ calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas := by
  rw [calcExcessBlobGas_of_below ht h]
  exact Nat.le_add_right _ _

/-- A parent with at most `GAS_PER_BLOB * max` blob gas raises the excess by at most `GAS_PER_BLOB * (max - target)`, as before EIP-7918. -/
theorem calcExcessBlobGas_le (schedule : BlobSchedule) (parentExcessBlobGas parentBaseFeePerGas : Nat)
    {parentBlobGasUsed : Nat} (h : parentBlobGasUsed ≤ GAS_PER_BLOB * schedule.max) :
    calcExcessBlobGas schedule parentExcessBlobGas parentBlobGasUsed parentBaseFeePerGas
      ≤ parentExcessBlobGas + GAS_PER_BLOB * (schedule.max - schedule.target) := by
  by_cases hbelow : BelowReserve schedule parentExcessBlobGas parentBaseFeePerGas
  · rcases Nat.lt_or_ge (parentExcessBlobGas + parentBlobGasUsed) (GAS_PER_BLOB * schedule.target) with hlt | hge
    · rw [calcExcessBlobGas_of_lt _ hlt]
      exact Nat.zero_le _
    · rw [calcExcessBlobGas_of_below hge hbelow]
      apply Nat.add_le_add_left
      -- The parent's blob gas is at most `GAS_PER_BLOB * max`, and the `max` cancels.
      calc parentBlobGasUsed * (schedule.max - schedule.target) / schedule.max
          ≤ GAS_PER_BLOB * schedule.max * (schedule.max - schedule.target) / schedule.max :=
            Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
        _ = GAS_PER_BLOB * (schedule.max - schedule.target) := by
            rw [Nat.mul_right_comm, Nat.mul_div_cancel _ schedule.max_pos]
  · rw [calcExcessBlobGas_of_not_below _ hbelow]
    exact Cancun.calcExcessBlobGas_le schedule parentExcessBlobGas h

end Osaka

/-! ## Known answers

Each answer is worked by hand from the formulas of EIP-4844 and EIP-7918.

For `fake_exponential`, each comment lists the accumulators, which the loop adds up before the last division. -/

/-- `fake_exponential(1, 0, d)` is 1: accumulators `d`, then 0, so `d // d = 1`. -/
example : fakeExponential 1 0 5007716 = 1 := by decide +kernel

/-- `fake_exponential(1, 1, 1)`, about e: accumulators 1, 1, then 0, so 2. -/
example : fakeExponential 1 1 1 = 2 := by decide +kernel

/-- `fake_exponential(1, 2, 1)`, about e^2: accumulators 1, 2, 2, 1, then 0, so 6. -/
example : fakeExponential 1 2 1 = 6 := by decide +kernel

/-- `fake_exponential(1, 3, 1)`, about e^3: accumulators 1, 3, 4, 4, 3, 1, then 0, so 16. -/
example : fakeExponential 1 3 1 = 16 := by decide +kernel

/-- `fake_exponential(1, 4, 2)`, about e^2: accumulators 2, 4, 4, 2, 1, then 0, so 13 // 2 = 6. -/
example : fakeExponential 1 4 2 = 6 := by decide +kernel

/-- `fake_exponential(10, 8, 2)`, about 10 * e^4.

The accumulators are 20, 80, 160, 213, 213, 170, 113, 64, 32, 14, 5, 1, then 0, so 1085 // 2 = 542. -/
example : fakeExponential 10 8 2 = 542 := by decide +kernel

namespace TestVector

/-- The schedule of Cancun: target 3, max 6, update fraction 3338477.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters), Parameters, gives the update fraction, and the target and the maximum in blob gas: `TARGET_BLOB_GAS_PER_BLOCK = 393216` and `MAX_BLOB_GAS_PER_BLOCK = 786432` are 3 and 6 blobs. -/
def cancun : BlobSchedule := { target := 3, max := 6, baseFeeUpdateFraction := 3338477 }

/-- The schedule of Osaka: target 6, max 9, update fraction 5007716.

[EIP-7691](https://eips.ethereum.org/EIPS/eip-7691#parameters), Parameters, sets them for Prague.

[`forks/osaka/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/osaka/vm/gas.py#L96-L101) of execution-specs at `2c0c8e7` keeps them for Osaka. -/
def osaka : BlobSchedule := { target := 6, max := 9, baseFeeUpdateFraction := 5007716 }

end TestVector

open TestVector

/-- An excess of 0 gives `MIN_BASE_FEE_PER_BLOB_GAS`. -/
example : getBaseFeePerBlobGas cancun 0 = 1 := by decide +kernel

/-- An excess equal to the update fraction, so about e.

With `numerator = denominator`, each accumulator is the previous one over `i`, rounded down.

The accumulators are 3338477, 3338477, 1669238, 556412, 139103, 27820, 4636, 662, 82, 9, then 0.

They add up to 9074916, and 9074916 // 3338477 = 2. -/
example : getBaseFeePerBlobGas cancun 3338477 = 2 := by decide +kernel

/-- The same for Osaka: 5007716, 5007716, 2503858, 834619, 208654, 41730, 6955, 993, 124, 13, 1, then 0.

They add up to 13612379, and 13612379 // 5007716 = 2. -/
example : getBaseFeePerBlobGas osaka 5007716 = 2 := by decide +kernel

/-- Cancun, a parent with 6 blobs and no excess: 6 * 2^17 - 3 * 2^17 = 393216. -/
example : Cancun.calcExcessBlobGas cancun 0 786432 = 393216 := by decide +kernel

/-- Cancun, a parent with 1 blob and no excess: below the target, so 0. -/
example : Cancun.calcExcessBlobGas cancun 0 131072 = 0 := by decide +kernel

/-- Osaka, a parent at its target of 6 blobs, with no excess and a base fee of 17.

The reserve price is 2^13 * 17 = 139264, above the blob price 2^17 * 1 = 131072.

So the excess grows by 786432 * (9 - 6) // 9 = 262144 instead of 0.

Dividing first would give 786432 // 9 * 3 = 262143. -/
example : Osaka.calcExcessBlobGas osaka 0 786432 17 = 262144 := by decide +kernel

/-- Osaka, a parent with 7 blobs, so 917504 blob gas, with no excess and a base fee of 17.

The excess grows by 917504 * 3 // 9 = 2752512 // 9 = 305834, rounded down from 305834.67. -/
example : Osaka.calcExcessBlobGas osaka 0 917504 17 = 305834 := by decide +kernel

/-- The parent at its target with a base fee of 16: 2^13 * 16 = 131072 is not above 131072, so the target is subtracted. -/
example : Osaka.calcExcessBlobGas osaka 0 786432 16 = 0 := by decide +kernel

/-- A parent with 5 blobs and no excess, below the target, gives 0 even far below the reserve price, at a base fee of 10^9. -/
example : Osaka.calcExcessBlobGas osaka 0 655360 1000000000 = 0 := by decide +kernel

/-- An empty parent with an excess of 500000, below the target of 786432: the excess falls to 0, even far below the reserve price. -/
example : Osaka.calcExcessBlobGas osaka 500000 0 1000000000 = 0 := by decide +kernel

/-- An excess of 5007716 makes the blob base fee 2, so the reserve price binds only for a base fee above 2^17 * 2 / 2^13 = 32.

With 33, the excess grows by 262144 for a parent at its target. -/
example : Osaka.calcExcessBlobGas osaka 5007716 786432 33 = 5269860 := by decide +kernel

/-- With 32, the reserve price equals the blob price, so the target is subtracted and the excess stays. -/
example : Osaka.calcExcessBlobGas osaka 5007716 786432 32 = 5007716 := by decide +kernel

end EthLib.Fees.BlobBaseFee
