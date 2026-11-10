module

public import EthLib.Consensus.Proofs.Transition.EpochUpdates

/-!
# Proofs: how fast a leak lowers the effective balance of an absent validator

From Altair, in a leak, an eligible validator without the target flag gains the bias each epoch.

Each epoch it then loses at least its effective balance times its new score, over a divisor.

Its effective balance follows its balance with some hysteresis.

It falls only once the balance is more than a quarter of an increment below it, on mainnet.

While the effective balance stays above a threshold, the losses add up quadratically.

So after an explicit number of epochs the effective balance is at most the threshold.

That number is about the square root of twice the divisor times the loss needed, over the slope.

The slope is the threshold plus an increment, times the score bias.

The divisor is the score bias times the penalty quotient, `2^26` on mainnet from Bellatrix.

Take a bias of 4, a score of zero, and a threshold of 16 ETH.

Take a balance and an effective balance of 32 ETH.

The bound is then 5,488 epochs.

That threshold is the ejection balance.

[Pavloff et al.][pat], Section 4.3, Figure 2, reports the ejection at epoch 4,685.

With the inactivity penalty alone, the discrete rule reaches it then too.

The closed form of the paper gives about 4,661, at the stake of 16.75 ETH where it ejects.

The bound is larger because it charges each epoch only the threshold plus an increment.

An effective balance at most the ejection balance only starts the exit, at the next registry update.

The validator leaves the active set later, after the exit queue, and pays the leak until then.

The traces of the bound are assumptions, not derived from the state transition.

They assume that no reward, deposit or consolidation raises the balance.

They also assume a fixed largest effective balance: one fork and one kind of credentials.

[pat]: https://arxiv.org/abs/2404.16363v2
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset}


/-- The least total that a leak takes from an absent validator over some epochs.

In each epoch its effective balance is at least some floor, and its score starts at a value.

The score gains the bias before each penalty, and each penalty rounds down. -/
def leakLoss (floor score bias divisor epochs : Nat) : Nat :=
  ((List.range epochs).map fun t => floor * (score + bias * (t + 1)) / divisor).sum

/-- One more epoch of a leak adds one more rounded penalty. -/
private theorem leakLoss_succ (floor score bias divisor n : Nat) :
    leakLoss floor score bias divisor (n + 1) =
      leakLoss floor score bias divisor n + floor * (score + bias * (n + 1)) / divisor := by
  simp [leakLoss, List.range_succ]

/-- A leak takes more as it lasts longer. -/
private theorem leakLoss_mono (floor score bias divisor : Nat) {n m : Nat} (le : n ≤ m) :
    leakLoss floor score bias divisor n ≤ leakLoss floor score bias divisor m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have := ih (Nat.le_add_right n k)
    rw [← Nat.add_assoc, leakLoss_succ]
    exact Nat.le_trans this (Nat.le_add_right _ _)

/-- The score of an absent validator is its start score plus the bias for each epoch. -/
private theorem score_eq {score : Nat → Nat} {bias epochs : Nat}
    (scored : ∀ t < epochs, score (t + 1) = score t + bias) :
    ∀ t ≤ epochs, score t = score 0 + bias * t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro h
    rw [scored t (by omega), ih (by omega), Nat.mul_succ]
    omega

/-- The loss of a leak is quadratic in its length, up to a rounding of each penalty. -/
private theorem quadratic_le_leakLoss {floor score bias divisor : Nat} (divisorPos : 0 < divisor)
    (n : Nat) :
    floor * bias * n * (n + 1) ≤
      2 * divisor * leakLoss floor score bias divisor n + 2 * divisor * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [leakLoss_succ]
    have rounding := Nat.lt_mul_div_succ (floor * (score + bias * (n + 1))) divisorPos
    have grown : floor * bias * (n + 1) ≤ floor * (score + bias * (n + 1)) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    have expand : floor * bias * (n + 1) * (n + 1 + 1) =
        floor * bias * n * (n + 1) + 2 * (floor * bias * (n + 1)) := by grind
    generalize floor * (score + bias * (n + 1)) / divisor = q at *
    generalize leakLoss floor score bias divisor n = loss at *
    have expand2 : 2 * divisor * (loss + q) + 2 * divisor * (n + 1) =
        2 * divisor * loss + 2 * divisor * n + 2 * (divisor * (q + 1)) := by grind
    rw [expand, expand2]
    omega

/-- A number of epochs after which a leak has taken at least some amount.

The slope is a floor of the effective balance times the score bias. -/
def leakEpochs (floor bias divisor amount : Nat) : Nat :=
  Nat.sqrt (2 * divisor * amount / (floor * bias)) + 2 * divisor / (floor * bias) + 2

/-- After that number of epochs the leak has taken at least the amount, from any score.

The floor, the bias and the divisor must be positive. -/
theorem le_leakLoss_leakEpochs {floor score bias divisor amount : Nat} (floorPos : 0 < floor)
    (biasPos : 0 < bias) (divisorPos : 0 < divisor) :
    amount ≤ leakLoss floor score bias divisor (leakEpochs floor bias divisor amount) := by
  have kPos : 0 < floor * bias := Nat.mul_pos floorPos biasPos
  have quad := quadratic_le_leakLoss (floor := floor) (score := score) (bias := bias) divisorPos
    (leakEpochs floor bias divisor amount)
  have rootBound := Nat.lt_succ_sqrt (2 * divisor * amount / (floor * bias))
  have divBound := Nat.lt_mul_div_succ (2 * divisor * amount) kPos
  have stepBound := Nat.lt_mul_div_succ (2 * divisor) kPos
  generalize leakLoss floor score bias divisor (leakEpochs floor bias divisor amount) = loss at *
  unfold leakEpochs at quad
  generalize Nat.sqrt (2 * divisor * amount / (floor * bias)) = s at *
  generalize 2 * divisor / (floor * bias) = r at *
  generalize 2 * divisor * amount / (floor * bias) = q at *
  generalize floor * bias = k at *
  have first : 2 * divisor * amount < k * ((s + 1) * (s + 1)) :=
    Nat.lt_of_lt_of_le divBound (Nat.mul_le_mul_left _ rootBound)
  have f1 : k * ((s + 1) * (s + 1)) ≤ k * ((s + 1) * (s + r + 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have f2 : 2 * divisor * (s + r + 2) < k * (r + 1) * (s + r + 2) :=
    Nat.mul_lt_mul_of_pos_right stepBound (by omega)
  have f3 : k * (s + r + 2) * (s + r + 2) =
      k * ((s + 1) * (s + r + 2)) + k * (r + 1) * (s + r + 2) := by grind
  have f4 : k * (s + r + 2) * (s + r + 2 + 1) =
      k * (s + r + 2) * (s + r + 2) + k * (s + r + 2) := by grind
  have f5 : 2 * divisor * amount < 2 * divisor * loss := by omega
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left f5)

/-- A whole number of increments above another is at least one increment above it. -/
private theorem add_le_of_lt_of_aligned {inc a b : Nat} (ha : a % inc = 0) (hb : b % inc = 0)
    (lt : b < a) : b + inc ≤ a := by
  obtain ⟨x, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  obtain ⟨y, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  have : y < x := Nat.lt_of_mul_lt_mul_left lt
  calc inc * y + inc = inc * (y + 1) := by rw [Nat.mul_succ]
    _ ≤ inc * x := Nat.mul_le_mul_left _ this

/-- An absent validator in a leak: its effective balance falls to a threshold.

Absent means eligible and without the timely target flag, while its effective balance is high.

The traces count the epochs of the leak.

While the effective balance is above the threshold, each epoch is a leak epoch.

In it the score gains the bias, and the balance pays the effective balance times the new score.

That product is divided by the divisor, and the balance stops at zero.

So the validator may leave the leak, or the leak may end, once its effective balance is that low.

In every epoch of the traces the balance does not rise, so the validator never votes again.

The penalty may be larger, and later steps of the epoch may lower the balance further.

The effective balance then follows the balance at that point, with its hysteresis.

The balance may fall again before the next epoch, and it is assumed never to rise.

So no reward, deposit or consolidation reaches this validator during the traces.

The largest effective balance stays fixed.

At the start, the balance is within the upward band, or the effective balance reaches the largest.

The traces are assumptions, not derived from the state transition.

If the leak takes enough over at least one epoch, the effective balance is at most the threshold.

Enough leaves less than the threshold plus an increment, less the downward band.

The first effective balance, the largest and the threshold are whole numbers of increments.

So an effective balance above the threshold is at least the threshold plus an increment.

The increment must be positive and at most the upward band, as on mainnet. -/
theorem effectiveBalance_le_of_leak {balance settled effective : Nat → Gwei}
    {score : Nat → Nat} {largest : Gwei} {bias divisor threshold epochs : Nat}
    (bands : preset.IncrementWithinUpwardBand)
    (startAligned : effective 0 % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (largestAligned : largest % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (thresholdAligned : threshold % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (started : 0 < epochs)
    (startAbove : (balance 0).toNat ≤ (effective 0).toNat + preset.upwardBand ∨
      largest ≤ effective 0)
    (stays : ∀ t < epochs, (settled t).toNat ≤ (balance t).toNat)
    (scored : ∀ t < epochs, threshold < (effective t).toNat → score (t + 1) = score t + bias)
    (penalized : ∀ t < epochs, threshold < (effective t).toNat → (settled t).toNat ≤
      (balance t).toNat - (effective t).toNat * (score t + bias) / divisor)
    (updated : ∀ t < epochs,
      updatedEffectiveBalance preset largest (settled t) (effective t) = .ok (effective (t + 1)))
    (between : ∀ t < epochs, (balance (t + 1)).toNat ≤ (settled t).toNat)
    (enough : (balance 0).toNat -
        leakLoss (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (score 0) bias divisor
          epochs + preset.downwardBand <
      threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    (effective epochs).toNat ≤ threshold := by
  have incPos := bands.1
  have inv : ∀ t ≤ epochs, (balance t).toNat ≤ (effective t).toNat + preset.upwardBand ∨
      largest ≤ effective t := by
    intro t
    induction t with
    | zero => intro _; exact startAbove
    | succ t ih =>
      intro h
      have step := updatedEffectiveBalance_band bands (updated t (by omega))
      have := between t (by omega)
      rcases step with s | s
      · left; omega
      · right; exact s
  have anti : ∀ t < epochs, (effective (t + 1)).toNat ≤ (effective t).toNat := by
    intro t h
    have := stays t h
    have band : (settled t).toNat ≤ (effective t).toNat + preset.upwardBand ∨
        largest ≤ effective t := by
      rcases inv t (by omega) with b | b
      · left; omega
      · right; exact b
    exact UInt64.le_iff_toNat_le.mp (updatedEffectiveBalance_le_of_band band (updated t h))
  by_cases fin : (effective epochs).toNat ≤ threshold
  · exact fin
  exfalso
  have aligned : ∀ t ≤ epochs,
      (effective t).toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    have toNat : ∀ x : Gwei, x % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        x.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := fun x h => by
      have := congrArg UInt64.toNat h
      rwa [UInt64.toNat_mod] at this
    intro t
    induction t with
    | zero => intro _; exact toNat _ startAligned
    | succ t ih =>
      intro h
      have prev : (effective t) % preset.EFFECTIVE_BALANCE_INCREMENT = 0 := by
        have := ih (by omega)
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod]
        exact this
      exact toNat _ (updatedEffectiveBalance_aligned largestAligned prev (updated t (by omega)))
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat = inc at *
  have big : ∀ t ≤ epochs, threshold + inc ≤
      (effective t).toNat := by
    intro t ht
    have chain : ∀ k, t + k ≤ epochs → (effective (t + k)).toNat ≤ (effective t).toNat := by
      intro k
      induction k with
      | zero => intro _; exact Nat.le_refl _
      | succ k ih =>
        intro h
        have := anti (t + k) (by omega)
        have := ih (by omega)
        rw [← Nat.add_assoc]
        omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
    have := chain k (by omega)
    rw [← hk] at this
    exact add_le_of_lt_of_aligned (aligned t ht) thresholdAligned (by omega)
  have above : ∀ t < epochs, threshold < (effective t).toNat := fun t h => by
    have := big t (by omega)
    omega
  have scoreEq := score_eq fun t h => scored t h (above t h)
  have pen : ∀ t < epochs, (threshold + inc) * (score 0 + bias * (t + 1)) / divisor ≤
      (effective t).toNat * (score t + bias) / divisor := by
    intro t h
    apply Nat.div_le_div_right
    have : score t + bias = score 0 + bias * (t + 1) := by
      rw [scoreEq t (by omega), Nat.mul_succ]
      omega
    rw [this]
    exact Nat.mul_le_mul_right _ (big t (by omega))
  have balanceBound : ∀ t ≤ epochs,
      (balance t).toNat ≤
        (balance 0).toNat - leakLoss (threshold + inc) (score 0) bias divisor t := by
    intro t
    induction t with
    | zero => intro _; simp [leakLoss]
    | succ t ih =>
      intro h
      have prev := ih (by omega)
      have := between t (by omega)
      have := penalized t (by omega) (above t (by omega))
      have := pen t (by omega)
      rw [leakLoss_succ]
      generalize leakLoss (threshold + inc) (score 0) bias divisor t = loss at *
      generalize (threshold + inc) * (score 0 + bias * (t + 1)) / divisor = low at *
      generalize (effective t).toNat * (score t + bias) / divisor = high at *
      omega
  have settledBound : ∀ t < epochs,
      (settled t).toNat ≤
        (balance 0).toNat - leakLoss (threshold + inc) (score 0) bias divisor (t + 1) := by
    intro t h
    have := balanceBound t (by omega)
    have := penalized t h (above t h)
    have := pen t h
    rw [leakLoss_succ]
    generalize leakLoss (threshold + inc) (score 0) bias divisor t = loss at *
    generalize (threshold + inc) * (score 0 + bias * (t + 1)) / divisor = low at *
    generalize (effective t).toNat * (score t + bias) / divisor = high at *
    omega
  cases epochs with
  | zero => exact absurd started (Nat.lt_irrefl 0)
  | succ n =>
    have := settledBound n (by omega)
    have := updatedEffectiveBalance_le_add (updated n (by omega))
    have := big (n + 1) (Nat.le_refl _)
    omega

/-- After explicit leak epochs, the effective balance of an absent validator is at most a threshold.

It is at most the threshold in any epoch of the leak from that number on.

That number depends on the start balance, the threshold, the score bias, the divisor and the preset.

The hypotheses are those of the bound above.

The bias and the divisor must be positive.

The threshold plus an increment must exceed the downward band. -/
theorem effectiveBalance_le_of_leakEpochs {balance settled effective : Nat → Gwei}
    {score : Nat → Nat} {largest : Gwei} {bias divisor threshold epochs : Nat}
    (biasPos : 0 < bias) (divisorPos : 0 < divisor)
    (wide : preset.downwardBand < threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (bands : preset.IncrementWithinUpwardBand)
    (startAligned : effective 0 % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (largestAligned : largest % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (thresholdAligned : threshold % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startAbove : (balance 0).toNat ≤ (effective 0).toNat + preset.upwardBand ∨
      largest ≤ effective 0)
    (stays : ∀ t < epochs, (settled t).toNat ≤ (balance t).toNat)
    (scored : ∀ t < epochs, threshold < (effective t).toNat → score (t + 1) = score t + bias)
    (penalized : ∀ t < epochs, threshold < (effective t).toNat → (settled t).toNat ≤
      (balance t).toNat - (effective t).toNat * (score t + bias) / divisor)
    (updated : ∀ t < epochs,
      updatedEffectiveBalance preset largest (settled t) (effective t) = .ok (effective (t + 1)))
    (between : ∀ t < epochs, (balance (t + 1)).toNat ≤ (settled t).toNat)
    (long : leakEpochs (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) bias divisor
      ((balance 0).toNat + preset.downwardBand + 1 -
        (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ epochs) :
    (effective epochs).toNat ≤ threshold := by
  have epochsPos : 0 < epochs :=
    Nat.lt_of_lt_of_le (by unfold leakEpochs; exact Nat.succ_pos _) long
  have incPos := bands.1
  have floorPos : 0 < threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by omega
  have taken := le_leakLoss_leakEpochs (score := score 0) floorPos biasPos divisorPos
    (amount := (balance 0).toNat + preset.downwardBand + 1 -
      (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
  have mono := leakLoss_mono (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (score 0) bias
    divisor long
  exact effectiveBalance_le_of_leak bands startAligned largestAligned thresholdAligned epochsPos
    startAbove stays scored penalized updated between (by omega)

end EthLib.Consensus
