module

public import EthLib.Consensus.Proofs.Transition.InactivityLeakBetween
public import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
public import EthLib.Consensus.Proofs.Transition.InactivityLeakStake
public import EthLib.Consensus.Proofs.Transition.InactivityLeakTrace

/-!
# Proofs: a run of a leak brings the absent validators to a threshold

The trace bound of an inactivity leak takes four sequences of one validator as hypotheses.

They are its balance, its effective balance and its score before each epoch transition.

The fourth is its balance at the update of the effective balances.

This module builds them from a run of the chain, from Altair, and discharges those hypotheses.

The run visits one state before each epoch transition.

From each such state, the slot that ends the epoch runs the epoch transition.

Then slots that end no epoch, and blocks that credit nothing to the validator, lead to the next one.

Each epoch leaks and does not raise the finalized epoch.

The bound for one validator assumes this over the whole run.

While the effective balance of the validator is above the threshold, it is eligible.

Its flags then lack the timely target.

Once its effective balance is at most the threshold, its eligibility does not matter.

The bound then only needs its balance not to rise.

The run assumes that the largest effective balance of the validator stays fixed.

A consolidation request can switch its credentials to compounding and raise that cap.

The module then applies the run to every absent validator.

Either the leak stops or finality advances during the run.

Otherwise the voters hold two thirds of the active stake at its end.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- A run of a leak brings the effective balance of an absent validator to a threshold.

This holds from Altair.

The run visits a state before each of its epoch transitions.

The slot that leaves each such state ends an epoch, and leads to a second state.

Steps that credit nothing to the validator lead from that second state to the next visited one.

Each epoch transition starts in a leak and does not raise the finalized epoch.

The registry stays within its limit.

The key is that of the validator at the start of the run.

No pending deposit carries the key, and no pending consolidation targets the validator.

The largest effective balance of the validator stays the same over the run.

While its effective balance is above the threshold, it is eligible and its flags lack the target.

At the start its effective balance and that cap are whole numbers of increments.

Its balance is then at most its effective balance plus the upward band.

Otherwise its effective balance is at least the cap.

The threshold is a whole number of increments, and with an increment it exceeds the downward band.

The run lasts at least the number of epochs of the trace bound, from the starting balance.

The score bias and the penalty quotient must be positive.

The increment must be positive and at most the upward band, as on mainnet.

The mixes must span more than the seed lookahead plus two epochs.

The run stays within one fork.

On mainnet a validator that exits is no longer eligible.

So the threshold must be at least the effective balance of an absent validator when it exits.

Then the effective balance of the validator at the end of the run is at most the threshold. -/
theorem effectiveBalance_le_of_leakRun (altair : .altair ≤ fork)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (bands : preset.IncrementWithinUpwardBand)
    (biasPos : 0 < config.INACTIVITY_SCORE_BIAS.toNat)
    (quotientPos : 0 < (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)
    {states slotted : Nat → BeaconState preset fork} {epochs threshold index : Nat}
    {key : Cryptography.Bls.BLSPubkey} {largest : Gwei}
    (ends : ∀ t < epochs, ((states t).slot + 1) % preset.SLOTS_PER_EPOCH = 0)
    (epochSlot : ∀ t < epochs, advanceSlot config checks (states t) = .ok (slotted t))
    (quiet : ∀ t < epochs,
      Relation.ReflTransGen (QuietStep config checks index key) (slotted t) (states (t + 1)))
    (within : ∀ t < epochs, (states t).RegistryWithinLimit)
    (leak : ∀ t < epochs, isInInactivityLeak (states t) = .ok true)
    (stalled : ∀ t < epochs,
      (slotted t).finalizedCheckpoint.epoch ≤ (states t).finalizedCheckpoint.epoch)
    (unnamed : ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ deposit ∈ ((states t).pendingDeposits electra).data, deposit.pubkey ≠ key)
    (untargeted : ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ ((states t).pendingConsolidations electra).data,
        consolidation.targetIndex.toNat ≠ index)
    (capped : ∀ t < epochs, ∀ validator, (states t).validators.data[index]? = some validator →
      withdrawalMaxEffectiveBalance preset fork validator = largest)
    (absent : ∀ t < epochs, ∀ validator,
      (states t).validators.data[index]? = some validator →
        threshold < validator.effectiveBalance.toNat →
        isEligibleValidator (getPreviousEpoch (states t)) validator = .ok true ∧
          ∀ flags, ((states t).previousEpochParticipation altair).data[index]? = some flags →
            hasFlag flags TIMELY_TARGET_FLAG_INDEX = false)
    {validator : Validator} (found : (states 0).validators.data[index]? = some validator)
    (keyed : validator.pubkey = key)
    {balance : Gwei} (held : (states 0).balances.data[index]? = some balance)
    (startAligned : validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (largestAligned : largest % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (thresholdAligned : threshold % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startAbove : balance.toNat ≤ validator.effectiveBalance.toNat + preset.upwardBand ∨
      largest ≤ validator.effectiveBalance)
    (wide : preset.downwardBand < threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (long : leakEpochs (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      config.INACTIVITY_SCORE_BIAS.toNat
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)
      (balance.toNat + preset.downwardBand + 1 -
        (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ epochs) :
    ∃ now, (states epochs).validators.data[index]? = some now ∧
      now.effectiveBalance.toNat ≤ threshold := by
  -- Along the run the validator keeps its position, its key and a balance.
  have present : ∀ t ≤ epochs, ∃ current, (states t).validators.data[index]? = some current ∧
      current.pubkey = key ∧ index < (states t).balances.data.size := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨validator, found, keyed, (Array.getElem?_eq_some_iff.mp held).1⟩
    | succ t step =>
      intro bound
      obtain ⟨current, atCurrent, currentKey, -⟩ := step (by omega)
      obtain ⟨_, settled, _, now, -, atSettled, -, -, atNow, -, nowKey, -, -⟩ :=
        leakEpoch_advanceSlot altair (epochSlot t (by omega)) (ends t (by omega))
          (within t (by omega)) (leak t (by omega)) (stalled t (by omega)) atCurrent
          (currentKey ▸ unnamed t (by omega)) (untargeted t (by omega))
      obtain ⟨later, atLater, laterKey, -, laterHeld, -, -⟩ :=
        quietSteps_kept apart (quiet t (by omega)) atNow (nowKey.trans currentKey)
          (Array.getElem?_eq_some_iff.mp atSettled).1
      exact ⟨later, atLater, laterKey, laterHeld⟩
  -- The four sequences of the trace bound, read at the visited states and after each epoch slot.
  let balanceAt : Nat → Gwei := fun t => ((states t).balances.data[index]?).getD 0
  let settledAt : Nat → Gwei := fun t => ((slotted t).balances.data[index]?).getD 0
  let effectiveAt : Nat → Gwei := fun t =>
    (((states t).validators.data[index]?).map (·.effectiveBalance)).getD 0
  let scoreAt : Nat → Nat := fun t =>
    ((((states t).inactivityScores altair).data[index]?).map (·.toNat)).getD 0
  have facts : ∀ t < epochs, (settledAt t).toNat ≤ (balanceAt t).toNat ∧
      (threshold < (effectiveAt t).toNat →
        scoreAt (t + 1) = scoreAt t + config.INACTIVITY_SCORE_BIAS.toNat) ∧
      (threshold < (effectiveAt t).toNat → (settledAt t).toNat ≤ (balanceAt t).toNat -
        (effectiveAt t).toNat * (scoreAt t + config.INACTIVITY_SCORE_BIAS.toNat) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)) ∧
      updatedEffectiveBalance preset largest (settledAt t) (effectiveAt t) =
        .ok (effectiveAt (t + 1)) ∧
      (balanceAt (t + 1)).toNat ≤ (settledAt t).toNat := by
    intro t during
    obtain ⟨current, atCurrent, currentKey, -⟩ := present t (by omega)
    obtain ⟨balance', settled, effective, now, atBalance, atSettled, lower, effectiveOk, atNow,
      nowEffective, nowKey, -, guarded⟩ :=
      leakEpoch_advanceSlot altair (epochSlot t during) (ends t during) (within t during)
        (leak t during) (stalled t during) atCurrent (currentKey ▸ unnamed t during)
        (untargeted t during)
    obtain ⟨later, atLater, -, laterEffective, laterHeld, raised, scoreKept⟩ :=
      quietSteps_kept apart (quiet t during) atNow (nowKey.trans currentKey)
        (Array.getElem?_eq_some_iff.mp atSettled).1
    have balanceEq : balanceAt t = balance' := by simp only [balanceAt, atBalance, Option.getD_some]
    have settledEq : settledAt t = settled := by simp only [settledAt, atSettled, Option.getD_some]
    have effectiveEq : effectiveAt t = current.effectiveBalance := by
      simp only [effectiveAt, atCurrent, Option.map_some, Option.getD_some]
    have effectiveNext : effectiveAt (t + 1) = effective := by
      simp only [effectiveAt, atLater, Option.map_some, Option.getD_some, laterEffective,
        nowEffective]
    rw [balanceEq, settledEq, effectiveEq, effectiveNext]
    refine ⟨UInt64.le_iff_toNat_le.mp lower, fun above => ?_, fun above => ?_, ?_, ?_⟩
    · obtain ⟨eligible, untimely⟩ := absent t during current atCurrent above
      obtain ⟨score, score', atScore, atScore', scoreEq, -⟩ := guarded eligible untimely
      simp only [scoreAt, atScore, scoreKept altair, atScore', Option.map_some, Option.getD_some,
        scoreEq]
    · obtain ⟨eligible, untimely⟩ := absent t during current atCurrent above
      obtain ⟨score, score', atScore, -, scoreEq, paid⟩ := guarded eligible untimely
      simp only [scoreAt, atScore, Option.map_some, Option.getD_some, ← scoreEq]
      exact paid
    · rw [← capped t during current atCurrent]
      exact effectiveOk
    · obtain ⟨next, atNext⟩ : ∃ next, (states (t + 1)).balances.data[index]? = some next :=
        ⟨_, Array.getElem?_eq_getElem laterHeld⟩
      obtain ⟨earlier, atEarlier, nextLower⟩ := raised next atNext
      rw [atSettled, Option.some.injEq] at atEarlier
      subst atEarlier
      simp only [balanceAt, atNext, Option.getD_some]
      exact UInt64.le_iff_toNat_le.mp nextLower
  have startBalance : balanceAt 0 = balance := by
    simp only [balanceAt, held, Option.getD_some]
  have startEffective : effectiveAt 0 = validator.effectiveBalance := by
    simp only [effectiveAt, found, Option.map_some, Option.getD_some]
  have bound := effectiveBalance_le_of_leakEpochs (balance := balanceAt) (settled := settledAt)
    (effective := effectiveAt) (score := scoreAt) (largest := largest) biasPos
    (Nat.mul_pos biasPos quotientPos) wide bands (startEffective ▸ startAligned) largestAligned
    thresholdAligned (startBalance ▸ startEffective ▸ startAbove)
    (fun t during => (facts t during).1)
    (fun t during => (facts t during).2.1) (fun t during => (facts t during).2.2.1)
    (fun t during => (facts t during).2.2.2.1) (fun t during => (facts t during).2.2.2.2)
    (startBalance ▸ long)
  obtain ⟨now, atNow, -, -⟩ := present epochs (Nat.le_refl _)
  refine ⟨now, atNow, ?_⟩
  simpa only [effectiveAt, atNow, Option.map_some, Option.getD_some] using bound

/-- A run of a leak stops leaking, advances finality, or ends with two thirds for the voters.

This holds from Altair.

The run visits a state before each of its epoch transitions.

The slot that leaves each such state ends an epoch, and leads to a second state.

Steps that credit nothing to any absent validator then lead to the next visited state.

Each absent validator keeps its own key and its own largest effective balance over the run.

Each one is in the registry at the start, with its key and a balance at most a common limit.

At the start its effective balance is a whole number of increments, and so is its cap.

At the start its balance is at most its effective balance plus the upward band.

Otherwise its effective balance is at least its cap.

No pending deposit carries the key of one, and no pending consolidation targets one.

While the effective balance of one is above the threshold, it is eligible and misses the target.

In the final state, each active validator is a voter or an absent validator.

The voters are meant to be the unslashed attesters of the target, but any list works.

The voters need not be active, so their balance may count inactive validators.

Twice the number of absent validators times the threshold is at most the balance of the voters.

That balance is read in the final state.

The threshold is a whole number of increments, and with an increment it exceeds the downward band.

The run lasts at least the number of epochs of the trace bound, from that common limit.

The score bias and the penalty quotient must be positive.

The increment must be positive and at most the upward band, as on mainnet.

The mixes must span more than the seed lookahead plus two epochs.

The registry stays within its limit, up to the final state.

The run stays within one fork.

Then some visited state does not leak, or the finalized epoch rises in the slot that leaves it.

Otherwise, in the final state, twice the active balance is at most three times that of the voters.

On mainnet a validator that exits is no longer eligible.

So the threshold must be at least the effective balance of an absent validator when it exits. -/
theorem twoThirds_of_leakRun (altair : .altair ≤ fork)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (bands : preset.IncrementWithinUpwardBand)
    (biasPos : 0 < config.INACTIVITY_SCORE_BIAS.toNat)
    (quotientPos : 0 < (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)
    {states slotted : Nat → BeaconState preset fork} {epochs threshold start : Nat}
    {voters : List ValidatorIndex} {absents : List Nat}
    {keys : Nat → Cryptography.Bls.BLSPubkey} {largest : Nat → Gwei} {total voterTotal : Gwei}
    (ends : ∀ t < epochs, ((states t).slot + 1) % preset.SLOTS_PER_EPOCH = 0)
    (epochSlot : ∀ t < epochs, advanceSlot config checks (states t) = .ok (slotted t))
    (quiet : ∀ j ∈ absents, ∀ t < epochs,
      Relation.ReflTransGen (QuietStep config checks j (keys j)) (slotted t) (states (t + 1)))
    (within : ∀ t ≤ epochs, (states t).RegistryWithinLimit)
    (unnamed : ∀ j ∈ absents, ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ deposit ∈ ((states t).pendingDeposits electra).data, deposit.pubkey ≠ keys j)
    (untargeted : ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ ((states t).pendingConsolidations electra).data,
        consolidation.targetIndex.toNat ∉ absents)
    (capped : ∀ j ∈ absents, ∀ t < epochs, ∀ validator,
      (states t).validators.data[j]? = some validator →
        withdrawalMaxEffectiveBalance preset fork validator = largest j)
    (absent : ∀ j ∈ absents, ∀ t < epochs, ∀ validator,
      (states t).validators.data[j]? = some validator →
        threshold < validator.effectiveBalance.toNat →
        isEligibleValidator (getPreviousEpoch (states t)) validator = .ok true ∧
          ∀ flags, ((states t).previousEpochParticipation altair).data[j]? = some flags →
            hasFlag flags TIMELY_TARGET_FLAG_INDEX = false)
    (started : ∀ j ∈ absents, ∃ validator balance,
      (states 0).validators.data[j]? = some validator ∧ validator.pubkey = keys j ∧
      (states 0).balances.data[j]? = some balance ∧
      validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      (balance.toNat ≤ validator.effectiveBalance.toNat + preset.upwardBand ∨
        largest j ≤ validator.effectiveBalance) ∧
      balance.toNat ≤ start)
    (largestAligned : ∀ j ∈ absents, largest j % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (thresholdAligned : threshold % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (wide : preset.downwardBand < threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (active : getTotalActiveBalance (states epochs) = .ok total)
    (voting : getTotalBalance (states epochs) voters = .ok voterTotal)
    (covered : ∀ j (inside : j < (states epochs).validators.data.size),
      isActiveValidator (states epochs).validators.data[j] (getCurrentEpoch (states epochs)) =
        true → j.toUInt64 ∈ voters ∨ j ∈ absents)
    (strong : 2 * absents.length * threshold ≤ voterTotal.toNat)
    (long : leakEpochs (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      config.INACTIVITY_SCORE_BIAS.toNat
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)
      (start + preset.downwardBand + 1 -
        (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ epochs) :
    (∃ t < epochs, isInInactivityLeak (states t) ≠ .ok true ∨
      (states t).finalizedCheckpoint.epoch < (slotted t).finalizedCheckpoint.epoch) ∨
      2 * total.toNat ≤ 3 * voterTotal.toNat := by
  by_cases stopped : ∃ t < epochs, isInInactivityLeak (states t) ≠ .ok true ∨
      (states t).finalizedCheckpoint.epoch < (slotted t).finalizedCheckpoint.epoch
  · exact .inl stopped
  simp only [not_exists, not_and, not_or, ne_eq, not_not, UInt64.not_lt] at stopped
  have leak : ∀ t < epochs, isInInactivityLeak (states t) = .ok true :=
    fun t during => (stopped t during).1
  have stalled : ∀ t < epochs,
      (slotted t).finalizedCheckpoint.epoch ≤ (states t).finalizedCheckpoint.epoch :=
    fun t during => (stopped t during).2
  refine .inr (twoThirds_of_effectiveBalance_le (within epochs (Nat.le_refl _)) active voting
    covered (fun j member inside => ?_) strong)
  obtain ⟨validator, balance, found, keyed, held, startAligned, startAbove, bounded⟩ :=
    started j member
  obtain ⟨now, atNow, low⟩ := effectiveBalance_le_of_leakRun altair apart bands biasPos
    quotientPos ends epochSlot (quiet j member) (fun t during => within t (Nat.le_of_lt during))
    leak stalled (unnamed j member)
    (fun t during electra consolidation listed same =>
      untargeted t during electra consolidation listed (same ▸ member))
    (capped j member) (absent j member) found keyed held startAligned (largestAligned j member)
    thresholdAligned startAbove wide
    (Nat.le_trans (leakEpochs_mono (by omega)) long)
  rw [(Array.getElem?_eq_some_iff.mp atNow).2]
  exact low

end EthLib.Consensus
