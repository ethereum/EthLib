module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.Requests
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Bounds for the sources of balance drift

These contracts use the amounts computed by the transition, not arbitrary accounting caps.

Epoch-interval bounds sum the per-call amounts, including queues inherited at the first state.

Deposits to withdrawn validators bypass the Electra churn and are accounted separately.

Consolidations count both their debit and credit even though their net balance change is zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The sum of a list of amounts, as a natural number. -/
def sumAmounts (values : Array Gwei) : Nat := (values.toList.map (·.toNat)).sum

/-- The sum of all balances of a state. -/
def totalBalance {fork : Fork} (s : BeaconState preset fork) : Nat := sumAmounts s.balances.data

/-- Positive changes are summed per index, so a transfer cannot cancel a loss elsewhere. -/
def balanceCredits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range t.balances.data.size,
    (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)

/-- Negative changes are summed per index, as for the credits. -/
def balanceDebits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range s.balances.data.size,
    (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i)

private theorem credits_increase {fork : Fork} {s t : BeaconState preset fork}
    {i : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s i amount = .ok t) :
    balanceCredits s t = amount.toNat ∧ balanceDebits s t = 0 := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  have point (j : Nat) :
      actualBalanceAt ⟨fork, s.putBalance i.toNat inside (s.balances.data[i.toNat] + amount)⟩ j =
        actualBalanceAt ⟨fork, s⟩ j + if j = i.toNat then amount.toNat else 0 := by
    by_cases same : j = i.toNat
    · subst j
      simp [actualBalanceAt, BeaconState.putBalance, inside, toNat_add_of_lt fits]
    · simp [actualBalanceAt, BeaconState.putBalance, same, Ne.symm same]
  have size : (s.putBalance i.toNat inside
      (s.balances.data[i.toNat] + amount)).balances.data.size =
        s.balances.data.size := by simp [BeaconState.putBalance]
  simp [balanceCredits, balanceDebits, size, point, Finset.sum_ite_eq', inside]

private theorem debits_decrease {fork : Fork} {s t : BeaconState preset fork}
    {i : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s i amount = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤ amount.toNat := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  have point (j : Nat) :
      actualBalanceAt ⟨fork, s.putBalance i.toNat inside
        (saturatingSub s.balances.data[i.toNat] amount)⟩ j =
        actualBalanceAt ⟨fork, s⟩ j - if j = i.toNat then amount.toNat else 0 := by
    by_cases same : j = i.toNat
    · subst j
      simp [actualBalanceAt, BeaconState.putBalance, inside, toNat_saturatingSub]
    · simp [actualBalanceAt, BeaconState.putBalance, same, Ne.symm same]
  have size : (s.putBalance i.toNat inside
      (saturatingSub s.balances.data[i.toNat] amount)).balances.data.size =
        s.balances.data.size := by simp [BeaconState.putBalance]
  constructor
  · simp [balanceCredits, size, point]
  · unfold balanceDebits
    simp only [point]
    calc
      _ ≤ ∑ j ∈ Finset.range s.balances.data.size,
          if j = i.toNat then amount.toNat else 0 := by
        apply Finset.sum_le_sum
        intro j _
        omega
      _ = amount.toNat := by simp [Finset.sum_ite_eq', inside]

private theorem credits_triangle {fork : Fork} (s u t : BeaconState preset fork)
    (size : t.balances.data.size = u.balances.data.size) :
    balanceCredits s t ≤ balanceCredits s u + balanceCredits u t := by
  unfold balanceCredits
  rw [← size, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  omega

private theorem debits_triangle {fork : Fork} (s u t : BeaconState preset fork)
    (size : s.balances.data.size = u.balances.data.size) :
    balanceDebits s t ≤ balanceDebits s u + balanceDebits u t := by
  unfold balanceDebits
  rw [← size, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  omega

private theorem credits_triangle_growing {fork : Fork} (s u t : BeaconState preset fork)
    (size : u.balances.data.size ≤ t.balances.data.size) :
    balanceCredits s t ≤ balanceCredits s u + balanceCredits u t := by
  -- Indices beyond the intermediate array contribute zero to its credits.
  have extend : (∑ i ∈ Finset.range t.balances.data.size,
      (actualBalanceAt ⟨fork, u⟩ i - actualBalanceAt ⟨fork, s⟩ i)) = balanceCredits s u := by
    symm
    apply Finset.sum_subset (Finset.range_mono size)
    intro i _ outside
    simp only [Finset.mem_range, not_lt] at outside
    simp [actualBalanceAt, Array.getElem?_eq_none outside]
  unfold balanceCredits at *
  rw [← extend, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  omega

private theorem debits_triangle_growing {fork : Fork} (s u t : BeaconState preset fork)
    (size : s.balances.data.size ≤ u.balances.data.size) :
    balanceDebits s t ≤ balanceDebits s u + balanceDebits u t := by
  have upper : (∑ i ∈ Finset.range s.balances.data.size,
      (actualBalanceAt ⟨fork, u⟩ i - actualBalanceAt ⟨fork, t⟩ i)) ≤ balanceDebits u t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono size)
    intros
    omega
  unfold balanceDebits at *
  have point : (∑ i ∈ Finset.range s.balances.data.size,
      (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i)) ≤
        (∑ i ∈ Finset.range s.balances.data.size,
          (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, u⟩ i)) +
        (∑ i ∈ Finset.range s.balances.data.size,
          (actualBalanceAt ⟨fork, u⟩ i - actualBalanceAt ⟨fork, t⟩ i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    omega
  omega

/-- Rewards and ordinary penalties are kept separate from the inactivity pass. -/
def rewardPasses {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError (List (Array Gwei × Array Gwei)) := do
  if getCurrentEpoch s = GENESIS_EPOCH then return []
  if altair : .altair ≤ fork then
    (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM (getFlagIndexDeltas s altair)
  else
    let early := Nat.lt_of_not_le altair
    return [← getSourceDeltas s early, ← getTargetDeltas s early,
      ← getHeadDeltas s early, ← getInclusionDelayDeltas s early]

/-- Both recipient credits are included, also when proposer and whistleblower coincide. -/
theorem initial_slashing_bounds {fork : Fork} (s t : BeaconState preset fork)
    (i : ValidatorIndex) (whistleblower : Option ValidatorIndex) (v : Validator)
    (found : getValidator s i = .ok v)
    (ok : slashValidator config s i whistleblower = .ok t) :
    balanceDebits s t ≤ v.effectiveBalance.toNat /
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    balanceCredits s t ≤ v.effectiveBalance.toNat /
      (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  obtain ⟨exited, validator, withdrawable, marked, slashed, total, slashings, lowered,
    proposer, reward, raised, last, exit, validatorOk, _, mark, _, _, _, lower, _, share,
    raise, lastOk, final⟩ := slashValidator_ok ok
  have exitFacts : exited.balances = s.balances ∧
      validator.effectiveBalance = v.effectiveBalance := by
    obtain ⟨v', found', exitedAlready | ⟨_, queued, epoch, withdrawable, queue, _, set⟩⟩ :=
      initiateValidatorExit_ok exit
    · have vv : v' = v := Except.ok.inj (found'.symm.trans found)
      subst v'
      rcases exitedAlready with ⟨_, rfl⟩
      have vv : validator = v := Except.ok.inj (validatorOk.symm.trans found)
      exact ⟨rfl, congrArg Validator.effectiveBalance vv⟩
    · have vv : v' = v := Except.ok.inj (found'.symm.trans found)
      subst v'
      have vv := getValidator_setValidator_self set
      have veq := Except.ok.inj (validatorOk.symm.trans vv)
      have effective := congrArg (fun x => x.effectiveBalance) veq
      obtain ⟨_, rfl⟩ := setValidator_ok set
      exact ⟨(exitQueue_validators queue).2, effective⟩
  have markedBalance : marked.balances = s.balances := by
    obtain ⟨_, rfl⟩ := setValidator_ok mark
    exact exitFacts.1
  have shareLe : reward.toNat ≤
      (validator.effectiveBalance /
        (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat := by
    unfold proposerShare at share
    split at share
    · simp only [bind_ok_iff, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq] at share
      obtain ⟨product, productOk, rfl⟩ := share
      have productEq := (mulChecked_ok_iff.mp productOk).2
      rw [UInt64.toNat_div, productEq]
      change _ * 8 / 64 ≤ _
      omega
    · simp only [pure, Except.pure, Except.ok.injEq] at share
      subst reward
      exact Nat.div_le_self _ _
  have lo := debits_decrease lower
  have up := credits_increase raise
  have tail := credits_increase lastOk
  have firstCredits := credits_triangle { marked with slashings } lowered raised
    (sameSizes_increaseBalance raise).2
  have firstDebits := debits_triangle { marked with slashings } lowered raised
    (sameSizes_decreaseBalance lower).2.symm
  have secondCredits := credits_triangle { marked with slashings } raised last
    (sameSizes_increaseBalance lastOk).2
  have secondDebits := debits_triangle { marked with slashings } raised last
    ((sameSizes_increaseBalance raise).2.trans (sameSizes_decreaseBalance lower).2).symm
  have leftReward : (validator.effectiveBalance /
      (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT - reward).toNat =
        (validator.effectiveBalance /
          (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat -
            reward.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr shareLe)
  have bound : balanceDebits { marked with slashings } last ≤
      (validator.effectiveBalance /
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT).toNat ∧
      balanceCredits { marked with slashings } last ≤
      (validator.effectiveBalance /
        (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat := by
    omega
  have finalBalance : t.balances = last.balances := by
    rw [final]
    split <;> rfl
  simpa only [balanceDebits, balanceCredits, actualBalanceAt, finalBalance, markedBalance,
    UInt64.toNat_div, exitFacts.2] using bound

/-- Sum only due penalties, with the fork's actual rounding and adjusted slashing balance. -/
def delayedSlashingLimit {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError Nat := do
  let total ← liftAccessor (getTotalActiveBalance s)
  let slashed ← slashingsSum s
  let adjusted := min (slashed.toNat *
    (EthLib.Consensus.parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat
  let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  return (s.validators.data.toList.map fun v =>
    if SlashingPenaltyDue preset (getCurrentEpoch s) v then
      if .pectra ≤ fork then
        adjusted / (total.toNat / increment) * (v.effectiveBalance.toNat / increment)
      else v.effectiveBalance.toNat / increment * adjusted / total.toNat * increment
    else 0).sum

/-- No penalty is charged merely because a validator has effective stake. -/
theorem delayed_slashing_bounds {fork : Fork} (s t : BeaconState preset fork)
    (within : s.RegistryWithinLimit)
    (ok : processSlashings s = .ok t) :
    ∃ limit, delayedSlashingLimit s = .ok limit ∧
      balanceCredits s t = 0 ∧ balanceDebits s t ≤ limit := by
  have sumLookup (xs : List Nat) (n : Nat) :
      (∑ i ∈ Finset.range n, xs[i]?.getD 0) ≤ xs.sum := by
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
        rw [Finset.sum_range_succ']
        simpa [Nat.add_comm] using Nat.add_le_add_right (ih n) x
  have aggregate (penalty : Validator → Nat)
      (point : ∀ i, actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i -
        ((s.validators.data[i]?).map penalty).getD 0) :
      balanceCredits s t = 0 ∧
      balanceDebits s t ≤ (s.validators.data.toList.map penalty).sum := by
    constructor
    · simp [balanceCredits, point]
    · calc
        balanceDebits s t ≤ ∑ i ∈ Finset.range s.balances.data.size,
            ((s.validators.data[i]?).map penalty).getD 0 := by
          unfold balanceDebits
          apply Finset.sum_le_sum
          intro i _
          rw [point]
          omega
        _ ≤ _ := by
          simpa using sumLookup (s.validators.data.toList.map penalty) s.balances.data.size
  have pointOf (penalty : Validator → Nat)
      (each : ∀ i, (i < s.validators.data.size → ∃ v,
        s.validators.data[i]? = some v ∧
        t.balances.data[i]?.map UInt64.toNat = s.balances.data[i]?.map
          (fun b => b.toNat - penalty v)) ∧
        (s.validators.data.size ≤ i → t.balances.data[i]? = s.balances.data[i]?)) :
      ∀ i, actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i -
        ((s.validators.data[i]?).map penalty).getD 0 := by
    intro i
    -- The slashing pass leaves balances beyond the registry unchanged.
    by_cases inside : i < s.validators.data.size
    · obtain ⟨v, found, h⟩ := (each i).1 inside
      unfold actualBalanceAt
      rw [h, found]
      cases s.balances.data[i]? <;> simp
    · simp [actualBalanceAt, (each i).2 (Nat.le_of_not_gt inside),
        Array.getElem?_eq_none (Nat.le_of_not_gt inside)]
  by_cases electra : .pectra ≤ fork
  · obtain ⟨total, slashed, totalOk, slashedOk, _, each⟩ :=
      processSlashings_balances_toNat_of_electra electra within ok
    let penalty (v : Validator) : Nat :=
      if SlashingPenaltyDue preset (getCurrentEpoch s) v then
        min (slashed.toNat *
          (EthLib.Consensus.parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat)
          total.toNat / (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
            (v.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      else 0
    refine ⟨(s.validators.data.toList.map penalty).sum, ?_,
      aggregate penalty (pointOf penalty each)⟩
    simp [delayedSlashingLimit, liftAccessor, totalOk, slashedOk, electra, penalty,
      bind, Except.bind, pure, Except.pure, Except.mapError]
  · obtain ⟨total, slashed, totalOk, slashedOk, _, each⟩ :=
      processSlashings_balances_toNat_of_lt_electra (Nat.lt_of_not_le electra) ok
    let penalty (v : Validator) : Nat :=
      if SlashingPenaltyDue preset (getCurrentEpoch s) v then
        v.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          min (slashed.toNat *
            (EthLib.Consensus.parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat)
            total.toNat / total.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      else 0
    refine ⟨(s.validators.data.toList.map penalty).sum, ?_,
      aggregate penalty (pointOf penalty each)⟩
    simp [delayedSlashingLimit, liftAccessor, totalOk, slashedOk, electra, penalty,
      bind, Except.bind, pure, Except.pure, Except.mapError]

theorem sync_reward_bounds {fork : Fork} (s t : BeaconState preset fork)
    (reward proposerReward : Gwei) (proposer : Except AccessorError ValidatorIndex)
    (member : ValidatorIndex × Bool)
    (ok : applySyncReward reward proposerReward proposer s member = .ok t) :
    balanceCredits s t ≤ (if member.2 then reward.toNat + proposerReward.toNat else 0) ∧
    balanceDebits s t ≤ (if member.2 then 0 else reward.toNat) := by
  unfold applySyncReward at ok
  split at ok
  · rename_i signed
    simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨u, first, p, _, last⟩ := ok
    have firstBounds := credits_increase first
    have lastBounds := credits_increase last
    have credits := credits_triangle s u t (sameSizes_increaseBalance last).2
    have debits := debits_triangle s u t (sameSizes_increaseBalance first).2.symm
    simp only [signed, ↓reduceIte]
    omega
  · rename_i absent
    have bounds := debits_decrease (liftAccessor_ok.mp ok)
    simpa [absent] using bounds

/-- Recompute the proposer credit from the newly set participation flags. -/
def attestationCredit {fork : Fork} (s : BeaconState preset fork)
    (att : Attestation preset fork) (parent : Slot) : Except TransitionError Nat := do
  if altair : .altair ≤ fork then
    let earned ← liftAccessor
      (getAttestationParticipationFlagIndices s att.data (s.slot - att.data.slot) parent)
    let participation := if att.data.target.epoch == getCurrentEpoch s then
        s.currentEpochParticipation altair else s.previousEpochParticipation altair
    let total ← liftAccessor (getTotalActiveBalance s)
    let attesters ← liftAccessor (getAttestingIndices s att)
    let (_, numerator) ← attesters.foldlM (addAttesterFlags s total earned) (participation, 0)
    let denominator :=
      (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT
    return (numerator / denominator).toNat
  else return 0

/-- Attestation proposer rewards are the checked numerator divided by the protocol denominator. -/
theorem attestation_proposer_bound {fork : Fork} (s t : BeaconState preset fork)
    (att : Attestation preset fork) (parent : Slot) (early : fork < .glamsterdam)
    (ok : processAttestation config checks s parent att = .ok t) :
    ∃ credit, attestationCredit s att parent = .ok credit ∧
      balanceDebits s t = 0 ∧ balanceCredits s t ≤ credit := by
  by_cases altair : .altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte, processAttestationAltair,
      bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _, total,
      totalOk, attesters, attestersOk, pair, flagsOk, proposer, _, u, raised, final⟩ := ok
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
    simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
    subst t
    refine ⟨(pair.2 /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat,
      ?_, ?_⟩
    · simp only [attestationCredit, altair, ↓reduceDIte, liftAccessor, earnedOk, totalOk,
        attestersOk, Except.mapError, bind, Except.bind, flagsOk]
      rfl
    · have bounds := credits_increase raised
      have kept : (setEpochParticipation s
          (att.data.target.epoch == getCurrentEpoch s) pair.1).balances = s.balances := by
        unfold setEpochParticipation
        split <;> rfl
      simpa only [balanceCredits, balanceDebits, actualBalanceAt, kept]
        using And.intro bounds.2 bounds.1.le
  · obtain ⟨_, _, _, _, _, recorded, _⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) ok
    have kept : t.balances = s.balances := by
      have h := recordPendingAttestation_ok recorded
      split at h <;> have eq := congrArg (fun x => x.balances) h.2 <;> exact eq
    refine ⟨0, by simp [attestationCredit, altair, pure, Except.pure], ?_⟩
    simp [balanceDebits, balanceCredits, actualBalanceAt, kept]

/-- The amount is an input, so top-ups are not silently bounded by activation churn. -/
theorem deposit_credit_bound {fork : Fork} (s t : BeaconState preset fork)
    («matches» : BalancesMatch s)
    (deposit : PendingDeposit) (ok : applyPendingDeposit config checks s deposit = .ok t) :
    balanceDebits s t = 0 ∧ balanceCredits s t ≤ deposit.amount.toNat := by
  have append {t : BeaconState preset fork}
      (balances : t.balances.data = s.balances.data.push deposit.amount) :
      balanceDebits s t = 0 ∧ balanceCredits s t ≤ deposit.amount.toNat := by
    -- Matching lengths makes a new validator append, rather than overwrite, a balance.
    have old (j : Nat) (hj : j < s.balances.data.size) :
        actualBalanceAt ⟨fork, t⟩ j = actualBalanceAt ⟨fork, s⟩ j := by
      simp [actualBalanceAt, balances, Array.getElem?_push, hj, Nat.ne_of_lt hj]
    constructor
    · apply Finset.sum_eq_zero
      intro j hj
      simp [old j (Finset.mem_range.mp hj)]
    · unfold balanceCredits
      have size : t.balances.data.size = s.balances.data.size + 1 := by
        simp [balances]
      rw [size, Finset.sum_range_succ]
      have zero : (∑ j ∈ Finset.range s.balances.data.size,
          (actualBalanceAt ⟨fork, t⟩ j - actualBalanceAt ⟨fork, s⟩ j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp [old j (Finset.mem_range.mp hj)]
      rw [zero]
      simp [actualBalanceAt, balances]
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok
      simp [balanceCredits, balanceDebits]
    · simp only [bind, Except.bind] at ok
      split at ok
      · cases ok
      · split at ok
        · exact append (addValidatorToRegistry_push ok «matches»).2
        · cases ok
          simp [balanceCredits, balanceDebits]
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨i, _, added⟩ := ok
    have bounds := credits_increase added
    exact ⟨bounds.2, bounds.1.le⟩

/-- Deposits retained or postponed by the real pass are not charged in this interval. -/
def consumedDeposits {fork : Fork} (s t : BeaconState preset fork) (electra : .pectra ≤ fork) :
    Nat :=
  ((s.pendingDeposits electra).data.toList.map fun d => d.amount.toNat).sum -
    ((t.pendingDeposits electra).data.toList.map fun d => d.amount.toNat).sum

/-- This covers top-ups and withdrawn-key exceptions without charging an unprocessed queue. -/
theorem pending_deposit_bound {fork : Fork} (s t : BeaconState preset fork)
    («matches» : BalancesMatch s)
    (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    balanceDebits s t = 0 ∧ balanceCredits s t ≤ consumedDeposits s t electra := by
  have fold (ds : List PendingDeposit) (s t : BeaconState preset fork)
      (hm : BalancesMatch s)
      (ok : ds.foldlM (applyPendingDeposit config checks) s = .ok t) :
      balanceDebits s t = 0 ∧
        balanceCredits s t ≤ (ds.map fun d => d.amount.toNat).sum ∧
        s.balances.data.size ≤ t.balances.data.size := by
    induction ds generalizing s with
    | nil =>
      cases ok
      simp [balanceCredits, balanceDebits]
    | cons d ds ih =>
      simp only [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨u, first, last⟩ := ok
      have hu := (applyPendingDeposit_kept first).1 hm
      have sizes : s.balances.data.size ≤ u.balances.data.size := by
        unfold applyPendingDeposit at first
        split at first
        · split at first
          · cases first; exact Nat.le_refl _
          · simp only [bind, Except.bind] at first
            split at first
            · cases first
            · split at first
              · rw [(addValidatorToRegistry_push first hm).2, Array.size_push]
                omega
              · cases first; exact Nat.le_refl _
        · simp only [liftAccessor_ok, bind_ok_iff] at first
          obtain ⟨_, _, first⟩ := first
          exact (sameSizes_increaseBalance first).2.ge
      have a := deposit_credit_bound s u hm d first
      have b := ih u hu last
      have credits := credits_triangle_growing s u t b.2.2
      have debits := debits_triangle_growing s u t sizes
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega, sizes.trans b.2.2⟩
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, _, _, _,
    perm, steps, rfl⟩ := processPendingDeposits_applied ok
  have bounds := fold applied s next «matches» steps
  have amounts := (perm.map (fun d => d.amount.toNat)).sum_eq
  -- Postponed deposits return to the queue, so only applied amounts are consumed.
  have consumed : consumedDeposits s
      { next with
        pendingDeposits := fun _ => pending
        depositBalanceToConsume := fun _ => carried } electra =
      (applied.map fun d => d.amount.toNat).sum := by
    unfold consumedDeposits
    rw [queue]
    change _ - (pending.data.toList.map _).sum = _
    rw [kept]
    simp only [List.map_append, List.sum_append] at amounts ⊢
    omega
  rw [consumed]
  exact ⟨bounds.1, bounds.2.1⟩

/-- The real pass removes a prefix; slashed entries are dropped without a transfer. -/
def consumedConsolidations {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) : Nat :=
  (((s.pendingConsolidations electra).data.toList.take
    ((s.pendingConsolidations electra).data.size - (t.pendingConsolidations electra).data.size)).map
      fun c => match s.validators.data[c.sourceIndex.toNat]? with
        | none => 0
        | some v => if v.slashed then 0 else v.effectiveBalance.toNat).sum

/-- Consolidations cannot mint balance, but a target can gain all the source's moved balance. -/
theorem consolidation_transfer_bound {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (ok : processPendingConsolidations s electra = .ok t) :
    totalBalance t = totalBalance s ∧
    balanceCredits s t ≤ consumedConsolidations s t electra ∧
    balanceDebits s t ≤ consumedConsolidations s t electra := by
  let cost (s : BeaconState preset fork) (c : PendingConsolidation) : Nat :=
    match s.validators.data[c.sourceIndex.toNat]? with
    | none => 0
    | some v => if v.slashed then 0 else v.effectiveBalance.toNat
  have pass (cs : List PendingConsolidation) (epoch : Epoch)
      (s t : BeaconState preset fork) (read : Nat)
      (ok : passPendingConsolidations epoch s cs = .ok (t, read)) :
      read ≤ cs.length ∧ t.balances.data.size = s.balances.data.size ∧
      balanceCredits s t ≤ ((cs.take read).map (cost s)).sum ∧
      balanceDebits s t ≤ ((cs.take read).map (cost s)).sum := by
    induction cs generalizing s read with
    | nil =>
      cases ok
      simp [balanceCredits, balanceDebits]
    | cons c cs ih =>
      simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨v, found, ok⟩ := ok
      have found' : s.validators.data[c.sourceIndex.toNat]? = some v := by
        unfold getValidator at found
        split at found <;> cases found
        assumption
      split at ok
      · rename_i slashed
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
        obtain ⟨⟨u, n⟩, rest, rfl, rfl⟩ := ok
        have later := ih s n rest
        have head : cost s c = 0 := by simp [cost, found', slashed]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, head, Nat.zero_add]
        exact ⟨Nat.succ_le_succ later.1, later.2⟩
      · rename_i notSlashed
        split at ok
        · cases ok
          simp [balanceCredits, balanceDebits]
        · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at ok
          obtain ⟨balance, readBalance, lowered, lower, raised, raise,
            ⟨u, n⟩, rest, rfl, rfl⟩ := ok
          have later := ih raised n rest
          dsimp only at later
          have kept := (increaseBalance_validators raise).trans (decreaseBalance_validators lower)
          -- Transfers keep the registry, so every later cost uses the original effective balance.
          have costs : cost raised = cost s := by simp only [cost, kept]
          rw [costs] at later
          have lo := debits_decrease lower
          have up := credits_increase raise
          have size1 := (sameSizes_decreaseBalance lower).2
          have size2 := (sameSizes_increaseBalance raise).2
          have firstCredits := credits_triangle s lowered raised size2
          have firstDebits := debits_triangle s lowered raised size1.symm
          have nextCredits := credits_triangle s raised u later.2.1
          have nextDebits := debits_triangle s raised u (size2.trans size1).symm
          have cap : (min balance v.effectiveBalance).toNat ≤ v.effectiveBalance.toNat := by
            rw [toNat_min]
            exact Nat.min_le_right _ _
          have head : cost s c = v.effectiveBalance.toNat := by
            simp [cost, found', notSlashed]
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons, head]
          exact ⟨by simpa using Nat.succ_le_succ later.1,
            later.2.1.trans (size2.trans size1), by omega, by omega⟩
  obtain ⟨⟨u, n⟩, processed, balances, queue⟩ := processPendingConsolidations_pass ok
  have facts := pass _ _ s u n processed
  have count : (s.pendingConsolidations electra).data.size -
      (t.pendingConsolidations electra).data.size = n := by
    have lengths := congrArg List.length queue
    simp only [Array.length_toList, List.length_drop] at lengths
    have le := facts.1
    simp only [Array.length_toList] at le
    omega
  refine ⟨(processPendingConsolidations_kept ok).2, ?_, ?_⟩
  · simpa only [consumedConsolidations, count, balanceCredits, actualBalanceAt, balances]
      using facts.2.2.1
  · simpa only [consumedConsolidations, count, balanceDebits, actualBalanceAt, balances]
      using facts.2.2.2

theorem withdrawal_debit_bound {fork : Fork} (s t : BeaconState preset fork)
    (withdrawals : Array Withdrawal) (ok : applyWithdrawals s withdrawals = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤
      (withdrawals.toList.map fun w => w.amount.toNat).sum := by
  have one {s t : BeaconState preset fork} (w : Withdrawal)
      (ok : applyWithdrawal s w = .ok t) :
      balanceCredits s t = 0 ∧ balanceDebits s t ≤ w.amount.toNat := by
    unfold applyWithdrawal at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨builder, _, set⟩ := ok
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      simp [balanceCredits, balanceDebits, actualBalanceAt, BeaconState.putBuilder]
    · exact debits_decrease ok
  have fold (ws : List Withdrawal) (s t : BeaconState preset fork)
      (ok : ws.foldlM applyWithdrawal s = .ok t) :
      balanceCredits s t = 0 ∧
        balanceDebits s t ≤ (ws.map fun w => w.amount.toNat).sum ∧
        t.balances.data.size = s.balances.data.size := by
    induction ws generalizing s with
    | nil =>
      cases ok
      simp [balanceCredits, balanceDebits]
    | cons w ws ih =>
      simp only [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨u, first, last⟩ := ok
      have a := one w first
      have b := ih u last
      have sizes := (sameSizes_applyWithdrawal first).2
      have credits := credits_triangle s u t b.2.2
      have debits := debits_triangle s u t sizes.symm
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega, b.2.2.trans sizes⟩
  exact (fold withdrawals.toList s t (by simpa [applyWithdrawals,
    ← Array.foldlM_toList] using ok)).imp_right And.left

theorem excess_queue_debit {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i : ValidatorIndex) (balance : Gwei)
    (read : getBalance s i = .ok balance)
    (ok : queueExcessActiveBalance s electra i = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤
      (balance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  simp only [queueExcessActiveBalance, read, bind_ok_iff, Except.ok.injEq,
    exists_eq_left'] at ok
  split at ok
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨validator, _, pending, _, u, set, rfl⟩ := ok
    have decreased : decreaseBalance s i
        (balance - preset.MIN_ACTIVATION_BALANCE) = .ok u := by
      simp only [decreaseBalance, read, bind, Except.bind]
      have eq : saturatingSub balance (balance - preset.MIN_ACTIVATION_BALANCE) =
          preset.MIN_ACTIVATION_BALANCE := by
        apply UInt64.toNat_inj.mp
        rw [toNat_saturatingSub, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)]
        have := UInt64.lt_iff_toNat_lt.mp above
        omega
      simpa [eq] using set
    have bounds := debits_decrease decreased
    simpa [balanceCredits, balanceDebits, actualBalanceAt,
      UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)] using bounds
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst t
    simp [balanceCredits, balanceDebits]

/-- The crossing queues balance instead of losing it; the debit is counted before later credits. -/
theorem electra_upgrade_debit (s : BeaconState preset .dencun) (t : BeaconState preset .pectra)
    (ok : upgradeToElectra config s = .ok t) :
    (∑ i ∈ Finset.range t.balances.data.size,
      (actualBalanceAt ⟨.pectra, t⟩ i - actualBalanceAt ⟨.dencun, s⟩ i)) = 0 ∧
    (∑ i ∈ Finset.range s.balances.data.size,
      (actualBalanceAt ⟨.dencun, s⟩ i - actualBalanceAt ⟨.pectra, t⟩ i)) ≤
      ((t.pendingDeposits (by decide)).data.toList.map fun d => d.amount.toNat).sum := by
  let queued (s : BeaconState preset .pectra) :=
    ((s.pendingDeposits (by decide)).data.toList.map fun d => d.amount.toNat).sum
  let bound (s t : BeaconState preset .pectra) :=
    t.balances.data.size = s.balances.data.size ∧ balanceCredits s t = 0 ∧
      balanceDebits s t + queued s ≤ queued t
  -- Each upgrade pass pays for its debit by appending the same amount to the queue.
  have excess (s t : BeaconState preset .pectra) (i : ValidatorIndex)
      (ok : queueExcessActiveBalance s (by decide) i = .ok t) : bound s t := by
    have read : ∃ b, getBalance s i = .ok b := by
      have steps := ok
      simp only [queueExcessActiveBalance, bind_ok_iff] at steps
      obtain ⟨b, read, _⟩ := steps
      exact ⟨b, read⟩
    obtain ⟨b, read⟩ := read
    have bounds := excess_queue_debit s t (by decide) i b read ok
    obtain ⟨_, added, queue, amount⟩ := queueExcessActiveBalance_balance read ok
    have sum : queued t = queued s + (added.map fun d => d.amount.toNat).sum := by
      simp only [queued, queue, List.map_append, List.sum_append]
    have minimum : (min b preset.MIN_ACTIVATION_BALANCE).toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat := by
      rw [toNat_min]
      exact Nat.min_le_right _ _
    exact ⟨(sameSizes_queueExcessActiveBalance ok).2, bounds.1, by omega⟩
  have pre (s t : BeaconState preset .pectra) (i : ValidatorIndex)
      (ok : queuePreActivation s (by decide) i = .ok t) : bound s t := by
    simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨v, _, b, read, pending, appended, u, setBalance, w, setValidator, rfl⟩ := ok
    have decreased : decreaseBalance s i b = .ok u := by
      simpa [decreaseBalance, read, bind, Except.bind, saturatingSub] using setBalance
    have bounds := debits_decrease decreased
    have size := (sameSizes_decreaseBalance decreased).2
    obtain ⟨_, rfl⟩ := setValidator_ok setValidator
    have sum : (pending.data.toList.map fun d => d.amount.toNat).sum = queued s + b.toNat := by
      rw [appendWithinLimit_data appended]
      simp [queued]
    refine ⟨size, bounds.1, ?_⟩
    change balanceDebits s u + queued s ≤ _
    change balanceDebits s u + queued s ≤
      (pending.data.toList.map fun d => d.amount.toNat).sum
    omega
  have compound (s t : BeaconState preset .pectra) (i : Nat)
      (ok : queueCompoundingExcess s (by decide) i = .ok t) : bound s t := by
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · exact excess s t _ (liftAccessor_ok.mp ok)
      · cases ok
        simp [bound, balanceCredits, balanceDebits]
    · cases ok
      simp [bound, balanceCredits, balanceDebits]
  have fold {α : Type} (f : BeaconState preset .pectra → α →
      Except TransitionError (BeaconState preset .pectra))
      (step : ∀ s t a, f s a = .ok t → bound s t)
      (xs : List α) (s t : BeaconState preset .pectra)
      (ok : xs.foldlM f s = .ok t) : bound s t := by
    induction xs generalizing s with
    | nil => cases ok; simp [bound, balanceCredits, balanceDebits]
    | cons x xs ih =>
      simp only [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨u, first, last⟩ := ok
      have a := step s u x first
      have b := ih u last
      have credits := credits_triangle s u t b.1
      have debits := debits_triangle s u t a.1.symm
      exact ⟨b.1.trans a.1, by omega, by omega⟩
  simp only [upgradeToElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨activationExit, _, earliestExit, _, exitChurn, _, consolidationChurn, _,
    u, first, last⟩ := ok
  have firstBound := fold _ pre _ _ u first
  have lastBound := fold _ compound _ u t last
  have trans {s u t : BeaconState preset .pectra} (a : bound s u) (b : bound u t) :
      bound s t := by
    have credits := credits_triangle s u t b.1
    have debits := debits_triangle s u t a.1.symm
    exact ⟨b.1.trans a.1, by omega, by omega⟩
  have combined := trans firstBound lastBound
  have before : ¬ Fork.pectra ≤ Fork.dencun := by decide
  simpa [bound, queued, balanceCredits, balanceDebits, actualBalanceAt,
    carryFields, carryList, before] using combined.2

end EthLib.Consensus
