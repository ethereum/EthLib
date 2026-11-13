module

public import EthLib.Consensus.BeaconApi.Rewards
public import EthLib.Consensus.Proofs.BeaconApi.Registries
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
public import EthLib.Consensus.Transition.StateTransition

/-!
# Proofs: the rewards answers of the Beacon API

The attestation rewards name each requested validator once, in order of index.

Each part is the reward minus the penalty of the deltas of its kind.

Before Altair the inclusion part is the attester's own part of the inclusion deltas.

The parts add up to what the epoch transition applies to the balance, with the proposer shares.

When the penalties do not exhaust the balance, the balance moves by exactly that sum.

The answer reads the state that the rewards step of the epoch transition reads.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork} {state : BeaconState preset fork}

/-- A checked run over deltas moves a balance by the rewards minus the penalties.

The balance must cover the penalties of all the deltas, so no step stops at zero. -/
private theorem foldlM_toNat (i : Nat) :
    ∀ (deltas : List (Array Gwei × Array Gwei)) (balance result : Gwei),
      deltas.foldlM (fun balance delta => (Uint64.addChecked balance (delta.1.getD i 0)).map
          fun raised => Uint64.saturatingSub raised (delta.2.getD i 0)) balance =
        Except.ok result →
      (deltas.map fun delta => (delta.2.getD i 0).toNat).sum ≤ balance.toNat →
      (result.toNat : Int) = balance.toNat +
        (deltas.map fun delta => (delta.1.getD i 0).toNat).sum -
          (deltas.map fun delta => (delta.2.getD i 0).toNat).sum
  | [], balance, result, run, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at run
    subst run
    simp
  | delta :: rest, balance, result, run, covered => by
    rw [List.foldlM_cons] at run
    cases added : Uint64.addChecked balance (delta.1.getD i 0) with
    | error e =>
      rw [added] at run
      cases run
    | ok raised =>
      rw [added] at run
      change List.foldlM _ _ rest = _ at run
      obtain ⟨fits, raisedNat⟩ := Uint64.addChecked_ok_iff.mp added
      simp only [List.map_cons, List.sum_cons] at covered ⊢
      have stepNat := Uint64.toNat_saturatingSub raised (delta.2.getD i 0)
      have next := foldlM_toNat i rest (Uint64.saturatingSub raised (delta.2.getD i 0)) result
        run (by omega)
      omega

/-- Summed over some deltas, the net rewards are the rewards minus the penalties. -/
private theorem sum_netDelta (i : Nat) :
    ∀ deltas : List (Array Gwei × Array Gwei),
      (deltas.map fun delta => netDelta delta i).sum =
        ((deltas.map fun delta => (delta.1.getD i 0).toNat).sum : Nat) -
          ((deltas.map fun delta => (delta.2.getD i 0).toNat).sum : Nat)
  | [] => by simp
  | delta :: rest => by
    simp only [List.map_cons, List.sum_cons]
    rw [sum_netDelta i rest]
    simp only [netDelta, Int.natCast_add]
    omega

/-! ## The validators of the answer -/

/-- The answer names the validators that the request selects, once each and in that order. -/
theorem attestationRewards_indices {config : Config} {ids : List ValidatorId}
    {entries : List AttestationRewards}
    (answered : attestationRewards config state ids = .ok entries) :
    entries.map (·.validatorIndex) = selectValidators state ids := by
  unfold attestationRewards at answered
  by_cases altair : .altair ≤ fork
  · simp only [altair, ↓reduceDIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at answered
    obtain ⟨_, _, _, _, rfl⟩ := answered
    simp [Function.comp_def]
  · simp only [altair, ↓reduceDIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at answered
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := answered
    simp [Function.comp_def]

/-- Each validator of the answer is one that the request selects. -/
private theorem mem_selectValidators_of_answered {config : Config} {ids : List ValidatorId}
    {entries : List AttestationRewards}
    (answered : attestationRewards config state ids = .ok entries)
    {entry : AttestationRewards} (member : entry ∈ entries) :
    entry.validatorIndex ∈ selectValidators state ids := by
  rw [← attestationRewards_indices answered]
  exact List.mem_map_of_mem member

/-! ## Each part -/

/-- From Altair, each part of the rewards of a validator is the net delta of its kind.

The source, target and head parts are those of the three flags, in the order of the transition.

The inactivity part is that of the inactivity deltas, and there is no inclusion part. -/
theorem attestationRewards_parts_of_altair {config : Config} (altair : .altair ≤ fork)
    {ids : List ValidatorId} {entries : List AttestationRewards}
    {flags : List (Array Gwei × Array Gwei)} {inactivity : Array Gwei × Array Gwei}
    (answered : attestationRewards config state ids = .ok entries)
    (flagged : (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
      (getFlagIndexDeltas state altair) = .ok flags)
    (penalized : getInactivityPenaltyDeltas config state = .ok inactivity)
    {entry : AttestationRewards} (member : entry ∈ entries) :
    entry.source = netDelta (flags.getD 0 (#[], #[])) entry.validatorIndex.toNat ∧
      entry.target = netDelta (flags.getD 1 (#[], #[])) entry.validatorIndex.toNat ∧
      entry.head = netDelta (flags.getD 2 (#[], #[])) entry.validatorIndex.toNat ∧
      entry.inclusionDelay = none ∧
      entry.inactivity = netDelta inactivity entry.validatorIndex.toNat := by
  simp only [attestationRewards, altair, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at answered
  obtain ⟨inactivity', inactivityOk, flags', flagsOk, rfl⟩ := answered
  obtain rfl := Except.ok.inj (inactivityOk.symm.trans penalized)
  obtain rfl := Except.ok.inj (flagsOk.symm.trans flagged)
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  have noReward := getInactivityPenaltyDeltas_rewards penalized index.toNat
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp [netDelta, noReward]

/-- Before Altair, each part of the rewards of a validator is the net delta of its kind.

The inclusion part is the attester's own inclusion reward. -/
theorem attestationRewards_parts_of_lt_altair {config : Config} (before : fork < .altair)
    {ids : List ValidatorId} {entries : List AttestationRewards}
    {source target head inactivity : Array Gwei × Array Gwei} {inclusion : Array Gwei}
    (answered : attestationRewards config state ids = .ok entries)
    (sourced : getSourceDeltas state before = .ok source)
    (targeted : getTargetDeltas state before = .ok target)
    (headed : getHeadDeltas state before = .ok head)
    (included : attesterInclusionRewards state before = .ok inclusion)
    (penalized : getInactivityPenaltyDeltas config state = .ok inactivity)
    {entry : AttestationRewards} (member : entry ∈ entries) :
    entry.source = netDelta source entry.validatorIndex.toNat ∧
      entry.target = netDelta target entry.validatorIndex.toNat ∧
      entry.head = netDelta head entry.validatorIndex.toNat ∧
      entry.inclusionDelay = some (inclusion.getD entry.validatorIndex.toNat 0) ∧
      entry.inactivity = netDelta inactivity entry.validatorIndex.toNat := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  simp only [attestationRewards, notAltair, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at answered
  obtain ⟨inactivity', inactivityOk, source', sourceOk, target', targetOk, head', headOk,
    inclusion', inclusionOk, rfl⟩ := answered
  obtain rfl := Except.ok.inj (inactivityOk.symm.trans penalized)
  obtain rfl := Except.ok.inj (sourceOk.symm.trans sourced)
  obtain rfl := Except.ok.inj (targetOk.symm.trans targeted)
  obtain rfl := Except.ok.inj (headOk.symm.trans headed)
  obtain rfl := Except.ok.inj (inclusionOk.symm.trans included)
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  have noReward := getInactivityPenaltyDeltas_rewards penalized index.toNat
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp [netDelta, noReward]

/-- The sum of pointwise sums is the sum of the two sums. -/
private theorem sum_map_add_nat {α : Type} (items : List α) (f g : α → Nat) :
    (items.map fun item => f item + g item).sum = (items.map f).sum + (items.map g).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- A fold whose steps each add an amount to the entries adds the sum of those amounts. -/
private theorem foldlM_getD_sum {α : Type} {step : Array Gwei → ValidatorIndex →
      Except TransitionError (Array Gwei)} {key : α → ValidatorIndex} (amount : α → Nat → Nat) :
    ∀ (items : List α) (start result : Array Gwei),
      (∀ item ∈ items, ∀ rewards next, step rewards (key item) = .ok next →
        ∀ j, (next.getD j 0).toNat = (rewards.getD j 0).toNat + amount item j) →
      (items.map key).foldlM step start = .ok result →
      ∀ j, (result.getD j 0).toNat = (start.getD j 0).toNat + (items.map (amount · j)).sum
  | [], start, result, _, computed => by
    simp only [List.map_nil, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | item :: rest, start, result, added, computed => by
    rw [List.map_cons, List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    intro j
    rw [foldlM_getD_sum amount rest middle result
      (fun other member => added other (List.mem_cons_of_mem _ member)) folded j,
      added item List.mem_cons_self start middle stepped j, List.map_cons, List.sum_cons,
      Nat.add_assoc]

/-- Before Altair, the inclusion deltas are the attesters' own parts plus the proposer shares.

Each unslashed signer of the matching source attestations has an earliest inclusion.

The signer earns its base reward less the proposer share, divided by the inclusion delay.

The proposer of that inclusion earns the proposer share of the signer's base reward. -/
theorem attesterInclusionRewards_split (before : fork < .altair)
    {rewards penalties parts : Array Gwei}
    (inclusion : getInclusionDelayDeltas state before = .ok (rewards, penalties))
    (own : attesterInclusionRewards state before = .ok parts) :
    ∃ attestations signers attesters total,
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations ∧
      attestations.toList.mapM (getPendingAttestingIndices state) = .ok signers ∧
      unslashedAmong state signers = .ok attesters ∧
      getTotalActiveBalance state = .ok total ∧
      ∃ shares : List (ValidatorIndex × PendingAttestation preset × Gwei),
        shares.map (·.1) = attesters ∧
        (∀ share ∈ shares, (earliestInclusions state.validators.data.size
            (attestations.zip signers.toArray)).getD share.1.toNat none = some share.2.1 ∧
          getBaseReward state total share.1 = .ok share.2.2 ∧ share.2.1.inclusionDelay ≠ 0) ∧
        ∀ j, (parts.getD j 0).toNat = (shares.map fun share =>
            if share.1.toNat = j then
              (share.2.2.toNat - share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) /
                share.2.1.inclusionDelay.toNat else 0).sum ∧
          (rewards.getD j 0).toNat = (parts.getD j 0).toNat + (shares.map fun share =>
            if share.2.1.proposerIndex.toNat = j then
              share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat else 0).sum := by
  obtain ⟨_, attestations, signers, attesters, total, attestationsOk, signersOk, attestersOk,
    totalOk, shares, named, facts, sums⟩ := getInclusionDelayDeltas_getD before inclusion
  simp only [attesterInclusionRewards, bind_ok_iff, liftAccessor_ok] at own
  obtain ⟨attestations', attestationsOk', signers', signersOk', attesters', attestersOk',
    total', totalOk', folded⟩ := own
  obtain rfl := Except.ok.inj (attestationsOk.symm.trans attestationsOk')
  obtain rfl := Except.ok.inj (signersOk.symm.trans signersOk')
  obtain rfl := Except.ok.inj (attestersOk.symm.trans attestersOk')
  obtain rfl := Except.ok.inj (totalOk.symm.trans totalOk')
  rw [← named] at folded
  have own := foldlM_getD_sum (key := fun share => share.1) (fun share j =>
      if share.1.toNat = j then
        (share.2.2.toNat - share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) /
          share.2.1.inclusionDelay.toNat else 0) shares _ parts
    (fun share member rewards next stepped j => by
      obtain ⟨found, based, nonzero⟩ := facts share member
      simp only [found, based, liftAccessor_ok, bind_ok_iff, Except.ok.injEq,
        exists_eq_left'] at stepped
      obtain ⟨reward, rewardOk, added⟩ := stepped
      obtain ⟨_, rfl⟩ := inclusionAttesterReward_ok_iff.mp rewardOk
      have shareLe : (proposerReward preset share.2.2).toNat ≤ share.2.2.toNat := by
        rw [proposerReward, UInt64.toNat_div]; exact Nat.div_le_self _ _
      rw [addDelta_getD added, UInt64.toNat_div,
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr shareLe), proposerReward,
        UInt64.toNat_div]) folded
  refine ⟨attestations, signers, attesters, total, attestationsOk, signersOk, attestersOk,
    totalOk, shares, named, facts, fun j => ⟨?_, ?_⟩⟩
  · rw [own j, replicate_getD_zero, UInt64.toNat_zero, Nat.zero_add]
  · rw [sums j, own j, replicate_getD_zero, UInt64.toNat_zero, Nat.zero_add, sum_map_add_nat,
      Nat.add_comm]

/-- Before Altair, the inclusion part of a validator is at most its inclusion deltas. -/
theorem attestationRewards_inclusionDelay_le_of_lt_altair {config : Config}
    (before : fork < .altair) {ids : List ValidatorId} {entries : List AttestationRewards}
    {inclusionRewards inclusionPenalties : Array Gwei}
    (answered : attestationRewards config state ids = .ok entries)
    (included : getInclusionDelayDeltas state before = .ok (inclusionRewards, inclusionPenalties))
    {entry : AttestationRewards} (member : entry ∈ entries) :
    (entry.inclusionDelay.getD 0).toNat ≤
      (inclusionRewards.getD entry.validatorIndex.toNat 0).toNat := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  have answered' := answered
  simp only [attestationRewards, notAltair, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at answered'
  obtain ⟨_, inactivityOk, _, sourceOk, _, targetOk, _, headOk, parts, partsOk, _⟩ := answered'
  obtain ⟨-, -, -, inclusionPart, -⟩ :=
    attestationRewards_parts_of_lt_altair before answered sourceOk targetOk headOk partsOk
      inactivityOk member
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, splits⟩ :=
    attesterInclusionRewards_split before included partsOk
  obtain ⟨_, split⟩ := splits entry.validatorIndex.toNat
  rw [inclusionPart, Option.getD_some, split]
  exact Nat.le_add_right _ _

/-! ## Ideal rewards -/

/-- The ideal rewards list distinct effective balances, in increasing order. -/
theorem idealAttestationRewards_sorted {ideal : List IdealAttestationRewards}
    (idealed : idealAttestationRewards state = .ok ideal) :
    (ideal.map (·.effectiveBalance.toNat)).Pairwise (· < ·) := by
  simp only [idealAttestationRewards, idealBalances, bind_ok_iff, pure, Except.pure] at idealed
  obtain ⟨sorted, ⟨eligible, -, firsts, folded, sortedOk⟩, mapped⟩ := idealed
  obtain rfl := Except.ok.inj sortedOk.symm
  have distinct : (firsts.map (·.1)).Nodup :=
    foldlM_ok_invariant (fun found : List (Gwei × ValidatorIndex) => (found.map (·.1)).Nodup)
      (fun found index next nodup stepped => by
        simp only [bind_ok_iff, liftAccessor_ok] at stepped
        obtain ⟨validator, -, stepped⟩ := stepped
        split at stepped
        · exact (Except.ok.inj stepped) ▸ nodup
        · rename_i fresh
          obtain rfl := Except.ok.inj stepped
          simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at fresh
          rw [List.map_append, List.nodup_append]
          refine ⟨nodup, by simp, ?_⟩
          simp only [List.mem_map, List.map_cons, List.map_nil, List.mem_singleton]
          rintro _ ⟨pair, pairMem, rfl⟩ _ rfl same
          exact fresh pair pairMem same)
      (by simp) folded
  have balances := map_of_mapM_ok
    (p := fun rates : IdealAttestationRewards => rates.effectiveBalance)
    (q := fun pair : Gwei × ValidatorIndex => pair.1) (fun pair rates computed => by
      unfold idealRewardsOf at computed
      split at computed
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
        obtain ⟨_, _, _, _, _, _, rfl⟩ := computed
        rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
        rfl) mapped
  have ordered := List.pairwise_mergeSort
    (le := fun a b : Gwei × ValidatorIndex => decide (a.1.toNat ≤ b.1.toNat))
    (fun a b c first second => by
      simp only [decide_eq_true_eq] at first second ⊢
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega)
    firsts
  have unique := ((List.mergeSort_perm firsts fun a b => decide (a.1.toNat ≤ b.1.toNat)).map
    (·.1)).nodup_iff.mpr distinct
  have mapped : ideal.map (fun rates => rates.effectiveBalance.toNat) =
      ((firsts.mergeSort fun a b => decide (a.1.toNat ≤ b.1.toNat)).map (·.1)).map
        UInt64.toNat := by
    rw [← balances, List.map_map]
    rfl
  rw [mapped, List.pairwise_map, List.pairwise_map]
  rw [List.Nodup, List.pairwise_map] at unique
  refine (ordered.and unique).imp fun {a b} both => ?_
  simp only [decide_eq_true_eq] at both
  have : a.1.toNat ≠ b.1.toNat := fun same => both.2 (UInt64.toNat_inj.mp same)
  omega

/-- From Altair, the flag reward of an eligible validator that set the flag. -/
private theorem getFlagIndexDeltas_reward_of_eligible {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    {eligible : List ValidatorIndex} (listed : getEligibleValidatorIndices state = .ok eligible)
    {index : ValidatorIndex} (eligibleMember : index ∈ eligible)
    (inside : index.toNat < state.validators.data.size) :
    ∃ participating participatingBalance total,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
        (getPreviousEpoch state) = .ok participating ∧
      getTotalBalance state participating = .ok participatingBalance ∧
      getTotalActiveBalance state = .ok total ∧
      (index ∈ participating → ∃ base leak, getBaseReward state total index = .ok base ∧
        isInInactivityLeak state = .ok leak ∧
        (rewards.getD index.toNat 0).toNat = if leak then 0 else
          base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
            (participatingBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat /
            ((total / preset.EFFECTIVE_BALANCE_INCREMENT).toNat * WEIGHT_DENOMINATOR.toNat)) := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨participating, flagged, participatingBalance, weighed, total, active, eligible',
    listed', folded⟩ := computed
  obtain rfl := Except.ok.inj (listed.symm.trans listed')
  refine ⟨participating, participatingBalance, total, flagged, weighed, active, fun present => ?_⟩
  have distinct := (getEligibleValidatorIndices_ok listed).1
  have entry := foldlM_entry (entry := fun deltas : Array Gwei × Array Gwei =>
      deltas.1.getD index.toNat 0) (j := index.toNat)
    (fun _ _ _ step other => (Prod.mk.inj (addFlagDelta_getD_of_ne step (Ne.symm other))).1)
    distinct folded
  obtain ⟨last, next, start, stepped, result⟩ := entry.2 index eligibleMember rfl
  have set : (markIndices state.validators.data.size participating).getD index.toNat false =
      true := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    simpa [inside] using ⟨index, present, rfl⟩
  obtain ⟨base, based⟩ := addFlagDelta_base stepped
  obtain ⟨leak, leaking⟩ := addFlagDelta_leak stepped set
  refine ⟨base, leak, based, leaking, ?_⟩
  simp only at start result
  rw [result, addFlagDelta_reward_of_set stepped set based leaking, start, replicate_getD_zero,
    UInt64.toNat_zero, Nat.zero_add]

/-- From Altair, the ideal reward of one flag, at a validator of the registry. -/
private theorem idealFlagReward_eq {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {index : ValidatorIndex} {reward : Gwei}
    (computed : idealFlagReward state altair flagIndex index = .ok reward)
    (inside : index.toNat < state.validators.data.size) :
    ∃ participating participatingBalance total base leak,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
        (getPreviousEpoch state) = .ok participating ∧
      getTotalBalance state participating = .ok participatingBalance ∧
      getTotalActiveBalance state = .ok total ∧
      getBaseReward state total index = .ok base ∧ isInInactivityLeak state = .ok leak ∧
      reward.toNat = if leak then 0 else
          base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
            (participatingBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat /
            ((total / preset.EFFECTIVE_BALANCE_INCREMENT).toNat * WEIGHT_DENOMINATOR.toNat) := by
  simp only [idealFlagReward, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨participating, flagged, participatingBalance, weighed, total, active, ⟨rewards, _⟩,
    stepped, rfl⟩ := computed
  have set : (Array.replicate state.validators.data.size true).getD index.toNat false = true := by
    simp [Array.getD_eq_getD_getElem?, inside]
  obtain ⟨base, based⟩ := addFlagDelta_base stepped
  obtain ⟨leak, leaking⟩ := addFlagDelta_leak stepped set
  refine ⟨participating, participatingBalance, total, base, leak, flagged, weighed, active, based,
    leaking, ?_⟩
  rw [addFlagDelta_reward_of_set stepped set based leaking, replicate_getD_zero,
    UInt64.toNat_zero, Nat.zero_add]

/-- The base reward of a validator depends only on its effective balance. -/
private theorem getBaseReward_congr {total : Gwei} {first second : ValidatorIndex}
    {firstValidator secondValidator : Validator}
    (firstRead : getValidator state first = .ok firstValidator)
    (secondRead : getValidator state second = .ok secondValidator)
    (same : firstValidator.effectiveBalance = secondValidator.effectiveBalance) :
    getBaseReward state total first = getBaseReward state total second := by
  simp only [getBaseReward, firstRead, secondRead, same, bind, Except.bind]

/-- The effective balance of each eligible validator is listed, with a validator that has it. -/
private theorem idealBalances_mem {balances : List (Gwei × ValidatorIndex)}
    (computed : idealBalances state = .ok balances) {eligible : List ValidatorIndex}
    (listed : getEligibleValidatorIndices state = .ok eligible) {index : ValidatorIndex}
    (member : index ∈ eligible) {validator : Validator}
    (read : getValidator state index = .ok validator) :
    ∃ first firstValidator, (validator.effectiveBalance, first) ∈ balances ∧
      getValidator state first = .ok firstValidator ∧
      firstValidator.effectiveBalance = validator.effectiveBalance := by
  simp only [idealBalances, bind_ok_iff, pure, Except.pure] at computed
  obtain ⟨eligible', listed', firsts, folded, sortedOk⟩ := computed
  obtain rfl := Except.ok.inj (listed.symm.trans listed')
  obtain rfl := Except.ok.inj sortedOk.symm
  -- Each listed pair names a validator with that balance.
  have named := foldlM_ok_invariant (fun found : List (Gwei × ValidatorIndex) =>
      ∀ pair ∈ found, ∃ pairValidator, getValidator state pair.2 = .ok pairValidator ∧
        pairValidator.effectiveBalance = pair.1)
    (fun found index next all stepped => by
      simp only [bind_ok_iff, liftAccessor_ok] at stepped
      obtain ⟨current, currentOk, stepped⟩ := stepped
      split at stepped
      · exact (Except.ok.inj stepped) ▸ all
      · obtain rfl := Except.ok.inj stepped
        intro pair inside
        rcases List.mem_append.mp inside with old | new
        · exact all pair old
        · obtain rfl := List.mem_singleton.mp new
          exact ⟨current, currentOk, rfl⟩)
    (by simp) folded
  -- The step of the validator lists its balance, and later steps keep every pair.
  obtain ⟨position, bound, rfl⟩ := List.getElem_of_mem member
  obtain ⟨-, steps⟩ := foldlM_ok_steps
    (fun small large : List (Gwei × ValidatorIndex) => ∀ pair ∈ small, pair ∈ large)
    (fun _ _ inside => inside) (fun first second pair inside => second pair (first pair inside))
    (fun found index next stepped => by
      simp only [bind_ok_iff, liftAccessor_ok] at stepped
      obtain ⟨_, _, stepped⟩ := stepped
      split at stepped
      · exact (Except.ok.inj stepped) ▸ fun _ inside => inside
      · obtain rfl := Except.ok.inj stepped
        exact fun _ inside => List.mem_append_left _ inside) folded
  obtain ⟨middle, next, -, stepped, kept⟩ := steps position bound
  simp only [bind_ok_iff, liftAccessor_ok, read] at stepped
  obtain ⟨_, same, stepped⟩ := stepped
  obtain rfl := Except.ok.inj same
  have listedPair : ∃ first, (validator.effectiveBalance, first) ∈ next := by
    split at stepped
    · rename_i found
      obtain rfl := Except.ok.inj stepped
      obtain ⟨pair, inside, same⟩ := List.any_eq_true.mp found
      rw [beq_iff_eq] at same
      exact ⟨pair.2, same ▸ inside⟩
    · obtain rfl := Except.ok.inj stepped
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩
  obtain ⟨first, inside⟩ := listedPair
  have final := kept _ inside
  obtain ⟨firstValidator, firstRead, same⟩ := named _ final
  exact ⟨first, firstValidator,
    (List.mergeSort_perm _ _).mem_iff.mpr final, firstRead, same⟩

/-- From Altair, an eligible validator that set a flag earns the ideal reward of its balance for it.

The ideal reward may be read at any validator of the registry with the same effective balance. -/
private theorem idealFlagReward_eq_netDelta {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {deltas : Array Gwei × Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok deltas)
    {eligible : List ValidatorIndex} (listed : getEligibleValidatorIndices state = .ok eligible)
    {index first : ValidatorIndex} (eligibleMember : index ∈ eligible)
    {validator firstValidator : Validator} (read : getValidator state index = .ok validator)
    (firstRead : getValidator state first = .ok firstValidator)
    (same : firstValidator.effectiveBalance = validator.effectiveBalance)
    (present : ∀ participating, getUnslashedParticipatingIndices state altair
      flagIndex.val.toUInt64 (getPreviousEpoch state) = .ok participating →
        index ∈ participating)
    {reward : Gwei} (idealed : idealFlagReward state altair flagIndex first = .ok reward) :
    (reward.toNat : Int) = netDelta deltas index.toNat := by
  obtain ⟨rewards, penalties⟩ := deltas
  have inside := (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp read)).1
  have firstInside := (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp firstRead)).1
  obtain ⟨participating, participatingBalance, total, flagged, weighed, active, earned⟩ :=
    getFlagIndexDeltas_reward_of_eligible computed listed eligibleMember inside
  have member := present participating flagged
  obtain ⟨base, leak, based, leaking, rewardSum⟩ := earned member
  obtain ⟨participating', participatingBalance', total', base', leak', flagged', weighed',
    active', based', leaking', idealSum⟩ := idealFlagReward_eq idealed firstInside
  obtain rfl := Except.ok.inj (flagged.symm.trans flagged')
  obtain rfl := Except.ok.inj (weighed.symm.trans weighed')
  obtain rfl := Except.ok.inj (active.symm.trans active')
  obtain rfl := Except.ok.inj (leaking.symm.trans leaking')
  rw [getBaseReward_congr firstRead read same, based, Except.ok.injEq] at based'
  subst based'
  have penalty := getFlagIndexDeltas_present computed flagged member inside
  simp only [netDelta, penalty, UInt64.toNat_zero, Int.natCast_zero, Int.sub_zero]
  rw [idealSum, rewardSum]

/-- From Altair, a validator that set every flag earns the ideal rewards of its effective balance.

It must be eligible, and the participating validators of each flag must include it. -/
theorem attestationRewards_ideal_of_altair {config : Config} (altair : .altair ≤ fork)
    {ids : List ValidatorId} {entries : List AttestationRewards}
    {ideal : List IdealAttestationRewards} {eligible : List ValidatorIndex}
    (answered : attestationRewards config state ids = .ok entries)
    (idealed : idealAttestationRewards state = .ok ideal)
    {entry : AttestationRewards} (member : entry ∈ entries)
    (listed : getEligibleValidatorIndices state = .ok eligible)
    (eligibleMember : entry.validatorIndex ∈ eligible)
    (full : ∀ (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) participating,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
          (getPreviousEpoch state) = .ok participating →
        entry.validatorIndex ∈ participating) :
    ∃ rates ∈ ideal, (state.validators.data[entry.validatorIndex.toNat]?.map
        (·.effectiveBalance)) = some rates.effectiveBalance ∧
      rates.head = entry.head ∧ rates.target = entry.target ∧ rates.source = entry.source ∧
      rates.inactivity = entry.inactivity := by
  have answered' := answered
  simp only [attestationRewards, altair, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at answered'
  obtain ⟨inactivity, penalized, flags, flagged, -⟩ := answered'
  obtain ⟨sourced, targeted, headed, -, inactive⟩ :=
    attestationRewards_parts_of_altair altair answered flagged penalized member
  obtain ⟨validator, found, -⟩ := (mem_getEligibleValidatorIndices_iff listed).mp eligibleMember
  have read := getValidator_eq_ok_iff.mpr found
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  simp only [idealAttestationRewards, bind_ok_iff] at idealed
  obtain ⟨balances, balanced, mapped⟩ := idealed
  obtain ⟨first, firstValidator, pairMember, firstRead, same⟩ :=
    idealBalances_mem balanced listed eligibleMember read
  obtain ⟨rates, ratesMember, ratesOk⟩ := exists_mem_of_mapM_ok mapped pairMember
  simp only [idealRewardsOf, altair, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ratesOk
  obtain ⟨_, ⟨headReward, headOk, rfl⟩, _, ⟨targetReward, targetOk, rfl⟩, _,
    ⟨sourceReward, sourceOk, rfl⟩, rfl⟩ := ratesOk
  -- The deltas of each flag are the entry of the list at its position.
  have flagAt (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
      getFlagIndexDeltas state altair flagIndex = .ok (flags.getD flagIndex.val (#[], #[])) := by
    have length := mapM_ok_length flagged
    have bound : flagIndex.val < flags.length := by
      rw [length, List.length_finRange]; exact flagIndex.isLt
    have := mapM_ok_getElem flagged flagIndex.val
      (by rw [List.length_finRange]; exact flagIndex.isLt)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]
    simpa using this
  have part (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) {reward : Gwei}
      (idealed : idealFlagReward state altair flagIndex first = .ok reward) :=
    idealFlagReward_eq_netDelta (flagAt flagIndex) listed eligibleMember read firstRead same
      (full flagIndex) idealed
  -- A validator with a timely target pays no inactivity penalty.
  obtain ⟨matching, -, -, timely, -⟩ := getFlagIndexDeltas_reward_of_eligible
    (flagAt ⟨1, by decide⟩) listed eligibleMember inside
  obtain ⟨rewards, penalties⟩ := inactivity
  have noPenalty := getInactivityPenaltyDeltas_target altair penalized timely
    (full ⟨1, by decide⟩ matching timely) inside
  have noReward := getInactivityPenaltyDeltas_rewards penalized entry.validatorIndex.toNat
  refine ⟨_, ratesMember, by rw [found, Option.map_some], ?_, ?_, ?_, ?_⟩
  · rw [part _ headOk, headed]; rfl
  · rw [part _ targetOk, targeted]; rfl
  · rw [part _ sourceOk, sourced]; rfl
  · rw [inactive]
    simp [netDelta, noPenalty, noReward]

/-! ## Sums -/

/-- Before Altair, four parts of a validator and its inclusion deltas add up to its net deltas.

The four parts are those of the head, target, source and inactivity.

The sum is its reward minus its penalty in the deltas that the epoch transition applies.

The inclusion deltas hold its own inclusion part and its proposer shares, as the split shows. -/
theorem attestationRewards_sum_of_lt_altair {config : Config} (before : fork < .altair)
    {ids : List ValidatorId} {entries : List AttestationRewards}
    {rewards penalties inclusionRewards inclusionPenalties : Array Gwei}
    (answered : attestationRewards config state ids = .ok entries)
    (deltas : getAttestationDeltas config state before = .ok (rewards, penalties))
    (included : getInclusionDelayDeltas state before = .ok (inclusionRewards, inclusionPenalties))
    {entry : AttestationRewards} (member : entry ∈ entries) :
    entry.head + entry.target + entry.source + entry.inactivity +
        ((inclusionRewards.getD entry.validatorIndex.toNat 0).toNat : Int) =
      netDelta (rewards, penalties) entry.validatorIndex.toNat := by
  have indexMem := mem_selectValidators_of_answered answered member
  obtain ⟨source, target, head, inclusion, inactivity, sourceOk, targetOk, headOk,
    inclusionOk, inactivityOk, sums⟩ := getAttestationDeltas_getD before deltas
  obtain rfl := Except.ok.inj (inclusionOk.symm.trans included)
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  have answered' := answered
  simp only [attestationRewards, notAltair, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at answered'
  obtain ⟨_, _, _, _, _, _, _, _, parts, partsOk, _⟩ := answered'
  obtain ⟨sourced, targeted, headed, -, inactive⟩ :=
    attestationRewards_parts_of_lt_altair before answered sourceOk targetOk headOk partsOk
      inactivityOk member
  obtain ⟨rewardSum, penaltySum⟩ :=
    sums _ (lt_of_mem_selectValidators indexMem)
  have noReward := getInactivityPenaltyDeltas_rewards inactivityOk entry.validatorIndex.toNat
  rw [sourced, targeted, headed, inactive]
  simp only [netDelta, noReward, UInt64.toNat_zero] at rewardSum penaltySum ⊢
  omega

/-- From Altair, the parts of the rewards of a validator add up to its deltas for the epoch.

They are those of each flag, then of inactivity, as the epoch transition applies them in turn. -/
theorem attestationRewards_sum_of_altair {config : Config} (altair : .altair ≤ fork)
    {ids : List ValidatorId} {entries : List AttestationRewards}
    {flags : List (Array Gwei × Array Gwei)} {inactivity : Array Gwei × Array Gwei}
    (answered : attestationRewards config state ids = .ok entries)
    (flagged : (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
      (getFlagIndexDeltas state altair) = .ok flags)
    (penalized : getInactivityPenaltyDeltas config state = .ok inactivity)
    {entry : AttestationRewards} (member : entry ∈ entries) :
    entry.head + entry.target + entry.source + entry.inactivity =
      ((flags ++ [inactivity]).map fun deltas =>
        netDelta deltas entry.validatorIndex.toNat).sum := by
  have length : flags.length = 3 := by
    rw [mapM_ok_length flagged]
    simp [PARTICIPATION_FLAG_WEIGHTS]
  obtain ⟨sourced, targeted, headed, _, inactive⟩ :=
    attestationRewards_parts_of_altair altair answered flagged penalized member
  obtain ⟨source, target, head, rfl⟩ : ∃ source target head, flags = [source, target, head] := by
    match flags, length with
    | [source, target, head], _ => exact ⟨source, target, head, rfl⟩
  rw [sourced, targeted, headed, inactive]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ]
  omega

/-! ## Balances -/

/-- Before Altair, the rewards and penalties step moves a balance by its parts and inclusion deltas.

The inclusion deltas take the place of the inclusion part, since they also hold the proposer shares.

This holds when the step succeeds after the first epoch.

The balance plus the reward must cover the penalty. -/
theorem attestationRewards_balance_of_lt_altair {config : Config} (before : fork < .altair)
    (later : getCurrentEpoch state ≠ GENESIS_EPOCH) {after : BeaconState preset fork}
    (applied : processRewardsAndPenalties config state = .ok after)
    {ids : List ValidatorId} {entries : List AttestationRewards}
    (answered : attestationRewards config state ids = .ok entries)
    {inclusionRewards inclusionPenalties : Array Gwei}
    (included : getInclusionDelayDeltas state before = .ok (inclusionRewards, inclusionPenalties))
    {entry : AttestationRewards} (member : entry ∈ entries) {balance : Gwei}
    (held : state.balances.data[entry.validatorIndex.toNat]? = some balance)
    (covered : ∀ rewards penalties,
      getAttestationDeltas config state before = .ok (rewards, penalties) →
        (penalties.getD entry.validatorIndex.toNat 0).toNat ≤
          balance.toNat + (rewards.getD entry.validatorIndex.toNat 0).toNat) :
    ∃ raised, after.balances.data[entry.validatorIndex.toNat]? = some raised ∧
      (raised.toNat : Int) = balance.toNat + entry.head + entry.target + entry.source +
        entry.inactivity + ((inclusionRewards.getD entry.validatorIndex.toNat 0).toNat : Int) := by
  obtain ⟨rewards, penalties, deltas, steps⟩ :=
    processRewardsAndPenalties_balances_of_lt_altair before later applied
  have indexMem := mem_selectValidators_of_answered answered member
  have total := attestationRewards_sum_of_lt_altair before answered deltas included member
  obtain ⟨balance', held', noWrap, stepped⟩ :=
    (steps entry.validatorIndex.toNat).1 (lt_of_mem_selectValidators indexMem)
  obtain rfl := Option.some.inj (held.symm.trans held')
  refine ⟨_, stepped, ?_⟩
  have cover := covered rewards penalties deltas
  have added : (balance + rewards.getD entry.validatorIndex.toNat 0).toNat =
      balance.toNat + (rewards.getD entry.validatorIndex.toNat 0).toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using noWrap)
  rw [Uint64.toNat_saturatingSub, added]
  simp only [netDelta] at total
  omega

/-- From Altair, the rewards and penalties step moves a balance by the parts of its rewards.

This holds when the step succeeds after the first epoch.

The penalties of the epoch must not exceed the balance, so that no step stops at zero. -/
theorem attestationRewards_balance_of_altair {config : Config} (altair : .altair ≤ fork)
    (later : getCurrentEpoch state ≠ GENESIS_EPOCH) {after : BeaconState preset fork}
    (applied : processRewardsAndPenalties config state = .ok after)
    {ids : List ValidatorId} {entries : List AttestationRewards}
    (answered : attestationRewards config state ids = .ok entries)
    {entry : AttestationRewards} (member : entry ∈ entries) {balance : Gwei}
    (held : state.balances.data[entry.validatorIndex.toNat]? = some balance)
    (covered : ∀ flags inactivity,
      (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
          (getFlagIndexDeltas state altair) = .ok flags →
        getInactivityPenaltyDeltas config state = .ok inactivity →
        ((flags ++ [inactivity]).map fun deltas =>
          (deltas.2.getD entry.validatorIndex.toNat 0).toNat).sum ≤ balance.toNat) :
    ∃ raised, after.balances.data[entry.validatorIndex.toNat]? = some raised ∧
      (raised.toNat : Int) = balance.toNat + entry.head + entry.target + entry.source +
        entry.inactivity := by
  obtain ⟨flags, inactivity, flagged, penalized, steps⟩ :=
    processRewardsAndPenalties_balances_of_altair altair later applied
  have indexMem := mem_selectValidators_of_answered answered member
  have total := attestationRewards_sum_of_altair altair answered flagged penalized member
  obtain ⟨stepped, run, _⟩ := steps entry.validatorIndex.toNat
  have inside := lt_of_mem_selectValidators indexMem
  have raised := foldlM_toNat entry.validatorIndex.toNat _ balance _ (run inside balance held)
    (covered flags inactivity flagged penalized)
  rw [stepped inside, held, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  have sum := sum_netDelta entry.validatorIndex.toNat (flags ++ [inactivity])
  omega

/-! ## The state and the response -/

/-- Adding an amount to some deltas succeeds only for an index inside them. -/
private theorem lt_size_of_addDelta {deltas result : Array Gwei} {index : ValidatorIndex}
    {amount : Gwei} (computed : addDelta deltas index amount = .ok result) :
    index.toNat < deltas.size := by
  unfold addDelta at computed
  split at computed
  · assumption
  · cases computed

/-- A fold succeeds from entries below those of a fold that succeeds, when each step does so. -/
private theorem foldlM_exists_ok_of_le
    {step other : Array Gwei → ValidatorIndex → Except TransitionError (Array Gwei)}
    (stepped : ∀ low high index next, low.size = high.size →
      (∀ j, (low.getD j 0).toNat ≤ (high.getD j 0).toNat) → other high index = .ok next →
      ∃ lower, step low index = .ok lower ∧ lower.size = next.size ∧
        ∀ j, (lower.getD j 0).toNat ≤ (next.getD j 0).toNat) :
    ∀ (indices : List ValidatorIndex) (low high result : Array Gwei), low.size = high.size →
      (∀ j, (low.getD j 0).toNat ≤ (high.getD j 0).toNat) →
      indices.foldlM other high = .ok result → ∃ lower, indices.foldlM step low = .ok lower
  | [], low, _, _, _, _, _ => ⟨low, rfl⟩
  | index :: rest, low, high, result, sized, below, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, otherOk, folded⟩ := computed
    obtain ⟨lower, stepOk, lowerSized, lowerBelow⟩ := stepped low high index middle sized below
      otherOk
    obtain ⟨final, finalOk⟩ :=
      foldlM_exists_ok_of_le stepped rest lower middle result lowerSized lowerBelow folded
    exact ⟨final, by rw [List.foldlM_cons, stepOk]; exact finalOk⟩

/-- Before Altair, the attesters' own inclusion parts succeed when the inclusion deltas do. -/
private theorem attesterInclusionRewards_exists_ok (before : fork < .altair)
    {deltas : Array Gwei × Array Gwei}
    (inclusion : getInclusionDelayDeltas state before = .ok deltas) :
    ∃ parts, attesterInclusionRewards state before = .ok parts := by
  simp only [getInclusionDelayDeltas, bind_ok_iff, liftAccessor_ok] at inclusion
  obtain ⟨attestations, attestationsOk, signers, signersOk, attesters, attestersOk, total,
    totalOk, rewards, folded, -⟩ := inclusion
  simp only [attesterInclusionRewards, attestationsOk, signersOk, attestersOk, totalOk,
    liftAccessor, Except.mapError, bind, Except.bind]
  refine foldlM_exists_ok_of_le ?_ attesters _ _ rewards rfl (fun _ => le_refl _) folded
  intro low high index next sized below computed
  unfold addInclusionReward at computed
  split at computed
  · rename_i attestation found
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨base, baseOk, raised, raisedOk, reward, rewardOk, added⟩ := computed
    have inside : index.toNat < low.size := by
      rw [sized, ← addDelta_size raisedOk]; exact lt_size_of_addDelta added
    have fits := (next.getD index.toNat 0).toNat_lt
    rw [addDelta_getD added, addDelta_getD raisedOk] at fits
    obtain ⟨lower, lowerOk⟩ := addDelta_exists_ok (amount := reward) inside (by
      have := below index.toNat
      simp only [↓reduceIte] at fits
      omega)
    refine ⟨lower, ?_, ?_, fun j => ?_⟩
    · simp only [found, baseOk, rewardOk, lowerOk]
    · rw [addDelta_size lowerOk, addDelta_size added, addDelta_size raisedOk, sized]
    · rw [addDelta_getD lowerOk, addDelta_getD added, addDelta_getD raisedOk]
      have := below j
      split <;> split <;> omega
  · cases computed

/-- Whenever the rewards step succeeds after the first epoch, so does the answer. -/
theorem attestationRewards_ok {config : Config} (later : getCurrentEpoch state ≠ GENESIS_EPOCH)
    {after : BeaconState preset fork}
    (applied : processRewardsAndPenalties config state = .ok after) (ids : List ValidatorId) :
    ∃ entries, attestationRewards config state ids = .ok entries := by
  by_cases altair : .altair ≤ fork
  · obtain ⟨flags, inactivity, flagged, penalized, _⟩ :=
      processRewardsAndPenalties_balances_of_altair altair later applied
    exact ⟨_, by simp only [attestationRewards, altair, ↓reduceDIte, penalized, flagged, bind,
      Except.bind, pure, Except.pure]; rfl⟩
  · have before := Nat.lt_of_not_le altair
    obtain ⟨rewards, penalties, deltas, _⟩ :=
      processRewardsAndPenalties_balances_of_lt_altair before later applied
    obtain ⟨source, target, head, inclusion, inactivity, sourceOk, targetOk, headOk,
      inclusionOk, inactivityOk, _⟩ := getAttestationDeltas_getD before deltas
    obtain ⟨parts, partsOk⟩ := attesterInclusionRewards_exists_ok before inclusionOk
    exact ⟨_, by simp only [attestationRewards, altair, ↓reduceDIte, inactivityOk, sourceOk,
      targetOk, headOk, partsOk, bind, Except.bind, pure, Except.pure]; rfl⟩

/-- The epoch transition runs its rewards step on the state that the answer reads.

This holds when the epoch transition succeeds. -/
theorem processEpoch_stateBeforeRewards {config : Config} {checks : SignatureChecks}
    {after : BeaconState preset fork} (applied : processEpoch config checks state = .ok after) :
    ∃ rewarded middle, stateBeforeRewards config state = .ok rewarded ∧
      processRewardsAndPenalties config rewarded = .ok middle := by
  unfold processEpoch at applied
  by_cases altair : .altair ≤ fork
  · simp only [altair, ↓reduceDIte, processEpochAltair, bind_ok_iff] at applied
    obtain ⟨justified, justifiedOk, inactive, inactiveOk, middle, middleOk, -⟩ := applied
    refine ⟨inactive, middle, ?_, middleOk⟩
    simp only [stateBeforeRewards, altair, ↓reduceDIte, justifiedOk, inactiveOk, bind,
      Except.bind]
  · simp only [altair, ↓reduceDIte, bind_ok_iff] at applied
    obtain ⟨justified, justifiedOk, middle, middleOk, -⟩ := applied
    refine ⟨justified, middle, ?_, middleOk⟩
    simp only [stateBeforeRewards, altair, ↓reduceDIte, justifiedOk, bind, Except.bind, pure,
      Except.pure]

/-- An answer comes from a state at the last slot of an epoch past the first, for the epoch before.

Its total rewards and its ideal rewards are read from the state that the rewards step reads. -/
theorem attestationRewardsResponse_ok {config : Config} {epoch : Epoch}
    {ids : List ValidatorId} {envelope : ApiEnvelope}
    (answered : attestationRewardsResponse config state epoch ids = .ok envelope) :
    getCurrentEpoch state ≠ GENESIS_EPOCH ∧ getPreviousEpoch state = epoch ∧
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
      ∃ rewarded ideal entries, stateBeforeRewards config state = .ok rewarded ∧
        idealAttestationRewards rewarded = .ok ideal ∧
        attestationRewards config rewarded ids = .ok entries ∧
        envelope = { data := .mkObj [("ideal_rewards", .arr (ideal.map (·.toJson)).toArray),
          ("total_rewards", .arr (entries.map (·.toJson)).toArray)] } := by
  unfold attestationRewardsResponse at answered
  by_cases unknown : getCurrentEpoch state = GENESIS_EPOCH ∨ getPreviousEpoch state ≠ epoch ∨
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0
  · simp only [unknown, ↓reduceIte, bind_ok_iff] at answered
    obtain ⟨_, thrown, _⟩ := answered
    cases thrown
  · simp only [unknown, ↓reduceIte, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at answered
    obtain ⟨rewarded, rewardedOk, ideal, idealOk, entries, entriesOk, rfl⟩ := answered
    simp only [not_or, not_not] at unknown
    exact ⟨unknown.1, unknown.2.1, unknown.2.2, rewarded, ideal, entries, rewardedOk, idealOk,
      entriesOk, rfl⟩

end EthLib.Consensus.BeaconApi
