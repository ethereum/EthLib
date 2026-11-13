module

public import EthLib.Consensus.BeaconApi.Rewards
public import EthLib.Consensus.Proofs.BeaconApi.Registries
public import EthLib.Consensus.Proofs.Transition.BlockRewards
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.ProposerBalance
public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
public import EthLib.Consensus.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# Proofs: the rewards answers of the Beacon API

The attestation rewards name each requested validator once, in order of index.

Each part is the reward minus the penalty of the deltas of its kind.

Before Altair the inclusion part is the attester's own part of the inclusion deltas.

The parts add up to what the epoch transition applies to the balance, with the proposer shares.

When the penalties do not exhaust the balance, the balance moves by exactly that sum.

The answer reads the state that the rewards step of the epoch transition reads.

The sync committee rewards name each requested member once, in order of index.

Each is the sum, over the seats of the member, of the participant reward of the transition.

That reward counts for a seat that signed, and against a seat that did not.

When the balance covers each seat of the member, it moves by that sum.

The proposer also earns a share of the reward of each seat that signed.

The block rewards start from the state that the operations of the block read.

Their total is the sum of their parts, and from Altair the sync part is the share of the step.

The operations and the sync aggregate raise the proposer's balance by exactly that total.

That needs a block that does not slash the proposer, pay it a deposit or switch its credentials.

It also needs a proposer without a seat in the sync committee.
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

/-! ## Sync committee rewards -/

/-- The sync aggregate steps move one balance by the net rewards of the seats it holds.

The balance must cover the participant reward once per seat that the member holds.

Then no penalty stops at zero.

The proposer share is paid once per signed seat, and only when the proposer is the member. -/
private theorem foldl_seats_balance (reward : Gwei) (proposerReward : Nat)
    (chosen index : ValidatorIndex) (seats : List (ValidatorIndex × Bool)) (balance : Nat)
    (covered : (seats.filter (·.1 == index)).length * reward.toNat ≤ balance) :
    ((seats.foldl (fun balance member =>
      if member.2 then balance + (if member.1.toNat = index.toNat then reward.toNat else 0) +
        (if chosen.toNat = index.toNat then proposerReward else 0)
      else if member.1.toNat = index.toNat then balance - reward.toNat else balance)
        balance : Nat) : Int) = balance + seatsReward reward seats index +
      (if chosen = index then (seats.filter (·.2)).length * proposerReward else 0 : Nat) := by
  have chosenIff : chosen.toNat = index.toNat ↔ chosen = index := UInt64.toNat_inj
  induction seats generalizing balance with
  | nil => simp [seatsReward]
  | cons seat rest ih =>
    obtain ⟨member, signed⟩ := seat
    have step : seatsReward reward ((member, signed) :: rest) index =
        (if member = index then seatReward reward signed else 0) +
          seatsReward reward rest index := by
      unfold seatsReward
      by_cases same : member = index <;> simp [same]
    have lenStep : (((member, signed) :: rest).filter (·.1 == index)).length =
        (rest.filter (·.1 == index)).length + if member = index then 1 else 0 := by
      by_cases same : member = index <;> simp [same]
    have signStep : (((member, signed) :: rest).filter (·.2)).length =
        (rest.filter (·.2)).length + if signed then 1 else 0 := by
      cases signed <;> simp
    have sameIff : member.toNat = index.toNat ↔ member = index := UInt64.toNat_inj
    rw [lenStep] at covered
    rw [List.foldl_cons, step, ih _ ?_]
    · by_cases same : member = index <;> by_cases ch : chosen = index <;> cases signed <;>
        simp [same, ch, chosenIff, sameIff, seatReward, Nat.add_mul] at covered ⊢ <;> omega
    · by_cases same : member = index <;> cases signed <;>
        simp [same, sameIff, Nat.add_mul] at covered ⊢ <;> (try split_ifs) <;> omega

/-- The answer names the members that the request selects, once each and in increasing order.

The members are the validators that hold the seats of the sync committee. -/
theorem syncCommitteeRewards_indices {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    {ids : List ValidatorId} {entries : List SyncCommitteeReward}
    (answered : syncCommitteeRewards state altair aggregate ids = .ok entries) :
    ∃ seats, syncRewardSeats state altair aggregate = .ok seats ∧
      (entries.map (·.validatorIndex)).Pairwise (· < ·) ∧
      ∀ index, index ∈ entries.map (·.validatorIndex) ↔
        index ∈ seats.map (·.1) ∧ (ids ≠ [] → index ∈ selectValidators state ids) := by
  unfold syncCommitteeRewards at answered
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at answered
  obtain ⟨seats, seatsOk, reward, rewardOk, rfl⟩ := answered
  refine ⟨seats, seatsOk, ?_, ?_⟩
  · simp only [List.map_map, Function.comp_def, List.map_id']
    split
    · exact sortedSet_sorted _
    · exact (sortedSet_sorted _).filter _
  · intro index
    simp only [List.map_map, Function.comp_def, List.map_id']
    split <;> rename_i h
    · simp [List.isEmpty_iff] at h
      simp [h, mem_sortedSet]
    · simp [List.isEmpty_iff] at h
      simp [h, mem_sortedSet, List.mem_filter, and_comm]

/-- The reward of a member is the sum of its seats, at the participant reward of the transition.

A seat that signed counts that reward, and a seat that did not counts minus it. -/
theorem syncCommitteeRewards_reward {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    {ids : List ValidatorId} {entries : List SyncCommitteeReward}
    (answered : syncCommitteeRewards state altair aggregate ids = .ok entries)
    {entry : SyncCommitteeReward} (member : entry ∈ entries) :
    ∃ seats reward, syncRewardSeats state altair aggregate = .ok seats ∧
      syncParticipantReward state = .ok reward ∧
      entry.reward = seatsReward reward seats entry.validatorIndex := by
  unfold syncCommitteeRewards at answered
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at answered
  obtain ⟨seats, seatsOk, reward, rewardOk, rfl⟩ := answered
  refine ⟨seats, reward, seatsOk, rewardOk, ?_⟩
  split at member <;> simp only [List.mem_map] at member <;>
    obtain ⟨index, _, rfl⟩ := member <;> rfl

/-- A member of the answer has the reward of its seats, at the participant reward of the step. -/
private theorem entry_reward_eq {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    {ids : List ValidatorId} {entries : List SyncCommitteeReward}
    {seats : List (ValidatorIndex × Bool)} {reward : Gwei}
    (answered : syncCommitteeRewards state altair aggregate ids = .ok entries)
    {entry : SyncCommitteeReward} (member : entry ∈ entries)
    (seated : syncRewardSeats state altair aggregate = .ok seats)
    (rewarded : syncParticipantReward state = .ok reward) :
    entry.reward = seatsReward reward seats entry.validatorIndex := by
  obtain ⟨seats', reward', seatsOk, rewardOk, entryReward⟩ :=
    syncCommitteeRewards_reward answered member
  rw [seated, Except.ok.injEq] at seatsOk
  rw [rewarded, Except.ok.injEq] at rewardOk
  subst seatsOk rewardOk
  exact entryReward

/-- The sync aggregate step moves the balance of a member by its seats and its proposer shares.

The proposer shares count once per signed seat, when the proposer is the member.

The balance must cover the participant reward once per seat that the member holds. -/
private theorem syncAggregate_member_balance {config : Config} {checks : SignatureChecks}
    {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    {seats : List (ValidatorIndex × Bool)} {reward balance : Gwei} {index : ValidatorIndex}
    (applied : processSyncAggregate config checks state altair aggregate = .ok after)
    (seated : syncRewardSeats state altair aggregate = .ok seats)
    (rewarded : syncParticipantReward state = .ok reward)
    (found : state.balances.data[index.toNat]? = some balance)
    (covered : (seats.filter (·.1 == index)).length * reward.toNat ≤ balance.toNat) :
    ∃ final chosen, after.balances.data[index.toNat]? = some final ∧
      ((∃ seat ∈ seats, seat.2 = true) → getBeaconProposerIndex state = .ok chosen) ∧
      (final.toNat : Int) = balance.toNat + seatsReward reward seats index +
        (if chosen = index then (seats.filter (·.2)).length *
          (reward.toNat * PROPOSER_WEIGHT.toNat /
            (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) else 0 : Nat) := by
  obtain ⟨computed, proposerReward, members, chosen, computedOk, shareEq, membersOk, chosenOk,
    folded⟩ := processSyncAggregate_balance applied
  rw [rewarded, Except.ok.injEq] at computedOk
  subst computedOk
  unfold syncRewardSeats at seated
  simp only [bind_ok_iff, membersOk, pure, Except.pure, Except.ok.injEq] at seated
  obtain ⟨members', membersOk', seatsEq⟩ := seated
  have sameSeats : (members.zip aggregate.syncCommitteeBits.bits.toArray).toList = seats := by
    rw [← seatsEq, ← membersOk']
  rw [sameSeats] at chosenOk folded
  obtain ⟨final, finalOk, finalValue⟩ := folded _ _ found
  refine ⟨final, chosen, finalOk, chosenOk, ?_⟩
  rw [finalValue, shareEq]
  exact foldl_seats_balance _ _ chosen index seats _ covered

/-- The sync aggregate step moves the balance of a member by exactly its reward in the answer.

The member must not be the proposer of the slot, which also earns a share for each signature.

Its balance must cover the participant reward once per seat that it holds.

Then no penalty stops at zero. -/
theorem syncCommitteeRewards_balance {config : Config} {checks : SignatureChecks}
    {altair : .altair ≤ fork} {aggregate : SyncAggregate preset} {ids : List ValidatorId}
    {entries : List SyncCommitteeReward} {seats : List (ValidatorIndex × Bool)}
    {reward balance : Gwei}
    (applied : processSyncAggregate config checks state altair aggregate = .ok after)
    (answered : syncCommitteeRewards state altair aggregate ids = .ok entries)
    {entry : SyncCommitteeReward} (member : entry ∈ entries)
    (notProposer : getBeaconProposerIndex state ≠ .ok entry.validatorIndex)
    (seated : syncRewardSeats state altair aggregate = .ok seats)
    (rewarded : syncParticipantReward state = .ok reward)
    (found : state.balances.data[entry.validatorIndex.toNat]? = some balance)
    (covered : (seats.filter (·.1 == entry.validatorIndex)).length * reward.toNat ≤
      balance.toNat) :
    ∃ final, after.balances.data[entry.validatorIndex.toNat]? = some final ∧
      (final.toNat : Int) = balance.toNat + entry.reward := by
  obtain ⟨final, chosen, finalOk, chosenOk, finalValue⟩ :=
    syncAggregate_member_balance applied seated rewarded found covered
  refine ⟨final, finalOk, ?_⟩
  rw [finalValue, entry_reward_eq answered member seated rewarded]
  have none : ¬(∃ seat ∈ seats, seat.2 = true) → (seats.filter (·.2)).length = 0 := by
    intro absent
    simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro seat mem
    simpa using fun flag => absent ⟨seat, mem, flag⟩
  by_cases signed : ∃ seat ∈ seats, seat.2 = true
  · have differs : chosen ≠ entry.validatorIndex := fun same =>
      notProposer (by rw [chosenOk signed, same])
    simp [differs]
  · simp [none signed]

/-- The proposer of the slot, when it holds seats, moves by its reward and a share per signature.

That share is the participant reward times the proposer weight, over the denominator less it.

It rounds down, and the proposer earns it for every seat that signed, its own or not.

Its balance must cover the participant reward once per seat that it holds. -/
theorem syncCommitteeRewards_balance_of_proposer {config : Config} {checks : SignatureChecks}
    {altair : .altair ≤ fork} {aggregate : SyncAggregate preset} {ids : List ValidatorId}
    {entries : List SyncCommitteeReward} {seats : List (ValidatorIndex × Bool)}
    {reward balance : Gwei}
    (applied : processSyncAggregate config checks state altair aggregate = .ok after)
    (answered : syncCommitteeRewards state altair aggregate ids = .ok entries)
    {entry : SyncCommitteeReward} (member : entry ∈ entries)
    (proposer : getBeaconProposerIndex state = .ok entry.validatorIndex)
    (seated : syncRewardSeats state altair aggregate = .ok seats)
    (rewarded : syncParticipantReward state = .ok reward)
    (found : state.balances.data[entry.validatorIndex.toNat]? = some balance)
    (covered : (seats.filter (·.1 == entry.validatorIndex)).length * reward.toNat ≤
      balance.toNat) :
    ∃ final, after.balances.data[entry.validatorIndex.toNat]? = some final ∧
      (final.toNat : Int) = balance.toNat + entry.reward +
        ((seats.filter (·.2)).length * (reward.toNat * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) : Nat) := by
  obtain ⟨final, chosen, finalOk, chosenOk, finalValue⟩ :=
    syncAggregate_member_balance applied seated rewarded found covered
  refine ⟨final, finalOk, ?_⟩
  rw [finalValue, entry_reward_eq answered member seated rewarded]
  by_cases signed : ∃ seat ∈ seats, seat.2 = true
  · have same : chosen = entry.validatorIndex := by
      have := (chosenOk signed).symm.trans proposer
      exact Except.ok.inj this
    simp [same, Int.add_assoc]
  · have none : (seats.filter (·.2)).length = 0 := by
      simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro seat mem
      simpa using fun flag => signed ⟨seat, mem, flag⟩
    simp [none]

/-- An answer comes only from Altair, and lists the sync committee rewards of the request. -/
theorem syncCommitteeRewardsResponse_ok {aggregate : SyncAggregate preset}
    {ids : List ValidatorId} {envelope : ApiEnvelope}
    (answered : syncCommitteeRewardsResponse state aggregate ids = .ok envelope) :
    ∃ (altair : .altair ≤ fork) (entries : List SyncCommitteeReward),
      syncCommitteeRewards state altair aggregate ids = .ok entries ∧
        envelope = { data := .arr (entries.map (·.toJson)).toArray } := by
  unfold syncCommitteeRewardsResponse at answered
  by_cases altair : .altair ≤ fork
  · simp only [altair, ↓reduceDIte, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at answered
    obtain ⟨entries, entriesOk, rfl⟩ := answered
    exact ⟨altair, entries, entriesOk, rfl⟩
  · simp [altair] at answered

/-- Before Altair a block has no sync aggregate, and the answer is the error with code 400. -/
theorem syncCommitteeRewardsResponse_of_lt_altair (before : fork < .altair)
    (aggregate : SyncAggregate preset) (ids : List ValidatorId) :
    syncCommitteeRewardsResponse state aggregate ids = .error invalidSyncRewardsRequest := by
  have not : ¬.altair ≤ fork := Nat.not_le_of_lt before
  simp [syncCommitteeRewardsResponse, not]
  rfl

/-! ## Block rewards -/

/-- The state that the operations of a block read, as the steps before them give it. -/
theorem stateBeforeOperations_ok_iff {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {input : BeaconState preset fork} :
    stateBeforeOperations config checks engine state block = .ok input ↔
      OperationsInput config checks engine state block input := by
  simp only [stateBeforeOperations, OperationsInput, bind_ok_iff]
  constructor
  · rintro ⟨parented, paid, headed, header, executed, execution, revealed, randao, eth1⟩
    exact ⟨parented, headed, executed, revealed, paid, header, execution, randao, eth1⟩
  · rintro ⟨parented, headed, executed, revealed, paid, header, execution, randao, eth1⟩
    exact ⟨parented, paid, headed, header, executed, execution, revealed, randao, eth1⟩

/-- A block runs its operations on the state that the block rewards start from. -/
theorem processBlock_stateBeforeOperations {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {after : BeaconState preset fork}
    (applied : processBlock config checks engine state block = .ok after) :
    ∃ start operated, stateBeforeOperations config checks engine state block = .ok start ∧
      processOperations config checks start block.body state.latestBlockHeader.slot =
        .ok operated ∧
      (if altair : .altair ≤ fork then
          processSyncAggregate config checks operated altair (block.body.syncAggregate altair)
        else pure operated) = .ok after := by
  obtain ⟨start, operated, started, operatedOk, -, synced⟩ :=
    processBlock_operationsInput applied
  exact ⟨start, operated, stateBeforeOperations_ok_iff.mpr started, operatedOk, synced⟩

/-- The steps that the block rewards run, named, with the parts they give. -/
private theorem blockRewards_ok {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {rewards : BlockRewards}
    (answered : blockRewards config checks engine state block = .ok rewards) :
    ∃ start slashed caught attested sync total,
      stateBeforeOperations config checks engine state block = .ok start ∧
      block.body.proposerSlashings.data.foldlM (processProposerSlashing config checks) start =
        .ok slashed ∧
      block.body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) slashed =
        .ok caught ∧
      block.body.attestations.data.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) caught =
        .ok attested ∧
      (if altair : .altair ≤ fork then do
          let operated ← processOperations config checks start block.body
            state.latestBlockHeader.slot
          let share ← syncProposerReward (← syncParticipantReward operated)
          let signed := (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray.countP id
          liftAccessor (liftArith (Uint64.mulChecked share signed.toUInt64))
        else pure (0 : Gwei)) = .ok sync ∧
      (∃ first second,
        Uint64.addChecked (balanceRise block.proposerIndex caught attested) sync = .ok first ∧
        Uint64.addChecked first (balanceRise block.proposerIndex start slashed) = .ok second ∧
        Uint64.addChecked second (balanceRise block.proposerIndex slashed caught) = .ok total) ∧
      rewards = ⟨block.proposerIndex, total, balanceRise block.proposerIndex caught attested, sync,
        balanceRise block.proposerIndex start slashed,
        balanceRise block.proposerIndex slashed caught⟩ := by
  simp only [blockRewards, bind_ok_iff] at answered
  obtain ⟨start, startOk, slashed, slashedOk, caught, caughtOk, attested, attestedOk, rest⟩ :=
    answered
  refine ⟨start, slashed, caught, attested, ?_⟩
  by_cases altair : Fork.altair ≤ fork
  · simp only [altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq] at rest ⊢
    obtain ⟨operated, operatedOk, reward, rewardOk, share, shareOk, sync, syncOk, total,
      ⟨first, firstOk, second, secondOk, totalOk⟩, rfl⟩ := rest
    exact ⟨sync, total, startOk, slashedOk, caughtOk, attestedOk,
      ⟨operated, operatedOk, reward, rewardOk, share, shareOk, syncOk⟩,
      ⟨first, second, firstOk, secondOk, totalOk⟩, rfl⟩
  · simp only [altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq] at rest ⊢
    obtain ⟨_, rfl, total, ⟨first, firstOk, second, secondOk, totalOk⟩, rfl⟩ := rest
    exact ⟨0, total, startOk, slashedOk, caughtOk, attestedOk, rfl,
      ⟨first, second, firstOk, secondOk, totalOk⟩, rfl⟩

/-- The block rewards name the proposer of the block, and their total is the sum of the parts. -/
theorem blockRewards_total {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {rewards : BlockRewards}
    (answered : blockRewards config checks engine state block = .ok rewards) :
    rewards.proposerIndex = block.proposerIndex ∧
      rewards.total.toNat = rewards.attestations.toNat + rewards.syncAggregate.toNat +
        rewards.proposerSlashings.toNat + rewards.attesterSlashings.toNat := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, ⟨first, second, firstOk, secondOk, totalOk⟩, rfl⟩ :=
    blockRewards_ok answered
  rw [Uint64.addChecked_ok_iff] at firstOk secondOk totalOk
  refine ⟨rfl, ?_⟩
  dsimp only
  omega

/-- From Altair the sync part is the share of the sync aggregate step, once per signature.

The step reads the state after the operations, and computes the share from its reward. -/
theorem blockRewards_syncAggregate {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {rewards : BlockRewards} (altair : .altair ≤ fork)
    (answered : blockRewards config checks engine state block = .ok rewards) :
    ∃ start operated reward share,
      stateBeforeOperations config checks engine state block = .ok start ∧
      processOperations config checks start block.body state.latestBlockHeader.slot =
        .ok operated ∧
      syncParticipantReward operated = .ok reward ∧ syncProposerReward reward = .ok share ∧
      rewards.syncAggregate.toNat = share.toNat *
        (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray.countP id := by
  obtain ⟨start, _, _, _, sync, _, startOk, -, -, -, syncOk, -, rfl⟩ := blockRewards_ok answered
  simp only [altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at syncOk
  obtain ⟨operated, operatedOk, reward, rewardOk, share, shareOk, syncOk⟩ := syncOk
  rw [Uint64.mulChecked_ok_iff] at syncOk
  refine ⟨start, operated, reward, share, startOk, operatedOk, rewardOk, shareOk, ?_⟩
  -- The count of signatures is at most the committee size, which fits in 64 bits.
  have small := Array.countP_le_size (p := id)
    (xs := (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray)
  have fits := preset.SYNC_COMMITTEE_SIZE.toNat_lt
  rw [Vector.size_toArray] at small
  rw [syncOk.2]
  simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt small fits)]

/-- Before Altair a block has no sync aggregate, and its attestations pay the proposer nothing. -/
theorem blockRewards_of_lt_altair {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {rewards : BlockRewards} (before : fork < .altair)
    (answered : blockRewards config checks engine state block = .ok rewards) :
    rewards.syncAggregate = 0 ∧ rewards.attestations = 0 := by
  have not : ¬.altair ≤ fork := Nat.not_le_of_lt before
  obtain ⟨_, _, caught, attested, sync, _, -, -, -, attestedOk, syncOk, -, rfl⟩ :=
    blockRewards_ok answered
  simp only [not, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at syncOk
  refine ⟨syncOk.symm, ?_⟩
  -- Before Altair an attestation only records itself, so no balance moves.
  have same : attested.balances = caught.balances := by
    rw [← Array.foldlM_toList] at attestedOk
    refine (foldlM_ok_steps (fun u v : BeaconState preset fork => v.balances = u.balances)
      (fun _ => rfl) (fun one two => two.trans one) (fun u attestation v ok => ?_)
      attestedOk).1
    unfold processAttestation at ok
    simp only [not, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
    have kept := recordPendingAttestation_ok recorded
    split at kept <;>
    · obtain ⟨_, rest⟩ := kept
      exact congrArg (·.balances) rest
  simp [balanceRise, same, Uint64.saturatingSub]

/-- The rise of a balance that does not fall is the difference of the two balances. -/
private theorem balanceRise_toNat {index : ValidatorIndex} {first second : BeaconState preset fork}
    {earlier later : Gwei} (atFirst : first.balances.data[index.toNat]? = some earlier)
    (atSecond : second.balances.data[index.toNat]? = some later) (low : earlier ≤ later) :
    (balanceRise index first second).toNat = later.toNat - earlier.toNat := by
  simp only [balanceRise, Array.getD_eq_getD_getElem?, atFirst, atSecond, Option.getD_some,
    Uint64.saturatingSub]
  rw [UInt64.le_iff_toNat_le] at low
  split
  · rename_i less
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt less)]
  · rename_i notLess
    rw [UInt64.lt_iff_toNat_lt] at notLess
    simp only [UInt64.toNat_zero]
    omega

/-- The share of the proposer is the participant reward times its weight, over the rest. -/
private theorem syncProposerReward_toNat {reward share : Gwei}
    (computed : syncProposerReward reward = .ok share) :
    share.toNat =
      reward.toNat * PROPOSER_WEIGHT.toNat /
        (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) := by
  simp only [syncProposerReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨scaled, scaledOk, computed⟩ := computed
  rw [Uint64.mulChecked_ok_iff] at scaledOk
  rw [Uint64.divChecked_ok_iff] at computed
  rw [computed.2, scaledOk.2]
  rfl

/-- The operations and the sync aggregate of a block raise the proposer's balance by the total.

The proposer must have a balance.

The block must not slash the proposer.

Before Electra, no deposit of the block may carry its key.

From Electra to Fulu, no consolidation request of the block may come from its key.

From Altair, its key must hold no seat in the sync committee.

The mixes must span more than the seed lookahead plus two epochs, as on mainnet and minimal. -/
theorem blockRewards_balance {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {rewards : BlockRewards} {after : BeaconState preset fork} {validator : Validator}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (applied : processBlock config checks engine state block = .ok after)
    (answered : blockRewards config checks engine state block = .ok rewards)
    (found : state.validators.data[block.proposerIndex.toNat]? = some validator)
    (held : block.proposerIndex.toNat < state.balances.data.size)
    (unslashedByProposers : ∀ slashing ∈ block.body.proposerSlashings.data,
      slashing.signedHeader1.message.proposerIndex ≠ block.proposerIndex)
    (unslashedByAttesters : ∀ slashing ∈ block.body.attesterSlashings.data,
      block.proposerIndex ∉ slashingIndices slashing)
    (undeposited : ∀ before : fork < .pectra,
      ∀ deposit ∈ (block.body.deposits (Nat.lt_trans before (by decide))).data,
        deposit.data.pubkey ≠ validator.pubkey)
    (unswitched : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
      ∀ request ∈ (block.body.executionRequests electra).consolidations.data,
        request.sourcePubkey ≠ validator.pubkey)
    (unseated : ∀ altair : .altair ≤ fork,
      validator.pubkey ∉ (state.currentSyncCommittee altair).value.pubkeys.toList) :
    ∃ start balance final, stateBeforeOperations config checks engine state block = .ok start ∧
      start.balances.data[block.proposerIndex.toNat]? = some balance ∧
      after.balances.data[block.proposerIndex.toNat]? = some final ∧
      final.toNat = balance.toNat + rewards.total.toNat := by
  obtain ⟨start, operated, startOk, operatedOk, synced⟩ :=
    processBlock_stateBeforeOperations applied
  obtain ⟨start', slashed, caught, attested, sync, total, startOk', slashedOk, caughtOk,
    attestedOk, -, ⟨first, second, firstOk, secondOk, totalOk⟩, rfl⟩ := blockRewards_ok answered
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  -- The operations start from a state with the proposer of the block and its balance.
  have started := stateBeforeOperations_ok_iff.mp startOk
  obtain ⟨readStart, committeeStart, downStart⟩ := operationsInput_proposer apart started
  obtain ⟨now, atNow, sameKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix (frame_operationsInput started).pubkeysPrefix found
  obtain ⟨balance, atBalance, -⟩ := downStart _ _ (Array.getElem?_eq_getElem held)
  -- The slashings and the attestations raise it, and the later operations keep it.
  obtain ⟨slashed', caught', attested', slashedOk', caughtOk', attestedOk', proposers, attesters,
    attestations, stays⟩ := processOperations_balance operatedOk atNow
      (fun slashing member same =>
        unslashedByProposers slashing member (UInt64.toNat_inj.mp same))
      (fun slashing member slashedIndex inside same =>
        unslashedByAttesters slashing member (UInt64.toNat_inj.mp same ▸ inside))
      (by rw [sameKey]; exact undeposited) (by rw [sameKey]; exact unswitched)
  rw [slashedOk, Except.ok.injEq] at slashedOk'
  subst slashedOk'
  rw [caughtOk, Except.ok.injEq] at caughtOk'
  subst caughtOk'
  rw [attestedOk, Except.ok.injEq] at attestedOk'
  subst attestedOk'
  obtain ⟨one, atOne, lowOne⟩ := proposers balance atBalance
  obtain ⟨two, atTwo, lowTwo⟩ := attesters one atOne
  obtain ⟨three, atThree, lowThree⟩ := attestations two atTwo
  have atOperated := stays three atThree
  have riseOne := balanceRise_toNat atBalance atOne lowOne
  have riseTwo := balanceRise_toNat atOne atTwo lowTwo
  have riseThree := balanceRise_toNat atTwo atThree lowThree
  rw [UInt64.le_iff_toNat_le] at lowOne lowTwo lowThree
  rw [Uint64.addChecked_ok_iff] at firstOk secondOk totalOk
  refine ⟨start, balance, ?_⟩
  by_cases altair : Fork.altair ≤ fork
  · simp only [altair, ↓reduceDIte] at synced
    -- The sync aggregate reads the proposer of the block, which holds no seat.
    obtain ⟨proposerSame, committeeSame⟩ := processOperations_proposer apart operatedOk
    obtain ⟨later, atLater, laterKey⟩ := validators_getElem?_of_validatorKeys_prefix
      (frame_processOperations operatedOk).pubkeysPrefix atNow
    obtain ⟨reward, proposerReward, final, rewardOk, proposerRewardValue, atFinal, finalValue⟩ :=
      processSyncAggregate_proposer synced (proposerSame.trans readStart) atLater
        (by rw [committeeSame, committeeStart, laterKey, sameKey]; exact unseated altair)
        atOperated
    obtain ⟨start', operated', reward', share, startOk', operatedOk', rewardOk', shareOk,
      syncValue⟩ := blockRewards_syncAggregate altair answered
    rw [startOk, Except.ok.injEq] at startOk'
    subst startOk'
    rw [operatedOk, Except.ok.injEq] at operatedOk'
    subst operatedOk'
    rw [rewardOk, Except.ok.injEq] at rewardOk'
    subst rewardOk'
    have shareValue := syncProposerReward_toNat shareOk
    refine ⟨final, startOk, atBalance, atFinal, ?_⟩
    dsimp only at syncValue riseOne riseTwo riseThree ⊢
    rw [finalValue, totalOk.2, secondOk.2, firstOk.2, syncValue, shareValue,
      ← proposerRewardValue, riseOne, riseTwo, riseThree]
    omega
  · simp only [altair, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at synced
    subst synced
    have none := (blockRewards_of_lt_altair (Nat.lt_of_not_le altair) answered).1
    refine ⟨three, startOk, atBalance, atOperated, ?_⟩
    dsimp only at none riseOne riseTwo riseThree ⊢
    rw [totalOk.2, secondOk.2, firstOk.2, none, riseOne, riseTwo, riseThree]
    simp only [UInt64.toNat_zero]
    omega

/-- An answer is the JSON of the block rewards. -/
theorem blockRewardsResponse_ok {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {envelope : ApiEnvelope}
    (answered : blockRewardsResponse config checks engine state block = .ok envelope) :
    ∃ rewards, blockRewards config checks engine state block = .ok rewards ∧
      envelope = { data := rewards.toJson } := by
  simp only [blockRewardsResponse, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
    Except.ok.injEq] at answered
  obtain ⟨rewards, rewardsOk, rfl⟩ := answered
  exact ⟨rewards, rewardsOk, rfl⟩

end EthLib.Consensus.BeaconApi
