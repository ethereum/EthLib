module

public import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Base.Proofs.FilterM
import EthLib.Consensus.Proofs.Transition.Committees

/-!
# Proofs: the supply grows by at most the issuance over one epoch, before Altair

Before Altair the rewards of an epoch pay for the votes of the previous epoch.

Assume the signers of the source hold no more balance than is active now.

A matching signer then earns at most one base reward for each of its source, target and head.

In a leak such a vote earns exactly one base reward, with no assumption.

Its inclusion pays at most one more base reward, shared between it and the proposer.

The inactivity penalties pay no rewards.

So each signer brings at most four base rewards.

Together they are at most its effective balance times the factor, over the root of the total.

The target and head votes are among the source votes.

So the rise is at most the base reward factor times two more than the root of the total.

The other steps keep or lower the balances.

There are no pending deposits before Electra, so the sum of the balances is the supply.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- A bound on what the rewards of one epoch add to the supply, before Altair.

It is the base reward factor times two more than the root of the total active balance. -/
def Preset.epochIssuanceBeforeAltair (preset : Preset) (total : Nat) : Nat :=
  preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt total + 2)

/-- The bound on the issuance before Altair grows with the active balance. -/
theorem Preset.epochIssuanceBeforeAltair_mono {total total' : Nat} (le : total ≤ total') :
    preset.epochIssuanceBeforeAltair total ≤ preset.epochIssuanceBeforeAltair total' := by
  unfold Preset.epochIssuanceBeforeAltair
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sqrt_le_sqrt le) 2)

/-- The bound from Altair is at most the bound before Altair. -/
theorem Preset.epochIssuance_le_epochIssuanceBeforeAltair (total : Nat) :
    preset.epochIssuance total ≤ preset.epochIssuanceBeforeAltair total := by
  unfold Preset.epochIssuance Preset.epochIssuanceBeforeAltair
  omega

/-- On mainnet, at an active balance of `2^57` Gwei, the bound before Altair is below `2^35` Gwei.

That is about 24.3 ETH of rewards. -/
theorem Preset.epochIssuanceBeforeAltair_mainnet :
    Preset.mainnet.epochIssuanceBeforeAltair (2 ^ 57) < 2 ^ 35 := by
  have root : Nat.sqrt (2 ^ 57) = 379625062 := (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  simp only [Preset.epochIssuanceBeforeAltair, root]
  decide

/-- Before Altair, four base rewards are at most the effective balance times the factor.

That product is divided by the root of the total. -/
private theorem four_mul_getBaseReward_le (before : fork < .altair) {total base : Gwei}
    {index : ValidatorIndex} (computed : getBaseReward state total index = .ok base) :
    4 * base.toNat ≤ ((state.validators.data[index.toNat]?).map
      (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat /
        Nat.sqrt total.toNat := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  unfold getBaseReward getValidator at computed
  split at computed
  · rename_i validator found
    simp only [notAltair, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨_, ⟨⟩, reward, rewardOk, based⟩ := computed
    simp only [liftArith, mapError_ok_iff, bind_ok_iff, mulChecked_ok_iff,
      divChecked_ok_iff] at rewardOk
    obtain ⟨product, ⟨-, productValue⟩, -, rewardValue⟩ := rewardOk
    simp only [pure, Except.pure, Except.ok.injEq] at based
    subst based
    rw [found, Option.map_some, Option.getD_some, UInt64.toNat_div, rewardValue, productValue,
      ← toNat_integerSquareroot]
    exact Nat.mul_div_le _ _
  · cases computed

/-- Before Altair, take the rewards of one kind of vote.

Its signers must hold no more balance than is active.

Four times the reward of a validator is at most its weight if it signed, and zero otherwise.

The weight is its effective balance times the factor, over the root of the active balance. -/
private theorem four_mul_componentReward_le (before : fork < .altair)
    (within : state.RegistryWithinLimit)
    {attestations : Array (PendingAttestation preset)} {rewards penalties : Array Gwei}
    (computed : getAttestationComponentDeltas state attestations = .ok (rewards, penalties))
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {attesters : List ValidatorIndex} {attestingBalance : Gwei}
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters)
    (weighed : getTotalBalance state attesters = .ok attestingBalance)
    (kept : attestingBalance ≤ total) {j : Nat} (inside : j < state.validators.data.size) :
    4 * (rewards.getD j 0).toNat ≤
      if j.toUInt64 ∈ attesters then ((state.validators.data[j]?).map
        (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat /
          Nat.sqrt total.toNat else 0 := by
  obtain ⟨total', attesters', attestingBalance', active', listed', weighed', entries⟩ :=
    getAttestationComponentDeltas_getD within computed
  obtain rfl : total = total' := Except.ok.inj (active.symm.trans active')
  obtain rfl : attesters = attesters' := Except.ok.inj (listed.symm.trans listed')
  obtain rfl : attestingBalance = attestingBalance' :=
    Except.ok.inj (weighed.symm.trans weighed')
  obtain ⟨eligible, -, notEligible, isEligible⟩ := entries j inside
  cases eligible
  · rw [(notEligible rfl).1]
    simp
  · obtain ⟨base, based, present, absent⟩ := isEligible rfl
    have four := four_mul_getBaseReward_le before based
    rw [toNat_toUInt64_of_lt within inside] at four
    by_cases member : j.toUInt64 ∈ attesters
    · obtain ⟨leak, -, value, -⟩ := present member
      rw [ite_eq_left member, value]
      refine Nat.le_trans (Nat.mul_le_mul_left 4 ?_) four
      split
      · exact Nat.le_refl _
      · rcases Nat.eq_zero_or_pos (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) with
          zero | positive
        · rw [zero, Nat.div_zero]
          exact Nat.zero_le _
        · refine Nat.div_le_of_le_mul ?_
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp kept))
    · rw [(absent member).1, ite_eq_right member]
      simp

/-- The total balance of some validators is at most that of validators that include them. -/
private theorem getTotalBalance_le_of_subset {few many : List ValidatorIndex}
    (sub : ∀ index ∈ few, index ∈ many) {small large : Gwei}
    (smallOk : getTotalBalance state few = .ok small)
    (largeOk : getTotalBalance state many = .ok large) : small ≤ large := by
  obtain ⟨-, smallFits, rfl⟩ := getTotalBalance_ok_iff.mp smallOk
  obtain ⟨-, largeFits, rfl⟩ := getTotalBalance_ok_iff.mp largeOk
  have marked : sumMarked state.validators.data (markIndices state.validators.data.size few) ≤
      sumMarked state.validators.data (markIndices state.validators.data.size many) := by
    rw [sumMarked_eq_sum, sumMarked_eq_sum]
    refine sum_map_le_sum_map fun j _ => ?_
    simp only [getElem?_markIndices]
    split
    · by_cases listed : few.any (·.toNat == j) = true
      · have also : many.any (·.toNat == j) = true := by
          rw [List.any_eq_true] at listed ⊢
          obtain ⟨index, member, named⟩ := listed
          exact ⟨index, sub index member, named⟩
        simp [listed, also]
      · simp [listed]
    · simp
  rw [UInt64.le_iff_toNat_le, toNat_max, toNat_max, Nat.toUInt64_eq, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt smallFits,
    Nat.mod_eq_of_lt largeFits]
  exact max_le_max (le_refl _) marked

/-- The unslashed signers of some attestations are among those of attestations that include them. -/
private theorem mem_getUnslashedAttestingIndices_of_subset
    {fewer more : Array (PendingAttestation preset)}
    (sub : ∀ attestation ∈ fewer, attestation ∈ more)
    {few many : List ValidatorIndex}
    (fewOk : getUnslashedAttestingIndices state fewer = .ok few)
    (manyOk : getUnslashedAttestingIndices state more = .ok many) :
    ∀ index ∈ few, index ∈ many := by
  intro index member
  unfold getUnslashedAttestingIndices at fewOk manyOk
  rw [bind_ok_iff] at fewOk manyOk
  obtain ⟨fewSigners, fewSignersOk, fewAmong⟩ := fewOk
  obtain ⟨manySigners, manySignersOk, manyAmong⟩ := manyOk
  unfold unslashedAmong at fewAmong manyAmong
  have inSet := mem_of_filterM_ok fewAmong member
  refine mem_filterM_ok_of_test manyAmong ?_ (passes_of_mem_filterM_ok fewAmong member)
  rw [mem_sortedSet] at inSet ⊢
  obtain ⟨signers, listed, signed⟩ := List.mem_flatten.mp inSet
  obtain ⟨attestation, held, signersOk⟩ := mapM_ok_mem fewSignersOk signers listed
  obtain ⟨signers', listed', signersOk'⟩ := exists_mem_of_mapM_ok manySignersOk
    (Array.mem_toList_iff.mpr (sub attestation (Array.mem_toList_iff.mp held)))
  obtain rfl : signers = signers' := Except.ok.inj (signersOk.symm.trans signersOk')
  exact List.mem_flatten.mpr ⟨signers, listed', signed⟩

/-- Before Altair, the votes that match the target are among those that match the source. -/
private theorem mem_of_getMatchingTargetAttestations (before : fork < .altair) {epoch : Epoch}
    {source target : Array (PendingAttestation preset)}
    (sourceOk : getMatchingSourceAttestations state before epoch = .ok source)
    (targetOk : getMatchingTargetAttestations state before epoch = .ok target) :
    ∀ attestation ∈ target, attestation ∈ source := by
  unfold getMatchingTargetAttestations at targetOk
  rw [sourceOk, bind_ok_iff] at targetOk
  obtain ⟨_, ⟨⟩, targetOk⟩ := targetOk
  split at targetOk
  · simp only [pure, Except.pure, Except.ok.injEq] at targetOk
    subst targetOk
    simp
  · rw [bind_ok_iff] at targetOk
    obtain ⟨root, -, targetOk⟩ := targetOk
    simp only [pure, Except.pure, Except.ok.injEq] at targetOk
    subst targetOk
    exact fun attestation member => (Array.mem_filter.mp member).1

/-- Before Altair, the votes that match the head are among those that match the target. -/
private theorem mem_of_getMatchingHeadAttestations (before : fork < .altair) {epoch : Epoch}
    {target head : Array (PendingAttestation preset)}
    (targetOk : getMatchingTargetAttestations state before epoch = .ok target)
    (headOk : getMatchingHeadAttestations state before epoch = .ok head) :
    ∀ attestation ∈ head, attestation ∈ target := by
  unfold getMatchingHeadAttestations at headOk
  rw [targetOk, bind_ok_iff] at headOk
  obtain ⟨_, ⟨⟩, headOk⟩ := headOk
  rw [← Array.toArray_toList (xs := target), List.filterM_toArray] at headOk
  generalize outOk : List.filterM (m := Except TransitionError) _ target.toList = out at headOk
  cases out with
  | error => cases headOk
  | ok out =>
    simp only [Functor.map, Except.map, Except.ok.injEq] at headOk
    subst headOk
    exact fun attestation member =>
      Array.mem_toList_iff.mp (mem_of_filterM_ok outOk (by simpa using member))

/-- An amount at one position, summed over the first positions, counts at most once. -/
private theorem sum_range_ite_le (n position amount : Nat) :
    ((List.range n).map fun j => if position = j then amount else 0).sum ≤ amount := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases same : position = n
    · subst same
      have zero : ((List.range position).map fun j =>
          if position = j then amount else 0).sum = 0 := by
        refine List.sum_eq_zero fun term member => ?_
        obtain ⟨j, below, rfl⟩ := List.mem_map.mp member
        simp [Nat.ne_of_gt (List.mem_range.mp below)]
      simp [zero]
    · simpa [same] using ih

/-- The inclusion shares, summed over the first positions, are at most their base rewards.

The proposer part and the attester part of a share together are at most its base reward. -/
private theorem sum_range_shares_le (n : Nat) :
    ∀ shares : List (ValidatorIndex × PendingAttestation preset × Gwei),
      ((List.range n).map fun j => (shares.map fun share =>
        (if share.2.1.proposerIndex.toNat = j then
          share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat else 0) +
        if share.1.toNat = j then
          (share.2.2.toNat - share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) /
            share.2.1.inclusionDelay.toNat else 0).sum).sum ≤
        (shares.map fun share => share.2.2.toNat).sum
  | [] => by simp
  | share :: rest => by
    have later := sum_range_shares_le n rest
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_add, List.sum_map_add]
    have first := sum_range_ite_le n share.2.1.proposerIndex.toNat
      (share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat)
    have second := sum_range_ite_le n share.1.toNat
      ((share.2.2.toNat - share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) /
        share.2.1.inclusionDelay.toNat)
    have rest := Nat.div_le_self
      (share.2.2.toNat - share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat)
      share.2.1.inclusionDelay.toNat
    have part := Nat.div_le_self share.2.2.toNat preset.PROPOSER_REWARD_QUOTIENT.toNat
    omega

/-- Before Altair, four times the inclusion rewards are at most the weights of the source signers.

The weight of a signer is its effective balance times the factor, over the root of the total. -/
private theorem four_mul_inclusionRewards_le (before : fork < .altair)
    {rewards penalties : Array Gwei}
    (computed : getInclusionDelayDeltas state before = .ok (rewards, penalties))
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {attestations : Array (PendingAttestation preset)} {attesters : List ValidatorIndex}
    (matching :
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations)
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters) (n : Nat) :
    4 * ((List.range n).map fun j => (rewards.getD j 0).toNat).sum ≤
      (attesters.map fun index => ((state.validators.data[index.toNat]?).map
        (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat /
          Nat.sqrt total.toNat).sum := by
  obtain ⟨-, attestations', signers, attesters', total', matching', signersOk, among, active',
    shares, named, facts, entries⟩ := getInclusionDelayDeltas_getD before computed
  obtain rfl : attestations = attestations' := Except.ok.inj (matching.symm.trans matching')
  obtain rfl : total = total' := Except.ok.inj (active.symm.trans active')
  have listed' : getUnslashedAttestingIndices state attestations = .ok attesters' := by
    unfold getUnslashedAttestingIndices
    rw [signersOk]
    exact among
  obtain rfl : attesters = attesters' := Except.ok.inj (listed.symm.trans listed')
  have summed := sum_range_shares_le (preset := preset) n shares
  rw [← funext entries] at summed
  subst named
  rw [List.map_map]
  refine Nat.le_trans (Nat.mul_le_mul_left 4 summed) ?_
  rw [← sum_map_mul_left]
  exact sum_map_le_sum_map fun share member =>
    four_mul_getBaseReward_le before (facts share member).2.1

/-- The weights of the listed validators, summed over the registry, are at most their total.

The weight is the effective balance times the factor, over some root. -/
private theorem sum_range_weights_le (within : state.RegistryWithinLimit)
    {attesters : List ValidatorIndex} {attestingBalance : Gwei}
    (weighed : getTotalBalance state attesters = .ok attestingBalance) (root : Nat) :
    ((List.range state.validators.data.size).map fun j =>
      if j.toUInt64 ∈ attesters then ((state.validators.data[j]?).map
        (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat / root
      else 0).sum ≤ attestingBalance.toNat * preset.BASE_REWARD_FACTOR.toNat / root := by
  obtain ⟨-, small, balance⟩ := getTotalBalance_ok_iff.mp weighed
  have covers : sumMarked state.validators.data
      (markIndices state.validators.data.size attesters) ≤ attestingBalance.toNat := by
    rw [balance, toNat_max, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
    exact Nat.le_max_right _ _
  rw [sumMarked_eq_sum] at covers
  refine Nat.le_trans (sum_map_le_sum_map (g := fun j =>
    (if ((markIndices state.validators.data.size attesters)[j]?).getD false then
      ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0 else 0) *
        preset.BASE_REWARD_FACTOR.toNat / root) fun j member => ?_) ?_
  · have marked := markIndices_getD_iff within (List.mem_range.mp member) attesters
    rw [Array.getD_eq_getD_getElem?] at marked
    by_cases listed : j.toUInt64 ∈ attesters
    · simp [listed, marked.mpr listed]
    · simp [listed]
  · refine Nat.le_trans (sum_map_div_le _ _ _) (Nat.div_le_div_right ?_)
    rw [sum_map_mul_right]
    exact Nat.mul_le_mul_right _ covers

/-- The weights of the unslashed signers sum to their weights read over the registry. -/
private theorem sum_weights_eq (within : state.RegistryWithinLimit)
    {attestations : Array (PendingAttestation preset)} {attesters : List ValidatorIndex}
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters)
    {attestingBalance : Gwei}
    (weighed : getTotalBalance state attesters = .ok attestingBalance) (root : Nat) :
    (attesters.map fun index => ((state.validators.data[index.toNat]?).map
        (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat / root).sum =
      ((List.range state.validators.data.size).map fun j =>
        if j.toUInt64 ∈ attesters then ((state.validators.data[j]?).map
          (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat / root
        else 0).sum := by
  obtain ⟨inside, -, -⟩ := getTotalBalance_ok_iff.mp weighed
  have distinct : (attesters.map UInt64.toNat).Nodup := by
    unfold getUnslashedAttestingIndices at listed
    obtain ⟨_, -, among⟩ := bind_ok_iff.mp listed
    exact unslashedAmong_nodup among
  -- A position with a nonzero weight names a validator of the registry.
  have named : ∀ j, (if j.toUInt64 ∈ attesters then ((state.validators.data[j]?).map
      (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat / root
      else 0) ≠ 0 → j < state.validators.data.size := by
    intro j nonzero
    by_contra outside
    rw [Array.getElem?_eq_none (by omega)] at nonzero
    simp at nonzero
  have mapped : (attesters.map fun index => ((state.validators.data[index.toNat]?).map
      (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat / root) =
      (attesters.map UInt64.toNat).map fun j => ((state.validators.data[j]?).map
        (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat / root := by
    rw [List.map_map]
    rfl
  rw [mapped, ← sum_map_eq_of_nodup distinct List.nodup_range ?_ ?_]
  · congr 1
    refine List.map_congr_left fun j member => ?_
    obtain ⟨index, held, rfl⟩ := List.mem_map.mp member
    have same : index.toNat.toUInt64 = index := by
      rw [Nat.toUInt64_eq, UInt64.ofNat_toNat]
    rw [same, ite_eq_left held]
  · intro j nonzero
    have below := named j nonzero
    have listedHere : j.toUInt64 ∈ attesters := by
      by_contra absent
      simp [absent] at nonzero
    exact List.mem_map.mpr ⟨j.toUInt64, listedHere, toNat_toUInt64_of_lt within below⟩
  · exact fun j nonzero => List.mem_range.mpr (named j nonzero)

/-- Before Altair, take the rewards of one kind of vote among those that match the source.

Four times the reward of a validator is at most its weight if it signed the source, else zero.

The weight is its effective balance times the factor, over the root of the active balance.

That needs the signers of the source to hold no more balance than is active. -/
private theorem four_mul_componentReward_le_of_subset (before : fork < .altair)
    (within : state.RegistryWithinLimit)
    {fewer attestations : Array (PendingAttestation preset)} {rewards penalties : Array Gwei}
    (computed : getAttestationComponentDeltas state fewer = .ok (rewards, penalties))
    (sub : ∀ attestation ∈ fewer, attestation ∈ attestations)
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {attesters : List ValidatorIndex} {attestingBalance : Gwei}
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters)
    (weighed : getTotalBalance state attesters = .ok attestingBalance)
    (kept : attestingBalance ≤ total) {j : Nat} (inside : j < state.validators.data.size) :
    4 * (rewards.getD j 0).toNat ≤
      if j.toUInt64 ∈ attesters then ((state.validators.data[j]?).map
        (·.effectiveBalance.toNat)).getD 0 * preset.BASE_REWARD_FACTOR.toNat /
          Nat.sqrt total.toNat else 0 := by
  obtain ⟨-, few, fewBalance, -, fewListed, fewWeighed, -⟩ :=
    getAttestationComponentDeltas_getD within computed
  have among := mem_getUnslashedAttestingIndices_of_subset sub fewListed listed
  have lighter := getTotalBalance_le_of_subset among fewWeighed weighed
  refine Nat.le_trans (four_mul_componentReward_le before within computed active fewListed
    fewWeighed (UInt64.le_trans lighter kept) inside) ?_
  by_cases signed : j.toUInt64 ∈ few
  · rw [ite_eq_left signed, ite_eq_left (among _ signed)]
  · rw [ite_eq_right signed]
    exact Nat.zero_le _

/-- Before Altair, the attestation rewards over the registry sum to at most the issuance bound.

That needs the signers of the source to hold no more balance than is active.

It also needs a registry within its limit, and an increment above zero. -/
private theorem sum_attestationRewards_le {config : Config} (before : fork < .altair)
    (within : state.RegistryWithinLimit)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) {rewards penalties : Array Gwei}
    (computed : getAttestationDeltas config state before = .ok (rewards, penalties))
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {attestations : Array (PendingAttestation preset)} {attesters : List ValidatorIndex}
    {attestingBalance : Gwei}
    (matching :
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations)
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters)
    (weighed : getTotalBalance state attesters = .ok attestingBalance)
    (kept : attestingBalance ≤ total) :
    ((List.range state.validators.data.size).map fun j => (rewards.getD j 0).toNat).sum ≤
      preset.epochIssuanceBeforeAltair total.toNat := by
  obtain ⟨⟨sourceRewards, sourcePenalties⟩, ⟨targetRewards, targetPenalties⟩,
    ⟨headRewards, headPenalties⟩, ⟨inclusionRewards, inclusionPenalties⟩, inactivity, sourceOk,
    targetOk, headOk, inclusionOk, inactivityOk, entries⟩ :=
    getAttestationDeltas_getD before computed
  have sourceDeltas :
      getAttestationComponentDeltas state attestations = .ok (sourceRewards, sourcePenalties) := by
    unfold getSourceDeltas at sourceOk
    rw [matching] at sourceOk
    exact sourceOk
  unfold getTargetDeltas at targetOk
  obtain ⟨target, targetMatching, targetDeltas⟩ := bind_ok_iff.mp targetOk
  unfold getHeadDeltas at headOk
  obtain ⟨head, headMatching, headDeltas⟩ := bind_ok_iff.mp headOk
  have targetSub := mem_of_getMatchingTargetAttestations before matching targetMatching
  have headSub := mem_of_getMatchingHeadAttestations before targetMatching headMatching
  -- Each validator earns at most three weights for its votes.
  have votes : ∀ j ∈ List.range state.validators.data.size,
      4 * (rewards.getD j 0).toNat ≤ 3 * (if j.toUInt64 ∈ attesters then
        ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0 *
          preset.BASE_REWARD_FACTOR.toNat / Nat.sqrt total.toNat else 0) +
        4 * (inclusionRewards.getD j 0).toNat := by
    intro j member
    have inside := List.mem_range.mp member
    have source := four_mul_componentReward_le_of_subset before within sourceDeltas
      (fun _ held => held) active listed weighed kept inside
    have target := four_mul_componentReward_le_of_subset before within targetDeltas targetSub
      active listed weighed kept inside
    have head := four_mul_componentReward_le_of_subset before within headDeltas
      (fun attestation held => targetSub attestation (headSub attestation held))
      active listed weighed kept inside
    have sum := (entries j inside).1
    simp only at sum
    omega
  have summed := sum_map_le_sum_map votes
  rw [List.sum_map_add, sum_map_mul_left, sum_map_mul_left, sum_map_mul_left] at summed
  have inclusion := four_mul_inclusionRewards_le before inclusionOk active matching listed
    state.validators.data.size
  rw [sum_weights_eq within listed weighed] at inclusion
  have weights := sum_range_weights_le within weighed (Nat.sqrt total.toNat)
  have positive : 0 < total.toNat := Nat.lt_of_lt_of_le increment
    (UInt64.le_iff_toNat_le.mp (le_getTotalBalance (getTotalActiveBalance_ok active)))
  have heavier : attestingBalance.toNat * preset.BASE_REWARD_FACTOR.toNat /
      Nat.sqrt total.toNat ≤ total.toNat * preset.BASE_REWARD_FACTOR.toNat /
        Nat.sqrt total.toNat :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp kept))
  have issuance := mul_div_sqrt_le positive preset.BASE_REWARD_FACTOR.toNat
  unfold Preset.epochIssuanceBeforeAltair
  omega

/-- Before Altair, take a step where the source signers hold no more balance than is active.

The signers are the unslashed ones of the previous epoch, and the active balance is the current one.

That is an assumption: it fails when validators that signed exit at the epoch boundary.

Then the step raises the sum of the balances by at most the issuance bound.

That needs a registry within its limit, and an increment above zero. -/
theorem processRewardsAndPenalties_balanceSum_le_of_lt_altair {config : Config}
    (before : fork < .altair) (within : state.RegistryWithinLimit)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (computed : processRewardsAndPenalties config state = .ok after)
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {attestations : Array (PendingAttestation preset)} {attesters : List ValidatorIndex}
    {attestingBalance : Gwei}
    (matching :
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations)
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters)
    (weighed : getTotalBalance state attesters = .ok attestingBalance)
    (kept : attestingBalance ≤ total) :
    balanceSum after ≤ balanceSum state + preset.epochIssuanceBeforeAltair total.toNat := by
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · rw [processRewardsAndPenalties_genesis config genesis] at computed
    cases computed
    exact Nat.le_add_right _ _
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  simp only [processRewardsAndPenalties, genesis, notAltair, ↓reduceIte, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨⟨rewards, penalties⟩, found, applied⟩ := computed
  have raised := balanceSum_foldlM_applyDeltas_le (indices := List.range _) applied
  simp only at raised
  have bounded := sum_attestationRewards_le before within increment found active matching
    listed weighed kept
  omega

/-- Before Altair, the steps after the rewards never raise the sum of the balances.

There are no pending deposits before Electra, and the rotation of the votes keeps the balances. -/
private theorem balanceSum_le_of_tail {config : Config} {checks : SignatureChecks}
    (before : fork < .altair)
    (trace : EpochTrace (action config checks) [.registry, .slashings, .eth1Reset,
      .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances, .slashingsReset,
      .randaoReset, .history, .participation, .syncCommittees, .proposerLookahead,
      .ptcWindow] state after) :
    balanceSum after ≤ balanceSum state := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  have notElectra : ¬ .pectra ≤ fork := fun h => notAltair (Nat.le_trans (by decide) h)
  have notFulu : ¬ .fusaka ≤ fork := fun h => notAltair (Nat.le_trans (by decide) h)
  have notGloas : ¬ .glamsterdam ≤ fork := fun h => notAltair (Nat.le_trans (by decide) h)
  have noDeposits : ∀ other : BeaconState preset fork, pendingDepositSum other = 0 := fun _ => by
    simp [pendingDepositSum, notElectra]
  refine trace.transport (fun first second => balanceSum second ≤ balanceSum first)
    (fun _ => Nat.le_refl _) (fun one two => Nat.le_trans two one)
    fun stage member first second ok => ?_
  by_cases early : stage ∈ [.registry, .slashings, .eth1Reset, .pendingDeposits,
      .pendingConsolidations, .payments, .effectiveBalances]
  · have lowered := supply_le_of_action early ok
    rw [noDeposits, noDeposits] at lowered
    exact lowered
  have edge := action_cases.mp ok
  refine Nat.le_of_eq (balanceSum_eq_of_balances ?_)
  cases stage <;> simp only [Edge] at edge <;> try (simp at member early; done)
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    rfl
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    rfl
  case history =>
    split at edge
    · unfold processHistoricalSummariesUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals rfl
    · unfold processHistoricalRootsUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals rfl
  case participation =>
    simp only [notAltair, ↓reduceDIte, processParticipationRecordUpdates, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq] at edge
    subst edge
    rfl
  case syncCommittees =>
    simp only [notAltair, ↓reduceDIte] at edge
    subst edge
    rfl
  case proposerLookahead =>
    simp only [notFulu, ↓reduceDIte] at edge
    subst edge
    rfl
  case ptcWindow =>
    simp only [notGloas, ↓reduceDIte] at edge
    subst edge
    rfl

/-- Justification and finalization keep every field that the rewards read before Altair.

These are the registry, the slot, the balances, the mixes, the votes and the flags. -/
private theorem processJustificationAndFinalization_rewardFields
    (computed : processJustificationAndFinalization state = .ok after) :
    after.validators = state.validators ∧ after.slot = state.slot ∧
      after.balances = state.balances ∧ after.randaoMixes = state.randaoMixes ∧
      after.previousEpochAttestations = state.previousEpochAttestations ∧
      after.currentEpochAttestations = state.currentEpochAttestations ∧
      after.previousEpochParticipation = state.previousEpochParticipation ∧
      after.currentEpochParticipation = state.currentEpochParticipation := by
  rw [processJustificationAndFinalization_eq computed]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two states with the same registry and mixes have the same unslashed signers of any votes. -/
private theorem getUnslashedAttestingIndices_congr {other : BeaconState preset fork}
    (validators : other.validators = state.validators)
    (mixes : other.randaoMixes = state.randaoMixes)
    (attestations : Array (PendingAttestation preset)) :
    getUnslashedAttestingIndices other attestations =
      getUnslashedAttestingIndices state attestations := by
  have committees : ∀ slot index,
      getBeaconCommittee other slot index = getBeaconCommittee state slot index :=
    fun slot index => CommitteesKept.of_eq (congrArg (·.data) validators)
      (congrArg (·.elements) mixes) _ slot index rfl
  have pending : getPendingAttestingIndices other = getPendingAttestingIndices state :=
    funext fun attestation => by simp only [getPendingAttestingIndices, committees]
  simp only [getUnslashedAttestingIndices, unslashedAmong, pending, getValidator, validators]

/-- Before Altair, the epoch transition raises the sum of the balances by at most the bound.

The bound reads the active balance of the state before the epoch.

Assume the unslashed signers of the source in the previous epoch hold at most the active balance.

That fails when validators that signed exit at the epoch boundary.

That needs a registry within its limit, and an increment above zero. -/
theorem processEpoch_supply_le_of_lt_altair {config : Config} {checks : SignatureChecks}
    (before : fork < .altair) (within : state.RegistryWithinLimit)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {attestations : Array (PendingAttestation preset)} {attesters : List ValidatorIndex}
    {attestingBalance : Gwei}
    (matching :
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations)
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters)
    (weighed : getTotalBalance state attesters = .ok attestingBalance)
    (kept : attestingBalance ≤ total)
    (computed : processEpoch config checks state = .ok after) :
    balanceSum after ≤ balanceSum state + preset.epochIssuanceBeforeAltair total.toNat := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity, .rewards] ++ [.registry, .slashings,
    .eth1Reset, .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances,
    .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨rewarded, head, tail⟩ := EpochTrace.append_iff.mp trace
  have lowered := balanceSum_le_of_tail before tail
  obtain _ | ⟨justifiedOk, head⟩ := head
  obtain _ | ⟨scoredOk, head⟩ := head
  obtain _ | ⟨rewardedOk, head⟩ := head
  cases head
  rename_i justified scored
  have justifiedEq : processJustificationAndFinalization state = .ok justified :=
    action_cases.mp justifiedOk
  have scoredEq := action_cases.mp scoredOk
  simp only [Edge, notAltair, ↓reduceDIte] at scoredEq
  subst scoredEq
  have rewardedEq : processRewardsAndPenalties config justified = .ok rewarded :=
    action_cases.mp rewardedOk
  -- Justification changes only the checkpoints and their bits, which the rewards do not read.
  obtain ⟨validators, slot, balances, mixes, previousVotes, currentVotes, previousFlags,
    currentFlags⟩ := processJustificationAndFinalization_rewardFields justifiedEq
  obtain ⟨activeSame, totalSame, -, previousSame⟩ :=
    rewardReads_congr validators slot previousFlags currentFlags
  have matchingSame : getMatchingSourceAttestations justified before
      (getPreviousEpoch justified) = .ok attestations := by
    rw [previousSame, ← matching]
    unfold getMatchingSourceAttestations getCurrentEpoch
    rw [slot, previousVotes, currentVotes, previousSame]
  have raised := processRewardsAndPenalties_balanceSum_le_of_lt_altair before
    (by unfold BeaconState.RegistryWithinLimit; rw [validators]; exact within) increment
    rewardedEq (activeSame.trans active) matchingSame
    ((getUnslashedAttestingIndices_congr validators mixes attestations).trans listed)
    ((totalSame attesters).trans weighed) kept
  rw [balanceSum_eq_of_balances balances] at raised
  omega

/-- Before Altair, without pending attestations, the signers hold no more balance than is active.

Without a signer the total is the floor of one increment, and the active balance has that floor.

A run of slots without blocks has no pending attestations from its third epoch on.

Both lists are read, since in the first epoch the previous epoch is the current one. -/
theorem attestingBalance_le_of_empty (before : fork < .altair)
    (previousEmpty : (state.previousEpochAttestations before).data = #[])
    (currentEmpty : (state.currentEpochAttestations before).data = #[])
    {attestations : Array (PendingAttestation preset)} {attesters : List ValidatorIndex}
    {attestingBalance total : Gwei}
    (matching :
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations)
    (listed : getUnslashedAttestingIndices state attestations = .ok attesters)
    (weighed : getTotalBalance state attesters = .ok attestingBalance)
    (active : getTotalActiveBalance state = .ok total) :
    attestingBalance ≤ total := by
  have none : attestations = #[] := by
    unfold getMatchingSourceAttestations at matching
    rw [bind_ok_iff] at matching
    obtain ⟨_, -, matching⟩ := matching
    simp only [pure, Except.pure, Except.ok.injEq] at matching
    rw [← matching]
    split
    · exact currentEmpty
    · exact previousEmpty
  subst none
  have nobody : attesters = [] := by
    simp only [getUnslashedAttestingIndices, unslashedAmong, List.mapM_nil,
      pure, Except.pure, bind, Except.bind, List.flatten_nil] at listed
    refine List.eq_nil_iff_forall_not_mem.mpr fun index member => ?_
    have := mem_sortedSet.mp (mem_of_filterM_ok listed member)
    simp at this
  subst nobody
  obtain ⟨-, -, rfl⟩ := getTotalBalance_ok_iff.mp weighed
  have zero : sumMarked state.validators.data
      (markIndices state.validators.data.size []) = 0 := by
    rw [sumMarked_eq_sum]
    refine List.sum_eq_zero fun term member => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp member
    simp only [getElem?_markIndices]
    split_ifs <;> simp_all
  rw [zero, UInt64.max_def]
  split
  · simp
  · exact le_getTotalBalance (getTotalActiveBalance_ok active)

end EthLib.Consensus
