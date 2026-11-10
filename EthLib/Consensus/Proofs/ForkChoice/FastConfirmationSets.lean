module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationIndicators
public import EthLib.Consensus.Proofs.ForkChoice.Supporters

/-!
# Proofs: the sets of validators behind the numbers of the fast confirmation rule

The fast confirmation rule of [arXiv 2405.00549v4][fcr] compares numbers that the store computes.

Its proof reasons about sets of validators: the supporters of a block, the equivocators, and `W`.

Here `W` is a set of validators whose stake the store's weight of a range of slots covers.

This file builds each set from the store and shows that its stake is the store's number.

The supporters of a node are the validators that count in a state and whose vote counts for it.

Their stake is the store's votes for the node, at every fork.

Usually `W` is the active members of the committees of the range, as in Section 2.1 of the paper.

The equivocators are the active members of those committees that the store knows to equivocate.

Their stake is the store's weight of the known equivocators of those committees.

No equivocator supports a node, so the two sets are apart.

With these sets, Lemmas 4 and 3 of the paper hold for a block that the store confirms.

They need each supporter to be a member of the committees of the range.

No theorem yet proves it.

The store checks a vote against the committees in the state of its target.

The rule reads them in the state of the head, and the two must agree on the slot of the vote.

A range with a whole epoch is weighed by the total active balance of the source of balances.

There `W` can be every validator active in that source, which holds each supporter.

So for such a range that hypothesis drops.

Both forms also need each effective balance of the source to be a whole number of increments.

In the rule, the source of those lemmas is the state of an observed justified checkpoint.

In a reachable store that state keeps the invariant of the state transition.

So in a reachable store that hypothesis holds, when the largest of the preset are whole.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork}

namespace Store

/-- The members of some committees that are active in a source of balances. -/
def activeMembers (balanceSource : BeaconState preset fork)
    (participants : Std.TreeSet ValidatorIndex) : Finset ValidatorIndex :=
  participants.toList.toFinset.filter
    (isActiveAt balanceSource (getCurrentEpoch balanceSource) ·.toNat)

/-- A validator is an active member of some committees when it is one of them, held by the source.

It must be active there in the epoch of that source. -/
theorem mem_activeMembers {balanceSource : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {v : ValidatorIndex} :
    v ∈ activeMembers balanceSource participants ↔ v ∈ participants ∧ ∃ validator,
      balanceSource.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch balanceSource) = true := by
  rw [activeMembers, Finset.mem_filter, List.mem_toFinset, Std.TreeSet.mem_toList]
  refine and_congr_right fun _ => ?_
  cases found : balanceSource.validators.data[v.toNat]? <;> simp [isActiveAt, found]

variable (store : Store preset fork)

/-- The known equivocators among the members of some committees active in a source of balances.
-/
def equivocatorsOf (balanceSource : BeaconState preset fork)
    (participants : Std.TreeSet ValidatorIndex) : Finset ValidatorIndex :=
  (activeMembers balanceSource participants).filter (· ∈ store.equivocatingIndices)

variable {store}

/-- The store's weight of the known equivocators of some committees is their stake.

A validator weighs its effective balance in the source of balances. -/
theorem stake_equivocatorsOf {balanceSource : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {score : Gwei}
    (computed : store.getEquivocationScoreOf balanceSource participants = .ok score) :
    stake (fun v => balanceAt balanceSource v.toNat)
      (store.equivocatorsOf balanceSource participants) = score.toNat := by
  simp only [getEquivocationScoreOf, bind_ok_iff] at computed
  obtain ⟨active, activeOk, summed⟩ := computed
  -- The filter keeps the known equivocators of the committees that are active.
  have members : active.toFinset = store.equivocatorsOf balanceSource participants := by
    ext v
    simp only [List.mem_toFinset, equivocatorsOf, Finset.mem_filter, mem_activeMembers]
    constructor
    · intro member
      have kept := mem_of_filterM_ok activeOk member
      have passes := passes_of_mem_filterM_ok activeOk member
      simp only [List.mem_filter, decide_eq_true_eq] at kept
      refine ⟨⟨Std.TreeSet.mem_toList.mp kept.1, ?_⟩, kept.2⟩
      cases found : balanceSource.validators.data[v.toNat]? with
      | none => simp [validatorAt, found, throw, throwThe, MonadExceptOf.throw, bind,
          Except.bind] at passes
      | some validator =>
        exact ⟨validator, rfl, by
          simpa [validatorAt, found, bind, Except.bind, pure, Except.pure] using passes⟩
    · rintro ⟨⟨inside, validator, found, isActive⟩, equivocating⟩
      refine mem_filterM_ok_of_test activeOk
        (List.mem_filter.mpr ⟨Std.TreeSet.mem_toList.mpr inside, by simpa using equivocating⟩) ?_
      simp [validatorAt, found, isActive, bind, Except.bind, pure, Except.pure]
  have distinct : active.Nodup :=
    ((sublist_of_filterM_ok activeOk).trans List.filter_sublist).nodup
      (Std.TreeSet.distinct_toList.imp fun different same =>
        different (Std.LawfulEqCmp.compare_eq_iff_eq.mpr same))
  rw [← members, stake, List.sum_toFinset _ distinct]
  refine (toNat_eq_of_sumGwei summed fun v _ value valueOk => ?_).symm
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at valueOk
  obtain ⟨validator, found, rfl⟩ := valueOk
  simp [balanceAt, validatorAt_ok_iff.mp found]

/-- The known equivocators of some committees are among their active members. -/
theorem equivocatorsOf_subset_activeMembers {balanceSource : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} :
    store.equivocatorsOf balanceSource participants ⊆ activeMembers balanceSource participants :=
  Finset.filter_subset _ _

/-- No known equivocator supports a node. -/
theorem disjoint_supportersOf_equivocatorsOf {state balanceSource : BeaconState preset fork}
    {node : ForkChoiceNode} {participants : Std.TreeSet ValidatorIndex} :
    Disjoint (store.supportersOf state node) (store.equivocatorsOf balanceSource participants) := by
  refine Finset.disjoint_left.mpr fun v supporter equivocator => ?_
  simp only [supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at supporter
  obtain ⟨⟨index, gwei⟩, ⟨-, counts⟩, rfl⟩ := supporter
  have known : store.equivocatingIndices.contains index = true := by
    simpa using (Finset.mem_filter.mp equivocator).2
  simp only [voteCountsFor] at counts
  split at counts
  · cases counts
  · simp at counts
    exact counts.1 (by simpa using known)

variable {config : Config}

/-- Lemmas 4 and 3 for a confirmed block, with any set `W` whose stake the store's weight covers.

The committee weight since the parent, plus the boost, is the store's `Φ`.

The discount is taken off it, and is added to the other side so that nothing truncates.

A validator weighs its effective balance in the source of balances.

The votes come from the tally of that source, as the handler of the rule takes them.

The supporters are the validators that this tally counts for the block.

The range ends at the last slot, and its adversary must be the adversary of the block.

The range that the rule uses for the block is one such range.

`W` must hold each supporter, and each active member of the committees of the range.

The store's weight of the range must cover the stake of `W`.

Assume that the Byzantine validators hold at most β of the stake of `W`.

Here β is the threshold of the configuration, in percent.

Assume that no known equivocator is honest.

Assume also that each effective balance of the source is a whole number of increments.

An increment must be a whole number of 100 Gwei, as 10^9 Gwei in the presets is.

The registry of the source of balances must stay within the limit of the preset. -/
theorem lt_two_mul_honest_supportersOf_of_weighed {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] {W : Finset ValidatorIndex} {head root : Root}
    {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (confirmed : store.isOneConfirmed config head balanceSource (store.tallyVotes balanceSource)
      root = .ok true)
    (supportersIn : store.supportersOf balanceSource ⟨root, .pending⟩ ⊆ W)
    (membersIn : ∀ participants,
      store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants →
        activeMembers balanceSource participants ⊆ W)
    (weighed : ∀ weight,
      store.computeCommitteeWeightBetweenSlots head balanceSource startSlot lastSlot = .ok weight →
        stake (fun v => balanceAt balanceSource v.toNat) W ≤ weight.toNat)
    (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat) W J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ store.supportersOf balanceSource ⟨root, .pending⟩ | v ∈ J} := by
  -- The store reads the support, the threshold, the weight and the equivocators.
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    isOneConfirmed_eq_ok_true_iff.mp confirmed
  obtain ⟨weight, equivocation, weightOk, equivocationOk⟩ := computeAdversarialWeight_eq_ok rangeOk
  have equivocationOfOk : ∃ participants,
      store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants ∧
        store.getEquivocationScoreOf balanceSource participants = .ok equivocation := by
    simpa only [getEquivocationScore, bind_ok_iff] using equivocationOk
  obtain ⟨participants, participantsOk, equivocationOfOk⟩ := equivocationOfOk
  -- Each effective balance is a whole number of increments, so of 100 Gwei.
  have whole : ∀ v ∈ W, balanceAt balanceSource v.toNat % 100 = 0 := fun v _ =>
    Nat.mod_eq_zero_of_dvd (dvd_balanceAt_of_aligned aligned (Nat.dvd_of_mod_eq_zero increment) _)
  exact lt_two_mul_honest_support_of_isOneConfirmed slotOk blockOk parentOk boostOk firstOk lastOk
    maximumOk discountOk adversaryOk rangeOk weightOk equivocationOk thresholdOk
    supportOk confirmed (stake_supportersOf within supportOk)
    (stake_equivocatorsOf equivocationOfOk) supportersIn
    (equivocatorsOf_subset_activeMembers.trans (membersIn participants participantsOk))
    (weighed weight weightOk) whole disjoint_supportersOf_equivocatorsOf
    (fun v member => dishonest v (Finset.mem_filter.mp member).2) byzantine

/-- Lemmas 4 and 3 for a confirmed block, with `W` the active members of the committees of a range.

A validator weighs its effective balance in the source of balances, and is active there.

The supporters are the validators that the tally of that source counts for the block.

The range ends at the last slot, and its adversary must be the adversary of the block.

The range that the rule uses for the block is one such range.

Assume that each supporter is a member of the committees of the range.

Assume that the Byzantine validators hold at most β of the stake of `W`, Assumption 2.

Here β is the threshold of the configuration, in percent.

Assume that no known equivocator is honest.

Assume also that each effective balance of the source is a whole number of increments.

An increment must be a whole number of 100 Gwei, as 10^9 Gwei in the presets is.

The registry of the source of balances must stay within the limit of the preset. -/
theorem lt_two_mul_honest_supportersOf_of_isOneConfirmed {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {participants : Std.TreeSet ValidatorIndex}
    {proposerScore maximumSupport discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (participantsOk : store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants)
    (confirmed : store.isOneConfirmed config head balanceSource (store.tallyVotes balanceSource)
      root = .ok true)
    (supportersIn : ∀ v ∈ store.supportersOf balanceSource ⟨root, .pending⟩, v ∈ participants)
    (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (activeMembers balanceSource participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ store.supportersOf balanceSource ⟨root, .pending⟩ | v ∈ J} := by
  refine lt_two_mul_honest_supportersOf_of_weighed within slotOk blockOk parentOk boostOk firstOk
    lastOk maximumOk discountOk adversaryOk rangeOk confirmed
    (fun v member => Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (Std.TreeSet.mem_toList.mpr (supportersIn v member)),
        isActiveAt_of_mem_supportersOf within member⟩)
    (fun found foundOk => ?_)
    (fun weight weightOk => stake_le_computeCommitteeWeightBetweenSlots participantsOk weightOk
      fun v member => mem_activeMembers.mp member) aligned increment dishonest byzantine
  rw [participantsOk, Except.ok.injEq] at foundOk
  exact foundOk ▸ Finset.Subset.refl _

/-- Lemmas 4 and 3 for a confirmed block whose range of the adversary holds a whole epoch.

The store then weighs that range by the total active balance of the source of balances.

So `W` can be the set of validators active in that source, which holds each supporter.

A validator weighs its effective balance in the source of balances.

The supporters are the validators that the tally of that source counts for the block.

The range ends at the last slot, and its adversary must be the adversary of the block.

The range that the rule uses for the block is one such range.

Assume that the Byzantine validators hold at most β of the stake of `W`.

With a static set of validators each member of `W` is in a committee of the range.

This is then Assumption 2.

Otherwise `W` may hold validators that have left the committees.

When those are Byzantine, as under Assumption 1, this bound implies Assumption 2.

If an honest validator has left, the two bounds are incomparable.

The tally still counts the votes of those validators, so the proof bounds their stake.

Here β is the threshold of the configuration, in percent.

Assume that no known equivocator is honest.

Assume also that each effective balance of the source is a whole number of increments.

An increment must be a whole number of 100 Gwei, as 10^9 Gwei in the presets is.

The registry of the source of balances must stay within the limit of the preset. -/
theorem lt_two_mul_honest_supportersOf_of_covered {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (covered : isFullValidatorSetCovered preset startSlot lastSlot = .ok true)
    (confirmed : store.isOneConfirmed config head balanceSource (store.tallyVotes balanceSource)
      root = .ok true)
    (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (getActiveValidatorIndices balanceSource (getCurrentEpoch balanceSource)).toFinset J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ store.supportersOf balanceSource ⟨root, .pending⟩ | v ∈ J} :=
  lt_two_mul_honest_supportersOf_of_weighed within slotOk blockOk parentOk boostOk firstOk lastOk
    maximumOk discountOk adversaryOk rangeOk confirmed
    (fun _ member => List.mem_toFinset.mpr (mem_getActiveValidatorIndices_of_isActiveAt
      (isActiveAt_of_mem_supportersOf within member)))
    (fun _ _ _ member => List.mem_toFinset.mpr (mem_getActiveValidatorIndices_of_isActiveAt
      (Finset.mem_filter.mp member).2))
    (fun _ weightOk => stake_le_computeCommitteeWeightBetweenSlots_of_covered covered weightOk)
    aligned increment dishonest byzantine

end Store

end EthLib.Consensus
