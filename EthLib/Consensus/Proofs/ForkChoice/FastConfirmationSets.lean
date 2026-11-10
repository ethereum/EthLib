module

public import EthLib.Consensus.Proofs.ForkChoice.AttestationScores
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationIndicators
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Accessors

/-!
# Proofs: the sets of validators behind the numbers of the fast confirmation rule

The fast confirmation rule of [arXiv 2405.00549v4][fcr] compares numbers that the store computes.

Its proof reasons about sets of validators: the supporters of a block, the equivocators, and `W`.

Here `W` is the set of validators of the committees of a range of slots, as in Definition 4.

This file builds each set from the store and shows that its stake is the store's number.

The supporters of a node are the validators that count in a state and whose vote counts for it.

Their stake is the store's votes for the node, at every fork.

The members of `W` are the members of the committees that are active in the source of balances.

The equivocators are those of them that the store knows to equivocate.

Their stake is the store's weight of the known equivocators of those committees.

No equivocator supports a node, so the two sets are apart.

With these sets, Lemmas 4 and 3 of the paper hold for a block that the store confirms.

They need each supporter to be a member of the committees of the range.

The store does not record the slot of a latest vote, so that hypothesis stays.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork}

/-- Whether a state holds a validator at an index, active in the epoch of that state. -/
def activeAt (state : BeaconState preset fork) (index : ValidatorIndex) : Bool :=
  state.validators.data[index.toNat]?.any (isActiveValidator · (getCurrentEpoch state))

/-- The members of some committees that are active in a source of balances. -/
def activeMembers (balanceSource : BeaconState preset fork)
    (participants : Std.TreeSet ValidatorIndex) : Finset ValidatorIndex :=
  participants.toList.toFinset.filter (activeAt balanceSource ·)

namespace Store

variable (store : Store preset fork)

/-- The validators whose votes the store counts for a node, from a state.

They are active and not slashed in that state, and their latest vote counts for the node. -/
def supportersOf (state : BeaconState preset fork) (node : ForkChoiceNode) :
    Finset ValidatorIndex :=
  (((unslashedActiveBalances state).filter (store.voteCountsFor node ·.1)).map (·.1)).toFinset

/-- The known equivocators among the members of some committees active in a source of balances.
-/
def equivocatorsOf (balanceSource : BeaconState preset fork)
    (participants : Std.TreeSet ValidatorIndex) : Finset ValidatorIndex :=
  (activeMembers balanceSource participants).filter (· ∈ store.equivocatingIndices)

variable {store}

/-- A sum over the entries of a list that pass a test is a sum over all of them, with zeros. -/
private theorem sum_map_filter {α : Type} (entries : List α) (test : α → Bool) (value : α → ℕ) :
    ((entries.filter test).map value).sum =
      (entries.map fun entry => if test entry then value entry else 0).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    by_cases passes : test entry <;> simp [passes, ih]

/-- The votes that the store counts for a node are the stake of its supporters.

A validator weighs its effective balance in the state.

The registry of the state must stay within the limit of the preset. -/
theorem stake_supportersOf {node : ForkChoiceNode} {state : BeaconState preset fork}
    {score : Gwei} (within : state.RegistryWithinLimit)
    (computed : store.getAttestationScore node state = .ok score) :
    stake (fun v => balanceAt state v.toNat) (store.supportersOf state node) = score.toNat := by
  set entries := unslashedActiveBalances state
  -- Each entry is a position of the registry with its effective balance.
  have balance : ∀ entry ∈ entries, balanceAt state entry.1.toNat = entry.2.toNat := by
    rintro ⟨index, gwei⟩ member
    simp only [entries, unslashedActiveBalances, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at member
    obtain ⟨validator, i, inZip, -, rfl, rfl⟩ := member
    have found := (List.mem_zipIdx_iff_getElem?.mp inZip)
    have lt : i < state.validators.data.size := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    rw [toNat_toUInt64_of_lt within lt]
    simp [balanceAt, by simpa using found]
  -- The positions are distinct.
  have distinct : (entries.map (·.1)).Nodup := by
    have sorted := validatorPositions_sorted within
      fun validator => isActiveValidator validator (getCurrentEpoch state) && !validator.slashed
    have same : entries.map (·.1) = state.validators.data.toList.zipIdx.filterMap
        fun (validator, index) =>
          if isActiveValidator validator (getCurrentEpoch state) && !validator.slashed then
            some index.toUInt64
          else none := by
      simp only [entries, unslashedActiveBalances, List.map_filterMap]
      congr 1
      funext entry
      split <;> rfl
    rw [same]
    exact sorted.imp UInt64.ne_of_lt
  have chosen := ((List.filter_sublist (p := fun entry : ValidatorIndex × Gwei =>
    store.voteCountsFor node entry.1) (l := entries)).map (·.1)).nodup distinct
  rw [supportersOf, stake, List.sum_toFinset _ chosen, List.map_map,
    store.getAttestationScore_toNat_eq_sum computed]
  exact (congrArg List.sum (List.map_congr_left (g := fun entry => entry.2.toNat)
    fun entry member => balance entry (List.mem_of_mem_filter member))).trans
      (sum_map_filter entries _ _)

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
    simp only [List.mem_toFinset, equivocatorsOf, activeMembers, Finset.mem_filter]
    constructor
    · intro member
      have kept := mem_of_filterM_ok activeOk member
      have passes := passes_of_mem_filterM_ok activeOk member
      simp only [List.mem_filter, decide_eq_true_eq] at kept
      refine ⟨⟨kept.1, ?_⟩, kept.2⟩
      cases found : balanceSource.validators.data[v.toNat]? with
      | none => simp [validatorAt, found, throw, throwThe, MonadExceptOf.throw, bind,
          Except.bind] at passes
      | some validator =>
        simpa [activeAt, validatorAt, found, bind, Except.bind, pure, Except.pure] using passes
    · rintro ⟨⟨inside, isActive⟩, equivocating⟩
      refine mem_filterM_ok_of_test activeOk
        (List.mem_filter.mpr ⟨inside, by simpa using equivocating⟩) ?_
      cases found : balanceSource.validators.data[v.toNat]? with
      | none => simp [activeAt, found] at isActive
      | some validator =>
        simp only [activeAt, found, Option.any_some] at isActive
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
theorem equivocatorsOf_subset {balanceSource : BeaconState preset fork}
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

/-- Lemmas 4 and 3 for a block that the store confirms, with the sets that the store weighs.

Here `Φ` is the store's: the committee weight since the parent, plus the boost.

The discount is taken off it, and is added to the other side so that nothing truncates.

A validator weighs its effective balance in the source of balances.

The votes come from the tally of that source, as the handler of the rule takes them.

The supporters are the validators that this tally counts for the block.

`W` is the set of members of the committees of the range of the adversary that are active.

The equivocators are the members of `W` that the store knows to equivocate.

Assume that each supporter is a member of those committees.

Assume that the Byzantine validators hold at most β of the stake of `W`, Assumption 2.

Here β is the threshold of the configuration, in percent, and no known equivocator is honest.

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
    (supportersIn : store.supportersOf balanceSource ⟨root, .pending⟩ ⊆
      activeMembers balanceSource participants)
    (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (activeMembers balanceSource participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ store.supportersOf balanceSource ⟨root, .pending⟩ | v ∈ J} := by
  -- The store reads the support, the threshold, the weight and the equivocators.
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    isOneConfirmed_eq_ok_true_iff.mp confirmed
  obtain ⟨weight, equivocation, weightOk, equivocationOk⟩ := computeAdversarialWeight_eq_ok rangeOk
  have equivocationOfOk :
      store.getEquivocationScoreOf balanceSource participants = .ok equivocation := by
    simpa [getEquivocationScore, participantsOk, bind, Except.bind] using equivocationOk
  -- Each member of `W` is a member of the committees, active in the source of balances.
  have inside : ∀ v ∈ activeMembers balanceSource participants, v ∈ participants ∧
      ∃ validator, balanceSource.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch balanceSource) = true := by
    intro v member
    rw [activeMembers, Finset.mem_filter, List.mem_toFinset, Std.TreeSet.mem_toList] at member
    obtain ⟨inParticipants, isActive⟩ := member
    refine ⟨inParticipants, ?_⟩
    cases found : balanceSource.validators.data[v.toNat]? with
    | none => simp [activeAt, found] at isActive
    | some validator => exact ⟨validator, rfl, by simpa [activeAt, found] using isActive⟩
  -- Each effective balance is a whole number of increments, so of 100 Gwei.
  have whole : ∀ v ∈ activeMembers balanceSource participants,
      balanceAt balanceSource v.toNat % 100 = 0 := by
    intro v member
    obtain ⟨-, validator, found, -⟩ := inside v member
    have increments := (aligned validator
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))).1
    rw [← UInt64.toNat_inj, UInt64.toNat_mod] at increments
    simp only [balanceAt, found, Option.map_some, Option.getD_some]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero increment)
      (Nat.dvd_of_mod_eq_zero increments))
  exact lt_two_mul_honest_support_of_isOneConfirmed slotOk blockOk parentOk boostOk firstOk lastOk
    maximumOk discountOk adversaryOk rangeOk participantsOk weightOk equivocationOk thresholdOk
    supportOk confirmed (stake_supportersOf within supportOk)
    (stake_equivocatorsOf equivocationOfOk) supportersIn equivocatorsOf_subset inside whole
    disjoint_supportersOf_equivocatorsOf
    (fun v member => dishonest v (Finset.mem_filter.mp member).2) byzantine

end Store

end EthLib.Consensus
