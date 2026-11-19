module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.Supporters
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.ForkChoice.Ghost

/-!
# Proofs: the supporters of a block that the fast confirmation rule tests

Lemmas 4 and 3 of [arXiv 2405.00549v4][fcr] need each supporter of the block in a set `W`.

For a range with part of an epoch, `W` is the active members of the committees of the range.

This file places the slot of the vote of each supporter in that range.

That is the first step towards placing each supporter in those committees.

Another file shows that the state of the target and the state of the head agree on them.

A supporter of a block votes for a node that descends from it.

That node is a known block, from the slot of the block or later.

In a store where each latest vote has its origin, that vote comes from an attestation.

Its slot is at or after the slot of the voted block, and before the current slot.

So the slot of the vote lies in the range of the adversary of the block.

In particular, no vote counts for a block at the current slot, which is never one-confirmed.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- Each supporter of a known node votes by an attestation from the slot of that node or later.

Each latest vote of the store must come from an attestation, with the facts behind it. -/
theorem VotesHaveOrigins.exists_attestation_of_mem_supportersOf
    (holds : store.VotesHaveOrigins config) {state : BeaconState preset fork}
    {node : ForkChoiceNode} {block : BeaconBlock preset fork} {v : ValidatorIndex}
    (found : store.blocks[node.root]? = some block)
    (supporter : v ∈ store.supportersOf state node) :
    ∃ attestation, store.latestMessages[v]? = some (LatestMessage.ofAttestation attestation) ∧
      store.VoteOrigin config v attestation ∧ block.slot ≤ attestation.data.slot := by
  obtain ⟨message, sn, latest, -, supported, descends⟩ :=
    store.exists_of_voteCountsFor (store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨attestation, rfl, origin⟩ := holds latest
  obtain ⟨snBlock, snFound, slotLe⟩ := slot_le_of_isAncestor found descends
  have root := getSupportedNode_root supported
  obtain ⟨voted, votedFound, votedLe⟩ := origin.voted
  rw [root] at snFound
  have same : snBlock = voted := by
    simp only [LatestMessage.ofAttestation] at snFound
    rw [votedFound] at snFound
    exact (Option.some.inj snFound).symm
  subst same
  exact ⟨attestation, latest, origin, UInt64.le_trans slotLe votedLe⟩

/-- The vote of each supporter of a known block is from a slot of a range of slots.

The range starts at or before the slot of the block.

It ends at the last slot before the current one.

Each latest vote of the store must come from an attestation, with the facts behind it. -/
theorem VotesHaveOrigins.slot_mem_range_of_mem_supportersOf (holds : store.VotesHaveOrigins config)
    {state : BeaconState preset fork} {root : Root} {block : BeaconBlock preset fork}
    {currentSlot startSlot lastSlot : Slot} {v : ValidatorIndex}
    (blockOk : store.block root = .ok block) (startLe : startSlot ≤ block.slot)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (supporter : v ∈ store.supportersOf state ⟨root, .pending⟩) :
    ∃ attestation, store.latestMessages[v]? = some (LatestMessage.ofAttestation attestation) ∧
      store.VoteOrigin config v attestation ∧
      startSlot ≤ attestation.data.slot ∧ attestation.data.slot ≤ lastSlot := by
  have found : store.blocks[root]? = some block := block_ok_iff.mp blockOk
  obtain ⟨attestation, latest, origin, slotLe⟩ :=
    holds.exists_attestation_of_mem_supportersOf (node := ⟨root, .pending⟩) found supporter
  refine ⟨attestation, latest, origin, UInt64.le_trans startLe slotLe, ?_⟩
  obtain ⟨current, currentOk, past⟩ := origin.past
  rw [slotOk] at currentOk
  cases currentOk
  obtain ⟨le, eq⟩ := subChecked_ok_iff.mp lastOk
  rw [UInt64.le_iff_toNat_le]
  have := UInt64.lt_iff_toNat_lt.mp past
  simp only [UInt64.toNat_one] at le eq
  omega

/-- The tally indices are the registry positions of the active, unslashed validators. -/
private theorem tally_indices {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) :
    ((unslashedActiveBalances state).map (·.1)).toFinset.image UInt64.toNat =
      voters state := by
  ext i
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map,
    unslashedActiveBalances, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq, Prod.exists, voters, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨v, ⟨index, balance, ⟨validator, j, inZip, active, rfl, rfl⟩, rfl⟩, rfl⟩
    have found := List.mem_zipIdx_iff_getElem?.mp inZip
    have lt : j < state.validators.data.size := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    rw [toNat_toUInt64_of_lt within lt]
    exact ⟨lt, by simpa [counts, ← Array.getElem?_toList, found] using active⟩
  · rintro ⟨lt, active⟩
    cases found : state.validators.data[i]? with
    | none => simp [counts, found] at active
    | some validator =>
      refine ⟨i.toUInt64, ⟨i.toUInt64, validator.effectiveBalance, ?_, rfl⟩,
        toNat_toUInt64_of_lt within lt⟩
      refine ⟨validator, i, ?_, ?_, rfl, rfl⟩
      · exact List.mem_zipIdx_iff_getElem?.mpr (by simpa using found)
      · simpa [counts, found] using active

/-- Reindexing the tally preserves the stake of every selected set of validators. -/
private theorem tally_stake {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (P : ValidatorIndex → Prop) [DecidablePred P] :
    Models.stake (balanceAt state) {i ∈ voters state | P i.toUInt64} =
      Models.stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | P v} := by
  rw [← tally_indices within]
  have selected :
      {i ∈ ((unslashedActiveBalances state).map (·.1)).toFinset.image UInt64.toNat |
        P i.toUInt64} =
      ({v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | P v}).image
        UInt64.toNat := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨v, member, rfl⟩, passes⟩
      exact ⟨v, ⟨member, by simpa using passes⟩, rfl⟩
    · rintro ⟨v, ⟨member, passes⟩, rfl⟩
      exact ⟨⟨v, member, rfl⟩, by simpa using passes⟩
  rw [selected, Models.stake, Finset.sum_image]
  · rfl
  · intro a _ b _ eq
    exact UInt64.toNat_inj.mp eq

/-- A viable block not covered by justification has its parent at or above justification. -/
private theorem justified_below_parent (lower : store.ParentsBelow)
    (before : fork < .glamsterdam)
    {nodes : List ForkChoiceNode} {root : Root} {block parent : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (parentKnown : store.blocks[block.parentRoot]? = some parent)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    (uncovered : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ ≠ .ok true) :
    ∃ justified, store.blocks[store.justifiedCheckpoint.root]? = some justified ∧
      justified.slot ≤ parent.slot := by
  have treeWalk : store.filterNodeTree config ⟨store.justifiedCheckpoint.root, .pending⟩ =
      .ok nodes := tree
  obtain ⟨justified, justifiedKnown⟩ := (filterNodeTree_mem treeWalk _
    (filterNodeTree_self treeWalk (by intro empty; simp [empty] at viable))).2.1
  refine ⟨justified, justifiedKnown, ?_⟩
  have ancestor := (filterNodeTree_ancestor (lower := lower) before treeWalk _ viable).1
  rcases ancestor.eq_or_parent with same | above
  · have same := Option.some.inj same
    change store.justifiedCheckpoint.root = root at same
    apply False.elim
    apply uncovered
    simpa only [same] using isAncestor_self (node := ⟨root, .pending⟩) known
  · rw [blockTree_parent_of known] at above
    have le := above.height_le
    rw [blockTree_height_of justifiedKnown, blockTree_height_of parentKnown] at le
    exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- An honest duty majority in the justified state puts a viable block on the head chain.

Twice the honest duty stake exceeds the active, unslashed stake plus proposer boost.

The successful head walk supplies the attestation-score read at the block's visited parent. -/
theorem isAncestor_getHead_of_duty_support
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode}
    {root : Root} {head : ForkChoiceNode} {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] (duty : ValidatorIndex → Prop) [DecidablePred duty]
    (within : state.RegistryWithinLimit) (lower : store.ParentsBelow)
    (before : fork < .glamsterdam)
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    {block parent : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (parentKnown : store.blocks[block.parentRoot]? = some parent)
    (parentAbove : store.isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    (supported : ∀ v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset,
      v ∈ J → duty v → v ∈ store.supportersOf state ⟨root, .pending⟩)
    (majority : Models.stake (fun v => balanceAt state v.toNat)
        ((unslashedActiveBalances state).map (·.1)).toFinset + store.boostScore config <
      2 * Models.stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧ duty v})
    (headOk : store.getHead config = .ok head) :
    store.isAncestor head ⟨root, .pending⟩ = .ok true := by
  classical
  by_cases covered : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ = .ok true
  · have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    have walk := headOk
    simp only [getHead, notGloas, false_and, ↓reduceIte, bind_ok_iff] at walk
    obtain ⟨nodes', _, walk⟩ := walk
    exact getHeadFrom_descends before rfl covered walk
  obtain ⟨justified, justifiedKnown, below⟩ := justified_below_parent lower before known
    parentKnown tree viable covered
  obtain ⟨score, scoreOk⟩ := getAttestationScore_ok_of_getHead before known parentKnown
    justifiedKnown below stateOk tree viable parentAbove headOk
  have total := tally_stake within (fun _ => True)
  simp only [Finset.filter_true] at total
  have counted : Models.stake (fun v => balanceAt state v.toNat)
      {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧ duty v} ≤
      score.toNat := by
    rw [← stake_supportersOf within scoreOk]
    apply Models.stake_mono
    intro v member
    obtain ⟨inside, honest, dutied⟩ := Finset.mem_filter.mp member
    exact supported v inside honest dutied
  apply isAncestor_getHead_of_majority_withBoost lower before stateOk tree viable scoreOk
    ?_ headOk
  rw [total]
  omega

/-- In a forward store, no counted vote supports a held block at the current slot.

Each counted vote is a latest vote, whose attestation is for a block at its slot or before.

That slot is before the current slot.

A vote counts only through a descendant of the block, which is at the block's slot or later. -/
theorem voteCountsFor_eq_false_of_slot_eq_current
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    {current : Slot} {root : Root} {block : BeaconBlock preset fork}
    (slotOk : store.getCurrentSlot config = .ok current)
    (found : store.blocks[root]? = some block) (atCurrent : block.slot = current)
    (index : ValidatorIndex) :
    store.voteCountsFor ⟨root, .pending⟩ index = false := by
  cases counts : store.voteCountsFor ⟨root, .pending⟩ index with
  | false => rfl
  | true =>
    obtain ⟨message, supported, latest, -, supportedOk, descends⟩ :=
      store.exists_of_voteCountsFor counts
    obtain ⟨attestation, rfl, origin⟩ := forward.votesHaveOrigins latest
    -- The vote's block is a descendant of the block, so at the current slot or later.
    obtain ⟨supportedBlock, supportedFound, above⟩ := slot_le_of_isAncestor found descends
    rw [getSupportedNode_root supportedOk] at supportedFound
    -- The vote's block is at the vote's slot or before, which is before the current slot.
    obtain ⟨votedBlock, votedFound, votedLe⟩ := origin.voted
    obtain ⟨current', currentOk, past⟩ := origin.past
    rw [slotOk, Except.ok.injEq] at currentOk
    subst current'
    have same : supportedBlock = votedBlock :=
      Option.some.inj (supportedFound.symm.trans votedFound)
    subst same
    exact absurd (UInt64.lt_of_le_of_lt above (UInt64.lt_of_le_of_lt votedLe past))
      (atCurrent ▸ UInt64.lt_irrefl _)

/-- In a forward store, a held block at the current slot is not one-confirmed.

This holds under the tally of any balance source. -/
theorem not_isOneConfirmed_of_slot_eq_current
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    {current : Slot} {root head : Root} {block : BeaconBlock preset fork}
    {source : BeaconState preset fork}
    (slotOk : store.getCurrentSlot config = .ok current)
    (found : store.blocks[root]? = some block) (atCurrent : block.slot = current) :
    store.isOneConfirmed config head source (store.tallyVotes source) root ≠ .ok true := by
  intro confirmed
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    isOneConfirmed_eq_ok_true_iff.mp confirmed
  have above := threshold_lt_of_isOneConfirmed supportOk thresholdOk confirmed
  -- The support is the sum of the balances whose vote counts, and none counts.
  have zero : support.toNat = 0 := by
    rw [store.getAttestationScore_toNat_eq_sum supportOk]
    simp [voteCountsFor_eq_false_of_slot_eq_current forward slotOk found atCurrent]
  omega

end Store

end EthLib.Consensus
