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
      store.VoteOrigin config v attestation ∧ block.slot ≤ attestation.data.slot :=
  -- A supporter of a block votes for a node that descends from it.
  --
  -- That node is a known block, from the slot of the block or later.
  --
  -- In a store where each latest vote has its origin, that vote comes from an attestation.
  holds.exists_attestation_of_voteCountsFor found
    (store.voteCountsFor_of_mem_supportersOf supporter)

/-- The vote of each supporter of a known block is from a slot of a range of slots.

Each latest vote of the store must come from an attestation, with the facts behind it. -/
theorem VotesHaveOrigins.slot_mem_range_of_mem_supportersOf (holds : store.VotesHaveOrigins config)
    {state : BeaconState preset fork} {root : Root} {block : BeaconBlock preset fork}
    {currentSlot startSlot lastSlot : Slot} {v : ValidatorIndex}
    -- The range starts at or before the slot of the block.
    (blockOk : store.block root = .ok block) (startLe : startSlot ≤ block.slot)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    -- It ends at the last slot before the current one.
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (supporter : v ∈ store.supportersOf state ⟨root, .pending⟩) :
    ∃ attestation, store.latestMessages[v]? = some (LatestMessage.ofAttestation attestation) ∧
      store.VoteOrigin config v attestation ∧
      startSlot ≤ attestation.data.slot ∧ attestation.data.slot ≤ lastSlot := by
  have found : store.blocks[root]? = some block := block_ok_iff.mp blockOk
  obtain ⟨attestation, latest, origin, slotLe⟩ :=
    holds.exists_attestation_of_mem_supportersOf (node := ⟨root, .pending⟩) found supporter
  -- Its slot is at or after the slot of the voted block, and before the current slot.
  --
  -- So the slot of the vote lies in the range of the adversary of the block.
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

open Models.ForkChoice in
/-- From Gloas, the stake of selected supporters of a known node is at most its weight over nodes.

The registry of the state must stay within the limit of the preset. -/
private theorem stake_le_weight_of_gloas (lower : store.ParentsBelow) (gloas : .glamsterdam ≤ fork)
    {state : BeaconState preset fork} (within : state.RegistryWithinLimit)
    {nodes : List ForkChoiceNode} {target : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[target.root]? = some block)
    (P : ValidatorIndex → Prop) [DecidablePred P]
    (supported : ∀ v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset, P v →
      v ∈ store.supportersOf state target) :
    Models.stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | P v} ≤
      Models.ForkChoice.weight (voters state) (balanceAt state) (nodeView lower nodes)
        target.toModel := by
  classical
  rw [← tally_stake within P]
  apply Models.stake_mono
  intro i member
  obtain ⟨voter, passes⟩ := Finset.mem_filter.mp member
  rw [← tally_indices within, Finset.mem_image] at voter
  obtain ⟨v, active, rfl⟩ := voter
  have same : v.toNat.toUInt64 = v := UInt64.ofNat_toNat
  rw [same] at passes
  obtain ⟨message, supportedNode, latest, honest, supportedOk, descends⟩ :=
    store.exists_of_voteCountsFor
      (store.voteCountsFor_of_mem_supportersOf (supported v active passes))
  have voterIn : v.toNat ∈ voters state := by
    rw [← tally_indices within]
    exact Finset.mem_image.mpr ⟨v, active, rfl⟩
  refine Finset.mem_filter.mpr ⟨voterIn, supportedNode.toModel, ?_,
    (isAncestor_iff_of_gloas (lower := lower) gloas found descends).mp rfl⟩
  show store.latestNode v.toNat.toUInt64 = _
  rw [same]
  simpa [latestNode, latest, supportedOk, Except.toOption] using honest

/-- An honest duty majority in the justified state puts a viable block on the head chain.

Twice the honest duty stake exceeds the active, unslashed stake plus the boost.

From Gloas, the store must return a current slot strictly after the block's slot. -/
theorem isAncestor_getHead_of_duty_support
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode}
    {root : Root} {head : ForkChoiceNode} {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] (duty : ValidatorIndex → Prop) [DecidablePred duty]
    (within : state.RegistryWithinLimit) (lower : store.ParentsBelow)
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    {block parent : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (early : .glamsterdam ≤ fork →
      ∃ current, store.getCurrentSlot config = .ok current ∧ block.slot < current)
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
  have total := tally_stake within (fun _ => True)
  simp only [Finset.filter_true] at total
  by_cases gloas : .glamsterdam ≤ fork
  · -- From Gloas the walk stays on the path to the block, which no payload decision crosses.
    obtain ⟨current, currentOk, early⟩ := early gloas
    have closed := filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
      fun _ _ _ ok _ mem => isChild_of_mem_getNodeChildren gloas ok mem
    have noDecision : ∀ n ∈ nodes, (nodeTree lower).Ancestor n.toModel
        (⟨root, .pending⟩ : ForkChoiceNode).toModel →
        store.isPreviousSlotPayloadDecision config n = .ok false := by
      intro n nIn above
      obtain ⟨-, ⟨nBlock, nFound⟩, -⟩ := filterNodeTree_mem tree n nIn
      -- The node's block is at or before the block, strictly when the node has a status.
      have heights := above.height_le
      rw [nodeTree_height, nodeTree_height] at heights
      simp only [blockTree_height_of nFound, blockTree_height_of known, ↓reduceIte] at heights
      have slotLt := UInt64.lt_iff_toNat_lt.mp early
      have bound := current.toNat_lt
      have fits : nBlock.slot.toNat + 1 < 2 ^ 64 := by split at heights <;> omega
      obtain ⟨next, add⟩ : ∃ next, addChecked nBlock.slot 1 = .ok next :=
        ⟨_, addChecked_of_lt (by simpa using fits)⟩
      have nextEq := (addChecked_ok_iff.mp add).2
      by_cases pending : n.payloadStatus = .pending
      · simp [isPreviousSlotPayloadDecision, block_ok_iff.mpr nFound, add, pending, currentOk,
          bind, Except.bind, pure, Except.pure, Except.mapError]
      · simp only [pending, ↓reduceIte] at heights
        have notCurrent : next ≠ current := by
          intro eq
          subst eq
          simp only [UInt64.toNat_one] at nextEq
          omega
        simp [isPreviousSlotPayloadDecision, block_ok_iff.mpr nFound, add, currentOk, notCurrent,
          bind, Except.bind, pure, Except.pure, Except.mapError]
    have counted := stake_le_weight_of_gloas lower gloas within known (nodes := nodes)
      (fun v => v ∈ J ∧ duty v) fun v active ⟨honest, dutied⟩ => supported v active honest dutied
    have boosts := boostScoreOfGloas_le_boostScore (store := store) (config := config) gloas
    have notEmpty : ¬ (.glamsterdam ≤ fork ∧ nodes.isEmpty = true) :=
      fun ⟨_, empty⟩ => List.ne_nil_of_mem viable (List.isEmpty_iff.mp empty)
    have headFrom := headOk
    simp only [getHead, tree, notEmpty, ↓reduceIte, bind, Except.bind] at headFrom
    have majority' : Models.stake (balanceAt state) (voters state) +
        store.boostScoreOfGloas config gloas <
      2 * Models.ForkChoice.weight (voters state) (balanceAt state) (nodeView lower nodes)
        (⟨root, .pending⟩ : ForkChoiceNode).toModel := by
      rw [total]
      omega
    exact isAncestor_getHeadFrom_of_sibling_bound
      (start := ⟨store.justifiedCheckpoint.root, .pending⟩) lower gloas tree stateOk viable
      (.refl _) (closed _ viable).1 (fun n nIn _ above => noDecision n nIn above)
      (fun _ _ _ _ _ _ _ cChild dChild toward other =>
        (siblingBound_of_majority lower gloas majority' cChild dChild toward other).imp_left
          fun beats _ => beats)
      headFrom
  have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
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
  -- No vote counts for a block at the current slot, as each vote is from an earlier slot.
  --
  -- The support is the sum of the balances whose vote counts, and none counts.
  have zero : support.toNat = 0 := by
    rw [store.getAttestationScore_toNat_eq_sum supportOk]
    have uncounted : ∀ index, store.voteCountsFor ⟨root, .pending⟩ index = false := fun index =>
      Bool.eq_false_iff.mpr fun counts => UInt64.lt_irrefl _
        (atCurrent ▸ forward.votesHaveOrigins.slot_lt_of_voteCountsFor slotOk found counts)
    simp [uncounted]
  omega

end Store

end EthLib.Consensus
