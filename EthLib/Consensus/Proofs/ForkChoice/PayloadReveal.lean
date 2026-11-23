module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: a timely payload is extended by the next head

From Gloas a builder reveals its payload after its block.

The payload committee of the slot votes on whether the payload came on time.

It also votes on whether the blob data of the payload is available.

At the next slot, the walk of the fork choice chooses between the empty and the full node.

Both nodes weigh nothing in that slot, so a tiebreaker decides between them.

The tiebreaker favours the full node when the payload should be extended.

A verified payload is extended when more than half of the committee votes it on time.

More than half must also vote its blob data available.

So a head that goes through the block goes through its full node.

The full node must lead to a viable leaf, or the walk cannot take it.

The theorems hold for a store whose known blocks sit later than their parents.

A store that the handlers build is such a store, when its anchor block is not after its state.

The parent of the anchor must also be unknown.

From Heze the payload must also satisfy its inclusion lists.

A payload that is not extended, such as one that fails them, leaves the next head on the empty node.

The source is [EIP-7732](https://eips.ethereum.org/EIPS/eip-7732), fork choice.

For the inclusion lists, it is [EIP-7805](https://eips.ethereum.org/EIPS/eip-7805), fork choice.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

variable {tally : Except ForkChoiceError VoteTally}

/-- A verified payload of the previous slot is extended when it is timely and its data available.

More than half of the committee must vote that it came on time.

More than half must also vote that its blob data is available.

From Heze it must also satisfy its inclusion lists. -/
theorem shouldExtendPayload_of_timely {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot}
    {timelyVotes availableVotes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyFound : (store.payloadTimelinessVote gloas)[root]? = some timelyVotes)
    (timely : ptcThreshold preset < timelyVotes.toList.countP (· == some true))
    (availableFound : (store.payloadDataAvailabilityVote gloas)[root]? = some availableVotes)
    (available : ptcThreshold preset < availableVotes.toList.countP (· == some true)) :
    store.shouldExtendPayload config gloas root = .ok true := by
  have onTime : store.payloadTimeliness gloas root true = .ok true := by
    rw [payloadTimeliness_of_verified timelyFound verified]
    simpa [ptcMajority] using timely
  have present : store.payloadDataAvailability gloas root true = .ok true := by
    rw [payloadDataAvailability_of_verified availableFound verified]
    simpa [ptcMajority] using available
  by_cases heze : .hegota ≤ fork <;>
    simp [shouldExtendPayload, Store.block, found, nextOk, current, verified, heze, onTime,
      present, Except.mapError, bind, Except.bind, pure, Except.pure, satisfied]

/-- From Gloas the walk from a node above the pending node of a block reaches that node.

The end of the walk must descend from that pending node.

When the walk then steps to the full or the empty node, it ends where the walk from that node ends.
-/
private theorem getHeadFrom_decided (lower : store.ParentsBelow) (gloas : .glamsterdam ≤ fork)
    {nodes : List ForkChoiceNode} {root : Root} {status : PayloadStatus} {head : ForkChoiceNode}
    (step : store.heaviestChild config tally nodes ⟨root, .pending⟩ = .ok (some ⟨root, status⟩))
    (rank : store.nodeRank ⟨root, status⟩ < store.nodeRank ⟨root, .pending⟩)
    (below : (nodeTree lower).Ancestor (ForkChoiceNode.toModel ⟨root, .pending⟩)
      head.toModel) :
    ∀ {start : ForkChoiceNode}, store.getHeadFrom config tally nodes start = .ok head →
      (nodeTree lower).Ancestor start.toModel (ForkChoiceNode.toModel ⟨root, .pending⟩) →
      store.getHeadFrom config tally nodes ⟨root, status⟩ = .ok head := by
  intro start walk above
  have walk := getHeadFrom_of_visited lower gloas below walk above
  rw [getHeadFrom, step] at walk
  simpa only [bind, Except.bind, rank, dite_true] using walk

/-- From Gloas the walk takes the full node of a verified block of the previous slot.

The payload must extend, and the full node must be among the given nodes. -/
private theorem heaviestChild_full {gloas : .glamsterdam ≤ fork}
    {nodes : List ForkChoiceNode} {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    (extend : store.shouldExtendPayload config gloas root = .ok true)
    (fullIn : ⟨root, .full⟩ ∈ nodes) :
    store.heaviestChild config tally nodes ⟨root, .pending⟩ = .ok (some ⟨root, .full⟩) := by
  by_cases emptyIn : (⟨root, .empty⟩ : ForkChoiceNode) ∈ nodes
  · simpa using heaviestChild_of_previousSlot found nextOk current verified emptyIn fullIn extend
  have fullDecision := isPreviousSlotPayloadDecision_of_previous (status := .full) found nextOk
    current (by decide)
  have fullWeighed : store.weighNode config tally ⟨root, .full⟩ = .ok (⟨root, .full⟩, 0, 2) :=
    weighNode_ok_iff.mpr ⟨rfl, getWeight_of_payloadDecision gloas fullDecision, by
      simp [tiebreaker, gloas, getPayloadStatusTiebreaker, fullDecision, extend, bind,
        Except.bind, pure, Except.pure]⟩
  unfold heaviestChild
  rw [getNodeChildren_of_pending gloas rfl]
  simp [verified, emptyIn, fullIn, fullWeighed, bind, Except.bind, pure, Except.pure,
    chooseHeaviest]

/-- From Gloas the walk takes the empty node of a block of the previous slot.

The payload must not extend, and the empty node must be among the given nodes. -/
private theorem heaviestChild_empty {gloas : .glamsterdam ≤ fork}
    {nodes : List ForkChoiceNode} {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (extend : store.shouldExtendPayload config gloas root = .ok false)
    (emptyIn : ⟨root, .empty⟩ ∈ nodes) :
    store.heaviestChild config tally nodes ⟨root, .pending⟩ = .ok (some ⟨root, .empty⟩) := by
  by_cases both : store.isPayloadVerified gloas root = true ∧ ⟨root, .full⟩ ∈ nodes
  · simpa using heaviestChild_of_previousSlot found nextOk current both.1 emptyIn both.2 extend
  -- Otherwise the empty node is the only child left to weigh.
  have emptyDecision := isPreviousSlotPayloadDecision_of_previous (status := .empty) found nextOk
    current (by decide)
  have emptyWeighed : store.weighNode config tally ⟨root, .empty⟩ = .ok (⟨root, .empty⟩, 0, 1) :=
    weighNode_ok_iff.mpr ⟨rfl, getWeight_of_payloadDecision gloas emptyDecision, by
      simp [tiebreaker, gloas, getPayloadStatusTiebreaker, emptyDecision, bind, Except.bind,
        pure, Except.pure]⟩
  have alone : (⟨root, .empty⟩ :: if store.isPayloadVerified gloas root then
      [(⟨root, .full⟩ : ForkChoiceNode)] else []).filter (· ∈ nodes) = [⟨root, .empty⟩] := by
    by_cases verified : store.isPayloadVerified gloas root = true
    · have fullOut : (⟨root, .full⟩ : ForkChoiceNode) ∉ nodes :=
        fun fullIn => both ⟨verified, fullIn⟩
      simp [verified, emptyIn, fullOut]
    · simp [verified, emptyIn]
  unfold heaviestChild
  rw [getNodeChildren_of_pending gloas rfl]
  simp [alone, emptyWeighed, bind, Except.bind, pure, Except.pure, chooseHeaviest]

/-- A head that goes through a block of the previous slot goes through its full node.

The payload of the block must be verified and extended.

Its full node must be among the viable nodes.

Each known block must sit at a later slot than its known parent. -/
theorem isAncestor_full_getHead_of_shouldExtendPayload (lower : store.ParentsBelow)
    {gloas : .glamsterdam ≤ fork} {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    (extend : store.shouldExtendPayload config gloas root = .ok true)
    (tree : store.getFilteredNodeTree config = .ok nodes) (fullIn : ⟨root, .full⟩ ∈ nodes)
    (headOk : store.getHead config = .ok head)
    (through : store.isAncestor head ⟨root, .pending⟩ = .ok true) :
    store.isAncestor head ⟨root, .full⟩ = .ok true := by
  unfold getHead at headOk
  simp only [tree, bind, Except.bind] at headOk
  have notEmpty : ¬(.glamsterdam ≤ fork ∧ nodes.isEmpty) :=
    fun empty => by simp [List.isEmpty_iff.mp empty.2] at fullIn
  simp only [notEmpty, ↓reduceIte] at headOk
  have below := (isAncestor_iff_of_gloas (lower := lower) (node := ⟨root, .pending⟩) gloas found
    through).mp rfl
  -- The justified block sits above the full node, so above its pending node.
  have closed := filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
    (fun _ _ _ childrenOk _ nMem => isChild_of_mem_getNodeChildren gloas childrenOk nMem)
  have above : (nodeTree lower).Ancestor
      (ForkChoiceNode.toModel ⟨store.justifiedCheckpoint.root, .pending⟩)
      (ForkChoiceNode.toModel ⟨root, .pending⟩) := by
    rcases ((closed _ fullIn).1).eq_or_parent with eq | par
    · cases ForkChoiceNode.toModel_injective eq
    · exact par
  have rank : store.nodeRank ⟨root, .full⟩ < store.nodeRank ⟨root, .pending⟩ := by
    simp [nodeRank, found]
  have walk := getHeadFrom_decided lower gloas
    (heaviestChild_full found nextOk current verified extend fullIn) rank below headOk above
  exact isAncestor_getHeadFrom_of_gloas gloas walk found

/-- A head that goes through a block of the previous slot goes through its empty node.

The payload of the block must not be extended.

Its empty node must be among the viable nodes.

Then the head does not go through the full node of the block.

From two slots after the block, the votes weigh both nodes, and this no longer holds.

Each known block must sit at a later slot than its known parent. -/
theorem isAncestor_empty_getHead_of_not_shouldExtendPayload (lower : store.ParentsBelow)
    {gloas : .glamsterdam ≤ fork} {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (extend : store.shouldExtendPayload config gloas root = .ok false)
    (tree : store.getFilteredNodeTree config = .ok nodes) (emptyIn : ⟨root, .empty⟩ ∈ nodes)
    (headOk : store.getHead config = .ok head)
    (through : store.isAncestor head ⟨root, .pending⟩ = .ok true) :
    store.isAncestor head ⟨root, .empty⟩ = .ok true ∧
      store.isAncestor head ⟨root, .full⟩ = .ok false := by
  have known : store.block root = .ok block := block_ok_iff.mpr found
  have empty : store.isAncestor head ⟨root, .empty⟩ = .ok true := by
    unfold getHead at headOk
    simp only [tree, bind, Except.bind] at headOk
    have notEmpty : ¬(.glamsterdam ≤ fork ∧ nodes.isEmpty) :=
      fun none => by simp [List.isEmpty_iff.mp none.2] at emptyIn
    simp only [notEmpty, ↓reduceIte] at headOk
    have below := (isAncestor_iff_of_gloas (lower := lower) (node := ⟨root, .pending⟩) gloas
      found through).mp rfl
    -- The justified block sits above the empty node, so above its pending node.
    have closed := filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
      (fun _ _ _ childrenOk _ nMem => isChild_of_mem_getNodeChildren gloas childrenOk nMem)
    have above : (nodeTree lower).Ancestor
        (ForkChoiceNode.toModel ⟨store.justifiedCheckpoint.root, .pending⟩)
        (ForkChoiceNode.toModel ⟨root, .pending⟩) := by
      rcases ((closed _ emptyIn).1).eq_or_parent with eq | par
      · cases ForkChoiceNode.toModel_injective eq
      · exact par
    have rank : store.nodeRank ⟨root, .empty⟩ < store.nodeRank ⟨root, .pending⟩ := by
      simp [nodeRank, found]
    have walk := getHeadFrom_decided lower gloas
      (heaviestChild_empty found nextOk current extend emptyIn) rank below headOk above
    exact isAncestor_getHeadFrom_of_gloas gloas walk found
  refine ⟨empty, ?_⟩
  -- Both checks read the same ancestor of the head, which is the empty node.
  simp only [isAncestor, known, gloas, ↓reduceIte, bind, Except.bind] at empty ⊢
  cases walk : store.getAncestor head block.slot with
  | error e => simp [walk] at empty
  | ok ancestor =>
    simp only [walk, pure, Except.pure, Except.ok.injEq] at empty ⊢
    cases status : ancestor.payloadStatus <;> simp_all

/-- From Heze, the next head never goes through the full node of a payload that fails its lists.

Take a block of the previous slot whose payload the store does not count as satisfying its lists.

A payload that the store has not verified counts as failing them.

Its empty node is among the viable nodes, and the head goes through the block.

Then the head goes through the empty node of the block, and not through its full node.

From two slots after the block, the votes weigh both nodes, and this no longer holds.

Each known block must sit at a later slot than its known parent. -/
theorem isAncestor_empty_getHead_of_not_satisfied (lower : store.ParentsBelow)
    (heze : .hegota ≤ fork) {nodes : List ForkChoiceNode} {head : ForkChoiceNode} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (unsatisfied : store.isPayloadInclusionListSatisfied heze root = .ok false)
    (tree : store.getFilteredNodeTree config = .ok nodes) (emptyIn : ⟨root, .empty⟩ ∈ nodes)
    (headOk : store.getHead config = .ok head)
    (through : store.isAncestor head ⟨root, .pending⟩ = .ok true) :
    store.isAncestor head ⟨root, .empty⟩ = .ok true ∧
      store.isAncestor head ⟨root, .full⟩ = .ok false :=
  isAncestor_empty_getHead_of_not_shouldExtendPayload (gloas := Nat.le_trans (by decide) heze)
    lower found nextOk current
    (shouldExtendPayload_of_not_satisfied heze found nextOk current unsatisfied)
    tree emptyIn headOk through

/-- A timely and available payload is extended by the next head.

Take a block of the previous slot whose payload the store has verified.

More than half of its payload committee voted that the payload came on time.

More than half voted that its blob data is available.

From Heze the payload also satisfied its inclusion lists.

Its full node is among the viable nodes, and the head goes through the block.

Then the head goes through the full node of the block.

Each known block must sit at a later slot than its known parent. -/
theorem isAncestor_full_getHead_of_timely (lower : store.ParentsBelow)
    {gloas : .glamsterdam ≤ fork} {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    {timelyVotes availableVotes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyFound : (store.payloadTimelinessVote gloas)[root]? = some timelyVotes)
    (timely : ptcThreshold preset < timelyVotes.toList.countP (· == some true))
    (availableFound : (store.payloadDataAvailabilityVote gloas)[root]? = some availableVotes)
    (available : ptcThreshold preset < availableVotes.toList.countP (· == some true))
    (tree : store.getFilteredNodeTree config = .ok nodes) (fullIn : ⟨root, .full⟩ ∈ nodes)
    (headOk : store.getHead config = .ok head)
    (through : store.isAncestor head ⟨root, .pending⟩ = .ok true) :
    store.isAncestor head ⟨root, .full⟩ = .ok true :=
  isAncestor_full_getHead_of_shouldExtendPayload lower found nextOk current verified
    (shouldExtendPayload_of_timely found nextOk current verified satisfied timelyFound timely
      availableFound available) tree fullIn headOk through

/-- A timely and available payload is extended by the next head, in a store the handlers build.

That needs the anchor block at or before the slot of the anchor state.

It also needs the parent root of the anchor to name no known block.

The payload, its votes and the head are as in the theorem for any such store above. -/
theorem Reachable.isAncestor_full_getHead_of_timely {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    {gloas : .glamsterdam ≤ fork} {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    {timelyVotes availableVotes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyFound : (store.payloadTimelinessVote gloas)[root]? = some timelyVotes)
    (timely : ptcThreshold preset < timelyVotes.toList.countP (· == some true))
    (availableFound : (store.payloadDataAvailabilityVote gloas)[root]? = some availableVotes)
    (available : ptcThreshold preset < availableVotes.toList.countP (· == some true))
    (tree : store.getFilteredNodeTree config = .ok nodes) (fullIn : ⟨root, .full⟩ ∈ nodes)
    (headOk : store.getHead config = .ok head)
    (through : store.isAncestor head ⟨root, .pending⟩ = .ok true) :
    store.isAncestor head ⟨root, .full⟩ = .ok true :=
  Store.isAncestor_full_getHead_of_timely (reachable.parentsBelow anchorSlot unknown) found nextOk
    current verified satisfied timelyFound timely availableFound available tree fullIn headOk
    through

end Store

end EthLib.Consensus
