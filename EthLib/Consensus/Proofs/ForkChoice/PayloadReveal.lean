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

The source is [EIP-7732](https://eips.ethereum.org/EIPS/eip-7732), fork choice.
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

/-- From Gloas the walk goes down the tree of nodes: its end descends from its start. -/
private theorem ancestor_getHeadFrom (lower : store.ParentsBelow) (gloas : .glamsterdam ≤ fork)
    {nodes : List ForkChoiceNode} {start head : ForkChoiceNode}
    (walk : store.getHeadFrom config tally nodes start = .ok head) :
    (nodeTree lower).Ancestor start.toModel head.toModel := by
  induction start using getHeadFrom.induct store with
  | _ start ih =>
    rw [getHeadFrom] at walk
    cases chosen : store.heaviestChild config tally nodes start with
    | error e => simp [chosen, bind, Except.bind] at walk
    | ok result =>
      cases result with
      | none =>
        simp [chosen, bind, Except.bind, pure, Except.pure] at walk
        subst walk
        exact .refl _
      | some child =>
        simp only [chosen, bind, Except.bind] at walk
        split at walk
        · rename_i lowerRank
          obtain ⟨children, weighted, hc, hw, choice⟩ := heaviestChild_eq chosen
          obtain ⟨key, mem, -⟩ := chooseHeaviest_some choice
          obtain ⟨source, member, pair⟩ := mapM_ok_mem hw _ mem
          have same : source = child := (weighNode_ok_iff.mp pair).1.symm
          subst same
          exact (isChild_of_mem_getNodeChildren gloas hc
            (List.mem_filter.mp member).1).ancestor.trans (ih source lowerRank walk)
        · cases walk

/-- From Gloas the walk from a node above the pending node of a block reaches that node.

The end of the walk must descend from that pending node.

When the walk then steps to the full node, it ends where the walk from the full node ends. -/
private theorem getHeadFrom_full (lower : store.ParentsBelow) (gloas : .glamsterdam ≤ fork)
    {nodes : List ForkChoiceNode} {root : Root} {head : ForkChoiceNode}
    (step : store.heaviestChild config tally nodes ⟨root, .pending⟩ = .ok (some ⟨root, .full⟩))
    (rank : store.nodeRank ⟨root, .full⟩ < store.nodeRank ⟨root, .pending⟩)
    (below : (nodeTree lower).Ancestor (ForkChoiceNode.toModel ⟨root, .pending⟩)
      head.toModel) :
    ∀ {start : ForkChoiceNode}, store.getHeadFrom config tally nodes start = .ok head →
      (nodeTree lower).Ancestor start.toModel (ForkChoiceNode.toModel ⟨root, .pending⟩) →
      store.getHeadFrom config tally nodes ⟨root, .full⟩ = .ok head := by
  intro start
  induction start using getHeadFrom.induct store with
  | _ start ih =>
  intro walk above
  by_cases same : start = ⟨root, .pending⟩
  · subst same
    rw [getHeadFrom, step] at walk
    simpa only [bind, Except.bind, rank, dite_true] using walk
  rw [getHeadFrom] at walk
  cases chosen : store.heaviestChild config tally nodes start with
  | error e => simp [chosen, bind, Except.bind] at walk
  | ok result =>
    cases result with
    | none =>
      simp [chosen, bind, Except.bind, pure, Except.pure] at walk
      subst walk
      exact absurd (ForkChoiceNode.toModel_injective (above.antisymm below)) same
    | some child =>
      simp only [chosen, bind, Except.bind] at walk
      split at walk
      · rename_i lowerRank
        obtain ⟨children, weighted, hc, hw, choice⟩ := heaviestChild_eq chosen
        obtain ⟨key, mem, -⟩ := chooseHeaviest_some choice
        obtain ⟨source, member, pair⟩ := mapM_ok_mem hw _ mem
        have sameChild : source = child := (weighNode_ok_iff.mp pair).1.symm
        subst sameChild
        have childOf := isChild_of_mem_getNodeChildren (lower := lower) gloas hc
          (List.mem_filter.mp member).1
        rcases below.total (ancestor_getHeadFrom lower gloas walk) with down | up
        · rcases down.eq_or_parent with eq | par
          · exact ih source lowerRank walk (eq ▸ .refl _)
          · rw [childOf.2] at par
            exact absurd (ForkChoiceNode.toModel_injective (above.antisymm par)) same
        · exact ih source lowerRank walk up
      · cases walk

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
  have walk := getHeadFrom_full lower gloas
    (heaviestChild_full found nextOk current verified extend fullIn) rank below headOk above
  exact isAncestor_getHeadFrom_of_gloas gloas walk found

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
