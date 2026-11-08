module

public import EthLib.Consensus.Proofs.ForkChoice.Ghost
public import EthLib.Consensus.Proofs.ForkChoice.Handlers
public import EthLib.Consensus.Proofs.Transition.Slot

/-!
# Proofs: the stores that the handlers reach

A store is reachable when the handlers build it from an anchor.

The handlers are the tick, the block, the attestation and the attester slashing.

From Gloas they also take a vote of the payload committee and a signed envelope.

From Heze they also take an inclusion list.

In a reachable store, each known parent sits at an earlier slot than its child.

That needs two conditions.

The anchor block must sit at or before the slot of the anchor state.

The state after a valid block sits at the slot of the block, so a genuine anchor meets that.

The parent root of the anchor must name no known block.

A known block has its own root as its key.

So a block at that root would hash to the parent root of the anchor.

The head of such a store is then the LMD-GHOST head of its filtered tree.

That holds before Gloas, with the proposer boost as one more vote for the boosted block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Models.ForkChoice

variable {preset : Preset} {fork : Fork}

/-- A lookup in a map of roots after an insertion. -/
theorem getElem?_insert_root {α : Type} {m : Std.TreeMap Root α} {k a : Root} {v : α} :
    (m.insert k v)[a]? = if k = a then some v else m[a]? := by
  rw [Std.TreeMap.getElem?_insert]
  simp only [Std.LawfulEqCmp.compare_eq_iff_eq]

namespace Store

/-- The known blocks and their states, as the handlers keep them.

Each state belongs to a known block, at or after the slot of that block.

A known block with an unknown parent has a given parent root, that of the anchor.

Each known parent sits at an earlier slot than its child. -/
structure Linked (store : Store preset fork) (orphanParent : Root) : Prop where
  stateAfter : ∀ (root : Root) (state : BeaconState preset fork),
    store.blockStates[root]? = some state →
      ∃ block, store.blocks[root]? = some block ∧ block.slot ≤ state.slot
  orphan : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
    store.blocks[block.parentRoot]? = none → block.parentRoot = orphanParent
  parentsBelow : store.ParentsBelow

variable {store after : Store preset fork} {orphanParent : Root}

theorem Linked.of_maps (linked : store.Linked orphanParent) (blocks : after.blocks = store.blocks)
    (states : after.blockStates = store.blockStates) : after.Linked orphanParent := by
  obtain ⟨stateAfter, orphan, parentsBelow⟩ := linked
  refine ⟨?_, ?_, ?_⟩ <;> unfold ParentsBelow at * <;> rw [blocks] <;> try rw [states]
  all_goals assumption

/-- A new block keeps the links under three conditions.

The state of its parent must sit at an earlier slot, and its own state at its slot.

Its root must differ from the given parent root. -/
theorem Linked.insert {root : Root} {block : BeaconBlock preset fork}
    {pre state : BeaconState preset fork} (linked : store.Linked orphanParent)
    (new : store.blocks[root]? = none) (notOrphanParent : root ≠ orphanParent)
    (parentState : store.blockStates[block.parentRoot]? = some pre)
    (earlier : pre.slot < block.slot) (atSlot : state.slot = block.slot)
    (blocks : after.blocks = store.blocks.insert root block)
    (states : after.blockStates = store.blockStates.insert root state) :
    after.Linked orphanParent := by
  obtain ⟨parent, parentFound, parentLe⟩ := linked.stateAfter _ _ parentState
  have parentNe : block.parentRoot ≠ root := fun same => by
    rw [same, new] at parentFound
    cases parentFound
  refine ⟨fun r s found => ?_, fun r b found unknown => ?_, fun r b p found parentOf => ?_⟩
  · rw [states, getElem?_insert_root] at found
    rw [blocks, getElem?_insert_root]
    by_cases same : root = r
    · simp only [same, ↓reduceIte, Option.some.injEq] at found ⊢
      exact ⟨block, rfl, found ▸ atSlot ▸ UInt64.le_refl _⟩
    · simp only [same, ↓reduceIte] at found ⊢
      exact linked.stateAfter r s found
  · rw [blocks, getElem?_insert_root] at found unknown
    by_cases same : root = r
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      subst found
      simp only [Ne.symm parentNe, ↓reduceIte, parentFound] at unknown
      cases unknown
    · simp only [same, ↓reduceIte] at found
      by_cases hits : root = b.parentRoot
      · simp [hits] at unknown
      · simp only [hits, ↓reduceIte] at unknown
        exact linked.orphan r b found unknown
  · rw [blocks, getElem?_insert_root] at found parentOf
    by_cases same : root = r
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      subst found
      simp only [Ne.symm parentNe, ↓reduceIte, parentFound, Option.some.injEq] at parentOf
      subst parentOf
      exact UInt64.lt_of_le_of_lt parentLe earlier
    · simp only [same, ↓reduceIte] at found
      by_cases hits : root = b.parentRoot
      · have orphaned := linked.orphan r b found (hits ▸ new)
        exact absurd (hits.trans orphaned) notOrphanParent
      · simp only [hits, ↓reduceIte] at parentOf
        exact linked.parentsBelow r b p found parentOf

/-- The anchor store is linked, unless the anchor block names its own root as its parent.

That needs the anchor block at or before the slot of the anchor state. -/
theorem linked_getForkchoiceStore {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) :
    store.Linked anchorBlock.parentRoot ∨ store.blocks.contains anchorBlock.parentRoot := by
  obtain ⟨anchorRoot, -, blocks, states⟩ := getForkchoiceStore_maps made
  by_cases self : anchorRoot = anchorBlock.parentRoot
  · right
    rw [blocks, ← self]
    simp
  left
  -- The only known block is the anchor, and its parent is unknown.
  have only : ∀ r b, store.blocks[r]? = some b → r = anchorRoot ∧ b = anchorBlock := by
    intro r b found
    rw [blocks, getElem?_insert_root] at found
    by_cases same : anchorRoot = r
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      exact ⟨same.symm, found.symm⟩
    · simp [same] at found
  have unknown : store.blocks[anchorBlock.parentRoot]? = none := by
    rw [blocks, getElem?_insert_root]
    simp [self]
  refine ⟨fun r s found => ?_, fun r b found _ => ?_, fun r b p found parentOf => ?_⟩
  · rw [states, getElem?_insert_root] at found
    by_cases same : anchorRoot = r
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      refine ⟨anchorBlock, ?_, found ▸ anchorSlot⟩
      rw [blocks, getElem?_insert_root]
      simp [same]
    · simp [same] at found
  · rw [(only r b found).2]
  · rw [(only r b found).2, unknown] at parentOf
    cases parentOf

/-- A block leaves the store as it was, or enters it at its root with the state after it. -/
theorem onBlock_same_or_insert {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (added : store.onBlock config checks sources signed = .ok after) :
    after = store ∨ ∃ blockRoot, SszType.hashTreeRoot signed.message = .ok blockRoot ∧
      store.blocks[blockRoot]? = none ∧
      after.blocks = store.blocks.insert blockRoot signed.message ∧
      ∃ pre state, store.blockStates[signed.message.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signed true = .ok state ∧
        after.blockStates = store.blockStates.insert blockRoot state := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      exact .inl rfl
    · obtain ⟨blocks, rest⟩ := onBlock_insert root known added
      exact .inr ⟨blockRoot, rfl, Std.TreeMap.getElem?_eq_none_of_contains_eq_false
        (Bool.eq_false_iff.mpr known), blocks, rest⟩

/-- A store that the handlers build from an anchor block and the state after it.

The handlers are the tick, the block, the attestation and the attester slashing. -/
inductive Reachable (config : Config) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) : Store preset fork → Prop where
  /-- The store built from the anchor. -/
  | anchor {store : Store preset fork} :
    getForkchoiceStore config anchorState anchorBlock = .ok store →
      Reachable config anchorState anchorBlock store
  /-- The store after a tick. -/
  | tick {store after : Store preset fork} {timeMs : UInt64} :
    Reachable config anchorState anchorBlock store → store.onTick config timeMs = .ok after →
      Reachable config anchorState anchorBlock after
  /-- The store after a signed block. -/
  | block {store after : Store preset fork} {checks : SignatureChecks}
      {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork} :
    Reachable config anchorState anchorBlock store →
      store.onBlock config checks sources signed = .ok after →
      Reachable config anchorState anchorBlock after
  /-- The store after an attestation, from the wire or from a block. -/
  | attestation {store after : Store preset fork} {checks : SignatureChecks}
      {attestation : Attestation preset fork} {isFromBlock : Bool} :
    Reachable config anchorState anchorBlock store →
      store.onAttestation config checks attestation isFromBlock = .ok after →
      Reachable config anchorState anchorBlock after
  /-- The store after an attester slashing. -/
  | attesterSlashing {store after : Store preset fork} {checks : SignatureChecks}
      {slashing : AttesterSlashing preset fork} :
    Reachable config anchorState anchorBlock store →
      store.onAttesterSlashing config checks slashing = .ok after →
      Reachable config anchorState anchorBlock after
  /-- From Gloas, the store after a vote of a member of the payload committee. -/
  | payloadAttestation {store after : Store preset fork} {checks : SignatureChecks}
      {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool} :
    Reachable config anchorState anchorBlock store →
      store.onPayloadAttestationMessage config checks gloas message isFromBlock = .ok after →
      Reachable config anchorState anchorBlock after
  /-- From Gloas, the store after a signed envelope. -/
  | envelope {store after : Store preset fork} {checks : SignatureChecks}
      {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
      {signed : SignedExecutionPayloadEnvelope preset fork} :
    Reachable config anchorState anchorBlock store →
      store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after →
      Reachable config anchorState anchorBlock after
  /-- From Heze, the store after an inclusion list. -/
  | inclusionList {store after : Store preset fork} {checks : SignatureChecks}
      {heze : .hegota ≤ fork} {signed : SignedInclusionList} :
    Reachable config anchorState anchorBlock store →
      store.onInclusionList config checks heze signed = .ok after →
      Reachable config anchorState anchorBlock after

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork}

/-- A block with the votes that it carries leads from a reachable store to a reachable store. -/
theorem Reachable.onBlockWithVotes {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock store)
    (added : store.onBlockWithVotes config checks sources signed = .ok after) :
    Reachable config anchorState anchorBlock after := by
  unfold Store.onBlockWithVotes at added
  simp only [bind_ok_iff, ← Array.foldlM_toList] at added
  obtain ⟨blocked, block, voted, attested, slashed⟩ := added
  have votes := foldlM_ok_invariant (Reachable config anchorState anchorBlock)
    (fun _ _ _ reached step => reached.attestation step) (reachable.block block) attested
  exact foldlM_ok_invariant (Reachable config anchorState anchorBlock)
    (fun _ _ _ reached step => reached.attesterSlashing step) votes slashed

/-- Each known block of a reachable store has its own root as its key. -/
theorem Reachable.root (reachable : Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    SszType.hashTreeRoot block = .ok root := by
  induction reachable generalizing root block with
  | anchor made =>
    obtain ⟨anchorRoot, hashed, blocks, -⟩ := getForkchoiceStore_maps made
    rw [blocks, getElem?_insert_root] at found
    by_cases same : anchorRoot = root
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      rw [← found, ← same, hashed]
    · simp [same] at found
  | tick _ ticked holds => exact holds ((onTick_frame ticked).2.2.1 ▸ found)
  | attestation _ attested holds => exact holds ((onAttestation_frame attested).2.1 ▸ found)
  | attesterSlashing _ slashed holds => exact holds ((onAttesterSlashing_frame slashed).2.1 ▸ found)
  | payloadAttestation _ voted holds =>
    exact holds ((onPayloadAttestationMessage_onlyPtcVotes voted).frame.2.1 ▸ found)
  | envelope _ accepted holds =>
    exact holds ((onExecutionPayloadEnvelope_frame accepted).2.1 ▸ found)
  | inclusionList _ accepted holds => exact holds ((onInclusionList_frame accepted).2.1 ▸ found)
  | @block before _ checks sources signed _ added holds =>
    rcases onBlock_same_or_insert added with same | ⟨blockRoot, hashed, -, blocks, -⟩
    · exact holds (same ▸ found)
    rw [blocks, getElem?_insert_root] at found
    by_cases same : blockRoot = root
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      rw [← found, ← same, hashed]
    · simp only [same, ↓reduceIte] at found
      exact holds found

/-- A reachable store is linked under the parent root of the anchor, unless it knows that root.

That needs the anchor block at or before the slot of the anchor state. -/
theorem Reachable.linked (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) :
    store.Linked anchorBlock.parentRoot ∨ store.blocks.contains anchorBlock.parentRoot := by
  induction reachable with
  | anchor made => exact linked_getForkchoiceStore made anchorSlot
  | tick _ ticked holds =>
    obtain ⟨-, -, blocks, states⟩ := onTick_frame ticked
    exact holds.imp (·.of_maps blocks states) (blocks ▸ ·)
  | attestation _ attested holds =>
    obtain ⟨-, blocks, states⟩ := onAttestation_frame attested
    exact holds.imp (·.of_maps blocks states) (blocks ▸ ·)
  | attesterSlashing _ slashed holds =>
    obtain ⟨-, blocks, states⟩ := onAttesterSlashing_frame slashed
    exact holds.imp (·.of_maps blocks states) (blocks ▸ ·)
  | payloadAttestation _ voted holds =>
    obtain ⟨-, blocks, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    exact holds.imp (·.of_maps blocks states) (blocks ▸ ·)
  | envelope _ accepted holds =>
    obtain ⟨-, blocks, states⟩ := onExecutionPayloadEnvelope_frame accepted
    exact holds.imp (·.of_maps blocks states) (blocks ▸ ·)
  | inclusionList _ accepted holds =>
    obtain ⟨-, blocks, states⟩ := onInclusionList_frame accepted
    exact holds.imp (·.of_maps blocks states) (blocks ▸ ·)
  | @block before after checks sources signed _ added holds =>
    rcases onBlock_same_or_insert added with same | ⟨blockRoot, -, new, blocks, inserted⟩
    · exact same ▸ holds
    obtain ⟨pre, state, parentState, transition, states⟩ := inserted
    have contains : ∀ root, before.blocks.contains root → after.blocks.contains root := by
      intro root known
      rw [blocks, Std.TreeMap.contains_insert]
      exact Bool.or_eq_true_iff.mpr (.inr known)
    rcases holds with linked | known
    · by_cases hits : blockRoot = anchorBlock.parentRoot
      · right
        rw [blocks, ← hits]
        simp
      · obtain ⟨earlier, atSlot⟩ := stateTransition_slot transition
        exact .inl (linked.insert new hits parentState earlier atSlot blocks states)
    · exact .inr (contains _ known)

/-- In a reachable store, each known parent sits at an earlier slot than its child.

That needs the anchor block at or before the slot of the anchor state.

It also needs the parent root of the anchor to name no known block. -/
theorem Reachable.parentsBelow (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none) : store.ParentsBelow := by
  rcases reachable.linked anchorSlot with linked | known
  · exact linked.parentsBelow
  · rw [Std.TreeMap.contains_eq_isSome_getElem?, unknown] at known
    cases known

/-- The facts that keep orphans low in a store that the handlers build.

Each state belongs to a known block, at or after the slot of that block.

A known block with an unknown parent sits at or below every known block. -/
private structure OrphansLow (store : Store preset fork) : Prop where
  stateAfter : ∀ (root : Root) (state : BeaconState preset fork),
    store.blockStates[root]? = some state →
      ∃ block, store.blocks[root]? = some block ∧ block.slot ≤ state.slot
  orphansLe : ∀ (root other : Root) (block otherBlock : BeaconBlock preset fork),
    store.blocks[root]? = some block → store.blocks[block.parentRoot]? = none →
    store.blocks[other]? = some otherBlock → block.slot ≤ otherBlock.slot

/-- A store with the same blocks and states keeps the facts. -/
private theorem OrphansLow.of_maps {store after : Store preset fork} (low : OrphansLow store)
    (blocks : after.blocks = store.blocks) (states : after.blockStates = store.blockStates) :
    OrphansLow after := by
  obtain ⟨stateAfter, orphansLe⟩ := low
  refine ⟨fun r s found => ?_, fun r o b ob found unknown otherFound => ?_⟩
  · rw [states] at found
    rw [blocks]
    exact stateAfter r s found
  · rw [blocks] at found unknown otherFound
    exact orphansLe r o b ob found unknown otherFound

/-- A reachable store keeps the facts.

That needs the anchor block at or before the slot of the anchor state. -/
private theorem Reachable.orphansLow (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) : OrphansLow store := by
  induction reachable with
  | @anchor st made =>
    obtain ⟨anchorRoot, -, blocks, states⟩ := getForkchoiceStore_maps made
    have only : ∀ (r : Root) (b : BeaconBlock preset fork), st.blocks[r]? = some b →
        b = anchorBlock := by
      intro r b found
      rw [blocks, getElem?_insert_root] at found
      by_cases same : anchorRoot = r
      · simp only [same, ↓reduceIte, Option.some.injEq] at found
        exact found.symm
      · simp [same] at found
    refine ⟨fun r s found => ?_, fun r o b ob found _ otherFound => ?_⟩
    · rw [states, getElem?_insert_root] at found
      by_cases same : anchorRoot = r
      · simp only [same, ↓reduceIte, Option.some.injEq] at found
        refine ⟨anchorBlock, ?_, found ▸ anchorSlot⟩
        rw [blocks, getElem?_insert_root]
        simp [same]
      · simp [same] at found
    · rw [only r b found, only o ob otherFound]
      exact UInt64.le_refl _
  | tick _ ticked holds =>
    obtain ⟨-, -, blocks, states⟩ := onTick_frame ticked
    exact holds.of_maps blocks states
  | attestation _ attested holds =>
    obtain ⟨-, blocks, states⟩ := onAttestation_frame attested
    exact holds.of_maps blocks states
  | attesterSlashing _ slashed holds =>
    obtain ⟨-, blocks, states⟩ := onAttesterSlashing_frame slashed
    exact holds.of_maps blocks states
  | payloadAttestation _ voted holds =>
    obtain ⟨-, blocks, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    exact holds.of_maps blocks states
  | envelope _ accepted holds =>
    obtain ⟨-, blocks, states⟩ := onExecutionPayloadEnvelope_frame accepted
    exact holds.of_maps blocks states
  | inclusionList _ accepted holds =>
    obtain ⟨-, blocks, states⟩ := onInclusionList_frame accepted
    exact holds.of_maps blocks states
  | @block before after checks sources signed _ added holds =>
    rcases onBlock_same_or_insert added with same | ⟨blockRoot, -, new, blocks, inserted⟩
    · exact same ▸ holds
    obtain ⟨pre, state, parentState, transition, states⟩ := inserted
    obtain ⟨parent, parentFound, parentLe⟩ := holds.stateAfter _ _ parentState
    obtain ⟨earlier, atSlot⟩ := stateTransition_slot transition
    have parentNe : signed.message.parentRoot ≠ blockRoot := fun same => by
      rw [same, new] at parentFound
      cases parentFound
    have parentBelow := UInt64.lt_of_le_of_lt parentLe earlier
    refine ⟨fun r s found => ?_, fun r o b ob found unknown otherFound => ?_⟩
    · rw [states, getElem?_insert_root] at found
      rw [blocks, getElem?_insert_root]
      by_cases same : blockRoot = r
      · simp only [same, ↓reduceIte, Option.some.injEq] at found ⊢
        exact ⟨signed.message, rfl, found ▸ atSlot ▸ UInt64.le_refl _⟩
      · simp only [same, ↓reduceIte] at found ⊢
        exact holds.stateAfter r s found
    · rw [blocks, getElem?_insert_root] at found unknown otherFound
      by_cases same : blockRoot = r
      · simp only [same, ↓reduceIte, Option.some.injEq] at found
        subst found
        simp only [Ne.symm parentNe, ↓reduceIte, parentFound] at unknown
        cases unknown
      · simp only [same, ↓reduceIte] at found
        by_cases hits : blockRoot = b.parentRoot
        · simp [hits] at unknown
        · simp only [hits, ↓reduceIte] at unknown
          have base := fun (o' : Root) (ob' : BeaconBlock preset fork) =>
            holds.orphansLe r o' b ob' found unknown
          by_cases same' : blockRoot = o
          · simp only [same', ↓reduceIte, Option.some.injEq] at otherFound
            subst otherFound
            exact UInt64.le_trans (base _ parent parentFound) (UInt64.le_iff_toNat_le.mpr
              (by have := UInt64.lt_iff_toNat_lt.mp parentBelow; omega))
          · simp only [same', ↓reduceIte] at otherFound
            exact base _ _ otherFound

/-- In a reachable store, a known block whose parent is unknown sits at or below every known block.

Each block that a handler adds has a known parent at an earlier slot.

That needs the anchor block at or before the slot of the anchor state. -/
theorem Reachable.orphans_le (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) {root other : Root}
    {block otherBlock : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block) (orphan : store.blocks[block.parentRoot]? = none)
    (otherFound : store.blocks[other]? = some otherBlock) : block.slot ≤ otherBlock.slot :=
  (reachable.orphansLow anchorSlot).orphansLe root other block otherBlock found orphan otherFound

/-- Before Gloas and without a boost, the head of a reachable store is the head of LMD-GHOST.

That needs the anchor block at or before the slot of the anchor state.

It also needs the parent root of the anchor to name no known block.

The model starts at the justified block, over the view of the viable nodes. -/
theorem Reachable.getHead_eq_ghost {state : BeaconState preset fork}
    {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (before : fork < .glamsterdam) (noBoost : store.proposerBoostRoot = Vector.replicate 32 0)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (found : store.getHead config = .ok head) :
    ghost (voters state) (balanceAt state) (view (reachable.parentsBelow anchorSlot unknown) nodes)
      rootValue (some store.justifiedCheckpoint.root) = some head.root :=
  Store.getHead_eq_ghost _ before noBoost justifiedState tree found

/-- Before Gloas, the head of a reachable store is the head of LMD-GHOST with the boost.

That needs the anchor block at or before the slot of the anchor state.

It also needs the parent root of the anchor to name no known block.

The model starts at the justified block, over the view of the viable nodes.

The boost is one more vote, for the boosted block, and its stake is the score of the boost. -/
theorem Reachable.getHead_eq_ghost_withBoost {state : BeaconState preset fork}
    {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none) (before : fork < .glamsterdam)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (found : store.getHead config = .ok head) :
    ghost (voters state).insertNone (boostStake (balanceAt state) (store.boostScore config))
      ((view (reachable.parentsBelow anchorSlot unknown) nodes).withBoost store.boostedRoot)
      rootValue (some store.justifiedCheckpoint.root) = some head.root :=
  Store.getHead_eq_ghost_withBoost _ before justifiedState tree found

end Store

end EthLib.Consensus
