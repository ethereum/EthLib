module

public import EthLib.Consensus.Proofs.ForkChoice.ForwardClock
import EthLib.Consensus.Proofs.Containers.Block
import EthLib.Consensus.Proofs.Transition.RunKept

/-!
# Proofs: each block state of a store comes from the state of its parent

A reachable store keeps a state for each known block.

A known anchor block has the anchor state.

Each other block has the state that its transition gives from the state of its parent.

So along a chain of known blocks above the anchor, each state is the transition of the one before.

When every handler runs with one setting of the signature checks, each transition uses it.

A block from the future is refused, and the clock of an honest node only moves forward.

So in a store with a forward clock each block state is at or before the current slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Store

/-- Each known block of a store has a state, the state after that block.

A known anchor block has the anchor state.

That case reads the block, not its root; a reachable store keeps each block at its own root.

Any other block is the message of a signed block whose transition gives that state.

The transition starts from the state of the parent, which the store keeps.

It ran with some execution engine, which may differ between blocks.

It ran with a setting of the signature checks that the given predicate allows.

It checks the state root, and the signature of the proposer under those checks.

Some checks accept every signature, so this says nothing on signatures. -/
def BlockStatesFromParents (config : Config) (allowed : SignatureChecks → Prop)
    (anchorState : BeaconState preset fork) (anchorBlock : BeaconBlock preset fork)
    (store : Store preset fork) : Prop :=
  ∀ ⦃root : Root⦄ ⦃block : BeaconBlock preset fork⦄, store.blocks[root]? = some block →
    ∃ state, store.blockStates[root]? = some state ∧
      (block = anchorBlock → state = anchorState) ∧
      (block ≠ anchorBlock → ∃ parentState checks engine, ∃ signed : SignedBeaconBlock preset fork,
        allowed checks ∧ signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parentState ∧
        stateTransition config checks engine parentState signed true = .ok state)

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- A reachable store knows the anchor block, at its own root. -/
theorem Store.Reachable.anchor_known
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      store.blocks[root]? = some anchorBlock := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, hashed, blocks, -⟩ := getForkchoiceStore_maps made
    exact ⟨anchorRoot, hashed, by rw [blocks, getElem?_insert_root]; simp⟩
  | tick _ ticked ih =>
    obtain ⟨-, -, blocks, -⟩ := Store.onTick_frame ticked
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | @block _ _ _ _ _ _ added ih =>
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, onBlock_blocks_of_found added f⟩
  | attestation _ attested ih =>
    obtain ⟨-, blocks, -⟩ := Store.onAttestation_frame attested
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, -⟩ := Store.onAttesterSlashing_frame slashed
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, -⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := Store.onExecutionPayloadEnvelope_frame accepted
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩
  | inclusionList _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := Store.onInclusionList_frame accepted
    obtain ⟨r, h, f⟩ := ih
    exact ⟨r, h, blocks ▸ f⟩

/-- A handler that keeps the blocks and the block states keeps the states from the parents. -/
private theorem Store.BlockStatesFromParents.of_maps {allowed : SignatureChecks → Prop}
    {after : Store preset fork} (blocks : after.blocks = store.blocks)
    (states : after.blockStates = store.blockStates)
    (holds : store.BlockStatesFromParents config allowed anchorState anchorBlock) :
    after.BlockStatesFromParents config allowed anchorState anchorBlock := by
  intro root block found
  rw [blocks] at found
  rw [states]
  exact holds found

/-- The store built from the anchor has each state from its parent. -/
private theorem Store.BlockStatesFromParents.anchor {allowed : SignatureChecks → Prop}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    store.BlockStatesFromParents config allowed anchorState anchorBlock := by
  obtain ⟨anchorRoot, -, blocks, states⟩ := getForkchoiceStore_maps made
  intro root block found
  rw [blocks, getElem?_insert_root] at found
  rw [states, getElem?_insert_root]
  by_cases same : anchorRoot = root
  · simp only [same, ↓reduceIte, Option.some.injEq] at found
    simp only [same, ↓reduceIte]
    subst found
    exact ⟨_, rfl, fun _ => rfl, fun ne => absurd rfl ne⟩
  · simp [same] at found

/-- A block handled with an allowed setting of the checks keeps the states from the parents. -/
private theorem Store.BlockStatesFromParents.onBlock {allowed : SignatureChecks → Prop}
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {prior after : Store preset fork}
    (ok : allowed checks) (previous : Store.Reachable config anchorState anchorBlock prior)
    (ih : prior.BlockStatesFromParents config allowed anchorState anchorBlock)
    (added : prior.onBlock config checks sources signed = .ok after) :
    after.BlockStatesFromParents config allowed anchorState anchorBlock := by
  rcases Store.onBlock_same_or_insert added with
    same | ⟨blockRoot, hashed, fresh, blocks, pre, state, preFound, transition, states⟩
  · subst same
    exact ih
  have parentNe : ∀ {parentState : BeaconState preset fork} {parentRoot : Root},
      prior.blockStates[parentRoot]? = some parentState → blockRoot ≠ parentRoot := by
    rintro _ _ hasState rfl
    have none := previous.blockState_eq_none fresh
    rw [none] at hasState
    cases hasState
  intro root block found
  rw [blocks, getElem?_insert_root] at found
  rw [states, getElem?_insert_root]
  by_cases same : blockRoot = root
  · simp only [same, ↓reduceIte, Option.some.injEq] at found
    subst found
    simp only [same, ↓reduceIte]
    have notAnchor : signed.message ≠ anchorBlock := by
      intro eq
      obtain ⟨r, h, f⟩ := previous.anchor_known
      rw [← eq, hashed] at h
      cases h
      rw [fresh] at f
      cases f
    refine ⟨state, rfl, fun eq => absurd eq notAnchor,
      fun _ => ⟨pre, _, _, _, ok, rfl, ?_, transition⟩⟩
    rw [getElem?_insert_root]
    simp only [← same, parentNe preFound, ↓reduceIte]
    exact preFound
  · simp only [same, ↓reduceIte] at found ⊢
    obtain ⟨old, oldFound, rest⟩ := ih found
    refine ⟨old, oldFound, rest.1, fun ne => ?_⟩
    obtain ⟨p, c, e, s, hc, hs, hp, ht⟩ := rest.2 ne
    refine ⟨p, c, e, s, hc, hs, ?_, ht⟩
    rw [getElem?_insert_root]
    simp only [parentNe hp, ↓reduceIte]
    exact hp

/-- In a reachable store, each known block has the state after it, from the state of its parent.

A known anchor block has the anchor state instead.

The transitions may run with any setting of the signature checks. -/
theorem Store.Reachable.blockStatesFromParents
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.BlockStatesFromParents config (fun _ => True) anchorState anchorBlock := by
  induction reachable with
  | anchor made => exact .anchor made
  | tick _ ticked ih =>
    obtain ⟨-, -, blocks, states⟩ := Store.onTick_frame ticked
    exact .of_maps blocks states ih
  | block previous added ih => exact .onBlock trivial previous ih added
  | attestation _ attested ih =>
    obtain ⟨-, blocks, states, -⟩ := Store.onAttestation_frame attested
    exact .of_maps blocks states ih
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, states, -⟩ := Store.onAttesterSlashing_frame slashed
    exact .of_maps blocks states ih
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    exact .of_maps blocks states ih
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onExecutionPayloadEnvelope_frame accepted
    exact .of_maps blocks states ih
  | inclusionList _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onInclusionList_frame accepted
    exact .of_maps blocks states ih

/-- In a reachable store, a known block is at or before the slot of its state.

The anchor block must not be after the anchor state. -/
theorem Store.Reachable.slot_le_of_blockState
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block)
    (stateFound : store.blockStates[root]? = some state) : block.slot ≤ state.slot := by
  obtain ⟨kept, keptFound, isAnchor, notAnchor⟩ := reachable.blockStatesFromParents found
  rw [stateFound, Option.some.injEq] at keptFound
  subst keptFound
  by_cases same : block = anchorBlock
  · rw [isAnchor same, same]
    exact anchorSlot
  · obtain ⟨_, _, _, _, -, message, -, transition⟩ := notAnchor same
    rw [(stateTransition_slot transition).2, message]
    exact UInt64.le_refl _

/-- In a store built with one setting of the checks, each block state comes from its parent.

Each transition runs with that setting.

A known anchor block has the anchor state instead. -/
theorem Store.ForwardReachableWith.blockStatesFromParents {checks : SignatureChecks}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store) :
    store.BlockStatesFromParents config (· = checks) anchorState anchorBlock := by
  induction reached with
  | anchor made => exact .anchor made
  | tick _ _ ticked ih =>
    obtain ⟨-, -, blocks, states⟩ := Store.onTick_frame ticked
    exact .of_maps blocks states ih
  | block previous added ih => exact .onBlock rfl previous.reachable ih added
  | attestation _ attested ih =>
    obtain ⟨-, blocks, states, -⟩ := Store.onAttestation_frame attested
    exact .of_maps blocks states ih
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, states, -⟩ := Store.onAttesterSlashing_frame slashed
    exact .of_maps blocks states ih
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    exact .of_maps blocks states ih
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onExecutionPayloadEnvelope_frame accepted
    exact .of_maps blocks states ih
  | inclusionList _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onInclusionList_frame accepted
    exact .of_maps blocks states ih

/-- A handler that changes neither the block states nor the clock keeps their slot bound. -/
private theorem blockStates_le_of_same {after : Store preset fork}
    (states : after.blockStates = store.blockStates) (clock : Store.SameClock store after)
    (holds : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
        ∃ current, store.getCurrentSlot config = .ok current ∧ state.slot ≤ current) :
    ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄, after.blockStates[root]? = some state →
      ∃ current, after.getCurrentSlot config = .ok current ∧ state.slot ≤ current := by
  intro root state found
  rw [states] at found
  rw [clock.getCurrentSlot]
  exact holds found

/-- In a store with a forward clock, each block state is at or before the current slot. -/
theorem Store.ForwardReachable.slot_le_of_blockState_of_getCurrentSlot
    (forward : Store.ForwardReachable config anchorState anchorBlock store) {root : Root}
    {state : BeaconState preset fork} {current : Slot}
    (stateFound : store.blockStates[root]? = some state)
    (slotOk : store.getCurrentSlot config = .ok current) : state.slot ≤ current := by
  suffices holds : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
        ∃ current, store.getCurrentSlot config = .ok current ∧ state.slot ≤ current by
    obtain ⟨other, otherOk, le⟩ := holds stateFound
    rw [slotOk, Except.ok.injEq] at otherOk
    exact otherOk ▸ le
  have positive := Store.slotDuration_pos slotOk
  clear stateFound slotOk
  induction forward with
  | anchor made =>
    -- The only block state is the anchor state, at the current slot.
    intro root state found
    obtain ⟨anchorRoot, -, -, states⟩ := getForkchoiceStore_maps made
    rw [states, getElem?_insert_root] at found
    split at found
    · rw [Option.some.injEq] at found
      subst found
      exact ⟨_, getCurrentSlot_getForkchoiceStore positive made, UInt64.le_refl _⟩
    · simp at found
  | tick previous forward ticked ih =>
    intro root state found
    obtain ⟨-, -, -, states⟩ := Store.onTick_frame ticked
    rw [states] at found
    obtain ⟨current, slotOk, le⟩ := ih found
    obtain ⟨later, laterOk, laterLe⟩ := Store.exists_getCurrentSlot_onTick_ge forward ticked slotOk
    exact ⟨later, laterOk, UInt64.le_trans le laterLe⟩
  | block _ added ih =>
    -- A new block is not from the future, and its state is at its slot.
    rcases Store.onBlock_same_or_insert added with
      same | ⟨blockRoot, hashed, fresh, -, pre, newState, -, transition, states⟩
    · subst same
      exact ih
    intro root state found
    rw [(Store.onBlock_sameClock added).getCurrentSlot]
    rw [states, getElem?_insert_root] at found
    split at found
    · rw [Option.some.injEq] at found
      subst found
      obtain ⟨current, slotOk, le⟩ := (Store.onBlock_checks hashed
        (by simp [Std.TreeMap.contains_eq_isSome_getElem?, fresh]) added).1
      exact ⟨current, slotOk, (stateTransition_slot transition).2 ▸ le⟩
    · exact ih found
  | attestation _ attested ih =>
    exact blockStates_le_of_same (Store.onAttestation_frame attested).2.2.1
      (Store.onAttestation_sameClock attested) ih
  | attesterSlashing _ slashed ih =>
    exact blockStates_le_of_same (Store.onAttesterSlashing_frame slashed).2.2.1
      (Store.onAttesterSlashing_sameClock slashed) ih
  | payloadAttestation _ voted ih =>
    exact blockStates_le_of_same (onPayloadAttestationMessage_onlyPtcVotes voted).frame.2.2
      (Store.onPayloadAttestationMessage_sameClock voted) ih
  | envelope _ accepted ih =>
    exact blockStates_le_of_same (Store.onExecutionPayloadEnvelope_frame accepted).2.2
      (Store.onExecutionPayloadEnvelope_sameClock accepted) ih
  | inclusionList _ accepted ih =>
    exact blockStates_le_of_same (Store.onInclusionList_frame accepted).2.2
      (Store.onInclusionList_sameClock accepted) ih

/-- A forward store has a current slot no earlier than any held block or block state. -/
theorem Store.ForwardReachable.slots_le_current
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot) :
    ∃ current, store.getCurrentSlot config = .ok current ∧
      (∀ (root : Root) (block : BeaconBlock preset fork),
        store.blocks[root]? = some block → block.slot ≤ current) ∧
      (∀ (root : Root) (state : BeaconState preset fork),
        store.blockStates[root]? = some state → state.slot ≤ current) := by
  obtain ⟨current, slotOk⟩ := forward.exists_getCurrentSlot positive
  have states := fun root state found =>
    forward.slot_le_of_blockState_of_getCurrentSlot (root := root) (state := state) found slotOk
  refine ⟨current, slotOk, ?_, states⟩
  intro root block found
  obtain ⟨state, stateFound, -⟩ := forward.reachable.blockStatesFromParents found
  exact UInt64.le_trans
    (forward.reachable.slot_le_of_blockState anchorSlot found stateFound)
    (states root state stateFound)

/-- The anchor state hashes to the state root of its anchor block. -/
theorem Store.Reachable.anchorState_root
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    SszType.hashTreeRoot anchorState = .ok anchorBlock.stateRoot := by
  induction reachable with
  | anchor made =>
    unfold getForkchoiceStore at made
    cases hashed : SszType.hashTreeRoot anchorState with
    | error err => simp [hashed, bind, Except.bind, Except.mapError] at made
    | ok root =>
      simp only [hashed, bind, Except.bind, Except.mapError] at made
      split at made
      · simp [throw, throwThe, MonadExceptOf.throw] at made
      · rename_i same
        simp only [not_not.mp same]
  | _ => assumption

/-- A non-anchor block state has the block's slot and header with an empty state root. -/
theorem Store.Reachable.blockState_header
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state)
    (other : block ≠ anchorBlock) :
    state.slot = block.slot ∧ SszType.hashTreeRoot state = .ok block.stateRoot ∧
      ∃ bodyRoot, SszType.hashTreeRoot block.body = .ok bodyRoot ∧
        state.latestBlockHeader =
          { slot := block.slot, proposerIndex := block.proposerIndex,
            parentRoot := block.parentRoot, stateRoot := Vector.replicate 32 0, bodyRoot } := by
  obtain ⟨post, postOk, -, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  obtain ⟨parent, checks, engine, signed, -, message, -, transitioned⟩ := produced other
  obtain ⟨advanced, -, -, -, processed, rooted⟩ := stateTransition_ok transitioned
  refine ⟨by simpa [message] using (stateTransition_slot transitioned).2, ?_, ?_⟩
  · simpa [message] using rooted rfl
  · simpa [message] using latestBlockHeader_processBlock processed

/-- Every held block state hashes to the state root of its block, including the anchor. -/
theorem Store.Reachable.blockState_root
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state) :
    SszType.hashTreeRoot state = .ok block.stateRoot := by
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same, same]
    exact reachable.anchorState_root
  · exact (reachable.blockState_header found stored same).2.1

/-- In a reachable store, the state kept for a known block sits at the slot of that block.

Its latest block header matches that block in every field but the state root.

It needs the anchor state and the anchor block to agree in the same two ways. -/
theorem Store.Reachable.blockState_latestBlockHeader
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state) :
    state.slot = block.slot ∧ state.latestBlockHeader.slot = block.slot ∧
      state.latestBlockHeader.proposerIndex = block.proposerIndex ∧
      state.latestBlockHeader.parentRoot = block.parentRoot ∧
      SszType.hashTreeRoot block.body = .ok state.latestBlockHeader.bodyRoot := by
  by_cases same : block = anchorBlock
  · obtain ⟨kept, keptFound, isAnchor, -⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at keptFound
    subst keptFound
    rw [isAnchor same, same]
    exact ⟨anchorSlot.symm, anchorHeader⟩
  · obtain ⟨atSlot, -, bodyRoot, bodyRooted, header⟩ :=
      reachable.blockState_header found stored same
    rw [header]
    exact ⟨atSlot, rfl, rfl, rfl, bodyRooted⟩

/-- A history read after the anchor state agrees with the store's ancestor walk. -/
theorem Store.Reachable.blockState_history_ancestor
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {state : BeaconState preset fork} {query : Slot}
    (stored : store.blockStates[root]? = some state)
    (read : getBlockRootAtSlot state query = .ok readRoot)
    (later : anchorState.slot ≤ query) (status : PayloadStatus) :
    (·.root) <$> store.getAncestor ⟨root, status⟩ query = .ok readRoot := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · rw [anchored same] at read
    have before := (getBlockRootAtSlot_ok_iff.mp read).1
    have le := UInt64.le_iff_toNat_le.mp later
    omega
  · obtain ⟨parent, checks, engine, signed, -, message, parentFound, transitioned⟩ := produced same
    obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok transitioned
    have atSlot := (reachable.blockState_header found stored same).1
    have advancedRead : getBlockRootAtSlot advanced query = .ok readRoot := by
      unfold getBlockRootAtSlot at read ⊢
      obtain ⟨_, _, first, operated, last⟩ := processBlock_split blockOk
      obtain ⟨_, _, before, attested, tail⟩ := processOperations_split operated
      have kept := foldlM_ok_invariant
        (fun s => s.blockRoots = advanced.blockRoots)
        (fun s a t old ok => (payloadInputs_processAttestation ok).blockRoots.trans old)
        (before.blockRoots.trans first.blockRoots) attested
      rwa [processBlock_slot blockOk, last.blockRoots.trans (tail.blockRoots.trans kept)]
        at read
    obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentFound
    have parentLe :=
      Store.Reachable.slot_le_of_blockState anchorSlot reachable parentKnown parentFound
    have parentLt : parent.slot < block.slot := by
      simpa only [message] using (stateTransition_slot transitioned).1
    have above : ¬ block.slot ≤ query := by
      have before := (getBlockRootAtSlot_ok_iff.mp read).1
      rw [atSlot] at before
      exact UInt64.not_le.mpr (UInt64.lt_iff_toNat_lt.mpr before)
    rw [Store.getAncestor_step found above parentKnown (UInt64.lt_of_le_of_lt parentLe parentLt)]
    by_cases old : query < parent.slot
    · have run := slotsOk
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
      obtain ⟨_, -, advancedOk⟩ := run
      exact reachable.blockState_history_ancestor anchorSlot nonzero parentFound
        (getBlockRootAtSlot_of_advanceSlots advancedOk advancedRead old) later _
    · have cached := getBlockRootAtSlot_processSlots_header
        (reachable.blockState_root parentKnown parentFound) (nonzero _ _ parentKnown)
        slotsOk advancedRead (UInt64.not_lt.mp old)
      have parentHash := (processBlock_parentRoot blockOk).2.2
      rw [message] at parentHash
      have eq := Except.ok.inj (cached.symm.trans parentHash)
      rw [Store.getAncestor_of_le parentKnown (UInt64.le_trans parentLe (UInt64.not_lt.mp old))]
      simp only [Functor.map, Except.map, eq]
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A later non-anchor block validates the anchor header after empty-slot processing. -/
private theorem Store.Reachable.anchor_processSlots_header
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {block : BeaconBlock preset fork} {state advanced : BeaconState preset fork}
    {checks : SignatureChecks} {slot : Slot}
    (found : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some state)
    (other : block ≠ anchorBlock)
    (computed : processSlots config checks anchorState slot = .ok advanced) :
    SszType.hashTreeRoot advanced.latestBlockHeader = SszType.hashTreeRoot anchorBlock := by
  obtain ⟨post, postOk, -, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  obtain ⟨parent, childChecks, engine, signed, -, message, parentFound, transitioned⟩ :=
    produced other
  obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentFound
  by_cases same : parentBlock = anchorBlock
  · obtain ⟨parentState, parentOk, anchored, -⟩ := reachable.blockStatesFromParents parentKnown
    rw [parentFound, Option.some.injEq] at parentOk
    subst parentState
    have parentEq := anchored same
    obtain ⟨childAdvanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transitioned
    rw [parentEq] at slotsOk
    rw [processSlots_latestBlockHeader_eq reachable.anchorState_root nonzero computed slotsOk]
    have parentHash := (processBlock_parentRoot blockOk).2.2
    rw [message] at parentHash
    exact parentHash.trans (by simpa only [same] using (reachable.root parentKnown).symm)
  · exact reachable.anchor_processSlots_header nonzero parentKnown parentFound same computed
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A known history root read during anchor lookahead names the anchor block. -/
private theorem Store.Reachable.anchor_processSlots_root
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {advanced : BeaconState preset fork}
    {readBlock : BeaconBlock preset fork}
    {checks : SignatureChecks} {slot query : Slot}
    (found : store.blocks[root]? = some anchorBlock)
    (known : store.blocks[readRoot]? = some readBlock)
    (computed : processSlots config checks anchorState slot = .ok advanced)
    (read : getBlockRootAtSlot advanced query = .ok readRoot)
    (later : anchorState.slot ≤ query) : readRoot = root := by
  by_cases same : readBlock = anchorBlock
  · have hashed := reachable.root known
    rw [same, reachable.root found, Except.ok.injEq] at hashed
    exact hashed.symm
  · obtain ⟨state, stored, -⟩ := reachable.blockStatesFromParents known
    have header := reachable.anchor_processSlots_header nonzero known stored same computed
    have cached := getBlockRootAtSlot_processSlots_header reachable.anchorState_root
      nonzero computed read later
    rw [header, reachable.root found, Except.ok.injEq] at cached
    exact cached.symm

/-- A known history root in lookahead agrees with the ancestor walk after the anchor slot. -/
theorem Store.Reachable.lookahead_history_ancestor
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {state advanced : BeaconState preset fork}
    {readBlock : BeaconBlock preset fork} {checks : SignatureChecks} {slot query : Slot}
    (stored : store.blockStates[root]? = some state)
    (known : store.blocks[readRoot]? = some readBlock)
    (computed : lookaheadState config checks state slot = .ok advanced)
    (read : getBlockRootAtSlot advanced query = .ok readRoot)
    (later : anchorState.slot ≤ query) (status : PayloadStatus) :
    (·.root) <$> store.getAncestor ⟨root, status⟩ query = .ok readRoot := by
  unfold lookaheadState at computed
  split at computed
  · have slotsOk := mapError_ok_iff.mp computed
    by_cases old : query < state.slot
    · have run := slotsOk
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
      obtain ⟨_, -, advancedOk⟩ := run
      exact reachable.blockState_history_ancestor anchorSlot nonzero stored
        (getBlockRootAtSlot_of_advanceSlots advancedOk read old) later status
    · obtain ⟨block, found⟩ := reachable.known_of_blockState stored
      obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
      rw [stored, Option.some.injEq] at postOk
      subst post
      by_cases same : block = anchorBlock
      · have eq := reachable.anchor_processSlots_root (by simpa [same] using nonzero _ _ found)
          (same ▸ found) known ((anchored same) ▸ slotsOk) read later
        rw [Store.getAncestor_of_le found (same ▸ UInt64.le_trans anchorSlot later)]
        simp only [Functor.map, Except.map, eq]
      · have eq := getBlockRootAtSlot_processSlots_header (reachable.blockState_root found stored)
          (nonzero _ _ found) slotsOk read (UInt64.not_lt.mp old)
        have filled := processSlots_latestBlockHeader_of_zero
          (by rw [(reachable.blockState_header found stored same).2.2.choose_spec.2])
          (reachable.blockState_root found stored) (nonzero _ _ found) slotsOk
        have body := (reachable.blockState_header found stored same).2.2.choose_spec
        have blockHash := (BeaconBlock.hashTreeRoot_header body.1).trans (reachable.root found)
        rw [filled, body.2, blockHash, Except.ok.injEq] at eq
        rw [Store.getAncestor_of_le found (UInt64.le_trans
          (Store.Reachable.slot_le_of_blockState anchorSlot reachable found stored)
          (UInt64.not_lt.mp old))]
        simp only [Functor.map, Except.map, eq]
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst advanced
    exact reachable.blockState_history_ancestor anchorSlot nonzero stored read later status

/-- A reachable receiver holding the tip agrees on ancestor walks above the anchor slot. -/
theorem Store.getAncestor_of_same_blocks {store receiver : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock receiver)
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b →
      receiver.blocks[r]? = some c → b = c)
    {node ancestor : ForkChoiceNode} {slot : Slot}
    (aboveAnchor : anchorBlock.slot ≤ slot)
    (known : ∃ block, receiver.blocks[node.root]? = some block)
    (walk : store.getAncestor node slot = .ok ancestor) :
    receiver.getAncestor node slot = .ok ancestor := by
  apply Store.getAncestor_of_parent_chain same ?_ known walk
  intro r block parent found parentFound above held
  have notAnchor : block ≠ anchorBlock := by
    intro eq
    exact UInt64.not_le.mpr above (eq ▸ aboveAnchor)
  obtain ⟨_, _, _, provenance⟩ := reachable.blockStatesFromParents held
  obtain ⟨_, _, _, _, _, _, parentStateFound, _⟩ := provenance notAnchor
  obtain ⟨other, otherFound⟩ := reachable.known_of_blockState parentStateFound
  exact (same _ _ _ parentFound otherFound).symm ▸ otherFound

/-- An ancestor test that succeeds in one store succeeds in a reachable store with the same blocks.

The ancestor lies above the anchor, and the receiver holds the tip.

The receiver need not hold the ancestor in advance: the walk from the tip reaches it. -/
theorem Store.isAncestor_of_same_blocks {store receiver : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock receiver)
    (before : fork < .glamsterdam)
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b →
      receiver.blocks[r]? = some c → b = c)
    {node ancestor : ForkChoiceNode} {block : BeaconBlock preset fork}
    (sourceKnown : store.blocks[ancestor.root]? = some block)
    (aboveAnchor : anchorBlock.slot ≤ block.slot)
    (known : ∃ tip, receiver.blocks[node.root]? = some tip)
    (descends : store.isAncestor node ancestor = .ok true) :
    receiver.isAncestor node ancestor = .ok true := by
  have walk := Store.getAncestor_of_isAncestor_of_lt before sourceKnown descends
  exact Store.isAncestor_of_getAncestor
    (Store.getAncestor_of_same_blocks reachable same aboveAnchor known walk)

/-- Checkpoint reads agree across reachable stores holding the tip above the anchor boundary. -/
theorem Store.getCheckpointBlock_of_same_blocks {store receiver : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock receiver)
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b →
      receiver.blocks[r]? = some c → b = c)
    {root checkpoint : Root} {epoch : Epoch} {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (aboveAnchor : anchorBlock.slot ≤ boundary)
    (known : ∃ block, receiver.blocks[root]? = some block)
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    receiver.getCheckpointBlock root epoch = .ok checkpoint := by
  simp only [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind] at read ⊢
  cases walk : store.getAncestor ⟨root, .pending⟩ boundary with
  | error error => simp [walk] at read
  | ok ancestor =>
    rw [Store.getAncestor_of_same_blocks reachable same aboveAnchor known walk]
    simpa [walk] using read

end EthLib.Consensus
