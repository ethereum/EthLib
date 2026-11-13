module

public import EthLib.Consensus.Proofs.ForkChoice.ForwardClock

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
    obtain ⟨-, blocks, states⟩ := Store.onAttestation_frame attested
    exact .of_maps blocks states ih
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, states⟩ := Store.onAttesterSlashing_frame slashed
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
    obtain ⟨-, blocks, states⟩ := Store.onAttestation_frame attested
    exact .of_maps blocks states ih
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, states⟩ := Store.onAttesterSlashing_frame slashed
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
    exact blockStates_le_of_same (Store.onAttestation_frame attested).2.2
      (Store.onAttestation_sameClock attested) ih
  | attesterSlashing _ slashed ih =>
    exact blockStates_le_of_same (Store.onAttesterSlashing_frame slashed).2.2
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

end EthLib.Consensus
