module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: each block state of a store comes from the state of its parent

A reachable store keeps a state for each known block.

A known anchor block has the anchor state.

Each other block has the state that its transition gives from the state of its parent.

So along a chain of known blocks above the anchor, each state is the transition of the one before.
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

It ran with some signature checks and some execution engine, which may differ between blocks.

It checks the state root, and the signature of the proposer under those checks.

Some checks accept every signature, so this says nothing on signatures. -/
def BlockStatesFromParents (config : Config) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) (store : Store preset fork) : Prop :=
  ∀ ⦃root : Root⦄ ⦃block : BeaconBlock preset fork⦄, store.blocks[root]? = some block →
    ∃ state, store.blockStates[root]? = some state ∧
      (block = anchorBlock → state = anchorState) ∧
      (block ≠ anchorBlock → ∃ parentState checks engine, ∃ signed : SignedBeaconBlock preset fork,
        signed.message = block ∧ store.blockStates[block.parentRoot]? = some parentState ∧
        stateTransition config checks engine parentState signed true = .ok state)

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- A reachable store knows the anchor block, at its own root. -/
private theorem Store.Reachable.anchor_known
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

/-- In a reachable store, each known block has the state after it, from the state of its parent.

A known anchor block has the anchor state instead. -/
theorem Store.Reachable.blockStatesFromParents
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.BlockStatesFromParents config anchorState anchorBlock := by
  induction reachable with
  | anchor made =>
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
  | tick _ ticked ih =>
    obtain ⟨-, -, blocks, states⟩ := Store.onTick_frame ticked
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | @block prior _ _ _ signed previous added ih =>
    rcases Store.onBlock_same_or_insert added with
      same | ⟨blockRoot, hashed, fresh, blocks, pre, state, preFound, ok, states⟩
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
      refine ⟨state, rfl, fun eq => absurd eq notAnchor, fun _ => ⟨pre, _, _, _, rfl, ?_, ok⟩⟩
      rw [getElem?_insert_root]
      simp only [← same, parentNe preFound, ↓reduceIte]
      exact preFound
    · simp only [same, ↓reduceIte] at found ⊢
      obtain ⟨old, oldFound, rest⟩ := ih found
      refine ⟨old, oldFound, rest.1, fun ne => ?_⟩
      obtain ⟨p, c, e, s, hs, hp, ht⟩ := rest.2 ne
      refine ⟨p, c, e, s, hs, ?_, ht⟩
      rw [getElem?_insert_root]
      simp only [parentNe hp, ↓reduceIte]
      exact hp
  | attestation _ attested ih =>
    obtain ⟨-, blocks, states⟩ := Store.onAttestation_frame attested
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, states⟩ := Store.onAttesterSlashing_frame slashed
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onExecutionPayloadEnvelope_frame accepted
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found
  | inclusionList _ accepted ih =>
    obtain ⟨-, blocks, states⟩ := Store.onInclusionList_frame accepted
    intro root block found
    rw [blocks] at found
    rw [states]
    exact ih found

end EthLib.Consensus
