module

public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.ForkChoice.ForwardClock

/-!
# Proofs: where each latest vote of a store comes from

The store records a latest vote only in the handler of an attestation.

So each latest vote of a store with a forward clock is the vote of an attestation with these facts.

That attestation votes for a known block, from the slot of that block or later.

Its target is in the epoch of its slot, with the checkpoint block of the chain of its vote as root.

The store keeps the state of its target.

In that state its committees pass the check of block processing, and the voter attests in it.

When no tick sets the clock back, its slot is also before the current slot of the store.

Those facts outlive the attestation: blocks and checkpoint states are only ever added.

A new block takes a new root, so the ancestors of the known blocks stay the same.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store after : Store preset fork}

/-- The facts behind a latest vote of a validator, from the attestation that cast it.

The attestation votes for a known block, from the slot of that block or later.

Its target is in the epoch of its slot, with the checkpoint block of the chain of its vote as root.

The store keeps the state of that target.

In that state the committees of the attestation pass the check of block processing.

The validator is one of the attesters of the attestation in that state.

The slot of the attestation is before the current slot of the store.

The handler checks more, such as the signature, and those checks are left out here.

The facts on the committees of the voter do not depend on them. -/
structure VoteOrigin (config : Config) (store : Store preset fork) (validator : ValidatorIndex)
    (attestation : Attestation preset fork) : Prop where
  /-- The vote is for a known block, from the slot of that block or later. -/
  voted : ∃ block, store.blocks[attestation.data.beaconBlockRoot]? = some block ∧
    block.slot ≤ attestation.data.slot
  /-- The target is in the epoch of the slot. -/
  targetEpoch : attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot
  /-- The root of the target is the checkpoint block of the chain of the vote. -/
  targetRoot : store.getCheckpointBlock attestation.data.beaconBlockRoot
    attestation.data.target.epoch = .ok attestation.data.target.root
  /-- The state of the target passes the committees, and the validator attests in it. -/
  committees : ∃ targetState indexed,
    store.checkpointStates[attestation.data.target]? = some targetState ∧
      checkAttestationCommittees targetState attestation = .ok () ∧
      getIndexedAttestation targetState attestation = .ok indexed ∧
      validator ∈ indexed.attestingIndices.data.toList
  /-- The slot is before the current slot. -/
  past : ∃ current, store.getCurrentSlot config = .ok current ∧ attestation.data.slot < current

/-- Each latest vote of the store is the vote of an attestation, with the facts behind it. -/
def VotesHaveOrigins (config : Config) (store : Store preset fork) : Prop :=
  ∀ ⦃validator : ValidatorIndex⦄ ⦃message : LatestMessage fork⦄,
    store.latestMessages[validator]? = some message →
      ∃ attestation, message = LatestMessage.ofAttestation attestation ∧
        store.VoteOrigin config validator attestation

/-! ## The facts outlive the step that set them -/

/-- The facts behind a vote hold in a later store that keeps every block and checkpoint state.

The clock of the later store must not be behind. -/
theorem VoteOrigin.mono {validator : ValidatorIndex} {attestation : Attestation preset fork}
    (origin : store.VoteOrigin config validator attestation)
    (blocks : ∀ {root : Root} {block : BeaconBlock preset fork},
      store.blocks[root]? = some block → after.blocks[root]? = some block)
    (states : ∀ {checkpoint : Checkpoint} {state : BeaconState preset fork},
      store.checkpointStates[checkpoint]? = some state →
        after.checkpointStates[checkpoint]? = some state)
    (clock : ∀ {current : Slot}, store.getCurrentSlot config = .ok current →
      ∃ later, after.getCurrentSlot config = .ok later ∧ current ≤ later) :
    after.VoteOrigin config validator attestation := by
  obtain ⟨⟨block, found, le⟩, epoch, root, ⟨targetState, indexed, state, committees, indexedOk,
    voter⟩, ⟨current, slotOk, lt⟩⟩ := origin
  obtain ⟨later, laterOk, laterLe⟩ := clock slotOk
  exact ⟨⟨block, blocks found, le⟩, epoch, getCheckpointBlock_of_blocks blocks root,
    ⟨targetState, indexed, states state, committees, indexedOk, voter⟩,
    ⟨later, laterOk, UInt64.lt_of_lt_of_le lt laterLe⟩⟩

/-- The voter of a vote sits in a committee of the slot of its attestation, in its target state.

Its index is below the count of committees per slot of the epoch of the slot. -/
theorem VoteOrigin.exists_mem_committee {validator : ValidatorIndex}
    {attestation : Attestation preset fork}
    (origin : store.VoteOrigin config validator attestation) :
    ∃ targetState index committee,
      store.checkpointStates[attestation.data.target]? = some targetState ∧
      index < getCommitteeCountPerSlot targetState
        (computeEpochAtSlot preset attestation.data.slot) ∧
      getBeaconCommittee targetState attestation.data.slot index = .ok committee ∧
      validator ∈ committee := by
  obtain ⟨targetState, indexed, state, checked, indexedOk, voter⟩ := origin.committees
  obtain ⟨index, committee, below, committeeOk, member⟩ :=
    exists_mem_getBeaconCommittee_of_checkAttestationCommittees checked indexedOk voter
  rw [origin.targetEpoch] at below
  exact ⟨targetState, index, committee, state, below, committeeOk, member⟩

/-- The latest votes keep their facts in a store with the same votes, blocks, states and clock. -/
private theorem VotesHaveOrigins.of_same (holds : store.VotesHaveOrigins config)
    (messages : after.latestMessages = store.latestMessages)
    (blocks : after.blocks = store.blocks)
    (states : after.checkpointStates = store.checkpointStates)
    (clock : SameClock store after) : after.VotesHaveOrigins config := by
  intro validator message found
  rw [messages] at found
  obtain ⟨attestation, rfl, origin⟩ := holds found
  refine ⟨attestation, rfl, origin.mono (fun known => ?_) (fun known => ?_)
    (fun slotOk => ⟨_, slotOk ▸ clock.getCurrentSlot, UInt64.le_refl _⟩)⟩
  · rw [blocks]
    exact known
  · rw [states]
    exact known

/-! ## The attestation handler -/

/-- Storing the state of a target keeps the latest votes and the states already stored. -/
private theorem storeTargetCheckpointState_kept {checks : SignatureChecks} {target : Checkpoint}
    (stored : store.storeTargetCheckpointState config checks target = .ok after) :
    after.latestMessages = store.latestMessages ∧
      ∀ {checkpoint : Checkpoint} {state : BeaconState preset fork},
        store.checkpointStates[checkpoint]? = some state →
          after.checkpointStates[checkpoint]? = some state := by
  unfold storeTargetCheckpointState at stored
  split at stored
  · simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    exact ⟨rfl, fun found => found⟩
  · rename_i absent
    simp only [bind_ok_iff] at stored
    obtain ⟨state, -, stored⟩ := stored
    simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    refine ⟨rfl, fun {checkpoint _} found => ?_⟩
    rw [Std.TreeMap.getElem?_insert]
    split
    · rename_i same
      exact absurd (Std.TreeMap.contains_iff_mem.mpr
        (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
          rw [Std.TreeMap.getElem?_congr same, found]
          rfl))) absent
    · exact found

/-- After an attestation, a latest vote is one from before or the vote of the attestation.

The vote of the attestation then has the facts behind it, in the store after it. -/
theorem onAttestation_latestMessages_cases {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool}
    {validator : ValidatorIndex} {latest : LatestMessage fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after)
    (found : after.latestMessages[validator]? = some latest) :
    store.latestMessages[validator]? = some latest ∨
      (latest = LatestMessage.ofAttestation attestation ∧
        after.VoteOrigin config validator attestation) := by
  have frame := onAttestation_frame attested
  have clock := (onAttestation_sameClock attested).getCurrentSlot (config := config)
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨passed, valid, stored, storing, targetState, stateFound, checked, committeesOk,
    indexed, indexedOk, isValid, _, attested⟩ := attested
  cases passed
  cases checked
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    obtain ⟨keptMessages, -⟩ := storeTargetCheckpointState_kept storing
    rcases foldl_recordVote_cases _ _ found with old | ⟨voter, rfl⟩
    · exact .inl (keptMessages ▸ old)
    obtain ⟨voted, epoch, root, past⟩ := validateOnAttestation_ok valid
    have blocks : ∀ {root : Root} {block : BeaconBlock preset fork},
        store.blocks[root]? = some block → (stored.updateLatestMessages
          indexed.attestingIndices.data.toList attestation).blocks[root]? = some block := by
      intro root block known
      rw [frame.2.1]
      exact known
    refine .inr ⟨rfl, ?_, epoch, getCheckpointBlock_of_blocks blocks root, ?_, ?_⟩
    · obtain ⟨block, known, le⟩ := voted
      exact ⟨block, blocks known, le⟩
    · exact ⟨targetState, indexed, checkpointState_ok_iff.mp stateFound,
        mapError_ok_iff.mp committeesOk, mapError_ok_iff.mp indexedOk, voter⟩
    · rw [clock]
      exact past
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- An attestation keeps the state of each checkpoint of the store. -/
theorem onAttestation_checkpointStates_of_found {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool} {checkpoint : Checkpoint}
    {state : BeaconState preset fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after)
    (found : store.checkpointStates[checkpoint]? = some state) :
    after.checkpointStates[checkpoint]? = some state := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact (storeTargetCheckpointState_kept storing).2 found
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- Each latest vote of a store with a forward clock is the vote of some attestation.

The facts behind that vote hold in the store. -/
theorem Store.ForwardReachable.votesHaveOrigins
    (forward : Store.ForwardReachable config anchorState anchorBlock store) :
    store.VotesHaveOrigins config := by
  induction forward with
  | anchor made =>
    obtain ⟨_, _, empty, _⟩ := getForkchoiceStore_fields made
    intro validator message found
    rw [empty] at found
    simp at found
  | tick _ forward ticked ih =>
    intro validator message found
    rw [(Store.onTick_checkpointStates_latestMessages ticked).2] at found
    obtain ⟨attestation, rfl, origin⟩ := ih found
    refine ⟨attestation, rfl, origin.mono (fun known => ?_) (fun known => ?_)
      (Store.exists_getCurrentSlot_onTick_ge forward ticked)⟩
    · rw [(Store.onTick_frame ticked).2.2.1]
      exact known
    · rw [(Store.onTick_checkpointStates_latestMessages ticked).1]
      exact known
  | block _ added ih =>
    intro validator message found
    rw [(Store.onBlock_checkpointStates_latestMessages added).2] at found
    obtain ⟨attestation, rfl, origin⟩ := ih found
    refine ⟨attestation, rfl, origin.mono (Store.onBlock_blocks_of_found added)
      (fun known => ?_) (fun slotOk =>
        ⟨_, slotOk ▸ (Store.onBlock_sameClock added).getCurrentSlot, UInt64.le_refl _⟩)⟩
    rw [(Store.onBlock_checkpointStates_latestMessages added).1]
    exact known
  | attestation _ attested ih =>
    intro validator message found
    rcases Store.onAttestation_latestMessages_cases attested found with old | ⟨rfl, origin⟩
    · obtain ⟨attestation, rfl, origin⟩ := ih old
      refine ⟨attestation, rfl, origin.mono (fun known => ?_)
        (Store.onAttestation_checkpointStates_of_found attested)
        (fun slotOk => ⟨_, slotOk ▸ (Store.onAttestation_sameClock attested).getCurrentSlot,
          UInt64.le_refl _⟩)⟩
      rw [(Store.onAttestation_frame attested).2.1]
      exact known
    · exact ⟨_, rfl, origin⟩
  | attesterSlashing _ slashed ih =>
    exact ih.of_same (Store.onAttesterSlashing_checkpointStates_latestMessages slashed).2
      (Store.onAttesterSlashing_frame slashed).2.1
      (Store.onAttesterSlashing_checkpointStates_latestMessages slashed).1
      (Store.onAttesterSlashing_sameClock slashed)
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih.of_same rfl rfl rfl ⟨rfl, rfl⟩
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih.of_same rfl rfl rfl ⟨rfl, rfl⟩
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
    exact ih.of_same rfl rfl rfl ⟨rfl, rfl⟩

end EthLib.Consensus
