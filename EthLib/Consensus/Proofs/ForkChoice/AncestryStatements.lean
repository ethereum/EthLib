module

public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.Transition.RootLinks

/-!
# Statements for issue 1423

This file is not an upstream-ready change: three of its five statements end in `sorry`.

The two provenance theorems of the store's justified and finalized fields are proved.

Their proofs are the untimed provenance proofs of the fork, without its network imports.

An anchor checkpoint is synthesized, and a pulled-up state is not a stored post-state.

State checkpoints at or before the anchor epoch can name blocks outside the store.

The ancestry candidates therefore separate that boundary explicitly.

They retain a concrete zero-state-root witness instead of assuming hash injectivity.

Gasper Section 4.1 defines epoch boundary pairs, including repeated blocks at different epochs.

Section 8.5 gives the four finalization cases.

Source: https://arxiv.org/html/2003.03052v3
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Pulling up a tip preserves justified-field provenance from its successful count. -/
theorem Store.justified_properties_of_computePulledUpTip {config : Config}
    {store after : Store preset fork} {root : Root} (P : Checkpoint → Prop)
    (realized : P store.justifiedCheckpoint)
    (unrealized : P store.unrealizedJustifiedCheckpoint)
    (counted : ∀ (state pulled : BeaconState preset fork),
      store.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.currentJustifiedCheckpoint)
    (computed : store.computePulledUpTip config root = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint := by
  have update : ∀ (s : Store preset fork) justified finalized,
      P s.justifiedCheckpoint → P s.unrealizedJustifiedCheckpoint → P justified →
      P (s.updateCheckpoints justified finalized).justifiedCheckpoint ∧
        P (s.updateCheckpoints justified finalized).unrealizedJustifiedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
  have updateUnrealized : ∀ (s : Store preset fork) justified finalized,
      P s.justifiedCheckpoint → P s.unrealizedJustifiedCheckpoint → P justified →
      P (s.updateUnrealizedCheckpoints justified finalized).justifiedCheckpoint ∧
        P (s.updateUnrealizedCheckpoints justified finalized).unrealizedJustifiedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨old, by assumption⟩
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, found, pulled, processed, block, -, epoch, -, computed⟩ := computed
  have new := counted state pulled (Store.blockState_ok_iff.mp found)
    (mapError_ok_iff.mp processed)
  have preserved := updateUnrealized
    { store with unrealizedJustifications :=
      store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint }
    pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint realized unrealized new
  split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
    subst after
  · exact update _ _ _ preserved.1 preserved.2 new
  · exact preserved

/-- An accepted block supplies justified fields only from its post-state or pulled-up count. -/
theorem Store.justified_properties_of_onBlock {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {store after : Store preset fork} (P : Checkpoint → Prop)
    (realized : P store.justifiedCheckpoint)
    (unrealized : P store.unrealizedJustifiedCheckpoint)
    (states : ∀ (root : Root) (state : BeaconState preset fork),
      after.blockStates[root]? = some state → P state.currentJustifiedCheckpoint)
    (counts : ∀ (root : Root) (state pulled : BeaconState preset fork),
      after.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.currentJustifiedCheckpoint)
    (added : store.onBlock config checks sources signed = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint := by
  cases root : SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact ⟨realized, unrealized⟩
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, -, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedFields : P recorded.justifiedCheckpoint ∧
        P recorded.unrealizedJustifiedCheckpoint := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact ⟨realized, unrealized⟩
      · cases record
        exact ⟨realized, unrealized⟩
    have boostedFields : P boosted.justifiedCheckpoint ∧
        P boosted.unrealizedJustifiedCheckpoint := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact recordedFields
    have kept := (Store.computePulledUpTip_frame added).2.2.1
    have newFound : after.blockStates[blockRoot]? = some state := by
      rw [kept, Store.updateCheckpoints_blockStates,
        (Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1]
      simp
    have new := states blockRoot state newFound
    have updated :
        P (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).justifiedCheckpoint ∧
        P (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).unrealizedJustifiedCheckpoint := by
      obtain ⟨old, pending⟩ := boostedFields
      unfold Store.updateCheckpoints
      split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
    exact Store.justified_properties_of_computePulledUpTip P updated.1 updated.2
      (fun s p found processed => counts blockRoot s p (kept.symm ▸ found) processed) added

/-- A per-slot tick retains provenance of both justified fields. -/
theorem Store.justified_properties_of_onTickPerSlot {config : Config}
    {store after : Store preset fork} {time : UInt64} (P : Checkpoint → Prop)
    (realized : P store.justifiedCheckpoint)
    (unrealized : P store.unrealizedJustifiedCheckpoint)
    (ticked : store.onTickPerSlot config time = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint := by
  have update : ∀ (s : Store preset fork) justified finalized,
      P s.justifiedCheckpoint → P s.unrealizedJustifiedCheckpoint → P justified →
      P (s.updateCheckpoints justified finalized).justifiedCheckpoint ∧
        P (s.updateCheckpoints justified finalized).unrealizedJustifiedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
  unfold Store.onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    obtain ⟨offset, -, ticked⟩ := ticked <;>
    split at ticked <;>
    simp only [pure, Except.pure, Except.ok.injEq] at ticked <;> subst after
  · exact update _ _ _ realized unrealized unrealized
  · exact ⟨realized, unrealized⟩
  · exact update _ _ _ realized unrealized unrealized
  · exact ⟨realized, unrealized⟩

/-- Catch-up retains provenance of both justified fields through every tick. -/
theorem Store.justified_properties_of_catchUp {config : Config}
    {store after : Store preset fork} {slot : Slot} (P : Checkpoint → Prop)
    (realized : P store.justifiedCheckpoint)
    (unrealized : P store.unrealizedJustifiedCheckpoint)
    (caught : Store.catchUp config store slot = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint := by
  induction store using Store.catchUp.induct config slot with
  | _ store ih =>
    rw [Store.catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTime, -, ticked, tick, caught⟩ := caught
      split at caught
      · obtain ⟨realized, unrealized⟩ :=
          Store.justified_properties_of_onTickPerSlot P realized unrealized tick
        exact ih ticked ‹_› realized unrealized caught
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst after
      exact ⟨realized, unrealized⟩

/-- A full tick retains justified-field provenance, including catch-up realization. -/
theorem Store.justified_properties_of_onTick {config : Config}
    {store after : Store preset fork} {time : UInt64} (P : Checkpoint → Prop)
    (realized : P store.justifiedCheckpoint)
    (unrealized : P store.unrealizedJustifiedCheckpoint)
    (ticked : store.onTick config time = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint := by
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨slot, -, caught, catchUp, ticked⟩ := ticked
  obtain ⟨realized, unrealized⟩ :=
    Store.justified_properties_of_catchUp P realized unrealized catchUp
  exact Store.justified_properties_of_onTickPerSlot P realized unrealized ticked

/-- Each justified store field has an anchor, held-state, or successful pulled-up origin.

The checkpoint pair is retained in full, with no timing bound. -/
theorem Store.Reachable.justified_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∀ checkpoint, (checkpoint = store.justifiedCheckpoint ∨
      checkpoint = store.unrealizedJustifiedCheckpoint) →
      (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
        checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = state.currentJustifiedCheckpoint) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = pulled.currentJustifiedCheckpoint := by
  let Origin := fun (s : Store preset fork) (checkpoint : Checkpoint) =>
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
    (∃ (root : Root) (state : BeaconState preset fork), s.blockStates[root]? = some state ∧
      checkpoint = state.currentJustifiedCheckpoint) ∨
    ∃ (root : Root) (state pulled : BeaconState preset fork), s.blockStates[root]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧
      checkpoint = pulled.currentJustifiedCheckpoint
  have mono {s t : Store preset fork}
      (kept : ∀ (root : Root) (state : BeaconState preset fork),
        s.blockStates[root]? = some state → t.blockStates[root]? = some state)
      {checkpoint : Checkpoint} (origin : Origin s checkpoint) : Origin t checkpoint := by
    rcases origin with anchor | ⟨root, state, found, same⟩ | ⟨root, state, pulled, found, run, same⟩
    · exact .inl anchor
    · exact .inr (.inl ⟨root, state, kept root state found, same⟩)
    · exact .inr (.inr ⟨root, state, pulled, kept root state found, run, same⟩)
  have both : Origin store store.justifiedCheckpoint ∧
      Origin store store.unrealizedJustifiedCheckpoint := by
    induction reachable with
    | anchor made =>
      obtain ⟨root, hashed, -, -, justified, -, unrealized, -⟩ := getForkchoiceStore_anchor made
      exact ⟨.inl ⟨root, hashed, justified⟩, .inl ⟨root, hashed, unrealized⟩⟩
    | @tick before after time reachable ticked ih =>
      have kept := (Store.onTick_frame ticked).2.2.2
      exact Store.justified_properties_of_onTick (Origin after)
        (mono (fun _ _ h => kept.symm ▸ h) ih.1)
        (mono (fun _ _ h => kept.symm ▸ h) ih.2) ticked
    | @block before after checks sources signed reachable added ih =>
      have kept : ∀ (root : Root) (state : BeaconState preset fork),
          before.blockStates[root]? = some state → after.blockStates[root]? = some state := by
        intro root state found
        rcases Store.onBlock_same_or_insert added with same |
          ⟨newRoot, -, fresh, -, -, post, -, -, states⟩
        · exact same ▸ found
        have other : newRoot ≠ root := by
          rintro rfl
          rw [reachable.blockState_eq_none fresh] at found
          cases found
        rw [states, getElem?_insert_root]
        simpa only [other, ↓reduceIte] using found
      exact Store.justified_properties_of_onBlock (Origin after)
        (mono kept ih.1) (mono kept ih.2)
        (fun root state found => .inr (.inl ⟨root, state, found, rfl⟩))
        (fun root state pulled found run => .inr (.inr ⟨root, state, pulled, found, run, rfl⟩))
        added
    | attestation _ attested ih =>
      unfold Store.onAttestation at attested
      simp only [bind_ok_iff] at attested
      obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
      have storedOrigin : Origin stored stored.justifiedCheckpoint ∧
          Origin stored stored.unrealizedJustifiedCheckpoint := by
        unfold Store.storeTargetCheckpointState at storing
        split at storing
        · simp only [pure, Except.pure, Except.ok.injEq] at storing
          exact storing ▸ ih
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
          obtain ⟨_, _, rfl⟩ := storing
          exact ih
      split at attested
      · simp only [pure, Except.pure, Except.ok.injEq] at attested
        subst attested
        exact storedOrigin
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested
    | attesterSlashing _ slashed ih =>
      unfold Store.onAttesterSlashing at slashed
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
      obtain ⟨_, _, rfl⟩ := slashed
      exact ih
    | payloadAttestation _ voted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
      exact ih
    | envelope _ accepted ih =>
      obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
      obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
      exact ih
    | inclusionList _ accepted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
      exact ih
  intro checkpoint same
  rcases same with rfl | rfl
  · exact both.1
  · exact both.2

/-- Pulling up a tip adds only the finalization of its successful justification computation. -/
theorem Store.finalized_properties_of_computePulledUpTip {config : Config}
    {store after : Store preset fork} {root : Root} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (counted : ∀ (state pulled : BeaconState preset fork),
      store.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.finalizedCheckpoint)
    (computed : store.computePulledUpTip config root = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  have update : ∀ (s : Store preset fork) justified finalized,
      P s.finalizedCheckpoint → P s.unrealizedFinalizedCheckpoint → P finalized →
      P (s.updateCheckpoints justified finalized).finalizedCheckpoint ∧
        P (s.updateCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
  have updateUnrealized : ∀ (s : Store preset fork) justified finalized,
      P s.finalizedCheckpoint → P s.unrealizedFinalizedCheckpoint → P finalized →
      P (s.updateUnrealizedCheckpoints justified finalized).finalizedCheckpoint ∧
        P (s.updateUnrealizedCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨old, by assumption⟩
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, found, pulled, processed, block, -, epoch, -, computed⟩ := computed
  have new := counted state pulled (Store.blockState_ok_iff.mp found)
    (mapError_ok_iff.mp processed)
  have preserved := updateUnrealized
    { store with unrealizedJustifications :=
      store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint }
    pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint realized unrealized new
  split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
    subst after
  · exact update _ _ _ preserved.1 preserved.2 new
  · exact preserved

/-- An accepted block adds only its post-state or its pulled-up finalization to the fields. -/
theorem Store.finalized_properties_of_onBlock {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {store after : Store preset fork} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (states : ∀ (root : Root) (state : BeaconState preset fork),
      after.blockStates[root]? = some state → P state.finalizedCheckpoint)
    (counts : ∀ (root : Root) (state pulled : BeaconState preset fork),
      after.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled → P pulled.finalizedCheckpoint)
    (added : store.onBlock config checks sources signed = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  cases root : SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact ⟨realized, unrealized⟩
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, -, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    have recordedFields : P recorded.finalizedCheckpoint ∧
        P recorded.unrealizedFinalizedCheckpoint := by
      unfold Store.recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact ⟨realized, unrealized⟩
      · cases record
        exact ⟨realized, unrealized⟩
    have boostedFields : P boosted.finalizedCheckpoint ∧
        P boosted.unrealizedFinalizedCheckpoint := by
      unfold Store.updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boosted <;> exact recordedFields
    have kept := (Store.computePulledUpTip_frame added).2.2.1
    have newFound : after.blockStates[blockRoot]? = some state := by
      rw [kept, Store.updateCheckpoints_blockStates,
        (Store.updateProposerBoostRoot_frame boost).2.2.1,
        (Store.recordBlockTimeliness_frame record).2.2.1]
      simp
    have new := states blockRoot state newFound
    have updated :
        P (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).finalizedCheckpoint ∧
        P (boosted.updateCheckpoints state.currentJustifiedCheckpoint
          state.finalizedCheckpoint).unrealizedFinalizedCheckpoint := by
      obtain ⟨old, pending⟩ := boostedFields
      unfold Store.updateCheckpoints
      split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
    exact Store.finalized_properties_of_computePulledUpTip P updated.1 updated.2
      (fun s p found processed => counts blockRoot s p (kept.symm ▸ found) processed) added

/-- A tick preserves a property shared by the realized and unrealized finalized checkpoints. -/
theorem Store.finalized_properties_of_onTickPerSlot {config : Config}
    {store after : Store preset fork} {time : UInt64} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (ticked : store.onTickPerSlot config time = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  have update : ∀ (s : Store preset fork) justified finalized,
      P s.finalizedCheckpoint → P s.unrealizedFinalizedCheckpoint → P finalized →
      P (s.updateCheckpoints justified finalized).finalizedCheckpoint ∧
        P (s.updateCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
    intro s justified finalized old pending new
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> exact ⟨by assumption, pending⟩
  unfold Store.onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    obtain ⟨offset, -, ticked⟩ := ticked <;>
    split at ticked <;>
    simp only [pure, Except.pure, Except.ok.injEq] at ticked <;> subst after
  · exact update _ _ _ realized unrealized unrealized
  · exact ⟨realized, unrealized⟩
  · exact update _ _ _ realized unrealized unrealized
  · exact ⟨realized, unrealized⟩

/-- Catch-up preserves a property of both finalized checkpoint fields through every tick. -/
theorem Store.finalized_properties_of_catchUp {config : Config}
    {store after : Store preset fork} {slot : Slot} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (caught : Store.catchUp config store slot = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  induction store using Store.catchUp.induct config slot with
  | _ store ih =>
    rw [Store.catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTime, -, ticked, tick, caught⟩ := caught
      split at caught
      · obtain ⟨realized, unrealized⟩ :=
          Store.finalized_properties_of_onTickPerSlot P realized unrealized tick
        exact ih ticked ‹_› realized unrealized caught
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst after
      exact ⟨realized, unrealized⟩

/-- A full tick retains original checkpoint provenance, including catch-up realization. -/
theorem Store.finalized_properties_of_onTick {config : Config}
    {store after : Store preset fork} {time : UInt64} (P : Checkpoint → Prop)
    (realized : P store.finalizedCheckpoint)
    (unrealized : P store.unrealizedFinalizedCheckpoint)
    (ticked : store.onTick config time = .ok after) :
    P after.finalizedCheckpoint ∧ P after.unrealizedFinalizedCheckpoint := by
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨slot, -, caught, catchUp, ticked⟩ := ticked
  obtain ⟨realized, unrealized⟩ :=
    Store.finalized_properties_of_catchUp P realized unrealized catchUp
  exact Store.finalized_properties_of_onTickPerSlot P realized unrealized ticked

/-- Each finalized store field has an anchor, held-state, or successful pulled-up origin.

The checkpoint pair is retained in full, with no timing bound. -/
theorem Store.Reachable.finalized_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∀ checkpoint, (checkpoint = store.finalizedCheckpoint ∨
      checkpoint = store.unrealizedFinalizedCheckpoint) →
      (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
        checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = state.finalizedCheckpoint) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = pulled.finalizedCheckpoint := by
  let Origin := fun (s : Store preset fork) (checkpoint : Checkpoint) =>
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
    (∃ (root : Root) (state : BeaconState preset fork), s.blockStates[root]? = some state ∧
      checkpoint = state.finalizedCheckpoint) ∨
    ∃ (root : Root) (state pulled : BeaconState preset fork), s.blockStates[root]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧
      checkpoint = pulled.finalizedCheckpoint
  have mono {s t : Store preset fork}
      (kept : ∀ (root : Root) (state : BeaconState preset fork),
        s.blockStates[root]? = some state → t.blockStates[root]? = some state)
      {checkpoint : Checkpoint} (origin : Origin s checkpoint) : Origin t checkpoint := by
    rcases origin with anchor | ⟨root, state, found, same⟩ | ⟨root, state, pulled, found, run, same⟩
    · exact .inl anchor
    · exact .inr (.inl ⟨root, state, kept root state found, same⟩)
    · exact .inr (.inr ⟨root, state, pulled, kept root state found, run, same⟩)
  have both : Origin store store.finalizedCheckpoint ∧
      Origin store store.unrealizedFinalizedCheckpoint := by
    induction reachable with
    | anchor made =>
      obtain ⟨root, hashed, -, -, -, final, -, unrealized⟩ := getForkchoiceStore_anchor made
      exact ⟨.inl ⟨root, hashed, final⟩, .inl ⟨root, hashed, unrealized⟩⟩
    | @tick before after time reachable ticked ih =>
      have kept := (Store.onTick_frame ticked).2.2.2
      exact Store.finalized_properties_of_onTick (Origin after)
        (mono (fun _ _ h => kept.symm ▸ h) ih.1)
        (mono (fun _ _ h => kept.symm ▸ h) ih.2) ticked
    | @block before after checks sources signed reachable added ih =>
      have kept : ∀ (root : Root) (state : BeaconState preset fork),
          before.blockStates[root]? = some state → after.blockStates[root]? = some state := by
        intro root state found
        rcases Store.onBlock_same_or_insert added with same |
          ⟨newRoot, -, fresh, -, -, post, -, -, states⟩
        · exact same ▸ found
        have other : newRoot ≠ root := by
          rintro rfl
          rw [reachable.blockState_eq_none fresh] at found
          cases found
        rw [states, getElem?_insert_root]
        simpa only [other, ↓reduceIte] using found
      exact Store.finalized_properties_of_onBlock (Origin after)
        (mono kept ih.1) (mono kept ih.2)
        (fun root state found => .inr (.inl ⟨root, state, found, rfl⟩))
        (fun root state pulled found run => .inr (.inr ⟨root, state, pulled, found, run, rfl⟩))
        added
    | attestation _ attested ih =>
      unfold Store.onAttestation at attested
      simp only [bind_ok_iff] at attested
      obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
      have storedOrigin : Origin stored stored.finalizedCheckpoint ∧
          Origin stored stored.unrealizedFinalizedCheckpoint := by
        unfold Store.storeTargetCheckpointState at storing
        split at storing
        · simp only [pure, Except.pure, Except.ok.injEq] at storing
          exact storing ▸ ih
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
          obtain ⟨_, _, rfl⟩ := storing
          exact ih
      split at attested
      · simp only [pure, Except.pure, Except.ok.injEq] at attested
        subst attested
        exact storedOrigin
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested
    | attesterSlashing _ slashed ih =>
      unfold Store.onAttesterSlashing at slashed
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
      obtain ⟨_, _, rfl⟩ := slashed
      exact ih
    | payloadAttestation _ voted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
      exact ih
    | envelope _ accepted ih =>
      obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
      obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
      exact ih
    | inclusionList _ accepted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
      exact ih
  intro checkpoint same
  rcases same with rfl | rfl
  · exact both.1
  · exact both.2

/-- A cache entry is the anchor entry or the successful pull-up at its own key.

Unlike the two store fields, a non-anchor entry has no plain held-state alternative. -/
theorem Store.Reachable.unrealizedJustifications_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {key : Root} {checkpoint : Checkpoint}
    (entry : store.unrealizedJustifications[key]? = some checkpoint) :
    (SszType.hashTreeRoot anchorBlock = .ok key ∧
      checkpoint = (⟨getCurrentEpoch anchorState, key⟩ : Checkpoint)) ∨
    ∃ (state pulled : BeaconState preset fork), store.blockStates[key]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧
      checkpoint = pulled.currentJustifiedCheckpoint := by
  sorry

namespace Store

variable {store : Store preset fork}

/-- Below the slot of a block, the walk from it reaches the roots that its parent's walk reaches. -/
private theorem getAncestor_root_of_parent {root : Root} {slot : Slot}
    {block parent : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) (below : slot < block.slot) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot =
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot := by
  rw [getAncestor_step found (UInt64.not_le.mpr below) parentFound lower]
  exact getAncestor_root _ _ _

/-- A checkpoint block is the root that the walk from a pending node reaches at the epoch start. -/
private theorem getCheckpointBlock_ok_iff {root target : Root} {epoch : Epoch} :
    store.getCheckpointBlock root epoch = .ok target ↔ ∃ start,
      computeStartSlotAtEpoch preset epoch = .ok start ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ start = .ok target := by
  unfold getCheckpointBlock
  cases computeStartSlotAtEpoch preset epoch with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok start =>
    cases store.getAncestor ⟨root, .pending⟩ start <;>
      simp [Except.mapError, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- A pending node descends from the pending node of each root that its walk reaches.

Before Gloas the walk keeps the pending status, as each parent is pending then. -/
private theorem isAncestor_of_getAncestor_root (lower : store.ParentsBelow) {root target : Root}
    {slot : Slot}
    (walk : (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok target) :
    store.isAncestor ⟨root, .pending⟩ ⟨target, .pending⟩ = .ok true := by
  cases reached : store.getAncestor ⟨root, .pending⟩ slot with
  | error e => simp [reached, Functor.map, Except.map] at walk
  | ok node =>
    simp only [reached, Functor.map, Except.map, Except.ok.injEq] at walk
    subst walk
    by_cases gloas : .glamsterdam ≤ fork
    · obtain ⟨block, found, le⟩ := getAncestor_le reached
      have stops : store.getAncestor ⟨root, .pending⟩ block.slot = .ok node := by
        rw [getAncestor_trans le reached, getAncestor_of_le found (UInt64.le_refl _)]
      simp [isAncestor_pending gloas, block_ok_iff.mpr found, stops, bind, Except.bind, pure,
        Except.pure]
    · obtain ⟨-, origin, -⟩ := getAncestor_climbs (lower := lower) reached
      obtain ⟨nodeRoot, status⟩ := node
      have pending : status = .pending := by
        rcases origin with same | ⟨_, _, _, _, _, _, parentStatus, _⟩
        · cases same
          rfl
        · exact parentStatus.trans (parentPayloadStatus_of_lt (Nat.lt_of_not_le gloas))
      subst pending
      exact isAncestor_of_getAncestor reached

/-- A zero preimage on the chain of a parent is on the chain of its child. -/
private theorem zeroPreimage_of_parent {root : Root} {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot)
    (zero : ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok badRoot) :
    ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
  obtain ⟨badRoot, badState, slot, badHeld, hashed, walk⟩ := zero
  by_cases below : slot < block.slot
  · exact ⟨badRoot, badState, slot, badHeld, hashed,
      (getAncestor_root_of_parent found parentFound lower below).trans walk⟩
  · -- A walk from the parent to a slot at or above the block stays at the parent.
    rw [getAncestor_of_le parentFound
      (UInt64.le_trans (UInt64.le_of_lt lower) (UInt64.not_lt.mp below))] at walk
    simp only [Functor.map, Except.map, Except.ok.injEq] at walk
    subst walk
    refine ⟨_, badState, parent.slot, badHeld, hashed, ?_⟩
    rw [getAncestor_root_of_parent found parentFound lower lower,
      getAncestor_of_le parentFound (UInt64.le_refl _)]
    rfl

/-- A root read in a transition from a held parent state is on the chain of the new block.

The read follows the cases of the recorded roots of the transition.

An older root is read in the parent state, whose own reads are on the chain of the parent.

Otherwise the root is that of the parent, or the parent state hashes to zero. -/
private theorem Linked.getAncestor_root_of_cases {orphanParent : Root}
    (linked : store.Linked orphanParent)
    {root readRoot : Root} {block : BeaconBlock preset fork} {parent : BeaconState preset fork}
    {slot : Slot} (found : store.blocks[root]? = some block)
    (parentHeld : store.blockStates[block.parentRoot]? = some parent)
    (history : getBlockRootAtSlot parent slot = .ok readRoot →
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok readRoot ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok badRoot)
    (below : slot < block.slot)
    (cases : (slot < parent.slot ∧ getBlockRootAtSlot parent slot = .ok readRoot) ∨
      (parent.slot ≤ slot ∧ (readRoot = block.parentRoot ∨
        (SszType.hashTreeRoot parent = .ok (Vector.replicate 32 0) ∧
          SszType.hashTreeRoot parent.latestBlockHeader = .ok readRoot)))) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok readRoot ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
  obtain ⟨parentBlock, parentFound, parentLe⟩ := linked.stateAfter _ _ parentHeld
  have lower := linked.parentsBelow _ _ _ found parentFound
  rcases cases with ⟨-, read⟩ | ⟨atLeast, parentRoot | ⟨zero, -⟩⟩
  · rcases history read with walk | bad
    · exact .inl ((getAncestor_root_of_parent found parentFound lower below).trans walk)
    · exact .inr (zeroPreimage_of_parent found parentFound lower bad)
  · left
    rw [getAncestor_root_of_parent found parentFound lower below,
      getAncestor_of_le parentFound (UInt64.le_trans parentLe atLeast), parentRoot]
    rfl
  · right
    refine ⟨block.parentRoot, parent, parentBlock.slot, parentHeld, zero, ?_⟩
    rw [getAncestor_root_of_parent found parentFound lower lower,
      getAncestor_of_le parentFound (UInt64.le_refl _)]
    rfl

end Store

/-- A root that a held state reads after the anchor state is on the chain of its block.

Otherwise a held state on that chain hashes to zero. -/
private theorem Store.Reachable.getAncestor_root_of_blockState {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (linked : store.Linked anchorBlock.parentRoot)
    {root readRoot : Root} {state : BeaconState preset fork} {slot : Slot}
    (held : store.blockStates[root]? = some state)
    (read : getBlockRootAtSlot state slot = .ok readRoot) (later : anchorState.slot ≤ slot) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok readRoot ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · -- The anchor state reads no slot from its own on.
    rw [anchored same] at read
    exact absurd later (UInt64.not_le.mpr (getBlockRootAtSlot_read read).1)
  obtain ⟨parent, checks, engine, signed, message, parentHeld, transitioned⟩ := produced same
  have below : slot < block.slot := by
    rw [← message, ← (stateTransition_slot transitioned).2]
    exact (getBlockRootAtSlot_read read).1
  refine linked.getAncestor_root_of_cases found parentHeld
    (fun parentRead => reachable.getAncestor_root_of_blockState linked parentHeld parentRead later)
    below ?_
  by_cases old : slot < parent.slot
  · exact .inl ⟨old, getBlockRootAtSlot_stateTransition_of_lt transitioned old read⟩
  · refine .inr ⟨UInt64.not_lt.mp old, ?_⟩
    rw [← message]
    exact getBlockRootAtSlot_stateTransition_cases transitioned (UInt64.not_lt.mp old) read
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- The three checkpoints of a state satisfy a predicate. -/
private def CheckpointsSatisfy (p : Checkpoint → Prop) (state : BeaconState preset fork) : Prop :=
  p state.previousJustifiedCheckpoint ∧ p state.currentJustifiedCheckpoint ∧
    p state.finalizedCheckpoint

/-- A frame keeps the three checkpoints. -/
private theorem CheckpointsSatisfy.of_frame {p : Checkpoint → Prop}
    {state after : BeaconState preset fork} (holds : CheckpointsSatisfy p state)
    (frame : Frame state after) : CheckpointsSatisfy p after := by
  simpa only [CheckpointsSatisfy, frame.previousJustified, frame.currentJustified,
    frame.finalized] using holds

/-- Justification keeps old checkpoints or selects one read from the history of the state. -/
private theorem CheckpointsSatisfy.processJustification {p : Checkpoint → Prop}
    {state after : BeaconState preset fork} (holds : CheckpointsSatisfy p state)
    (reads : ∀ checkpoint,
      (checkpoint.epoch = getPreviousEpoch state ∨ checkpoint.epoch = getCurrentEpoch state) →
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root → p checkpoint)
    (computed : processJustificationAndFinalization state = .ok after) :
    CheckpointsSatisfy p after := by
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · exact holds
  · obtain ⟨previous, _, final, _⟩ := weighJustificationAndFinalization_checkpoints weighed
    refine ⟨previous ▸ holds.2.1, ?_, ?_⟩
    · rcases weighJustificationAndFinalization_currentJustified weighed with
        ⟨same, _⟩ | ⟨current, _, _, _, _, _, epoch, read⟩
      · exact same ▸ holds.2.1
      · exact reads _ (by cases current; exact .inl epoch; exact .inr epoch) read
    · rcases final with same | same | same
      · exact same ▸ holds.2.2
      · exact same ▸ holds.1
      · exact same ▸ holds.2.1

/-- A slot run selects checkpoints only by reads at its intermediate states.

Each read comes with the slots before and after its state. -/
private theorem CheckpointsSatisfy.advanceSlots {config : Config} {p : Checkpoint → Prop}
    {state after : BeaconState preset fork} {checks : SignatureChecks} {count : ℕ}
    (holds : CheckpointsSatisfy p state)
    (reads : ∀ i, i < count → ∀ middle cached,
      advanceSlots config checks i state = .ok middle →
      advanceSlots config checks (count - i) middle = .ok after →
      processSlot middle = .ok cached → ∀ checkpoint,
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) →
      getBlockRoot cached checkpoint.epoch = .ok checkpoint.root → p checkpoint)
    (computed : advanceSlots config checks count state = .ok after) :
    CheckpointsSatisfy p after := by
  induction count generalizing state after with
  | zero =>
    cases Except.ok.inj computed
    exact holds
  | succ count ih =>
    have whole := computed
    simp only [EthLib.Consensus.advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, step, rest⟩ := computed
    have nextHolds : CheckpointsSatisfy p next := by
      obtain ⟨slot, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok step
      have cachedHolds := holds.of_frame (frame_processSlot cachedOk)
      have epochedHolds : CheckpointsSatisfy p epoched := by
        unfold epochIfLast at epochedOk
        split at epochedOk
        · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
          exact (cachedHolds.processJustification
            (reads 0 (Nat.zero_lt_succ _) state cached rfl (by simpa using whole) cachedOk)
              justifiedOk).of_frame frame.toFrame
        · cases Except.ok.inj epochedOk
          exact cachedHolds
      exact epochedHolds
    apply ih nextHolds (fun i hi middle cached run more cachedOk => ?_) rest
    refine reads (i + 1) (by omega) middle cached ?_ (by rwa [Nat.add_sub_add_right]) cachedOk
    simp only [EthLib.Consensus.advanceSlots, step, bind, Except.bind]
    exact run

/-- With a two-epoch window, a slot keeps the roots of the previous and the current epoch. -/
private theorem getBlockRoot_processSlot_of_recent_epoch {state cached : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (computed : processSlot state = .ok cached) {epoch : Epoch}
    (recent : epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state) :
    getBlockRoot cached epoch = getBlockRoot state epoch := by
  apply getBlockRoot_processSlot computed
  have remainder := Nat.mod_lt state.slot.toNat positive
  have divide := Nat.mod_add_div state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [Nat.mul_comm preset.SLOTS_PER_EPOCH.toNat] at divide
  rcases recent with rfl | rfl
  · rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat]
    have subtract : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
        (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat - 1) + 1 := by omega
    have multiplied := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat subtract
    rw [Nat.add_mul, Nat.one_mul] at multiplied
    omega
  · rw [getCurrentEpoch_toNat]
    omega

/-- An epoch after the current epoch of a state starts after the slot of that state. -/
private theorem slot_le_of_getCurrentEpoch_lt {state : BeaconState preset fork} {epoch : Epoch}
    {start : Slot} (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (later : getCurrentEpoch state < epoch)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start) : state.slot ≤ start := by
  have epochLt := UInt64.lt_iff_toNat_lt.mp later
  rw [getCurrentEpoch_toNat] at epochLt
  have next := (Nat.div_lt_iff_lt_mul positive).mp epochLt
  have eq := (mulChecked_ok_iff.mp startOk).2
  exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- After the anchor epoch, each checkpoint of a held state is on the chain of its block.

Otherwise a held state on that chain hashes to zero. -/
private theorem Store.Reachable.checkpointsSatisfy_of_blockState {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (linked : store.Linked anchorBlock.parentRoot)
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state) :
    CheckpointsSatisfy (fun checkpoint => checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot) state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · -- The anchor state has no checkpoint after its own epoch.
    rw [anchored same]
    have bound := UInt64.le_trans sound.settled (getPreviousEpoch_le anchorState)
    exact ⟨.inl (UInt64.le_trans sound.ordered.2 bound), .inl bound,
      .inl (UInt64.le_trans sound.ordered.1 (UInt64.le_trans sound.ordered.2 bound))⟩
  obtain ⟨parent, checks, engine, signed, message, parentHeld, transitioned⟩ := produced same
  obtain ⟨parentBlock, parentFound, -⟩ := linked.stateAfter _ _ parentHeld
  have lower := linked.parentsBelow _ _ _ found parentFound
  have bounds := stateTransition_slot transitioned
  rw [message] at bounds
  -- A checkpoint of the parent state starts no later than that state, so below the block.
  have lift : ∀ checkpoint : Checkpoint, checkpoint.epoch ≤ getCurrentEpoch parent →
      (checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        store.getCheckpointBlock block.parentRoot checkpoint.epoch = .ok checkpoint.root ∨
        ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
          store.blockStates[badRoot]? = some badState ∧
          SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
          (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok badRoot) →
      checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∨
        ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
          store.blockStates[badRoot]? = some badState ∧
          SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
          (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
    intro checkpoint early holds
    rcases holds with old | path | bad
    · exact .inl old
    · obtain ⟨start, startOk, walk⟩ := Store.getCheckpointBlock_ok_iff.mp path
      have below : start < block.slot := by
        have eq := (mulChecked_ok_iff.mp startOk).2
        have epochLe := UInt64.le_iff_toNat_le.mp early
        rw [getCurrentEpoch_toNat] at epochLe
        have scaled := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochLe
        have floor := Nat.div_mul_le_self parent.slot.toNat preset.SLOTS_PER_EPOCH.toNat
        have earlier := UInt64.lt_iff_toNat_lt.mp bounds.1
        exact UInt64.lt_iff_toNat_lt.mpr (by omega)
      exact .inr (.inl (Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk,
        (Store.getAncestor_root_of_parent found parentFound lower below).trans walk⟩))
    · exact .inr (.inr (Store.zeroPreimage_of_parent found parentFound lower bad))
  have parentHolds :=
    reachable.checkpointsSatisfy_of_blockState sound positive window linked parentHeld
  have invariant := (reachable.ordered sound).2 parentHeld
  have currentLe := UInt64.le_trans invariant.settled (getPreviousEpoch_le parent)
  obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok transitioned
  rw [message] at blockOk advancedSlot
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, run⟩ := slotsOk
  refine CheckpointsSatisfy.of_frame (CheckpointsSatisfy.advanceSlots
    ⟨lift _ (UInt64.le_trans invariant.ordered.2 currentLe) parentHolds.1,
      lift _ currentLe parentHolds.2.1,
      lift _ (UInt64.le_trans invariant.ordered.1 (UInt64.le_trans invariant.ordered.2 currentLe))
        parentHolds.2.2⟩ ?_ run) (frame_processBlock blockOk)
  intro i _ middle cached first rest cachedOk checkpoint recent read
  by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl old
  -- A new checkpoint is read at an intermediate state of the transition.
  have recent' : checkpoint.epoch = getPreviousEpoch middle ∨
      checkpoint.epoch = getCurrentEpoch middle := by
    simpa only [getPreviousEpoch, getCurrentEpoch, processSlot_slot cachedOk] using recent
  rw [getBlockRoot_processSlot_of_recent_epoch positive window cachedOk recent'] at read
  obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp read
  have later := slot_le_of_getCurrentEpoch_lt positive (UInt64.not_le.mp old) startOk
  have below : start < block.slot := by
    have before := UInt64.lt_iff_toNat_lt.mp (getBlockRootAtSlot_read read).1
    have moved := advanceSlots_slot _ rest
    rw [advancedSlot] at moved
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  rcases linked.getAncestor_root_of_cases found parentHeld
      (fun parentRead =>
        reachable.getAncestor_root_of_blockState linked parentHeld parentRead later)
      below (getBlockRootAtSlot_advanceSlots_cases first rest blockOk read) with walk | bad
  · exact .inr (.inl (Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk, walk⟩))
  · exact .inr (.inr bad)
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- After the anchor epoch, a state checkpoint names its epoch boundary on the source chain.

The alternative exposes a held state on that chain whose hash is the zero sentinel. -/
theorem Store.Reachable.checkpoint_source_ancestor {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    {root : Root} {state view : BeaconState preset fork} {checkpoint : Checkpoint}
    (held : store.blockStates[root]? = some state)
    (selected : view = state ∨ processJustificationAndFinalization state = .ok view)
    (field : checkpoint = view.previousJustifiedCheckpoint ∨
      checkpoint = view.currentJustifiedCheckpoint ∨ checkpoint = view.finalizedCheckpoint)
    (afterAnchor : getCurrentEpoch anchorState < checkpoint.epoch) :
    (store.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) ∨
    ∃ (badRoot : Root) (badState : BeaconState preset fork),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      store.isAncestor ⟨root, .pending⟩ ⟨badRoot, .pending⟩ = .ok true := by
  -- The anchor parent is unknown, so the store keeps its blocks and states linked.
  have linked : store.Linked anchorBlock.parentRoot := by
    rcases reachable.linked anchorSlot with linked | known
    · exact linked
    · rw [Std.TreeMap.contains_eq_isSome_getElem?, unknownParent] at known
      cases known
  suffices viewHolds : CheckpointsSatisfy (fun checkpoint =>
      checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∨
        ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
          store.blockStates[badRoot]? = some badState ∧
          SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
          (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot) view by
    have fieldHolds : ∀ p : Checkpoint → Prop, CheckpointsSatisfy p view → p checkpoint := by
      intro p holds
      rcases field with rfl | rfl | rfl
      exacts [holds.1, holds.2.1, holds.2.2]
    rcases fieldHolds _ viewHolds with old | path | ⟨badRoot, badState, slot, badHeld, zero, walk⟩
    · exact absurd afterAnchor (UInt64.not_lt.mpr old)
    · obtain ⟨start, -, walk⟩ := Store.getCheckpointBlock_ok_iff.mp path
      exact .inl ⟨Store.isAncestor_of_getAncestor_root linked.parentsBelow walk, path⟩
    · exact .inr ⟨badRoot, badState, badHeld, zero,
        Store.isAncestor_of_getAncestor_root linked.parentsBelow walk⟩
  have holds := reachable.checkpointsSatisfy_of_blockState sound positive window linked held
  rcases selected with rfl | pulled
  · exact holds
  -- A pull-up reads the new checkpoint in the held state itself.
  refine holds.processJustification (fun checkpoint _ read => ?_) pulled
  by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl old
  obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp read
  rcases reachable.getAncestor_root_of_blockState linked held read
      (slot_le_of_getCurrentEpoch_lt positive (UInt64.not_le.mp old) startOk) with walk | bad
  · exact .inr (.inl (Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk, walk⟩))
  · exact .inr (.inr bad)

/-- Within one held post-state or its pull-up, finalization precedes current justification.

Checkpoints at or before the anchor epoch and a zero-hashing state are explicit alternatives. -/
theorem Store.Reachable.postState_finalized_ancestor {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    {root : Root} {state view : BeaconState preset fork}
    (held : store.blockStates[root]? = some state)
    (selected : view = state ∨ processJustificationAndFinalization state = .ok view) :
    view.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
    (store.isAncestor ⟨view.currentJustifiedCheckpoint.root, .pending⟩
        ⟨view.finalizedCheckpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock view.currentJustifiedCheckpoint.root
        view.finalizedCheckpoint.epoch = .ok view.finalizedCheckpoint.root) ∨
    ∃ (badRoot : Root) (badState : BeaconState preset fork),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      store.isAncestor ⟨root, .pending⟩ ⟨badRoot, .pending⟩ = .ok true := by
  sorry

end EthLib.Consensus
