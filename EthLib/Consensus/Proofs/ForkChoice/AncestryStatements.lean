module

public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints

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
  sorry

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
