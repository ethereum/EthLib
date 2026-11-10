module

public import EthLib.Consensus.Proofs.Transition.BuilderRequests
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.TargetFlags
public import EthLib.Consensus.Transition.Upgrade

/-!
# Proofs: the upgrades of the state

The carry-over to a later fork before Gloas keeps the registry, balances, slot and checkpoints.

After the upgrade to Altair, each list of flags and scores has one entry for each validator.

The upgrade to Electra keeps the number of validators and of balances.

The upgrade to Gloas keeps the Fulu fields, with each list unchanged as a sequence.

The latest block hash and the block hash of the latest bid are the hash of the latest payload.

The onboarding of builders changes only the builders and the queue of pending deposits.

Each pending deposit stays in the queue, funds a builder with its amount, or is dropped.

A deposit is dropped only when it has builder credentials and an invalid signature.

So the builder balances and the queue together hold at most the value of the queue before.

The upgrade of a Gloas state to Heze succeeds exactly when every contract deposit is processed.

It then keeps every Gloas field that Heze keeps, each list as the same sequence.

The latest bid differs from the Gloas bid only by its inclusion list bits, which are all unset.

Each upgrade keeps the slot, the three checkpoints and the block roots.

From Altair, an upgrade adds no target flag.

Each upgrade keeps the invariant that each valid block keeps, and the finalized checkpoint.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## Upgrade frames -/

/-- A step that keeps each byte of flags or zeroes it adds no target flag. -/
theorem TargetFlagAt.of_flagsKeptOrZero {fork : Fork} {state after : BeaconState preset fork}
    {altair : .altair ≤ fork} {current : Bool} {position : Nat}
    (kept : FlagsKeptOrZero state after)
    (flagged : TargetFlagAt (recentParticipation after altair current) position) :
    TargetFlagAt (recentParticipation state altair current) position := by
  obtain ⟨flags, found, set⟩ := flagged
  have kept := kept altair position flags
  cases current
  · rcases kept.1 found with old | rfl
    · exact ⟨flags, old, set⟩
    · exact absurd set (by decide)
  · rcases kept.2 found with old | rfl
    · exact ⟨flags, old, set⟩
    · exact absurd set (by decide)

/-- An upgrade to a fork no earlier than the fork before.

It keeps the slot, the three checkpoints, the bits of justification and the block roots.

It also keeps the genesis validators root.

The current fork version becomes the previous one, and the new one is that of the fork after.

It never shrinks the registry.

When each validator has one balance before it, each has one after it.

When each validator may withdraw no earlier than it exits before it, the same holds after it.

Let the largest effective balances of the preset be whole numbers of increments.

When each effective balance is a whole number of increments before it, the same holds after it.

From Altair, a target flag after it was a target flag at its position before. -/
structure UpgradeFrame (config : Config) {fork post : Fork} (pre : BeaconState preset fork)
    (after : BeaconState preset post) : Prop where
  forward : fork ≤ post
  slot : after.slot = pre.slot
  finalized : after.finalizedCheckpoint = pre.finalizedCheckpoint
  previousJustified : after.previousJustifiedCheckpoint = pre.previousJustifiedCheckpoint
  currentJustified : after.currentJustifiedCheckpoint = pre.currentJustifiedCheckpoint
  justificationBits : after.justificationBits = pre.justificationBits
  blockRoots : after.blockRoots = pre.blockRoots
  genesisValidatorsRoot : after.genesisValidatorsRoot = pre.genesisValidatorsRoot
  previousVersion : after.forkVersions.previousVersion = pre.forkVersions.currentVersion
  currentVersion : after.forkVersions.currentVersion = config.forkVersion post
  registryGrows : pre.validators.data.size ≤ after.validators.data.size
  balancesMatch : BalancesMatch pre → BalancesMatch after
  exitsOrdered : ExitsOrdered pre → ExitsOrdered after
  aligned : MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned pre →
    EffectiveBalancesAligned after
  flags : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation after (Nat.le_trans altair forward) current) position →
      TargetFlagAt (recentParticipation pre altair current) position

/-- An upgrade that carries the registry and both lists of flags as the same sequences.

It also keeps the number of balances. -/
theorem UpgradeFrame.of_carried {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (forward : fork ≤ post) (slot : after.slot = pre.slot)
    (finalized : after.finalizedCheckpoint = pre.finalizedCheckpoint)
    (previousJustified : after.previousJustifiedCheckpoint = pre.previousJustifiedCheckpoint)
    (currentJustified : after.currentJustifiedCheckpoint = pre.currentJustifiedCheckpoint)
    (justificationBits : after.justificationBits = pre.justificationBits)
    (blockRoots : after.blockRoots = pre.blockRoots)
    (genesisValidatorsRoot : after.genesisValidatorsRoot = pre.genesisValidatorsRoot)
    (previousVersion : after.forkVersions.previousVersion = pre.forkVersions.currentVersion)
    (currentVersion : after.forkVersions.currentVersion = config.forkVersion post)
    (validators : after.validators.data = pre.validators.data)
    (balances : after.balances.data.size = pre.balances.data.size)
    (participation : ∀ (altair : .altair ≤ fork) (current : Bool),
      (recentParticipation after (Nat.le_trans altair forward) current).data =
        (recentParticipation pre altair current).data) :
    UpgradeFrame config pre after where
  forward := forward
  slot := slot
  finalized := finalized
  previousJustified := previousJustified
  currentJustified := currentJustified
  justificationBits := justificationBits
  blockRoots := blockRoots
  genesisValidatorsRoot := genesisValidatorsRoot
  previousVersion := previousVersion
  currentVersion := currentVersion
  registryGrows := by rw [validators]; exact Nat.le_refl _
  balancesMatch holds := by
    unfold BalancesMatch at holds ⊢
    rw [balances, validators]
    exact holds
  exitsOrdered holds := by
    unfold ExitsOrdered at holds ⊢
    rw [validators]
    exact holds
  aligned _ holds := by
    unfold EffectiveBalancesAligned at holds ⊢
    rw [validators]
    exact holds
  flags altair current position flagged := by
    obtain ⟨flags, found, set⟩ := flagged
    exact ⟨flags, by rw [← participation altair current]; exact found, set⟩

/-- An upgrade frame followed by a block frame of the new fork is an upgrade frame. -/
theorem UpgradeFrame.trans_blockFrame {fork post : Fork} {pre : BeaconState preset fork}
    {middle after : BeaconState preset post} (one : UpgradeFrame config pre middle)
    (two : BlockFrame middle after) : UpgradeFrame config pre after where
  forward := one.forward
  slot := two.slot.trans one.slot
  finalized := two.finalized.trans one.finalized
  previousJustified := two.previousJustified.trans one.previousJustified
  currentJustified := two.currentJustified.trans one.currentJustified
  justificationBits := two.justificationBits.trans one.justificationBits
  blockRoots := two.blockRoots.trans one.blockRoots
  genesisValidatorsRoot := two.genesisValidatorsRoot.trans one.genesisValidatorsRoot
  previousVersion := by rw [two.forkVersions]; exact one.previousVersion
  currentVersion := by rw [two.forkVersions]; exact one.currentVersion
  registryGrows := Nat.le_trans one.registryGrows two.registryGrows
  balancesMatch := two.balancesMatch ∘ one.balancesMatch
  exitsOrdered := two.exitsOrdered ∘ one.exitsOrdered
  aligned maxAligned := two.aligned maxAligned ∘ one.aligned maxAligned
  flags altair current position flagged :=
    one.flags altair current position (flagged.of_flagsKeptOrZero two.flags)

/-- An upgrade frame carries the invariant from the state before to the state after. -/
theorem UpgradeFrame.invariant {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (frame : UpgradeFrame config pre after)
    (holds : Invariant pre) : Invariant after where
  balancesMatch := frame.balancesMatch holds.balancesMatch
  exitsOrdered := frame.exitsOrdered holds.exitsOrdered
  ordered := by
    have := holds.ordered
    unfold CheckpointsOrdered at this ⊢
    rw [frame.finalized, frame.previousJustified, frame.currentJustified]
    exact this
  settled := by
    have := holds.settled
    unfold JustifiedSettled getPreviousEpoch getCurrentEpoch at this ⊢
    rw [frame.currentJustified, frame.slot]
    exact this
  aligned maxAligned := frame.aligned maxAligned (holds.aligned maxAligned)

/-! ## The upgrades -/

/-- An upgrade before Gloas carries the registry, the balances, the slot and the checkpoints.

The fork version moves to that of the later fork at the current epoch. -/
theorem carryFields_spec {fork post : Fork} (pre : BeaconState preset fork)
    (upgrade : fork < post) (before : post < .glamsterdam) :
    (carryFields config post pre upgrade before).validators.data = pre.validators.data ∧
      (carryFields config post pre upgrade before).balances.data = pre.balances.data ∧
      (carryFields config post pre upgrade before).slot = pre.slot ∧
      (carryFields config post pre upgrade before).finalizedCheckpoint =
        pre.finalizedCheckpoint ∧
      (carryFields config post pre upgrade before).currentJustifiedCheckpoint =
        pre.currentJustifiedCheckpoint ∧
      (carryFields config post pre upgrade before).forkVersions =
        ⟨pre.forkVersions.currentVersion, config.forkVersion post, getCurrentEpoch pre⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An upgrade from Phase 0 gives each validator zero flags and a zero inactivity score. -/
theorem carryFields_of_lt_altair {fork post : Fork} (pre : BeaconState preset fork)
    (upgrade : fork < post) (before : post < .glamsterdam) (phase0 : fork < .altair)
    (altair : .altair ≤ post) :
    ((carryFields config post pre upgrade before).previousEpochParticipation altair).data =
        Array.replicate pre.validators.data.size 0 ∧
      ((carryFields config post pre upgrade before).currentEpochParticipation altair).data =
        Array.replicate pre.validators.data.size 0 ∧
      ((carryFields config post pre upgrade before).inactivityScores altair).data =
        Array.replicate pre.validators.data.size 0 := by
  have early : ¬Fork.altair ≤ fork := Nat.not_le_of_lt phase0
  simp [carryFields, early, zeroPerValidator]

/-- One translated attestation changes only the flags of the previous epoch, and keeps their count.
-/
theorem translateAttestation_spec {fork : Fork} {state after : BeaconState preset fork}
    {altair : .altair ≤ fork} {attestation : PendingAttestation preset}
    (computed : translateAttestation state altair attestation = .ok after) :
    ∃ participation : EpochParticipation preset fork,
      after = { state with previousEpochParticipation := fun _ => participation } ∧
        participation.data.size = (state.previousEpochParticipation altair).data.size := by
  simp only [translateAttestation, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, -, _, -, participation, folded, rfl⟩ := computed
  refine ⟨participation, rfl, ?_⟩
  refine foldlM_ok_invariant
    (fun (list : EpochParticipation preset fork) =>
      list.data.size = (state.previousEpochParticipation altair).data.size)
    (fun list index list' same step => ?_) rfl folded
  split at step
  · cases step
    simpa using same
  · cases step

/-- A fold of translated attestations keeps every field but the flags of the previous epoch.

Those flags keep their count. -/
theorem foldlM_translateAttestation {fork : Fork} {altair : .altair ≤ fork}
    {attestations : List (PendingAttestation preset)} {state after : BeaconState preset fork}
    (computed : attestations.foldlM (fun state attestation =>
      translateAttestation state altair attestation) state = .ok after) :
    ∃ participation : EpochParticipation preset fork,
      after = { state with previousEpochParticipation := fun _ => participation } ∧
        participation.data.size = (state.previousEpochParticipation altair).data.size := by
  refine foldlM_ok_invariant
    (fun (middle : BeaconState preset fork) => ∃ participation : EpochParticipation preset fork,
      middle = { state with previousEpochParticipation := fun _ => participation } ∧
        participation.data.size = (state.previousEpochParticipation altair).data.size)
    (fun middle attestation next holds step => ?_) ⟨_, rfl, rfl⟩ computed
  obtain ⟨participation, rfl, same⟩ := holds
  obtain ⟨participation', rfl, same'⟩ := translateAttestation_spec step
  exact ⟨participation', rfl, same'.trans same⟩

/-- The upgrade to Altair translates the pending attestations, from the carried fields.

It then sets both sync committees to one committee. -/
theorem upgradeToAltair_ok {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair} (computed : upgradeToAltair config pre = .ok after) :
    ∃ middle, (pre.previousEpochAttestations (by decide)).data.toList.foldlM
        (fun state attestation => translateAttestation state (by decide) attestation)
        (carryFields config .altair pre (by decide) (by decide)) = .ok middle ∧
      ∃ committee, after = { middle with
        currentSyncCommittee := fun _ => committee, nextSyncCommittee := fun _ => committee } := by
  simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨middle, folded, _, -, rfl⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact ⟨middle, folded, _, rfl⟩

private theorem upgradeToAltair_frame_spec {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair} (computed : upgradeToAltair config pre = .ok after) :
    UpgradeFrame config pre after ∧
    after.validators.data = pre.validators.data ∧ after.balances.data = pre.balances.data ∧
      (after.previousEpochParticipation (by decide)).data.size = pre.validators.data.size ∧
      (after.currentEpochParticipation (by decide)).data.size = pre.validators.data.size ∧
      (after.inactivityScores (by decide)).data.size = pre.validators.data.size ∧
      after.currentSyncCommittee (by decide) = after.nextSyncCommittee (by decide) ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.ALTAIR_FORK_VERSION, getCurrentEpoch pre⟩ := by
  obtain ⟨_, folded, _, rfl⟩ := upgradeToAltair_ok computed
  obtain ⟨participation, rfl, same⟩ := foldlM_translateAttestation folded
  obtain ⟨previous, current, scores⟩ := carryFields_of_lt_altair (config := config)
    (post := .altair) pre (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      fun altair => absurd altair (by decide)
  · show participation.data.size = _
    rw [same, previous, Array.size_replicate]
  · show (_ : EpochParticipation preset .altair).data.size = _
    rw [current, Array.size_replicate]
  · show (_ : InactivityScores preset .altair).data.size = _
    rw [scores, Array.size_replicate]

/-- The upgrade to Altair keeps the registry and the balances.

Each list of flags and of inactivity scores has one entry for each validator.

Both sync committees are the same committee, and the fork version moves to Altair. -/
theorem upgradeToAltair_spec {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair} (computed : upgradeToAltair config pre = .ok after) :
    after.validators.data = pre.validators.data ∧ after.balances.data = pre.balances.data ∧
      (after.previousEpochParticipation (by decide)).data.size = pre.validators.data.size ∧
      (after.currentEpochParticipation (by decide)).data.size = pre.validators.data.size ∧
      (after.inactivityScores (by decide)).data.size = pre.validators.data.size ∧
      after.currentSyncCommittee (by decide) = after.nextSyncCommittee (by decide) ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.ALTAIR_FORK_VERSION, getCurrentEpoch pre⟩ :=
  (upgradeToAltair_frame_spec computed).2

/-- What each step of the Electra upgrade keeps.

It keeps the number of validators and of balances, the fork versions and the deposit start index.
-/
def ElectraKept {fork : Fork} (state after : BeaconState preset fork) : Prop :=
  SameSizes state after ∧ after.forkVersions = state.forkVersions ∧
    after.depositRequestsStartIndex = state.depositRequestsStartIndex

theorem ElectraKept.trans {fork : Fork} {first second third : BeaconState preset fork}
    (one : ElectraKept first second) (two : ElectraKept second third) :
    ElectraKept first third :=
  ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.trans one.2.2⟩

theorem electraKept_queuePreActivation {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : ElectraKept state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, -, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  have sizes₁ := sameSizes_setBalance set₁
  have sizes₂ := sameSizes_setValidator set₂
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨_, rfl⟩ := setValidator_ok set₂
  exact ⟨sizes₁.trans (sizes₂.trans ⟨rfl, rfl⟩), rfl, rfl⟩

theorem electraKept_queueCompoundingExcess {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    ElectraKept state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      refine ⟨sameSizes_queueExcessActiveBalance queued, ?_⟩
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok set
        exact ⟨rfl, rfl⟩
      · cases queued
        exact ⟨rfl, rfl⟩
    · cases computed
      exact ⟨SameSizes.refl _, rfl, rfl⟩
  · cases computed
    exact ⟨SameSizes.refl _, rfl, rfl⟩

/-- Queueing a validator that is not yet active changes no exit epoch.

It keeps the block roots, and keeps each byte of flags or zeroes it. -/
theorem frame_queuePreActivation {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    BlockFrame state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  have sizes := sameSizes_setBalance set₁
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  have zeroed := BlockFrame.of_validators sizes
  have reset := frame_setValidator_of_whole set₂
    (fun ordered => ordered validator (mem_of_getValidator found)) fun _ _ => UInt64.zero_mod
  exact (zeroed.trans reset.toBlockFrame).trans (BlockFrame.of_validators ⟨rfl, rfl⟩)

/-- Queueing the excess balance of a validator with compounding credentials keeps the frame.

It keeps the block roots, and keeps each byte of flags or zeroes it. -/
theorem frame_queueCompoundingExcess {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    BlockFrame state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · exact frame_queueExcessActiveBalance (liftAccessor_ok.mp computed)
    · cases computed
      exact BlockFrame.refl _
  · cases computed
    exact BlockFrame.refl _

private theorem upgradeToElectra_frame_spec {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    UpgradeFrame config pre after ∧
    after.validators.data.size = pre.validators.data.size ∧
      after.balances.data.size = pre.balances.data.size ∧
      after.depositRequestsStartIndex (by decide) = UNSET_DEPOSIT_REQUESTS_START_INDEX ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.ELECTRA_FORK_VERSION, getCurrentEpoch pre⟩ := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := computed
  have frame : UpgradeFrame config pre after := by
    refine ((UpgradeFrame.trans_blockFrame ?_
      (BlockFrame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued)).trans_blockFrame
      (BlockFrame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok) compounded))
    have altair : Fork.altair ≤ Fork.dencun := by decide
    exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      fun _ current => by cases current <;>
        simp [recentParticipation, carryFields, carryList, altair]
  have first := foldlM_ok_invariant (ElectraKept _)
    (fun _ _ _ before step => before.trans (electraKept_queuePreActivation step))
    ⟨SameSizes.refl _, rfl, rfl⟩ queued
  have kept := foldlM_ok_invariant (ElectraKept _)
    (fun _ _ _ before step => before.trans (electraKept_queueCompoundingExcess step))
    first compounded
  obtain ⟨⟨validators, balances⟩, versions, start⟩ := kept
  exact ⟨frame, validators, balances, congrFun start _, versions⟩

/-- The upgrade to Electra keeps the number of validators and of balances.

The index of the first deposit request starts unset, and the fork version moves to Electra. -/
theorem upgradeToElectra_spec {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    after.validators.data.size = pre.validators.data.size ∧
      after.balances.data.size = pre.balances.data.size ∧
      after.depositRequestsStartIndex (by decide) = UNSET_DEPOSIT_REQUESTS_START_INDEX ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.ELECTRA_FORK_VERSION, getCurrentEpoch pre⟩ :=
  (upgradeToElectra_frame_spec computed).2

private theorem upgradeToFulu_frame_spec {pre : BeaconState preset .pectra}
    {after : BeaconState preset .fusaka} (computed : upgradeToFulu config pre = .ok after) :
    UpgradeFrame config pre after ∧
    after.validators.data = pre.validators.data ∧ after.balances.data = pre.balances.data ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.FULU_FORK_VERSION, getCurrentEpoch pre⟩ := by
  simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, -, rfl⟩ := computed
  have altair : Fork.altair ≤ Fork.pectra := by decide
  refine ⟨?_, rfl, rfl, rfl⟩
  exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> simp [recentParticipation, carryFields, carryList, altair]

/-- The upgrade to Fulu keeps the registry and the balances.

The fork version moves to Fulu. -/
theorem upgradeToFulu_spec {pre : BeaconState preset .pectra}
    {after : BeaconState preset .fusaka} (computed : upgradeToFulu config pre = .ok after) :
    after.validators.data = pre.validators.data ∧ after.balances.data = pre.balances.data ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.FULU_FORK_VERSION, getCurrentEpoch pre⟩ :=
  (upgradeToFulu_frame_spec computed).2

/-- The upgrade carries the registry, the balances and the queues as the same sequences. -/
theorem upgradeFields_lists (pre : BeaconState preset .fusaka) (requestsRoot : Root) :
    (upgradeFields config pre requestsRoot).validators.data = pre.validators.data ∧
      (upgradeFields config pre requestsRoot).balances.data = pre.balances.data ∧
      ((upgradeFields config pre requestsRoot).pendingDeposits (by decide)).data =
        (pre.pendingDeposits (by decide)).data ∧
      ((upgradeFields config pre requestsRoot).pendingPartialWithdrawals (by decide)).data =
        (pre.pendingPartialWithdrawals (by decide)).data ∧
      ((upgradeFields config pre requestsRoot).pendingConsolidations (by decide)).data =
        (pre.pendingConsolidations (by decide)).data ∧
      (upgradeFields config pre requestsRoot).proposerLookahead (by decide) =
        pre.proposerLookahead (by decide) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The latest block hash and the latest bid's block hash are the latest payload's hash.

The fork version moves to Gloas at the current epoch, and the Fulu version becomes the previous one.
-/
theorem upgradeFields_payload (pre : BeaconState preset .fusaka) (requestsRoot : Root) :
    (upgradeFields config pre requestsRoot).latestBlockHash (by decide) =
        (pre.latestExecutionPayloadHeader (by decide)).blockHash ∧
      ((upgradeFields config pre requestsRoot).latestExecutionPayloadBid (by decide)).blockHash =
        (pre.latestExecutionPayloadHeader (by decide)).blockHash ∧
      (upgradeFields config pre requestsRoot).forkVersions =
        ⟨pre.forkVersions.currentVersion, config.GLOAS_FORK_VERSION, getCurrentEpoch pre⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- One pending deposit stays in the queue, funds a builder with its amount, or is dropped.

It is dropped only when it has builder credentials and an invalid signature.

Every field of the state but the builders stays. -/
theorem onboardDeposit_cases {validatorKeys : List BLSPubkey}
    {state after : BeaconState preset .glamsterdam} {kept kept' : Array PendingDeposit}
    {deposit : PendingDeposit}
    (computed : onboardDeposit config checks validatorKeys (state, kept) deposit =
      .ok (after, kept')) :
    (after = state ∧ kept' = kept.push deposit) ∨
      (kept' = kept ∧ builderBalanceSum after (by decide) =
        builderBalanceSum state (by decide) + deposit.amount.toNat ∧
        ∃ builders, after = { state with builders := builders }) ∨
      (after = state ∧ kept' = kept ∧
        isBuilderWithdrawalCredential deposit.withdrawalCredentials = true ∧
        isValidDepositSignature config checks deposit.pubkey deposit.withdrawalCredentials
          deposit.amount deposit.signature = .ok false) := by
  dsimp only [onboardDeposit] at computed
  split at computed
  · cases computed
    exact .inl ⟨rfl, rfl⟩
  split at computed
  · -- A known builder adds the amount to its balance.
    rename_i index _
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp computed
    obtain ⟨balance, summed, rest⟩ := bind_ok_iff.mp computed
    rw [liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at summed
    cases rest
    refine .inr (.inl ⟨rfl, ?_, _, rfl⟩)
    have := builderBalanceSum_putBuilder (state := state) (gloas := by decide)
      (builder := { (state.builders (by decide)).data[index] with balance }) index.isLt
    simp only [Fin.getElem_fin] at summed this ⊢
    omega
  split at computed
  · cases computed
    exact .inl ⟨rfl, rfl⟩
  rename_i _ credential
  obtain ⟨pending, -, rest⟩ := bind_ok_iff.mp computed
  split at rest
  · cases rest
    exact .inl ⟨rfl, rfl⟩
  obtain ⟨valid, checked, rest⟩ := bind_ok_iff.mp rest
  split at rest
  · -- A new key with a valid signature becomes a builder.
    obtain ⟨_, added, rest⟩ := bind_ok_iff.mp rest
    cases rest
    refine .inr (.inl ⟨rfl, builderBalanceSum_addBuilderToRegistry added, ?_⟩)
    simp only [addBuilderToRegistry, bind_ok_iff] at added
    obtain ⟨_, _, added⟩ := added
    split at added
    · cases added
      exact ⟨_, rfl⟩
    · cases added
      exact ⟨_, rfl⟩
  · cases rest
    rename_i invalid
    simp only [Bool.not_eq_true] at invalid
    subst invalid
    refine .inr (.inr ⟨rfl, rfl, ?_, checked⟩)
    simpa using credential

/-- A fold of the onboarding over some pending deposits changes only the builders of the state.

The builder balances and the queue then hold at most their value plus the deposits folded. -/
theorem foldlM_onboardDeposit {validatorKeys : List BLSPubkey} :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset .glamsterdam}
      {kept kept' : Array PendingDeposit},
      deposits.foldlM (onboardDeposit config checks validatorKeys) (state, kept) =
          .ok (after, kept') →
      (∃ builders, after = { state with builders := builders }) ∧
        builderBalanceSum after (by decide) + pendingAmount kept'.toList ≤
          builderBalanceSum state (by decide) + pendingAmount kept.toList +
            pendingAmount deposits := by
  intro deposits
  induction deposits with
  | nil =>
    intro state after kept kept' folded
    cases folded
    exact ⟨⟨_, rfl⟩, by simp [pendingAmount]⟩
  | cons deposit rest ih =>
    intro state after kept kept' folded
    rw [List.foldlM_cons] at folded
    obtain ⟨⟨middle, middleKept⟩, step, folded⟩ := bind_ok_iff.mp folded
    obtain ⟨⟨builders, rfl⟩, bound⟩ := ih folded
    have amounts : pendingAmount (deposit :: rest) =
        deposit.amount.toNat + pendingAmount rest := by simp [pendingAmount]
    rcases onboardDeposit_cases step with ⟨rfl, rfl⟩ | ⟨rfl, funded, builders', rfl⟩ |
        ⟨rfl, rfl, -⟩
    · refine ⟨⟨_, rfl⟩, ?_⟩
      have pushed : pendingAmount (kept.push deposit).toList =
          pendingAmount kept.toList + deposit.amount.toNat := by simp [pendingAmount]
      simp only [builderBalanceSum] at bound ⊢
      omega
    · refine ⟨⟨_, rfl⟩, ?_⟩
      simp only [builderBalanceSum] at bound funded ⊢
      omega
    · refine ⟨⟨_, rfl⟩, ?_⟩
      simp only [builderBalanceSum] at bound ⊢
      omega

/-- The onboarding changes only the builders and the queue of pending deposits.

The builder balances and the queue together hold at most the value they held before. -/
theorem onboardBuildersFromPendingDeposits_spec {state after : BeaconState preset .glamsterdam}
    (computed : onboardBuildersFromPendingDeposits config checks state = .ok after) :
    (∃ builders pendingDeposits,
        after = { state with builders := builders, pendingDeposits := pendingDeposits }) ∧
      builderBalanceSum after (by decide) +
          pendingAmount ((after.pendingDeposits (by decide)).data.toList) ≤
        builderBalanceSum state (by decide) +
          pendingAmount ((state.pendingDeposits (by decide)).data.toList) := by
  unfold onboardBuildersFromPendingDeposits at computed
  obtain ⟨⟨folded, kept⟩, foldedOk, rest⟩ := bind_ok_iff.mp computed
  cases rest
  rw [← Array.foldlM_toList] at foldedOk
  obtain ⟨⟨builders, rfl⟩, bound⟩ := foldlM_onboardDeposit foldedOk
  refine ⟨⟨builders, _, rfl⟩, ?_⟩
  simp only [builderBalanceSum, pendingAmount] at bound ⊢
  simpa using bound

private theorem upgradeToGloas_frame_spec {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok after) :
    UpgradeFrame config pre after ∧
    after.validators.data = pre.validators.data ∧ after.balances.data = pre.balances.data ∧
      after.latestBlockHash (by decide) =
        (pre.latestExecutionPayloadHeader (by decide)).blockHash ∧
      (after.latestExecutionPayloadBid (by decide)).blockHash =
        (pre.latestExecutionPayloadHeader (by decide)).blockHash ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.GLOAS_FORK_VERSION, getCurrentEpoch pre⟩ := by
  unfold upgradeToGloas at computed
  obtain ⟨root, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
  obtain ⟨⟨builders, pending, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> rfl

/-- The upgrade of a Fulu state keeps its registry and balances, and the hash of its payload.

The latest block hash and the latest bid's block hash are both the hash of the latest payload.
-/
theorem upgradeToGloas_spec {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok after) :
    after.validators.data = pre.validators.data ∧ after.balances.data = pre.balances.data ∧
      after.latestBlockHash (by decide) =
        (pre.latestExecutionPayloadHeader (by decide)).blockHash ∧
      (after.latestExecutionPayloadBid (by decide)).blockHash =
        (pre.latestExecutionPayloadHeader (by decide)).blockHash ∧
      after.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.GLOAS_FORK_VERSION, getCurrentEpoch pre⟩ :=
  (upgradeToGloas_frame_spec computed).2

/-- The upgrade to Gloas starts with no pending payment and no pending withdrawal of a builder.

The latest bid of the upgraded state has no value. -/
theorem upgradeToGloas_builderFields {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok after) :
    (after.builderPendingPayments (by decide)).elements = Vector.replicate _ .empty ∧
      (after.builderPendingWithdrawals (by decide)).data = #[] ∧
      (after.latestExecutionPayloadBid (by decide)).value = 0 := by
  unfold upgradeToGloas at computed
  obtain ⟨root, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
  obtain ⟨⟨builders, pending, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
  exact ⟨rfl, rfl, rfl⟩

/-- The upgraded bid keeps every field of the Gloas bid, and sets no inclusion list bit. -/
theorem upgradeBidToHeze_spec (bid : ExecutionPayloadBid preset .glamsterdam) :
    (upgradeBidToHeze bid).parentBlockHash = bid.parentBlockHash ∧
      (upgradeBidToHeze bid).parentBlockRoot = bid.parentBlockRoot ∧
      (upgradeBidToHeze bid).blockHash = bid.blockHash ∧
      (upgradeBidToHeze bid).prevRandao = bid.prevRandao ∧
      (upgradeBidToHeze bid).feeRecipient = bid.feeRecipient ∧
      (upgradeBidToHeze bid).gasLimit = bid.gasLimit ∧
      (upgradeBidToHeze bid).builderIndex = bid.builderIndex ∧
      (upgradeBidToHeze bid).slot = bid.slot ∧
      (upgradeBidToHeze bid).value = bid.value ∧
      (upgradeBidToHeze bid).executionPayment = bid.executionPayment ∧
      (upgradeBidToHeze bid).blobKzgCommitments.data = bid.blobKzgCommitments.data ∧
      (upgradeBidToHeze bid).executionRequestsRoot = bid.executionRequestsRoot ∧
      ∀ i : Fin preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat,
        ((upgradeBidToHeze bid).inclusionListBits (by decide)).bits[i] = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i => ?_⟩
  simp [upgradeBidToHeze]

/-- Two Gloas bids with the same upgraded bid are equal. -/
theorem upgradeBidToHeze_injective :
    Function.Injective (upgradeBidToHeze (preset := preset)) := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, ⟨data, bound⟩, _, bits⟩
    ⟨_, _, _, _, _, _, _, _, _, _, ⟨data', bound'⟩, _, bits'⟩ same
  simp only [upgradeBidToHeze, toHezeList] at same
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := same
  -- Before Heze the bits field holds nothing, so the two functions are equal.
  have : bits = bits' := funext fun later => absurd later (by decide)
  subst this
  rfl

/-- The upgrade to Heze carries the registry, the balances, the scores and the queues.

Each list keeps its elements, in order. -/
theorem upgradeHezeFields_lists (pre : BeaconState preset .glamsterdam) :
    (upgradeHezeFields config pre).validators.data = pre.validators.data ∧
      (upgradeHezeFields config pre).balances.data = pre.balances.data ∧
      ((upgradeHezeFields config pre).previousEpochParticipation (by decide)).data =
        (pre.previousEpochParticipation (by decide)).data ∧
      ((upgradeHezeFields config pre).currentEpochParticipation (by decide)).data =
        (pre.currentEpochParticipation (by decide)).data ∧
      ((upgradeHezeFields config pre).inactivityScores (by decide)).data =
        (pre.inactivityScores (by decide)).data ∧
      ((upgradeHezeFields config pre).pendingDeposits (by decide)).data =
        (pre.pendingDeposits (by decide)).data ∧
      ((upgradeHezeFields config pre).pendingPartialWithdrawals (by decide)).data =
        (pre.pendingPartialWithdrawals (by decide)).data ∧
      ((upgradeHezeFields config pre).pendingConsolidations (by decide)).data =
        (pre.pendingConsolidations (by decide)).data ∧
      ((upgradeHezeFields config pre).payloadExpectedWithdrawals (by decide)).data =
        (pre.payloadExpectedWithdrawals (by decide)).data :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The upgrade to Heze keeps every field of a Gloas state whose type does not change.

The fork version moves to Heze at the current epoch.

The Gloas version becomes the previous one. -/
theorem upgradeHezeFields_kept (pre : BeaconState preset .glamsterdam) :
    let post := upgradeHezeFields config pre
    post.genesisTime = pre.genesisTime ∧
      post.genesisValidatorsRoot = pre.genesisValidatorsRoot ∧ post.slot = pre.slot ∧
      post.forkVersions =
        ⟨pre.forkVersions.currentVersion, config.HEZE_FORK_VERSION, getCurrentEpoch pre⟩ ∧
      post.latestBlockHeader = pre.latestBlockHeader ∧ post.blockRoots = pre.blockRoots ∧
      post.stateRoots = pre.stateRoots ∧ post.historicalRoots = pre.historicalRoots ∧
      post.randaoMixes = pre.randaoMixes ∧ post.slashings = pre.slashings ∧
      post.justificationBits = pre.justificationBits ∧
      post.previousJustifiedCheckpoint = pre.previousJustifiedCheckpoint ∧
      post.currentJustifiedCheckpoint = pre.currentJustifiedCheckpoint ∧
      post.finalizedCheckpoint = pre.finalizedCheckpoint ∧
      post.currentSyncCommittee (by decide) = pre.currentSyncCommittee (by decide) ∧
      post.nextSyncCommittee (by decide) = pre.nextSyncCommittee (by decide) ∧
      post.latestBlockHash (by decide) = pre.latestBlockHash (by decide) ∧
      post.nextWithdrawalIndex (by decide) = pre.nextWithdrawalIndex (by decide) ∧
      post.nextWithdrawalValidatorIndex (by decide) =
        pre.nextWithdrawalValidatorIndex (by decide) ∧
      post.historicalSummaries (by decide) = pre.historicalSummaries (by decide) ∧
      post.depositBalanceToConsume (by decide) = pre.depositBalanceToConsume (by decide) ∧
      post.exitBalanceToConsume (by decide) = pre.exitBalanceToConsume (by decide) ∧
      post.earliestExitEpoch (by decide) = pre.earliestExitEpoch (by decide) ∧
      post.consolidationBalanceToConsume (by decide) =
        pre.consolidationBalanceToConsume (by decide) ∧
      post.earliestConsolidationEpoch (by decide) = pre.earliestConsolidationEpoch (by decide) ∧
      post.proposerLookahead (by decide) = pre.proposerLookahead (by decide) ∧
      post.builders (by decide) = pre.builders (by decide) ∧
      post.nextWithdrawalBuilderIndex (by decide) = pre.nextWithdrawalBuilderIndex (by decide) ∧
      post.executionPayloadAvailability (by decide) =
        pre.executionPayloadAvailability (by decide) ∧
      post.builderPendingPayments (by decide) = pre.builderPendingPayments (by decide) ∧
      post.builderPendingWithdrawals (by decide) = pre.builderPendingWithdrawals (by decide) ∧
      post.latestExecutionPayloadBid (by decide) =
        upgradeBidToHeze (pre.latestExecutionPayloadBid (by decide)) ∧
      post.ptcWindow (by decide) = pre.ptcWindow (by decide) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The upgrade to Heze succeeds exactly when the two deposit indices are equal.

The first counts the processed deposits, and the second is the index of the first deposit request.

The result is then the state with the carried fields. -/
theorem upgradeToHeze_ok_iff {pre : BeaconState preset .glamsterdam}
    {post : BeaconState preset .hegota} :
    upgradeToHeze config pre = .ok post ↔
      pre.eth1DepositIndex (by decide) = pre.depositRequestsStartIndex (by decide) ∧
        post = upgradeHezeFields config pre := by
  simp only [upgradeToHeze, bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨_, equal, rfl⟩
    exact ⟨equal, rfl⟩
  · rintro ⟨equal, rfl⟩
    exact ⟨(), equal, rfl⟩

/-- The upgrade to Heze fails exactly when the two deposit indices differ, with both indices. -/
theorem upgradeToHeze_error_iff {pre : BeaconState preset .glamsterdam}
    {error : TransitionError} :
    upgradeToHeze config pre = .error error ↔
      pre.eth1DepositIndex (by decide) ≠ pre.depositRequestsStartIndex (by decide) ∧
        error = .depositIndicesDiffer (pre.eth1DepositIndex (by decide))
          (pre.depositRequestsStartIndex (by decide)) := by
  dsimp only [upgradeToHeze, ensure]
  by_cases equal : pre.eth1DepositIndex (by decide) = pre.depositRequestsStartIndex (by decide)
  · simp [equal, bind, Except.bind, pure, Except.pure]
  · simp [equal, bind, Except.bind, eq_comm]

/-! ## Each upgrade is an upgrade frame -/

/-- An upgrade that carries the fields before Gloas is an upgrade frame. -/
theorem upgradeFrame_carryFields {fork post : Fork} (pre : BeaconState preset fork)
    (upgrade : fork < post) (before : post < .glamsterdam) :
    UpgradeFrame config pre (carryFields config post pre upgrade before) :=
  UpgradeFrame.of_carried (Nat.le_of_lt upgrade) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    fun altair current => by
      cases current <;> simp [recentParticipation, carryFields, altair, carryList]

/-- The upgrade to Altair is an upgrade frame, with no flags before it to keep. -/
theorem upgradeFrame_upgradeToAltair {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair} (computed : upgradeToAltair config pre = .ok after) :
    UpgradeFrame config pre after :=
  (upgradeToAltair_frame_spec computed).1

/-- The upgrade to Electra is an upgrade frame. -/
theorem upgradeFrame_upgradeToElectra {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    UpgradeFrame config pre after :=
  (upgradeToElectra_frame_spec computed).1

/-- The upgrade to Fulu is an upgrade frame. -/
theorem upgradeFrame_upgradeToFulu {pre : BeaconState preset .pectra}
    {after : BeaconState preset .fusaka} (computed : upgradeToFulu config pre = .ok after) :
    UpgradeFrame config pre after :=
  (upgradeToFulu_frame_spec computed).1

/-- The upgrade to Gloas is an upgrade frame. -/
theorem upgradeFrame_upgradeToGloas {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok after) : UpgradeFrame config pre after :=
  (upgradeToGloas_frame_spec computed).1

/-- The upgrade to Heze is an upgrade frame. -/
theorem upgradeFrame_upgradeToHeze {pre : BeaconState preset .glamsterdam}
    {after : BeaconState preset .hegota} (computed : upgradeToHeze config pre = .ok after) :
    UpgradeFrame config pre after := by
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp computed
  exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> rfl

/-! ## The invariant across an upgrade -/

/-- A carry-over upgrade before Gloas keeps the invariant and the finalized checkpoint. -/
theorem carryFields_invariant {fork post : Fork} {pre : BeaconState preset fork}
    (upgrade : fork < post) (before : post < .glamsterdam) (holds : Invariant pre) :
    Invariant (carryFields config post pre upgrade before) ∧
      (carryFields config post pre upgrade before).finalizedCheckpoint = pre.finalizedCheckpoint :=
  have frame := upgradeFrame_carryFields (config := config) pre upgrade before
  ⟨frame.invariant holds, frame.finalized⟩

/-- The upgrade to Altair keeps the invariant and the finalized checkpoint. -/
theorem upgradeToAltair_invariant {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair} (holds : Invariant pre)
    (computed : upgradeToAltair config pre = .ok after) :
    Invariant after ∧ after.finalizedCheckpoint = pre.finalizedCheckpoint := by
  have frame := upgradeFrame_upgradeToAltair computed
  exact ⟨frame.invariant holds, frame.finalized⟩

/-- The upgrade to Electra keeps the invariant and the finalized checkpoint.

It moves no exit epoch, and keeps one balance for each validator. -/
theorem upgradeToElectra_invariant {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (holds : Invariant pre)
    (computed : upgradeToElectra config pre = .ok after) :
    Invariant after ∧ after.finalizedCheckpoint = pre.finalizedCheckpoint := by
  have frame := upgradeFrame_upgradeToElectra computed
  exact ⟨frame.invariant holds, frame.finalized⟩

/-- The upgrade to Fulu keeps the invariant and the finalized checkpoint. -/
theorem upgradeToFulu_invariant {pre : BeaconState preset .pectra}
    {after : BeaconState preset .fusaka} (holds : Invariant pre)
    (computed : upgradeToFulu config pre = .ok after) :
    Invariant after ∧ after.finalizedCheckpoint = pre.finalizedCheckpoint := by
  have frame := upgradeFrame_upgradeToFulu computed
  exact ⟨frame.invariant holds, frame.finalized⟩

/-- The upgrade to Gloas keeps the invariant and the finalized checkpoint.

The onboarding of builders changes only the builders and the queue of pending deposits. -/
theorem upgradeToGloas_invariant {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam} (holds : Invariant pre)
    (computed : upgradeToGloas config checks pre = .ok after) :
    Invariant after ∧ after.finalizedCheckpoint = pre.finalizedCheckpoint := by
  have frame := upgradeFrame_upgradeToGloas computed
  exact ⟨frame.invariant holds, frame.finalized⟩

/-- The upgrade to Heze keeps the invariant and the finalized checkpoint. -/
theorem upgradeToHeze_invariant {pre : BeaconState preset .glamsterdam}
    {after : BeaconState preset .hegota} (holds : Invariant pre)
    (computed : upgradeToHeze config pre = .ok after) :
    Invariant after ∧ after.finalizedCheckpoint = pre.finalizedCheckpoint := by
  have frame := upgradeFrame_upgradeToHeze computed
  exact ⟨frame.invariant holds, frame.finalized⟩

end EthLib.Consensus
