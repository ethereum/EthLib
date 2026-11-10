module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.TargetSlots
public import EthLib.Consensus.Proofs.Transition.Upgrade

/-!
# Proofs: the target flags across the fork upgrades

From Altair each target flag of the state comes from a signed vote for the link of its epoch.

Each upgrade from Altair on keeps that.

It carries the slot, the justified checkpoints, the block roots and the flags of both epochs.

It also carries the genesis validators root and the key of each validator.

So a vote for the link of a flag stays a vote for that link, and stays signed.

The upgrade moves the current fork version into the previous one.

The current version becomes that of the new fork.

So the two versions stay versions of forks of the chain, up to the fork of the state.

A vote stays signed under the version of the fork it was signed in.

The upgrade from Phase 0 builds the flags from the pending attestations, and is not covered here.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- An upgrade to a fork no earlier than the fork before.

It keeps the slot, the justified checkpoints, the block roots and the genesis validators root.

The current fork version becomes the previous one, and the new one is that of the fork after.

It never shrinks the registry, and keeps the keys while the registry stays below 2^64 validators.

From Altair, each byte of flags after it with the target flag is the byte at its position before. -/
structure UpgradeFrame (config : Config) {fork post : Fork} (pre : BeaconState preset fork)
    (after : BeaconState preset post) : Prop where
  forward : fork ≤ post
  slot : after.slot = pre.slot
  previousJustified : after.previousJustifiedCheckpoint = pre.previousJustifiedCheckpoint
  currentJustified : after.currentJustifiedCheckpoint = pre.currentJustifiedCheckpoint
  blockRoots : after.blockRoots = pre.blockRoots
  genesisValidatorsRoot : after.genesisValidatorsRoot = pre.genesisValidatorsRoot
  previousVersion : after.forkVersions.previousVersion = pre.forkVersions.currentVersion
  currentVersion : after.forkVersions.currentVersion = config.forkVersion post
  registryGrows : pre.validators.data.size ≤ after.validators.data.size
  keysKept : after.validators.data.size < 2 ^ 64 → KeysKept pre after
  flags : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation after (Nat.le_trans altair forward) current) position →
      TargetFlagAt (recentParticipation pre altair current) position

/-- An upgrade that carries the registry and both lists of flags as the same sequences. -/
theorem UpgradeFrame.of_carried {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (forward : fork ≤ post) (slot : after.slot = pre.slot)
    (previousJustified : after.previousJustifiedCheckpoint = pre.previousJustifiedCheckpoint)
    (currentJustified : after.currentJustifiedCheckpoint = pre.currentJustifiedCheckpoint)
    (blockRoots : after.blockRoots = pre.blockRoots)
    (genesisValidatorsRoot : after.genesisValidatorsRoot = pre.genesisValidatorsRoot)
    (previousVersion : after.forkVersions.previousVersion = pre.forkVersions.currentVersion)
    (currentVersion : after.forkVersions.currentVersion = config.forkVersion post)
    (validators : after.validators.data = pre.validators.data)
    (participation : ∀ (altair : .altair ≤ fork) (current : Bool),
      (recentParticipation after (Nat.le_trans altair forward) current).data =
        (recentParticipation pre altair current).data) :
    UpgradeFrame config pre after where
  forward := forward
  slot := slot
  previousJustified := previousJustified
  currentJustified := currentJustified
  blockRoots := blockRoots
  genesisValidatorsRoot := genesisValidatorsRoot
  previousVersion := previousVersion
  currentVersion := currentVersion
  registryGrows := by rw [validators]; exact Nat.le_refl _
  keysKept _ index validator found := ⟨validator, by
    unfold getValidator at found ⊢
    rw [validators]
    exact found, rfl⟩
  flags altair current position flagged := by
    obtain ⟨flags, found, set⟩ := flagged
    exact ⟨flags, by rw [← participation altair current]; exact found, set⟩

/-- An upgrade followed by a block frame of the new fork is an upgrade. -/
theorem UpgradeFrame.trans_blockFrame {fork post : Fork} {pre : BeaconState preset fork}
    {middle after : BeaconState preset post} (one : UpgradeFrame config pre middle)
    (two : BlockFrame middle after) : UpgradeFrame config pre after where
  forward := one.forward
  slot := two.slot.trans one.slot
  previousJustified := two.previousJustified.trans one.previousJustified
  currentJustified := two.currentJustified.trans one.currentJustified
  blockRoots := two.blockRoots.trans one.blockRoots
  genesisValidatorsRoot := two.genesisValidatorsRoot.trans one.genesisValidatorsRoot
  previousVersion := by rw [two.forkVersions]; exact one.previousVersion
  currentVersion := by rw [two.forkVersions]; exact one.currentVersion
  registryGrows := Nat.le_trans one.registryGrows two.registryGrows
  keysKept small :=
    (one.keysKept (Nat.lt_of_le_of_lt two.registryGrows small)).trans (two.keysKept small)
  flags altair current position flagged := by
    apply one.flags altair current position
    obtain ⟨flags, found, set⟩ := flagged
    have kept := two.flags (Nat.le_trans altair one.forward) position flags
    cases current
    · rcases kept.1 found with old | rfl
      · exact ⟨flags, old, set⟩
      · exact absurd set (by decide)
    · rcases kept.2 found with old | rfl
      · exact ⟨flags, old, set⟩
      · exact absurd set (by decide)

/-! ## What an upgrade keeps -/

/-- A vote for a link is one in a state of another fork with the same slot, roots and checkpoints.
-/
theorem LinkVote.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} {current : Bool} {position : Nat}
    {vote : ValidatorIndex × AttestationData} (frame : UpgradeFrame config pre after)
    (link : LinkVote pre current position vote) : LinkVote after current position vote := by
  simpa only [LinkVote, getCurrentEpoch, getPreviousEpoch, getBlockRoot, getBlockRootAtSlot,
    frame.slot, frame.blockRoots, frame.previousJustified, frame.currentJustified] using link

/-- An upgrade keeps the fork versions those of forks of the chain, up to the fork of the state. -/
theorem ForkVersionsKnown.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (frame : UpgradeFrame config pre after)
    (known : ForkVersionsKnown config pre) : ForkVersionsKnown config after := by
  obtain ⟨signer, le, same⟩ := known.2
  exact ⟨⟨signer, Nat.le_trans le frame.forward, frame.previousVersion.trans same⟩,
    ⟨post, Nat.le_refl _, frame.currentVersion⟩⟩

/-- An upgrade keeps the two justified checkpoints equal in the first two epochs. -/
theorem JustifiedEarly.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (frame : UpgradeFrame config pre after)
    (early : JustifiedEarly pre) : JustifiedEarly after := by
  unfold JustifiedEarly getCurrentEpoch at early ⊢
  rw [frame.slot, frame.previousJustified, frame.currentJustified]
  exact early

/-- An upgrade from Altair on keeps each target flag backed by a signed vote for its link.

It needs the registry below 2^64 validators after the upgrade. -/
theorem TargetFlagsSigned.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (frame : UpgradeFrame config pre after)
    (altair : .altair ≤ fork) (small : after.validators.data.size < 2 ^ 64)
    (holds : TargetFlagsSigned config checks pre) : TargetFlagsSigned config checks after := by
  intro _ current position flagged
  obtain ⟨vote, link, signed⟩ := holds altair current position (frame.flags altair current
    position flagged)
  exact ⟨vote, link.of_upgradeFrame frame,
    signed.of_keys frame.forward frame.genesisValidatorsRoot (frame.keysKept small)⟩

/-! ## The upgrades from Altair on -/

/-- An upgrade that carries the fields, from Altair on and before Gloas, is an upgrade frame. -/
theorem upgradeFrame_carryFields {fork post : Fork} (pre : BeaconState preset fork)
    (upgrade : fork < post) (before : post < .glamsterdam) (altair : .altair ≤ fork) :
    UpgradeFrame config pre (carryFields config post pre upgrade before) :=
  UpgradeFrame.of_carried (Nat.le_of_lt upgrade) rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> simp [recentParticipation, carryFields, altair, carryList]

/-- The upgrade to Electra is an upgrade frame. -/
theorem upgradeFrame_upgradeToElectra {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    UpgradeFrame config pre after := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := computed
  refine ((UpgradeFrame.trans_blockFrame ?_
    (BlockFrame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued)).trans_blockFrame
    (BlockFrame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok) compounded))
  have altair : Fork.altair ≤ Fork.dencun := by decide
  exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> simp [recentParticipation, carryFields, carryList, altair]

/-- The upgrade to Fulu is an upgrade frame. -/
theorem upgradeFrame_upgradeToFulu {pre : BeaconState preset .pectra}
    {after : BeaconState preset .fusaka} (computed : upgradeToFulu config pre = .ok after) :
    UpgradeFrame config pre after := by
  simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, -, rfl⟩ := computed
  have altair : Fork.altair ≤ Fork.pectra := by decide
  exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> simp [recentParticipation, carryFields, carryList, altair]

/-- The upgrade to Gloas is an upgrade frame. -/
theorem upgradeFrame_upgradeToGloas {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok after) : UpgradeFrame config pre after := by
  unfold upgradeToGloas at computed
  obtain ⟨_, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨_, -, onboarded⟩ := bind_ok_iff.mp rest
  obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
  exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> rfl

/-- The upgrade to Heze is an upgrade frame. -/
theorem upgradeFrame_upgradeToHeze {pre : BeaconState preset .glamsterdam}
    {after : BeaconState preset .hegota} (computed : upgradeToHeze config pre = .ok after) :
    UpgradeFrame config pre after := by
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp computed
  exact UpgradeFrame.of_carried (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    fun _ current => by cases current <;> rfl

/-- Each upgrade from Altair on is an upgrade frame. -/
theorem upgradeFrame_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (altair : .altair ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    UpgradeFrame config pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 => exact absurd altair (by exact (by decide : ¬Fork.altair ≤ Fork.phase0))
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    refine upgradeFrame_carryFields state ?_ ?_ ?_ <;> first | decide | (dsimp only; decide)
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact upgradeFrame_upgradeToElectra upgraded
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact upgradeFrame_upgradeToFulu upgraded
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact upgradeFrame_upgradeToGloas upgraded
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact upgradeFrame_upgradeToHeze upgraded
  all_goals
    simp only [upgradeNext] at computed
    cases computed

/-! ## The upgrades due at a slot -/

/-- The upgrades due at a slot, from Altair on, never shrink the registry. -/
theorem processUpgrades_registryGrows {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (computed : processUpgrades config checks forked = .ok after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    have frame := upgradeFrame_upgradeNext altair stepOk
    exact Nat.le_trans frame.registryGrows
      (more step (Nat.le_trans altair (Nat.le_of_lt step.property)) rest)
  | case2 forked _ =>
    cases computed
    exact Nat.le_refl _

/-- The upgrades due at a slot, from Altair on, keep the fork versions known. -/
theorem ForkVersionsKnown.of_processUpgrades {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (known : ForkVersionsKnown config forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    ForkVersionsKnown config after.state := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    exact more step (Nat.le_trans altair (Nat.le_of_lt step.property))
      (known.of_upgradeFrame (upgradeFrame_upgradeNext altair stepOk)) rest
  | case2 forked _ =>
    cases computed
    exact known

/-- The upgrades due at a slot, from Altair on, keep the justified checkpoints equal early on.

Those are the first two epochs. -/
theorem JustifiedEarly.of_processUpgrades {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (early : JustifiedEarly forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    JustifiedEarly after.state := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    exact more step (Nat.le_trans altair (Nat.le_of_lt step.property))
      (early.of_upgradeFrame (upgradeFrame_upgradeNext (checks := checks) altair stepOk)) rest
  | case2 forked _ =>
    cases computed
    exact early

/-- The upgrades due at a slot, from Altair on, keep each target flag backed by a signed vote.

That vote is for the link of the epoch of the flag.

The registry must stay below 2^64 validators after the upgrades. -/
theorem TargetFlagsSigned.of_processUpgrades {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (small : after.state.validators.data.size < 2 ^ 64)
    (holds : TargetFlagsSigned config checks forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    TargetFlagsSigned config checks after.state := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    have later := Nat.le_trans altair (Nat.le_of_lt step.property)
    exact more step later small (holds.of_upgradeFrame (upgradeFrame_upgradeNext altair stepOk)
      altair (Nat.lt_of_le_of_lt (processUpgrades_registryGrows later rest) small)) rest
  | case2 forked _ =>
    cases computed
    exact holds

end EthLib.Consensus
