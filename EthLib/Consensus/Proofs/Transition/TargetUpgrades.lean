module

public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.TargetPending
public import EthLib.Consensus.Proofs.Transition.TargetSlots
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Transition.ForkBoundary

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

The upgrade from Phase 0 builds the flags of the previous epoch from the pending attestations.

When each of their attesters signed a vote for the link of that epoch, each such flag has one.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## What an upgrade keeps -/

/-- A vote for a link is one in a state of another fork with the same slot, roots and checkpoints.

That is the case after an upgrade. -/
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

/-- An upgrade keeps the previous justified epoch below the previous epoch. -/
theorem JustifiedSeparated.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (frame : UpgradeFrame config pre after)
    (separated : JustifiedSeparated pre) : JustifiedSeparated after := by
  unfold JustifiedSeparated getPreviousEpoch getCurrentEpoch at separated ⊢
  rw [frame.slot, frame.previousJustified]
  exact separated

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

/-! ## The upgrade from Phase 0 -/

/-- One translated pending attestation sets a target flag only for one of its attesters.

Its target root is then the root of the block at the first slot of its target epoch. -/
private theorem translateAttestation_target {fork : Fork} {state after : BeaconState preset fork}
    {altair : .altair ≤ fork} {pending : PendingAttestation preset}
    (computed : translateAttestation state altair pending = .ok after) (position : Nat)
    (flagged : TargetFlagAt (after.previousEpochParticipation altair) position) :
    TargetFlagAt (state.previousEpochParticipation altair) position ∨
      getBlockRoot state pending.data.target.epoch = .ok pending.data.target.root ∧
        ∃ attesters, getPendingAttestingIndices state pending = .ok attesters ∧
          ∃ attester ∈ attesters, attester.toNat = position := by
  simp only [translateAttestation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨flags, flagsOk, attesters, attestersOk, participation, folded, rfl⟩ := computed
  have kinds := (getAttestationParticipationFlagIndices_spec flagsOk).2
  -- Each attester in turn gets the earned flags at its own position.
  rcases foldlM_targetFlag (earned := TIMELY_TARGET_FLAG_INDEX ∈ flags) (flagsOf := id)
      (fun list index updated ok place ⟨value, found, set⟩ => by
        split at ok
        · rename_i inside
          simp only [Except.ok.injEq] at ok
          subst ok
          dsimp only [id] at found ⊢
          rw [Array.getElem?_set] at found
          split at found
          · rename_i same
            cases found
            rcases hasFlag_foldl_addFlag_target flags _ kinds set with before | chosen
            · exact .inl ⟨_, by rw [← same]; exact Array.getElem?_eq_getElem inside, before⟩
            · exact .inr ⟨chosen, same⟩
          · exact .inl ⟨value, found, set⟩
        · cases ok)
      attesters _ participation folded position flagged with
    old | ⟨chosen, attester, member, place⟩
  · exact .inl old
  · exact .inr ⟨getAttestationParticipationFlagIndices_targetRoot flagsOk chosen, attesters,
      attestersOk, attester, member, place⟩

/-- The upgrade to Altair builds each target flag from a signed vote for the link of its epoch.

The flags of the previous epoch come from the pending attestations of Phase 0.

Each pending attestation of Phase 0 must be a signed vote for the link of its epoch.

The flags of the current epoch start empty. -/
theorem TargetFlagsSigned.of_upgradeToAltair {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair} (holds : PendingSigned config checks pre)
    (computed : upgradeToAltair config pre = .ok after) :
    TargetFlagsSigned config checks after := by
  have frame := upgradeFrame_upgradeToAltair computed
  -- The upgrade keeps the registry, so each key, with no bound on its size.
  have keys : KeysKept pre after := KeysKept.of_validators (upgradeToAltair_spec computed).1
  obtain ⟨_, folded, _, rfl⟩ := upgradeToAltair_ok computed
  obtain ⟨previousZero, currentZero, -⟩ := carryFields_of_lt_altair (config := config)
    (post := .altair) pre (by decide) (by decide) (by decide) (by decide)
  -- A flag of the previous epoch in a state of the fold comes from a signed vote in Phase 0.
  let Claim : BeaconState preset .altair → Prop := fun state =>
    state.validators.data = pre.validators.data ∧
      state.randaoMixes.elements = pre.randaoMixes.elements ∧
      state.slot = pre.slot ∧ state.blockRoots = pre.blockRoots ∧
      (∀ position, ¬TargetFlagAt (state.currentEpochParticipation (by decide)) position) ∧
      ∀ position, TargetFlagAt (state.previousEpochParticipation (by decide)) position →
        ∃ vote, LinkVote pre false position vote ∧ SignedVote config checks pre vote
  have walk : ∀ (list : List (PendingAttestation preset)),
      (∀ pending ∈ list, pending ∈ recentPending pre (by decide) false) →
      ∀ (state final : BeaconState preset .altair), Claim state →
        list.foldlM (fun state attestation => translateAttestation state (by decide) attestation)
          state = .ok final → Claim final := by
    intro list
    induction list with
    | nil =>
      intro _ state final holdsState computed
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ holdsState
    | cons first rest more =>
      intro listed state final holdsState computed
      rw [List.foldlM_cons, bind_ok_iff] at computed
      obtain ⟨middle, middleOk, computed⟩ := computed
      refine more (fun pending member => listed pending (List.mem_cons_of_mem first member))
        middle final ?_ computed
      obtain ⟨validators, mixes, slot, roots, none, flags⟩ := holdsState
      have translated := translateAttestation_target middleOk
      obtain ⟨participation, rfl, -⟩ := translateAttestation_spec middleOk
      refine ⟨validators, mixes, slot, roots, none, fun position flagged => ?_⟩
      rcases translated position flagged with old | ⟨root, attesters, attestersOk, attester,
        member, place⟩
      · exact flags position old
      obtain ⟨epoch, slotEpoch, source, signed⟩ :=
        holds (by decide) false first (listed first List.mem_cons_self)
      have committees : CommitteesKept first.data.target.epoch pre state :=
        CommitteesKept.of_eq validators mixes _
      have attestersPre : getPendingAttestingIndices pre first = .ok attesters := by
        unfold getPendingAttestingIndices at attestersOk ⊢
        rw [← committees _ _ slotEpoch]
        exact attestersOk
      refine ⟨(attester, first.data), ⟨place, epoch, source, ?_⟩,
        signed attesters attestersPre attester member⟩
      have same : getBlockRoot state first.data.target.epoch =
          getBlockRoot pre first.data.target.epoch := by
        simp only [getBlockRoot, getBlockRootAtSlot, slot, roots]
      exact same ▸ root
  have empty : ∀ {list : EpochParticipation preset .altair},
      list.data = Array.replicate pre.validators.data.size 0 → ∀ position,
        ¬TargetFlagAt list position := fun zero position ⟨value, found, set⟩ => by
    rw [zero, Array.getElem?_replicate] at found
    split at found
    · cases found
      exact absurd set (by decide)
    · cases found
  have start : Claim (carryFields config .altair pre (by decide) (by decide)) :=
    ⟨rfl, rfl, rfl, rfl, empty currentZero, fun position flagged =>
      absurd flagged (empty previousZero position)⟩
  obtain ⟨-, -, -, -, currentNone, previousFlags⟩ :=
    walk _ (fun pending member => by simpa [recentPending] using member) _ _ start folded
  intro altair current position flagged
  cases current
  · obtain ⟨vote, link, signed⟩ := previousFlags position flagged
    exact ⟨vote, link.of_upgradeFrame frame,
      signed.of_keys frame.forward frame.genesisValidatorsRoot keys⟩
  · exact absurd flagged (currentNone position)

/-! ## The upgrades due at a slot -/

/-- The upgrades due at a slot never shrink the registry. -/
theorem processUpgrades_registryGrows {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size :=
  processUpgrades_induction
    (property := fun state => forked.state.validators.data.size ≤ state.state.validators.data.size)
    (fun le stepOk => Nat.le_trans le (upgradeFrame_upgradeNext stepOk).registryGrows)
    (Nat.le_refl _) computed

/-- The upgrades due at a slot keep the fork versions those of forks of the chain. -/
theorem ForkVersionsKnown.of_processUpgrades {forked after : ForkedBeaconState preset}
    (known : ForkVersionsKnown config forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    ForkVersionsKnown config after.state :=
  processUpgrades_induction (property := fun state => ForkVersionsKnown config state.state)
    (fun known stepOk => known.of_upgradeFrame (upgradeFrame_upgradeNext stepOk)) known computed

/-- The upgrades due at a slot keep the two justified checkpoints equal in the first two epochs.
-/
theorem JustifiedEarly.of_processUpgrades {forked after : ForkedBeaconState preset}
    (early : JustifiedEarly forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    JustifiedEarly after.state :=
  processUpgrades_induction (property := fun state => JustifiedEarly state.state)
    (fun early stepOk => early.of_upgradeFrame (upgradeFrame_upgradeNext stepOk)) early computed

/-- The upgrades due at a slot keep the previous justified epoch below the previous epoch. -/
theorem JustifiedSeparated.of_processUpgrades {forked after : ForkedBeaconState preset}
    (separated : JustifiedSeparated forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    JustifiedSeparated after.state :=
  processUpgrades_induction (property := fun state => JustifiedSeparated state.state)
    (fun separated stepOk => separated.of_upgradeFrame (upgradeFrame_upgradeNext stepOk))
    separated computed

/-- The upgrades due at a slot keep both justified checkpoints. -/
theorem processUpgrades_justified {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    after.state.previousJustifiedCheckpoint = forked.state.previousJustifiedCheckpoint ∧
      after.state.currentJustifiedCheckpoint = forked.state.currentJustifiedCheckpoint :=
  processUpgrades_induction
    (property := fun state =>
      state.state.previousJustifiedCheckpoint = forked.state.previousJustifiedCheckpoint ∧
        state.state.currentJustifiedCheckpoint = forked.state.currentJustifiedCheckpoint)
    (fun ⟨previous, current⟩ stepOk =>
      ⟨(upgradeFrame_upgradeNext stepOk).previousJustified.trans previous,
        (upgradeFrame_upgradeNext stepOk).currentJustified.trans current⟩)
    ⟨rfl, rfl⟩ computed

/-- An upgrade reaches Altair or a later fork.

Before Altair, only a state of Phase 0 upgrades. -/
private theorem upgradeNext_altair {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    .altair ≤ post.val.fork ∧ (pre.fork < .altair → pre.fork = .phase0) := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed <;>
    first
      | (obtain ⟨_, -, rfl⟩ := computed; dsimp only; decide)
      | (subst computed; dsimp only; decide)

/-- The upgrades due at a slot keep each pending attestation a signed vote for its link.

An upgrade moves the state to Altair or later, where no pending attestation remains. -/
theorem PendingSigned.of_processUpgrades {forked after : ForkedBeaconState preset}
    (holds : PendingSigned config checks forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    PendingSigned config checks after.state :=
  processUpgrades_induction (property := fun state => PendingSigned config checks state.state)
    (fun _ stepOk before => absurd (upgradeNext_altair stepOk).1 (Nat.not_le_of_lt before))
    holds computed

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
    exact more step (Nat.le_trans altair (Nat.le_of_lt step.property)) small
      (holds.of_upgradeFrame (upgradeFrame_upgradeNext stepOk) altair
        (Nat.lt_of_le_of_lt (processUpgrades_registryGrows rest) small)) rest
  | case2 forked _ =>
    cases computed
    exact holds

/-- The upgrades due at a slot, from Phase 0, give each target flag a signed vote.

That vote is for the link of the epoch of the flag.

Each pending attestation of Phase 0 must be a signed vote for the link of its epoch.

The registry must stay below 2^64 validators after the upgrades. -/
theorem TargetFlagsSigned.of_processUpgrades_of_phase0 {forked after : ForkedBeaconState preset}
    (phase0 : forked.fork = .phase0)
    (small : after.state.validators.data.size < 2 ^ 64)
    (holds : PendingSigned config checks forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    TargetFlagsSigned config checks after.state := by
  obtain ⟨fork, state⟩ := forked
  simp only at phase0 holds
  subst phase0
  unfold processUpgrades at computed
  split at computed
  · obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at stepOk
    obtain ⟨_, upgraded, rfl⟩ := stepOk
    exact TargetFlagsSigned.of_processUpgrades (show Fork.altair ≤ Fork.altair by decide) small
      (TargetFlagsSigned.of_upgradeToAltair holds upgraded) rest
  · cases computed
    intro altair
    exact absurd altair (by decide : ¬Fork.altair ≤ Fork.phase0)

/-- The upgrades due at a slot, before Altair, give each target flag a signed vote.

That vote is for the link of the epoch of the flag.

Each pending attestation must be a signed vote for the link of its epoch.

The registry must stay below 2^64 validators after the upgrades. -/
theorem TargetFlagsSigned.of_processUpgrades_of_lt_altair {forked after : ForkedBeaconState preset}
    (before : forked.fork < .altair) (small : after.state.validators.data.size < 2 ^ 64)
    (holds : PendingSigned config checks forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    TargetFlagsSigned config checks after.state := by
  by_cases phase0 : forked.fork = .phase0
  · exact TargetFlagsSigned.of_processUpgrades_of_phase0 phase0 small holds computed
  unfold processUpgrades at computed
  split at computed
  · obtain ⟨step, stepOk, -⟩ := bind_ok_iff.mp computed
    exact absurd ((upgradeNext_altair stepOk).2 before) phase0
  · cases computed
    intro altair
    exact absurd altair (Nat.not_le_of_lt before)

/-! ## Genesis, slots and blocks -/

/-- A frame keeps the fork versions those of forks of the chain. -/
theorem ForkVersionsKnown.of_frame {fork : Fork} {state after : BeaconState preset fork}
    (frame : Frame state after) (known : ForkVersionsKnown config state) :
    ForkVersionsKnown config after :=
  (ForkVersionsKnown.congr frame.forkVersions).mpr known

/-- Slots keep the fork versions those of forks of the chain. -/
theorem ForkVersionsKnown.of_advanceSlots {fork : Fork} :
    ∀ {count : Nat} {state after : BeaconState preset fork}, ForkVersionsKnown config state →
      advanceSlots config checks count state = .ok after → ForkVersionsKnown config after
  | 0, state, after, known, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ known
  | count + 1, state, after, known, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact ForkVersionsKnown.of_advanceSlots
      ((ForkVersionsKnown.congr (advanceSlot_keys nextOk).1).mpr known) rest

/-- A block that the transition accepts keeps the fork versions those of forks of the chain. -/
theorem ForkVersionsKnown.of_stateTransition {fork : Fork} {state after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} (known : ForkVersionsKnown config state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    ForkVersionsKnown config after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, -, slotsOk⟩ := slotsOk
  exact (known.of_advanceSlots slotsOk).of_frame (frame_processBlock blockOk)

/-- The fork versions of the genesis state built from deposits are those of forks of the chain.

Its two justified checkpoints are also equal. -/
theorem initializeBeaconStateFromEth1_target {fork : Fork} {after : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    ForkVersionsKnown config after ∧ JustifiedEarly after := by
  obtain ⟨before, _, _, _, activated, _, depositedOk, activatedOk, rfl⟩ :=
    initializeBeaconStateFromEth1_ok computed
  have altair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  have frame := (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit ok) depositedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  have later : ∀ next : Fork, Fork.altair ≤ next → ¬next ≤ fork :=
    fun _ le le' => altair (Nat.le_trans le le')
  have genesis : config.GENESIS_FORK_VERSION = config.forkVersion fork := by
    unfold Config.forkVersion
    simp [later .hegota (by decide), later .glamsterdam (by decide), later .fusaka (by decide),
      later .pectra (by decide), later .dencun (by decide), later .shapella (by decide),
      later .bellatrix (by decide), altair]
  refine ⟨?_, fun _ => ?_⟩
  · show ForkVersionsKnown config activated
    rw [ForkVersionsKnown.congr frame.forkVersions]
    exact ⟨⟨fork, Nat.le_refl _, genesis⟩, ⟨fork, Nat.le_refl _, genesis⟩⟩
  · show activated.previousJustifiedCheckpoint = activated.currentJustifiedCheckpoint
    rw [frame.previousJustified, frame.currentJustified]
    rfl

/-- Before Altair, the genesis state built from deposits has no pending attestations. -/
theorem initializeBeaconStateFromEth1_pending {fork : Fork} {after : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) (before : fork < .altair) (current : Bool) :
    recentPending after before current = #[] := by
  obtain ⟨_, _, _, deposited, activated, _, depositedOk, activatedOk, rfl⟩ :=
    initializeBeaconStateFromEth1_ok computed
  let Empty : BeaconState preset fork → Prop := fun state =>
    (state.previousEpochAttestations before).data = #[] ∧
      (state.currentEpochAttestations before).data = #[]
  have afterDeposits : Empty deposited := by
    refine foldlM_ok_invariant Empty (fun state entry next empty ok => ?_) ⟨rfl, rfl⟩ depositedOk
    simp only [genesisDeposit, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    have frame := pendingFrame_processDeposit before ok
    exact ⟨by rw [funext frame.previousPending]; exact empty.1,
      by rw [funext frame.currentPending]; exact empty.2⟩
  have afterActivation : Empty activated := by
    refine foldlM_ok_invariant Empty (fun state index next empty ok => ?_) afterDeposits
      activatedOk
    simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact empty
  cases current
  · exact afterActivation.1
  · exact afterActivation.2

end EthLib.Consensus
