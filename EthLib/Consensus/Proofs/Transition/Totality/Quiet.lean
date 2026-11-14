module

public import EthLib.Consensus.Proofs.Transition.Totality.Signers
public import EthLib.Consensus.Proofs.Transition.Totality.UpgradeNext

/-!
# Proofs: slots without blocks empty the records of signers

Only a block brings attestations, so a run of slots alone never records a new signer.

Each epoch moves the record of the current epoch to the previous one, and starts an empty record.

So after one epoch the current record is empty, and after two epochs both records are empty.

Before Altair a record is a list of pending attestations, and from Altair a list of flags.

The upgrade to Altair starts every flag at zero and translates only the previous attestations.

So the upgrades keep both records empty.

A state whose records are both empty meets the condition on the signers of the supply bound.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- No validator has signed in the current epoch.

Before Altair, the list of pending attestations of the current epoch is empty.

From Altair, every participation flag of the current epoch is unset. -/
def QuietCurrent (state : BeaconState preset fork) : Prop :=
  (∀ before : fork < .altair, (state.currentEpochAttestations before).data = #[]) ∧
    ∀ altair : .altair ≤ fork, ∀ flags ∈ (state.currentEpochParticipation altair).data, flags = 0

/-- No validator has signed in the previous or the current epoch. -/
def Quiet (state : BeaconState preset fork) : Prop :=
  QuietCurrent state ∧
    (∀ before : fork < .altair, (state.previousEpochAttestations before).data = #[]) ∧
    ∀ altair : .altair ≤ fork, ∀ flags ∈ (state.previousEpochParticipation altair).data, flags = 0

/-- When no validator has signed, the signers hold at most the total active balance. -/
theorem Quiet.signers (quiet : Quiet state) : SignersWithinActive state :=
  .of_quiet (fun before => ⟨quiet.2.1 before, quiet.1.1 before⟩)
    fun altair => ⟨quiet.2.2 altair, quiet.1.2 altair⟩

/-- A list whose every entry is kept or zeroed keeps the absence of set flags. -/
private theorem unset_of_keptOrZero {xs ys : Array ParticipationFlags}
    (kept : ∀ (i : Nat) flags, ys[i]? = some flags → xs[i]? = some flags ∨ flags = 0)
    (unset : ∀ flags ∈ xs, flags = 0) : ∀ flags ∈ ys, flags = 0 := by
  intro flags mem
  obtain ⟨i, found⟩ := Array.mem_iff_getElem?.mp mem
  rcases kept i flags found with old | zero
  · exact unset flags (Array.mem_of_getElem? old)
  · exact zero

/-- From Altair, one epoch unsets every current flag, and moves the current flags to the previous.
-/
private theorem processEpoch_unset (altair : .altair ≤ fork)
    (computed : processEpoch config checks state = .ok after) :
    (∀ flags ∈ (after.currentEpochParticipation altair).data, flags = 0) ∧
      ((∀ flags ∈ (state.currentEpochParticipation altair).data, flags = 0) →
        ∀ flags ∈ (after.previousEpochParticipation altair).data, flags = 0) := by
  simp only [processEpoch, altair, ↓reduceDIte] at computed
  obtain ⟨justified, rooted, justifiedOk, head, tail⟩ := processEpochAltair_split computed
  have current := (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.2.2.2.2
  refine ⟨unset_of_keptOrZero (fun i flags found => (tail.flags altair i flags).2 found) ?_,
    fun unset => unset_of_keptOrZero (fun i flags found => (tail.flags altair i flags).1 found) ?_⟩
  · rw [processParticipationFlagUpdates_current]
    exact fun flags mem => (Array.mem_replicate.mp mem).2
  · rw [processParticipationFlagUpdates_previous]
    refine unset_of_keptOrZero (fun i flags found => (head.flags altair i flags).2 found) ?_
    rw [current]
    exact unset

/-- One epoch leaves no signer in the current epoch. -/
theorem processEpoch_quietCurrent (computed : processEpoch config checks state = .ok after) :
    QuietCurrent after :=
  ⟨fun before => (processEpoch_pendingRotation before computed).2,
    fun altair => (processEpoch_unset altair computed).1⟩

/-- One epoch from a state with no signer in the current epoch leaves no signer at all. -/
theorem QuietCurrent.quiet_of_processEpoch (quiet : QuietCurrent state)
    (computed : processEpoch config checks state = .ok after) : Quiet after := by
  refine ⟨processEpoch_quietCurrent computed, fun before => ?_,
    fun altair => (processEpoch_unset altair computed).2 (quiet.2 altair)⟩
  rw [(processEpoch_pendingRotation before computed).1]
  exact quiet.1 before

/-- Two states with the same records of the previous and the current epoch. -/
private def SameRecords (s t : BeaconState preset fork) : Prop :=
  t.previousEpochAttestations = s.previousEpochAttestations ∧
    t.currentEpochAttestations = s.currentEpochAttestations ∧
    t.previousEpochParticipation = s.previousEpochParticipation ∧
    t.currentEpochParticipation = s.currentEpochParticipation

private theorem QuietCurrent.of_same {s t : BeaconState preset fork} (same : SameRecords s t)
    (quiet : QuietCurrent s) : QuietCurrent t := by
  obtain ⟨-, current, -, flags⟩ := same
  unfold QuietCurrent
  rw [current, flags]
  exact quiet

private theorem Quiet.of_same {s t : BeaconState preset fork} (same : SameRecords s t)
    (quiet : Quiet s) : Quiet t := by
  obtain ⟨previous, current, previousFlags, flags⟩ := same
  unfold Quiet QuietCurrent
  rw [previous, current, previousFlags, flags]
  exact quiet

/-- One slot keeps the records, or runs one epoch on a state with the same records.

When it runs no epoch, the epoch of the state stays the same. -/
private theorem advanceSlot_records (computed : advanceSlot config checks state = .ok after) :
    ∃ cached, SameRecords state cached ∧
      (((getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat ∧
          SameRecords state after) ∨
        ∃ epoched, processEpoch config checks cached = .ok epoched ∧
          SameRecords epoched after) := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  refine ⟨cached, by subst cachedEq; exact ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact .inr ⟨epoched, epochedOk, rfl, rfl, rfl, rfl⟩
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk cachedEq
    refine .inl ⟨?_, rfl, rfl, rfl, rfl⟩
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    exact nextSlot_epoch_of_inside sum inside

/-- One slot keeps the absence of signers in the current epoch. -/
theorem QuietCurrent.of_advanceSlot (quiet : QuietCurrent state)
    (computed : advanceSlot config checks state = .ok after) : QuietCurrent after := by
  obtain ⟨cached, same, kept | ⟨epoched, epochedOk, same'⟩⟩ := advanceSlot_records computed
  · exact quiet.of_same kept.2
  · exact (processEpoch_quietCurrent epochedOk).of_same same'

/-- One slot keeps the absence of signers. -/
theorem Quiet.of_advanceSlot (quiet : Quiet state)
    (computed : advanceSlot config checks state = .ok after) : Quiet after := by
  obtain ⟨cached, same, kept | ⟨epoched, epochedOk, same'⟩⟩ := advanceSlot_records computed
  · exact quiet.of_same kept.2
  · exact (QuietCurrent.quiet_of_processEpoch (quiet.1.of_same same) epochedOk).of_same same'

/-- One slot that starts a new epoch leaves no signer in the current epoch. -/
theorem advanceSlot_quietCurrent_of_lt
    (computed : advanceSlot config checks state = .ok after)
    (crossed : (getCurrentEpoch state).toNat < (getCurrentEpoch after).toNat) :
    QuietCurrent after := by
  obtain ⟨cached, same, kept | ⟨epoched, epochedOk, same'⟩⟩ := advanceSlot_records computed
  · exact absurd kept.1 (Nat.ne_of_gt crossed)
  · exact (processEpoch_quietCurrent epochedOk).of_same same'

/-- One slot that starts a new epoch, with no signer in the current epoch, leaves no signer. -/
theorem QuietCurrent.quiet_of_advanceSlot_of_lt (quiet : QuietCurrent state)
    (computed : advanceSlot config checks state = .ok after)
    (crossed : (getCurrentEpoch state).toNat < (getCurrentEpoch after).toNat) :
    Quiet after := by
  obtain ⟨cached, same, kept | ⟨epoched, epochedOk, same'⟩⟩ := advanceSlot_records computed
  · exact absurd kept.1 (Nat.ne_of_gt crossed)
  · exact (QuietCurrent.quiet_of_processEpoch (quiet.of_same same) epochedOk).of_same same'

/-- From Altair on both sides, a step that keeps or zeroes each flag keeps the absence of signers.
-/
private theorem quiet_of_flags {fork' : Fork} {pre : BeaconState preset fork}
    {post : BeaconState preset fork'} (altair : .altair ≤ fork) (altair' : .altair ≤ fork')
    (previous : ∀ (i : Nat) flags,
      (post.previousEpochParticipation altair').data[i]? = some flags →
        (pre.previousEpochParticipation altair).data[i]? = some flags ∨ flags = 0)
    (current : ∀ (i : Nat) flags,
      (post.currentEpochParticipation altair').data[i]? = some flags →
        (pre.currentEpochParticipation altair).data[i]? = some flags ∨ flags = 0) :
    (QuietCurrent pre → QuietCurrent post) ∧ (Quiet pre → Quiet post) := by
  have late : ¬fork' < .altair := Nat.not_lt_of_le altair'
  have kept (quiet : QuietCurrent pre) : QuietCurrent post :=
    ⟨fun before => absurd before late, fun _ => unset_of_keptOrZero current (quiet.2 altair)⟩
  exact ⟨kept, fun quiet => ⟨kept quiet.1, fun before => absurd before late,
    fun _ => unset_of_keptOrZero previous (quiet.2.2 altair)⟩⟩

/-- Equal lists keep each flag. -/
private theorem kept_of_eq {xs ys : Array ParticipationFlags} (same : ys = xs) :
    ∀ (i : Nat) flags, ys[i]? = some flags → xs[i]? = some flags ∨ flags = 0 :=
  fun _ _ found => .inl (same ▸ found)

/-- Each upgrade keeps the absence of signers, and of signers in the current epoch. -/
private theorem upgradeNext_quiet {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    (QuietCurrent pre.state → QuietCurrent post.val.state) ∧
      (Quiet pre.state → Quiet post.val.state) := by
  obtain ⟨fork, pre⟩ := pre
  cases fork with
  | phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    obtain ⟨middle, folded, _, rfl⟩ := upgradeToAltair_ok afterOk
    obtain ⟨previous, current, -⟩ := carryFields_of_lt_altair (config := config)
      (post := .altair) pre (by decide) (by decide) (by decide) (by decide)
    have late : ¬Fork.altair < .altair := by decide
    -- The translation writes only the previous flags, so the current flags stay at zero.
    have kept : QuietCurrent { middle with
        currentSyncCommittee := fun _ => ‹_›, nextSyncCommittee := fun _ => ‹_› } := by
      obtain ⟨_, rfl, -⟩ := foldlM_translateAttestation folded
      refine ⟨fun before => absurd before late, fun _ flags mem => ?_⟩
      rw [show _ = _ from current] at mem
      exact (Array.mem_replicate.mp mem).2
    refine ⟨fun _ => kept, fun quiet => ⟨kept, fun before => absurd before late, fun _ => ?_⟩⟩
    -- With no pending attestation of the previous epoch, nothing is translated.
    rw [quiet.2.1 (by decide : Fork.phase0 < .altair), Array.toList_empty,
      List.foldlM_nil] at folded
    cases folded
    intro flags mem
    rw [show _ = _ from previous] at mem
    exact (Array.mem_replicate.mp mem).2
  | altair =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact quiet_of_flags (fork := .altair) (fork' := .bellatrix) (by decide) (by decide)
      (kept_of_eq rfl) (kept_of_eq rfl)
  | bellatrix =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact quiet_of_flags (fork := .bellatrix) (fork' := .shapella) (by decide) (by decide)
      (kept_of_eq rfl) (kept_of_eq rfl)
  | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact quiet_of_flags (fork := .shapella) (fork' := .dencun) (by decide) (by decide)
      (kept_of_eq rfl) (kept_of_eq rfl)
  | dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at afterOk
    obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := afterOk
    -- Both folds keep each flag or zero it.
    have frame := (BlockFrame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued).trans
      (BlockFrame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok) compounded)
    exact quiet_of_flags (fork := .dencun) (fork' := .pectra) (by decide) (by decide)
      (fun i flags found => (frame.flags (by decide) i flags).1 found)
      (fun i flags found => (frame.flags (by decide) i flags).2 found)
  | pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at afterOk
    obtain ⟨_, -, rfl⟩ := afterOk
    exact quiet_of_flags (fork := .pectra) (fork' := .fusaka) (by decide) (by decide)
      (kept_of_eq rfl) (kept_of_eq rfl)
  | fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    unfold upgradeToGloas at afterOk
    obtain ⟨_, -, rest⟩ := bind_ok_iff.mp afterOk
    obtain ⟨_, -, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact quiet_of_flags (fork := .fusaka) (fork' := .glamsterdam) (by decide) (by decide)
      (kept_of_eq rfl) (kept_of_eq rfl)
  | glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp afterOk
    exact quiet_of_flags (fork := .glamsterdam) (fork' := .hegota) (by decide) (by decide)
      (kept_of_eq rfl) (kept_of_eq rfl)
  | _ => cases computed

/-- The upgrades due at a slot keep the absence of signers in the current epoch. -/
theorem QuietCurrent.of_processUpgrades {forked upgraded : ForkedBeaconState preset}
    (quiet : QuietCurrent forked.state)
    (computed : processUpgrades config checks forked = .ok upgraded) :
    QuietCurrent upgraded.state :=
  processUpgrades_induction (property := fun forked => QuietCurrent forked.state)
    (fun held computed => (upgradeNext_quiet computed).1 held) quiet computed

/-- The upgrades due at a slot keep the absence of signers. -/
theorem Quiet.of_processUpgrades {forked upgraded : ForkedBeaconState preset}
    (quiet : Quiet forked.state)
    (computed : processUpgrades config checks forked = .ok upgraded) :
    Quiet upgraded.state :=
  processUpgrades_induction (property := fun forked => Quiet forked.state)
    (fun held computed => (upgradeNext_quiet computed).2 held) quiet computed

end EthLib.Consensus
