module

public import EthLib.Consensus.Proofs.DirectSafety.Identity
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Participation backed by attestations of the selected run

Pending records retain their full data; participation flags retain a source and target.

The epoch rotation and Altair upgrade must preserve the same accepted witnesses.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The pending attestations and the target flags of the state hold only votes of the run. -/
def ParticipationBacked {g a : ForkedBeaconState preset} (run : Run config checks g a)
    {fork : Fork} (state : BeaconState preset fork) : Prop :=
  PendingVoted run.votes state ∧ TargetFlagsVoted run.votes state

-- Epoch rotation needs equal justified checkpoints in the first two epochs.
private theorem run_justifiedEarly {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g) :
    JustifiedEarly a.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    exact .of_initializeBeaconStateFromEth1 ok
  | snoc pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨_, advanced, upgraded⟩ := bind_ok_iff.mp ok
      exact (ih.of_advanceSlot advanced).of_processUpgrades upgraded
    | block engine signed due ok =>
      obtain ⟨_, processed, _⟩ := applySignedBlock_ok ok
      exact ih.of_frame (frame_processBlock processed)

private theorem votes_snoc {g a b : ForkedBeaconState preset} (run : Run config checks g a)
    (step : Step config checks a b) : run.votes ∪ step.votes ⊆ (run.snoc step).votes := by
  rintro vote (⟨before, after, selected, member, voted⟩ | voted)
  · exact ⟨before, after, selected, .earlier member step, voted⟩
  · exact ⟨a, b, step, .last run step, voted⟩

private theorem genesis_participation {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ParticipationBacked (Run.nil : Run config checks g g) g.state := by
  obtain ⟨_, _, _, ok⟩ := genesis
  constructor
  · intro before current pending member
    rw [initializeBeaconStateFromEth1_pending ok before current] at member
    simp at member
  · intro altair
    exact False.elim (Nat.not_le_of_lt (initializeBeaconStateFromEth1_invariant ok).1 altair)

/-- This includes epoch rotation and every due upgrade, in particular pending-to-flag conversion. -/
private theorem slot_participation {g a b : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (ok : advanceSlotAcross config checks a = .ok b)
    (backed : ParticipationBacked run a.state) :
    ParticipationBacked (run.snoc (.slot ok)) b.state := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  have pending : PendingVoted run.votes advanced := by
    by_cases before : a.fork < .altair
    · exact backed.1.of_advanceSlot before parameters.lookahead
        (run_justifiedEarly run genesis) advancedOk
    · intro beforeAltair
      exact False.elim (before beforeAltair)
  have flags : TargetFlagsVoted run.votes b.state := by
    by_cases before : a.fork < .altair
    -- The upgrade translates the pending witnesses after the slot's epoch rotation.
    · exact TargetFlagsVoted.of_processUpgrades_of_lt_altair
        (forked := ⟨a.fork, advanced⟩) before pending upgraded
    · have advancedFlags : TargetFlagsVoted run.votes advanced :=
        backed.2.of_advanceSlot (by have := parameters.slots; omega)
          (by have := parameters.roots; omega) (run_justifiedEarly run genesis)
          advancedOk
      exact TargetFlagsVoted.of_processUpgrades (forked := ⟨a.fork, advanced⟩)
        (Nat.le_of_not_lt before) advancedFlags upgraded
  have sub : run.votes ⊆ (run.snoc (.slot ok)).votes := fun _ voted =>
    votes_snoc run (.slot ok) (.inl voted)
  exact ⟨(pending.of_processUpgrades upgraded).mono sub, flags.mono sub⟩

private theorem block_participation {g : ForkedBeaconState preset} {fork : Fork}
    {a b : BeaconState preset fork} (run : Run config checks g ⟨fork, a⟩)
    (parameters : Parameters preset) (engine : ExecutionEngine preset fork)
    (signed : SignedBeaconBlock preset fork) (due : upgradeDue config ⟨fork, a⟩ = false)
    (ok : applySignedBlock config checks engine a signed true = .ok b)
    (backed : ParticipationBacked run a) :
    ParticipationBacked (run.snoc (.block engine signed due ok)) b := by
  obtain ⟨_, processed, _⟩ := applySignedBlock_ok ok
  have pending : PendingVoted (run.votes ∪ blockVotes a signed.message) b := by
    by_cases before : fork < .altair
    · exact backed.1.of_processBlock before parameters.lookahead processed
    · intro beforeAltair
      exact False.elim (before beforeAltair)
  have flags := backed.2.of_voteFrame (voteFrame_processBlock parameters.lookahead processed)
  exact ⟨pending.mono (votes_snoc run (.block engine signed due ok)),
    flags.mono (votes_snoc run (.block engine signed due ok))⟩

private theorem run_participation {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g) :
    ParticipationBacked run a.state := by
  induction run with
  | nil => exact genesis_participation genesis
  | snoc pre step backed =>
    cases step with
    | slot ok => exact slot_participation pre parameters genesis ok backed
    | block engine signed due ok =>
      exact block_participation pre parameters engine signed due ok backed

/-- At the end of a prefix, the pending attestations and target flags hold votes of the whole run.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem inherited_participation {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g) :
    ParticipationBacked (shared.append tail) x.state := by
  have backed := run_participation shared parameters genesis
  have sub : shared.votes ⊆ (shared.append tail).votes := by
    rintro vote ⟨before, after, step, member, voted⟩
    exact ⟨before, after, step, (shared.contains_append tail step).mpr (.inl member), voted⟩
  exact ⟨backed.1.mono sub, backed.2.mono sub⟩

end EthLib.Consensus.DirectSafety
