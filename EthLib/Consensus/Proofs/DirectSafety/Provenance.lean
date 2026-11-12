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

/-- The last state of a run keeps the invariant of valid blocks and its justified checkpoints apart.

In the first two epochs its two justified checkpoints are equal.

Later its previous justified checkpoint is before the previous epoch.

The run starts at a genesis built from deposits. -/
theorem run_justified_separated {g a : ForkedBeaconState preset}
    (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) :
    Invariant a.state ∧ JustifiedEarly a.state ∧ JustifiedSeparated a.state := by
  induction run with
  | nil =>
    obtain ⟨hash, time, deposits, ok⟩ := genesis
    refine ⟨(initializeBeaconStateFromEth1_invariant ok).2,
      JustifiedEarly.of_initializeBeaconStateFromEth1 ok, ?_⟩
    obtain ⟨_, _, _, _, _, frame, equal⟩ := initializeBeaconStateFromEth1_frame ok
    rw [equal]
    intro later
    have slot := frame.slot
    simp only [getCurrentEpoch, slot, emptyGenesisState] at later
    simp [GENESIS_SLOT, GENESIS_EPOCH, computeEpochAtSlot, UInt64.lt_iff_toNat_lt] at later
  | snoc pre step ih =>
    rcases ih with ⟨holds, early, separated⟩
    cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      exact ⟨(advanceSlotAcross_invariant holds ok).1,
        (early.of_advanceSlot advancedOk).of_processUpgrades upgraded,
        (separated.of_advanceSlot early holds.settled advancedOk).of_processUpgrades upgraded⟩
    | block engine signed due ok =>
      obtain ⟨_, blockOk, _⟩ := applySignedBlock_ok ok
      have frame := frame_processBlock blockOk
      exact ⟨frame.invariant holds, early.of_frame frame, separated.of_frame frame⟩

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

private theorem run_participation {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g) :
    ParticipationBacked run a.state := by
  induction run with
  | nil => exact genesis_participation genesis
  | @snoc middle last pre step backed =>
    -- The votes of the step join those of the run before it.
    have sub := votes_snoc pre step
    cases step with
    | slot ok =>
      obtain ⟨flags, pending⟩ := votedParticipation_advanceSlotAcross
        (by have := parameters.slots; omega) (by have := parameters.roots; omega)
        parameters.lookahead (run_justified_separated pre genesis).2.1 backed.2 backed.1 ok
      exact ⟨pending.mono (fun _ voted => sub (.inl voted)),
        flags.mono (fun _ voted => sub (.inl voted))⟩
    | block engine signed due ok =>
      obtain ⟨flags, pending⟩ := votedParticipation_processBlock parameters.lookahead
        (backed.2.mono Set.subset_union_left) (backed.1.mono Set.subset_union_left)
        Set.subset_union_right (applySignedBlock_ok ok).2.1
      exact ⟨pending.mono sub, flags.mono sub⟩

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
