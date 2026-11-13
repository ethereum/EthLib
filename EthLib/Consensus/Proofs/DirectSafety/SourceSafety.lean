module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
public import EthLib.Consensus.Proofs.DirectSafety.Safety

/-!
# Accountable safety with the drift bounded by its sources

Two runs from a shared prefix finalize conflicting checkpoints.

Then the hashes of the runs show evidence, or direct accountable safety holds with a new drift.

That drift is the larger source envelope of the two runs.

The envelope reads the reference state, the balance replay of the run and its largest exit cohort.

Twice the envelope over three weighs exits at four thirds and activations at two thirds.

Those are the weights of [EIP-8061].

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Accountable safety with the drift of each run bounded by its source envelope.

The unslashed active stake at the reference state is at most three times the accountable stake.

The bound adds twice the larger envelope of the two runs, or the hashes of the runs show evidence.

Each envelope reads the balance replay of its run up to the finalized epoch of the right run.

The theorem also returns those replays.

The runs finalize conflicting checkpoints, and the right one is no earlier.

Each run keeps enough active stake through one epoch past its finalized epoch.

Each run ends before Gloas, and the reference state is at most one epoch past that epoch.

The preset meets the parameters, has at least two slots per epoch and orders its caps.

Its largest effective balances are whole numbers of increments.

The withdrawal delay is positive. -/
theorem source_safety {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (startEpoch : (getCurrentEpoch x.state).toNat ≤ b.state.finalizedCheckpoint.epoch.toNat + 1)
    (enoughA : EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch)
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint) :
    ∃ eventsA eventsB,
      left.balanceEvents b.state.finalizedCheckpoint.epoch.toNat = .ok eventsA ∧
      right.balanceEvents b.state.finalizedCheckpoint.epoch.toNat = .ok eventsB ∧
      ((Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
          2 * max
            (sourceDrift (config := config) x b.state.finalizedCheckpoint.epoch.toNat
              (boundaryWindow b.state.finalizedCheckpoint.epoch.toNat left) eventsA)
            (sourceDrift (config := config) x b.state.finalizedCheckpoint.epoch.toNat
              (boundaryWindow b.state.finalizedCheckpoint.epoch.toNat right) eventsB)) ∨
        HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects)) := by
  obtain ⟨eventsA, replayedA, driftA⟩ := derivedDrift_le_sources shared left genesis delay
    parameters twoSlots caps aligned earlyA _ startEpoch
  obtain ⟨eventsB, replayedB, driftB⟩ := derivedDrift_le_sources shared right genesis delay
    parameters twoSlots caps aligned earlyB _ startEpoch
  refine ⟨eventsA, eventsB, replayedA, replayedB, ?_⟩
  rcases accountable_safety shared left right parameters genesis enoughA enoughB ordered
    conflict with bound | hashes
  · exact .inl (bound.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left 2 (max_le_max driftA driftB)) _))
  · exact .inr hashes

end EthLib.Consensus.DirectSafety
