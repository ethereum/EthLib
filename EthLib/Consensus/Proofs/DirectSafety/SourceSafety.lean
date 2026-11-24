module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
public import EthLib.Consensus.Proofs.DirectSafety.Safety

/-!
# Accountable safety with the drift bounded by its sources

Direct accountable safety holds with the larger source envelope of the two runs as its drift.

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

The bound adds twice the larger envelope of the two runs.

Otherwise the hashes of the runs show evidence. -/
theorem source_safety {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    -- The preset meets the parameters.
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    -- The withdrawal delay is positive.
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    -- The preset has at least two slots per epoch and orders its caps.
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    -- The largest effective balances of the preset are whole numbers of increments.
    (aligned : MaxEffectiveBalancesAligned preset)
    -- Each run ends before Gloas.
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    -- The reference state is at most one epoch past the finalized epoch of the right run.
    (startEpoch : (getCurrentEpoch x.state).toNat ≤ b.state.finalizedCheckpoint.epoch.toNat + 1)
    -- Each run keeps enough active stake through one epoch past its finalized epoch.
    (enoughA : EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat)
    -- The runs finalize conflicting checkpoints, and the right one is no earlier.
    (ordered : a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch)
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint) :
    -- Each envelope reads the balance replay of its run up to the finalized epoch of the right run.
    --
    -- The theorem also returns those replays.
    ∃ eventsA eventsB,
      left.balanceEvents b.state.finalizedCheckpoint.epoch.toNat = .ok eventsA ∧
      right.balanceEvents b.state.finalizedCheckpoint.epoch.toNat = .ok eventsB ∧
      ((Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
          -- The envelope reads the reference state, the balance replay and the largest exit cohort.
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
