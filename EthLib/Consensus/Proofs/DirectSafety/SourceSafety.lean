module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
public import EthLib.Consensus.Proofs.DirectSafety.Safety

/-!
# Accountable safety with the drift bounded by its sources

Two runs from a shared prefix finalize and justify conflicting checkpoints.

Either the following bound holds, or the hashes of the runs show evidence.

The evidence is a collision of the node hash or an object whose root is zero.

The unslashed active stake at the reference state is at most three times the accountable stake.

The bound adds twice the larger source envelope of the two runs.

The source envelope of a run replaces the observed drift of direct accountable safety.

It is computed from the run's balance replay up to the right finalized epoch.

A slashing in the shared prefix does not make a key accountable by itself.

A key that it slashed leaves the reference set and the accountable set.

The accountability predicate can still hold for such a key.

But the accountable set keeps only the keys unslashed at the reference state.

A prefix attester slashing can name a key without slashing it, when the key is not slashable.

Such a key stays in the reference set and can still count, through double votes or tail evidence.

Only forward persistence keeps a prefix-slashed key's stake out of the later drift and support.

The source envelope is a conservative bound, not the weak subjectivity formula.

In the bound, twice the envelope divided by three weighs exits at four thirds.

It weighs activations at two thirds, the weights of exits and of activations in [EIP-8061].

The bound holds for every pair of runs; nothing says that a run attains it.

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Accountable safety with the drift of each run bounded by its source envelope.

The envelope of a run reads the run's balance replay up to the right finalized epoch `high`.

Each run must end before Gloas, and the epoch of the reference state is at most `high + 1`.

The preset must meet the parameters, have two slots per epoch and order its caps.

Its largest effective balances must be whole numbers of increments. -/
theorem source_safety {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
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
  obtain ⟨eventsA, replayedA, driftA⟩ := derivedDrift_le_sources shared left genesis parameters
    twoSlots caps aligned earlyA _ startEpoch
  obtain ⟨eventsB, replayedB, driftB⟩ := derivedDrift_le_sources shared right genesis parameters
    twoSlots caps aligned earlyB _ startEpoch
  refine ⟨eventsA, eventsB, replayedA, replayedB, ?_⟩
  rcases accountable_safety shared left right parameters genesis enoughA enoughB ordered
    conflict with bound | hashes
  · exact .inl (bound.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left 2 (max_le_max driftA driftB)) _))
  · exact .inr hashes

end EthLib.Consensus.DirectSafety
