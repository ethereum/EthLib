module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.WeakSubjectivity

/-!
# `Exports.WeakSubjectivity`

C-ABI exports of weak subjectivity.

One export computes the period of a state.

Another checks that a checkpoint is not stale.

They take states as SSZ bytes, and accept forks up to Gloas.

The check reads only the time of the store, so the export takes the two times of a store.

The configuration of a name holds, with the replacements that a JSON object gives.

An input that does not decode, or an unknown name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)

/-- The result of weak subjectivity, with the code and the text of its error. -/
def runWeakSubjectivity {α : Type} (result : Except WeakSubjectivityError α) : Result α :=
  result.mapError fun e => (e.code, reprStr e)

/-- The weak subjectivity period of a state, in epochs.

The preset, the configuration and the fork are named in UTF-8. -/
@[export eth_consensus_compute_weak_subjectivity_period]
def computeWeakSubjectivityPeriodExport (name fork state replacements : ByteArray) :
    Result UInt64 := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) state
  runWeakSubjectivity (computeWeakSubjectivityPeriod config state)

/-- A store with a time and a time of genesis, and nothing else.

The staleness check reads only these two times. -/
def storeAtTime (preset : Preset) (fork : Fork) (genesisTimeMs timeMs : UInt64) :
    Store preset fork :=
  let zero : Checkpoint := { epoch := 0, root := Vector.replicate 32 0 }
  { timeMs, genesisTimeMs, justifiedCheckpoint := zero, finalizedCheckpoint := zero,
    unrealizedJustifiedCheckpoint := zero, unrealizedFinalizedCheckpoint := zero,
    proposerBoostRoot := Vector.replicate 32 0, equivocatingIndices := [], blocks := {},
    blockStates := {}, blockTimeliness := {}, checkpointStates := {}, latestMessages := {},
    unrealizedJustifications := {} }

/-- Whether a checkpoint is within the weak subjectivity period of its state, at a time.

The preset, the configuration and the fork are named in UTF-8.

The checkpoint comes as its SSZ bytes, and the state as the state at the checkpoint.

The two times are those of a store, in milliseconds since the Unix epoch. -/
@[export eth_consensus_is_within_weak_subjectivity_period]
def isWithinWeakSubjectivityPeriodExport (name fork state checkpoint replacements : ByteArray)
    (genesisTimeMs timeMs : UInt64) : Result Bool := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let checkpoint ← decodeInput Checkpoint checkpoint
  runWeakSubjectivity (isWithinWeakSubjectivityPeriod config
    (storeAtTime preset fork genesisTimeMs timeMs) state checkpoint)

end EthLib.Consensus.Exports
