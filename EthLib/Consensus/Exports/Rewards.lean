module

public import EthLib.Consensus.Exports.Transition

/-!
# `Exports.Rewards`

C-ABI export of the reward and penalty deltas of an epoch, for the consensus test vectors.

It takes a state as SSZ bytes, and returns the deltas of one kind of vote as SSZ bytes.

A second export returns the deltas of several kinds from one decode of the state.

The deltas hold two lists of amounts, one entry for each validator: the rewards, then the penalties.

An input that does not decode, or an unknown name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)

/-- The rewards and the penalties of each validator for one kind of vote, as the vectors hold them.

Each list holds at most a fixed number of amounts. -/
structure Deltas (limit : Nat) where
  /-- The reward of each validator. -/
  rewards : SszList Gwei limit
  /-- The penalty of each validator. -/
  penalties : SszList Gwei limit

instance {limit : Nat} : SszType (Deltas limit) :=
  .container ["rewards", "penalties"] (fun d => (d.rewards, d.penalties))
    (fun (rewards, penalties) => ⟨rewards, penalties⟩)

/-- The deltas of the kind of vote that a component of the vectors names.

Before Altair the kinds are the source, target and head votes, their inclusion and inactivity.

From Altair the source, target and head are participation flags, and the inclusion is gone. -/
def runDeltas {preset : Preset} {fork : Fork} (config : Config) (component : String)
    (state : BeaconState preset fork) : Result (Array Gwei × Array Gwei) :=
  if altair : .altair ≤ fork then
    match component with
    | "source_deltas" =>
      runTransition (getFlagIndexDeltas state altair ⟨TIMELY_SOURCE_FLAG_INDEX.toNat, by decide⟩)
    | "target_deltas" =>
      runTransition (getFlagIndexDeltas state altair ⟨TIMELY_TARGET_FLAG_INDEX.toNat, by decide⟩)
    | "head_deltas" =>
      runTransition (getFlagIndexDeltas state altair ⟨TIMELY_HEAD_FLAG_INDEX.toNat, by decide⟩)
    | "inactivity_penalty_deltas" => runTransition (getInactivityPenaltyDeltas config state)
    | component => throw (0, s!"no deltas {component} at {fork.name}")
  else
    have before := Nat.lt_of_not_le altair
    match component with
    | "source_deltas" => runTransition (getSourceDeltas state before)
    | "target_deltas" => runTransition (getTargetDeltas state before)
    | "head_deltas" => runTransition (getHeadDeltas state before)
    | "inclusion_delay_deltas" => runTransition (getInclusionDelayDeltas state before)
    | "inactivity_penalty_deltas" => runTransition (getInactivityPenaltyDeltas config state)
    | component => throw (0, s!"no deltas {component} at {fork.name}")

/-- The SSZ bytes of the rewards and the penalties of each validator.

A list longer than the registry limit has code 0. -/
def encodeDeltas (preset : Preset) (deltas : Array Gwei × Array Gwei) : Result ByteArray :=
  let (rewards, penalties) := deltas
  let limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat
  if within : rewards.size ≤ limit ∧ penalties.size ≤ limit then
    let deltas : Deltas limit := ⟨⟨rewards, within.1⟩, ⟨penalties, within.2⟩⟩
    (SszType.serialize deltas).mapError fun e => (0, s!"deltas rejected: {reprStr e}")
  else throw (0, "deltas longer than the registry limit")

/-- The rewards and the penalties of each validator for one kind of vote, as SSZ bytes.

The preset, the configuration, the fork and the kind of vote are named in UTF-8.

The kinds are the file names of the vectors without their extension, such as source deltas.

A list longer than the registry limit has code 0. -/
@[export eth_consensus_rewards_deltas]
def rewardsDeltasExport (name fork component pre replacements : ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) pre
  encodeDeltas preset (← runDeltas config (← nameOf component) state)

/-- The deltas of several kinds of vote for one state, as SSZ bytes, in the order of the kinds.

The state is decoded once for all the kinds.

Each kind gives the same bytes as the export for one kind.

The first kind that fails gives the error. -/
@[export eth_consensus_rewards_deltas_batch]
def rewardsDeltasBatchExport (name fork : ByteArray) (components : Array ByteArray)
    (pre replacements : ByteArray) : Result (Array ByteArray) := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) pre
  components.mapM fun component => do
    encodeDeltas preset (← runDeltas config (← nameOf component) state)

end EthLib.Consensus.Exports
