module

public import EthLib.Consensus.ForkChoice.Handlers
public import Std.Data.TreeSet

/-!
# `Consensus.Gossip.Seen`

What gossip validation reads besides a message: the messages seen so far, the clock and the head.

A node keeps, for each topic, the keys of the valid messages it has already received.

A message with a key already seen is ignored, so that each one spreads only once.

A key is recorded only when its message is valid.

The clock is the local time in milliseconds, which may run ahead of other nodes.

So a message dated up to a fixed disparity in the future still counts as current.

The checks that read the chain read the state after the head of the fork choice.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Base.Uint64

/-- The keys of the valid gossip messages that a node has seen, by topic.

A topic of a later fork leaves its keys empty before that fork. -/
structure Seen where
  /-- The validators whose voluntary exit was valid. -/
  voluntaryExitIndices : Std.TreeSet ValidatorIndex := ∅
  /-- The proposers whose proposer slashing was valid. -/
  proposerSlashingIndices : Std.TreeSet ValidatorIndex := ∅
  /-- The validators that a valid attester slashing could slash. -/
  attesterSlashingIndices : Std.TreeSet ValidatorIndex := ∅
  /-- From Capella: the validators whose change of BLS credentials was valid. -/
  blsToExecutionChangeIndices : Std.TreeSet ValidatorIndex := ∅
  deriving Inhabited

namespace Store

variable {preset : Preset} {fork : Fork} (config : Config) (store : Store preset fork)

/-- Whether an epoch starts after the current one, by the clock.

The clock may run ahead by the maximum gossip clock disparity.

A time before genesis, or one that leaves the 64-bit range, is an error. -/
def isFutureEpoch (epoch : Epoch) (currentTimeMs : UInt64) : Except ForkChoiceError Bool := do
  let latest ← (addChecked currentTimeMs config.MAXIMUM_GOSSIP_CLOCK_DISPARITY).mapError .arith
  let slot ← (computeSlotAtTimeMs config store.genesisTimeMs latest).mapError .arith
  return computeEpochAtSlot preset slot < epoch

/-- The state after the head of the fork choice. -/
def headState : Except ForkChoiceError (BeaconState preset fork) := do
  store.blockState (← store.getHead config).root

end Store

end EthLib.Consensus
