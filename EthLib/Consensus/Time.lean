module

public import EthLib.Base.Uint64
public import EthLib.Consensus.Config
public import EthLib.Consensus.Preset

/-!
# `Consensus.Time`

The beacon chain counts time in slots and epochs from genesis.

A slot lasts a fixed number of milliseconds, and an epoch is a fixed number of slots.

A conversion whose result leaves the 64-bit range fails there instead of wrapping.

Each division assumes a nonzero divisor, as every preset and configuration has.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

/-- Seconds in milliseconds, or the largest 64-bit integer when the product does not fit. -/
def secondsToMilliseconds (seconds : UInt64) : UInt64 :=
  if UINT64_MAX / 1000 < seconds then UINT64_MAX else seconds * 1000

/-- Milliseconds in whole seconds, rounded down. -/
def millisecondsToSeconds (milliseconds : UInt64) : UInt64 :=
  milliseconds / 1000

/-- The time at the start of a slot, in milliseconds, from the time of genesis. -/
def computeTimeAtSlotMs (config : Config) (genesisTimeMs : UInt64) (slot : Slot) :
    Except ArithError UInt64 := do
  addChecked genesisTimeMs (← mulChecked slot config.SLOT_DURATION_MS)

/-- The time at the start of a slot, in seconds, from the time of genesis. -/
def computeTimeAtSlot (config : Config) (genesisTime : UInt64) (slot : Slot) :
    Except ArithError UInt64 := do
  return millisecondsToSeconds
    (← computeTimeAtSlotMs config (secondsToMilliseconds genesisTime) slot)

/-- The slot at a time in milliseconds, from the time of genesis.

A time before genesis has no slot. -/
def computeSlotAtTimeMs (config : Config) (genesisTimeMs timeMs : UInt64) :
    Except ArithError Slot := do
  divChecked (← subChecked timeMs genesisTimeMs) config.SLOT_DURATION_MS

/-- The slot at a time in seconds, from the time of genesis. -/
def computeSlotAtTime (config : Config) (genesisTime time : UInt64) : Except ArithError Slot :=
  computeSlotAtTimeMs config (secondsToMilliseconds genesisTime) (secondsToMilliseconds time)

/-- The epoch that contains a slot. -/
def computeEpochAtSlot (preset : Preset) (slot : Slot) : Epoch :=
  slot / preset.SLOTS_PER_EPOCH

/-- The first slot of an epoch. -/
def computeStartSlotAtEpoch (preset : Preset) (epoch : Epoch) : Except ArithError Slot :=
  mulChecked epoch preset.SLOTS_PER_EPOCH

/-- The epoch in which an activation or an exit that starts in a given epoch takes effect.

The delay keeps the validators of an epoch fixed once the seed of its committees is known. -/
def computeActivationExitEpoch (preset : Preset) (epoch : Epoch) : Except ArithError Epoch := do
  addChecked (← addChecked epoch 1) preset.MAX_SEED_LOOKAHEAD

end EthLib.Consensus
