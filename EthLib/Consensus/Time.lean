module

public import EthLib.Base.Fork
public import EthLib.Base.Uint64
public import EthLib.Consensus.Config
public import EthLib.Consensus.Preset

/-!
# `Consensus.Time`

The beacon chain counts time in slots and epochs from genesis.

A slot lasts a fixed number of milliseconds, and an epoch is a fixed number of slots.

A conversion whose result leaves the 64-bit range fails there instead of wrapping.

Each division assumes a nonzero divisor, as every preset and configuration has.

A duty is due a fixed part of a slot after its start, given in basis points.

From Gloas, EIP-7732 moves the attestation and aggregation deadlines earlier, and adds two.
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

/-- From Altair: the period of the sync committees that contains an epoch.

A period is a fixed number of epochs, and one sync committee serves through each. -/
def computeSyncCommitteePeriod (preset : Preset) (epoch : Epoch) : UInt64 :=
  epoch / preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD

/-- From Altair: the period of the sync committees that contains a slot. -/
def computeSyncCommitteePeriodAtSlot (preset : Preset) (slot : Slot) : UInt64 :=
  computeSyncCommitteePeriod preset (computeEpochAtSlot preset slot)

/-- The first slot of an epoch. -/
def computeStartSlotAtEpoch (preset : Preset) (epoch : Epoch) : Except ArithError Slot :=
  mulChecked epoch preset.SLOTS_PER_EPOCH

/-- The slots of an epoch, in order.

The guides add the length of an epoch to its first slot, as a 64-bit sum.

So the slot after the last one must be a 64-bit slot too. -/
def epochSlots (preset : Preset) (epoch : Epoch) : Except ArithError (List Slot) := do
  let startSlot ← computeStartSlotAtEpoch preset epoch
  let _ ← addChecked startSlot preset.SLOTS_PER_EPOCH
  return (List.range preset.SLOTS_PER_EPOCH.toNat).map fun offset => startSlot + offset.toUInt64

/-- The epoch in which an activation or an exit that starts in a given epoch takes effect.

The delay keeps the validators of an epoch fixed once the seed of its committees is known. -/
def computeActivationExitEpoch (preset : Preset) (epoch : Epoch) : Except ArithError Epoch := do
  addChecked (← addChecked epoch 1) preset.MAX_SEED_LOOKAHEAD

/-- A part of a slot, in milliseconds and rounded down, from that part in basis points. -/
def getSlotComponentDurationMs (config : Config) (basisPoints : UInt64) :
    Except ArithError UInt64 := do
  return (← mulChecked basisPoints config.SLOT_DURATION_MS) / BASIS_POINTS

/-- The time into a slot after which a proposer does not reorganize its head. -/
def getProposerReorgCutoffMs (config : Config) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config config.PROPOSER_REORG_CUTOFF_BPS

/-- The time into a slot at which an attestation is due. -/
def getAttestationDueMs (config : Config) (fork : Fork) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config <|
    if fork ≥ .glamsterdam then config.ATTESTATION_DUE_BPS_GLOAS else config.ATTESTATION_DUE_BPS

/-- The time into a slot at which an aggregate is due. -/
def getAggregateDueMs (config : Config) (fork : Fork) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config <|
    if fork ≥ .glamsterdam then config.AGGREGATE_DUE_BPS_GLOAS else config.AGGREGATE_DUE_BPS

/-- From Altair: the time into a slot at which a sync committee message is due. -/
def getSyncMessageDueMs (config : Config) (fork : Fork) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config <|
    if fork ≥ .glamsterdam then config.SYNC_MESSAGE_DUE_BPS_GLOAS
    else config.SYNC_MESSAGE_DUE_BPS

/-- From Altair: the time into a slot at which a sync committee contribution is due. -/
def getContributionDueMs (config : Config) (fork : Fork) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config <|
    if fork ≥ .glamsterdam then config.CONTRIBUTION_DUE_BPS_GLOAS
    else config.CONTRIBUTION_DUE_BPS

/-- From Gloas: the time into a slot at which the builder's payload is due. -/
def getPayloadDueMs (config : Config) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config config.PAYLOAD_DUE_BPS

/-- From Gloas: the time into a slot at which a payload attestation is due. -/
def getPayloadAttestationDueMs (config : Config) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config config.PAYLOAD_ATTESTATION_DUE_BPS

/-- From Heze: the time into a slot by which an inclusion list must arrive to be timely. -/
def getInclusionListDueMs (config : Config) : Except ArithError UInt64 :=
  getSlotComponentDurationMs config config.INCLUSION_LIST_DUE_BPS

end EthLib.Consensus
