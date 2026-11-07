module

public import EthLib.Consensus.Mutators

/-!
# `Consensus.Participation`

From Altair: the participation flags of the validators, and the base reward.

The state keeps one byte of flags for each validator, for the previous and the current epochs.

Each flag records one timely vote of an attestation: its source, its target or its head.

Bit `i` of the byte holds flag `i`, so only an index below 8 names a flag.

The rule uses the indices 0, 1 and 2.

The base reward of a validator is the reward of one epoch of timely votes on average.

Before Altair it grows with the effective balance over the square root of the total active balance.

From Altair it counts the effective balance in increments.

A sum, a product or a division that has no 64-bit result is an error.

A read past the end of a list is an error too.

Deneb rewards a timely target at any inclusion delay, as [EIP-7045] specifies.

Gloas also checks the payload of the head, which is not yet in EthLib, so the flags fail there.

[EIP-7045]: https://eips.ethereum.org/EIPS/eip-7045#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The byte that holds only the flag at an index below 8. -/
def flagBit (flagIndex : UInt64) : ParticipationFlags :=
  1 <<< flagIndex.toUInt8

/-- From Altair: the flags with the flag at an index set. -/
def addFlag (flags : ParticipationFlags) (flagIndex : UInt64) : ParticipationFlags :=
  flags ||| flagBit flagIndex

/-- From Altair: whether the flag at an index is set. -/
def hasFlag (flags : ParticipationFlags) (flagIndex : UInt64) : Bool :=
  flags &&& flagBit flagIndex == flagBit flagIndex

/-- From Altair: the index of the next validator to join the registry, the size of the registry. -/
def getIndexForNewValidator (state : BeaconState preset fork) : ValidatorIndex :=
  state.validators.data.size.toUInt64

/-- From Altair: a list with the entry at an index set.

When the index is the size of the list, the entry is added at its end.

An index past the size is an error, and so is an append to a full list. -/
def setOrAppendList {switch : Base.Fork} {α : Type} {limit : Nat}
    (list : ForkList switch fork α limit) (index : UInt64) (value : α) :
    Except AccessorError (ForkList switch fork α limit) :=
  if index.toNat = list.data.size then appendWithinLimit list value
  else if inside : index.toNat < list.data.size then
    .ok ⟨list.data.set index.toNat value inside, fun before => by simpa using list.bound before⟩
  else .error (.indexOutOfRange index)

/-- From Altair: a rooted list with the entry at an index set, or added at its end.

The rules and the errors are those of a plain list, and the tree is rehashed along one path. -/
def setOrAppendRooted {switch : Base.Fork} {α : Type} [SszType α] {limit : Nat}
    (list : RootedForkList switch fork α limit) (index : UInt64) (value : α) :
    Except AccessorError (RootedForkList switch fork α limit) :=
  if index.toNat = list.data.size then
    if fits : fork < switch → list.data.size + 1 ≤ limit then
      .ok (list.push value fun before => fits before)
    else .error (.listFull limit)
  else if inside : index.toNat < list.data.size then .ok (list.set index.toNat value inside)
  else .error (.indexOutOfRange index)

/-- From Altair: the base reward of one increment of effective balance.

It is a fixed factor of the increment over the square root of the total active balance.

The caller reads that total from the state once, and passes it. -/
def getBaseRewardPerIncrement (preset : Preset) (totalActiveBalance : Gwei) :
    Except AccessorError Gwei :=
  liftArith do
    divChecked (← mulChecked preset.EFFECTIVE_BALANCE_INCREMENT preset.BASE_REWARD_FACTOR)
      (integerSquareroot totalActiveBalance)

/-- The base reward of a validator, under the total active balance of the state.

Before Altair it is a fixed factor of its effective balance over the square root of the total.

The result is shared among the parts of an epoch reward.

From Altair it is the base reward of one increment, for each whole increment of effective balance.

The caller reads the total from the state once, and passes it for every validator.
-/
def getBaseReward (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (index : ValidatorIndex) : Except AccessorError Gwei := do
  let effectiveBalance := (← getValidator state index).effectiveBalance
  if .altair ≤ fork then
    let increments := effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT
    liftArith (mulChecked increments (← getBaseRewardPerIncrement preset totalActiveBalance))
  else
    let reward ← liftArith do
      divChecked (← mulChecked effectiveBalance preset.BASE_REWARD_FACTOR)
        (integerSquareroot totalActiveBalance)
    return reward / BASE_REWARDS_PER_EPOCH

/-- From Altair: the validators active in a recent epoch, not slashed, with a flag set for it.

The epoch must be the previous or the current epoch.

The validators come as a set, in increasing order. -/
def getUnslashedParticipatingIndices (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (flagIndex : UInt64) (epoch : Epoch) : Except AccessorError (List ValidatorIndex) := do
  let current := getCurrentEpoch state
  let previous := getPreviousEpoch state
  if epoch = previous ∨ epoch = current then
    let participation :=
      if epoch = current then (state.currentEpochParticipation altair).data
      else (state.previousEpochParticipation altair).data
    let read ← (getActiveValidatorIndices state epoch).mapM fun index => do
      let some flags := participation[index.toNat]? | throw (.indexOutOfRange index)
      return (index, hasFlag flags flagIndex && !(← getValidator state index).slashed)
    return (read.filter (·.2)).map (·.1)
  else throw (.epochNotRecent epoch previous current)

/-- From Gloas: whether an attestation votes for the block proposed at its own slot.

A vote at slot zero always does.

Otherwise its block root must be the root at its slot, and not the root at the slot before.

So a vote for a block of an earlier slot, at a slot with no block, does not. -/
def isAttestationSameSlot (state : BeaconState preset fork) (data : AttestationData) :
    Except AccessorError Bool := do
  if data.slot = 0 then return true
  let slotRoot ← getBlockRootAtSlot state data.slot
  let previousRoot ← getBlockRootAtSlot state (data.slot - 1)
  return data.beaconBlockRoot == slotRoot && data.beaconBlockRoot != previousRoot

/-- From Gloas: whether the payload vote of an attestation matches the chain.

A vote for the block of its own slot cannot see a payload, so its index must be zero.

Any other vote names by its index whether the payload of its block is available.

The bit read is that of the parent slot of the block being processed.

A vote that can earn the head flag names the head at its slot, which is that parent. -/
def payloadMatches (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (data : AttestationData) (parentSlot : Slot) : Except AccessorError Bool := do
  if ← isAttestationSameSlot state data then
    if data.index = 0 then return true else throw (.sameSlotIndexNotZero data.index)
  let position := (parentSlot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat
  let some available := (state.executionPayloadAvailability gloas).bits[position]?
    | throw (.bitOutOfRange position)
  return data.index == if available then 1 else 0

/-- From Altair: the flags that an attestation earns, from the source, target and head it votes for.

The source must be the justified checkpoint of the epoch of its target.

A timely source needs an inclusion delay of at most the square root of the slots of an epoch.

A target counts when the source counts too, and before Deneb only within one epoch of delay.

A head counts when the target counts too, and only at the least inclusion delay.

From Gloas a head also needs its payload vote to match, read at the slot of the parent block. -/
def getAttestationParticipationFlagIndices (state : BeaconState preset fork)
    (data : AttestationData) (inclusionDelay : UInt64) (parentSlot : Slot) :
    Except AccessorError (List UInt64) := do
  let justified := if data.target.epoch = getCurrentEpoch state then
    state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint
  let matchingSource := data.source == justified
  let matchingTarget :=
    matchingSource && data.target.root == (← getBlockRoot state data.target.epoch)
  let payload ← (if gloas : .glamsterdam ≤ fork then payloadMatches state gloas data parentSlot
    else pure true)
  let matchingHead :=
    matchingTarget && data.beaconBlockRoot == (← getBlockRootAtSlot state data.slot) && payload
  if data.source = justified then
    return (if inclusionDelay ≤ integerSquareroot preset.SLOTS_PER_EPOCH then
        [TIMELY_SOURCE_FLAG_INDEX] else []) ++
      (if matchingTarget && (.dencun ≤ fork || inclusionDelay ≤ preset.SLOTS_PER_EPOCH) then
        [TIMELY_TARGET_FLAG_INDEX] else []) ++
      (if matchingHead && inclusionDelay == preset.MIN_ATTESTATION_INCLUSION_DELAY then
        [TIMELY_HEAD_FLAG_INDEX] else [])
  else throw .wrongSource

end EthLib.Consensus
