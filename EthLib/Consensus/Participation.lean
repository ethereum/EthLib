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

From Gloas the head flag also needs the payload vote to match the state, as [EIP-7732] specifies.

[EIP-7045]: https://eips.ethereum.org/EIPS/eip-7045#specification
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#state-transition
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The byte that holds only the flag at an index below 8. -/
def flagBit (flagIndex : UInt64) : ParticipationFlags :=
  -- `2^i` for the flag index `i`.
  1 <<< flagIndex.toUInt8

/-- From Altair: the flags with the flag at an index set. -/
def addFlag (flags : ParticipationFlags) (flagIndex : UInt64) : ParticipationFlags :=
  -- The bitwise OR of the flags with `2^i`.
  flags ||| flagBit flagIndex

/-- From Altair: whether the flag at an index is set. -/
def hasFlag (flags : ParticipationFlags) (flagIndex : UInt64) : Bool :=
  -- The bitwise AND of the flags with `2^i` is `2^i`.
  flags &&& flagBit flagIndex == flagBit flagIndex

/-- From Altair: the index of the next validator to join the registry, the size of the registry.

A registry of `2^64` validators or more has no such index, an overflow. -/
def getIndexForNewValidator (state : BeaconState preset fork) :
    Except AccessorError ValidatorIndex :=
  -- The count of validators in the registry.
  liftArith (ofNatChecked state.validators.data.size)

/-- From Altair: a list with the entry at an index set.

When the index is the size of the list, the entry is added at its end.

An index past the size is an error, and so is an append to a full list. -/
def setOrAppendList {switch : Base.Fork} {α : Type} {limit : Nat}
    (list : ForkList switch fork α limit) (index : UInt64) (value : α) :
    Except AccessorError (ForkList switch fork α limit) :=
  -- An index equal to the length appends.
  if index.toNat = list.data.size then appendWithinLimit list value
  -- An index below it replaces the entry.
  else if inside : index.toNat < list.data.size then
    .ok ⟨list.data.set index.toNat value inside, fun before => by simpa using list.bound before⟩
  else .error (.indexOutOfRange index)

/-- From Altair: a rooted list with the entry at an index set, or added at its end.

The rules and the errors are those of a plain list, and the tree is rehashed along one path. -/
def setOrAppendRooted {switch : Base.Fork} {α : Type} [SszType α] {limit : Nat}
    (list : RootedForkList switch fork α limit) (index : UInt64) (value : α) :
    Except AccessorError (RootedForkList switch fork α limit) :=
  -- An index equal to the length appends, within the limit of the list.
  if index.toNat = list.data.size then
    if fits : fork < switch → list.data.size + 1 ≤ limit then
      .ok (list.push value fun before => fits before)
    else .error (.listFull limit)
  -- An index below it replaces the entry.
  else if inside : index.toNat < list.data.size then .ok (list.set index.toNat value inside)
  else .error (.indexOutOfRange index)

/-- From Altair: the base reward of one increment of effective balance.

The caller reads the total active balance from the state once, and passes it. -/
def getBaseRewardPerIncrement (preset : Preset) (totalActiveBalance : Gwei) :
    Except AccessorError Gwei :=
  -- `EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR / isqrt(total)`, with integer division.
  liftArith do
    divChecked (← mulChecked preset.EFFECTIVE_BALANCE_INCREMENT preset.BASE_REWARD_FACTOR)
      (integerSquareroot totalActiveBalance)

/-- The base reward of a validator, under the total active balance of the state.

The caller reads the total from the state once, and passes it for every validator.
-/
def getBaseReward (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (index : ValidatorIndex) : Except AccessorError Gwei := do
  let effectiveBalance := (← getValidator state index).effectiveBalance
  -- From Altair: the base reward per increment, times the whole increments of effective balance.
  if .altair ≤ fork then
    let increments := effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT
    liftArith (mulChecked increments (← getBaseRewardPerIncrement preset totalActiveBalance))
  else
    -- Before Altair: `b * BASE_REWARD_FACTOR / isqrt(total)`, with `b` the effective balance.
    let reward ← liftArith do
      divChecked (← mulChecked effectiveBalance preset.BASE_REWARD_FACTOR)
        (integerSquareroot totalActiveBalance)
    -- Divided by `BASE_REWARDS_PER_EPOCH`, shared among the parts of a reward.
    return reward / BASE_REWARDS_PER_EPOCH

/-- From Altair: the validators active in a recent epoch, not slashed, with a flag set for it.

The epoch must be the previous or the current epoch.

The validators come as a set, in increasing order. -/
def getUnslashedParticipatingIndices (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (flagIndex : UInt64) (epoch : Epoch) : Except AccessorError (List ValidatorIndex) := do
  let current := getCurrentEpoch state
  let previous := getPreviousEpoch state
  -- The epoch is the previous or the current epoch.
  if epoch = previous ∨ epoch = current then
    -- The flags that the state keeps for that epoch.
    let participation :=
      if epoch = current then (state.currentEpochParticipation altair).data
      else (state.previousEpochParticipation altair).data
    -- The validators active in the epoch whose flag is set and who are not slashed.
    let read ← (← getActiveValidatorIndicesChecked state epoch).mapM fun index => do
      let some flags := participation[index.toNat]? | throw (.indexOutOfRange index)
      return (index, hasFlag flags flagIndex && !(← getValidator state index).slashed)
    return (read.filter (·.2)).map (·.1)
  else throw (.epochNotRecent epoch previous current)

/-- From Gloas: whether an attestation votes for the block proposed at its own slot.

A vote for a block of an earlier slot, at a slot with no block, does not. -/
def isAttestationSameSlot (state : BeaconState preset fork) (data : AttestationData) :
    Except AccessorError Bool := do
  -- A vote at slot 0 is always for the block of its slot.
  if data.slot = 0 then return true
  -- Otherwise its block root is the root at its slot `s`, and not the root at `s - 1`.
  let slotRoot ← getBlockRootAtSlot state data.slot
  let previousRoot ← getBlockRootAtSlot state (data.slot - 1)
  return data.beaconBlockRoot == slotRoot && data.beaconBlockRoot != previousRoot

/-- From Gloas: whether the payload vote of an attestation matches the chain. -/
def payloadMatches (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (data : AttestationData) (parentSlot : Slot) : Except AccessorError Bool := do
  -- EIP-7732: a vote for the block of its own slot cannot see a payload, so its index is 0.
  if ← isAttestationSameSlot state data then
    if data.index = 0 then return true else throw (.sameSlotIndexNotZero data.index)
  -- Any other vote names by its index, 1 or 0, whether the payload of its block is available.
  --
  -- The bit read is that of the parent slot of the block being processed.
  --
  -- A vote that can earn the head flag names the head at its slot, which is that parent.
  let position := (parentSlot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat
  let some available := (state.executionPayloadAvailability gloas).bits[position]?
    | throw (.bitOutOfRange position)
  return data.index == if available then 1 else 0

/-- From Altair: the flags that an attestation earns, from the source, target and head it votes for.

A wrong source is an error, and so is a nonzero index for a vote at its own slot from Gloas. -/
def getAttestationParticipationFlagIndices (state : BeaconState preset fork)
    (data : AttestationData) (inclusionDelay : UInt64) (parentSlot : Slot) :
    Except AccessorError (List UInt64) := do
  -- The justified checkpoint of the epoch of the target: current or previous.
  let justified := if data.target.epoch = getCurrentEpoch state then
    state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint
  -- The source matches when it is that checkpoint.
  let matchingSource := data.source == justified
  -- The target matches when the source does and its root is the block root at its first slot.
  let matchingTarget :=
    matchingSource && data.target.root == (← getBlockRoot state data.target.epoch)
  -- From Gloas, the payload vote matches, read at the slot of the parent block.
  let payload ← (if gloas : .glamsterdam ≤ fork then payloadMatches state gloas data parentSlot
    else pure true)
  -- The head matches when the target does and its root is that of the block at its slot.
  --
  -- From Gloas the payload vote must match too.
  let matchingHead :=
    matchingTarget && data.beaconBlockRoot == (← getBlockRootAtSlot state data.slot) && payload
  -- The source must match.
  if data.source = justified then
    -- A timely source: an inclusion delay of at most `isqrt(SLOTS_PER_EPOCH)`.
    return (if inclusionDelay ≤ integerSquareroot preset.SLOTS_PER_EPOCH then
        [TIMELY_SOURCE_FLAG_INDEX] else []) ++
      -- A timely target: a matching target, before Deneb within `SLOTS_PER_EPOCH` of delay.
      --
      -- From Deneb any delay counts, as EIP-7045 specifies.
      (if matchingTarget && (.dencun ≤ fork || inclusionDelay ≤ preset.SLOTS_PER_EPOCH) then
        [TIMELY_TARGET_FLAG_INDEX] else []) ++
      -- A timely head: a matching head at the least delay `MIN_ATTESTATION_INCLUSION_DELAY`.
      (if matchingHead && inclusionDelay == preset.MIN_ATTESTATION_INCLUSION_DELAY then
        [TIMELY_HEAD_FLAG_INDEX] else [])
  else throw (.wrongSource data.source.epoch data.source.root justified.epoch justified.root)

end EthLib.Consensus
