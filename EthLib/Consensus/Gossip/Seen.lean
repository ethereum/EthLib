module

public import EthLib.Consensus.Containers.ProposerPreferences
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
  /-- From Altair: the slot, the validator and the subnet of each valid sync committee message. -/
  syncMessageKeys : List (Slot × ValidatorIndex × UInt64) := []
  /-- From Altair: the slot, the aggregator and the subcommittee of each valid contribution. -/
  syncContributionAggregatorKeys : List (Slot × ValidatorIndex × UInt64) := []
  /-- From Altair: the slot, the block root and the subcommittee of each valid contribution.

  Each key comes with the bits of the members that the contribution aggregates. -/
  syncContributionBits : List ((Slot × Root × UInt64) × List Bool) := []
  /-- The slot and the proposer of each valid block. -/
  proposerSlots : List (Slot × ValidatorIndex) := []
  /-- The target epoch and the attester of each valid attestation. -/
  attestationValidatorEpochs : List (Epoch × ValidatorIndex) := []
  /-- The target epoch and the aggregator of each valid aggregate. -/
  aggregatorEpochs : List (Epoch × ValidatorIndex) := []
  /-- The root of the data and the committee of each valid aggregate, with its bits.

  Before Electra the root alone is the key, so the committee there is 0. -/
  aggregateBits : List ((Root × CommitteeIndex) × List Bool) := []
  /-- At Deneb and Electra: the slot, the proposer and the index of each valid blob sidecar. -/
  blobSidecarTuples : List (Slot × ValidatorIndex × BlobIndex) := []
  /-- At Fulu: the slot, the proposer and the column index of each valid column sidecar. -/
  dataColumnSidecarTuples : List (Slot × ValidatorIndex × DataAvailability.ColumnIndex) := []
  /-- From Gloas: the block root and the column index of each valid column sidecar. -/
  dataColumnSidecarRoots : List (Root × DataAvailability.ColumnIndex) := []
  /-- From Gloas: the valid preferences of proposers, by proposal slot and dependent root. -/
  proposerPreferences : List ((Slot × Root) × ProposerPreferences) := []
  /-- From Gloas: the block root and the builder of each valid envelope. -/
  executionPayloadEnvelopes : List (Root × BuilderIndex) := []
  /-- From Gloas: the gas limit of the payload of each valid envelope, by the hash of the payload.

  Gossip validation reads nothing else of these payloads. -/
  executionPayloadGasLimits : List (Hash32 × UInt64) := []
  /-- From Gloas: the slot and the committee member of each valid payload vote. -/
  payloadAttestationValidators : List (Slot × ValidatorIndex) := []
  /-- From Gloas: the slot, the parent payload, the parent block and the builder of each valid bid.
  -/
  executionPayloadBids : List (Slot × Hash32 × Root × BuilderIndex) := []
  /-- From Gloas: the value of the latest valid bid, by its slot, parent payload and parent block.

  Each valid bid beats the value before it, so the latest value is the best. -/
  bestExecutionPayloadBids : List ((Slot × Hash32 × Root) × Gwei) := []
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

/-- Whether the clock is in a range of slots: from a slot to a given count of slots after it.

The range ends with the end of its last slot.

The clock may run ahead or behind by the maximum gossip clock disparity, at both ends.

A time or a slot that leaves the 64-bit range is an error. -/
def isWithinSlotRange (slot : Slot) (slotRange currentTimeMs : UInt64) :
    Except ForkChoiceError Bool := do
  let start ← (computeTimeAtSlotMs config store.genesisTimeMs slot).mapError .arith
  let latest ← (addChecked currentTimeMs config.MAXIMUM_GOSSIP_CLOCK_DISPARITY).mapError .arith
  if latest < start then return false
  let after ← (addChecked slot slotRange >>= (addChecked · 1)).mapError .arith
  let stop ← (computeTimeAtSlotMs config store.genesisTimeMs after).mapError .arith
  let earliest ← (addChecked stop config.MAXIMUM_GOSSIP_CLOCK_DISPARITY).mapError .arith
  return !(earliest < currentTimeMs)

/-- Whether the clock is in a slot, with the maximum gossip clock disparity at both ends. -/
def isCurrentSlot (slot : Slot) (currentTimeMs : UInt64) : Except ForkChoiceError Bool :=
  store.isWithinSlotRange config slot 0 currentTimeMs

/-- Whether a slot starts after the clock, which may run ahead by the maximum gossip disparity.

A time or a slot that leaves the 64-bit range is an error. -/
def isFutureSlot (slot : Slot) (currentTimeMs : UInt64) : Except ForkChoiceError Bool := do
  let start ← (computeTimeAtSlotMs config store.genesisTimeMs slot).mapError .arith
  let latest ← (addChecked currentTimeMs config.MAXIMUM_GOSSIP_CLOCK_DISPARITY).mapError .arith
  return latest < start

/-- Whether a slot started more than the maximum gossip clock disparity before the clock.

A time or a slot that leaves the 64-bit range is an error. -/
def isPastSlot (slot : Slot) (currentTimeMs : UInt64) : Except ForkChoiceError Bool := do
  let start ← (computeTimeAtSlotMs config store.genesisTimeMs slot).mapError .arith
  let latest ← (addChecked start config.MAXIMUM_GOSSIP_CLOCK_DISPARITY).mapError .arith
  return latest < currentTimeMs

/-- From Deneb: whether the clock is in an epoch, with the maximum gossip disparity at both ends.

A slot or a time that leaves the 64-bit range is an error. -/
def isWithinEpoch (epoch : Epoch) (currentTimeMs : UInt64) : Except ForkChoiceError Bool := do
  let start ← (computeStartSlotAtEpoch preset epoch).mapError .arith
  let range ← (subChecked preset.SLOTS_PER_EPOCH 1).mapError .arith
  store.isWithinSlotRange config start range currentTimeMs

/-- From Deneb: whether the clock is in an epoch or in the epoch after it.

Both tests run, so an error of either one is an error. -/
def isCurrentOrPreviousEpoch (epoch : Epoch) (currentTimeMs : UInt64) :
    Except ForkChoiceError Bool := do
  let current ← store.isWithinEpoch config epoch currentTimeMs
  let next ← (addChecked epoch 1).mapError .arith
  let previous ← store.isWithinEpoch config next currentTimeMs
  return current || previous

/-- The state after the head of the fork choice. -/
def headState : Except ForkChoiceError (BeaconState preset fork) := do
  store.blockState (← store.getHead config).root

end Store

variable {preset : Preset} {fork : Fork}

/-- Whether a key signed an object under a domain type, at an epoch. -/
def isValidSignatureAtEpoch {α : Type} [Serialization.Ssz.SszType α] (config : Config)
    (checks : SignatureChecks) (state : BeaconState preset fork) (domainType : DomainType)
    (epoch : Epoch) (object : α) (pubkey : Cryptography.Bls.BLSPubkey)
    (signature : Cryptography.Bls.BLSSignature) : Except ForkChoiceError Bool := do
  let domain ← (getDomain config state domainType (some epoch)).mapError .accessor
  let signingRoot ← (computeSigningRoot object domain).mapError .ssz
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signature)

/-- Whether a key signed an object under a domain type, at the epoch of a slot. -/
def isValidSignatureAtSlot {α : Type} [Serialization.Ssz.SszType α] (config : Config)
    (checks : SignatureChecks) (state : BeaconState preset fork) (domainType : DomainType)
    (slot : Slot) (object : α) (pubkey : Cryptography.Bls.BLSPubkey)
    (signature : Cryptography.Bls.BLSSignature) : Except ForkChoiceError Bool :=
  isValidSignatureAtEpoch config checks state domainType (computeEpochAtSlot preset slot) object
    pubkey signature

/-- Whether earlier bits cover new bits: one of them sets every bit that the new bits set.

Earlier bits of another length cover nothing, since they belong to a committee of another size.

So new bits of a wrong length are not ignored here, and a later check rejects them. -/
def isNonStrictSuperset (seenBits : List (List Bool)) (newBits : List Bool) : Bool :=
  seenBits.any fun prior =>
    prior.length == newBits.length && (prior.zip newBits).all fun (bit, newBit) => !newBit || bit

end EthLib.Consensus
