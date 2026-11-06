module

public import EthLib.Consensus.Gossip.Seen
public import EthLib.Consensus.Gossip.Topics
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.Gossip.Attestation`

Gossip validation of attestations and of aggregates.

A validator votes for a block, and sends its attestation on the subnet of its committee.

An aggregator of a committee combines those votes into an aggregate, which goes to every node.

The block voted for must be known and valid, and the vote must be recent.

The target of the vote must be an ancestor of that block, and so must the finalized checkpoint.

Before Deneb a vote is recent within a range of slots.

From Deneb it is recent in its epoch or in the next one, as [EIP-7045] specifies.

From Electra an attestation names its attester and its committee, as [EIP-7549] specifies.

An aggregate then names its committee by its committee bits.

The checks run in a fixed order, and the first check that fails gives the outcome.

The checks that read the chain read the state after the head.

From Gloas the rules are not yet specified here, so they fail.

[EIP-7045]: https://eips.ethereum.org/EIPS/eip-7045#specification
[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Networking.Gossip Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Shared checks -/

/-- The error of a subnet computation as an error of arithmetic.

No subnets make the rule divide by zero, and every other failure is an overflow. -/
def SubnetError.toForkChoice {ε : Type} : SubnetError ε → ForkChoiceError
  | .zeroSubnetCount => .arith .divisionByZero
  | _ => .arith .overflow

/-- Whether the block voted for is known, and passed validation.

An unknown block makes the vote ignored, and a block with no state makes it rejected. -/
def votedBlockOutcome (store : Store preset fork) (root : Root) : ValidationResult :=
  (ignoreUnless (store.blocks.contains root) "block being voted for has not been seen").andThen
    fun _ =>
  rejectUnless (store.blockStates.contains root) "block being voted for failed validation"

/-- The checks of the clock on the slot of a vote, with the reasons of the topic from Deneb.

Before Deneb the clock must be in a range of slots from the slot of the vote.

From Deneb the slot must not be in the future, and its epoch must be the current or the previous. -/
def voteTimeOutcome (config : Config) (store : Store preset fork) (slot : Slot)
    (currentTimeMs : UInt64) (futureReason epochReason : String) :
    Except ForkChoiceError ValidationResult := do
  if .dencun ≤ fork then
    let future ← store.isFutureSlot config slot currentTimeMs
    (ignoreUnless (!future) futureReason).andThenM fun _ => do
    let recent ← store.isCurrentOrPreviousEpoch config (computeEpochAtSlot preset slot)
      currentTimeMs
    return ignoreUnless recent epochReason
  else
    let within ← store.isWithinSlotRange config slot config.ATTESTATION_PROPAGATION_SLOT_RANGE
      currentTimeMs
    return ignoreUnless within "attestation slot not within propagation range"

/-- The last checks of a vote: its target and the finalized checkpoint are ancestors of its block.

A wrong target makes the vote rejected, and a block off the finalized chain makes it ignored. -/
def voteAncestryOutcome (store : Store preset fork) (root : Root) (target : Checkpoint) :
    Except ForkChoiceError ValidationResult := do
  let targetBlock ← store.getCheckpointBlock root target.epoch
  (rejectUnless (targetBlock == target.root)
    "target block is not an ancestor of LMD vote block").andThenM fun _ => do
  let finalizedBlock ← store.getCheckpointBlock root store.finalizedCheckpoint.epoch
  return ignoreUnless (finalizedBlock == store.finalizedCheckpoint.root)
    "finalized checkpoint is not an ancestor of block"

/-- The member of a committee whose bit is set first, if a bit is set. -/
def firstAttester (committee : Array ValidatorIndex) (bits : Array Bool) :
    Option ValidatorIndex :=
  (committee.toList.zip bits.toList).findSome? fun (member, bit) =>
    if bit then some member else none

/-- Whether a selection proof makes its signer an aggregator of a committee.

The first 8 bytes of the SHA-256 hash of the proof, read little-endian, give a number.

The proof selects its signer when that number is a multiple of a modulus.

The modulus aims at a fixed number of aggregators in each committee, and is at least 1. -/
def isAggregator (committeeSize : Nat) (selectionProof : BLSSignature) : Bool :=
  let modulo := max 1 (committeeSize.toUInt64 / TARGET_AGGREGATORS_PER_COMMITTEE)
  let hash := sha256Bytes32 (packBytes selectionProof)
  bytesToUint64 (Vector.ofFn fun i : Fin 8 => hash[i.val]) % modulo == 0

/-! ## Attestations -/

/-- Before Electra: the checks of an attestation on a subnet, at a time in milliseconds.

It must vote for a known valid block, from a committee of its slot, on the subnet of that committee.

It must be recent, and its slot must be in the epoch of its target.

It must set one bit, and have one bit for each member of its committee.

Its attester must not have a valid attestation for the target epoch already.

Its attester must have signed it, and its target and the finalized checkpoint must be ancestors. -/
def validateBeaconAttestation (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (_early : fork < .pectra) (attestation : Attestation preset fork)
    (currentTimeMs subnetId : UInt64) : Except ForkChoiceError ValidationResult :=
  let data := attestation.data
  let bits := attestation.aggregationBits.bits
  (votedBlockOutcome store data.beaconBlockRoot).andThenM fun _ => do
  let state ← store.headState config
  let committees := getCommitteeCountPerSlot state data.target.epoch
  (rejectUnless (data.index < committees) "committee index out of range").andThenM fun _ => do
  let subnet ← (computeSubnetForAttestation preset config committees data.slot data.index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "attestation is for wrong subnet").andThenM fun _ => do
  (← voteTimeOutcome config store data.slot currentTimeMs "attestation slot is from a future slot"
    "attestation epoch is not current or previous epoch").andThenM fun _ =>
  (rejectUnless (data.target.epoch == computeEpochAtSlot preset data.slot)
    "attestation epoch does not match target epoch").andThenM fun _ =>
  (rejectUnless (bits.count true == 1) "attestation is not unaggregated").andThenM fun _ => do
  let committee ← (getBeaconCommittee state data.slot data.index).mapError .accessor
  (rejectUnless (bits.size == committee.size)
    "aggregation bits length does not match committee size").andThenM fun _ => do
  -- One bit is set, and there is one bit for each member, so the attester exists.
  let some attester := firstAttester committee bits
    | throw (.accessor (.bitOutOfRange bits.size))
  (ignoreUnless (!seen.attestationValidatorEpochs.contains (data.target.epoch, attester))
    "already seen attestation for this epoch and validator").andThenM fun _ => do
  let indexed ← (getIndexedAttestation state attestation).mapError .accessor
  let valid ← (isValidIndexedAttestation config checks state indexed).mapError .transition
  (rejectUnless valid "invalid attestation signature").andThenM fun _ =>
  voteAncestryOutcome store data.beaconBlockRoot data.target

/-- Before Electra: the attester of an attestation, whose key a valid attestation records.

It is the member of the committee whose bit is set, in the head state. -/
def beaconAttestationAttester (config : Config) (store : Store preset fork)
    (attestation : Attestation preset fork) : Except ForkChoiceError (Option ValidatorIndex) := do
  let state ← store.headState config
  let committee ← (getBeaconCommittee state attestation.data.slot attestation.data.index).mapError
    .accessor
  return firstAttester committee attestation.aggregationBits.bits

/-- The keys after a valid attestation: its target epoch and its attester. -/
def Seen.recordAttestation (seen : Seen) (target : Epoch) (attester : ValidatorIndex) : Seen :=
  { seen with attestationValidatorEpochs := (target, attester) :: seen.attestationValidatorEpochs }

/-- From Electra: the checks of a single attestation on a subnet, at a time in milliseconds.

Its attester must not have a valid attestation for the target epoch already.

The index in its data must be zero, since the attestation names its committee itself.

It must vote for a known valid block, from a committee of its slot, on the subnet of that committee.

It must be recent, and its slot must be in the epoch of its target.

Its attester must be a member of its committee, and must have signed its data.

Its target and the finalized checkpoint must be ancestors of the block voted for. -/
def validateSingleAttestation (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (_electra : .pectra ≤ fork) (attestation : SingleAttestation)
    (currentTimeMs subnetId : UInt64) : Except ForkChoiceError ValidationResult :=
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork) else
  let data := attestation.data
  let index := attestation.committeeIndex
  (ignoreUnless
    (!seen.attestationValidatorEpochs.contains (data.target.epoch, attestation.attesterIndex))
    "already seen attestation for this epoch and validator").andThenM fun _ =>
  (rejectUnless (data.index == 0) "attestation data index is non-zero").andThenM fun _ =>
  (votedBlockOutcome store data.beaconBlockRoot).andThenM fun _ => do
  let state ← store.headState config
  let committees := getCommitteeCountPerSlot state data.target.epoch
  (rejectUnless (index < committees) "committee index out of range").andThenM fun _ => do
  let subnet ← (computeSubnetForAttestation preset config committees data.slot index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "attestation is for wrong subnet").andThenM fun _ => do
  (← voteTimeOutcome config store data.slot currentTimeMs "attestation slot is from a future slot"
    "attestation epoch is not current or previous epoch").andThenM fun _ =>
  (rejectUnless (data.target.epoch == computeEpochAtSlot preset data.slot)
    "attestation epoch does not match target epoch").andThenM fun _ => do
  let committee ← (getBeaconCommittee state data.slot index).mapError .accessor
  (rejectUnless (committee.contains attestation.attesterIndex)
    "attester is not a member of the committee").andThenM fun _ => do
  let some attester := state.validators.data[attestation.attesterIndex.toNat]?
    | throw (.accessor (.indexOutOfRange attestation.attesterIndex))
  let valid ← isValidSignatureAtEpoch config checks state DOMAIN_BEACON_ATTESTER data.target.epoch
    data attester.pubkey attestation.signature
  (rejectUnless valid "invalid attestation signature").andThenM fun _ =>
  voteAncestryOutcome store data.beaconBlockRoot data.target

/-! ## Aggregates -/

/-- The key of an aggregate in the keys seen: the root of its data, with its committee from Electra.

Before Electra the root alone is the key, so the committee there is 0. -/
def aggregateKey (fork : Fork) (root : Root) (index : CommitteeIndex) : Root × CommitteeIndex :=
  (root, if .pectra ≤ fork then index else 0)

/-- The bits of the valid aggregates seen for the root of a data and a committee. -/
def Seen.aggregateBitsFor (seen : Seen) (key : Root × CommitteeIndex) : List (List Bool) :=
  seen.aggregateBits.filterMap fun (seenKey, bits) => if seenKey = key then some bits else none

/-- The checks of a signed aggregate once its committee is known, at a time in milliseconds.

From Electra the committee comes from the committee bits, and before from the data.

A valid aggregate for the same data and committee that covers its bits makes it ignored.

So does a valid aggregate of its aggregator for the same target epoch.

It must vote for a known valid block, from a committee of its slot.

It must be recent, and its slot must be in the epoch of its target.

It must have one bit for each member of the committee, and one participant at least.

Its selection proof must select its aggregator, a member of the committee.

The aggregator must have signed the slot and the aggregate, and the participants the data.

Its target and the finalized checkpoint must be ancestors of the block voted for. -/
def validateAggregateInCommittee (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (signed : SignedAggregateAndProof preset fork)
    (index : CommitteeIndex) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult := do
  let proof := signed.message
  let aggregate := proof.aggregate
  let data := aggregate.data
  let bits := aggregate.aggregationBits.bits
  let root ← (SszType.hashTreeRoot data).mapError .ssz
  let seenBits := seen.aggregateBitsFor (aggregateKey fork root index)
  (ignoreUnless (!isNonStrictSuperset seenBits bits.toList)
    "already seen aggregate for this data").andThenM fun _ =>
  (ignoreUnless (!seen.aggregatorEpochs.contains (data.target.epoch, proof.aggregatorIndex))
    "already seen aggregate for this epoch and aggregator").andThenM fun _ =>
  (votedBlockOutcome store data.beaconBlockRoot).andThenM fun _ => do
  let state ← store.headState config
  (rejectUnless (index < getCommitteeCountPerSlot state data.target.epoch)
    "committee index out of range").andThenM fun _ => do
  (← voteTimeOutcome config store data.slot currentTimeMs "aggregate slot is from a future slot"
    "aggregate epoch is not current or previous epoch").andThenM fun _ =>
  (rejectUnless (data.target.epoch == computeEpochAtSlot preset data.slot)
    "attestation epoch does not match target epoch").andThenM fun _ => do
  let committee ← (getBeaconCommittee state data.slot index).mapError .accessor
  (rejectUnless (bits.size == committee.size)
    "aggregation bits length does not match committee size").andThenM fun _ => do
  let participants ← (getAttestingIndices state aggregate).mapError .accessor
  (rejectUnless (!participants.isEmpty) "aggregate has no participants").andThenM fun _ =>
  (rejectUnless (isAggregator committee.size proof.selectionProof)
    "validator is not selected as aggregator").andThenM fun _ =>
  (rejectUnless (committee.contains proof.aggregatorIndex)
    "aggregator is not a member of the committee").andThenM fun _ => do
  let some aggregator := state.validators.data[proof.aggregatorIndex.toNat]?
    | throw (.accessor (.indexOutOfRange proof.aggregatorIndex))
  let selected ← isValidSignatureAtEpoch config checks state DOMAIN_SELECTION_PROOF
    data.target.epoch data.slot aggregator.pubkey proof.selectionProof
  (rejectUnless selected "invalid selection proof signature").andThenM fun _ => do
  let signedByAggregator ← isValidSignatureAtEpoch config checks state DOMAIN_AGGREGATE_AND_PROOF
    data.target.epoch proof aggregator.pubkey signed.signature
  (rejectUnless signedByAggregator "invalid aggregator signature").andThenM fun _ => do
  let indexed ← (getIndexedAttestation state aggregate).mapError .accessor
  let valid ← (isValidIndexedAttestation config checks state indexed).mapError .transition
  (rejectUnless valid "invalid aggregate signature").andThenM fun _ =>
  voteAncestryOutcome store data.beaconBlockRoot data.target

/-- The checks of a signed aggregate on its topic, at a time in milliseconds.

Before Electra the committee is the index in the data.

From Electra that index must be zero, and the committee bits must name exactly one committee.

From Gloas the rule is not yet specified here, so it fails. -/
def validateAggregateAndProof (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (signed : SignedAggregateAndProof preset fork)
    (currentTimeMs : UInt64) : Except ForkChoiceError ValidationResult :=
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork) else
  let aggregate := signed.message.aggregate
  if electra : .pectra ≤ fork then
    (rejectUnless (aggregate.data.index == 0) "aggregate data index is non-zero").andThenM
      fun _ =>
    match getCommitteeIndices (aggregate.committeeBits electra) with
    | [index] => validateAggregateInCommittee config checks seen store signed index currentTimeMs
    | _ => return .reject "aggregate committee bits must specify exactly one committee"
  else validateAggregateInCommittee config checks seen store signed aggregate.data.index
    currentTimeMs

/-- The committee in the key of an aggregate: from Electra the first that its committee bits name.

A valid aggregate names exactly one there.

Before Electra the key holds the committee 0, so the root of the data alone is the key. -/
def aggregateKeyCommittee (aggregate : Attestation preset fork) : CommitteeIndex :=
  if electra : .pectra ≤ fork then
    (getCommitteeIndices (aggregate.committeeBits electra)).headD 0
  else 0

/-- The keys after a valid aggregate: its aggregator, and its bits for its data and committee.

The root of the data is an input, since computing it can fail. -/
def Seen.recordAggregateAndProof (seen : Seen) (signed : SignedAggregateAndProof preset fork)
    (root : Root) : Seen :=
  let aggregate := signed.message.aggregate
  { seen with
    aggregatorEpochs :=
      (aggregate.data.target.epoch, signed.message.aggregatorIndex) :: seen.aggregatorEpochs
    aggregateBits :=
      ((root, aggregateKeyCommittee aggregate), aggregate.aggregationBits.bits.toList) ::
        seen.aggregateBits }

end EthLib.Consensus
