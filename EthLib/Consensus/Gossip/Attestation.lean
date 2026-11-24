module

public import EthLib.Consensus.Gossip.Block
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

From Gloas the index in the data says whether the vote sees the payload of its block, 0 or 1.

A vote in the slot of its block must say 0, since the payload cannot be there yet.

A vote that says 1 needs the payload verified, and not optimistic or invalid.

[EIP-7045]: https://eips.ethereum.org/EIPS/eip-7045#specification
[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Networking.Gossip Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Shared checks -/

/-- The error of a subnet computation as an error of arithmetic. -/
def SubnetError.toForkChoice {ε : Type} : SubnetError ε → ForkChoiceError
  -- No subnets make the rule divide by zero.
  | .zeroSubnetCount => .arith .divisionByZero
  -- Every other failure is an overflow.
  | _ => .arith .overflow

/-- Whether the block voted for is known, and passed validation. -/
def votedBlockOutcome (store : Store preset fork) (root : Root) : ValidationResult :=
  -- IGNORE unless the store holds the block voted for.
  (ignoreUnless (store.blocks.contains root) "block being voted for has not been seen").andThen
    fun _ =>
  -- REJECT unless the store holds its state, since a block without one failed validation.
  rejectUnless (store.blockStates.contains root) "block being voted for failed validation"

/-- The checks of the clock on the slot of a vote, with the reasons of the topic from Deneb. -/
def voteTimeOutcome (config : Config) (store : Store preset fork) (slot : Slot)
    (currentTimeMs : UInt64) (futureReason epochReason : String) :
    Except ForkChoiceError ValidationResult := do
  if .dencun ≤ fork then
    -- From Deneb, IGNORE when the slot starts after the clock plus the maximum gossip disparity.
    let future ← store.isFutureSlot config slot currentTimeMs
    (ignoreUnless (!future) futureReason).andThenM fun _ => do
    -- Let `e` be the epoch of the slot.
    --
    -- IGNORE unless the clock is in the epoch `e` or in the epoch `e + 1`.
    let recent ← store.isCurrentOrPreviousEpoch config (computeEpochAtSlot preset slot)
      currentTimeMs
    return ignoreUnless recent epochReason
  else
    -- Let `s` be the slot, and `R` be `ATTESTATION_PROPAGATION_SLOT_RANGE`.
    --
    -- Before Deneb, IGNORE unless the clock is in the slots `s` to `s + R`.
    let within ← store.isWithinSlotRange config slot config.ATTESTATION_PROPAGATION_SLOT_RANGE
      currentTimeMs
    return ignoreUnless within "attestation slot not within propagation range"

/-- The last checks of a vote: its target and the finalized checkpoint are ancestors of its block.
-/
def voteAncestryOutcome (store : Store preset fork) (root : Root) (target : Checkpoint) :
    Except ForkChoiceError ValidationResult := do
  -- REJECT unless the target root is the ancestor of the block voted for at the target epoch.
  let targetBlock ← store.getCheckpointBlock root target.epoch
  (rejectUnless (targetBlock == target.root)
    "target block is not an ancestor of LMD vote block").andThenM fun _ => do
  -- IGNORE unless the finalized root is its ancestor at the finalized epoch.
  let finalizedBlock ← store.getCheckpointBlock root store.finalizedCheckpoint.epoch
  return ignoreUnless (finalizedBlock == store.finalizedCheckpoint.root)
    "finalized checkpoint is not an ancestor of block"

/-- From Gloas: the checks of the payload that a vote sees, once its other checks pass. -/
def attestationPayloadOutcome (store : Store preset fork) (statuses : PayloadStatuses)
    (data : AttestationData) : Except ForkChoiceError ValidationResult := do
  if gloas : .glamsterdam ≤ fork then
    -- REJECT when the vote is in the slot of its block and its index is not 0.
    --
    -- The payload of that block cannot be there yet.
    let block ← store.block data.beaconBlockRoot
    (rejectUnless (block.slot != data.slot || data.index == 0)
      "same-slot attestation must attest with index 0").andThenM fun _ =>
    -- A vote whose index is not 1 sees no payload, so nothing more is checked.
    if data.index != 1 then return .accept else
    -- IGNORE unless the payload of the block is seen and verified.
    --
    -- A vote of index 1 is ignored until that payload has been seen, as EIP-7732 specifies.
    (ignoreUnless (store.isPayloadVerified gloas data.beaconBlockRoot)
      "execution payload envelope has not been seen").andThenM fun _ =>
    -- The status of the payload, not validated when the node holds none.
    let status := statuses.get data.beaconBlockRoot
    -- IGNORE when that status is not validated, since the payload is then optimistic.
    return (ignoreUnless (status != PAYLOAD_STATUS_NOT_VALIDATED)
      "attested payload is optimistic").andThen fun _ =>
      -- REJECT when the payload is invalid.
      rejectUnless (status != PAYLOAD_STATUS_INVALIDATED) "attested payload is invalid"
  -- Before Gloas there is nothing to check.
  else return .accept

/-- The last checks of a vote: its ancestors, then from Gloas the payload it sees. -/
def voteOutcome (store : Store preset fork) (statuses : PayloadStatuses) (data : AttestationData) :
    Except ForkChoiceError ValidationResult := do
  -- The checks of the target and of the finalized checkpoint.
  (← voteAncestryOutcome store data.beaconBlockRoot data.target).andThenM fun _ =>
  -- From Gloas, the checks of the payload that the vote sees.
  attestationPayloadOutcome store statuses data

/-- From Electra: whether the index in the data of a vote is allowed. -/
def isValidDataIndex (fork : Fork) (index : CommitteeIndex) : Bool :=
  -- From Gloas the index is 0 or 1, and before Gloas it is 0.
  if .glamsterdam ≤ fork then index ≤ 1 else index == 0

/-- From Electra: the check of the index in the data of a vote, with the reasons of a topic. -/
def dataIndexOutcome (fork : Fork) (index : CommitteeIndex) (zeroReason binaryReason : String) :
    ValidationResult :=
  -- REJECT unless the index is allowed, with the reason of the fork.
  rejectUnless (isValidDataIndex fork index)
    (if .glamsterdam ≤ fork then binaryReason else zeroReason)

/-- The member of a committee whose bit is set first, if a bit is set. -/
def firstAttester (committee : Array ValidatorIndex) (bits : Array Bool) :
    Option ValidatorIndex :=
  -- The first member, in committee order, whose bit is set.
  (committee.toList.zip bits.toList).findSome? fun (member, bit) =>
    if bit then some member else none

/-- Whether a selection proof makes its signer an aggregator of a committee.

The modulus aims at a fixed number of aggregators in each committee. -/
def isAggregator (committeeSize : Nat) (selectionProof : BLSSignature) : Bool :=
  -- Let `n` be the size of the committee.
  --
  -- The modulus is `max(1, floor(n / TARGET_AGGREGATORS_PER_COMMITTEE))`.
  let modulo := max 1 (committeeSize.toUInt64 / TARGET_AGGREGATORS_PER_COMMITTEE)
  -- Let `h` be the SHA-256 hash of the proof.
  let hash := Cryptography.Hash.Sha256.hash32 (packBytes selectionProof)
  -- The integer of the first 8 bytes of `h`, read little-endian, is a multiple of the modulus.
  UInt64.ofNat (ByteOrder.ofLE (Vector.ofFn fun i : Fin 8 => hash[i.val])) % modulo == 0

/-! ## Attestations -/

/-- Before Electra: the checks of an attestation on a subnet, at a time in milliseconds. -/
def validateBeaconAttestation (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (_early : fork < .pectra) (attestation : Attestation preset fork)
    (currentTimeMs subnetId : UInt64) : Except ForkChoiceError ValidationResult :=
  let data := attestation.data
  let bits := attestation.aggregationBits.bits
  -- IGNORE unless the block voted for is known, and REJECT unless it passed validation.
  (votedBlockOutcome store data.beaconBlockRoot).andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the committee index is below the committee count per slot of the target epoch.
  let committees := getCommitteeCountPerSlot state data.target.epoch
  (rejectUnless (data.index < committees) "committee index out of range").andThenM fun _ => do
  -- REJECT unless the subnet of the topic is that of the committee at the slot of the vote.
  let subnet ← (computeSubnetForAttestation preset config committees data.slot data.index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "attestation is for wrong subnet").andThenM fun _ => do
  -- IGNORE unless the clock allows the slot of the vote.
  (← voteTimeOutcome config store data.slot currentTimeMs "attestation slot is from a future slot"
    "attestation epoch is not current or previous epoch").andThenM fun _ =>
  -- REJECT unless the target epoch is the epoch of the slot.
  (rejectUnless (data.target.epoch == computeEpochAtSlot preset data.slot)
    "attestation epoch does not match target epoch").andThenM fun _ =>
  -- REJECT unless exactly one bit is set.
  (rejectUnless (bits.count true == 1) "attestation is not unaggregated").andThenM fun _ => do
  -- REJECT unless there is one bit for each member of the committee.
  let committee ← (getBeaconCommittee state data.slot data.index).mapError .accessor
  (rejectUnless (bits.size == committee.size)
    "aggregation bits length does not match committee size").andThenM fun _ => do
  -- The attester is the member whose bit is set.
  --
  -- One bit is set, and there is one bit for each member, so the attester exists.
  let some attester := firstAttester committee bits
    | throw (.accessor (.bitOutOfRange bits.size))
  -- IGNORE when a valid attestation of the attester for the target epoch was already seen.
  (ignoreUnless (!seen.attestationValidatorEpochs.contains (data.target.epoch, attester))
    "already seen attestation for this epoch and validator").andThenM fun _ => do
  -- REJECT unless the attestation, in indexed form, is valid: its attester signed its data.
  let indexed ← (getIndexedAttestation state attestation).mapError .accessor
  let valid ← (isValidIndexedAttestation config checks state indexed).mapError .transition
  (rejectUnless valid "invalid attestation signature").andThenM fun _ =>
  -- The checks of the target and of the finalized checkpoint.
  voteAncestryOutcome store data.beaconBlockRoot data.target

/-- Before Electra: the attester of an attestation, whose key a valid attestation records. -/
def beaconAttestationAttester (config : Config) (store : Store preset fork)
    (attestation : Attestation preset fork) : Except ForkChoiceError (Option ValidatorIndex) := do
  -- The member of the committee whose bit is set, in the state after the head.
  let state ← store.headState config
  let committee ← (getBeaconCommittee state attestation.data.slot attestation.data.index).mapError
    .accessor
  return firstAttester committee attestation.aggregationBits.bits

/-- The keys after a valid attestation: its target epoch and its attester. -/
def Seen.recordAttestation (seen : Seen) (target : Epoch) (attester : ValidatorIndex) : Seen :=
  -- The target epoch and the attester join the keys of attesters.
  { seen with attestationValidatorEpochs := (target, attester) :: seen.attestationValidatorEpochs }

/-- From Electra: the checks of a single attestation on a subnet, at a time in milliseconds.

From Gloas the payload it sees is checked with the statuses of payloads. -/
def validateSingleAttestation (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (statuses : PayloadStatuses) (_electra : .pectra ≤ fork)
    (attestation : SingleAttestation) (currentTimeMs subnetId : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let data := attestation.data
  let index := attestation.committeeIndex
  -- IGNORE when a valid attestation of the attester for the target epoch was already seen.
  (ignoreUnless
    (!seen.attestationValidatorEpochs.contains (data.target.epoch, attestation.attesterIndex))
    "already seen attestation for this epoch and validator").andThenM fun _ =>
  -- REJECT unless the index in the data is allowed.
  --
  -- That index is 0, since the attestation names its committee itself, as EIP-7549 specifies.
  --
  -- From Gloas it is 0 or 1, and says whether the vote sees the payload, as EIP-7732 specifies.
  (dataIndexOutcome fork data.index "attestation data index is non-zero"
    "attestation data index must be 0 or 1").andThenM fun _ =>
  -- IGNORE unless the block voted for is known, and REJECT unless it passed validation.
  (votedBlockOutcome store data.beaconBlockRoot).andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the committee index is below the committee count per slot of the target epoch.
  let committees := getCommitteeCountPerSlot state data.target.epoch
  (rejectUnless (index < committees) "committee index out of range").andThenM fun _ => do
  -- REJECT unless the subnet of the topic is that of the committee at the slot of the vote.
  let subnet ← (computeSubnetForAttestation preset config committees data.slot index).mapError
    SubnetError.toForkChoice
  (rejectUnless (subnet == subnetId) "attestation is for wrong subnet").andThenM fun _ => do
  -- IGNORE unless the clock allows the slot of the vote.
  (← voteTimeOutcome config store data.slot currentTimeMs "attestation slot is from a future slot"
    "attestation epoch is not current or previous epoch").andThenM fun _ =>
  -- REJECT unless the target epoch is the epoch of the slot.
  (rejectUnless (data.target.epoch == computeEpochAtSlot preset data.slot)
    "attestation epoch does not match target epoch").andThenM fun _ => do
  -- REJECT unless the attester is a member of the committee, as EIP-7549 specifies.
  let committee ← (getBeaconCommittee state data.slot index).mapError .accessor
  (rejectUnless (committee.contains attestation.attesterIndex)
    "attester is not a member of the committee").andThenM fun _ => do
  -- REJECT unless the attester signed the data, under `DOMAIN_BEACON_ATTESTER` at the target epoch.
  let attester ← (getValidator state attestation.attesterIndex).mapError .accessor
  let valid ← isValidSignatureAtEpoch config checks state DOMAIN_BEACON_ATTESTER data.target.epoch
    data attester.pubkey attestation.signature
  (rejectUnless valid "invalid attestation signature").andThenM fun _ =>
  -- The checks of the target and of the finalized checkpoint, then from Gloas of the payload.
  voteOutcome store statuses data

/-! ## Aggregates -/

/-- The key of an aggregate in the keys seen: the root of its data, with its committee from Electra.

Before Electra the root alone is the key, so the committee there is 0. -/
def aggregateKey (fork : Fork) (root : Root) (index : CommitteeIndex) : Root × CommitteeIndex :=
  -- The root, with the committee from Electra and 0 before.
  (root, if .pectra ≤ fork then index else 0)

/-- The bits of the valid aggregates seen for the root of a data and a committee. -/
def Seen.aggregateBitsFor (seen : Seen) (key : Root × CommitteeIndex) : List (List Bool) :=
  -- The bits of each recorded aggregate whose key is the key, in the order of the record.
  seen.aggregateBits.filterMap fun (seenKey, bits) => if seenKey = key then some bits else none

/-- The checks of a signed aggregate once its committee is known, at a time in milliseconds.

From Electra the committee comes from the committee bits, and before from the data.

From Gloas the payload it sees is checked with the statuses of payloads.

The committee and the participants share one shuffle of the epoch of its slot, computed once. -/
def validateAggregateInCommittee (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (statuses : PayloadStatuses)
    (signed : SignedAggregateAndProof preset fork)
    (index : CommitteeIndex) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult := do
  let proof := signed.message
  let aggregate := proof.aggregate
  let data := aggregate.data
  let bits := aggregate.aggregationBits.bits
  let root ← (SszType.hashTreeRoot data).mapError .ssz
  -- IGNORE when a valid aggregate of the same data and committee sets every bit that it sets.
  let seenBits := seen.aggregateBitsFor (aggregateKey fork root index)
  (ignoreUnless (!isNonStrictSuperset seenBits bits.toList)
    "already seen aggregate for this data").andThenM fun _ =>
  -- IGNORE when a valid aggregate of the aggregator for the target epoch was already seen.
  (ignoreUnless (!seen.aggregatorEpochs.contains (data.target.epoch, proof.aggregatorIndex))
    "already seen aggregate for this epoch and aggregator").andThenM fun _ =>
  -- IGNORE unless the block voted for is known, and REJECT unless it passed validation.
  (votedBlockOutcome store data.beaconBlockRoot).andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the committee index is below the committee count per slot of the target epoch.
  (rejectUnless (index < getCommitteeCountPerSlot state data.target.epoch)
    "committee index out of range").andThenM fun _ => do
  -- IGNORE unless the clock allows the slot of the vote.
  (← voteTimeOutcome config store data.slot currentTimeMs "aggregate slot is from a future slot"
    "aggregate epoch is not current or previous epoch").andThenM fun _ =>
  -- REJECT unless the target epoch is the epoch of the slot.
  (rejectUnless (data.target.epoch == computeEpochAtSlot preset data.slot)
    "attestation epoch does not match target epoch").andThenM fun _ => do
  let epoch := computeEpochAtSlot preset data.slot
  -- The active validators and the shuffle of the epoch of the slot.
  --
  -- The committee alone would read this shuffle first, so sharing it changes no error.
  let (active, shuffled) ← (attesterShuffle state epoch).mapError .accessor
  let perSlot := getCommitteeCountPerSlot state epoch
  -- REJECT unless there is one bit for each member of the committee at the slot.
  let committee ← (beaconCommitteeOf preset data.slot index perSlot active shuffled).mapError
    .accessor
  (rejectUnless (bits.size == committee.size)
    "aggregation bits length does not match committee size").andThenM fun _ => do
  -- REJECT unless the aggregate has one participant at least.
  let participants ← (attestingIndicesOf aggregate perSlot active shuffled).mapError .accessor
  (rejectUnless (!participants.isEmpty) "aggregate has no participants").andThenM fun _ =>
  -- REJECT unless the selection proof selects the aggregator, for the size of the committee.
  (rejectUnless (isAggregator committee.size proof.selectionProof)
    "validator is not selected as aggregator").andThenM fun _ =>
  -- REJECT unless the aggregator is a member of the committee.
  (rejectUnless (committee.contains proof.aggregatorIndex)
    "aggregator is not a member of the committee").andThenM fun _ => do
  -- REJECT unless the selection proof is the signature of the aggregator on the slot.
  --
  -- The domain is that of `DOMAIN_SELECTION_PROOF` at the target epoch.
  let aggregator ← (getValidator state proof.aggregatorIndex).mapError .accessor
  let selected ← isValidSignatureAtEpoch config checks state DOMAIN_SELECTION_PROOF
    data.target.epoch data.slot aggregator.pubkey proof.selectionProof
  (rejectUnless selected "invalid selection proof signature").andThenM fun _ => do
  -- REJECT unless the aggregator signed the message, under `DOMAIN_AGGREGATE_AND_PROOF`.
  let signedByAggregator ← isValidSignatureAtEpoch config checks state DOMAIN_AGGREGATE_AND_PROOF
    data.target.epoch proof aggregator.pubkey signed.signature
  (rejectUnless signedByAggregator "invalid aggregator signature").andThenM fun _ => do
  -- REJECT unless the aggregate, in indexed form, is valid: its participants signed its data.
  --
  -- The indexed form alone would compute the same participants again.
  let indexed ← (indexedAttestationOf aggregate participants).mapError .accessor
  let valid ← (isValidIndexedAttestation config checks state indexed).mapError .transition
  (rejectUnless valid "invalid aggregate signature").andThenM fun _ =>
  -- The checks of the target and of the finalized checkpoint, then from Gloas of the payload.
  voteOutcome store statuses data

/-- The checks of a signed aggregate on its topic, at a time in milliseconds. -/
def validateAggregateAndProof (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (statuses : PayloadStatuses)
    (signed : SignedAggregateAndProof preset fork) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let aggregate := signed.message.aggregate
  if electra : .pectra ≤ fork then
    -- From Electra, REJECT unless the index in the data is allowed.
    --
    -- That index is 0, as EIP-7549 specifies.
    --
    -- From Gloas it is 0 or 1, and says whether the vote sees the payload, as EIP-7732 specifies.
    (dataIndexOutcome fork aggregate.data.index "aggregate data index is non-zero"
      "aggregate data index must be 0 or 1").andThenM fun _ =>
    -- REJECT unless the committee bits name exactly one committee, which the checks below use.
    match getCommitteeIndices (aggregate.committeeBits electra) with
    | [index] =>
      validateAggregateInCommittee config checks seen store statuses signed index currentTimeMs
    | _ => return .reject "aggregate committee bits must specify exactly one committee"
  -- Before Electra the committee is the index in the data.
  else validateAggregateInCommittee config checks seen store statuses signed aggregate.data.index
    currentTimeMs

/-- The committee in the key of an aggregate.

From Electra a valid aggregate names exactly one committee in its committee bits.

Before Electra the root of the data alone is the key. -/
def aggregateKeyCommittee (aggregate : Attestation preset fork) : CommitteeIndex :=
  -- From Electra, the first committee that the committee bits name, else 0.
  if electra : .pectra ≤ fork then
    (getCommitteeIndices (aggregate.committeeBits electra)).headD 0
  -- Before Electra, the committee 0.
  else 0

/-- The keys after a valid aggregate: its aggregator, and its bits for its data and committee.

The root of the data is an input, since computing it can fail. -/
def Seen.recordAggregateAndProof (seen : Seen) (signed : SignedAggregateAndProof preset fork)
    (root : Root) : Seen :=
  let aggregate := signed.message.aggregate
  { seen with
    -- The target epoch and the aggregator join the keys of aggregators.
    aggregatorEpochs :=
      (aggregate.data.target.epoch, signed.message.aggregatorIndex) :: seen.aggregatorEpochs
    -- The bits join the keys, under the root of the data and the committee.
    aggregateBits :=
      ((root, aggregateKeyCommittee aggregate), aggregate.aggregationBits.bits.toList) ::
        seen.aggregateBits }

end EthLib.Consensus
