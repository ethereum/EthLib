module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Consensus.Gossip.SyncCommittee
public import EthLib.Consensus.Mutators
public import EthLib.Cryptography.Bls.Signatures

/-!
# `Consensus.HonestValidator`

The duties of an honest validator.

They are what it computes to propose, attest, aggregate and serve on a sync committee.

A validator finds its committee for an epoch, and whether it proposes a block.

From Altair, it finds whether it serves on a sync committee, and on which subnets.

Each message it sends carries its BLS signature of the message's signing root.

The root joins the root of the message with a domain of a kind of message, a fork and a chain.

Each kind of message has its own domain type, so two kinds are signed under different domains.

Each duty signs one object at one epoch:

- The RANDAO reveal signs the epoch of the block, at that epoch.
- A block is signed at the epoch of its slot.
- Attestation data is signed at its target epoch.
- A selection proof signs a slot, at the epoch of the slot.
- An aggregate and proof is signed at the epoch of the aggregate's slot.
- A sync committee message signs a block root, at the current epoch.
- A sync selection proof signs selection data, at the epoch of its slot.
- A contribution and proof is signed at the epoch of its slot.

The guides of the later forks, up to Heze, change none of these duties and only add others.

The steps that read the network or the execution layer are not specified here.

The choice of a head is one of them.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Why a duty of a validator has no result. -/
inductive ValidatorDutyError where
  /-- A state accessor fails. -/
  | accessor (error : AccessorError)
  /-- A root cannot be computed. -/
  | ssz (error : Err)
  /-- The BLS signature fails. -/
  | bls (error : BlsError)
  /-- A 64-bit operation has no result. -/
  | arith (error : ArithError)
  /-- An assignment is asked for an epoch after the next one. -/
  | epochTooFar (epoch nextEpoch : Epoch)
  /-- A sync committee assignment is asked for a period other than the current or the next. -/
  | periodOutOfRange (period currentPeriod : UInt64)

/-- The code of an error at the C boundary, one for each constructor. -/
def ValidatorDutyError.code : ValidatorDutyError → UInt32
  | .accessor _ => 1
  | .ssz _ => 2
  | .bls _ => 3
  | .arith _ => 4
  | .epochTooFar .. => 5
  | .periodOutOfRange .. => 6

/-! ## Assignments -/

/-- The first committee of some slots and indices that holds a validator.

It comes with its index and its slot. -/
def findCommittee (state : BeaconState preset fork) (validatorIndex : ValidatorIndex) :
    List (Slot × CommitteeIndex) →
      Except ValidatorDutyError (Option (Array ValidatorIndex × CommitteeIndex × Slot))
  | [] => return none
  | (slot, index) :: rest => do
    let committee ← (getBeaconCommittee state slot index).mapError .accessor
    if validatorIndex ∈ committee then return some (committee, index, slot)
    findCommittee state validatorIndex rest

/-- The slots of an epoch, each with the indices of its committees, in order. -/
def committeePositions (state : BeaconState preset fork) (epoch : Epoch) :
    Except ValidatorDutyError (List (Slot × CommitteeIndex)) := do
  let startSlot ← (computeStartSlotAtEpoch preset epoch).mapError .arith
  -- The last slot of the epoch must be a 64-bit slot.
  if startSlot.toNat + preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64 then
    let perSlot := getCommitteeCountPerSlot state epoch
    return (List.range preset.SLOTS_PER_EPOCH.toNat).flatMap fun offset =>
      (List.range perSlot.toNat).map fun index => (startSlot + offset.toUInt64, index.toUInt64)
  else throw (.arith .overflow)

/-- The committee of a validator in an epoch, with the index and the slot of the committee.

The epoch must be at most the next one, since later committees are not known yet.

A validator that is not active in the epoch has no committee. -/
def getCommitteeAssignment (state : BeaconState preset fork) (epoch : Epoch)
    (validatorIndex : ValidatorIndex) :
    Except ValidatorDutyError (Option (Array ValidatorIndex × CommitteeIndex × Slot)) := do
  let nextEpoch ← (addChecked (getCurrentEpoch state) 1).mapError .arith
  if epoch ≤ nextEpoch then findCommittee state validatorIndex (← committeePositions state epoch)
  else throw (.epochTooFar epoch nextEpoch)

/-- Whether a validator proposes the block of the slot of a state. -/
def isProposer (state : BeaconState preset fork) (validatorIndex : ValidatorIndex) :
    Except ValidatorDutyError Bool := do
  return (← (getBeaconProposerIndex state).mapError .accessor) == validatorIndex

/-- From Altair: whether a validator serves on the sync committee of the period of an epoch.

The period must be the current one or the next, since the state holds only those committees. -/
def isAssignedToSyncCommittee (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (epoch : Epoch) (validatorIndex : ValidatorIndex) : Except ValidatorDutyError Bool := do
  let period := computeSyncCommitteePeriod preset epoch
  let currentPeriod := computeSyncCommitteePeriod preset (getCurrentEpoch state)
  let nextPeriod ← (addChecked currentPeriod 1).mapError .arith
  unless period = currentPeriod ∨ period = nextPeriod do
    throw (.periodOutOfRange period currentPeriod)
  let pubkey := (← (getValidator state validatorIndex).mapError .accessor).pubkey
  if period = currentPeriod then
    return (state.currentSyncCommittee altair).pubkeys.contains pubkey
  else
    return (state.nextSyncCommittee altair).pubkeys.contains pubkey

/-- From Altair: the sync committee subnets of a validator for the next slot.

The committee is the current one, unless the next slot starts a new period.

Each seat of the validator in the committee gives the subnet of its subcommittee.

The subnets come once each, in increasing order. -/
def computeSubnetsForSyncCommittee (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (validatorIndex : ValidatorIndex) : Except ValidatorDutyError (List UInt64) := do
  let syncCommittee ← (syncCommitteeAtNextSlot state altair).mapError .arith
  let targetPubkey := (← (getValidator state validatorIndex).mapError .accessor).pubkey
  return (syncSubnetsOfPubkey syncCommittee targetPubkey).mergeSort (· ≤ ·)

/-! ## Signatures -/

/-- The signature of an object by a secret key, under a domain type at an epoch.

It signs the signing root of the object with the domain of the state at that epoch. -/
def signAtEpoch {α : Type} [SszType α] (config : Config) (state : BeaconState preset fork)
    (domainType : DomainType) (epoch : Epoch) (object : α) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature := do
  let domain ← (getDomain config state domainType (some epoch)).mapError .accessor
  let signingRoot ← (computeSigningRoot object domain).mapError .ssz
  (Signatures.sign key (packBytes signingRoot)).mapError .bls

/-- The RANDAO reveal of a block: the signature of the epoch of its slot. -/
def getEpochSignature (config : Config) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  let epoch := computeEpochAtSlot preset block.slot
  signAtEpoch config state DOMAIN_RANDAO epoch epoch key

/-- The signature of a block by its proposer, in the epoch of its slot. -/
def getBlockSignature (config : Config) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  signAtEpoch config state DOMAIN_BEACON_PROPOSER (computeEpochAtSlot preset block.slot) block key

/-- The signature of attestation data, in its target epoch. -/
def getAttestationSignature (config : Config) (state : BeaconState preset fork)
    (attestationData : AttestationData) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  signAtEpoch config state DOMAIN_BEACON_ATTESTER attestationData.target.epoch attestationData key

/-- The selection proof of a slot: the signature of the slot, in its epoch.

It decides whether the validator aggregates for its committee in that slot. -/
def getSlotSignature (config : Config) (state : BeaconState preset fork) (slot : Slot)
    (key : Signatures.SecretKey) : Except ValidatorDutyError BLSSignature :=
  signAtEpoch config state DOMAIN_SELECTION_PROOF (computeEpochAtSlot preset slot) slot key

/-- An aggregate with the index of its aggregator and its selection proof. -/
def getAggregateAndProof (config : Config) (state : BeaconState preset fork)
    (aggregatorIndex : ValidatorIndex) (aggregate : Attestation preset fork)
    (key : Signatures.SecretKey) : Except ValidatorDutyError (AggregateAndProof preset fork) := do
  return {
    aggregatorIndex, aggregate,
    selectionProof := ← getSlotSignature config state aggregate.data.slot key }

/-- The signature of an aggregate and proof, in the epoch of the aggregate's slot. -/
def getAggregateAndProofSignature (config : Config) (state : BeaconState preset fork)
    (aggregateAndProof : AggregateAndProof preset fork) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  signAtEpoch config state DOMAIN_AGGREGATE_AND_PROOF
    (computeEpochAtSlot preset aggregateAndProof.aggregate.data.slot) aggregateAndProof key

/-- From Altair: the message of a sync committee member for a block root, at the slot of the state.

It signs the root in the current epoch. -/
def getSyncCommitteeMessage (config : Config) (state : BeaconState preset fork) (blockRoot : Root)
    (validatorIndex : ValidatorIndex) (key : Signatures.SecretKey) :
    Except ValidatorDutyError SyncCommitteeMessage := do
  let signature ←
    signAtEpoch config state DOMAIN_SYNC_COMMITTEE (getCurrentEpoch state) blockRoot key
  return { slot := state.slot, beaconBlockRoot := blockRoot, validatorIndex, signature }

/-- From Altair: the selection proof of a subcommittee at a slot, in the epoch of the slot. -/
def getSyncCommitteeSelectionProof (config : Config) (state : BeaconState preset fork)
    (slot : Slot) (subcommitteeIndex : UInt64) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  signAtEpoch config state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF (computeEpochAtSlot preset slot)
    ({ slot, subcommitteeIndex } : SyncAggregatorSelectionData) key

/-- From Altair: a contribution with the index of its aggregator and its selection proof. -/
def getContributionAndProof (config : Config) (state : BeaconState preset fork)
    (aggregatorIndex : ValidatorIndex) (contribution : SyncCommitteeContribution preset)
    (key : Signatures.SecretKey) : Except ValidatorDutyError (ContributionAndProof preset) := do
  let selectionProof ← getSyncCommitteeSelectionProof config state contribution.slot
    contribution.subcommitteeIndex key
  return { aggregatorIndex, contribution, selectionProof }

/-- From Altair: the signature of a contribution and proof, in the epoch of its slot. -/
def getContributionAndProofSignature (config : Config) (state : BeaconState preset fork)
    (contributionAndProof : ContributionAndProof preset) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  signAtEpoch config state DOMAIN_CONTRIBUTION_AND_PROOF
    (computeEpochAtSlot preset contributionAndProof.contribution.slot) contributionAndProof key

end EthLib.Consensus
