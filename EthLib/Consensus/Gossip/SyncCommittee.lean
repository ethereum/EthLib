module

public import EthLib.Consensus.Gossip.Seen
public import EthLib.Consensus.Gossip.Topics
public import EthLib.Consensus.Transition.SyncAggregate
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.Gossip.SyncCommittee`

From Altair: gossip validation of the messages of the sync committee.

A member signs a block root in a slot, and sends its message on the subnet of its subcommittee.

An aggregator of a subcommittee combines those signatures into a contribution.

Contributions go to every node, so that the next proposer can include them.

Each topic runs its checks in a fixed order, and the first check that fails gives the outcome.

The members come from the sync committee of the slot after the head state.

A valid message records its keys among the messages seen.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Networking.Gossip Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Subcommittees -/

/-- From Altair: the sync committee that signs in the slot after a state.

Members sign in a slot for the block of the slot before.

So when that slot starts a new period, the next committee of the state signs. -/
def syncCommitteeAtNextSlot (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    Except ArithError (SyncCommittee preset) := do
  let nextSlot ← addChecked state.slot 1
  return if computeSyncCommitteePeriod preset (getCurrentEpoch state) ==
      computeSyncCommitteePeriodAtSlot preset nextSlot
    then state.currentSyncCommittee altair else state.nextSyncCommittee altair

/-- From Altair: the keys of the members of a subcommittee, in committee order.

The committee splits into equal slices, one for each subcommittee, in order.

A slice past the end of the committee is empty. -/
def getSyncSubcommitteePubkeys (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (subcommitteeIndex : UInt64) : Except ArithError (List BLSPubkey) := do
  let committee ← syncCommitteeAtNextSlot state altair
  let size := syncSubcommitteeSize preset
  let start ← mulChecked subcommitteeIndex size.toUInt64
  return (committee.pubkeys.toList.drop start.toNat).take size

/-- From Altair: the subnets of the subcommittees that hold a key, each once.

A key can hold several seats in a committee, and so belong to several subcommittees. -/
def syncSubnetsOfPubkey (committee : SyncCommittee preset) (pubkey : BLSPubkey) : List UInt64 :=
  (committee.pubkeys.toList.zipIdx.filterMap fun (key, position) =>
    if key = pubkey then some (position / syncSubcommitteeSize preset).toUInt64 else none).eraseDups

/-- From Altair: whether a selection proof makes its signer an aggregator of a subcommittee.

The first 8 bytes of the SHA-256 hash of the proof, read little-endian, give a number.

The proof selects its signer when that number is a multiple of a modulus.

The modulus aims at a fixed number of aggregators in each subcommittee, and is at least 1. -/
def isSyncCommitteeAggregator (preset : Preset) (signature : BLSSignature) : Bool :=
  let modulo := max 1
    (preset.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT /
      TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE)
  let hash := sha256Bytes32 (packBytes signature)
  bytesToUint64 (Vector.ofFn fun i : Fin 8 => hash[i.val]) % modulo == 0

/-- From Altair: the bits of the valid contributions seen for a slot, a root and a subcommittee. -/
def Seen.contributionBits (seen : Seen) (key : Slot × Root × UInt64) : List (List Bool) :=
  seen.syncContributionBits.filterMap fun (seenKey, bits) =>
    if seenKey = key then some bits else none

/-! ## Signatures -/

/-- From Altair: whether the members whose bit is set signed the block root of a contribution.

The keys are those of the subcommittee, in order, and the bits pick the members that signed. -/
def isValidContributionSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (pubkeys : List BLSPubkey)
    (contribution : SyncCommitteeContribution preset) : Except ForkChoiceError Bool := do
  let participants := (pubkeys.zip contribution.aggregationBits.bits.toList).filterMap
    fun (key, bit) => if bit then some (packBytes key) else none
  let domain ← (getDomain config state DOMAIN_SYNC_COMMITTEE
    (some (computeEpochAtSlot preset contribution.slot))).mapError .accessor
  let signingRoot ← (computeSigningRoot contribution.beaconBlockRoot domain).mapError .ssz
  return syncAggregateVerify checks participants.toArray (packBytes signingRoot)
    (packBytes contribution.signature)

/-! ## Sync committee messages -/

/-- From Altair: the checks of a sync committee message on a subnet, at a time in milliseconds.

The first valid message of a validator for a slot and a subnet passes, and a later one is ignored.

A message for a slot other than the current one is ignored.

The validator must hold a seat of the subcommittee of the subnet, and must have signed the root. -/
def validateSyncCommitteeMessage (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (altair : .altair ≤ fork) (message : SyncCommitteeMessage)
    (currentTimeMs subnetId : UInt64) : Except ForkChoiceError ValidationResult :=
  (ignoreUnless (!seen.syncMessageKeys.contains (message.slot, message.validatorIndex, subnetId))
    "already seen message from this validator for this slot and subnet").andThenM fun _ => do
  let current ← store.isCurrentSlot config message.slot currentTimeMs
  (ignoreUnless current "message is not for the current slot").andThenM fun _ => do
  let state ← store.headState config
  match state.validators.data[message.validatorIndex.toNat]? with
  | none => return .reject "validator index out of range"
  | some validator => do
  let committee ← (syncCommitteeAtNextSlot state altair).mapError .arith
  (rejectUnless ((syncSubnetsOfPubkey committee validator.pubkey).contains subnetId)
    "subnet_id is not valid for the validator").andThenM fun _ => do
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE message.slot
    message.beaconBlockRoot validator.pubkey message.signature
  return rejectUnless valid "invalid sync committee message signature"

/-- From Altair: the keys after a valid sync committee message on a subnet. -/
def Seen.recordSyncCommitteeMessage (seen : Seen) (message : SyncCommitteeMessage)
    (subnetId : UInt64) : Seen :=
  { seen with
    syncMessageKeys := (message.slot, message.validatorIndex, subnetId) :: seen.syncMessageKeys }

/-! ## Contributions -/

/-- From Altair: the checks of a signed contribution on its topic, at a time in milliseconds.

A contribution is ignored when a valid one for the same slot, root and subcommittee covers its bits.

It is ignored when its aggregator has a valid one for the slot and the subcommittee already.

A contribution for a slot other than the current one is ignored.

It must name a subcommittee, have one participant at least, and select its aggregator.

The aggregator must hold a seat of the subcommittee.

It must have signed the selection proof and the contribution, and the participants the root. -/
def validateContributionAndProof (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (altair : .altair ≤ fork)
    (signed : SignedContributionAndProof preset) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let proof := signed.message
  let contribution := proof.contribution
  let bits := contribution.aggregationBits.bits.toList
  let dataKey := (contribution.slot, contribution.beaconBlockRoot, contribution.subcommitteeIndex)
  let aggregatorKey := (contribution.slot, proof.aggregatorIndex, contribution.subcommitteeIndex)
  (ignoreUnless (!isNonStrictSuperset (seen.contributionBits dataKey) bits)
    "already seen contribution for this data").andThenM fun _ =>
  (ignoreUnless (!seen.syncContributionAggregatorKeys.contains aggregatorKey)
    "already seen contribution from this aggregator").andThenM fun _ => do
  let current ← store.isCurrentSlot config contribution.slot currentTimeMs
  (ignoreUnless current "contribution is not for the current slot").andThenM fun _ =>
  (rejectUnless (contribution.subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT)
    "subcommittee index out of range").andThenM fun _ =>
  (rejectUnless (bits.any id) "contribution has no participants").andThenM fun _ =>
  (rejectUnless (isSyncCommitteeAggregator preset proof.selectionProof)
    "validator is not selected as aggregator").andThenM fun _ => do
  let state ← store.headState config
  match state.validators.data[proof.aggregatorIndex.toNat]? with
  | none => return .reject "aggregator index out of range"
  | some aggregator => do
  let pubkeys ← (getSyncSubcommitteePubkeys state altair contribution.subcommitteeIndex).mapError
    .arith
  (rejectUnless (pubkeys.contains aggregator.pubkey)
    "aggregator is not a member of the committee").andThenM fun _ => do
  let selected ← isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
    contribution.slot (SyncAggregatorSelectionData.mk contribution.slot
      contribution.subcommitteeIndex) aggregator.pubkey proof.selectionProof
  (rejectUnless selected "invalid selection proof signature").andThenM fun _ => do
  let signedByAggregator ← isValidSignatureAtSlot config checks state
    DOMAIN_CONTRIBUTION_AND_PROOF contribution.slot proof aggregator.pubkey signed.signature
  (rejectUnless signedByAggregator "invalid aggregator signature").andThenM fun _ => do
  let aggregate ← isValidContributionSignature config checks state pubkeys contribution
  return rejectUnless aggregate "invalid aggregate signature"

/-- From Altair: the keys after a valid contribution: its aggregator, and its bits for its data. -/
def Seen.recordContributionAndProof (seen : Seen) (signed : SignedContributionAndProof preset) :
    Seen :=
  let proof := signed.message
  let contribution := proof.contribution
  { seen with
    syncContributionAggregatorKeys :=
      (contribution.slot, proof.aggregatorIndex, contribution.subcommitteeIndex) ::
        seen.syncContributionAggregatorKeys
    syncContributionBits :=
      ((contribution.slot, contribution.beaconBlockRoot, contribution.subcommitteeIndex),
        contribution.aggregationBits.bits.toList) :: seen.syncContributionBits }

end EthLib.Consensus
