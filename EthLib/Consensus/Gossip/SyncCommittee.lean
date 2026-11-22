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
  -- The slot after the state, which must be below `2^64`.
  let nextSlot ← addChecked state.slot 1
  -- The current committee when that slot is in the sync committee period of the current epoch.
  --
  -- Else the next committee.
  return if computeSyncCommitteePeriod preset (getCurrentEpoch state) ==
      computeSyncCommitteePeriodAtSlot preset nextSlot
    then (state.currentSyncCommittee altair).value else (state.nextSyncCommittee altair).value

/-- From Altair: the keys of the members of a subcommittee of a sync committee, in committee order.
-/
def syncSubcommitteePubkeys (committee : SyncCommittee preset) (subcommitteeIndex : Nat) :
    List BLSPubkey :=
  -- Let `k` be `floor(SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT)`, the size of a slice.
  let size := syncSubcommitteeSize preset
  -- Subcommittee `i` holds the keys at the positions `i * k` to `i * k + k - 1`.
  --
  -- Positions past the end of the committee hold no key, so a slice there is short or empty.
  (committee.pubkeys.toList.drop (subcommitteeIndex * size)).take size

/-- From Altair: the keys of the members of a subcommittee, in committee order.

It fails when the position of the first member does not fit in 64 bits. -/
def getSyncSubcommitteePubkeys (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (subcommitteeIndex : UInt64) : Except ArithError (List BLSPubkey) := do
  -- The sync committee that signs in the slot after the state.
  let committee ← syncCommitteeAtNextSlot state altair
  -- For the index `i` and the size `k` of a subcommittee, `i * k` must be below `2^64`.
  let _ ← mulChecked subcommitteeIndex (syncSubcommitteeSize preset).toUInt64
  -- The slice of the subcommittee in that committee.
  return syncSubcommitteePubkeys committee subcommitteeIndex.toNat

/-- From Altair: the subnets of the subcommittees that hold a key, each once.

A key can hold several seats in a committee, and so belong to several subcommittees. -/
def syncSubnetsOfPubkey (committee : SyncCommittee preset) (pubkey : BLSPubkey) : List UInt64 :=
  -- Let `k` be the size of a subcommittee.
  --
  -- Each position `p` of the key in the committee gives the subnet `floor(p / k)`.
  (committee.pubkeys.toList.zipIdx.filterMap fun (key, position) =>
    if key = pubkey then some (position / syncSubcommitteeSize preset).toUInt64 else none).eraseDups

/-- From Altair: whether a selection proof makes its signer an aggregator of a subcommittee.

The modulus aims at a fixed number of aggregators in each subcommittee. -/
def isSyncCommitteeAggregator (preset : Preset) (signature : BLSSignature) : Bool :=
  -- Let `k` be `floor(SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT)`.
  --
  -- The modulus is `max(1, floor(k / TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE))`.
  let modulo := max 1
    (preset.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT /
      TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE)
  -- Let `h` be the SHA-256 hash of the proof.
  let hash := Cryptography.Hash.Sha256.hash32 (packBytes signature)
  -- The integer of the first 8 bytes of `h`, read little-endian, is a multiple of the modulus.
  bytesToUint64 (Vector.ofFn fun i : Fin 8 => hash[i.val]) % modulo == 0

/-- From Altair: the bits of the valid contributions seen for a slot, a root and a subcommittee. -/
def Seen.contributionBits (seen : Seen) (key : Slot × Root × UInt64) : List (List Bool) :=
  -- The bits of each recorded contribution whose key is the key, in the order of the record.
  seen.syncContributionBits.filterMap fun (seenKey, bits) =>
    if seenKey = key then some bits else none

/-! ## Signatures -/

/-- From Altair: whether the members whose bit is set signed the block root of a contribution.

The keys are those of the subcommittee, in order. -/
def isValidContributionSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (pubkeys : List BLSPubkey)
    (contribution : SyncCommitteeContribution preset) : Except ForkChoiceError Bool := do
  -- The participants: the keys whose bit is set, in order.
  let participants := (pubkeys.zip contribution.aggregationBits.bits.toList).filterMap
    fun (key, bit) => if bit then some key else none
  -- The domain of `DOMAIN_SYNC_COMMITTEE` at the epoch of the slot.
  let domain ← (getDomain config state DOMAIN_SYNC_COMMITTEE
    (some (computeEpochAtSlot preset contribution.slot))).mapError .accessor
  let signingRoot ← (computeSigningRoot contribution.beaconBlockRoot domain).mapError .ssz
  -- The participants signed the block root, as one aggregate signature.
  return syncAggregateVerify checks participants.toArray (packBytes signingRoot)
    contribution.signature

/-! ## Sync committee messages -/

/-- From Altair: the checks of a sync committee message on a subnet, at a time in milliseconds. -/
def validateSyncCommitteeMessage (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (altair : .altair ≤ fork) (message : SyncCommitteeMessage)
    (currentTimeMs subnetId : UInt64) : Except ForkChoiceError ValidationResult :=
  -- IGNORE when a valid message of the validator for the slot and the subnet was already seen.
  --
  -- The key holds the subnet, so a validator with seats on several subnets passes on each.
  (ignoreUnless (!seen.syncMessageKeys.contains (message.slot, message.validatorIndex, subnetId))
    "already seen message from this validator for this slot and subnet").andThenM fun _ => do
  -- IGNORE unless the clock is in the slot of the message.
  let current ← store.isCurrentSlot config message.slot currentTimeMs
  (ignoreUnless current "message is not for the current slot").andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the validator index names a validator of that state.
  match state.validators.data[message.validatorIndex.toNat]? with
  | none => return .reject "validator index out of range"
  | some validator => do
  -- The sync committee that signs in the slot after that state.
  let committee ← (syncCommitteeAtNextSlot state altair).mapError .arith
  -- REJECT unless a seat of the key of the validator in that committee is on the subnet.
  (rejectUnless ((syncSubnetsOfPubkey committee validator.pubkey).contains subnetId)
    "subnet_id is not valid for the validator").andThenM fun _ => do
  -- REJECT unless the validator signed the block root, under `DOMAIN_SYNC_COMMITTEE`.
  --
  -- The domain is taken at the epoch of the slot.
  let valid ← isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE message.slot
    message.beaconBlockRoot validator.pubkey message.signature
  return rejectUnless valid "invalid sync committee message signature"

/-- From Altair: the keys after a valid sync committee message on a subnet. -/
def Seen.recordSyncCommitteeMessage (seen : Seen) (message : SyncCommitteeMessage)
    (subnetId : UInt64) : Seen :=
  -- The slot, the validator and the subnet join the keys of messages.
  { seen with
    syncMessageKeys := (message.slot, message.validatorIndex, subnetId) :: seen.syncMessageKeys }

/-! ## Contributions -/

/-- From Altair: the checks of a signed contribution on its topic, at a time in milliseconds. -/
def validateContributionAndProof (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (altair : .altair ≤ fork)
    (signed : SignedContributionAndProof preset) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let proof := signed.message
  let contribution := proof.contribution
  let bits := contribution.aggregationBits.bits.toList
  let dataKey := (contribution.slot, contribution.beaconBlockRoot, contribution.subcommitteeIndex)
  let aggregatorKey := (contribution.slot, proof.aggregatorIndex, contribution.subcommitteeIndex)
  -- IGNORE when a valid contribution of the same slot, root and subcommittee covers its bits.
  --
  -- Covering means setting every bit that it sets.
  (ignoreUnless (!isNonStrictSuperset (seen.contributionBits dataKey) bits)
    "already seen contribution for this data").andThenM fun _ =>
  -- IGNORE when a valid contribution of the aggregator for the slot and subcommittee was seen.
  (ignoreUnless (!seen.syncContributionAggregatorKeys.contains aggregatorKey)
    "already seen contribution from this aggregator").andThenM fun _ => do
  -- IGNORE unless the clock is in the slot of the contribution.
  let current ← store.isCurrentSlot config contribution.slot currentTimeMs
  (ignoreUnless current "contribution is not for the current slot").andThenM fun _ =>
  -- REJECT unless the subcommittee index is below `SYNC_COMMITTEE_SUBNET_COUNT`.
  (rejectUnless (contribution.subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT)
    "subcommittee index out of range").andThenM fun _ =>
  -- REJECT unless one bit at least is set.
  (rejectUnless (bits.any id) "contribution has no participants").andThenM fun _ =>
  -- REJECT unless the selection proof selects the aggregator.
  (rejectUnless (isSyncCommitteeAggregator preset proof.selectionProof)
    "validator is not selected as aggregator").andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the aggregator index names a validator of that state.
  match state.validators.data[proof.aggregatorIndex.toNat]? with
  | none => return .reject "aggregator index out of range"
  | some aggregator => do
  -- REJECT unless the key of the aggregator is a key of the subcommittee.
  let pubkeys ← (getSyncSubcommitteePubkeys state altair contribution.subcommitteeIndex).mapError
    .arith
  (rejectUnless (pubkeys.contains aggregator.pubkey)
    "aggregator is not a member of the committee").andThenM fun _ => do
  -- REJECT unless the selection proof is the aggregator's signature on the slot and subcommittee.
  --
  -- The domain is that of `DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF` at the epoch of the slot.
  let selected ← isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
    contribution.slot (SyncAggregatorSelectionData.mk contribution.slot
      contribution.subcommitteeIndex) aggregator.pubkey proof.selectionProof
  (rejectUnless selected "invalid selection proof signature").andThenM fun _ => do
  -- REJECT unless the aggregator signed the message, under `DOMAIN_CONTRIBUTION_AND_PROOF`.
  let signedByAggregator ← isValidSignatureAtSlot config checks state
    DOMAIN_CONTRIBUTION_AND_PROOF contribution.slot proof aggregator.pubkey signed.signature
  (rejectUnless signedByAggregator "invalid aggregator signature").andThenM fun _ => do
  -- REJECT unless the members whose bit is set signed the block root.
  let aggregate ← isValidContributionSignature config checks state pubkeys contribution
  return rejectUnless aggregate "invalid aggregate signature"

/-- From Altair: the keys after a valid contribution: its aggregator, and its bits for its data. -/
def Seen.recordContributionAndProof (seen : Seen) (signed : SignedContributionAndProof preset) :
    Seen :=
  let proof := signed.message
  let contribution := proof.contribution
  { seen with
    -- The slot, the aggregator and the subcommittee join the keys of aggregators.
    syncContributionAggregatorKeys :=
      (contribution.slot, proof.aggregatorIndex, contribution.subcommitteeIndex) ::
        seen.syncContributionAggregatorKeys
    -- The bits join the keys, under the slot, the block root and the subcommittee.
    syncContributionBits :=
      ((contribution.slot, contribution.beaconBlockRoot, contribution.subcommitteeIndex),
        contribution.aggregationBits.bits.toList) :: seen.syncContributionBits }

end EthLib.Consensus
