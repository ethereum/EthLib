module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.HonestAggregation
public import EthLib.Consensus.Transition.StateTransition

/-!
# `Consensus.BeaconApi.ValidatorData`

The answers of the Beacon API that hand a validator the data it signs or aggregates.

The [attestation data] and the [payload attestation data] are built at the head of the store.

The [aggregate] and the [contribution] join messages that the node has collected.

Which messages a node collects is its own matter, so the caller gives them.

The attestation data, the aggregate and the contribution refuse an unverified payload: code 503.

SOUNDNESS.md records the points that the source leaves open.

[attestation data]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/attestation_data.yaml
[payload attestation data]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/payload_attestation_data.yaml
[aggregate]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/aggregate_attestation.v2.yaml
[contribution]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/sync_committee_contribution.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-! ## Errors -/

/-- The error of a block whose payload is not yet verified, with code 503. -/
def optimisticBlock (root : Root) : ErrorMessage :=
  -- The source names code 503 for an optimistic block; the message is EthLib's.
  { code := 503, message := s!"Block {toHex root.toArray} is optimistic" }

/-- The error of a request that no collected message answers, with code 404. -/
def noMatch (what : String) : ErrorMessage :=
  -- The message is EthLib's.
  { code := 404, message := s!"No {what} matches the request" }

/-- The error of a slot before the head, with code 400. -/
def slotBeforeHead (slot : Slot) : ErrorMessage :=
  -- The source names code 400 for an invalid request; the message is EthLib's.
  { code := 400, message := s!"Slot {slot.toNat} is before the head" }

/-- The error body of a failed construction: code 400 for an index out of range, else code 500. -/
def constructionError : ValidatorDutyError → ErrorMessage
  -- An index of the request out of range is an invalid request.
  | .indexOutOfRange index limit =>
    { code := 400, message := s!"Index {index.toNat} is not below {limit.toNat}" }
  -- Any other failure is internal.
  | fault => internalError (toString fault.code.toNat)

/-- Nothing when a block is verified, or the error with code 503. -/
def checkVerified (optimistic : OptimisticStore preset fork) (root : Root) :
    Except ErrorMessage Unit :=
  -- The source: code 503 for a block not yet fully verified by an execution engine.
  if isExecutionOptimistic optimistic root then .error (optimisticBlock root) else .ok ()

/-! ## Attestation data -/

/-- The state after a block, taken through the empty slots up to a slot. -/
def stateAtSlot (config : Config) (state : BeaconState preset fork) (slot : Slot) :
    Except ErrorMessage (BeaconState preset fork) :=
  -- A slot before the state: code 400.
  if slot < state.slot then .error (slotBeforeHead slot)
  else if slot = state.slot then .ok state
  -- The empty slots up to the slot, with their epoch transitions; a failure gives code 500.
  else (processSlots config .bls state slot).mapError fun _ => internalError "no state at the slot"

/-- The attestation data for a slot, at the head of the store. -/
def produceAttestationData (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) (slot : Slot) (committeeIndex : CommitteeIndex) :
    Except ErrorMessage AttestationData := do
  -- The head of the store, its block and the state after it; a missing one gives code 500.
  let head ← (store.getHead config).mapError fun _ => internalError "no head"
  let some block := store.blocks[head.root]? | .error (internalError "unknown head block")
  let some headState := store.blockStates[head.root]? | .error (internalError "unknown head state")
  -- The source: code 503 when the block of the data is optimistic, here the head block.
  checkVerified optimistic head.root
  -- EthLib's choice: a slot after the current slot of the store gives code 400.
  let current ← (store.getCurrentSlot config).mapError fun _ => internalError "no current slot"
  if current < slot then
    throw { code := 400, message := s!"Slot {slot.toNat} is after the current slot" }
  -- The state of the head block, taken through the empty slots up to the slot.
  --
  -- A slot before the head gives code 400.
  let state ← stateAtSlot config headState slot
  -- The data, with the index by the rule of the fork of the store, which holds one fork.
  --
  -- Before Electra: the requested committee index.
  --
  -- The source: in Electra and Fulu, index 0.
  --
  -- The source: from Gloas, the index signals payload availability.
  --
  -- That is 0 at the slot of the head block, else whether the head payload is full.
  (getAttestationData state head.root block.slot committeeIndex head.payloadStatus).mapError
    constructionError

/-- From Gloas: the payload attestation data for the block of a slot, or none.

The two flags record what the node has seen, so the caller gives them. -/
def producePayloadAttestationData (config : Config) (store : Store preset fork) (slot : Slot)
    (payloadPresent blobDataAvailable : Bool) :
    Except ErrorMessage (Option PayloadAttestationData) := do
  -- Before Gloas: code 400.
  unless .glamsterdam ≤ fork do throw (beforeFork "payload attestation data" .glamsterdam)
  let some head := headRoot config store | .error (internalError "no head")
  -- The block of that slot on the chain of the head.
  --
  -- The source: none, the answer with code 204, when no block has been seen for the slot.
  --
  -- EthLib reads that as no block at that slot on the chain of the head.
  return (blockAtSlot store head slot).map fun root =>
    { beaconBlockRoot := root, slot, payloadPresent, blobDataAvailable }

/-! ## Aggregates -/

/-- Whether some attestation data has a given root. -/
def hasRoot (data : AttestationData) (root : Root) : Bool :=
  -- The hash tree root of the data is the root.
  match SszType.hashTreeRoot data with
  | .ok own => own == root
  -- Data without a hash tree root has no root.
  | .error _ => false

/-- Whether an attestation before Electra matches a request: its data root, slot and committee. -/
def matchesRequest (attestation : Attestation preset fork) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Bool :=
  -- The source: the same data root, slot and committee index; the index is in the data.
  hasRoot attestation.data dataRoot && attestation.data.slot == slot &&
    attestation.data.index == committeeIndex

/-- Whether a single attestation matches a request: its data root, slot and committee. -/
def singleMatchesRequest (single : SingleAttestation) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Bool :=
  -- The source: the same data root, slot and committee index; the index is that of the message.
  hasRoot single.data dataRoot && single.data.slot == slot &&
    single.committeeIndex == committeeIndex

/-- The aggregate of the collected attestations that match a data root, a slot and a committee. -/
def aggregateAttestation (state : BeaconState preset fork)
    (optimistic : OptimisticStore preset fork) (attestations : List (Attestation preset fork))
    (singles : List SingleAttestation) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Except ErrorMessage (Attestation preset fork) :=
  -- Before Electra: the attestations.
  if before : fork < .pectra then do
    -- The first match; the source: no attestation for the data root gives code 404.
    let some first := attestations.find? (matchesRequest · dataRoot slot committeeIndex)
      | .error (noMatch "attestation")
    -- The source: code 503 when the block of the data is optimistic.
    checkVerified optimistic first.data.beaconBlockRoot
    -- The source: the aggregate of all the attestations with the data of that match.
    (constructAggregate state before first.data attestations).mapError constructionError
  -- From Electra: the single attestations.
  else do
    -- As above: the first match, else code 404; then code 503 when its block is optimistic.
    let some first := singles.find? (singleMatchesRequest · dataRoot slot committeeIndex)
      | .error (noMatch "attestation")
    checkVerified optimistic first.data.beaconBlockRoot
    -- The aggregate of the single attestations with that data and of the requested committee.
    (constructAggregateOfSingleAttestations state first.data committeeIndex singles).mapError
      constructionError

/-! ## Sync committee contributions -/

/-- Whether the validator of a message has one of some keys. -/
def inSubcommittee (state : BeaconState preset fork) (keys : List BLSPubkey)
    (message : SyncCommitteeMessage) : Bool :=
  match getValidator state message.validatorIndex with
  | .ok validator => keys.contains validator.pubkey
  -- A message whose validator is not known is left out.
  | .error _ => false

/-- From Altair: the contribution of a subcommittee for a block root, at the slot of a state. -/
def produceSyncCommitteeContribution (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (optimistic : OptimisticStore preset fork) (messages : List SyncCommitteeMessage)
    (slot : Slot) (subcommitteeIndex : UInt64) (root : Root) :
    Except ErrorMessage (SyncCommitteeContribution preset) := do
  -- EthLib's choice: the slot must be that of the state, else code 400.
  unless slot = state.slot do
    throw { code := 400, message := s!"Slot {slot.toNat} is not the slot of the state" }
  -- A subcommittee index that names no subnet gives code 400.
  unless subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT do
    throw (constructionError (.indexOutOfRange subcommitteeIndex SYNC_COMMITTEE_SUBNET_COUNT))
  -- The source: code 503 when the block of the root is optimistic.
  checkVerified optimistic root
  -- The messages of a slot come from the sync committee of the next slot.
  let committee ← (syncCommitteeAtNextSlot state altair).mapError fun _ =>
    internalError "no sync committee"
  -- Only the messages of validators with a key of the subcommittee count.
  --
  -- So the messages of the other subcommittees are left out.
  let keys := syncSubcommitteePubkeys committee subcommitteeIndex.toNat
  let members := messages.filter (inSubcommittee state keys)
  -- The contribution of the messages of the slot on the root.
  match constructSyncCommitteeContribution state committee root subcommitteeIndex members with
  | .ok contribution => return contribution
  -- The source: no contribution for the block root gives code 404.
  | .error (.noMessages ..) => throw (noMatch "sync committee message")
  | .error fault => throw (constructionError fault)

/-! ## Responses -/

/-- The response of the attestation data endpoint, with no metadata. -/
def attestationDataResponse (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) (slot : Slot) (committeeIndex : CommitteeIndex) :
    Except ErrorMessage ApiEnvelope := do
  -- The source: the attestation data as data, with no version.
  return { data := ← apiJsonOr500 (← produceAttestationData config store optimistic slot
    committeeIndex) }

/-- The response of the payload attestation data endpoint, or none for the answer with code 204. -/
def payloadAttestationDataResponse (config : Config) (store : Store preset fork) (slot : Slot)
    (payloadPresent blobDataAvailable : Bool) : Except ErrorMessage (Option ApiEnvelope) := do
  match ← producePayloadAttestationData config store slot payloadPresent blobDataAvailable with
  -- No block for the slot: code 204, with no body.
  | none => return none
  -- The source: the consensus version of the store, and the data.
  | some data => return some (← versioned fork (.ok data))

/-- The response of the aggregate endpoint, which names the consensus version of the state. -/
def aggregateAttestationResponse (state : BeaconState preset fork)
    (optimistic : OptimisticStore preset fork) (attestations : List (Attestation preset fork))
    (singles : List SingleAttestation) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Except ErrorMessage ApiEnvelope :=
  -- The source: the version of the fork, and the aggregate as data.
  versioned fork
    (aggregateAttestation state optimistic attestations singles dataRoot slot committeeIndex)

/-- The response of the contribution endpoint, with no metadata. -/
def syncCommitteeContributionResponse (state : BeaconState preset fork)
    (optimistic : OptimisticStore preset fork) (messages : List SyncCommitteeMessage)
    (slot : Slot) (subcommitteeIndex : UInt64) (root : Root) : Except ErrorMessage ApiEnvelope :=
  if altair : .altair ≤ fork then do
    -- The source: the contribution as data, with no version.
    return { data := ← apiJsonOr500 (← produceSyncCommitteeContribution state altair optimistic
      messages slot subcommitteeIndex root) }
  -- Before Altair there is no sync committee: code 400.
  else .error (beforeFork "sync committee contribution" .altair)

end EthLib.Consensus.BeaconApi
