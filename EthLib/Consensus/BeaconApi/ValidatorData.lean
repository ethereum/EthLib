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

[attestation data]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/attestation_data.yaml
[payload attestation data]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/payload_attestation_data.yaml
[aggregate]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/aggregate_attestation.v2.yaml
[contribution]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/sync_committee_contribution.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-! ## Errors -/

/-- The error of a block whose payload is not yet verified, with code 503. -/
def optimisticBlock (root : Root) : ErrorMessage :=
  { code := 503, message := s!"Block {toHex root.toArray} is optimistic" }

/-- The error of a request that no collected message answers, with code 404. -/
def noMatch (what : String) : ErrorMessage :=
  { code := 404, message := s!"No {what} matches the request" }

/-- The error of a slot before the head, with code 400. -/
def slotBeforeHead (slot : Slot) : ErrorMessage :=
  { code := 400, message := s!"Slot {slot.toNat} is before the head" }

/-- The error body of a failed construction: code 400 for an index out of range, else code 500. -/
def constructionError : ValidatorDutyError → ErrorMessage
  | .indexOutOfRange index limit =>
    { code := 400, message := s!"Index {index.toNat} is not below {limit.toNat}" }
  | fault => internalError (toString fault.code.toNat)

/-- Nothing when a block is verified, or the error with code 503. -/
def checkVerified (optimistic : OptimisticStore preset fork) (root : Root) :
    Except ErrorMessage Unit :=
  if isExecutionOptimistic optimistic root then .error (optimisticBlock root) else .ok ()

/-! ## Attestation data -/

/-- The state after a block, taken through the empty slots up to a slot.

The slot must not be before the state, or the answer is the error with code 400. -/
def stateAtSlot (config : Config) (state : BeaconState preset fork) (slot : Slot) :
    Except ErrorMessage (BeaconState preset fork) :=
  if slot < state.slot then .error (slotBeforeHead slot)
  else if slot = state.slot then .ok state
  else (processSlots config .bls state slot).mapError fun _ => internalError "no state at the slot"

/-- The attestation data for a slot, at the head of the store.

The state of the head block is taken through the empty slots up to the slot.

The store holds one fork, and the index follows the rule of that fork.

Before Electra the index is the requested committee index, and in Electra and Fulu it is 0.

From Gloas it is 0 at the slot of the head block, else it records whether the head payload is full.

A head payload whose status is still pending gives the error with code 500.

A head block whose payload is not yet verified gives the error with code 503.

A slot before the head, or after the current slot of the store, gives the error with code 400. -/
def produceAttestationData (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) (slot : Slot) (committeeIndex : CommitteeIndex) :
    Except ErrorMessage AttestationData := do
  let head ← (store.getHead config).mapError fun _ => internalError "no head"
  let some block := store.blocks[head.root]? | .error (internalError "unknown head block")
  let some headState := store.blockStates[head.root]? | .error (internalError "unknown head state")
  checkVerified optimistic head.root
  let current ← (store.getCurrentSlot config).mapError fun _ => internalError "no current slot"
  if current < slot then
    throw { code := 400, message := s!"Slot {slot.toNat} is after the current slot" }
  let state ← stateAtSlot config headState slot
  (getAttestationData state head.root block.slot committeeIndex head.payloadStatus).mapError
    constructionError

/-- From Gloas: the payload attestation data for the block of a slot, or none.

Before Gloas the answer is the error with code 400.

The block is the one of that slot on the chain of the head.

None, the answer with code 204, means that the chain of the head has no block at that slot.

The two flags record what the node has seen, so the caller gives them. -/
def producePayloadAttestationData (config : Config) (store : Store preset fork) (slot : Slot)
    (payloadPresent blobDataAvailable : Bool) :
    Except ErrorMessage (Option PayloadAttestationData) := do
  unless .glamsterdam ≤ fork do throw (beforeFork "payload attestation data" .glamsterdam)
  let some head := headRoot config store | .error (internalError "no head")
  return (blockAtSlot store head slot).map fun root =>
    { beaconBlockRoot := root, slot, payloadPresent, blobDataAvailable }

/-! ## Aggregates -/

/-- Whether some attestation data has a given root. -/
def hasRoot (data : AttestationData) (root : Root) : Bool :=
  match SszType.hashTreeRoot data with
  | .ok own => own == root
  | .error _ => false

/-- Whether an attestation before Electra matches a request: its data root, slot and committee. -/
def matchesRequest (attestation : Attestation preset fork) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Bool :=
  hasRoot attestation.data dataRoot && attestation.data.slot == slot &&
    attestation.data.index == committeeIndex

/-- Whether a single attestation matches a request: its data root, slot and committee. -/
def singleMatchesRequest (single : SingleAttestation) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Bool :=
  hasRoot single.data dataRoot && single.data.slot == slot &&
    single.committeeIndex == committeeIndex

/-- The aggregate of the collected attestations that match a data root, a slot and a committee.

Before Electra it joins the attestations, and from Electra the single attestations.

The data is that of the first match, and the aggregate joins every message with that data.

From Electra it joins only those of the requested committee.

No match gives the error with code 404.

A block of the data whose payload is not yet verified gives the error with code 503. -/
def aggregateAttestation (state : BeaconState preset fork)
    (optimistic : OptimisticStore preset fork) (attestations : List (Attestation preset fork))
    (singles : List SingleAttestation) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Except ErrorMessage (Attestation preset fork) :=
  if before : fork < .pectra then do
    let some first := attestations.find? (matchesRequest · dataRoot slot committeeIndex)
      | .error (noMatch "attestation")
    checkVerified optimistic first.data.beaconBlockRoot
    (constructAggregate state before first.data attestations).mapError constructionError
  else do
    let some first := singles.find? (singleMatchesRequest · dataRoot slot committeeIndex)
      | .error (noMatch "attestation")
    checkVerified optimistic first.data.beaconBlockRoot
    (constructAggregateOfSingleAttestations state first.data committeeIndex singles).mapError
      constructionError

/-! ## Sync committee contributions -/

/-- Whether the validator of a message has one of some keys. -/
def inSubcommittee (state : BeaconState preset fork) (keys : List BLSPubkey)
    (message : SyncCommitteeMessage) : Bool :=
  match getValidator state message.validatorIndex with
  | .ok validator => keys.contains validator.pubkey
  | .error _ => false

/-- From Altair: the contribution of a subcommittee for a block root, at the slot of a state.

The messages are those of the slot on that root, from the sync committee of the next slot.

Only the messages of validators with a key of the subcommittee count.

So the messages of the other subcommittees are left out.

A message whose validator is not known is left out too.

The slot must be that of the state, or the answer is the error with code 400.

No matching message gives the error with code 404.

A subcommittee index that names no subnet gives the error with code 400.

A block whose payload is not yet verified gives the error with code 503. -/
def produceSyncCommitteeContribution (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (optimistic : OptimisticStore preset fork) (messages : List SyncCommitteeMessage)
    (slot : Slot) (subcommitteeIndex : UInt64) (root : Root) :
    Except ErrorMessage (SyncCommitteeContribution preset) := do
  unless slot = state.slot do
    throw { code := 400, message := s!"Slot {slot.toNat} is not the slot of the state" }
  unless subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT do
    throw (constructionError (.indexOutOfRange subcommitteeIndex SYNC_COMMITTEE_SUBNET_COUNT))
  checkVerified optimistic root
  let committee ← (syncCommitteeAtNextSlot state altair).mapError fun _ =>
    internalError "no sync committee"
  let keys := syncSubcommitteePubkeys committee subcommitteeIndex.toNat
  let members := messages.filter (inSubcommittee state keys)
  match constructSyncCommitteeContribution state committee root subcommitteeIndex members with
  | .ok contribution => return contribution
  | .error .noMessages => throw (noMatch "sync committee message")
  | .error fault => throw (constructionError fault)

/-! ## Responses -/

/-- The response of the attestation data endpoint, with no metadata. -/
def attestationDataResponse (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) (slot : Slot) (committeeIndex : CommitteeIndex) :
    Except ErrorMessage ApiEnvelope := do
  return { data := ← apiJsonOr500 (← produceAttestationData config store optimistic slot
    committeeIndex) }

/-- The response of the payload attestation data endpoint, or none for the answer with code 204.

It names the consensus version of the store. -/
def payloadAttestationDataResponse (config : Config) (store : Store preset fork) (slot : Slot)
    (payloadPresent blobDataAvailable : Bool) : Except ErrorMessage (Option ApiEnvelope) := do
  match ← producePayloadAttestationData config store slot payloadPresent blobDataAvailable with
  | none => return none
  | some data => return some (← versioned fork (.ok data))

/-- The response of the aggregate endpoint, which names the consensus version of the state. -/
def aggregateAttestationResponse (state : BeaconState preset fork)
    (optimistic : OptimisticStore preset fork) (attestations : List (Attestation preset fork))
    (singles : List SingleAttestation) (dataRoot : Root) (slot : Slot)
    (committeeIndex : CommitteeIndex) : Except ErrorMessage ApiEnvelope :=
  versioned fork
    (aggregateAttestation state optimistic attestations singles dataRoot slot committeeIndex)

/-- The response of the contribution endpoint, with no metadata.

Before Altair there is no sync committee, and the answer is the error with code 400. -/
def syncCommitteeContributionResponse (state : BeaconState preset fork)
    (optimistic : OptimisticStore preset fork) (messages : List SyncCommitteeMessage)
    (slot : Slot) (subcommitteeIndex : UInt64) (root : Root) : Except ErrorMessage ApiEnvelope :=
  if altair : .altair ≤ fork then do
    return { data := ← apiJsonOr500 (← produceSyncCommitteeContribution state altair optimistic
      messages slot subcommitteeIndex root) }
  else .error (beforeFork "sync committee contribution" .altair)

end EthLib.Consensus.BeaconApi
