module

public import EthLib.Consensus.BeaconApi.Spelling

/-!
# `Consensus.RemoteSigningApi.Request`

The requests that a validator client sends to a remote signer, and their JSON forms.

A request names its kind in the field `type`, and the signer reads the object of that kind.

A versioned body names the fork of its data in the field `version`.

The [schemas] of the Remote-signing API fix each request, and the [sign endpoint] lists them.

This module holds the thirteen kinds of request that exist before Gloas.

[schemas]: https://github.com/ethereum/remote-signing-api/blob/44e9e0dcc115c91f8b739684f4789a8310476bd9/signing/schemas.yaml
[sign endpoint]: https://github.com/ethereum/remote-signing-api/blob/44e9e0dcc115c91f8b739684f4789a8310476bd9/signing/paths/sign.yaml
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Lean Base Serialization.Ssz BeaconApi

/-! ## The bodies of the requests -/

/-- The fork of the client and the chain it signs for, as the schema `Signing` gives them.

The container gives the JSON form only; no signature covers its root. -/
structure ForkInfo where
  /-- The fork versions and the epoch of the current fork. -/
  fork : ForkVersions
  /-- The root of the validators at genesis, which names the chain. -/
  genesisValidatorsRoot : Root
  deriving DecidableEq, Repr

instance : SszType ForkInfo :=
  .container ["fork", "genesis_validators_root"]
    (fun i => (i.fork, i.genesisValidatorsRoot))
    (fun (fork, genesisValidatorsRoot) => ⟨fork, genesisValidatorsRoot⟩)

instance : ApiSpelling ForkInfo := .unmarked

/-- The slot whose aggregator selection a request signs. -/
structure AggregationSlot where
  /-- The slot. -/
  slot : Slot
  deriving DecidableEq, Repr

instance : SszType AggregationSlot :=
  .container ["slot"] (fun a => a.slot) (fun slot => ⟨slot⟩)

instance : ApiSpelling AggregationSlot := .unmarked

/-- The epoch whose RANDAO reveal a request signs. -/
structure RandaoReveal where
  /-- The epoch. -/
  epoch : Epoch
  deriving DecidableEq, Repr

instance : SszType RandaoReveal :=
  .container ["epoch"] (fun r => r.epoch) (fun epoch => ⟨epoch⟩)

instance : ApiSpelling RandaoReveal := .unmarked

/-- The block root that a member of the sync committee signs at a slot.

The schema keeps only these two fields of the message of the consensus layer.

The container gives the JSON form only; the member signs the block root alone. -/
structure SyncCommitteeMessageData where
  /-- The root of the block at the head. -/
  beaconBlockRoot : Root
  /-- The slot of the message. -/
  slot : Slot
  deriving DecidableEq, Repr

instance : SszType SyncCommitteeMessageData :=
  .container ["beacon_block_root", "slot"] (fun m => (m.beaconBlockRoot, m.slot))
    (fun (beaconBlockRoot, slot) => ⟨beaconBlockRoot, slot⟩)

instance : ApiSpelling SyncCommitteeMessageData := .unmarked

/-- The deposit that a request signs, with the fork version of the chain it is for.

A deposit is signed before the chain knows the validator, so the request carries no fork info.

The container gives the JSON form only; the depositor signs the deposit message. -/
structure DepositSigningData where
  /-- The public key of the validator. -/
  pubkey : Cryptography.Bls.BLSPubkey
  /-- The commitment to the key or address that may withdraw the balance. -/
  withdrawalCredentials : Bytes32
  /-- The amount deposited. -/
  amount : Gwei
  /-- The fork version at genesis of the chain. -/
  genesisForkVersion : Version
  deriving DecidableEq, Repr

instance : SszType DepositSigningData :=
  .container ["pubkey", "withdrawal_credentials", "amount", "genesis_fork_version"]
    (fun d => (d.pubkey, d.withdrawalCredentials, d.amount, d.genesisForkVersion))
    (fun (pubkey, withdrawalCredentials, amount, genesisForkVersion) =>
      ⟨pubkey, withdrawalCredentials, amount, genesisForkVersion⟩)

instance : ApiSpelling DepositSigningData := .unmarked

/-! ## Versions -/

/-- The name of a consensus version in a request: the Beacon API name in upper case.

The discriminators of the versioned bodies in the schemas spell the versions so. -/
def versionName : ConsensusVersion → String
  | .phase0 => "PHASE0"
  | .altair => "ALTAIR"
  | .bellatrix => "BELLATRIX"
  | .capella => "CAPELLA"
  | .deneb => "DENEB"
  | .electra => "ELECTRA"
  | .fulu => "FULU"
  | .gloas => "GLOAS"

/-- The version with a name in a request, if one has it.

The schemas fix each name exactly, so no other spelling names a version. -/
def versionOfName? (name : String) : Option ConsensusVersion :=
  ConsensusVersion.all.find? (versionName · == name)

/-! ## The requests -/

/-- The kind of a request, as its field `type` names it. -/
inductive RequestType where
  /-- The selection proof of an aggregator, over a slot. -/
  | aggregationSlot
  /-- An aggregate and its proof, before versioned bodies; the source deprecates it. -/
  | aggregateAndProof
  /-- An aggregate and its proof, under the version of its data. -/
  | aggregateAndProofV2
  /-- The data of an attestation. -/
  | attestation
  /-- A Phase 0 block; the source deprecates it. -/
  | block
  /-- A block, or from Bellatrix its header, under the version of its data. -/
  | blockV2
  /-- A deposit. -/
  | deposit
  /-- The RANDAO reveal of an epoch. -/
  | randaoReveal
  /-- A voluntary exit. -/
  | voluntaryExit
  /-- The message of a member of the sync committee. -/
  | syncCommitteeMessage
  /-- The selection proof of an aggregator of the sync committee. -/
  | syncCommitteeSelectionProof
  /-- A contribution of the sync committee and its proof. -/
  | syncCommitteeContributionAndProof
  /-- The registration of a validator with builders. -/
  | validatorRegistration
  deriving DecidableEq, Repr

namespace RequestType

/-- Every kind of request, in the order of the schemas. -/
def all : List RequestType :=
  [aggregationSlot, aggregateAndProof, aggregateAndProofV2, attestation, block, blockV2,
    deposit, randaoReveal, voluntaryExit, syncCommitteeMessage, syncCommitteeSelectionProof,
    syncCommitteeContributionAndProof, validatorRegistration]

/-- The value of the field `type` for a kind of request. -/
def name : RequestType → String
  | aggregationSlot => "AGGREGATION_SLOT"
  | aggregateAndProof => "AGGREGATE_AND_PROOF"
  | aggregateAndProofV2 => "AGGREGATE_AND_PROOF_V2"
  | attestation => "ATTESTATION"
  | block => "BLOCK"
  | blockV2 => "BLOCK_V2"
  | deposit => "DEPOSIT"
  | randaoReveal => "RANDAO_REVEAL"
  | voluntaryExit => "VOLUNTARY_EXIT"
  | syncCommitteeMessage => "SYNC_COMMITTEE_MESSAGE"
  | syncCommitteeSelectionProof => "SYNC_COMMITTEE_SELECTION_PROOF"
  | syncCommitteeContributionAndProof => "SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF"
  | validatorRegistration => "VALIDATOR_REGISTRATION"

/-- The kind of request with a name, if one has it. -/
def ofName? (name : String) : Option RequestType :=
  all.find? (·.name == name)

end RequestType

/-- The part that most requests share: the fork info and an optional signing root.

The client may send the signing root so that the signer can check it against its own. -/
structure Signing where
  /-- The fork of the client and the chain it signs for. -/
  forkInfo : ForkInfo
  /-- The signing root that the client computed, if it sends one. -/
  signingRoot : Option Root := none
  deriving DecidableEq, Repr

/-- The block of a request of the second block kind, under the version of its data.

Up to Altair the request holds the whole block.

From Bellatrix it holds only the header, whose root is the root of the block. -/
inductive BlockV2Body (preset : Preset) where
  /-- A Phase 0 block. -/
  | phase0 (block : BeaconBlock preset .phase0)
  /-- An Altair block. -/
  | altair (block : BeaconBlock preset .altair)
  /-- The header of a block of a version from Bellatrix on. -/
  | header (version : { v : ConsensusVersion // .bellatrix ≤ v }) (header : BeaconBlockHeader)

/-- The version of the block of a request. -/
def BlockV2Body.version {preset : Preset} : BlockV2Body preset → ConsensusVersion
  | .phase0 _ => .phase0
  | .altair _ => .altair
  | .header version _ => version.1

/-- A request to sign, one case for each kind.

Each body is a container of the consensus layer, or a container of the schema itself.

The aggregate of the second aggregate kind has the shape of the fork of its version.

A deposit and a registration are signed outside any fork, so they carry no fork info. -/
inductive SigningRequest (preset : Preset) where
  /-- The selection proof of an aggregator, over a slot. -/
  | aggregationSlot (signing : Signing) (body : AggregationSlot)
  /-- A Phase 0 aggregate and its proof. -/
  | aggregateAndProof (signing : Signing) (body : AggregateAndProof preset .phase0)
  /-- An aggregate and its proof, under the version of its data. -/
  | aggregateAndProofV2 (signing : Signing) (version : ConsensusVersion)
      (body : AggregateAndProof preset version.fork)
  /-- The data of an attestation. -/
  | attestation (signing : Signing) (body : AttestationData)
  /-- A Phase 0 block. -/
  | block (signing : Signing) (body : BeaconBlock preset .phase0)
  /-- A block or its header, under the version of its data. -/
  | blockV2 (signing : Signing) (body : BlockV2Body preset)
  /-- A deposit, with its own signing root if the client sends one. -/
  | deposit (signingRoot : Option Root) (body : DepositSigningData)
  /-- The RANDAO reveal of an epoch. -/
  | randaoReveal (signing : Signing) (body : RandaoReveal)
  /-- A voluntary exit. -/
  | voluntaryExit (signing : Signing) (body : VoluntaryExit)
  /-- The message of a member of the sync committee. -/
  | syncCommitteeMessage (signing : Signing) (body : SyncCommitteeMessageData)
  /-- The selection proof of an aggregator of the sync committee. -/
  | syncCommitteeSelectionProof (signing : Signing) (body : SyncAggregatorSelectionData)
  /-- A contribution of the sync committee and its proof. -/
  | syncCommitteeContributionAndProof (signing : Signing) (body : ContributionAndProof preset)
  /-- The registration of a validator, with its own signing root if the client sends one. -/
  | validatorRegistration (signingRoot : Option Root) (body : ValidatorRegistrationV1)

namespace SigningRequest

variable {preset : Preset}

/-- The kind of a request. -/
def type : SigningRequest preset → RequestType
  | .aggregationSlot .. => .aggregationSlot
  | .aggregateAndProof .. => .aggregateAndProof
  | .aggregateAndProofV2 .. => .aggregateAndProofV2
  | .attestation .. => .attestation
  | .block .. => .block
  | .blockV2 .. => .blockV2
  | .deposit .. => .deposit
  | .randaoReveal .. => .randaoReveal
  | .voluntaryExit .. => .voluntaryExit
  | .syncCommitteeMessage .. => .syncCommitteeMessage
  | .syncCommitteeSelectionProof .. => .syncCommitteeSelectionProof
  | .syncCommitteeContributionAndProof .. => .syncCommitteeContributionAndProof
  | .validatorRegistration .. => .validatorRegistration

/-- The version that a versioned body of a request names, if the request has one. -/
def version? : SigningRequest preset → Option ConsensusVersion
  | .aggregateAndProofV2 _ version _ => some version
  | .blockV2 _ body => some body.version
  | _ => none

end SigningRequest

/-! ## Writing a request -/

/-- The field of an optional signing root, written as hex when present. -/
def signingRootFields : Option Root → List (String × Json)
  | none => []
  | some root => [("signingRoot", .str (toHex root.toArray))]

/-- The fields of the shared part of a request. -/
def signingFields (signing : Signing) : Except Err (List (String × Json)) := do
  return ("fork_info", ← toApiJson signing.forkInfo) :: signingRootFields signing.signingRoot

/-- A versioned body: its version, and its data under a key. -/
def versionedJson (version : ConsensusVersion) (key : String) (data : Json) : Json :=
  .mkObj [("version", .str (versionName version)), (key, data)]

/-- The JSON of the block of a request of the second block kind. -/
def BlockV2Body.toJson {preset : Preset} : BlockV2Body preset → Except Err Json
  | .phase0 block => return versionedJson .phase0 "block" (← toApiJson block)
  | .altair block => return versionedJson .altair "block" (← toApiJson block)
  | .header version blockHeader =>
    return versionedJson version.1 "block_header" (← toApiJson blockHeader)

namespace SigningRequest

variable {preset : Preset}

/-- The fields of a request other than its kind: the shared part and the body. -/
def fields : SigningRequest preset → Except Err (List (String × Json))
  | .aggregationSlot signing body =>
    return ("aggregation_slot", ← toApiJson body) :: (← signingFields signing)
  | .aggregateAndProof signing body =>
    return ("aggregate_and_proof", ← toApiJson body) :: (← signingFields signing)
  | .aggregateAndProofV2 signing version body =>
    return ("aggregate_and_proof", ← (versionedJson version "data" <$> toApiJson body)) ::
      (← signingFields signing)
  | .attestation signing body =>
    return ("attestation", ← toApiJson body) :: (← signingFields signing)
  | .block signing body => return ("block", ← toApiJson body) :: (← signingFields signing)
  | .blockV2 signing body => return ("beacon_block", ← body.toJson) :: (← signingFields signing)
  | .deposit signingRoot body =>
    return ("deposit", ← toApiJson body) :: signingRootFields signingRoot
  | .randaoReveal signing body =>
    return ("randao_reveal", ← toApiJson body) :: (← signingFields signing)
  | .voluntaryExit signing body =>
    return ("voluntary_exit", ← toApiJson body) :: (← signingFields signing)
  | .syncCommitteeMessage signing body =>
    return ("sync_committee_message", ← toApiJson body) :: (← signingFields signing)
  | .syncCommitteeSelectionProof signing body =>
    return ("sync_aggregator_selection_data", ← toApiJson body) :: (← signingFields signing)
  | .syncCommitteeContributionAndProof signing body =>
    return ("contribution_and_proof", ← toApiJson body) :: (← signingFields signing)
  | .validatorRegistration signingRoot body =>
    return ("validator_registration", ← toApiJson body) :: signingRootFields signingRoot

/-- The JSON document of a request: its kind under `type`, then its other fields. -/
def toJson (request : SigningRequest preset) : Except Err Json := do
  return .mkObj (("type", .str request.type.name) :: (← request.fields))

end SigningRequest

/-! ## Reading a request -/

/-- Why a JSON document is not a request. -/
inductive RequestError where
  /-- The object under the key that the error gives is not an object.

  An empty key names the whole document. -/
  | notAnObject (key : String)
  /-- The object lacks the key that the error gives.

  The key is the one inside its object, such as `version` inside a versioned body. -/
  | missingField (key : String)
  /-- The value under the key that the error gives does not read, for the reason it gives. -/
  | badField (key : String) (fault : Err)
  /-- The field `type` names no kind of request; the error gives the name. -/
  | unknownType (name : String)
  /-- The body under the key that the error gives names no version that the kind admits.

  The error gives the name of the version. -/
  | unknownVersion (key name : String)
  deriving DecidableEq, Repr

/-- The code of an error at the C boundary, one for each constructor. -/
def RequestError.code : RequestError → UInt32
  | .notAnObject _ => 1
  | .missingField _ => 2
  | .badField .. => 3
  | .unknownType _ => 4
  | .unknownVersion .. => 5

/-- The value under a key of an object, which must be present. -/
def field (document : Json) (key : String) : Except RequestError Json :=
  match document.getObjVal? key with
  | .ok value => .ok value
  | .error _ => .error (.missingField key)

/-- The value of a type under a key of an object, read in the JSON mapping of SSZ. -/
def readValue (α : Type) [SszType α] [ApiSpelling α] (document : Json) (key : String) :
    Except RequestError α := do
  match ofApiJson α (← field document key) with
  | .ok x => .ok x
  | .error fault => .error (.badField key fault)

/-- The optional signing root of a request: 32 bytes as hex, with digits in either case. -/
def readSigningRoot (document : Json) : Except RequestError (Option Root) :=
  (ApiEnvelope.readKey document "signingRoot" ApiEnvelope.readRoot).mapError fun _ =>
    .badField "signingRoot" .typeMismatch

/-- The shared part of a request: the fork info, which must be present, and the signing root. -/
def readSigning (document : Json) : Except RequestError Signing := do
  return ⟨← readValue ForkInfo document "fork_info", ← readSigningRoot document⟩

/-- The object under a key, which must be an object. -/
def readObject (document : Json) (key : String) : Except RequestError Json := do
  let body ← field document key
  let .obj _ := body | throw (.notAnObject key)
  return body

/-- The version that the versioned body under a key names. -/
def readVersion (body : Json) (key : String) : Except RequestError ConsensusVersion := do
  let .str name ← field body "version" | throw (.badField "version" .typeMismatch)
  let some version := versionOfName? name | throw (.unknownVersion key name)
  return version

/-- The kind of request that the field `type` names. -/
def readType (document : Json) : Except RequestError RequestType := do
  let .str name ← field document "type" | throw (.badField "type" .typeMismatch)
  let some type := RequestType.ofName? name | throw (.unknownType name)
  return type

/-- The block of a request of the second block kind, from its versioned body.

Up to Altair the body holds the block under `block`.

From Bellatrix it holds the header under `block_header`. -/
def BlockV2Body.ofJson (preset : Preset) (body : Json) :
    Except RequestError (BlockV2Body preset) := do
  let version ← readVersion body "beacon_block"
  if atLeast : .bellatrix ≤ version then
    return .header ⟨version, atLeast⟩ (← readValue BeaconBlockHeader body "block_header")
  else if version = .phase0 then
    return .phase0 (← readValue (BeaconBlock preset .phase0) body "block")
  else
    return .altair (← readValue (BeaconBlock preset .altair) body "block")

/-- The request that a JSON document holds.

The field `type` decides the kind, and the body must be under the key of that kind.

A versioned body must name a version that the kind admits.

The request ignores any other key, as the schemas do not forbid one.

Each body is read in the JSON mapping of SSZ, which refuses a key that its container lacks. -/
def SigningRequest.ofJson (preset : Preset) (document : Json) :
    Except RequestError (SigningRequest preset) := do
  let .obj _ := document | throw (.notAnObject "")
  match ← readType document with
  | .aggregationSlot =>
    return .aggregationSlot (← readSigning document)
      (← readValue AggregationSlot document "aggregation_slot")
  | .aggregateAndProof =>
    return .aggregateAndProof (← readSigning document)
      (← readValue (AggregateAndProof preset .phase0) document "aggregate_and_proof")
  | .aggregateAndProofV2 =>
    let signing ← readSigning document
    let body ← readObject document "aggregate_and_proof"
    let version ← readVersion body "aggregate_and_proof"
    return .aggregateAndProofV2 signing version
      (← readValue (AggregateAndProof preset version.fork) body "data")
  | .attestation =>
    return .attestation (← readSigning document)
      (← readValue AttestationData document "attestation")
  | .block =>
    return .block (← readSigning document)
      (← readValue (BeaconBlock preset .phase0) document "block")
  | .blockV2 =>
    let signing ← readSigning document
    return .blockV2 signing (← BlockV2Body.ofJson preset (← readObject document "beacon_block"))
  | .deposit =>
    return .deposit (← readSigningRoot document) (← readValue DepositSigningData document "deposit")
  | .randaoReveal =>
    return .randaoReveal (← readSigning document)
      (← readValue RandaoReveal document "randao_reveal")
  | .voluntaryExit =>
    return .voluntaryExit (← readSigning document)
      (← readValue VoluntaryExit document "voluntary_exit")
  | .syncCommitteeMessage =>
    return .syncCommitteeMessage (← readSigning document)
      (← readValue SyncCommitteeMessageData document "sync_committee_message")
  | .syncCommitteeSelectionProof =>
    return .syncCommitteeSelectionProof (← readSigning document)
      (← readValue SyncAggregatorSelectionData document "sync_aggregator_selection_data")
  | .syncCommitteeContributionAndProof =>
    return .syncCommitteeContributionAndProof (← readSigning document)
      (← readValue (ContributionAndProof preset) document "contribution_and_proof")
  | .validatorRegistration =>
    return .validatorRegistration (← readSigningRoot document)
      (← readValue ValidatorRegistrationV1 document "validator_registration")

end EthLib.Consensus.RemoteSigningApi
