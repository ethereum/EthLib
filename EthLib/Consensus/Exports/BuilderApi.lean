module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.BuilderApi.AuthData
public import EthLib.Consensus.BuilderApi.Bid
public import EthLib.Consensus.BuilderApi.Encoding
public import EthLib.Consensus.BuilderApi.GloasBid
public import EthLib.Consensus.BuilderApi.Registration
public import EthLib.Consensus.BuilderApi.RequestAuth
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Exports.Ssz
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.BuilderApi`

C-ABI exports for Builder API signature checks, registrations, bids, unblinding and bid valuation.

Two more exports write and read the JSON body of a response, which carries its version.

One more gives the default data of a Gloas request, from the builder's URL.

The value of a bid is capped by the proposer's cap on the execution payment.

From Bellatrix to Fulu, a signed registration or bid carries the key that signed it.

From Gloas, a request names the proposer's key outside the signed authentication.

The configuration names the chain, whose genesis fork version enters the domain.

For a signature check, an unknown name, an unsigned container or a fork out of range has code 0.

Bytes that do not decode, or a root that fails, keep the code of their SSZ error.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- Whether the signature of a signed message of the Builder API verifies. -/
def isValidBuilderSignatureOf (args : String × String × Option PyValue × String × ByteArray) :
    Result Bool := do
  let (name, fork, replacements, type, data) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  unless HasBuilderApi fork do
    throw (0, s!"no Builder API messages at {fork.name}")
  let config ← configWithValue name replacements
  match type with
  | "SignedValidatorRegistrationV1" =>
    let signed ← runSsz "input rejected" (SszType.deserialize SignedValidatorRegistrationV1 data)
    runSsz "root rejected" (verifyRegistrationSignature config .bls signed)
  | "SignedBuilderBid" =>
    let signed ← runSsz "input rejected"
      (SszType.deserialize (SignedBuilderBid preset fork) data)
    runSsz "root rejected" (verifyBuilderBidSignature config .bls signed)
  | _ => throw (0, s!"no signed message {type} in the Builder API")

/-- Whether the signature of a signed message of the Builder API verifies.

The arguments are the name of the preset and of the configuration, the fork and replacements.

Then come the name of the container and its SSZ bytes. -/
@[export eth_consensus_is_valid_builder_signature]
def isValidBuilderSignatureExport (args : PyValue) : Result PyValue :=
  pyExport isValidBuilderSignatureOf args

/-- The root and the bytes of the signed block that a signed blinded block and a payload give.

The payload comes as the builder reveals it: alone before Deneb, with its blobs bundle from Deneb.

The bundle is decoded but not checked, since the header alone binds the payload.

None when the header of the payload is not the header of the blinded block. -/
def unblindOf (args : String × String × ByteArray × ByteArray) :
    Result (Option (Root × ByteArray)) := do
  let (name, fork, blinded, revealed) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if range : HasBuilderApi fork then
    let signed ← runSsz "input rejected"
      (SszType.deserialize (SignedBlindedBeaconBlock preset fork) blinded)
    let payload ← (·.executionPayload) <$> runSsz "payload rejected"
      (SszType.deserialize (RevealedPayload preset fork) revealed)
    match signed.unblind range payload with
    | .error .headerMismatch => return none
    | .error (.header fault) => runSsz "header rejected" (.error fault)
    | .ok full =>
      let root ← runSsz "root rejected" (SszType.hashTreeRoot full)
      let bytes ← runSsz "value rejected" (SszType.serialize full)
      return some (root, bytes)
  else throw (0, s!"no Builder API messages at {fork.name}")

/-- The root and the bytes of the signed block that a signed blinded block and a payload give.

The arguments are the name of the preset, the fork, the signed blinded block and the payload.

The payload is the SSZ response of the builder, with its blobs bundle from Deneb.

None when the header of the payload is not the header of the blinded block. -/
@[export eth_consensus_unblind_signed_blinded_block]
def unblindExport (args : PyValue) : Result PyValue := pyExport unblindOf args

/-- The name of the rule that refuses a registration. -/
def RegistrationError.reason : BuilderApi.RegistrationError → String
  | .unknownValidator => "unknown_validator"
  | .notEligible => "not_eligible"
  | .clockOverflow => "clock_overflow"
  | .tooFarInFuture => "too_far_in_future"
  | .olderThanPrevious => "older_than_previous"
  | .badSignature => "bad_signature"
  | .root _ => "root"

/-- None when a builder keeps a signed registration, or the rule that refuses it. -/
def processRegistrationOf
    (args : String × String × Option PyValue × ByteArray × List ByteArray × ByteArray × UInt64) :
    Result (Option String) := do
  let (name, fork, replacements, state, kept, data, now) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  unless HasBuilderApi fork do
    throw (0, s!"no Builder API messages at {fork.name}")
  let config ← configWithValue name replacements
  let state ← runSsz "state rejected" (SszType.deserialize (BeaconState preset fork) state)
  let entries ← kept.mapM fun bytes =>
    runSsz "registry rejected" (SszType.deserialize SignedValidatorRegistrationV1 bytes)
  let signed ← runSsz "input rejected" (SszType.deserialize SignedValidatorRegistrationV1 data)
  match BuilderApi.processRegistration config .bls state ⟨entries⟩ signed now with
  | .ok () => return none
  | .error (.root fault) => runSsz "root rejected" (.error fault)
  | .error e => return some (RegistrationError.reason e)

/-- None when a builder keeps a signed registration, or the name of the rule that refuses it.

The arguments are the name of the preset and of the configuration, the fork and replacements.

Then come the state, the signed registrations the builder keeps, the one to check and the time.

The time is that of the builder's clock, in seconds. -/
@[export eth_consensus_process_registration]
def processRegistrationExport (args : PyValue) : Result PyValue :=
  pyExport processRegistrationOf args

/-- The value that SSZ bytes encode, with code 0 and a name for the input when they do not. -/
def decodeRejected (α : Type) [SszType α] (what : String) (bytes : ByteArray) : Result α :=
  (SszType.deserialize α bytes).mapError fun e => (0, s!"{what} rejected: {reprStr e}")

/-- Whether a builder serves a request for a bid, on its state transitioned to the slot. -/
def isEligibleForBidOf
    (args : String × String × ByteArray × List ByteArray × UInt64 × Hash32 ×
      Cryptography.Bls.BLSPubkey) : Result Bool := do
  let (name, fork, state, kept, slot, parentHash, pubkey) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if range : HasBuilderApi fork then
    let state ← decodeRejected (BeaconState preset fork) "state" state
    let entries ← kept.mapM (decodeRejected SignedValidatorRegistrationV1 "registry")
    (liftAccessor (BuilderApi.isEligibleForBid state range ⟨entries⟩ slot parentHash
      pubkey)).mapError fun e => (e.code, reprStr e)
  else throw (0, s!"no Builder API messages at {fork.name}")

/-- Whether a builder serves a request for a bid.

The arguments are the name of the preset, the fork, the state and the signed registrations kept.

Then come the slot, the parent hash and the key of the request.

The state is the builder's state, transitioned to the slot.

Bytes that do not decode have code 0, and a state with no proposer keeps the code of its error. -/
@[export eth_consensus_is_eligible_for_bid]
def isEligibleForBidExport (args : PyValue) : Result PyValue :=
  pyExport isEligibleForBidOf args

/-- The name of the rule that refuses a bid. -/
def BidError.reason : BuilderApi.BidError → String
  | .wrongParentHash => "wrong_parent_hash"
  | .wrongFeeRecipient => "wrong_fee_recipient"
  | .badSignature => "bad_signature"
  | .root _ => "root"

/-- None when a proposer accepts a signed bid, or the rule that refuses it. -/
def processBidOf
    (args : String × String × Option PyValue × ByteArray × ByteArray × ExecutionAddress) :
    Result (Option String) := do
  let (name, fork, replacements, state, data, feeRecipient) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if range : HasBuilderApi fork then
    let config ← configWithValue name replacements
    let state ← runSsz "state rejected" (SszType.deserialize (BeaconState preset fork) state)
    let signed ← runSsz "input rejected"
      (SszType.deserialize (SignedBuilderBid preset fork) data)
    match BuilderApi.processBid config .bls state range signed feeRecipient with
    | .ok () => return none
    | .error (.root fault) => runSsz "root rejected" (.error fault)
    | .error e => return some (BidError.reason e)
  else throw (0, s!"no Builder API messages at {fork.name}")

/-- None when a proposer accepts a signed bid, or the name of the rule that refuses it.

The arguments are the name of the preset and of the configuration, the fork and replacements.

Then come the state of the proposal, the signed bid and the fee recipient that was registered. -/
@[export eth_consensus_process_bid]
def processBidExport (args : PyValue) : Result PyValue :=
  pyExport processBidOf args

/-- From Gloas: whether a builder serves a request for a bid, on its state at the slot.

The preferences are those received on gossip, found by the index of their validator. -/
def isEligibleForBidGloasOf
    (args : String × String × ByteArray × List ByteArray × UInt64 × Hash32 × Root ×
      Cryptography.Bls.BLSPubkey) : Result Bool := do
  let (name, fork, state, received, slot, parentHash, parentRoot, pubkey) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if gloas : .glamsterdam ≤ fork then
    let state ← decodeRejected (BeaconState preset fork) "state" state
    let received ← received.mapM (decodeRejected ProposerPreferences "preferences")
    let preferences (index : ValidatorIndex) := received.find? (·.validatorIndex = index)
    (BuilderApi.isEligibleForBidGloas state gloas preferences slot parentHash parentRoot
      pubkey).mapError fun e => (e.code, reprStr e)
  else throw (0, s!"no Gloas bids at {fork.name}")

/-- From Gloas: whether a builder serves a request for a bid.

The arguments are the name of the preset, the fork, the state and the preferences received.

Then come the slot, the parent hash, the parent root and the key of the request.

Bytes that do not decode have code 0, and a value that cannot be read keeps its own code. -/
@[export eth_consensus_is_eligible_for_bid_gloas]
def isEligibleForBidGloasExport (args : PyValue) : Result PyValue :=
  pyExport isEligibleForBidGloasOf args

/-- The name of the rule that refuses a fetched bid. -/
def ValidateBidError.reason : BuilderApi.ValidateBidError → String
  | .inactiveBuilder => "inactive_builder"
  | .wrongSlot => "wrong_slot"
  | .wrongFeeRecipient => "wrong_fee_recipient"
  | .wrongParentHash => "wrong_parent_hash"
  | .wrongParentRoot => "wrong_parent_root"
  | .wrongPrevRandao => "wrong_prev_randao"
  | .incompatibleGasLimit => "incompatible_gas_limit"
  | .cannotCoverBid => "cannot_cover_bid"
  | .fault _ => "fault"

/-- From Gloas: None when a proposer accepts a fetched bid, or the rule that refuses it. -/
def validateBidOf
    (args : String × String × Option PyValue × ByteArray × ByteArray × UInt64 × ByteArray ×
      ExecutionAddress) : Result (Option String) := do
  let (name, fork, replacements, state, preferences, parentGasLimit, data, feeRecipient) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if gloas : .glamsterdam ≤ fork then
    let config ← configWithValue name replacements
    let state ← decodeRejected (BeaconState preset fork) "state" state
    let preferences ← decodeRejected ProposerPreferences "preferences" preferences
    let signed ← decodeRejected (SignedExecutionPayloadBid preset fork) "bid" data
    match BuilderApi.validateBid config .bls state gloas preferences parentGasLimit signed
        feeRecipient with
    | .ok true => return none
    | .ok false => return some "bad_signature"
    | .error (.fault e) => throw (e.code, reprStr e)
    | .error e => return some (ValidateBidError.reason e)
  else throw (0, s!"no Gloas bids at {fork.name}")

/-- From Gloas: None when a proposer accepts a fetched bid, or the name of the rule that refuses it.

The arguments are the name of the preset and of the configuration, the fork and replacements.

Then come the state, the proposer's preferences and the gas limit of the parent payload.

Then come the signed bid and the proposer's fee recipient.

A signature that does not verify is named, bytes that do not decode have code 0.

A value that cannot be read keeps its own code. -/
@[export eth_consensus_validate_bid]
def validateBidExport (args : PyValue) : Result PyValue :=
  pyExport validateBidOf args

/-- Whether a proposer key signed a Gloas request authentication. -/
def verifyBuilderRequestAuthSignatureOf
    (args : String × String × Option PyValue × Cryptography.Bls.BLSPubkey × ByteArray) :
    Result Bool := do
  let (name, fork, replacements, pubkey, data) := args
  let fork ← forkOf fork.toUTF8
  unless .glamsterdam ≤ fork do
    throw (0, s!"no builder request authentication at {fork.name}")
  let config ← configWithValue name replacements
  let signed ← runSsz "input rejected" (SszType.deserialize SignedBuilderRequestAuth data)
  runSsz "root rejected" (verifyBuilderRequestAuthSignature config .bls signed pubkey)

/-- Whether a proposer key signed a Gloas request authentication given in SSZ. -/
@[export eth_consensus_verify_builder_request_auth_signature]
def verifyBuilderRequestAuthSignatureExport (args : PyValue) : Result PyValue :=
  pyExport verifyBuilderRequestAuthSignatureOf args

/-- The name of a failed check of a request to a builder. -/
def AuthFailure.reason : BuilderApi.AuthFailure → String
  | .badVersion => "bad_version"
  | .emptyData => "empty_data"
  | .dataMismatch => "data_mismatch"
  | .slotMismatch => "slot_mismatch"
  | .slotPassed => "slot_passed"
  | .badSignature => "bad_signature"

/-- From Gloas: the failed checks of a request for a bid, by name. -/
def builderRequestAuthFailuresOf
    (args : String × String × Option PyValue × ByteArray × UInt64 × Cryptography.Bls.BLSPubkey ×
      Option String × ByteArray) : Result (List String) := do
  let (name, fork, replacements, agreed, pathSlot, pubkey, header, data) := args
  let fork ← forkOf fork.toUTF8
  unless .glamsterdam ≤ fork do
    throw (0, s!"no builder request authentication at {fork.name}")
  let config ← configWithValue name replacements
  let signed ← runSsz "input rejected" (SszType.deserialize SignedBuilderRequestAuth data)
  let failures ← runSsz "root rejected"
    (BuilderApi.authFailures config .bls agreed pathSlot pubkey header signed)
  return failures.map AuthFailure.reason

/-- From Gloas: the failed checks of a request for a bid, by name, in order.

The arguments are the name of the preset and of the configuration, the fork and replacements.

Then come the agreed data, the slot of the path, the key of the path and the version header.

Then come the SSZ bytes of the signed authentication. -/
@[export eth_consensus_builder_request_auth_failures]
def builderRequestAuthFailuresExport (args : PyValue) : Result PyValue :=
  pyExport builderRequestAuthFailuresOf args

/-- From Gloas: the failed checks of a request that submits preferences, by name. -/
def builderPreferencesFailuresOf
    (args : String × String × Option PyValue × ByteArray × UInt64 × Cryptography.Bls.BLSPubkey ×
      Option String × ByteArray) : Result (List String) := do
  let (name, fork, replacements, agreed, currentSlot, pubkey, header, data) := args
  let fork ← forkOf fork.toUTF8
  unless .glamsterdam ≤ fork do
    throw (0, s!"no builder request authentication at {fork.name}")
  let config ← configWithValue name replacements
  let request ← runSsz "input rejected" (SszType.deserialize BuilderPreferencesRequest data)
  let failures ← runSsz "root rejected"
    (BuilderApi.preferencesFailures config .bls agreed currentSlot pubkey header request)
  return failures.map AuthFailure.reason

/-- From Gloas: the failed checks of a request that submits preferences, by name, in order.

The arguments are the name of the preset and of the configuration, the fork and replacements.

Then come the agreed data, the builder's current slot, the key of the path and the version header.

Then come the SSZ bytes of the request. -/
@[export eth_consensus_builder_preferences_failures]
def builderPreferencesFailuresExport (args : PyValue) : Result PyValue :=
  pyExport builderPreferencesFailuresOf args

/-- From Gloas: the default data of a request to a builder, from the builder's URL. -/
@[export eth_consensus_default_auth_data]
def defaultAuthDataExport (args : PyValue) : Result PyValue :=
  pyExport (fun url => (BuilderApi.defaultAuthData url).mapError fun e => (e.code, reprStr e) :
    String → Result ByteArray) args

/-- The value of a builder's bid from its two payments and the proposer's execution payment cap. -/
@[export eth_consensus_builder_bid_value]
def builderBidValueExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, payment, cap) =>
    .ok (builderBidValue value payment ⟨cap⟩) : Gwei × Gwei × Gwei → Result Nat) args

/-- Whether the Builder API sends a container with its version, at a fork.

From Bellatrix to Fulu, the response to a request for a [header] carries a signed builder bid.

The response to a [blinded block] carries the payload alone before Deneb.

From Deneb to Fulu, it carries the payload with its blobs bundle.

At Gloas, the response to a request for a [bid] carries a signed bid of the execution payload.

[header]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/apis/builder/header.yaml
[blinded block]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/apis/builder/blinded_blocks.yaml
[bid]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/apis/builder/execution_payload_bid.yaml
-/
def isVersionedBody (fork : Fork) : String → Bool
  | "SignedBuilderBid" => .bellatrix ≤ fork && fork < .glamsterdam
  | "ExecutionPayload" => .bellatrix ≤ fork && fork < .dencun
  | "ExecutionPayloadAndBlobsBundle" => .dencun ≤ fork && fork < .glamsterdam
  | "SignedExecutionPayloadBid" => .glamsterdam ≤ fork && fork < .hegota
  | _ => false

/-- The version of a versioned body of the Builder API, at a fork. -/
def versionedBodyOf (fork : Fork) (type : String) : Result ConsensusVersion := do
  let some version := BuilderApi.builderVersion? fork
    | throw (0, s!"no Builder API version at {fork.name}")
  unless isVersionedBody fork type do
    throw (0, s!"no versioned body {type} at {fork.name}")
  return version

/-- The JSON body of a response of the Builder API, for the value that the bytes encode. -/
def builderApiJsonOf (args : String × String × String × ByteArray) : Result PyValue := do
  let (name, fork, type, data) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let version ← versionedBodyOf fork type
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  let data ← runSsz "value rejected" (BeaconApi.toApiJson value)
  return PyValue.ofJson (BeaconApi.ApiEnvelope.toJson { version := some version, data })

/-- The JSON body of a response of the Builder API: the version of the fork and the data.

The arguments are the name of the preset, the fork, the container and its SSZ bytes.

An unknown preset or fork, or a container that the API does not version at the fork, has code 0.

Bytes that do not decode keep the code of their SSZ error. -/
@[export eth_consensus_builder_api_json]
def builderApiJsonExport (args : PyValue) : Result PyValue := pyExport builderApiJsonOf args

/-- The code and the message of a JSON body that is not a value in the envelope of a version.

A fault of the data keeps the code of its SSZ error, and a fault of the envelope has code 0. -/
def envelopeFault : BeaconApi.EnvelopeError → UInt32 × String
  | .data fault => (fault.code, s!"document rejected: {reprStr fault}")
  | .notAnObject => (0, "body rejected: not an object")
  | .missingData => (0, "body rejected: no data")
  | .badField key => (0, s!"body rejected: malformed {key}")
  | .wrongVersion expected found =>
    (0, s!"body rejected: version {(found.map (·.name)).getD "absent"}, expected {expected.name}")

/-- The SSZ bytes of the value that a JSON body of the Builder API holds, at the fork's version. -/
def builderApiSszOf (args : String × String × String × PyValue) : Result ByteArray := do
  let (name, fork, type, document) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let version ← versionedBodyOf fork type
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  match BeaconApi.readVersioned container.type version document.toJson with
  | .ok value => runSsz "value rejected" (SszType.serialize value)
  | .error fault => throw (envelopeFault fault)

/-- The SSZ bytes of the value that a JSON body of the Builder API holds.

The arguments are the name of the preset, the fork, the container and the body.

The body must name the version of the fork, and its data must hold the container.

Every other key is ignored, except the metadata keys of the Beacon API, which must hold their form.

An unknown preset or fork, or a container that the API does not version at the fork, has code 0.

So does a body that is not an object, lacks data, has a malformed key, or lacks the version.

Data that the container does not read keeps the code of its SSZ error. -/
@[export eth_consensus_builder_api_ssz]
def builderApiSszExport (args : PyValue) : Result PyValue := pyExport builderApiSszOf args

end EthLib.Consensus.Exports
