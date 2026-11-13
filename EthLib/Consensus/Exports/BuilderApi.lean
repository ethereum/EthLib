module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.BuilderApi.Bid
public import EthLib.Consensus.BuilderApi.Registration
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.BuilderApi`

C-ABI exports for Builder API signature checks, registrations, bids, unblinding and bid valuation.

The value of a bid is capped by the proposer's cap on the execution payment.

From Bellatrix to Fulu, a signed registration or bid carries the key that signed it.

From Gloas, a request names the proposer's key outside the signed authentication.

The configuration names the chain, whose genesis fork version enters the domain.

An unknown name, a container that is not a signed message, or a fork out of range has code 0.

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
    let payload ← if .dencun ≤ fork then
        (·.executionPayload) <$> runSsz "payload rejected"
          (SszType.deserialize (ExecutionPayloadAndBlobsBundle preset fork) revealed)
      else runSsz "payload rejected" (SszType.deserialize (ExecutionPayload preset fork) revealed)
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
    runSsz "registry rejected" (SszType.deserialize ValidatorRegistrationV1 bytes)
  let signed ← runSsz "input rejected" (SszType.deserialize SignedValidatorRegistrationV1 data)
  match BuilderApi.processRegistration config .bls state ⟨entries⟩ signed now with
  | .ok () => return none
  | .error (.root fault) => runSsz "root rejected" (.error fault)
  | .error e => return some (RegistrationError.reason e)

/-- None when a builder keeps a signed registration, or the name of the rule that refuses it.

The arguments are the name of the preset and of the configuration, the fork and replacements.

Then come the state, the registrations the builder keeps, the signed registration and the time.

The time is that of the builder's clock, in seconds. -/
@[export eth_consensus_process_registration]
def processRegistrationExport (args : PyValue) : Result PyValue :=
  pyExport processRegistrationOf args

/-- Whether a builder serves a request for a bid, on its state transitioned to the slot. -/
def isEligibleForBidOf
    (args : String × String × ByteArray × List ByteArray × UInt64 × Hash32 ×
      Cryptography.Bls.BLSPubkey) : Result Bool := do
  let (name, fork, state, kept, slot, parentHash, pubkey) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if range : HasBuilderApi fork then
    let decode {α : Type} [SszType α] (what : String) (bytes : ByteArray) : Result α :=
      (SszType.deserialize α bytes).mapError fun e => (0, s!"{what} rejected: {reprStr e}")
    let state ← decode (α := BeaconState preset fork) "state" state
    let entries ← kept.mapM (decode (α := ValidatorRegistrationV1) "registry")
    (liftAccessor (BuilderApi.isEligibleForBid state range ⟨entries⟩ slot parentHash
      pubkey)).mapError fun e => (e.code, reprStr e)
  else throw (0, s!"no Builder API messages at {fork.name}")

/-- Whether a builder serves a request for a bid.

The arguments are the name of the preset, the fork, the state and the registrations kept.

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

/-- The value of a builder's bid from its two payments and the proposer's execution payment cap. -/
@[export eth_consensus_builder_bid_value]
def builderBidValueExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, payment, cap) =>
    .ok (builderBidValue value payment ⟨cap⟩) : Gwei × Gwei × Gwei → Result Nat) args

end EthLib.Consensus.Exports
