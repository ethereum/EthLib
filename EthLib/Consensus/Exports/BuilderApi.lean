module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.BuilderApi`

C-ABI exports for Builder API signature checks and capped bid valuation.

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
