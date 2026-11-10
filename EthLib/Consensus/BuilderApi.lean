module

public import EthLib.Consensus.Accessors
public import EthLib.Consensus.Containers.BuilderApi
public import EthLib.Consensus.Signing
public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.BuilderApi`

The Builder API connects a proposer to the builders that sell it a payload.

From Bellatrix to Fulu, a validator first registers its fee recipient and gas limit with a builder.

A builder then bids on a payload by its header, under its own key.

The proposer signs a blinded block, which holds that header in place of the payload.

Only then does the builder reveal the payload, and publish the full block with that signature.

A registration and a bid are signed under the application domain of builders.

That domain reads the genesis fork version and a zero root of the genesis validators.

So a registration keeps its signature across forks.

A blinded block is signed under the proposer domain of its fork, like a full block.

The proposer signs the same root for both, so one signature serves the two blocks.

From Gloas the protocol carries the bids of builders, and the Builder API has other messages.

Its request authentication uses a separate application domain.

The [Gloas builder] document gives that domain and the cap on a bid's execution payment.

The [signing] rules come from the builder specification.

[signing]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/builder.md#signing
[Gloas builder]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- From Bellatrix to Fulu: the body with the header of its payload in place of the payload.

It fails when the root of the transactions or of the withdrawals of the payload fails.

The proofs show that this never happens. -/
def BeaconBlockBody.blind (body : BeaconBlockBody preset fork) (range : HasBuilderApi fork) :
    Except Err (BlindedBeaconBlockBody preset fork) := do
  let header ← (body.executionPayload range).header
  return ⟨body.randaoReveal, body.eth1Data, body.graffiti, body.proposerSlashings,
    body.attesterSlashings, body.attestations, body.deposits, body.voluntaryExits,
    body.syncAggregate, fun _ => header, body.blsToExecutionChanges, body.blobKzgCommitments,
    body.executionRequests⟩

/-- From Bellatrix to Fulu: the block with the header of its payload in place of the payload.

It fails as the blinding of its body does, which never happens. -/
def BeaconBlock.blind (block : BeaconBlock preset fork) (range : HasBuilderApi fork) :
    Except Err (BlindedBeaconBlock preset fork) := do
  return ⟨block.slot, block.proposerIndex, block.parentRoot, block.stateRoot,
    ← block.body.blind range⟩

/-- The domain type of the messages of the Builder API, an application domain.

It is the single bit of the application mask, so no domain type of a fork equals it. -/
def DOMAIN_APPLICATION_BUILDER : DomainType := #v[0x00, 0x00, 0x00, 0x01]

/-- From Gloas: the application domain type for request authentication. -/
def DOMAIN_BUILDER_REQUEST_AUTH : DomainType := #v[0x0B, 0x00, 0x00, 0x01]

/-- The request authentication domain at the genesis fork version, with a zero validators root. -/
def builderRequestAuthDomain (config : Config) : Except Err Domain :=
  computeDomain config DOMAIN_BUILDER_REQUEST_AUTH

/-- Whether the endpoint's proposer key signed the request authentication.

This checks the signature alone; the endpoint also checks the agreed data and the proposal slot. -/
def verifyBuilderRequestAuthSignature (config : Config) (checks : SignatureChecks)
    (signed : SignedBuilderRequestAuth) (pubkey : BLSPubkey) : Except Err Bool := do
  let signingRoot ← computeSigningRoot signed.message (← builderRequestAuthDomain config)
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature)

/-- A bid's value to the proposer, in Gwei, with its execution payment capped by preferences.

The sum is a natural number, so two 64-bit payments do not wrap when compared. -/
def builderBidValue (value executionPayment : Gwei) (preferences : BuilderPreferences) : Nat :=
  value.toNat + min executionPayment.toNat preferences.maxExecutionPayment.toNat

/-- A Gloas bid's value to the proposer under its per-builder preferences, in Gwei. -/
def ExecutionPayloadBid.proposerValue (bid : ExecutionPayloadBid preset fork)
    (preferences : BuilderPreferences) : Nat :=
  builderBidValue bid.value bid.executionPayment preferences

/-- The domain of the messages of the Builder API on a chain.

It is the domain of its type at the genesis fork version, with a zero root of the validators.

The builder specification passes no fork version and no root, at every fork. -/
def builderDomain (config : Config) : Except Err Domain :=
  computeDomain config DOMAIN_APPLICATION_BUILDER

/-- Whether a key signed an object under the domain of the Builder API.

It fails when the root of the object or of the domain fails. -/
def verifyBuilderApiSignature {α : Type} [SszType α] (config : Config) (checks : SignatureChecks)
    (object : α) (pubkey : BLSPubkey) (signature : BLSSignature) : Except Err Bool := do
  let signingRoot ← computeSigningRoot object (← builderDomain config)
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signature)

/-- Whether the key of a registration signed it, under the domain of the Builder API.

It fails as the check of a signature under that domain does. -/
def verifyRegistrationSignature (config : Config) (checks : SignatureChecks)
    (signed : SignedValidatorRegistrationV1) : Except Err Bool :=
  verifyBuilderApiSignature config checks signed.message signed.message.pubkey signed.signature

/-- Whether the key of the builder in a bid signed it, under the domain of the Builder API.

It fails as the check of a signature under that domain does. -/
def verifyBuilderBidSignature (config : Config) (checks : SignatureChecks)
    (signed : SignedBuilderBid preset fork) : Except Err Bool :=
  verifyBuilderApiSignature config checks signed.message signed.message.pubkey signed.signature

/-- From Bellatrix to Fulu: whether a signed blinded block carries the signature of its proposer.

The proposer is the one of the slot of the state, as the [builder specification] reads it.

The domain is that of a block, in the current epoch of the state.

It fails when the proposer, its validator, the domain or the signing root fails.

[builder specification]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/builder.md#blinded-block-processing
-/
def verifyBlindedBlockSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBlindedBeaconBlock preset fork) :
    Except TransitionError Bool := do
  let index ← liftAccessor (getBeaconProposerIndex state)
  let proposer ← liftAccessor (getValidator state index)
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_PROPOSER)
  let signingRoot ← liftSsz (computeSigningRoot signed.message domain)
  return checks.verify (packBytes proposer.pubkey) (packBytes signingRoot)
    (packBytes signed.signature)

end EthLib.Consensus
