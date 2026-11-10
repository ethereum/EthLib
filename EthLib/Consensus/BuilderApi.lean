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

A proposer signs the authentication of its requests under a second application domain.

That domain also reads the genesis fork version and a zero root, so one check serves both domains.

The [signing] rules come from the builder specification.

Its [Gloas signing] rules add the second domain.

A proposer counts a bid's execution payment up to its own cap, as the [Gloas valuation] rules say.

[signing]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/builder.md#signing
[Gloas signing]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md#signing
[Gloas valuation]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md#max_execution_payment
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

/-- From Gloas: the application domain type of the authentication of a request to a builder.

It sets the bit of the application mask, so no domain type of a fork equals it. -/
def DOMAIN_BUILDER_REQUEST_AUTH : DomainType := #v[0x0B, 0x00, 0x00, 0x01]

/-- The domain of a type of messages of the Builder API on a chain.

By default the type is that of registrations and bids.

It is the domain of its type at the genesis fork version, with a zero root of the validators.

The builder specification passes no fork version and no root, at every fork. -/
def builderDomain (config : Config) (domainType : DomainType := DOMAIN_APPLICATION_BUILDER) :
    Except Err Domain :=
  computeDomain config domainType

/-- Whether a key signed an object under a domain of the Builder API.

By default the domain is that of registrations and bids.

It fails when the root of the object or of the domain fails. -/
def verifyBuilderApiSignature {α : Type} [SszType α] (config : Config) (checks : SignatureChecks)
    (object : α) (pubkey : BLSPubkey) (signature : BLSSignature)
    (domainType : DomainType := DOMAIN_APPLICATION_BUILDER) : Except Err Bool := do
  let signingRoot ← computeSigningRoot object (← builderDomain config domainType)
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signature)

/-- From Gloas: whether a proposer key signed the authentication of a request.

The request names that key outside the signed message.

This checks the signature alone, and the builder also checks the agreed data and the slot.

The signature covers the data and the slot, not the preferences that a request may carry. -/
def verifyBuilderRequestAuthSignature (config : Config) (checks : SignatureChecks)
    (signed : SignedBuilderRequestAuth) (pubkey : BLSPubkey) : Except Err Bool :=
  verifyBuilderApiSignature config checks signed.message pubkey signed.signature
    DOMAIN_BUILDER_REQUEST_AUTH

/-- From Gloas: a bid's value to the proposer, in Gwei, with its execution payment capped.

The sum is a natural number, so two 64-bit amounts add without wrapping. -/
def builderBidValue (value executionPayment : Gwei) (preferences : BuilderPreferences) : Nat :=
  value.toNat + min executionPayment.toNat preferences.maxExecutionPayment.toNat

/-- From Gloas: a bid's value to the proposer under its preferences for the builder, in Gwei. -/
def ExecutionPayloadBid.proposerValue (bid : ExecutionPayloadBid preset fork)
    (preferences : BuilderPreferences) : Nat :=
  builderBidValue bid.value bid.executionPayment preferences

/-- Whether the key of a registration signed it, under the domain of registrations and bids.

It fails as the check of a signature under that domain does. -/
def verifyRegistrationSignature (config : Config) (checks : SignatureChecks)
    (signed : SignedValidatorRegistrationV1) : Except Err Bool :=
  verifyBuilderApiSignature config checks signed.message signed.message.pubkey signed.signature

/-- Whether the key of the builder in a bid signed it, under the domain of registrations and bids.

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
