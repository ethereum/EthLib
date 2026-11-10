module

public import EthLib.Consensus.Containers.BuilderApi
public import EthLib.Consensus.Signing
public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.BuilderApi`

From Bellatrix to Fulu: the Builder API, between a proposer and the builders that sell it a payload.

A validator first registers its fee recipient and its gas limit with a builder.

A builder then bids on a payload by its header, under its own key.

The proposer signs a blinded block, which holds that header in place of the payload.

Only then does the builder reveal the payload, and publish the full block with that signature.

A registration and a bid are signed under the application domain of builders.

That domain reads the genesis fork version and a zero root of the genesis validators.

So a registration keeps its signature across forks.

A blinded block is signed under the proposer domain of its fork, like a full block.

From Gloas the protocol carries the bids of builders, and the Builder API has other messages.

The [signing] rules come from the builder specification.

[signing]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/builder.md#signing
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

end EthLib.Consensus
