module

public import EthLib.Consensus.Builders
public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.Transition.Payload`

From Gloas: the signature checks of the bid and of the envelope of an execution payload.

A builder bids for the payload of a slot, and later reveals the payload in an envelope.

Both messages carry a signature under the builder domain, in the current epoch of the state.

A bid is signed by its builder.

An envelope is signed by its builder, or by the proposer of the latest block for a self-build.

The signature checks are an argument, as for the other steps of the transition.

A builder or proposer index outside its registry is an error.

[EIP-7732] adds the bid, the envelope and the builder domain.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-- The root that a builder signs for a message, under the builder domain of an epoch.

The epoch is by default the current epoch of the state. -/
def builderSigningRoot {α : Type} [Serialization.Ssz.SszType α] (config : Config)
    (state : BeaconState preset fork) (message : α) (epoch : Option Epoch := none) :
    Except TransitionError Root := do
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_BUILDER epoch)
  liftSsz (computeSigningRoot message domain)

/-- Whether a signed bid carries the signature of its builder, in the current epoch. -/
def verifyExecutionPayloadBidSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) : Except TransitionError Bool := do
  let builder ← liftAccessor (getBuilder state gloas signed.message.builderIndex)
  let signingRoot ← builderSigningRoot config state signed.message
  return checks.verify (packBytes builder.pubkey) (packBytes signingRoot)
    (packBytes signed.signature)

/-- The key that signs an envelope.

It is the key of the builder, or for a self-build the key of the proposer of the latest block. -/
def envelopeSignerKey (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (builderIndex : BuilderIndex) : Except TransitionError BLSPubkey :=
  if builderIndex = BUILDER_INDEX_SELF_BUILD then
    return (← liftAccessor (getValidator state state.latestBlockHeader.proposerIndex)).pubkey
  else return (← liftAccessor (getBuilder state gloas builderIndex)).pubkey

/-- Whether a signed envelope carries the signature of its signer, in the current epoch. -/
def verifyExecutionPayloadEnvelopeSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Except TransitionError Bool := do
  let pubkey ← envelopeSignerKey state gloas signed.message.builderIndex
  let signingRoot ← builderSigningRoot config state signed.message
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature)

end EthLib.Consensus
