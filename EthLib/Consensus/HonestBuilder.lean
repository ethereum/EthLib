module

public import EthLib.Consensus.Transition.Payload

/-!
# `Consensus.HonestBuilder`

From Gloas: the signatures that an honest builder puts on its bid and on its envelope.

A builder signs a bid under the builder domain of the epoch of the bid's slot.

It signs an envelope under the builder domain of the current epoch of the state.

The builder also chooses the contents of the bid and of the envelope, and gossips both.

Those steps read the fork choice and the network, so they are not specified here.

[EIP-7732] describes the honest builder.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#honest-validator-and-builder-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork}

/-- An error of a builder that signs a message. -/
inductive BuilderSigningError where
  /-- The domain or the root of the message has no value. -/
  | root (error : TransitionError)
  /-- The BLS signature fails. -/
  | bls (error : BlsError)

/-- The signature of a bid by a builder with a secret key. -/
def getExecutionPayloadBidSignature (config : Config) (state : BeaconState preset fork)
    (bid : ExecutionPayloadBid preset fork) (key : Signatures.SecretKey) :
    Except BuilderSigningError BLSSignature := do
  let root ← (builderSigningRoot config state bid
    (some (computeEpochAtSlot preset bid.slot))).mapError .root
  (Signatures.sign key (packBytes root)).mapError .bls

/-- The signature of an envelope by a builder with a secret key. -/
def getExecutionPayloadEnvelopeSignature (config : Config) (state : BeaconState preset fork)
    (envelope : ExecutionPayloadEnvelope preset fork) (key : Signatures.SecretKey) :
    Except BuilderSigningError BLSSignature := do
  let root ← (builderSigningRoot config state envelope
    (some (computeEpochAtSlot preset state.slot))).mapError .root
  (Signatures.sign key (packBytes root)).mapError .bls

end EthLib.Consensus
