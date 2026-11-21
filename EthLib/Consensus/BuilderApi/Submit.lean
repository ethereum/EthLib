module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.Transition.StateTransition

/-!
# `Consensus.BuilderApi.Submit`

From Bellatrix to Fulu, the answer of a builder to a signed blinded block.

The proposer sends the blinded block that it signed to the builder whose bid it chose.

The builder answers with a success when the block is valid, and with 400 otherwise.

The first endpoint answers 200 with the payload.

The second answers 202, and the builder publishes the block.

A block is valid when it unblinds with the builder's payload into a full block.

The full block must pass the state transition from the builder's state.

The signature checks are an argument, and the source asks for BLS checks, which the export uses.

The transition checks the signature of the proposer, which the [builder specification] asks for.

The source does not say what a builder answers for a header that is not that of its payload.

Such a block does not unblind, so it is invalid here and gets 400.

[builder specification]: https://github.com/ethereum/builder-specs/blob/ea92eff73ad77c33d3b59a2033ffa02dfae5ee05/specs/bellatrix/builder.md#blinded-block-processing
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base

variable {preset : Preset} {fork : Fork}

/-- The two endpoints that take a signed blinded block.

[`blinded_blocks.yaml`][v1] answers 200 with the payload.

[`blinded_blocks_v2.yaml`][v2] answers 202, and the builder publishes the block itself.

[v1]: https://github.com/ethereum/builder-specs/blob/ea92eff73ad77c33d3b59a2033ffa02dfae5ee05/apis/builder/blinded_blocks.yaml
[v2]: https://github.com/ethereum/builder-specs/blob/ea92eff73ad77c33d3b59a2033ffa02dfae5ee05/apis/builder/blinded_blocks_v2.yaml
-/
inductive SubmitVersion where
  /-- The first endpoint, which answers with the payload. -/
  | v1
  /-- The second endpoint, which publishes the block. -/
  | v2
  deriving DecidableEq, Repr

/-- The status of a success at an endpoint: 200 for the first, 202 for the second. -/
def SubmitVersion.success : SubmitVersion → Nat
  | .v1 => 200
  | .v2 => 202

/-- Whether a signed blinded block is valid for a builder.

It must unblind with the builder's payload into a full block.

That block must pass the state transition from the builder's state, under the given checks. -/
def ValidBlindedBlock (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (range : HasBuilderApi fork) (payload : ExecutionPayload preset fork)
    (signed : SignedBlindedBeaconBlock preset fork) : Prop :=
  ∃ full, signed.unblind range payload = .ok full ∧
    ∃ post, stateTransition config checks engine state full = .ok post

/-- From Bellatrix to Fulu: the status of a request that submits a signed blinded block.

It is the success of the endpoint when the block is valid for the builder, and 400 otherwise. -/
def submitBlindedBlockStatus (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (range : HasBuilderApi fork) (payload : ExecutionPayload preset fork)
    (signed : SignedBlindedBeaconBlock preset fork) (version : SubmitVersion) : Nat :=
  match signed.unblind range payload with
  | .error _ => 400
  | .ok full =>
    match stateTransition config checks engine state full with
    | .ok _ => version.success
    | .error _ => 400

end EthLib.Consensus.BuilderApi
