module

public import EthLib.Base.Denominations
public import EthLib.Consensus.BeaconApi.Rewards
public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.Builders
public import EthLib.Consensus.Containers.BuilderConfig

/-!
# `Consensus.BeaconApi.Produce`

The answers of the Beacon API that produce a block for a validator.

A response of the [v3] and [v4] block production endpoints carries the value of the block.

Its [consensus block value] is what the proposer earns from the block, in Wei.

The node also chooses between its local payload and the payload of a builder.

Through Fulu, the [v3] rule compares the two values with a factor from the validator.

From Gloas, the [v4] request carries a [builder configuration] with the terms of each bid.

A bid's terms may name the builders they accept, and they set a floor, a cap and a factor.

[v3]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/block.v3.yaml
[v4]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/block.v4.yaml
[builder configuration]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/gloas/builder_entry.yaml
[consensus block value]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/beacon-node-oapi.yaml#L615-L624
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- What the proposer of a block earns from it, in Wei, from the state of the slot of the block. -/
def consensusBlockValue (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError Nat := do
  -- The source: the sum of the proposer rewards from attestations, sync committees and slashings.
  --
  -- That is the total of the block rewards of the block, in Gwei.
  --
  -- The source counts it in Wei, at 10^9 Wei per Gwei.
  return (← blockRewards config checks engine state block).total.toNat * GWEI_TO_WEI

/-- From Bellatrix to Fulu: whether the node returns its local payload rather than the builder's.

The two values are in Wei, and the factor is in percent of the builder's value. -/
def preferLocalV3 (localValue builderValue : Nat) (boost : UInt64) : Bool :=
  -- The source: the local payload when `local >= boost * floor(builder / 100)`.
  --
  -- So the builder's value is first rounded down to a multiple of 100 Wei.
  boost.toNat * (builderValue / 100) ≤ localValue

/-- From Gloas: a bid that competes with the local payload, with the terms that apply to it. -/
structure CandidateBid where
  /-- The key of the builder that signed the bid. -/
  signer : BLSPubkey
  /-- What the builder pays the proposer on the beacon chain, in Gwei. -/
  value : Gwei
  /-- What the builder pays the proposer on the execution layer, in Gwei. -/
  executionPayment : Gwei
  /-- The terms that apply to the bid. -/
  terms : BidTerms
  deriving DecidableEq

/-- The candidate that a signed bid gives under some terms.

Its signer is the key of the builder that the bid names, from the registry of the state.

So the signature of the bid must have been checked first.

It fails when the registry has no such builder. -/
def CandidateBid.ofBid (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) (terms : BidTerms) :
    Except AccessorError CandidateBid := do
  -- The builder that the bid names, from the registry of the state.
  let builder ← getBuilder state gloas signed.message.builderIndex
  -- Its key is the signer of the bid.
  return ⟨builder.pubkey, signed.message.value, signed.message.executionPayment, terms⟩

/-- The value of a bid, in Gwei: its value plus its execution payment, counted up to its cap. -/
def cappedBidValue (bid : CandidateBid) : Nat :=
  -- The source: value + min(execution payment, max execution payment).
  --
  -- The sum saturates at 2^64 - 1.
  min (builderBidValue bid.value bid.executionPayment ⟨bid.terms.maxExecutionPayment⟩)
    UINT64_MAX.toNat

/-- Whether the terms of a bid accept it. -/
def bidAccepted (bid : CandidateBid) : Bool :=
  -- The source: an empty list of keys accepts any builder.
  --
  -- Otherwise a bid that one of them did not sign must not be accepted.
  (bid.terms.builderPubkeys.isEmpty || bid.terms.builderPubkeys.contains bid.signer) &&
    -- The source: a bid whose counted value is below the minimum bid must be rejected.
    bid.terms.minBid.toNat ≤ cappedBidValue bid

/-- The weight of a bid: its value times its factor, in hundredths of a Gwei. -/
def bidWeight (bid : CandidateBid) : Nat :=
  -- The source: boost factor times the counted value of the bid, without overflow.
  bid.terms.builderBoostFactor.toNat * cappedBidValue bid

/-- The bid of largest weight in a list, the first one on a tie, or none for no bid. -/
def heaviestBid : List CandidateBid → Option CandidateBid
  | [] => none
  | bid :: rest =>
    match heaviestBid rest with
    | none => some bid
    -- The source compares bids by weight and does not say which of two equal ones competes.
    --
    -- EthLib's choice: the first one.
    | some other => if bidWeight other ≤ bidWeight bid then some bid else some other

/-- From Gloas: the bid that the node commits to, or none for its local payload.

The local value is in Wei, the value of the local payload that the execution layer gives. -/
def selectPayload (localValue : Nat) (bids : List CandidateBid) : Option CandidateBid :=
  -- The source: the bids that their terms accept, and the heaviest of them.
  (heaviestBid (bids.filter bidAccepted)).filter fun bid =>
    -- The source: it competes with the local value weighted by 100, and the local build wins a tie.
    --
    -- Both sides are in hundredths of a Wei, so the bid must weigh strictly more.
    100 * localValue < bidWeight bid * GWEI_TO_WEI

end EthLib.Consensus.BeaconApi
