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

The source sums the proposer rewards "from attestations, sync committees and slashings".

So it is the total of the block rewards of the block, at 10^9 Wei per Gwei.

The node also chooses between its local payload and the payload of a builder.

Through Fulu, the [v3] rule compares the two values with a factor from the validator.

From Gloas, the [v4] request carries a [builder configuration] with the terms of each bid.

A bid's terms may name the builders they accept, and they set a floor, a cap and a factor.

Each accepted bid is weighted by its factor, and the local payload is weighted by 100.

The local payload wins a tie.

[v3]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/block.v3.yaml
[v4]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/block.v4.yaml
[builder configuration]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/gloas/builder_entry.yaml
[consensus block value]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/beacon-node-oapi.yaml#L615-L624
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- What the proposer of a block earns from it, in Wei, from the state of the slot of the block.

It is the total of the block rewards, at 10^9 Wei per Gwei. -/
def consensusBlockValue (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError Nat := do
  return (← blockRewards config checks engine state block).total.toNat * GWEI_TO_WEI

/-- From Bellatrix to Fulu: whether the node returns its local payload rather than the builder's.

The two values are in Wei, and the factor is in percent of the builder's value.

The builder's value is first rounded down to a multiple of 100 Wei. -/
def preferLocalV3 (localValue builderValue : Nat) (boost : UInt64) : Bool :=
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
  let builder ← getBuilder state gloas signed.message.builderIndex
  return ⟨builder.pubkey, signed.message.value, signed.message.executionPayment, terms⟩

/-- The value of a bid, in Gwei: its value plus its execution payment, counted up to its cap.

The sum saturates at the largest 64-bit integer. -/
def cappedBidValue (bid : CandidateBid) : Nat :=
  min (builderBidValue bid.value bid.executionPayment ⟨bid.terms.maxExecutionPayment⟩)
    UINT64_MAX.toNat

/-- Whether the terms of a bid accept it.

The signer must be among the keys of the terms, when they name some.

The value of the bid must reach the smallest value of the terms. -/
def bidAccepted (bid : CandidateBid) : Bool :=
  (bid.terms.builderPubkeys.isEmpty || bid.terms.builderPubkeys.contains bid.signer) &&
    bid.terms.minBid.toNat ≤ cappedBidValue bid

/-- The weight of a bid: its value times its factor, in hundredths of a Gwei. -/
def bidWeight (bid : CandidateBid) : Nat :=
  bid.terms.builderBoostFactor.toNat * cappedBidValue bid

/-- The bid of largest weight in a list, the first one on a tie, or none for no bid. -/
def heaviestBid : List CandidateBid → Option CandidateBid
  | [] => none
  | bid :: rest =>
    match heaviestBid rest with
    | none => some bid
    | some other => if bidWeight other ≤ bidWeight bid then some bid else some other

/-- From Gloas: the bid that the node commits to, or none for its local payload.

The local value is in Wei, the value of the local payload that the execution layer gives.

The node drops the bids that their terms refuse, and keeps the first one of largest weight.

That bid wins only when its weight is above 100 times the local value.

Both sides are in hundredths of a Wei, and the bid must weigh strictly more.

So the local payload wins a tie. -/
def selectPayload (localValue : Nat) (bids : List CandidateBid) : Option CandidateBid :=
  (heaviestBid (bids.filter bidAccepted)).filter fun bid =>
    100 * localValue < bidWeight bid * GWEI_TO_WEI

end EthLib.Consensus.BeaconApi
