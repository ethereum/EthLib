module

public import EthLib.Consensus.Types

/-!
# `Consensus.BuilderApi.Proposal`

From Bellatrix to Fulu, a proposer that uses external builders also builds a block locally.

The [builder specification][validator] gives it four rules for choosing between the two.

The circuit breaker fires when the node judges the chain unhealthy.

The source leaves its conditions to the implementation, so it is an input here.

The source does not say when the one second starts, so the arrival of the bid is an input.

It counts from the request for the bid, in milliseconds.

[validator]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/validator.md#relation-to-local-block-building
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

/-- The time that builders have to give a bid, in seconds.

The [builder specification][constants] sets it to one second.

[constants]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/validator.md#constants
-/
def BUILDER_PROPOSAL_DELAY_TOLERANCE : Nat := 1

/-- Where the payload of a proposal comes from. -/
inductive ProposalSource where
  /-- The payload of the bid of an external builder, through a blinded block. -/
  | builder
  /-- The payload that the proposer builds locally. -/
  | local
  deriving DecidableEq, Repr

/-- From Bellatrix to Fulu: where a proposer takes its payload from.

The inputs are whether the circuit breaker fired, and when the bid arrived, if it did.

The arrival is in milliseconds after the request for the bid.

The last input is whether the proposer has already signed a blinded block for the slot.

The inputs are assumed consistent: a signed blinded block comes from a bid.
-/
def chooseSource (circuitBreaker : Bool) (bidArrival : Option Nat) (signedBlinded : Bool) :
    ProposalSource :=
  -- How to avoid slashing: after a signed blinded block, the proposer must not build locally.
  --
  -- The source says this of a published blinded block, and EthLib takes the safer signed one.
  --
  -- This rule comes first, so it wins over a circuit breaker that fires after the signature.
  if signedBlinded then .builder
  -- Liveness failsafe: when the circuit breaker fires, the proposer builds locally.
  else if circuitBreaker then .local
  else match bidArrival with
    -- Builders have the tolerance of one second to give a bid, here in whole milliseconds.
    --
    -- A bid that arrives at the tolerance exactly is in time, else the proposer builds locally.
    | some arrival => if arrival ≤ BUILDER_PROPOSAL_DELAY_TOLERANCE * 1000 then .builder else .local
    -- Without a bid from the builders, the proposer builds locally.
    | none => .local

end EthLib.Consensus.BuilderApi
