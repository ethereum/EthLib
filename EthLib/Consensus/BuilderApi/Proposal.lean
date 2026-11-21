module

public import EthLib.Consensus.Types

/-!
# `Consensus.BuilderApi.Proposal`

From Bellatrix to Fulu, a proposer that uses external builders also builds a block locally.

The [builder specification][validator] gives it four rules for choosing between the two.

- It builds locally when the builders give no bid in time.
- Builders have one second to give a bid, after which the proposer builds locally.
- When the circuit breaker fires, it does not use the builders, and builds locally.
- Once it has signed a blinded block, it must not fall back to a local block.

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

A signed blinded block keeps the builder, since the source forbids the local fallback then.

Otherwise the circuit breaker, a missing bid, or a late bid gives the local payload.

A bid that arrives at the tolerance exactly is in time, and the arrival is in whole milliseconds.

The source triggers the last rule on publishing the blinded block, and signing is the safer trigger.

With the circuit breaker fired after a blinded block is signed, the rule against a local block wins.

The inputs are assumed consistent: a signed blinded block comes from a bid.
-/
def chooseSource (circuitBreaker : Bool) (bidArrival : Option Nat) (signedBlinded : Bool) :
    ProposalSource :=
  if signedBlinded then .builder
  else if circuitBreaker then .local
  else match bidArrival with
    | some arrival => if arrival ≤ BUILDER_PROPOSAL_DELAY_TOLERANCE * 1000 then .builder else .local
    | none => .local

end EthLib.Consensus.BuilderApi
