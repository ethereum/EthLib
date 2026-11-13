module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Consensus.BeaconApi.Produce
public import EthLib.Consensus.Exports.Transition
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.BeaconApiProduce`

C-ABI exports of the choice between the local payload and a builder's, in block production.

The consensus value of a block is in Wei, from the state at its slot, before it.

Bid values are in Gwei, and the value of the local payload is in Wei.

The terms of a bid and a bid cross as `dict`s whose keys are their field names in snake case.

An amount at or above 2^64, where the API reads a 64-bit integer, has code 0.

Bytes of a builder configuration that do not decode keep the code of their SSZ error.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz BeaconApi
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- The consensus value of a signed block, in Wei, from the state at its slot. -/
def apiConsensusBlockValueOf (args : String × String × ByteArray × ByteArray × Option PyValue) :
    Result Nat := do
  let (name, fork, state, block, replacements) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let signed ← decodeInput (SignedBeaconBlock preset fork) block
  runTransition (consensusBlockValue config SignatureChecks.acceptAll (.constant true) state
    signed.message)

/-- The consensus value of a signed block, in Wei.

The arguments are the name, the fork, and the SSZ bytes of the state and of the signed block.

The state is the one at the slot of the block, before the block.

Then come the replacements of the configuration, or None.

The block was imported, so no signature is checked, and the execution layer accepts its payload. -/
@[export eth_consensus_api_consensus_block_value]
def apiConsensusBlockValueExport (args : PyValue) : Result PyValue :=
  pyExport apiConsensusBlockValueOf args

derive_py BidTerms
derive_py_laws BidTerms
derive_py CandidateBid
derive_py_laws CandidateBid

/-- From Bellatrix to Fulu, whether the node returns its local payload rather than the builder's. -/
@[export eth_consensus_api_prefer_local_v3]
def apiPreferLocalV3Export (args : PyValue) : Result PyValue :=
  pyExport (fun (localValue, builderValue, boost) =>
    .ok (preferLocalV3 localValue builderValue boost) : Nat × Nat × UInt64 → Result Bool) args

/-- The value of a bid in Gwei, with its execution payment capped and the sum saturated. -/
@[export eth_consensus_api_capped_bid_value]
def apiCappedBidValueExport (args : PyValue) : Result PyValue :=
  pyExport (fun bid => .ok (cappedBidValue bid) : CandidateBid → Result Nat) args

/-- Whether the terms of a bid accept it. -/
@[export eth_consensus_api_bid_accepted]
def apiBidAcceptedExport (args : PyValue) : Result PyValue :=
  pyExport (fun bid => .ok (bidAccepted bid) : CandidateBid → Result Bool) args

/-- From Gloas, the bid that the node commits to, or None for its local payload. -/
@[export eth_consensus_api_select_payload]
def apiSelectPayloadExport (args : PyValue) : Result PyValue :=
  pyExport (fun (localValue, bids) => .ok (selectPayload localValue bids) :
    Nat × List CandidateBid → Result (Option CandidateBid)) args

/-- The terms that a builder configuration gives: those of gossip, then those of its entries. -/
def apiBuilderConfigTermsOf (args : ByteArray × Slot) : Result (BidTerms × List BidTerms) := do
  let (data, slot) := args
  let config ← runSsz "input rejected" (SszType.deserialize BuilderConfig data)
  return (config.gossipTerms, config.entryTerms slot)

/-- From Gloas, the terms that the SSZ bytes of a builder configuration give.

The second argument is the slot of the request.

They are the terms of the bids received on gossip.

Then come those of each entry that serves the slot, in order, without repeated requests. -/
@[export eth_consensus_api_builder_config_terms]
def apiBuilderConfigTermsExport (args : PyValue) : Result PyValue :=
  pyExport apiBuilderConfigTermsOf args

end EthLib.Consensus.Exports
