module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.HonestProposer

/-!
# `Exports.HonestProposer`

C-ABI exports of what an honest proposer computes for its block.

A state, a block and an attestation come as SSZ bytes, the requests as the lists of EIP-7685.

The exports that take a state take the tuple of their arguments as typed Python values.

In those, the preset, the configuration and the fork are named by `str`, at a fork up to Heze.

A configuration replacement comes as a `dict`.

The other exports take the preset and the fork named in UTF-8.

An input that does not decode, an unknown name or a fork without the rule has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz Cryptography.Bls
open EthLib.Exports (Result PyValue pyExport)

/-- The result of a step of a proposer, with the code of its error. -/
def runProposer {α : Type} (result : Except ProposerError α) : Result α :=
  result.mapError fun e => (e.code, s!"proposer step failed with code {e.code}")

/-- The proof of a condition on the fork, or code 0 with a message. -/
def holds (condition : Prop) [Decidable condition] (message : String) :
    Result (PLift condition) :=
  if proof : condition then return ⟨proof⟩ else throw (0, message)

/-- Before Heze: the Eth1 vote of a proposer on a state, as the SSZ bytes of the Eth1 data. -/
def getEth1VoteOf
    (args : String × String × ByteArray × Option PyValue × List (UInt64 × ByteArray)) :
    Result ByteArray := do
  let (name, fork, state, replacements, chain) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨before⟩ ← holds (fork < .hegota) s!"no Eth1 vote at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let blocks ← chain.mapM fun (timestamp, data) => return (timestamp, ← decodeInput Eth1Data data)
  let vote ← runProposer (getEth1Vote config state before Prod.fst Prod.snd blocks)
  (SszType.serialize vote).mapError fun e => (0, s!"vote rejected: {reprStr e}")

/-- Before Heze: the Eth1 vote of a proposer on a state, as the SSZ bytes of the Eth1 data.

Each block of the Eth1 chain is its timestamp and its Eth1 data, by increasing height. -/
@[export eth_consensus_get_eth1_vote]
def getEth1VoteExport (args : PyValue) : Result PyValue := pyExport getEth1VoteOf args

/-- In Electra: the number of deposits of the deposit contract that a proposer includes. -/
def getEth1PendingDepositCountOf (args : String × String × ByteArray) : Result UInt64 := do
  let (name, fork, state) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let ⟨electra⟩ ← holds (.pectra ≤ fork ∧ fork < .fusaka)
    s!"no pending deposit count at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  return getEth1PendingDepositCount state electra

/-- In Electra: the number of deposits of the deposit contract that a proposer includes. -/
@[export eth_consensus_get_eth1_pending_deposit_count]
def getEth1PendingDepositCountExport (args : PyValue) : Result PyValue :=
  pyExport getEth1PendingDepositCountOf args

/-- The root of the state after a block, to set as its state root, as 32 bytes. -/
def computeNewStateRootOf
    (args : String × String × ByteArray × ByteArray × Option PyValue × Bool) :
    Result ByteArray := do
  let (name, fork, state, block, replacements, verify) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset fork) state
  let block ← decodeInput (BeaconBlock preset fork) block
  let root ← runProposer (computeNewStateRoot config checks (.constant true) state block)
  return ⟨root.toArray⟩

/-- The root of the state after a block, to set as its state root, as 32 bytes.

The signature checks of the operations run unless the last argument is false.

The execution layer accepts every payload, as in the vectors. -/
@[export eth_consensus_compute_new_state_root]
def computeNewStateRootExport (args : PyValue) : Result PyValue :=
  pyExport computeNewStateRootOf args

/-- From Electra: the attestation on chain from network aggregates, as SSZ bytes. -/
@[export eth_consensus_compute_on_chain_aggregate]
def computeOnChainAggregateExport (name fork : ByteArray) (aggregates : Array ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨electra⟩ ← holds (.pectra ≤ fork) s!"no on-chain aggregate at {fork.name}"
  let aggregates ← aggregates.toList.mapM (decodeInput (Attestation preset fork))
  let attestation ← runProposer (computeOnChainAggregate electra aggregates)
  (SszType.serialize attestation).mapError fun e => (0, s!"attestation rejected: {reprStr e}")

/-- From Altair: the sync aggregate of a block from the contributions of subcommittees.

It comes as SSZ bytes, and so does each contribution. -/
@[export eth_consensus_process_sync_committee_contributions]
def processSyncCommitteeContributionsExport (name fork : ByteArray)
    (contributions : Array ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨_⟩ ← holds (.altair ≤ fork) s!"no sync aggregate at {fork.name}"
  let contributions ← contributions.toList.mapM (decodeInput (SyncCommitteeContribution preset))
  let aggregate ← runProposer (processSyncCommitteeContributions contributions)
  (SszType.serialize aggregate).mapError fun e => (0, s!"sync aggregate rejected: {reprStr e}")

/-- From Electra: the requests of an execution block, as SSZ bytes.

They come from the list that the execution layer gives, one typed list per entry. -/
@[export eth_consensus_get_execution_requests]
def getExecutionRequestsExport (name fork : ByteArray) (list : Array ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  unless .pectra ≤ fork do throw (0, s!"no execution requests at {fork.name}")
  let requests ← runProposer (getExecutionRequests (preset := preset) (fork := fork) list.toList)
  (SszType.serialize requests).mapError fun e => (0, s!"requests rejected: {reprStr e}")

/-- From Fulu: the number of custody groups of a node, from the indices of its validators. -/
def getValidatorsCustodyRequirementOf
    (args : String × String × ByteArray × Option PyValue × List UInt64) :
    Result UInt64 := do
  let (name, fork, state, replacements, indices) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  unless .fusaka ≤ fork do throw (0, s!"no validator custody at {fork.name}")
  let state ← decodeInput (BeaconState preset fork) state
  runProposer (getValidatorsCustodyRequirement config state indices)

/-- From Fulu: the number of custody groups of a node, from the indices of its validators.

The arguments are the name of the preset and the configuration, the fork and the state.

Then come replacements of values of the configuration, and the list of the indices. -/
@[export eth_consensus_get_validators_custody_requirement]
def getValidatorsCustodyRequirementExport (args : PyValue) :
    Result PyValue :=
  pyExport getValidatorsCustodyRequirementOf args

end EthLib.Consensus.Exports
