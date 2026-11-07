module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.HonestValidator

/-!
# `Exports.HonestValidator`

C-ABI exports of the duties of an honest validator.

They take a state as SSZ bytes, and accept forks up to Heze.

One export finds the committee assignment of a validator, and one whether it proposes.

Two find its sync committee assignment and its sync committee subnets, from Altair.

One export signs the object of a duty, named as the duty, with a secret key of 32 big-endian bytes.

The configuration of a name holds, with the replacements that a JSON object gives.

An input that does not decode, an unknown name or an unknown duty has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz Cryptography.Bls
open EthLib.Exports (Result)

/-- The result of a duty, with the code of its error. -/
def runDuty {α : Type} (result : Except ValidatorDutyError α) : Result α :=
  result.mapError fun e => (e.code, s!"validator duty failed with code {e.code}")

/-- The proof that a fork is at least Altair, or code 0. -/
def altairOf (fork : Fork) : Result (PLift (.altair ≤ fork)) :=
  if altair : .altair ≤ fork then return ⟨altair⟩
  else throw (0, s!"no sync committee at {fork.name}")

/-- The committee assignment of a validator in an epoch, as JSON.

The preset, the configuration and the fork are named in UTF-8.

It is `null` without an assignment, or the committee, its index and its slot. -/
@[export eth_consensus_get_committee_assignment]
def getCommitteeAssignmentExport (name fork state replacements : ByteArray) (epoch : UInt64)
    (validatorIndex : UInt64) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let _ ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) state
  match ← runDuty (getCommitteeAssignment state epoch validatorIndex) with
  | none => return jsonBytes Json.null
  | some (committee, index, slot) =>
    return jsonBytes (Json.mkObj [("committee", toJson (committee.toList.map UInt64.toNat)),
      ("index", toJson index.toNat), ("slot", toJson slot.toNat)])

/-- Whether a validator proposes the block of the slot of a state.

The preset, the configuration and the fork are named in UTF-8. -/
@[export eth_consensus_is_proposer]
def isProposerExport (name fork state replacements : ByteArray) (validatorIndex : UInt64) :
    Result Bool := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let _ ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) state
  runDuty (isProposer state validatorIndex)

/-- From Altair: whether a validator serves on the sync committee of the period of an epoch.

The preset, the configuration and the fork are named in UTF-8. -/
@[export eth_consensus_is_assigned_to_sync_committee]
def isAssignedToSyncCommitteeExport (name fork state replacements : ByteArray) (epoch : UInt64)
    (validatorIndex : UInt64) : Result Bool := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let _ ← configWith name replacements
  let ⟨altair⟩ ← altairOf fork
  let state ← decodeInput (BeaconState preset fork) state
  runDuty (isAssignedToSyncCommittee state altair epoch validatorIndex)

/-- From Altair: the sync committee subnets of a validator for the next slot, as a JSON list.

The preset, the configuration and the fork are named in UTF-8. -/
@[export eth_consensus_compute_subnets_for_sync_committee]
def computeSubnetsForSyncCommitteeExport (name fork state replacements : ByteArray)
    (validatorIndex : UInt64) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let _ ← configWith name replacements
  let ⟨altair⟩ ← altairOf fork
  let state ← decodeInput (BeaconState preset fork) state
  let subnets ← runDuty (computeSubnetsForSyncCommittee state altair validatorIndex)
  return jsonBytes (toJson (subnets.map UInt64.toNat))

/-- The signature of the object of a duty, by a secret key of 32 big-endian bytes.

The preset, the configuration, the fork and the duty are named in UTF-8.

The object comes as SSZ bytes, by duty:

- `randao` and `block`: a block.
- `attestation`: attestation data.
- `slot`: a slot.
- `aggregate_and_proof`: an aggregate and proof.
- `sync_committee_message`: a block root.
- `sync_committee_selection_proof`: sync aggregator selection data.
- `contribution_and_proof`: a contribution and proof.

The three duties of the sync committee need Altair; before it they have code 0. -/
@[export eth_consensus_get_validator_signature]
def getValidatorSignatureExport (name fork state replacements duty object secretKey : ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let key ← (Signatures.SecretKey.fromBytes secretKey).mapError fun _ =>
    (0, "the secret key is not a nonzero scalar below the group order")
  let signature ← match ← nameOf duty with
    | "randao" => do
      runDuty (getEpochSignature config state (← decodeInput (BeaconBlock preset fork) object) key)
    | "block" => do
      runDuty (getBlockSignature config state (← decodeInput (BeaconBlock preset fork) object) key)
    | "attestation" => do
      runDuty (getAttestationSignature config state (← decodeInput AttestationData object) key)
    | "slot" => do
      runDuty (getSlotSignature config state (← decodeInput UInt64 object) key)
    | "aggregate_and_proof" => do
      runDuty (getAggregateAndProofSignature config state
        (← decodeInput (AggregateAndProof preset fork) object) key)
    | "sync_committee_message" => do
      let ⟨_⟩ ← altairOf fork
      let message ← runDuty (getSyncCommitteeMessage config state
        (← decodeInput Root object) 0 key)
      pure message.signature
    | "sync_committee_selection_proof" => do
      let ⟨_⟩ ← altairOf fork
      let data ← decodeInput SyncAggregatorSelectionData object
      runDuty (getSyncCommitteeSelectionProof config state data.slot data.subcommitteeIndex key)
    | "contribution_and_proof" => do
      let ⟨_⟩ ← altairOf fork
      runDuty (getContributionAndProofSignature config state
        (← decodeInput (ContributionAndProof preset) object) key)
    | other => throw (0, s!"unknown duty {other}")
  return packBytes signature

end EthLib.Consensus.Exports
