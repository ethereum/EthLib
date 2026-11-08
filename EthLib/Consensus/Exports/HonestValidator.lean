module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.HonestValidator

/-!
# `Exports.HonestValidator`

C-ABI exports of the duties of an honest validator.

They take a state as SSZ bytes, and accept forks up to Heze.

One export finds the committee assignment of a validator, and one whether it proposes.

Two find its sync committee assignment and its sync committee subnets, from Altair.

Two find the slot of its payload timeliness committee and the slots it will propose, from Gloas.

One export signs the object of a duty, named as the duty, with a secret key of 32 big-endian bytes.

The configuration of a name holds, with the replacements that a `dict` gives.

The exports take the tuple of their arguments as typed Python values.

An input that does not decode, an unknown name or an unknown duty has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz Cryptography.Bls
open EthLib.Exports (Result PyValue pyExport)

/-- The result of a duty, with the code of its error. -/
def runDuty {α : Type} (result : Except ValidatorDutyError α) : Result α :=
  result.mapError fun e => (e.code, s!"validator duty failed with code {e.code}")

/-- The proof that a fork is at least Altair, or code 0. -/
def altairOf (fork : Fork) : Result (PLift (.altair ≤ fork)) :=
  if altair : .altair ≤ fork then return ⟨altair⟩
  else throw (0, s!"no sync committee at {fork.name}")

/-- The proof that a fork is at least Gloas, or code 0. -/
def gloasOf (fork : Fork) : Result (PLift (.glamsterdam ≤ fork)) :=
  if gloas : .glamsterdam ≤ fork then return ⟨gloas⟩
  else throw (0, s!"no payload timeliness committee at {fork.name}")

/-- The committee assignment of a validator in an epoch, if it has one. -/
def getCommitteeAssignmentOf
    (args : String × String × ByteArray × Option PyValue × UInt64 × UInt64) :
    Result (Option (List UInt64 × UInt64 × UInt64)) := do
  let (name, fork, state, replacements, epoch, validatorIndex) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let _ ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let assignment ← runDuty (getCommitteeAssignment state epoch validatorIndex)
  return assignment.map fun (committee, index, slot) => (committee.toList, index, slot)

/-- The committee assignment of a validator in an epoch, if it has one.

The preset, the configuration and the fork are named by `str`.

It is `None` without an assignment, or the tuple of the committee, its index and its slot. -/
@[export eth_consensus_get_committee_assignment]
def getCommitteeAssignmentExport (args : PyValue) : Result PyValue :=
  pyExport getCommitteeAssignmentOf args

/-- Whether a validator proposes the block of the slot of a state. -/
def isProposerOf (args : String × String × ByteArray × Option PyValue × UInt64) : Result Bool := do
  let (name, fork, state, replacements, validatorIndex) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let _ ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  runDuty (isProposer state validatorIndex)

/-- Whether a validator proposes the block of the slot of a state.

The preset, the configuration and the fork are named by `str`. -/
@[export eth_consensus_is_proposer]
def isProposerExport (args : PyValue) : Result PyValue := pyExport isProposerOf args

/-- From Altair: whether a validator serves on the sync committee of the period of an epoch. -/
def isAssignedToSyncCommitteeOf
    (args : String × String × ByteArray × Option PyValue × UInt64 × UInt64) :
    Result Bool := do
  let (name, fork, state, replacements, epoch, validatorIndex) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let _ ← configWithValue name replacements
  let ⟨altair⟩ ← altairOf fork
  let state ← decodeInput (BeaconState preset fork) state
  runDuty (isAssignedToSyncCommittee state altair epoch validatorIndex)

/-- From Altair: whether a validator serves on the sync committee of the period of an epoch.

The preset, the configuration and the fork are named by `str`. -/
@[export eth_consensus_is_assigned_to_sync_committee]
def isAssignedToSyncCommitteeExport (args : PyValue) : Result PyValue :=
  pyExport isAssignedToSyncCommitteeOf args

/-- From Altair: the sync committee subnets of a validator for the next slot, as a list. -/
def computeSubnetsForSyncCommitteeOf
    (args : String × String × ByteArray × Option PyValue × UInt64) :
    Result (List UInt64) := do
  let (name, fork, state, replacements, validatorIndex) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let _ ← configWithValue name replacements
  let ⟨altair⟩ ← altairOf fork
  let state ← decodeInput (BeaconState preset fork) state
  runDuty (computeSubnetsForSyncCommittee state altair validatorIndex)

/-- From Altair: the sync committee subnets of a validator for the next slot, as a list.

The preset, the configuration and the fork are named by `str`. -/
@[export eth_consensus_compute_subnets_for_sync_committee]
def computeSubnetsForSyncCommitteeExport (args : PyValue) : Result PyValue :=
  pyExport computeSubnetsForSyncCommitteeOf args

/-- The signature of the object of a duty, by a secret key of 32 big-endian bytes. -/
def getValidatorSignatureOf
    (args : String × String × ByteArray × Option PyValue × String × ByteArray × ByteArray) :
    Result ByteArray := do
  let (name, fork, state, replacements, duty, object, secretKey) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let key ← (Signatures.SecretKey.fromBytes secretKey).mapError fun _ =>
    (0, "the secret key is not a nonzero scalar below the group order")
  let signature ← match duty with
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
    | "payload_attestation_message" => do
      let ⟨_⟩ ← gloasOf fork
      runDuty (getPayloadAttestationMessageSignature config state
        (← decodeInput PayloadAttestationMessage object) key)
    | "proposer_preferences" => do
      runDuty (getProposerPreferencesSignature config state
        (← decodeInput ProposerPreferences object) key)
    | other => throw (0, s!"unknown duty {other}")
  return packBytes signature

/-- The signature of the object of a duty, by a secret key of 32 big-endian bytes.

The preset, the configuration, the fork and the duty are named by `str`.

The object comes as SSZ bytes, by duty:

- `randao` and `block`: a block.
- `attestation`: attestation data.
- `slot`: a slot.
- `aggregate_and_proof`: an aggregate and proof.
- `sync_committee_message`: a block root.
- `sync_committee_selection_proof`: sync aggregator selection data.
- `contribution_and_proof`: a contribution and proof.
- `payload_attestation_message`: a payload attestation message, whose data is signed.
- `proposer_preferences`: the preferences of a proposer.

The three duties of the sync committee need Altair; before it they have code 0.

The payload attestation message needs Gloas; before it, it has code 0.

The preferences of a proposer take a state of any fork.

Their domain reads only the root of the genesis validators of the state.

So a state of the epoch before Gloas can sign them for the first epoch of Gloas. -/
@[export eth_consensus_get_validator_signature]
def getValidatorSignatureExport (args : PyValue) : Result PyValue :=
  pyExport getValidatorSignatureOf args

/-- From Gloas: the slot of an epoch whose payload timeliness committee holds a validator. -/
def getPtcAssignmentOf
    (args : String × String × ByteArray × Option PyValue × UInt64 × UInt64) :
    Result (Option UInt64) := do
  let (name, fork, state, replacements, epoch, validatorIndex) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨gloas⟩ ← gloasOf fork
  let state ← decodeInput (BeaconState preset fork) state
  runDuty (getPtcAssignment config state gloas epoch validatorIndex)

/-- From Gloas: the slot of an epoch whose payload timeliness committee holds a validator.

The preset, the configuration and the fork are named by `str`.

It is `None` without an assignment, or the slot. -/
@[export eth_consensus_get_ptc_assignment]
def getPtcAssignmentExport (args : PyValue) : Result PyValue := pyExport getPtcAssignmentOf args

/-- From Gloas: the slots after the slot of a state that a validator proposes, as a list. -/
def getUpcomingProposalSlotsOf
    (args : String × String × ByteArray × Option PyValue × UInt64) :
    Result (List UInt64) := do
  let (name, fork, state, replacements, validatorIndex) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let _ ← configWithValue name replacements
  let ⟨gloas⟩ ← gloasOf fork
  let state ← decodeInput (BeaconState preset fork) state
  runDuty (getUpcomingProposalSlots state gloas validatorIndex)

/-- From Gloas: the slots after the slot of a state that a validator proposes, as a list.

The preset, the configuration and the fork are named by `str`. -/
@[export eth_consensus_get_upcoming_proposal_slots]
def getUpcomingProposalSlotsExport (args : PyValue) : Result PyValue :=
  pyExport getUpcomingProposalSlotsOf args

end EthLib.Consensus.Exports
