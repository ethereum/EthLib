module

public import EthLib.Consensus.Exports.HonestProposer
public import EthLib.Consensus.Exports.HonestValidator
public import EthLib.Consensus.HonestAggregation

/-!
# `Exports.HonestAggregation`

C-ABI exports of the vote of an honest attester and of the aggregates of votes.

A state, attestation data, a vote and a sync committee come as SSZ bytes, at a fork up to Heze.

Two exports build the vote of a validator.

It is an attestation before Electra, and a single attestation from Electra.

One export aggregates the signatures of attestations.

Two exports build an aggregate, of attestations before Electra and of single attestations from it.

One export builds the contribution of a sync subcommittee, from Altair.

A secret key is 32 big-endian bytes, and the configuration of a name holds, with its replacements.

An input that does not decode, an unknown name or a fork without the rule has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz Cryptography.Bls
open EthLib.Exports (Result)

/-- A secret key from its bytes, or code 0. -/
def secretKeyOf (bytes : ByteArray) : Result Signatures.SecretKey :=
  (Signatures.SecretKey.fromBytes bytes).mapError fun _ =>
    (0, "the secret key is not a nonzero scalar below the group order")

/-- The aggregate of the signatures of attestations, as 96 bytes.

The preset and the fork are named in UTF-8, and each attestation comes as SSZ bytes. -/
@[export eth_consensus_get_aggregate_signature]
def getAggregateSignatureExport (name fork : ByteArray) (attestations : Array ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let attestations ← attestations.toList.mapM (decodeInput (Attestation preset fork))
  return packBytes (← runDuty ((getAggregateSignature attestations).mapError .bls))

/-- Before Electra: the attestation of a validator on attestation data, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8. -/
@[export eth_consensus_construct_attestation]
def constructAttestationExport (name fork state replacements data : ByteArray)
    (validatorIndex : UInt64) (secretKey : ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let ⟨before⟩ ← holds (fork < .pectra) s!"no attestation of one validator at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let data ← decodeInput AttestationData data
  let attestation ← runDuty
    (constructAttestation config state before data validatorIndex (← secretKeyOf secretKey))
  (SszType.serialize attestation).mapError fun e => (0, s!"attestation rejected: {reprStr e}")

/-- From Electra: the single attestation of a validator in a committee, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8. -/
@[export eth_consensus_construct_single_attestation]
def constructSingleAttestationExport (name fork state replacements data : ByteArray)
    (committeeIndex validatorIndex : UInt64) (secretKey : ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let ⟨_⟩ ← holds (.pectra ≤ fork) s!"no single attestation at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let data ← decodeInput AttestationData data
  let single ← runDuty (constructSingleAttestation config state data committeeIndex
    validatorIndex (← secretKeyOf secretKey))
  (SszType.serialize single).mapError fun e => (0, s!"attestation rejected: {reprStr e}")

/-- Before Electra: the aggregate of the attestations that vote for attestation data, as SSZ bytes.

The preset and the fork are named in UTF-8, and each attestation comes as SSZ bytes. -/
@[export eth_consensus_construct_aggregate]
def constructAggregateExport (name fork state data : ByteArray) (attestations : Array ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨before⟩ ← holds (fork < .pectra) s!"no aggregate of attestations at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let data ← decodeInput AttestationData data
  let attestations ← attestations.toList.mapM (decodeInput (Attestation preset fork))
  let aggregate ← runDuty (constructAggregate state before data attestations)
  (SszType.serialize aggregate).mapError fun e => (0, s!"aggregate rejected: {reprStr e}")

/-- From Electra: the aggregate of the single attestations of a committee, as SSZ bytes.

The preset and the fork are named in UTF-8, and each single attestation comes as SSZ bytes. -/
@[export eth_consensus_construct_aggregate_of_single_attestations]
def constructAggregateOfSingleAttestationsExport (name fork state data : ByteArray)
    (committeeIndex : UInt64) (singles : Array ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨_⟩ ← holds (.pectra ≤ fork) s!"no aggregate of single attestations at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let data ← decodeInput AttestationData data
  let singles ← singles.toList.mapM (decodeInput SingleAttestation)
  let aggregate ← runDuty (constructAggregateOfSingleAttestations state data committeeIndex singles)
  (SszType.serialize aggregate).mapError fun e => (0, s!"aggregate rejected: {reprStr e}")

/-- From Altair: the contribution of a subcommittee from sync committee messages, as SSZ bytes.

The preset and the fork are named in UTF-8.

The sync committee, the block root and each message come as SSZ bytes. -/
@[export eth_consensus_construct_sync_committee_contribution]
def constructSyncCommitteeContributionExport (name fork state committee blockRoot : ByteArray)
    (subcommitteeIndex : UInt64) (messages : Array ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨_⟩ ← altairOf fork
  let state ← decodeInput (BeaconState preset fork) state
  let committee ← decodeInput (SyncCommittee preset) committee
  let blockRoot ← decodeInput Root blockRoot
  let messages ← messages.toList.mapM (decodeInput SyncCommitteeMessage)
  let contribution ← runDuty (constructSyncCommitteeContribution state committee blockRoot
    subcommitteeIndex messages)
  (SszType.serialize contribution).mapError fun e => (0, s!"contribution rejected: {reprStr e}")

end EthLib.Consensus.Exports
