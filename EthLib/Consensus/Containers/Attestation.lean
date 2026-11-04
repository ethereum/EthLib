module

public import EthLib.Base.Fork
public import EthLib.Consensus.Containers.Misc
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.Containers.Attestation`

Attestations, their indexed form, attester slashings and aggregates, at every fork.

Before Electra an attestation covers one committee.

From Electra one attestation covers several committees of a slot, as [EIP-7549] specifies.

Its bits then run over all those committees, and a bit vector says which committees take part.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The largest number of validators that one attestation covers at a fork.

Before Electra it is the largest size of a committee.

From Electra it is that size times the largest number of committees in a slot. -/
def maxAttesters (preset : Preset) (fork : Fork) : Nat :=
  if .pectra ≤ fork then
    preset.MAX_VALIDATORS_PER_COMMITTEE.toNat * preset.MAX_COMMITTEES_PER_SLOT.toNat
  else preset.MAX_VALIDATORS_PER_COMMITTEE.toNat

/-- An aggregate vote of validators, with one bit for each validator that signed. -/
structure Attestation (preset : Preset) (fork : Fork) where
  /-- One bit for each member of the committees, in committee order, set when it signed. -/
  aggregationBits : Bitlist (maxAttesters preset fork)
  /-- What the validators vote for. -/
  data : AttestationData
  /-- The aggregate signature of the validators whose bit is set. -/
  signature : BLSSignature
  /-- From Electra: one bit for each committee of the slot, set when it takes part. -/
  committeeBits : Since .pectra fork (Bitvector preset.MAX_COMMITTEES_PER_SLOT.toNat)

namespace Attestation

/-- The names of the fields of an attestation at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["aggregation_bits", "data", "signature"] ++ sinceNames .pectra fork ["committee_bits"]

instance {preset : Preset} {fork : Fork} : SszType (Attestation preset fork) :=
  .container (names fork)
    (fun a => (a.aggregationBits, a.data, a.signature, a.committeeBits))
    (fun (aggregationBits, data, signature, committeeBits) =>
      ⟨aggregationBits, data, signature, committeeBits⟩)

end Attestation

/-- An attestation with the indices of the validators that signed, in place of their bits. -/
structure IndexedAttestation (preset : Preset) (fork : Fork) where
  /-- The indices of the validators that signed. -/
  attestingIndices : SszList ValidatorIndex (maxAttesters preset fork)
  /-- What the validators vote for. -/
  data : AttestationData
  /-- The aggregate signature of those validators. -/
  signature : BLSSignature

instance {preset : Preset} {fork : Fork} : SszType (IndexedAttestation preset fork) :=
  .container ["attesting_indices", "data", "signature"]
    (fun a => (a.attestingIndices, a.data, a.signature))
    (fun (attestingIndices, data, signature) => ⟨attestingIndices, data, signature⟩)

/-- Evidence that validators signed two attestations that Casper FFG forbids together. -/
structure AttesterSlashing (preset : Preset) (fork : Fork) where
  /-- The first attestation. -/
  attestation1 : IndexedAttestation preset fork
  /-- The second attestation. -/
  attestation2 : IndexedAttestation preset fork

instance {preset : Preset} {fork : Fork} : SszType (AttesterSlashing preset fork) :=
  .container ["attestation_1", "attestation_2"] (fun s => (s.attestation1, s.attestation2))
    (fun (attestation1, attestation2) => ⟨attestation1, attestation2⟩)

/-- An aggregate that a validator selected as aggregator publishes, with its proof of selection. -/
structure AggregateAndProof (preset : Preset) (fork : Fork) where
  /-- The aggregator. -/
  aggregatorIndex : ValidatorIndex
  /-- The aggregate attestation. -/
  aggregate : Attestation preset fork
  /-- The signature of the slot by the aggregator, which shows that it was selected. -/
  selectionProof : BLSSignature

instance {preset : Preset} {fork : Fork} : SszType (AggregateAndProof preset fork) :=
  .container ["aggregator_index", "aggregate", "selection_proof"]
    (fun a => (a.aggregatorIndex, a.aggregate, a.selectionProof))
    (fun (aggregatorIndex, aggregate, selectionProof) =>
      ⟨aggregatorIndex, aggregate, selectionProof⟩)

/-- An aggregate and its proof, with the signature of the aggregator. -/
structure SignedAggregateAndProof (preset : Preset) (fork : Fork) where
  /-- The aggregate and its proof. -/
  message : AggregateAndProof preset fork
  /-- The signature of the message by the aggregator. -/
  signature : BLSSignature

instance {preset : Preset} {fork : Fork} : SszType (SignedAggregateAndProof preset fork) :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

/-- From Electra: the vote of one validator, as it travels before aggregation. -/
structure SingleAttestation where
  /-- The committee of the validator. -/
  committeeIndex : CommitteeIndex
  /-- The validator. -/
  attesterIndex : ValidatorIndex
  /-- What the validator votes for. -/
  data : AttestationData
  /-- The signature of the validator. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType SingleAttestation :=
  .container ["committee_index", "attester_index", "data", "signature"]
    (fun a => (a.committeeIndex, a.attesterIndex, a.data, a.signature))
    (fun (committeeIndex, attesterIndex, data, signature) =>
      ⟨committeeIndex, attesterIndex, data, signature⟩)

end EthLib.Consensus
