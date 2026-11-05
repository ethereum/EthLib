module

public import EthLib.Consensus.Containers.Misc
public import EthLib.Networking.Enr.Consensus

/-!
# `Consensus.Containers.SyncCommittee`

From Altair: the sync committee and the messages of its members.

A sync committee is a set of validators that sign the head block in each slot of a period.

A block carries the aggregate of their signatures.

The members gossip in subnets, and an aggregator of each subnet combines their messages.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The members of a sync committee, with the aggregate of their keys. -/
structure SyncCommittee (preset : Preset) where
  /-- The keys of the members, in committee order. -/
  pubkeys : Vector BLSPubkey preset.SYNC_COMMITTEE_SIZE.toNat
  /-- The aggregate of those keys. -/
  aggregatePubkey : BLSPubkey
  deriving DecidableEq

/-- The sync committee whose keys are all zero, which stands for an unknown committee. -/
def SyncCommittee.empty (preset : Preset) : SyncCommittee preset :=
  ⟨Vector.replicate _ (Vector.replicate 48 0), Vector.replicate 48 0⟩

instance {preset : Preset} : SszType (SyncCommittee preset) :=
  .container ["pubkeys", "aggregate_pubkey"] (fun c => (c.pubkeys, c.aggregatePubkey))
    (fun (pubkeys, aggregatePubkey) => ⟨pubkeys, aggregatePubkey⟩)

/-- The signature of the sync committee that a block carries, with the members that signed. -/
structure SyncAggregate (preset : Preset) where
  /-- One bit for each member, in committee order, set when it signed. -/
  syncCommitteeBits : Bitvector preset.SYNC_COMMITTEE_SIZE.toNat
  /-- The aggregate signature of the members whose bit is set. -/
  syncCommitteeSignature : BLSSignature
  deriving DecidableEq

instance {preset : Preset} : SszType (SyncAggregate preset) :=
  .container ["sync_committee_bits", "sync_committee_signature"]
    (fun a => (a.syncCommitteeBits, a.syncCommitteeSignature))
    (fun (syncCommitteeBits, syncCommitteeSignature) =>
      ⟨syncCommitteeBits, syncCommitteeSignature⟩)

/-- The signature of one member of the sync committee on a block root. -/
structure SyncCommitteeMessage where
  /-- The slot of the message. -/
  slot : Slot
  /-- The root of the block that the member signs. -/
  beaconBlockRoot : Root
  /-- The member. -/
  validatorIndex : ValidatorIndex
  /-- The signature of the member. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType SyncCommitteeMessage :=
  .container ["slot", "beacon_block_root", "validator_index", "signature"]
    (fun m => (m.slot, m.beaconBlockRoot, m.validatorIndex, m.signature))
    (fun (slot, beaconBlockRoot, validatorIndex, signature) =>
      ⟨slot, beaconBlockRoot, validatorIndex, signature⟩)

/-- The number of members of one subcommittee: one subnet's share of the sync committee. -/
def syncSubcommitteeSize (preset : Preset) : Nat :=
  preset.SYNC_COMMITTEE_SIZE.toNat / Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT

/-- The aggregate of the messages of one subcommittee on a block root. -/
structure SyncCommitteeContribution (preset : Preset) where
  /-- The slot of the messages. -/
  slot : Slot
  /-- The root of the block that the members sign. -/
  beaconBlockRoot : Root
  /-- The subcommittee. -/
  subcommitteeIndex : UInt64
  /-- One bit for each member of the subcommittee, in order, set when it signed. -/
  aggregationBits : Bitvector (syncSubcommitteeSize preset)
  /-- The aggregate signature of the members whose bit is set. -/
  signature : BLSSignature
  deriving DecidableEq

instance {preset : Preset} : SszType (SyncCommitteeContribution preset) :=
  .container ["slot", "beacon_block_root", "subcommittee_index", "aggregation_bits", "signature"]
    (fun c => (c.slot, c.beaconBlockRoot, c.subcommitteeIndex, c.aggregationBits, c.signature))
    (fun (slot, beaconBlockRoot, subcommitteeIndex, aggregationBits, signature) =>
      ⟨slot, beaconBlockRoot, subcommitteeIndex, aggregationBits, signature⟩)

/-- A contribution that an aggregator publishes, with its proof of selection. -/
structure ContributionAndProof (preset : Preset) where
  /-- The aggregator. -/
  aggregatorIndex : ValidatorIndex
  /-- The contribution. -/
  contribution : SyncCommitteeContribution preset
  /-- The signature of the selection data by the aggregator, which shows that it was selected. -/
  selectionProof : BLSSignature
  deriving DecidableEq

instance {preset : Preset} : SszType (ContributionAndProof preset) :=
  .container ["aggregator_index", "contribution", "selection_proof"]
    (fun c => (c.aggregatorIndex, c.contribution, c.selectionProof))
    (fun (aggregatorIndex, contribution, selectionProof) =>
      ⟨aggregatorIndex, contribution, selectionProof⟩)

/-- A contribution and its proof, with the signature of the aggregator. -/
structure SignedContributionAndProof (preset : Preset) where
  /-- The contribution and its proof. -/
  message : ContributionAndProof preset
  /-- The signature of the message by the aggregator. -/
  signature : BLSSignature
  deriving DecidableEq

instance {preset : Preset} : SszType (SignedContributionAndProof preset) :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

/-- What a member signs to show that it aggregates a subcommittee in a slot. -/
structure SyncAggregatorSelectionData where
  /-- The slot. -/
  slot : Slot
  /-- The subcommittee. -/
  subcommitteeIndex : UInt64
  deriving DecidableEq, Repr

instance : SszType SyncAggregatorSelectionData :=
  .container ["slot", "subcommittee_index"] (fun d => (d.slot, d.subcommitteeIndex))
    (fun (slot, subcommitteeIndex) => ⟨slot, subcommitteeIndex⟩)

end EthLib.Consensus
