module

public import EthLib.Consensus.Containers.Misc

/-!
# `Consensus.Containers.PayloadAttestation`

From Gloas: the payload timeliness committee and the votes of its members.

The committee of a slot votes on whether the payload of the block arrived in time.

It also votes on whether the blob data of that payload is available.

The state records, for each recent slot, whether its block has a payload.

[EIP-7732] adds them; on 2026-11-03 the EIP was in Last Call.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#new-containers
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- What a member of the committee votes on: the payload of one block. -/
structure PayloadAttestationData where
  /-- The root of the block. -/
  beaconBlockRoot : Root
  /-- The slot of the block. -/
  slot : Slot
  /-- Whether the payload of the block arrived in time. -/
  payloadPresent : Bool
  /-- Whether the blob data of the payload is available. -/
  blobDataAvailable : Bool
  deriving DecidableEq, Repr

instance : SszType PayloadAttestationData :=
  .container ["beacon_block_root", "slot", "payload_present", "blob_data_available"]
    (fun d => (d.beaconBlockRoot, d.slot, d.payloadPresent, d.blobDataAvailable))
    (fun (beaconBlockRoot, slot, payloadPresent, blobDataAvailable) =>
      ⟨beaconBlockRoot, slot, payloadPresent, blobDataAvailable⟩)

/-- The vote of one member of the committee, with its signature. -/
structure PayloadAttestationMessage where
  /-- The member. -/
  validatorIndex : ValidatorIndex
  /-- The vote. -/
  data : PayloadAttestationData
  /-- The signature of the member on the vote. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType PayloadAttestationMessage :=
  .container ["validator_index", "data", "signature"]
    (fun m => (m.validatorIndex, m.data, m.signature))
    (fun (validatorIndex, data, signature) => ⟨validatorIndex, data, signature⟩)

/-- The payload timeliness committee of one slot, in committee order. -/
abbrev PayloadTimelinessCommittee (preset : Preset) :=
  Vector ValidatorIndex preset.PTC_SIZE.toNat

/-- The members of the committee that took part in a vote, at most the size of the committee. -/
abbrev PayloadTimelinessCommitteeIndices (preset : Preset) :=
  SszList ValidatorIndex preset.PTC_SIZE.toNat

/-- One bit for each member of the committee, in committee order, set when it took part. -/
abbrev PayloadTimelinessCommitteeBits (preset : Preset) := Bitvector preset.PTC_SIZE.toNat

/-- The committees of the slots of the previous epoch, the current epoch and the lookahead.

The lookahead is the epochs whose committees the seed already fixes. -/
abbrev PayloadTimelinessCommitteeWindow (preset : Preset) :=
  Vector (PayloadTimelinessCommittee preset)
    ((preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat)

/-- One bit for each recent slot, at the slot modulo the length, set when its block has a payload.

The length is the number of recent block roots that the state keeps. -/
abbrev ExecutionPayloadAvailability (preset : Preset) :=
  Bitvector preset.SLOTS_PER_HISTORICAL_ROOT.toNat

/-- The votes of the members of the committee on one payload, aggregated.

The block of the next slot includes it. -/
structure PayloadAttestation (preset : Preset) where
  /-- One bit for each member of the committee, in committee order, set when it signed. -/
  aggregationBits : PayloadTimelinessCommitteeBits preset
  /-- The vote. -/
  data : PayloadAttestationData
  /-- The aggregate signature of the members whose bit is set. -/
  signature : BLSSignature

/-- The layout of an aggregated vote, its three fields in their order. -/
def PayloadAttestation.activeFields : List Bool := [true, true, true]

instance {preset : Preset} : SszType (PayloadAttestation preset) :=
  .progressiveContainer PayloadAttestation.activeFields ["aggregation_bits", "data", "signature"]
    (fun a => (a.aggregationBits, a.data, a.signature))
    (fun (aggregationBits, data, signature) => ⟨aggregationBits, data, signature⟩)

/-- The aggregated votes that a beacon block includes. -/
abbrev PayloadAttestations (preset : Preset) := ProgressiveList (PayloadAttestation preset)

/-- An aggregated vote with the indices of the members that signed, in place of their bits. -/
structure IndexedPayloadAttestation (preset : Preset) where
  /-- The indices of the members that signed. -/
  attestingIndices : PayloadTimelinessCommitteeIndices preset
  /-- The vote. -/
  data : PayloadAttestationData
  /-- The aggregate signature of those members. -/
  signature : BLSSignature

/-- The layout of an indexed vote, its three fields in their order. -/
def IndexedPayloadAttestation.activeFields : List Bool := [true, true, true]

instance {preset : Preset} : SszType (IndexedPayloadAttestation preset) :=
  .progressiveContainer IndexedPayloadAttestation.activeFields
    ["attesting_indices", "data", "signature"]
    (fun a => (a.attestingIndices, a.data, a.signature))
    (fun (attestingIndices, data, signature) => ⟨attestingIndices, data, signature⟩)

end EthLib.Consensus
