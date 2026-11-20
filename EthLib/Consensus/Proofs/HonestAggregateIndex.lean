module

public import EthLib.Consensus.Proofs.HonestAggregation
public import EthLib.Consensus.Proofs.HonestValidator

/-!
# Proofs: an honest aggregate names a committee of its slot

The lookup of a committee does not check its index against the count of committees of a slot.

Neither does the construction of an aggregate, which takes the index as an argument.

An honest aggregator takes that index from its committee assignment.

That index is below the count of committees of a slot, in the state of the assignment.

Block processing reads the count in its own state, so the bound holds there only when they agree.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- Attestation data built at the slot of an assignment has the epoch of that assignment as target.

The state of the data must be at the slot of the assignment. -/
theorem target_epoch_eq_of_getCommitteeAssignment {dutyState state : BeaconState preset fork}
    {epoch : Epoch} {validatorIndex : ValidatorIndex} {committee : Array ValidatorIndex}
    {index : CommitteeIndex} {slot : Slot} {headRoot : Root} {headSlot : Slot}
    {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus} {data : AttestationData}
    (assigned :
      getCommitteeAssignment dutyState epoch validatorIndex = .ok (some (committee, index, slot)))
    (atSlot : state.slot = slot)
    (made : getAttestationData state headRoot headSlot committeeIndex payloadStatus = .ok data) :
    data.target.epoch = epoch := by
  rw [target_epoch_eq_of_getAttestationData made, (getAttestationData_eq_ok_iff.mp made).2.2.1,
    atSlot, (getCommitteeAssignment_sound assigned).1]

/-- Before Electra, an aggregate on the data of an assignment has its index below the count.

The count is the number of committees of a slot.

The data is built at the slot of the assignment, with the index of the assignment.

The count is that of the state of the assignment, in the target epoch of the aggregate.

Block processing checks the index against this count, read in its own state. -/
theorem index_lt_of_constructAggregate_getCommitteeAssignment
    {dutyState state aggregateState : BeaconState preset fork} {before : fork < .pectra}
    {epoch : Epoch} {validatorIndex : ValidatorIndex} {committee : Array ValidatorIndex}
    {index : CommitteeIndex} {slot : Slot} {headRoot : Root} {headSlot : Slot}
    {payloadStatus : PayloadStatus} {data : AttestationData}
    {attestations : List (Attestation preset fork)} {aggregate : Attestation preset fork}
    (assigned :
      getCommitteeAssignment dutyState epoch validatorIndex = .ok (some (committee, index, slot)))
    (atSlot : state.slot = slot)
    (made : getAttestationData state headRoot headSlot index payloadStatus = .ok data)
    (built : constructAggregate aggregateState before data attestations = .ok aggregate) :
    aggregate.data.target.epoch = epoch ∧
      aggregate.data.index < getCommitteeCountPerSlot dutyState aggregate.data.target.epoch := by
  obtain ⟨-, below, -⟩ := getCommitteeAssignment_sound assigned
  obtain ⟨-, -, -, -, -, sameData, -⟩ := constructAggregate_spec built
  obtain ⟨indexed, -⟩ := getAttestationData_eq_ok_iff.mp made
  rw [attestationDataIndex_of_lt_pectra before, Except.ok.injEq] at indexed
  have targetEpoch := target_epoch_eq_of_getCommitteeAssignment assigned atSlot made
  rw [sameData, targetEpoch, ← indexed]
  exact ⟨rfl, below⟩

/-- From Electra, an aggregate for the committee of an assignment names indices below the count.

The count is the number of committees of a slot, and the aggregate names one committee.

Its data is built at the slot of the assignment, and its committee index is that of the assignment.

The count is that of the state of the assignment, in the target epoch of the aggregate.

Block processing checks each named index against this count, read in its own state. -/
theorem lt_of_mem_getCommitteeIndices_constructAggregateOfSingleAttestations
    {dutyState state aggregateState : BeaconState preset fork} (electra : .pectra ≤ fork)
    {epoch : Epoch} {validatorIndex : ValidatorIndex} {committee : Array ValidatorIndex}
    {index : CommitteeIndex} {slot : Slot} {headRoot : Root} {headSlot : Slot}
    {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus} {data : AttestationData}
    {singles : List SingleAttestation} {aggregate : Attestation preset fork}
    (assigned :
      getCommitteeAssignment dutyState epoch validatorIndex = .ok (some (committee, index, slot)))
    (atSlot : state.slot = slot)
    (made : getAttestationData state headRoot headSlot committeeIndex payloadStatus = .ok data)
    (built : constructAggregateOfSingleAttestations aggregateState data index singles =
      .ok aggregate) :
    aggregate.data.target.epoch = epoch ∧
      ∀ named ∈ getCommitteeIndices (aggregate.committeeBits electra),
        named < getCommitteeCountPerSlot dutyState aggregate.data.target.epoch := by
  obtain ⟨-, below, -⟩ := getCommitteeAssignment_sound assigned
  obtain ⟨-, -, -, -, -, sameData, -⟩ := constructAggregateOfSingleAttestations_spec built
  have targetEpoch := target_epoch_eq_of_getCommitteeAssignment assigned atSlot made
  rw [getCommitteeIndices_constructAggregateOfSingleAttestations electra built, sameData,
    targetEpoch]
  refine ⟨rfl, fun named member => ?_⟩
  rw [List.mem_singleton.mp member]
  exact below

end EthLib.Consensus
