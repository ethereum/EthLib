module

public import EthLib.Consensus.HonestValidator

/-!
# `Consensus.HonestAggregation`

The vote of an honest attester, and the aggregates that an honest aggregator builds from votes.

An attester builds attestation data from the head block and the state of its slot.

The data votes for the head block, and from the justified checkpoint to the start of the epoch.

Its index is the committee before Electra and zero from Electra, as [EIP-7549] specifies.

From Gloas the index of a vote on a block of an earlier slot says whether its payload is present.

That is the rule of [EIP-7732], and a vote on a block of its own slot keeps index zero.

An attester signs attestation data, and sends its vote on the subnet of its committee.

Before Electra the vote is an attestation, with the one bit of the attester's seat in its committee.

From Electra it is a single attestation, which names the committee and the attester.

An aggregator joins the votes of one committee on the same data into one attestation.

Its bits mark the seats of the attesters, and its signature is the aggregate of their signatures.

From Electra it also sets the bit of its one committee, as [EIP-7549] specifies.

From Altair, a sync aggregator joins the messages on one block root into a contribution.

Its bits mark each seat of its subcommittee whose key signed, and a key can hold several seats.

Its signature holds one signature for each seat it marks.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
[EIP-7732]: https://github.com/ethereum/EIPs/blob/f1ade090fd315895461fc3e249cb1a675aeb55a9/EIPS/eip-7732.md#state-transition

The collection of the votes from the network is not specified here.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-! ## Attestation data -/

/-- The root of the block at the first slot of the epoch of a state.

At the first slot the head block is that block, and the root of the head block is given.

Otherwise it is the root that the state records for that slot.

It fails when that slot is out of the range of the recorded roots, or a 64-bit operation overflows.
-/
def getEpochBoundaryBlockRoot (state : BeaconState preset fork) (headRoot : Root) :
    Except ValidatorDutyError Root := do
  let epoch := getCurrentEpoch state
  let startSlot ← (computeStartSlotAtEpoch preset epoch).mapError .arith
  if startSlot = state.slot then return headRoot
  else (getBlockRoot state epoch).mapError .accessor

/-- The index in attestation data, from the fork, the slot of the data and the head block.

Before Electra it is the index of the committee of the attester.

From Electra it is zero, since the attestation names the committee itself.

From Gloas it is zero for a head block of the slot of the data.

For a head block of an earlier slot it is the status of its payload in the fork choice.

It is 0 for an empty payload and 1 for a full one, and it fails for a pending status. -/
def attestationDataIndex (fork : Base.Fork) (slot headSlot : Slot)
    (committeeIndex : CommitteeIndex) (payloadStatus : PayloadStatus) :
    Except ValidatorDutyError CommitteeIndex :=
  if .glamsterdam ≤ fork then
    if headSlot = slot then .ok 0
    else
      match payloadStatus with
      | .empty => .ok 0
      | .full => .ok 1
      | .pending => .error .pendingPayloadStatus
  else if .pectra ≤ fork then .ok 0
  else .ok committeeIndex

/-- The attestation data of an attester, from the head block and the state at its slot.

The guide takes the state of the head block through the empty slots up to the slot of the duty.

So the slot of the data is the slot of the state.

The data votes for the root of the head block, which the fork choice gives.

Its source is the current justified checkpoint of the state.

Its target is the current epoch of the state, at the root of the block at the first slot of it.

The slot of the head block and the status of its payload are read only from Gloas.

It fails when the index fails, or the root of the target fails. -/
def getAttestationData (state : BeaconState preset fork) (headRoot : Root) (headSlot : Slot)
    (committeeIndex : CommitteeIndex) (payloadStatus : PayloadStatus) :
    Except ValidatorDutyError AttestationData := do
  let index ← attestationDataIndex fork state.slot headSlot committeeIndex payloadStatus
  let targetRoot ← getEpochBoundaryBlockRoot state headRoot
  return {
    slot := state.slot, index, beaconBlockRoot := headRoot
    source := state.currentJustifiedCheckpoint
    target := { epoch := getCurrentEpoch state, root := targetRoot } }

/-! ## Attestations -/

/-- The aggregate of the signatures of some attestations, in order.

It fails on an empty list, and on a signature that does not decode. -/
def getAggregateSignature (attestations : List (Attestation preset fork)) :
    Except BlsError BLSSignature :=
  Signatures.aggregate (attestations.map fun a => Base.packBytes a.signature).toArray

/-- Before Electra: the attestation of a validator, with the one bit of its seat in its committee.

The committee is that of the slot and the index of the data, and the bit is at its first seat.

The signature is that of the data, in its target epoch.

It fails when the committee has no value or does not hold the validator.

It also fails when the committee exceeds the limit of an attestation, or the signature fails. -/
def constructAttestation (config : Config) (state : BeaconState preset fork)
    (before : fork < .pectra) (data : AttestationData) (validatorIndex : ValidatorIndex)
    (key : Signatures.SecretKey) : Except ValidatorDutyError (Attestation preset fork) := do
  let committee ← (getBeaconCommittee state data.slot data.index).mapError .accessor
  let position := committee.idxOf validatorIndex
  unless position < committee.size do throw (.notInCommittee validatorIndex)
  let bits := Array.ofFn fun seat : Fin committee.size => decide (seat.val = position)
  if bound : bits.size ≤ maxAttesters preset fork then
    let signature ← getAttestationSignature config state data key
    return {
      aggregationBits := ⟨bits, fun _ => bound⟩, data, signature
      committeeBits := fun electra => absurd electra (Nat.not_le_of_lt before) }
  else throw (.tooManyBits bits.size (maxAttesters preset fork))

/-- From Electra: the single attestation of a validator in a committee.

The signature is that of the data, in its target epoch.

It fails when the signature fails. -/
def constructSingleAttestation (config : Config) (state : BeaconState preset fork)
    (data : AttestationData) (committeeIndex : CommitteeIndex) (validatorIndex : ValidatorIndex)
    (key : Signatures.SecretKey) : Except ValidatorDutyError SingleAttestation := do
  let signature ← getAttestationSignature config state data key
  return { committeeIndex, attesterIndex := validatorIndex, data, signature }

/-- Before Electra: the aggregate of the attestations that vote for some data.

It joins the attestations with that data, and fails when there is none.

The committee is that of the slot and the index of the data.

Each attestation must have one bit for each member of the committee.

A bit of the aggregate is set when the bit of some attestation is.

The signature is the aggregate of their signatures, which verifies only if no two share a bit.

It also fails when the committee has no value, and when a signature does not decode. -/
def constructAggregate (state : BeaconState preset fork) (before : fork < .pectra)
    (data : AttestationData) (attestations : List (Attestation preset fork)) :
    Except ValidatorDutyError (Attestation preset fork) := do
  match attestations.filter (·.data = data) with
  | [] => throw .noMessages
  | first :: rest =>
    let committee ← (getBeaconCommittee state data.slot data.index).mapError .accessor
    match found : (first :: rest).find? (·.aggregationBits.bits.size ≠ committee.size) with
    | some other => throw (.bitsLength other.aggregationBits.bits.size committee.size)
    | none =>
      let bits := Array.ofFn fun seat : Fin committee.size =>
        (first :: rest).any (·.aggregationBits.bits.getD seat.val false)
      -- The bits of the first attestation have the size of the committee, within the limit.
      have bound : bits.size ≤ maxAttesters preset fork := by
        have sized := List.find?_eq_none.mp found first List.mem_cons_self
        simp only [ne_eq, decide_eq_true_eq, Decidable.not_not] at sized
        simpa [bits, ← sized] using
          first.aggregationBits.bound (Nat.lt_of_lt_of_le before (by decide))
      let signature ← (getAggregateSignature (first :: rest)).mapError .bls
      return {
        aggregationBits := ⟨bits, fun _ => bound⟩, data, signature
        committeeBits := fun electra => absurd electra (Nat.not_le_of_lt before) }

/-- From Electra: the aggregate of the single attestations of a committee that vote for some data.

It joins the single attestations of that committee with that data, and fails when there is none.

The committee is that of the slot of the data, and each attester must hold a seat in it.

A bit of the aggregate is set at each seat whose member is the attester of one of them.

Its committee bits mark that one committee.

The signature is the aggregate of their signatures, which verifies only if no attester comes twice.

It fails when the index is not below the number of committees of a slot.

It also fails when the committee has no value, and when a signature does not decode.

Before Gloas it fails when the committee exceeds the limit of an attestation. -/
def constructAggregateOfSingleAttestations (state : BeaconState preset fork)
    (data : AttestationData) (committeeIndex : CommitteeIndex)
    (singles : List SingleAttestation) : Except ValidatorDutyError (Attestation preset fork) := do
  if inside : committeeIndex < preset.MAX_COMMITTEES_PER_SLOT then
    let same := singles.filter fun single =>
      single.data = data ∧ single.committeeIndex = committeeIndex
    if same.isEmpty then throw .noMessages
    else
      let committee ← (getBeaconCommittee state data.slot committeeIndex).mapError .accessor
      match same.find? (·.attesterIndex ∉ committee) with
      | some other => throw (.notInCommittee other.attesterIndex)
      | none =>
        let bits := Array.ofFn fun seat : Fin committee.size =>
          same.any (·.attesterIndex = committee[seat])
        if bound : fork < .glamsterdam → bits.size ≤ maxAttesters preset fork then
          let signature ← (Signatures.aggregate
            (same.map fun single => Base.packBytes single.signature).toArray).mapError .bls
          return {
            aggregationBits := ⟨bits, bound⟩, data, signature
            committeeBits := fun _ =>
              ⟨Vector.ofFn fun index : Fin preset.MAX_COMMITTEES_PER_SLOT.toNat =>
                index.val.toUInt64 == committeeIndex⟩ }
        else throw (.tooManyBits bits.size (maxAttesters preset fork))
  else throw (.indexOutOfRange committeeIndex preset.MAX_COMMITTEES_PER_SLOT)

/-! ## Sync committee contributions -/

/-- From Altair: the key of a seat of a subcommittee of a sync committee.

It is the key at that seat of the slice of the subcommittee, which gossip reads too. -/
def syncSubcommitteeKey (committee : SyncCommittee preset) (subcommitteeIndex : UInt64)
    (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT)
    (seat : Fin (syncSubcommitteeSize preset)) : BLSPubkey :=
  (syncSubcommitteePubkeys committee subcommitteeIndex.toNat)[seat.val]'(by
    have below : subcommitteeIndex.toNat < Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT := by
      simpa [SYNC_COMMITTEE_SUBNET_COUNT, Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT,
        UInt64.lt_iff_toNat_lt] using inRange
    -- The slices before the last one end at most one slice before the end of the committee.
    have room : (subcommitteeIndex.toNat + 1) * syncSubcommitteeSize preset ≤
        preset.SYNC_COMMITTEE_SIZE.toNat :=
      calc (subcommitteeIndex.toNat + 1) * syncSubcommitteeSize preset
          ≤ Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT * syncSubcommitteeSize preset :=
            Nat.mul_le_mul_right _ below
        _ ≤ preset.SYNC_COMMITTEE_SIZE.toNat := Nat.mul_div_le _ _
    rw [Nat.succ_mul] at room
    have := seat.isLt
    simp only [syncSubcommitteePubkeys, List.length_take, List.length_drop, Vector.length_toList]
    omega)

/-- From Altair: the contribution of a subcommittee from the messages on a block root.

It joins the messages of the slot of the state on that root, and fails when there is none.

The subcommittee is a slice of the sync committee given, and each signer must hold a seat in it.

The caller gives the committee of the next slot, since gossip and the next block check that one.

A bit is set at each seat whose key is the key of the validator of one of the messages.

The signature is the aggregate of one signature for each set seat, in the order of the seats.

So a key with two seats of the subcommittee counts twice.

A seat takes the signature of the first message whose validator has its key.

It fails when the index is not below the number of subnets, and when a validator is not known.

It also fails when a signature does not decode. -/
def constructSyncCommitteeContribution (state : BeaconState preset fork)
    (committee : SyncCommittee preset) (blockRoot : Root) (subcommitteeIndex : UInt64)
    (messages : List SyncCommitteeMessage) :
    Except ValidatorDutyError (SyncCommitteeContribution preset) := do
  if inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT then
    let seatKey := syncSubcommitteeKey committee subcommitteeIndex inRange
    let same := messages.filter fun message =>
      message.slot = state.slot ∧ message.beaconBlockRoot = blockRoot
    if same.isEmpty then throw .noMessages
    else
      let keyed ← same.mapM fun message => do
        let validator ← (getValidator state message.validatorIndex).mapError .accessor
        return (validator.pubkey, message)
      match keyed.find? fun (key, _) => !(List.finRange _).any (seatKey · = key) with
      | some (_, other) => throw (.notInCommittee other.validatorIndex)
      | none =>
        let signatures := (List.finRange _).filterMap fun seat =>
          (keyed.find? (·.1 = seatKey seat)).map fun (_, message) =>
            Base.packBytes message.signature
        let signature ← (Signatures.aggregate signatures.toArray).mapError .bls
        return {
          slot := state.slot, beaconBlockRoot := blockRoot, subcommitteeIndex
          aggregationBits := ⟨Vector.ofFn fun seat => keyed.any (·.1 = seatKey seat)⟩, signature }
  else throw (.indexOutOfRange subcommitteeIndex SYNC_COMMITTEE_SUBNET_COUNT)

end EthLib.Consensus
