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
[EIP-7732]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7732.md#state-transition

The collection of the votes from the network is not specified here.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-! ## Attestation data -/

/-- The root of the block at the first slot of the epoch of a state.

The root of the head block is given, for the case where the state is at that first slot.

It fails when that slot is out of the range of the recorded roots, or a 64-bit operation overflows.
-/
def getEpochBoundaryBlockRoot (state : BeaconState preset fork) (headRoot : Root) :
    Except ValidatorDutyError Root := do
  -- The current epoch `e` and its first slot `e * SLOTS_PER_EPOCH`.
  let epoch := getCurrentEpoch state
  let startSlot ← (computeStartSlotAtEpoch preset epoch).mapError .arith
  -- At that slot the head block is the block of the slot, whose root is given.
  if startSlot = state.slot then return headRoot
  -- Otherwise the root that the state records for that slot.
  else (getBlockRoot state epoch).mapError .accessor

/-- The index in attestation data, from the fork, the slot of the data and the head block.

From Electra the attestation names the committee itself.

From Gloas the status of the payload of the head block in the fork choice gives the index.

It fails for a pending status. -/
def attestationDataIndex (fork : Base.Fork) (slot headSlot : Slot)
    (committeeIndex : CommitteeIndex) (payloadStatus : PayloadStatus) :
    Except ValidatorDutyError CommitteeIndex :=
  if .glamsterdam ≤ fork then
    -- From Gloas, 0 for a head block of the slot of the data, as EIP-7732 specifies.
    if headSlot = slot then .ok 0
    -- For a head block of an earlier slot, 0 without its payload and 1 with it, as EIP-7732 says.
    --
    -- The fork choice says which; the source gives no index for a pending status, an error.
    else
      match payloadStatus with
      | .empty => .ok 0
      | .full => .ok 1
      | .pending => .error (.pendingPayloadStatus slot headSlot)
  -- From Electra, 0, as EIP-7549 specifies.
  else if .pectra ≤ fork then .ok 0
  -- Before Electra, the index of the committee of the attester.
  else .ok committeeIndex

/-- The attestation data of an attester, from the head block and the state at its slot.

The state of the head block goes through the empty slots up to the slot of the duty.

So the slot of the data is the slot of the state.

The fork choice gives the root of the head block.

The slot of the head block and the status of its payload are read only from Gloas.

It fails when the index fails, or the root of the block at the first slot of the epoch fails. -/
def getAttestationData (state : BeaconState preset fork) (headRoot : Root) (headSlot : Slot)
    (committeeIndex : CommitteeIndex) (payloadStatus : PayloadStatus) :
    Except ValidatorDutyError AttestationData := do
  -- The index, from the fork, the slot of the state and the head block.
  let index ← attestationDataIndex fork state.slot headSlot committeeIndex payloadStatus
  -- The root of the block at the first slot of the current epoch.
  let targetRoot ← getEpochBoundaryBlockRoot state headRoot
  -- The data at the slot of the state votes for the head block.
  --
  -- Its source is the current justified checkpoint of the state.
  --
  -- Its target is the current epoch, at that root.
  return {
    slot := state.slot, index, beaconBlockRoot := headRoot
    source := state.currentJustifiedCheckpoint
    target := { epoch := getCurrentEpoch state, root := targetRoot } }

/-! ## Attestations -/

/-- The aggregate of the signatures of some attestations, in order.

It fails on an empty list, and on a signature that does not decode. -/
def getAggregateSignature (attestations : List (Attestation preset fork)) :
    Except BlsError BLSSignature :=
  -- The BLS aggregate of their signatures, in order.
  Signatures.aggregate (attestations.map (·.signature)).toArray

/-- Before Electra: the attestation of a validator, with the one bit of its seat in its committee.

It fails when the committee has no value or does not hold the validator.

It also fails when the committee exceeds the limit of an attestation, or the signature fails. -/
def constructAttestation (config : Config) (state : BeaconState preset fork)
    (before : fork < .pectra) (data : AttestationData) (validatorIndex : ValidatorIndex)
    (key : Signatures.SecretKey) : Except ValidatorDutyError (Attestation preset fork) := do
  -- The committee `C` of the slot and the index of the data.
  let committee ← (getBeaconCommittee state data.slot data.index).mapError .accessor
  -- The first seat `j` of the validator in `C`, which must hold it.
  let position := committee.idxOf validatorIndex
  unless position < committee.size do throw (.notInCommittee validatorIndex)
  -- One bit for each seat of `C`, set only at `j`.
  let bits := Array.ofFn fun seat : Fin committee.size => decide (seat.val = position)
  -- The bits fit the limit of an attestation.
  if bound : bits.size ≤ maxAttesters preset fork then
    -- The signature of the data at its target epoch.
    let signature ← getAttestationSignature config state data key
    return {
      aggregationBits := ⟨bits, fun _ => bound⟩, data, signature
      committeeBits := fun electra => absurd electra (Nat.not_le_of_lt before) }
  -- More bits than the limit are an error.
  else throw (.tooManyBits bits.size (maxAttesters preset fork))

/-- From Electra: the single attestation of a validator in a committee.

It fails when the signature fails. -/
def constructSingleAttestation (config : Config) (state : BeaconState preset fork)
    (data : AttestationData) (committeeIndex : CommitteeIndex) (validatorIndex : ValidatorIndex)
    (key : Signatures.SecretKey) : Except ValidatorDutyError SingleAttestation := do
  -- The signature of the data at its target epoch.
  let signature ← getAttestationSignature config state data key
  -- The single attestation names the committee and the attester beside the data.
  return { committeeIndex, attesterIndex := validatorIndex, data, signature }

/-- Before Electra: the aggregate of the attestations that vote for some data.

It fails when no attestation has that data.

The aggregate signature verifies only if no two attestations share a bit.

It also fails when the committee of the data has no value, and when a signature does not decode.

It fails when an attestation does not have one bit for each member of that committee. -/
def constructAggregate (state : BeaconState preset fork) (before : fork < .pectra)
    (data : AttestationData) (attestations : List (Attestation preset fork)) :
    Except ValidatorDutyError (Attestation preset fork) := do
  -- The attestations `A` with that data.
  match attestations.filter (·.data = data) with
  -- No such attestation is an error.
  | [] => throw (.noMessages data.slot data.beaconBlockRoot)
  | first :: rest =>
    -- The committee `C` of the slot and the index of the data.
    let committee ← (getBeaconCommittee state data.slot data.index).mapError .accessor
    -- Each attestation of `A` has one bit for each seat of `C`.
    match found : (first :: rest).find? (·.aggregationBits.bits.size ≠ committee.size) with
    | some other => throw (.bitsLength other.aggregationBits.bits.size committee.size)
    | none =>
      -- Bit `j` of the aggregate is set when bit `j` of some attestation of `A` is.
      let bits := Array.ofFn fun seat : Fin committee.size =>
        (first :: rest).any (·.aggregationBits.bits.getD seat.val false)
      -- The bits of the first attestation have the size of the committee, within the limit.
      have bound : bits.size ≤ maxAttesters preset fork := by
        have sized := List.find?_eq_none.mp found first List.mem_cons_self
        simp only [ne_eq, decide_eq_true_eq, Decidable.not_not] at sized
        simpa [bits, ← sized] using
          first.aggregationBits.bound (Nat.lt_of_lt_of_le before (by decide))
      -- The signature is the aggregate of the signatures of `A`, in order.
      let signature ← (getAggregateSignature (first :: rest)).mapError .bls
      return {
        aggregationBits := ⟨bits, fun _ => bound⟩, data, signature
        committeeBits := fun electra => absurd electra (Nat.not_le_of_lt before) }

/-- From Electra: the aggregate of the single attestations of a committee that vote for some data.

It fails when no single attestation of that committee has that data.

The aggregate signature verifies only if no attester comes twice.

It fails when the index is not below the number of committees of a slot.

It also fails when the committee has no value, and when a signature does not decode.

It fails when an attester holds no seat in the committee.

Before Gloas it fails when the committee exceeds the limit of an attestation. -/
def constructAggregateOfSingleAttestations (state : BeaconState preset fork)
    (data : AttestationData) (committeeIndex : CommitteeIndex)
    (singles : List SingleAttestation) : Except ValidatorDutyError (Attestation preset fork) := do
  -- The committee index `i` is below `MAX_COMMITTEES_PER_SLOT`.
  if inside : committeeIndex < preset.MAX_COMMITTEES_PER_SLOT then
    -- The single attestations `S` of committee `i` with that data.
    let same := singles.filter fun single =>
      single.data = data ∧ single.committeeIndex = committeeIndex
    -- No such attestation is an error.
    if same.isEmpty then throw (.noMessages data.slot data.beaconBlockRoot)
    else
      -- The committee `C` of index `i` at the slot of the data.
      let committee ← (getBeaconCommittee state data.slot committeeIndex).mapError .accessor
      -- Each attester of `S` holds a seat of `C`.
      match same.find? (·.attesterIndex ∉ committee) with
      | some other => throw (.notInCommittee other.attesterIndex)
      | none =>
        -- Bit `j` is set when the member at seat `j` of `C` is the attester of some element of `S`.
        let bits := Array.ofFn fun seat : Fin committee.size =>
          same.any (·.attesterIndex = committee[seat])
        -- Before Gloas, the bits fit the limit of an attestation.
        if bound : fork < .glamsterdam → bits.size ≤ maxAttesters preset fork then
          -- The signature is the aggregate of the signatures of `S`, in order.
          let signature ← (Signatures.aggregate
            (same.map (·.signature)).toArray).mapError .bls
          -- The committee bits set only bit `i`.
          return {
            aggregationBits := ⟨bits, bound⟩, data, signature
            committeeBits := fun _ =>
              ⟨Vector.ofFn fun index : Fin preset.MAX_COMMITTEES_PER_SLOT.toNat =>
                index.val.toUInt64 == committeeIndex⟩ }
        -- More bits than the limit are an error.
        else throw (.tooManyBits bits.size (maxAttesters preset fork))
  -- An index of `MAX_COMMITTEES_PER_SLOT` or more is an error.
  else throw (.indexOutOfRange committeeIndex preset.MAX_COMMITTEES_PER_SLOT)

/-! ## Sync committee contributions -/

/-- From Altair: the key of a seat of a subcommittee of a sync committee.

It is the key at that seat of the slice of the subcommittee, which gossip reads too. -/
def syncSubcommitteeKey (committee : SyncCommittee preset) (subcommitteeIndex : UInt64)
    (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT)
    (seat : Fin (syncSubcommitteeSize preset)) : BLSPubkey :=
  -- The key at the seat in the slice of the subcommittee.
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

It fails when no message of the slot of the state is on that root.

The subcommittee is a slice of the sync committee given.

The caller gives the committee of the next slot, since gossip and the next block check that one.

The signature holds one signature for each set seat, so a key with two seats counts twice.

A seat takes the signature of the first message whose validator has its key.

It fails when the index is not below the number of subnets, and when a validator is not known.

It also fails when a signature does not decode.

It fails when the key of a signer holds no seat of the subcommittee. -/
def constructSyncCommitteeContribution (state : BeaconState preset fork)
    (committee : SyncCommittee preset) (blockRoot : Root) (subcommitteeIndex : UInt64)
    (messages : List SyncCommitteeMessage) :
    Except ValidatorDutyError (SyncCommitteeContribution preset) := do
  -- The subcommittee index `k` is below `SYNC_COMMITTEE_SUBNET_COUNT`.
  if inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT then
    -- The key at each seat of slice `k` of the committee.
    let seatKey := syncSubcommitteeKey committee subcommitteeIndex inRange
    -- The messages at the slot of the state on the block root.
    let same := messages.filter fun message =>
      message.slot = state.slot ∧ message.beaconBlockRoot = blockRoot
    -- No such message is an error.
    if same.isEmpty then throw (.noMessages state.slot blockRoot)
    else
      -- The key of the validator of each message.
      let keyed ← same.mapM fun message => do
        let validator ← (getValidator state message.validatorIndex).mapError .accessor
        return (validator.pubkey, message)
      -- Each such key is at some seat of the slice.
      match keyed.find? fun (key, _) => !(List.finRange _).any (seatKey · = key) with
      | some (_, other) => throw (.notInCommittee other.validatorIndex)
      | none =>
        -- For each seat whose key signed, the signature of the first message with that key.
        --
        -- The seats come in order.
        let signatures := (List.finRange _).filterMap fun seat =>
          (keyed.find? (·.1 = seatKey seat)).map fun (_, message) => message.signature
        -- The aggregate of those signatures.
        let signature ← (Signatures.aggregate signatures.toArray).mapError .bls
        -- The contribution is at the slot of the state, on the root, for the subcommittee `k`.
        --
        -- Bit `j` is set when the key at seat `j` signed.
        return {
          slot := state.slot, beaconBlockRoot := blockRoot, subcommitteeIndex
          aggregationBits := ⟨Vector.ofFn fun seat => keyed.any (·.1 = seatKey seat)⟩, signature }
  -- An index of `SYNC_COMMITTEE_SUBNET_COUNT` or more is an error.
  else throw (.indexOutOfRange subcommitteeIndex SYNC_COMMITTEE_SUBNET_COUNT)

end EthLib.Consensus
