module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.PayloadTimeliness

/-!
# `Consensus.BeaconApi.Committees`

The answers of the Beacon API that list the committees of a state.

The [committees] endpoint lists the beacon committees of an epoch, with filters on index and slot.

The [sync committees] endpoint gives the indices of a sync committee, and its slices.

From Gloas, the [PTC] endpoint gives the payload timeliness committee of a slot.

Each answer is computed from the state alone.

The flags `execution_optimistic` and `finalized` come from the store, not from the state.

SOUNDNESS.md records the points that the source leaves open.

[committees]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/committee.yaml
[sync committees]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/sync_committees.yaml
[PTC]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/ptc.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-- The JSON of an index or a slot: its decimal text. -/
def uintJson (n : UInt64) : Json :=
  .str (toString n.toNat)

/-! ## Beacon committees -/

/-- A beacon committee: its index in its slot, its slot, and its members in committee order. -/
structure Committee where
  /-- The index of the committee among those of its slot. -/
  index : CommitteeIndex
  /-- The slot of the committee. -/
  slot : Slot
  /-- The members, in committee order. -/
  validators : Array ValidatorIndex
  deriving DecidableEq, Repr

/-- The JSON of a committee, as the API writes it. -/
def Committee.toJson (committee : Committee) : Json :=
  .mkObj [("index", uintJson committee.index), ("slot", uintJson committee.slot),
    ("validators", .arr (committee.validators.map uintJson))]

/-- The committees of an epoch that match the filters, slot after slot, then index after index.

It fails when a slot of the epoch overflows 64 bits, or as the shuffle or a cut does. -/
def epochCommittees (state : BeaconState preset fork) (epoch : Epoch)
    (index : Option CommitteeIndex) (slot : Option Slot) :
    Except AccessorError (List Committee) := do
  -- The slots of the epoch, each below 2^64.
  let slots ← liftArith (epochSlots preset epoch)
  -- The count of committees in each slot of the epoch.
  let perSlot := getCommitteeCountPerSlot state epoch
  -- One shuffle of the active validators of the epoch, which every committee cuts.
  let (active, shuffled) ← attesterShuffle state epoch
  -- The indices below that count that match the index filter, any index when it is absent.
  let indices := ((List.range perSlot.toNat).map Nat.toUInt64).filter fun i => index.all (· == i)
  -- The slots that match the slot filter, any slot when it is absent, with each index.
  let positions := (slots.filter fun s => slot.all (· == s)).flatMap fun s => indices.map (s, ·)
  -- The members of the committee at each slot and index, in committee order.
  positions.mapM fun (s, i) => do
    return { index := i, slot := s,
             validators := ← beaconCommitteeOf preset s i perSlot active shuffled }

/-- The response of the committees endpoint, without the two flags that come from the store. -/
def committeesResponse (state : BeaconState preset fork) (epoch : Option Epoch)
    (index : Option CommitteeIndex) (slot : Option Slot) : Except ErrorMessage ApiEnvelope := do
  -- The source: the epoch of the state when no epoch is present.
  let epoch := epoch.getD (getCurrentEpoch state)
  -- The source names no range of epochs.
  --
  -- EthLib's choice: code 400 after the next epoch, the last epoch of a committee assignment.
  unless epoch.toNat ≤ (getCurrentEpoch state).toNat + 1 do
    throw { code := 400, message := s!"Epoch {epoch.toNat} is after the next epoch" }
  -- EthLib's choice: code 400 when the seed of the epoch would read a mix the state overwrote.
  --
  -- That holds unless current epoch + seed lookahead + 1 < epoch + length of the buffer of mixes.
  unless (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat do
    throw { code := 400, message := s!"Epoch {epoch.toNat} is before the mixes of the state" }
  -- The source: code 400 for a slot outside the epoch, with its example message.
  if slot.any (computeEpochAtSlot preset · != epoch) then
    throw { code := 400, message := "Slot does not belong in epoch" }
  -- An index filter only restricts the list: an index that names no committee gives an empty list.
  --
  -- A committee that cannot be computed gives code 500.
  let committees ← (epochCommittees state epoch index slot).mapError fun _ =>
    internalError "no committees"
  -- The data is the array of the committees.
  return { data := .arr (committees.map Committee.toJson).toArray }

/-! ## Sync committees -/

/-- From Altair: the sync committee of the period of an epoch, or an error with code 400. -/
def syncCommitteeOf (state : BeaconState preset fork) (altair : .altair ≤ fork) (epoch : Epoch) :
    Except ErrorMessage (SyncCommittee preset) :=
  let period := computeSyncCommitteePeriod preset epoch
  let current := computeSyncCommitteePeriod preset (getCurrentEpoch state)
  -- The state holds only two committees: the one of the current period, and the next one.
  if period = current then .ok (state.currentSyncCommittee altair).value
  else if period.toNat = current.toNat + 1 then .ok (state.nextSyncCommittee altair).value
  -- Any other period: code 400, with the example message of the source.
  else .error { code := 400, message := "Epoch is outside the sync committee period of the state" }

/-- A sync committee by the indices of its members, with its slices for the subnets. -/
structure SyncCommitteeIndices where
  /-- The index of the validator of each seat, in seat order. -/
  validators : List ValidatorIndex
  /-- The slices of that list, one for each subnet, in order. -/
  validatorAggregates : List (List ValidatorIndex)
  deriving DecidableEq, Repr

/-- The JSON of a sync committee by indices, as the API writes it. -/
def SyncCommitteeIndices.toJson (committee : SyncCommitteeIndices) : Json :=
  .mkObj [("validators", .arr (committee.validators.map uintJson).toArray),
    ("validator_aggregates", .arr (committee.validatorAggregates.map fun slice =>
      Json.arr (slice.map uintJson).toArray).toArray)]

/-- The slices of the seats of a sync committee, one for each subnet, in order.

They are cut as the keys of the subcommittees are. -/
def syncAggregates {α : Type} (preset : Preset) (seats : List α) : List (List α) :=
  -- Slice `j` holds the seats from `j * k` to `(j + 1) * k - 1`, with `k` the subcommittee size.
  (List.range Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT).map fun subnet =>
    (seats.drop (subnet * syncSubcommitteeSize preset)).take (syncSubcommitteeSize preset)

/-- From Altair: the sync committee of the period of an epoch, by the indices of its members. -/
def epochSyncCommittees (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (epoch : Epoch) : Except ErrorMessage SyncCommitteeIndices := do
  -- The committee of the current or the next period, else code 400.
  let committee ← syncCommitteeOf state altair epoch
  -- The index of each seat: the first validator of the registry that holds its key.
  let validators ← committee.pubkeys.toList.mapM fun pubkey =>
    match resolveValidatorId state (.pubkey pubkey) with
    | some index => .ok index
    -- A key that no validator holds gives code 500.
    | none => .error (internalError "a sync committee key that no validator holds")
  -- The schema: the indices of all seats, and their slices for the subcommittees.
  return { validators, validatorAggregates := syncAggregates preset validators }

/-- The response of the sync committees endpoint, without the two flags that come from the store. -/
def syncCommitteesResponse (state : BeaconState preset fork) (epoch : Option Epoch) :
    Except ErrorMessage ApiEnvelope := do
  -- A state before Altair holds no sync committee: code 400, EthLib's choice.
  if altair : .altair ≤ fork then
    -- The source: the epoch of the state when no epoch is present.
    let committee ← epochSyncCommittees state altair (epoch.getD (getCurrentEpoch state))
    return { data := committee.toJson }
  else .error (beforeFork "sync_committees" .altair)

/-! ## Payload timeliness committees -/

/-- The payload timeliness committee of a slot. -/
structure PtcResponse (preset : Preset) where
  /-- The slot. -/
  slot : Slot
  /-- The members of the committee, in committee order. -/
  validators : PayloadTimelinessCommittee preset
  deriving DecidableEq, Repr

instance : SszType (PtcResponse preset) :=
  .container ["slot", "validators"] (fun r => (r.slot, r.validators))
    (fun (slot, validators) => ⟨slot, validators⟩)

instance : ApiSpelling (PtcResponse preset) := .unmarked

/-- The payload timeliness committee of a slot, from Gloas. -/
def statePtc (config : Config) (state : BeaconState preset fork) (slot : Option Slot) :
    Except ErrorMessage (PtcResponse preset) := do
  if gloas : .glamsterdam ≤ fork then
    -- The source: the slot of the state when no slot is given.
    let slot := slot.getD state.slot
    -- The committee that the window of the state holds for the slot.
    match getPtc config state gloas slot with
    | .ok validators => return { slot, validators }
    -- The source: code 400 for a slot before Gloas or outside the window, with its example.
    --
    -- The window holds the slots from Gloas on whose epoch e has c - 1 <= e <= c + lookahead.
    --
    -- Here c is the epoch of the state and the lookahead is that of seeds.
    | .error _ => throw { code := 400, message := "Slot is outside the PTC window of the state" }
  -- The source: code 400 for a state before Gloas.
  else throw (beforeFork "ptc" .glamsterdam)

/-- The response of the PTC endpoint, without the two flags that come from the store. -/
def ptcResponse (config : Config) (state : BeaconState preset fork) (slot : Option Slot) :
    Except ErrorMessage ApiEnvelope := do
  return { data := ← apiJsonOr500 (← statePtc config state slot) }

/-- The SSZ body of the PTC answer. -/
def ptcSsz (config : Config) (state : BeaconState preset fork) (slot : Option Slot) :
    Except ErrorMessage ByteArray :=
  -- The source: the container of the slot and the vector of the members of the committee.
  statePtc config state slot >>= apiSszOr500

end EthLib.Consensus.BeaconApi
