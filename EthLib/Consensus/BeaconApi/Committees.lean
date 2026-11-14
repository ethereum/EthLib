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

[committees]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/committee.yaml
[sync committees]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/sync_committees.yaml
[PTC]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/ptc.yaml
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

A slot of the epoch matches when the slot filter is absent or names it.

The indices of a slot are those below its count of committees.

An index matches when the index filter is absent or names it.

The committees share one shuffle of the active validators of the epoch.

It fails when a slot of the epoch overflows 64 bits, or as the shuffle or a cut does. -/
def epochCommittees (state : BeaconState preset fork) (epoch : Epoch)
    (index : Option CommitteeIndex) (slot : Option Slot) :
    Except AccessorError (List Committee) := do
  let slots ← liftArith (epochSlots preset epoch)
  let perSlot := getCommitteeCountPerSlot state epoch
  let (active, shuffled) ← attesterShuffle state epoch
  let indices := ((List.range perSlot.toNat).map Nat.toUInt64).filter fun i => index.all (· == i)
  let positions := (slots.filter fun s => slot.all (· == s)).flatMap fun s => indices.map (s, ·)
  positions.mapM fun (s, i) => do
    return { index := i, slot := s,
             validators := ← beaconCommitteeOf preset s i perSlot active shuffled }

/-- The response of the committees endpoint, without the two flags that come from the store.

The epoch is that of the state when none is given, and it must be at most the next one.

Its seed must read a RANDAO mix that the state still holds.

So the epoch plus the length of the buffer of mixes must be after the next one plus the lookahead.

An epoch outside these bounds, or a slot filter outside the epoch, gives the error with code 400.

An index filter only restricts the list, so an index that names no committee gives an empty list.

A committee that cannot be computed gives the error with code 500. -/
def committeesResponse (state : BeaconState preset fork) (epoch : Option Epoch)
    (index : Option CommitteeIndex) (slot : Option Slot) : Except ErrorMessage ApiEnvelope := do
  let epoch := epoch.getD (getCurrentEpoch state)
  unless epoch.toNat ≤ (getCurrentEpoch state).toNat + 1 do
    throw { code := 400, message := s!"Epoch {epoch.toNat} is after the next epoch" }
  unless (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat do
    throw { code := 400, message := s!"Epoch {epoch.toNat} is before the mixes of the state" }
  if slot.any (computeEpochAtSlot preset · != epoch) then
    throw { code := 400, message := "Slot does not belong in epoch" }
  let committees ← (epochCommittees state epoch index slot).mapError fun _ =>
    internalError "no committees"
  return { data := .arr (committees.map Committee.toJson).toArray }

/-! ## Sync committees -/

/-- From Altair: the sync committee of the period of an epoch, or an error with code 400.

The period must be that of the current epoch of the state, or the next one.

The state holds only those two committees. -/
def syncCommitteeOf (state : BeaconState preset fork) (altair : .altair ≤ fork) (epoch : Epoch) :
    Except ErrorMessage (SyncCommittee preset) :=
  let period := computeSyncCommitteePeriod preset epoch
  let current := computeSyncCommitteePeriod preset (getCurrentEpoch state)
  if period = current then .ok (state.currentSyncCommittee altair).value
  else if period.toNat = current.toNat + 1 then .ok (state.nextSyncCommittee altair).value
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
  (List.range Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT).map fun subnet =>
    (seats.drop (subnet * syncSubcommitteeSize preset)).take (syncSubcommitteeSize preset)

/-- From Altair: the sync committee of the period of an epoch, by the indices of its members.

Each key names the first validator of the registry that holds it.

The period must be the current one or the next, or the answer is the error with code 400.

A key that no validator holds gives the error with code 500. -/
def epochSyncCommittees (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (epoch : Epoch) : Except ErrorMessage SyncCommitteeIndices := do
  let committee ← syncCommitteeOf state altair epoch
  let validators ← committee.pubkeys.toList.mapM fun pubkey =>
    match resolveValidatorId state (.pubkey pubkey) with
    | some index => .ok index
    | none => .error (internalError "a sync committee key that no validator holds")
  return { validators, validatorAggregates := syncAggregates preset validators }

/-- The response of the sync committees endpoint, without the two flags that come from the store.

The epoch is that of the state when none is given.

A state before Altair gives the error with code 400. -/
def syncCommitteesResponse (state : BeaconState preset fork) (epoch : Option Epoch) :
    Except ErrorMessage ApiEnvelope := do
  if altair : .altair ≤ fork then
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

/-- The payload timeliness committee of a slot, from Gloas.

The slot is that of the state when none is given.

A state before Gloas gives the error with code 400.

So does a slot that the window of the state does not hold.

The window holds the slots from Gloas on, from the epoch before that of the state.

It ends at the epoch of the state plus the lookahead of seeds. -/
def statePtc (config : Config) (state : BeaconState preset fork) (slot : Option Slot) :
    Except ErrorMessage (PtcResponse preset) := do
  if gloas : .glamsterdam ≤ fork then
    let slot := slot.getD state.slot
    match getPtc config state gloas slot with
    | .ok validators => return { slot, validators }
    | .error _ => throw { code := 400, message := "Slot is outside the PTC window of the state" }
  else throw (beforeFork "ptc" .glamsterdam)

/-- The response of the PTC endpoint, without the two flags that come from the store. -/
def ptcResponse (config : Config) (state : BeaconState preset fork) (slot : Option Slot) :
    Except ErrorMessage ApiEnvelope := do
  return { data := ← apiJsonOr500 (← statePtc config state slot) }

/-- The SSZ body of the PTC answer. -/
def ptcSsz (config : Config) (state : BeaconState preset fork) (slot : Option Slot) :
    Except ErrorMessage ByteArray :=
  statePtc config state slot >>= apiSszOr500

end EthLib.Consensus.BeaconApi
