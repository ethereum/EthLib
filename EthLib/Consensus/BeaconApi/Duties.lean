module

public import EthLib.Consensus.BeaconApi.Committees
public import EthLib.Consensus.HonestValidator
public import EthLib.Consensus.Proposers

/-!
# `Consensus.BeaconApi.Duties`

The answers of the Beacon API that give the duties of validators in an epoch.

The [duties endpoints] give the attester, proposer, sync committee and PTC duties.

Their [types] fix the fields of each duty.

Each answer is computed from a state that the caller chooses.

The attester, proposer and PTC answers also give the root of the block their duties depend on.

The flag `execution_optimistic` comes from the store, not from the state.

SOUNDNESS.md records the points that the source leaves open.

[duties endpoints]: https://github.com/ethereum/beacon-APIs/tree/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/duties
[types]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/duty.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-! ## Duties -/

/-- The duty of a validator to attest: its committee, its place in it, and its slot. -/
structure AttesterDuty where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The index of the validator in the registry. -/
  validatorIndex : ValidatorIndex
  /-- The index of the committee among those of its slot. -/
  committeeIndex : CommitteeIndex
  /-- The number of members of the committee. -/
  committeeLength : UInt64
  /-- The number of committees at the slot. -/
  committeesAtSlot : UInt64
  /-- The position of the validator in the committee. -/
  validatorCommitteeIndex : UInt64
  /-- The slot at which the validator attests. -/
  slot : Slot
  deriving DecidableEq, Repr

/-- The duty of a validator to propose the block of a slot. -/
structure ProposerDuty where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The index of the validator in the registry. -/
  validatorIndex : ValidatorIndex
  /-- The slot of the block. -/
  slot : Slot
  deriving DecidableEq, Repr

/-- The duty of a validator to sign in a sync committee: its seats in the committee. -/
structure SyncDuty where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The index of the validator in the registry. -/
  validatorIndex : ValidatorIndex
  /-- The seats of the validator in the committee, in order. -/
  validatorSyncCommitteeIndices : List UInt64
  deriving DecidableEq, Repr

/-- The duty of a validator to vote in the payload timeliness committee of a slot. -/
structure PtcDuty where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The index of the validator in the registry. -/
  validatorIndex : ValidatorIndex
  /-- The slot of the committee. -/
  slot : Slot
  deriving DecidableEq, Repr

/-- The JSON of a public key: its hex text. -/
def pubkeyJson (pubkey : BLSPubkey) : Json :=
  .str (toHex pubkey.toArray)

/-- The JSON of an attester duty, as the API writes it. -/
def AttesterDuty.toJson (duty : AttesterDuty) : Json :=
  .mkObj [("pubkey", pubkeyJson duty.pubkey), ("validator_index", uintJson duty.validatorIndex),
    ("committee_index", uintJson duty.committeeIndex),
    ("committee_length", uintJson duty.committeeLength),
    ("committees_at_slot", uintJson duty.committeesAtSlot),
    ("validator_committee_index", uintJson duty.validatorCommitteeIndex),
    ("slot", uintJson duty.slot)]

/-- The JSON of a proposer duty, as the API writes it. -/
def ProposerDuty.toJson (duty : ProposerDuty) : Json :=
  .mkObj [("pubkey", pubkeyJson duty.pubkey), ("validator_index", uintJson duty.validatorIndex),
    ("slot", uintJson duty.slot)]

/-- The JSON of a sync duty, as the API writes it. -/
def SyncDuty.toJson (duty : SyncDuty) : Json :=
  .mkObj [("pubkey", pubkeyJson duty.pubkey), ("validator_index", uintJson duty.validatorIndex),
    ("validator_sync_committee_indices",
      .arr (duty.validatorSyncCommitteeIndices.map uintJson).toArray)]

/-- The JSON of a PTC duty, as the API writes it. -/
def PtcDuty.toJson (duty : PtcDuty) : Json :=
  .mkObj [("pubkey", pubkeyJson duty.pubkey), ("validator_index", uintJson duty.validatorIndex),
    ("slot", uintJson duty.slot)]

/-! ## Errors -/

/-- The error of an epoch that the state cannot answer for, with code 400. -/
def invalidEpoch (epoch : Epoch) : ErrorMessage :=
  { code := 400, message := s!"Invalid epoch: {epoch.toNat}" }

/-- The error of an index that names no validator of the state, with code 400. -/
def invalidIndex (index : ValidatorIndex) : ErrorMessage :=
  { code := 400, message := s!"Invalid validator index: {index.toNat}" }

/-- The error of a request that names no validator, with code 400.

The source asks for at least one index. -/
def emptyIndices : ErrorMessage :=
  { code := 400, message := "Empty validator index list" }

/-- Whether the state can answer for the committees of an epoch, or the error with code 400.

The epoch must be at most the next one.

The mixes of the state must still hold its seed, as for the committees answer. -/
def checkDutyEpoch (state : BeaconState preset fork) (epoch : Epoch) :
    Except ErrorMessage Unit := do
  let current := (getCurrentEpoch state).toNat
  unless epoch.toNat ≤ current + 1 do throw (invalidEpoch epoch)
  unless current + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat do
    throw (invalidEpoch epoch)

/-- The error body of a failed duty: code 400 for an epoch out of range, else code 500. -/
def dutyError (epoch : Epoch) : ValidatorDutyError → ErrorMessage
  | .epochTooFar .. | .periodOutOfRange .. => invalidEpoch epoch
  | fault => internalError (reprStr fault.code)

/-- The validator at an index of the registry, or the error with code 400. -/
def requestedValidator (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except ErrorMessage Validator :=
  (getValidator state index).mapError fun _ => invalidIndex index

/-! ## Attester duties -/

/-- The attester duty of a validator in an epoch, or none when it sits in no committee of it.

The epoch must be at most the next one, or the answer is the error with code 400.

The index must name a validator of the state, or the answer is the error with code 400. -/
def attesterDuty (state : BeaconState preset fork) (epoch : Epoch) (index : ValidatorIndex) :
    Except ErrorMessage (Option AttesterDuty) := do
  let validator ← requestedValidator state index
  match ← (getCommitteeAssignment state epoch index).mapError (dutyError epoch) with
  | none => return none
  | some (committee, committeeIndex, slot) =>
    return some {
      pubkey := validator.pubkey
      validatorIndex := index
      committeeIndex
      committeeLength := committee.size.toUInt64
      committeesAtSlot := getCommitteeCountPerSlot state epoch
      validatorCommitteeIndex := (committee.idxOf index).toUInt64
      slot }

/-- The attester duties of the requested validators in an epoch, in the order of the request.

A validator in no committee of the epoch has no duty.

An empty request, or an epoch the state cannot answer for, gives the error with code 400. -/
def attesterDuties (state : BeaconState preset fork) (epoch : Epoch)
    (indices : List ValidatorIndex) : Except ErrorMessage (List AttesterDuty) := do
  if indices.isEmpty then throw emptyIndices
  checkDutyEpoch state epoch
  return (← indices.mapM (attesterDuty state epoch)).filterMap id

/-! ## Proposer duties -/

/-- The proposers of the slots of an epoch, in slot order.

From Fulu they are read from the lookahead of the state, as the proposer of a slot is.

The epoch must then be the current one or one of the seed lookahead.

Before Fulu they are drawn for the current epoch only.

Another epoch gives the error with code 400. -/
def epochProposers (state : BeaconState preset fork) (epoch : Epoch) :
    Except ErrorMessage (List ValidatorIndex) := do
  let current := getCurrentEpoch state
  if fulu : .fusaka ≤ fork then
    unless current ≤ epoch ∧ epoch.toNat ≤ current.toNat + preset.MIN_SEED_LOOKAHEAD.toNat do
      throw (invalidEpoch epoch)
    let offset := (epoch.toNat - current.toNat) * preset.SLOTS_PER_EPOCH.toNat
    return ((state.proposerLookahead fulu).toList.drop offset).take preset.SLOTS_PER_EPOCH.toNat
  else
    unless epoch = current do throw (invalidEpoch epoch)
    let proposers ← (getBeaconProposerIndices state epoch).mapError fun fault =>
      internalError (reprStr fault)
    return proposers.toList

/-- The proposer duties of an epoch, one for each slot, in slot order. -/
def proposerDuties (state : BeaconState preset fork) (epoch : Epoch) :
    Except ErrorMessage (List ProposerDuty) := do
  let proposers ← epochProposers state epoch
  let start ← (computeStartSlotAtEpoch preset epoch).mapError fun fault =>
    internalError (reprStr fault)
  proposers.zipIdx.mapM fun (proposer, offset) => do
    let slot ← (addChecked start offset.toUInt64).mapError fun fault =>
      internalError (reprStr fault)
    let validator ← (getValidator state proposer).mapError fun fault =>
      internalError (reprStr fault)
    return { pubkey := validator.pubkey, validatorIndex := proposer, slot }

/-! ## Sync duties -/

/-- The seats of a key in a sync committee, in order. -/
def syncSeats (committee : SyncCommittee preset) (pubkey : BLSPubkey) : List UInt64 :=
  ((committee.pubkeys.toList.zipIdx).filter (·.1 == pubkey)).map (·.2.toUInt64)

/-- From Altair: the sync duty of a validator in the committee of a period, or none.

A validator with no seat in the committee has no duty. -/
def syncDuty (state : BeaconState preset fork) (committee : SyncCommittee preset)
    (index : ValidatorIndex) : Except ErrorMessage (Option SyncDuty) := do
  let validator ← requestedValidator state index
  match syncSeats committee validator.pubkey with
  | [] => return none
  | seats =>
    return some { pubkey := validator.pubkey, validatorIndex := index,
                  validatorSyncCommitteeIndices := seats }

/-- From Altair: the sync duties of the requested validators in the period of an epoch.

The period must be the current one or the next, or the answer is the error with code 400.

So does an empty request. -/
def syncDuties (state : BeaconState preset fork) (altair : .altair ≤ fork) (epoch : Epoch)
    (indices : List ValidatorIndex) : Except ErrorMessage (List SyncDuty) := do
  if indices.isEmpty then throw emptyIndices
  let committee ← syncCommitteeOf state altair epoch
  return (← indices.mapM (syncDuty state committee)).filterMap id

/-! ## PTC duties -/

/-- From Gloas: the PTC duty of a validator in an epoch, or none when it sits in no committee.

The epoch must be at most the seed lookahead after the current one, or the error has code 400. -/
def ptcDuty (config : Config) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (epoch : Epoch) (index : ValidatorIndex) : Except ErrorMessage (Option PtcDuty) := do
  let validator ← requestedValidator state index
  match ← (getPtcAssignment config state gloas epoch index).mapError (dutyError epoch) with
  | none => return none
  | some slot => return some { pubkey := validator.pubkey, validatorIndex := index, slot }

/-- From Gloas: the PTC duties of the requested validators in an epoch, in request order.

An empty request, or an epoch the state cannot answer for, gives the error with code 400.

The window of the state holds the committees from the previous epoch on, from Gloas.

The source asks for distinct indices, so a repeated one gives the error with code 400 too. -/
def ptcDuties (config : Config) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (epoch : Epoch) (indices : List ValidatorIndex) : Except ErrorMessage (List PtcDuty) := do
  if indices.isEmpty then throw emptyIndices
  checkDutyEpoch state epoch
  if epoch.toNat + 1 < (getCurrentEpoch state).toNat ∨ epoch < config.GLOAS_FORK_EPOCH then
    throw (invalidEpoch epoch)
  unless indices.Nodup do throw { code := 400, message := "Repeated validator index" }
  return (← indices.mapM (ptcDuty config state gloas epoch)).filterMap id

/-! ## Dependent roots -/

/-- The error body of a failed root read: code 400 for a slot out of range, else code 500. -/
def rootError (epoch : Epoch) : AccessorError → ErrorMessage
  | .slotOutOfRange .. => invalidEpoch epoch
  | fault => internalError (reprStr fault)

/-- The root of the block that the duties of an epoch depend on.

It is the root at the last slot before the epoch that lies a lag before the given one.

On underflow, before the first epoch or slot, it is the root of the genesis block.

The state must be past that slot and still hold its root, or the error has code 400.

A slot past 64 bits gives the error with code 500. -/
def dependentRoot (state : BeaconState preset fork) (lag : Nat) (epoch : Epoch)
    (genesisRoot : Root) : Except ErrorMessage Root := do
  if epoch.toNat < lag then return genesisRoot
  let start ← (computeStartSlotAtEpoch preset (epoch - lag.toUInt64)).mapError fun fault =>
    internalError (reprStr fault)
  if start = 0 then return genesisRoot
  (getBlockRootAtSlot state (start - 1)).mapError (rootError epoch)

/-! ## Responses -/

/-- Which duties a request asks for. -/
inductive DutyKind where
  /-- The attester duties of some validators. -/
  | attester
  /-- The proposer duties, with the dependent root of the first version of the endpoint. -/
  | proposerV1
  /-- The proposer duties, with the dependent root of the second version of the endpoint. -/
  | proposerV2
  /-- The sync committee duties of some validators. -/
  | sync
  /-- The PTC duties of some validators. -/
  | ptc
  deriving DecidableEq, Repr

/-- The response of a duties endpoint, without the flag that comes from the store.

The sync answer has no dependent root; the proposer answers take no indices.

The first proposer answer is for the current epoch only.

The root of a later epoch is that of a slot the state has not reached.

The sync answer needs Altair and the PTC answer Gloas, or the error has code 400. -/
def dutiesResponse (config : Config) (state : BeaconState preset fork) (kind : DutyKind)
    (epoch : Epoch) (indices : List ValidatorIndex) (genesisRoot : Root) :
    Except ErrorMessage ApiEnvelope :=
  match kind with
  | .attester => do
    let duties ← attesterDuties state epoch indices
    return { dependentRoot := some (← dependentRoot state 1 epoch genesisRoot),
             data := .arr (duties.map AttesterDuty.toJson).toArray }
  | .proposerV1 => do
    unless epoch = getCurrentEpoch state do throw (invalidEpoch epoch)
    let duties ← proposerDuties state epoch
    return { dependentRoot := some (← dependentRoot state 0 epoch genesisRoot),
             data := .arr (duties.map ProposerDuty.toJson).toArray }
  | .proposerV2 => do
    let duties ← proposerDuties state epoch
    return { dependentRoot := some (← dependentRoot state 1 epoch genesisRoot),
             data := .arr (duties.map ProposerDuty.toJson).toArray }
  | .sync =>
    if altair : .altair ≤ fork then do
      let duties ← syncDuties state altair epoch indices
      return { data := .arr (duties.map SyncDuty.toJson).toArray }
    else .error (beforeFork "sync duties" .altair)
  | .ptc =>
    if gloas : .glamsterdam ≤ fork then do
      let duties ← ptcDuties config state gloas epoch indices
      return { dependentRoot := some (← dependentRoot state 1 epoch genesisRoot),
               data := .arr (duties.map PtcDuty.toJson).toArray }
    else .error (beforeFork "PTC duties" .glamsterdam)

end EthLib.Consensus.BeaconApi
