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

[duties endpoints]: https://github.com/ethereum/beacon-APIs/tree/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/duties
[types]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/duty.yaml
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
  .str (toHex ⟨pubkey.toArray⟩)

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
  -- The example message of the source, with the epoch.
  { code := 400, message := s!"Invalid epoch: {epoch.toNat}" }

/-- The error of an index that names no validator of the state, with code 400. -/
def invalidIndex (index : ValidatorIndex) : ErrorMessage :=
  -- The source: code 400 for an invalid index; the message is EthLib's.
  { code := 400, message := s!"Invalid validator index: {index.toNat}" }

/-- The error of a request that names no validator, with code 400. -/
def emptyIndices : ErrorMessage :=
  -- The source asks for at least one index; the message is EthLib's.
  { code := 400, message := "Empty validator index list" }

/-- Whether the state can answer for the committees of an epoch, or the error with code 400. -/
def checkDutyEpoch (state : BeaconState preset fork) (epoch : Epoch) :
    Except ErrorMessage Unit := do
  let current := (getCurrentEpoch state).toNat
  -- The source: at most one epoch ahead, epoch <= current + 1.
  unless epoch.toNat ≤ current + 1 do throw (invalidEpoch epoch)
  -- EthLib's choice: the mixes of the state must still hold the seed, as for the committees answer.
  --
  -- That holds when current + seed lookahead + 1 < epoch + length of the buffer of mixes.
  unless current + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat do
    throw (invalidEpoch epoch)

/-- The error body of a failed duty: code 400 for an epoch out of range, else code 500. -/
def dutyError (epoch : Epoch) : ValidatorDutyError → ErrorMessage
  -- An epoch or a period out of range: the invalid epoch of the source.
  | .epochTooFar .. | .periodOutOfRange .. => invalidEpoch epoch
  -- Any other failure is internal.
  | fault => internalError (toString fault.code.toNat)

/-- The validator at an index of the registry, or the error with code 400. -/
def requestedValidator (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except ErrorMessage Validator :=
  -- The source: an index that names no validator is an invalid index, code 400.
  (getValidator state index).mapError fun _ => invalidIndex index

/-! ## Attester duties -/

/-- The attester duty of a validator in an epoch, or none when it sits in no committee of it. -/
def attesterDuty (state : BeaconState preset fork) (epoch : Epoch) (index : ValidatorIndex) :
    Except ErrorMessage (Option AttesterDuty) := do
  -- The index must name a validator of the state, else code 400.
  let validator ← requestedValidator state index
  -- Its committee, its index and its slot in the epoch, which is at most the next one, else 400.
  match ← (getCommitteeAssignment state epoch index).mapError (dutyError epoch) with
  -- A validator in no committee of the epoch has no duty.
  | none => return none
  | some (committee, committeeIndex, slot) =>
    -- The fields of the attester duty, as the source defines it.
    return some {
      pubkey := validator.pubkey
      validatorIndex := index
      committeeIndex
      committeeLength := committee.size.toUInt64
      committeesAtSlot := getCommitteeCountPerSlot state epoch
      validatorCommitteeIndex := (committee.idxOf index).toUInt64
      slot }

/-- The attester duties of the requested validators in an epoch, in the order of the request. -/
def attesterDuties (state : BeaconState preset fork) (epoch : Epoch)
    (indices : List ValidatorIndex) : Except ErrorMessage (List AttesterDuty) := do
  -- The source: at least one index, else code 400.
  if indices.isEmpty then throw emptyIndices
  -- An epoch that the state cannot answer for: code 400.
  checkDutyEpoch state epoch
  -- The duty of each requested validator in turn; the first index that fails ends the answer.
  return (← indices.mapM (attesterDuty state epoch)).filterMap id

/-! ## Proposer duties -/

/-- The proposers of the slots of an epoch, in slot order. -/
def epochProposers (state : BeaconState preset fork) (epoch : Epoch) :
    Except ErrorMessage (List ValidatorIndex) := do
  let current := getCurrentEpoch state
  if fulu : .fusaka ≤ fork then
    -- From Fulu: the epoch is the current one or one of the seed lookahead, else code 400.
    --
    -- The source names no range of epochs, so the range is that of the lookahead of the state.
    unless current ≤ epoch ∧ epoch.toNat ≤ current.toNat + preset.MIN_SEED_LOOKAHEAD.toNat do
      throw (invalidEpoch epoch)
    -- The proposers are read from the lookahead of the state, as the proposer of a slot is.
    --
    -- The slots of the epoch start at (epoch - current) * slots per epoch in that lookahead.
    let offset := (epoch.toNat - current.toNat) * preset.SLOTS_PER_EPOCH.toNat
    return ((state.proposerLookahead fulu).toList.drop offset).take preset.SLOTS_PER_EPOCH.toNat
  else
    -- Before Fulu: the current epoch only, else code 400, EthLib's choice.
    unless epoch = current do throw (invalidEpoch epoch)
    -- The proposers drawn for the current epoch; a failure gives code 500.
    let proposers ← (getBeaconProposerIndices state epoch).mapError fun _ =>
      internalError "no proposers"
    return proposers.toList

/-- The proposer duties of an epoch, one for each slot, in slot order. -/
def proposerDuties (state : BeaconState preset fork) (epoch : Epoch) :
    Except ErrorMessage (List ProposerDuty) := do
  let proposers ← epochProposers state epoch
  -- The first slot of the epoch; an overflow gives code 500.
  let start ← (computeStartSlotAtEpoch preset epoch).mapError fun _ =>
    internalError "no start slot"
  proposers.zipIdx.mapM fun (proposer, offset) => do
    -- The slot of the proposer: the first slot of the epoch plus its offset.
    let slot ← (addChecked start offset.toUInt64).mapError fun _ =>
      internalError "no slot"
    -- The key of the proposer, from the registry.
    let validator ← (getValidator state proposer).mapError fun _ =>
      internalError "no proposer"
    return { pubkey := validator.pubkey, validatorIndex := proposer, slot }

/-! ## Sync duties -/

/-- The seats of a key in a sync committee, in order. -/
def syncSeats (committee : SyncCommittee preset) (pubkey : BLSPubkey) : List UInt64 :=
  -- Each position of the committee that holds the key: a key may hold several seats.
  ((committee.pubkeys.toList.zipIdx).filter (·.1 == pubkey)).map (·.2.toUInt64)

/-- From Altair: the sync duty of a validator in the committee of a period, or none. -/
def syncDuty (state : BeaconState preset fork) (committee : SyncCommittee preset)
    (index : ValidatorIndex) : Except ErrorMessage (Option SyncDuty) := do
  -- The index must name a validator of the state, else code 400.
  let validator ← requestedValidator state index
  match syncSeats committee validator.pubkey with
  -- A validator with no seat in the committee has no duty.
  | [] => return none
  | seats =>
    -- The fields of the sync committee duty, as the source defines it.
    return some { pubkey := validator.pubkey, validatorIndex := index,
                  validatorSyncCommitteeIndices := seats }

/-- From Altair: the sync duties of the requested validators in the period of an epoch. -/
def syncDuties (state : BeaconState preset fork) (altair : .altair ≤ fork) (epoch : Epoch)
    (indices : List ValidatorIndex) : Except ErrorMessage (List SyncDuty) := do
  -- The source: at least one index, else code 400.
  if indices.isEmpty then throw emptyIndices
  -- The source: p(epoch) <= p(current) + 1, with p the sync committee period of an epoch.
  --
  -- EthLib's choice: an earlier period also gives code 400, since the state holds no other.
  let committee ← syncCommitteeOf state altair epoch
  -- The duty of each requested validator in turn; the first index that fails ends the answer.
  return (← indices.mapM (syncDuty state committee)).filterMap id

/-! ## PTC duties -/

/-- From Gloas: the PTC duty of a validator in an epoch, or none when it sits in no committee. -/
def ptcDuty (config : Config) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (epoch : Epoch) (index : ValidatorIndex) : Except ErrorMessage (Option PtcDuty) := do
  -- The index must name a validator of the state, else code 400.
  let validator ← requestedValidator state index
  -- The epoch must be at most the seed lookahead after the current one, else code 400.
  match ← (getPtcAssignment config state gloas epoch index).mapError (dutyError epoch) with
  -- A validator in no committee of the epoch has no duty.
  | none => return none
  -- The fields of the PTC duty, as the source defines it.
  --
  -- Its slot is the first one whose committee holds the validator.
  | some slot => return some { pubkey := validator.pubkey, validatorIndex := index, slot }

/-- From Gloas: the PTC duties of the requested validators in an epoch, in request order. -/
def ptcDuties (config : Config) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (epoch : Epoch) (indices : List ValidatorIndex) : Except ErrorMessage (List PtcDuty) := do
  -- The source: at least one index, else code 400.
  if indices.isEmpty then throw emptyIndices
  -- The source: not after the next epoch; EthLib also asks that the mixes hold the seed.
  checkDutyEpoch state epoch
  -- The window of the state holds the committees from the previous epoch on, from Gloas.
  --
  -- EthLib's choice: an epoch before the previous one, outside that window, gives code 400.
  --
  -- So does an epoch before the Gloas fork epoch, which has no PTC.
  if epoch.toNat + 1 < (getCurrentEpoch state).toNat ∨ epoch < config.GLOAS_FORK_EPOCH then
    throw (invalidEpoch epoch)
  -- The source asks for distinct indices, so a repeated one gives code 400 too.
  --
  -- One pass with a search tree finds a repeat, in `O(n log n)` for `n` indices.
  unless (firstRepeated indices).isNone do
    throw { code := 400, message := "Repeated validator index" }
  -- The duty of each requested validator in turn; the first index that fails ends the answer.
  return (← indices.mapM (ptcDuty config state gloas epoch)).filterMap id

/-! ## Dependent roots -/

/-- The error body of a failed root read: code 400 for a slot out of range, else code 500. -/
def rootError (epoch : Epoch) : AccessorError → ErrorMessage
  -- A slot that the state is not past, or whose root it does not hold: an invalid epoch.
  | .slotOutOfRange .. => invalidEpoch epoch
  | _ => internalError "no block root"

/-- The root of the block that the duties of an epoch depend on. -/
def dependentRoot (state : BeaconState preset fork) (lag : Nat) (epoch : Epoch)
    (genesisRoot : Root) : Except ErrorMessage Root := do
  -- The source: the root of the block at slot start(epoch - lag) - 1.
  --
  -- Here start(e) is the first slot of epoch e.
  --
  -- The lag is 1, or 0 where the root is the one at start(epoch) - 1.
  --
  -- The source: on underflow, before the first epoch or slot, the root of the genesis block.
  if epoch.toNat < lag then return genesisRoot
  -- A slot past 64 bits gives code 500.
  let start ← (computeStartSlotAtEpoch preset (epoch - lag.toUInt64)).mapError fun _ =>
    internalError "no start slot"
  if start = 0 then return genesisRoot
  -- The state must be past that slot and still hold its root, else code 400.
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

For the Gloas fork epoch, the PTC root follows the [PTC duties endpoint][ptc].

Up to the Fulu fork epoch, the second proposer root is that of the first version.

[ptc]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/validator/duties/ptc.yaml#L19-L27
-/
def dutiesResponse (config : Config) (state : BeaconState preset fork) (kind : DutyKind)
    (epoch : Epoch) (indices : List ValidatorIndex) (genesisRoot : Root) :
    Except ErrorMessage ApiEnvelope :=
  match kind with
  | .attester => do
    let duties ← attesterDuties state epoch indices
    -- The source: the dependent root at slot start(epoch - 1) - 1, and the array of the duties.
    return { dependentRoot := some (← dependentRoot state 1 epoch genesisRoot),
             data := .arr (duties.map AttesterDuty.toJson).toArray }
  | .proposerV1 => do
    -- EthLib's choice: the first proposer answer is for the current epoch only.
    --
    -- The root of a later epoch is that of a slot the state has not reached.
    unless epoch = getCurrentEpoch state do throw (invalidEpoch epoch)
    let duties ← proposerDuties state epoch
    -- The source: the dependent root at slot start(epoch) - 1, and the array of the duties.
    return { dependentRoot := some (← dependentRoot state 0 epoch genesisRoot),
             data := .arr (duties.map ProposerDuty.toJson).toArray }
  | .proposerV2 => do
    let duties ← proposerDuties state epoch
    -- From Fulu, the proposers of an epoch are drawn at the end of the epoch two before it.
    --
    -- So the source gives the root at slot start(epoch - 1) - 1.
    --
    -- The upgrade to Fulu draws the proposers of the fork epoch, after the epoch before it.
    --
    -- So up to the fork epoch, the blocks of the epoch before still change the proposers.
    --
    -- EthLib's rule: there, the root is the one at slot start(epoch) - 1, as before Fulu.
    let lag := if epoch ≤ config.FULU_FORK_EPOCH then 0 else 1
    -- The dependent root at that lag, and the array of the duties.
    return { dependentRoot := some (← dependentRoot state lag epoch genesisRoot),
             data := .arr (duties.map ProposerDuty.toJson).toArray }
  | .sync =>
    if altair : .altair ≤ fork then do
      let duties ← syncDuties state altair epoch indices
      -- The source: the array of the duties, with no dependent root.
      return { data := .arr (duties.map SyncDuty.toJson).toArray }
    -- Before Altair there is no sync committee: code 400.
    else .error (beforeFork "sync duties" .altair)
  | .ptc =>
    if gloas : .glamsterdam ≤ fork then do
      let duties ← ptcDuties config state gloas epoch indices
      -- The PTC of the Gloas fork epoch is computed at the fork, from balances of the epoch before.
      --
      -- So its root is the one at slot start(epoch) - 1, as the PTC duties endpoint says.
      --
      -- Every other epoch has the root at slot start(epoch - 1) - 1.
      let lag := if epoch = config.GLOAS_FORK_EPOCH then 0 else 1
      return { dependentRoot := some (← dependentRoot state lag epoch genesisRoot),
               data := .arr (duties.map PtcDuty.toJson).toArray }
    -- Before Gloas there is no PTC: code 400.
    else .error (beforeFork "PTC duties" .glamsterdam)

end EthLib.Consensus.BeaconApi
