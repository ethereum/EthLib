module

public import EthLib.Consensus.Containers.InclusionList
public import EthLib.Consensus.Mutators
public import EthLib.Consensus.PayloadTimeliness

/-!
# `Consensus.InclusionListCommittee`

From Heze: the inclusion list committee of a slot, and the signature of its lists.

The committee takes its sixteen seats from the beacon committees of the slot, in their order.

When the slot has fewer validators than seats, the seats wrap around to the first validator.

A member signs its list under the domain of the committee, at the fork version of the list's epoch.

A validator finds its seat in an epoch up to the next one, since later committees are not fixed.

[EIP-7805](https://eips.ethereum.org/EIPS/eip-7805#consensus-layer) adds the committee.

The EIP names its domain `DOMAIN_IL_COMMITTEE` with the value `0x0C000000`.

Heze uses `DOMAIN_INCLUSION_LIST_COMMITTEE`, with the value `0x10000000`.

EIP-7805 is a Draft on 2026-11-03, so these rules can still change.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The inclusion list committee of a slot.

Seat `i` holds member `i` of the beacon committees of the slot, counted modulo their number.

Those committees share one shuffle of the active validators, computed once for the slot.

A slot whose committees hold no validator has no committee, and that is an error. -/
def getInclusionListCommittee (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError (InclusionListCommittee preset) := do
  let members ← slotCommitteeMembers state slot
  if nonempty : 0 < members.size then
    return Vector.ofFn fun i => members[i.val % members.size]'(Nat.mod_lt _ nonempty)
  else throw .noCandidates

/-- The first of a list of slots whose inclusion list committee holds a validator, if any.

The search stops at that slot, so the committees of later slots are not computed. -/
def firstInclusionListSlot (state : BeaconState preset fork) (validator : ValidatorIndex) :
    List Slot → Except AccessorError (Option Slot)
  | [] => return none
  | slot :: rest => do
    let committee ← getInclusionListCommittee state slot
    if validator ∈ committee.toList then return some slot
    else firstInclusionListSlot state validator rest

/-- The slot of an epoch in which a validator sits on the inclusion list committee, if any.

The epoch can be at most the next epoch of the state, since later committees are not fixed yet.

A validator with seats in several slots gets the first of them. -/
def getInclusionListCommitteeAssignment (state : BeaconState preset fork) (epoch : Epoch)
    (validator : ValidatorIndex) : Except AccessorError (Option Slot) := do
  let nextEpoch ← liftArith (addChecked (getCurrentEpoch state) 1)
  if nextEpoch < epoch then throw (.epochTooFar epoch nextEpoch)
  firstInclusionListSlot state validator (← liftArith (epochSlots preset epoch))

/-- The root that a member signs for an inclusion list, on the chain of a state.

The domain is that of the inclusion list committee, at the fork version of the list's epoch. -/
def inclusionListSigningRoot (config : Config) (state : BeaconState preset fork)
    (list : InclusionList) : Except Err Root := do
  let version := config.computeForkVersion (computeEpochAtSlot preset list.slot)
  let domain ← computeDomain config DOMAIN_INCLUSION_LIST_COMMITTEE version
    state.genesisValidatorsRoot
  computeSigningRoot list domain

/-- Whether the signature of an inclusion list is that of its member, under the member's key.

A member index outside the registry is an error. -/
def isValidInclusionListSignature (config : Config) (state : BeaconState preset fork)
    (signed : SignedInclusionList) : Except AccessorError Bool := do
  let validator ← getValidator state signed.message.validatorIndex
  let root ← (inclusionListSigningRoot config state signed.message).mapError fun _ => .ssz
  return Signatures.verify (packBytes validator.pubkey) (packBytes root)
    (packBytes signed.signature)

/-- An error of a member that signs an inclusion list. -/
inductive InclusionListSigningError where
  /-- The root of the list has no value. -/
  | root (error : Err)
  /-- The BLS signature fails. -/
  | bls (error : BlsError)

/-- The signature of an inclusion list by a member with a secret key. -/
def getInclusionListSignature (config : Config) (state : BeaconState preset fork)
    (list : InclusionList) (key : Signatures.SecretKey) :
    Except InclusionListSigningError BLSSignature := do
  let root ← (inclusionListSigningRoot config state list).mapError .root
  (Signatures.sign key (packBytes root)).mapError .bls

end EthLib.Consensus
