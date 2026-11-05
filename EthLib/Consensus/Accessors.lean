module

public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Time

/-!
# `Consensus.Accessors`

Values that the beacon chain reads from a beacon state.

A validator is active from its activation epoch up to its exit epoch.

The total balance of a set of validators sums their effective balances.

It is never below one effective balance increment, so it can always divide.

A sum of 2^64 or more is an error, as in 64-bit arithmetic.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

/-- An error of a state accessor. -/
inductive AccessorError where
  /-- A validator index names no validator of the registry. -/
  | indexOutOfRange (index : ValidatorIndex)
  /-- A total balance reaches 2^64. -/
  | balanceOverflow
  deriving DecidableEq, Repr

/-- Whether a validator is active in an epoch: from its activation epoch, before its exit epoch. -/
def isActiveValidator (validator : Validator) (epoch : Epoch) : Bool :=
  validator.activationEpoch ≤ epoch && epoch < validator.exitEpoch

variable {preset : Preset} {fork : Base.Fork}

/-- The epoch of the slot of a state. -/
def getCurrentEpoch (state : BeaconState preset fork) : Epoch :=
  computeEpochAtSlot preset state.slot

/-- The indices of the validators active in an epoch, in increasing order. -/
def getActiveValidatorIndices (state : BeaconState preset fork) (epoch : Epoch) :
    List ValidatorIndex :=
  state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isActiveValidator validator epoch then some index.toUInt64 else none

/-- The marks of the validators at some indices: one flag per validator of the registry.

An index outside the registry marks nothing. -/
def markIndices (size : Nat) (indices : List ValidatorIndex) : Array Bool :=
  indices.foldl (fun marked index => marked.set! index.toNat true) (Array.replicate size false)

/-- The sum of the effective balances of the marked validators, on natural numbers. -/
def sumMarked (validators : Array Validator) (marked : Array Bool) : Nat :=
  (validators.zip marked).foldl
    (fun sum (validator, mark) => if mark then sum + validator.effectiveBalance.toNat else sum) 0

/-- The total effective balance of a set of validators, and at least one increment.

The indices form a set, so an index that appears twice counts once.

An index that names no validator is an error. -/
def getTotalBalance (state : BeaconState preset fork) (indices : List ValidatorIndex) :
    Except AccessorError Gwei := do
  let validators := state.validators.data
  if let some index := indices.find? (validators.size ≤ ·.toNat) then
    throw (.indexOutOfRange index)
  let total := sumMarked validators (markIndices validators.size indices)
  if 2 ^ 64 ≤ total then throw .balanceOverflow
  return max preset.EFFECTIVE_BALANCE_INCREMENT total.toUInt64

/-- The total effective balance of the validators active in the epoch of a state. -/
def getTotalActiveBalance (state : BeaconState preset fork) : Except AccessorError Gwei :=
  getTotalBalance state (getActiveValidatorIndices state (getCurrentEpoch state))

end EthLib.Consensus
