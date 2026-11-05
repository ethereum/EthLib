module

public import EthLib.Consensus.PayloadTimeliness

/-!
# `Consensus.Proposers`

From Fulu: the proposers of every slot of an epoch, and the lookahead of proposers in the state.

The state keeps the proposers of the current epoch and of the epochs of the seed lookahead.

At each epoch boundary the lookahead moves by one epoch, and its last epoch is computed anew.

The proposer of a slot is drawn from the candidates with a seed of its slot.

The draw walks the candidates in shuffled order, each with a chance that grows with its balance.

From Gloas the draw is a balance-weighted selection of one candidate, on the same random bytes.

From Gloas a slashed validator is not a candidate.

A 64-bit overflow, or a slot with no candidate, is an error.

[EIP-7917] adds the lookahead, and [EIP-8045] drops slashed proposers.

[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
[EIP-8045]: https://eips.ethereum.org/EIPS/eip-8045#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- The seed of the proposer draw of a slot: the hash of the epoch's seed and the slot. -/
def proposerSlotSeed (seed : Bytes32) (slot : Slot) : Bytes32 :=
  sha256Bytes32 ⟨seed.toArray ++ (uintToBytes 8 slot.toNat).toArray⟩

/-- The proposer of a slot, drawn from candidates with the seed of the slot.

Before Gloas it is the proposer draw; from Gloas, a balance-weighted selection of one. -/
def computeSlotProposer (state : BeaconState preset fork) (indices : Array ValidatorIndex)
    (seed : Bytes32) : Except AccessorError ValidatorIndex := do
  if .glamsterdam ≤ fork then
    let selected ← computeBalanceWeightedSelection state indices seed 1 true
    return selected[0]
  else computeProposerIndex state indices seed

/-- The proposers of the slots of an epoch, drawn from candidates with a seed of the epoch. -/
def computeProposerIndices (state : BeaconState preset fork) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) :
    Except AccessorError (Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat) := do
  let start ← liftArith (computeStartSlotAtEpoch preset epoch)
  (Vector.range _).mapM fun offset => do
    let slot ← liftArith (addChecked start offset.toUInt64)
    computeSlotProposer state indices (proposerSlotSeed seed slot)

/-- The candidates to propose in an epoch: its active validators, unslashed from Gloas. -/
def proposerCandidates (state : BeaconState preset fork) (epoch : Epoch) : Array ValidatorIndex :=
  let active := (getActiveValidatorIndices state epoch).toArray
  if .glamsterdam ≤ fork then
    active.filter fun index =>
      match state.validators.data[index.toNat]? with
      | some validator => !validator.slashed
      | none => true
  else active

/-- The proposers of the slots of an epoch. -/
def getBeaconProposerIndices (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError (Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat) := do
  let seed ← getSeed state epoch DOMAIN_BEACON_PROPOSER
  computeProposerIndices state epoch seed (proposerCandidates state epoch)

/-- The state with its lookahead of proposers moved by one epoch.

The last epoch of the lookahead becomes the epoch after the seed lookahead. -/
def processProposerLookahead (state : BeaconState preset fork) (fulu : .fusaka ≤ fork) :
    Except AccessorError (BeaconState preset fork) := do
  let lookahead := state.proposerLookahead fulu
  let perEpoch := preset.SLOTS_PER_EPOCH.toNat
  let epoch ← liftArith do
    addChecked (← addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD) 1
  let last ← getBeaconProposerIndices state epoch
  let moved := Vector.ofFn fun (position : Fin _) =>
    if kept : position.val + perEpoch < lookahead.size then lookahead[position.val + perEpoch]
    else last[position.val + perEpoch - lookahead.size]'(by
      have := position.isLt
      simp only [Vector.size] at kept ⊢
      omega)
  return { state with proposerLookahead := fun _ => moved }

end EthLib.Consensus
