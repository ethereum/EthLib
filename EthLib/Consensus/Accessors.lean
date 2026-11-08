module

public import EthLib.Base.LittleEndian
public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Shuffle
public import EthLib.Consensus.Signing
public import EthLib.Consensus.Time

/-!
# `Consensus.Accessors`

Values that the beacon chain reads from a beacon state.

A validator is active from its activation epoch up to its exit epoch.

The total balance of a set of validators sums their effective balances.

It is never below one effective balance increment, so it can always divide.

A sum of 2^64 or more is an error, as in 64-bit arithmetic.

The committees cut the shuffled active validators of an epoch, and the proposer is drawn from them.

A failed assertion of the rule, or a read past the end of a list, is an error.

A division by a parameter of the preset or the configuration assumes that it is not zero.

A read or a write of a circular buffer of length zero is an error.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

/-- An error of a state accessor. -/
inductive AccessorError where
  /-- A validator index names no validator of the registry. -/
  | indexOutOfRange (index : ValidatorIndex)
  /-- A total balance reaches 2^64. -/
  | balanceOverflow
  /-- The slot is not one of the recent slots whose block root the state keeps. -/
  | slotOutOfRange (slot stateSlot : Slot)
  /-- A 64-bit operation has no result. -/
  | arith (error : ArithError)
  /-- A shuffle or a committee has no value. -/
  | shuffle (error : ShuffleError)
  /-- The root of a fork has no value. -/
  | ssz
  /-- There is no candidate to draw a proposer from. -/
  | noCandidates
  /-- An attestation has no bit at a position of its committees. -/
  | bitOutOfRange (position : Nat)
  /-- An attestation has more attesters than its indexed form can list. -/
  | tooManyAttesters (count limit : Nat)
  /-- The rule at this fork is not yet in EthLib, so no older rule stands in for it. -/
  | forkNotYetSpecified (fork : Base.Fork)
  /-- The epoch is past the next epoch, whose duties the state does not fix yet. -/
  | epochTooFar (epoch nextEpoch : Epoch)
  /-- From Gloas: a builder index names no builder of the registry. -/
  | builderIndexOutOfRange (index : BuilderIndex)
  /-- From Gloas: a position is past the end of the pending builder payments. -/
  | paymentIndexOutOfRange (index : UInt64)
  /-- From Gloas: the window of payload committees holds no committee for the slot. -/
  | ptcSlotOutOfRange (slot stateSlot : Slot)
  /-- From Electra: a list of the state that has a limit is full. -/
  | listFull (limit : Nat)
  /-- The epoch is neither the previous nor the current epoch. -/
  | epochNotRecent (epoch previous current : Epoch)
  /-- From Altair: the public keys to aggregate are none, or one of them is not valid. -/
  | invalidPubkeys
  /-- From Altair: the source of an attestation is not the justified checkpoint it should vote for.
  -/
  | wrongSource
  /-- From Gloas: an attestation for the block of its own slot has a nonzero index. -/
  | sameSlotIndexNotZero (index : CommitteeIndex)
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
  indices.foldl (fun marked index => marked.setIfInBounds index.toNat true)
    (Array.replicate size false)

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

/-- An error of a 64-bit operation, as an error of an accessor. -/
def liftArith {α : Type} (result : Except ArithError α) : Except AccessorError α :=
  result.mapError .arith

/-- The position `i mod n` is below `n`, for `n ≠ 0`. -/
theorem toNat_mod_lt {i n : UInt64} (nonzero : n ≠ 0) : (i % n).toNat < n.toNat := by
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun zero => nonzero (UInt64.toNat_inj.mp (by simpa)))

/-- The entry at position `i mod n` of a circular buffer of length `n`.

A buffer of length zero has no entry, so the read is a division-by-zero error. -/
def readCircular {α : Type} {n : UInt64} (buffer : Vector α n.toNat) (i : UInt64) :
    Except AccessorError α :=
  if nonzero : n = 0 then .error (.arith .divisionByZero)
  else .ok (buffer[(i % n).toNat]'(toNat_mod_lt nonzero))

/-- A circular buffer of length `n` with the entry at position `i mod n` replaced.

A buffer of length zero has no entry to replace, so the write is a division-by-zero error. -/
def writeCircular {α : Type} {n : UInt64} (buffer : Vector α n.toNat) (i : UInt64) (value : α) :
    Except AccessorError (Vector α n.toNat) :=
  if nonzero : n = 0 then .error (.arith .divisionByZero)
  else .ok (buffer.set (i % n).toNat value (toNat_mod_lt nonzero))

/-- A circular buffer of length `n` that keeps its Merkle tree, with entry `i mod n` replaced.

It writes the entry as the plain buffer does, then rehashes the path above it. -/
def writeCircularRooted {α : Type} [SszType α] {n : UInt64} (buffer : RootedVector α n.toNat)
    (i : UInt64) (value : α) : Except AccessorError (RootedVector α n.toNat) :=
  if nonzero : n = 0 then .error (.arith .divisionByZero)
  else .ok (buffer.set (i % n).toNat value (toNat_mod_lt nonzero))

/-- One step of the pass that drops repeats: keep an index unless it repeats the last one. -/
def keepNew (kept : List ValidatorIndex) (index : ValidatorIndex) : List ValidatorIndex :=
  match kept with
  | last :: _ => if last = index then kept else index :: kept
  | [] => [index]

/-- A list of indices as a set: sorted, with each index once. -/
def sortedSet (indices : List ValidatorIndex) : List ValidatorIndex :=
  -- After the sort, equal indices are adjacent, so one pass drops the repeats.
  ((indices.mergeSort (· ≤ ·)).foldl keepNew []).reverse

/-- Whether a validator may join the activation queue.

It must not be in the queue yet.

Before Electra it needs the largest effective balance.

From Electra it needs at least the activation balance, as [EIP-7251] specifies.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/
def isEligibleForActivationQueue (preset : Preset) (fork : Base.Fork) (validator : Validator) :
    Bool :=
  validator.activationEligibilityEpoch == FAR_FUTURE_EPOCH &&
    if .pectra ≤ fork then preset.MIN_ACTIVATION_BALANCE ≤ validator.effectiveBalance
    else validator.effectiveBalance == preset.MAX_EFFECTIVE_BALANCE

/-- Whether a validator in the activation queue may be activated.

Its place in the queue must be finalized, and it must not be activated yet. -/
def isEligibleForActivation (state : BeaconState preset fork) (validator : Validator) : Bool :=
  validator.activationEligibilityEpoch ≤ state.finalizedCheckpoint.epoch &&
    validator.activationEpoch == FAR_FUTURE_EPOCH

/-- Whether a validator may be slashed in an epoch.

It must not be slashed yet, and the epoch must be from its activation and before it can withdraw. -/
def isSlashableValidator (validator : Validator) (epoch : Epoch) : Bool :=
  !validator.slashed && validator.activationEpoch ≤ epoch && epoch < validator.withdrawableEpoch

/-- The epoch before the epoch of a state, or the genesis epoch at genesis. -/
def getPreviousEpoch (state : BeaconState preset fork) : Epoch :=
  saturatingSub (getCurrentEpoch state) 1

/-- The root of the block at a recent slot.

The slot must be before the slot of the state, by at most the length of the buffer of roots. -/
def getBlockRootAtSlot (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError Root := do
  unless slot < state.slot do throw (.slotOutOfRange slot state.slot)
  unless state.slot ≤ (← liftArith (addChecked slot preset.SLOTS_PER_HISTORICAL_ROOT)) do
    throw (.slotOutOfRange slot state.slot)
  readCircular state.blockRoots.elements slot

/-- The root of the block at the first slot of a recent epoch. -/
def getBlockRoot (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError Root := do
  getBlockRootAtSlot state (← liftArith (computeStartSlotAtEpoch preset epoch))

/-- The RANDAO mix of a recent epoch. -/
def getRandaoMix (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError Bytes32 :=
  readCircular state.randaoMixes.elements epoch

/-- The most validators that may join, or leave, the active validators in one epoch.

It is a fixed share of the active validators, and at least a fixed minimum.

Electra counts the churn in balance instead, as [EIP-7251] specifies.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/
def getValidatorChurnLimit (config : Config) (state : BeaconState preset fork) : UInt64 :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT
    ((getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64 /
      config.CHURN_LIMIT_QUOTIENT)

/-- From Deneb: the most validators that an epoch activates.

It is the churn limit, up to a maximum, as [EIP-7514] specifies.

[EIP-7514]: https://eips.ethereum.org/EIPS/eip-7514#specification
-/
def getValidatorActivationChurnLimit (config : Config) (state : BeaconState preset fork) :
    UInt64 :=
  min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT (getValidatorChurnLimit config state)

/-- From Electra: the sum of the amounts of the pending partial withdrawals of a validator.

A sum of 2^64 or more is an error. -/
def getPendingBalanceToWithdraw (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (index : ValidatorIndex) : Except AccessorError Gwei :=
  let total := ((state.pendingPartialWithdrawals electra).data.toList.map fun withdrawal =>
    if withdrawal.validatorIndex = index then withdrawal.amount.toNat else 0).sum
  if total < 2 ^ 64 then .ok total.toUInt64 else .error .balanceOverflow

/-- The seed of an epoch for one kind of duty.

It is the SHA-256 hash of the domain type, the epoch as 8 bytes little-endian, and a RANDAO mix.

The mix is that of the epoch `MIN_SEED_LOOKAHEAD + 1` epochs before, so it is known in advance. -/
def getSeed (state : BeaconState preset fork) (epoch : Epoch) (domainType : DomainType) :
    Except AccessorError Bytes32 := do
  -- The length of the buffer comes first, so that no step goes below zero near genesis.
  let shifted ← liftArith do
    subChecked (← subChecked (← addChecked epoch preset.EPOCHS_PER_HISTORICAL_VECTOR)
      preset.MIN_SEED_LOOKAHEAD) 1
  let mix ← getRandaoMix state shifted
  return Cryptography.Hash.Sha256.hash32
    ⟨domainType.toArray ++ (uintToBytes 8 epoch.toNat).toArray ++ mix.toArray⟩

/-- The number of committees in each slot of an epoch.

It aims at a target size of committee, from one up to the most committees in a slot. -/
def getCommitteeCountPerSlot (state : BeaconState preset fork) (epoch : Epoch) : UInt64 :=
  max 1 (min preset.MAX_COMMITTEES_PER_SLOT
    ((getActiveValidatorIndices state epoch).length.toUInt64 / preset.SLOTS_PER_EPOCH /
      preset.TARGET_COMMITTEE_SIZE))

/-- The committee of a slot with a given index, cut from active validators in a shuffled order.

The count of committees in each slot is an argument, so that a caller computes it once.

It is the committee of the rule when its inputs are those of the epoch of the slot.

The committees of an epoch are numbered across its slots, in the order of the slots. -/
def beaconCommitteeOf (preset : Preset) (slot : Slot) (index : CommitteeIndex) (perSlot : UInt64)
    (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    Except AccessorError (Array ValidatorIndex) := do
  let position ← liftArith do
    addChecked (← mulChecked (slot % preset.SLOTS_PER_EPOCH) perSlot) index
  let count ← liftArith (mulChecked perSlot preset.SLOTS_PER_EPOCH)
  (shuffledCommittee active shuffled position count).mapError .shuffle

/-- The committee of a slot with a given index, cut from the shuffled active validators.

The committees of an epoch are numbered across its slots, in the order of the slots.

It fails as the shuffle does, for more than `2^40` active validators. -/
def getBeaconCommittee (state : BeaconState preset fork) (slot : Slot) (index : CommitteeIndex) :
    Except AccessorError (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot preset slot
  let seed ← getSeed state epoch DOMAIN_BEACON_ATTESTER
  let active := (getActiveValidatorIndices state epoch).toArray
  let shuffled ← (computeShuffledPermutation preset (UInt64.ofNat active.size) seed).mapError
    .shuffle
  beaconCommitteeOf preset slot index (getCommitteeCountPerSlot state epoch) active shuffled

/-- The number of draws that read one hash: 16 from Electra, 32 before. -/
def drawsPerHash (fork : Base.Fork) : Nat :=
  if .pectra ≤ fork then 16 else 32

/-- The hash that draw number `i` reads its random bytes from.

The draws come in blocks of the number of draws per hash, and each block has its own hash. -/
def drawHash (fork : Base.Fork) (seed : Bytes32) (i : Nat) : Bytes32 :=
  Cryptography.Hash.Sha256.hash32
    ⟨seed.toArray ++ (uintToBytes 8 (i / drawsPerHash fork)).toArray⟩

/-- A draw that does not start a block reads the hash of the draw before it. -/
theorem drawHash_succ {fork : Base.Fork} {seed : Bytes32} {i : Nat}
    (inside : (i + 1) % drawsPerHash fork ≠ 0) :
    drawHash fork seed (i + 1) = drawHash fork seed i := by
  have same : (i + 1) / drawsPerHash fork = i / drawsPerHash fork :=
    Nat.succ_div_of_not_dvd fun divides => inside (Nat.mod_eq_zero_of_dvd divides)
  simp only [drawHash, same]

/-- Whether draw number `i` accepts a candidate of an effective balance, from its hash.

The draw accepts with a chance of the balance over the largest effective balance.

Before Electra it compares with byte `i mod 32` of the hash.

From Electra it compares with the two bytes from `2 * (i mod 16)`, little-endian, per [EIP-7251].

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/
def drawAccepts (preset : Preset) (fork : Base.Fork) (random : Bytes32) (i : Nat)
    (effectiveBalance : Gwei) : Except AccessorError Bool := liftArith do
  if .pectra ≤ fork then
    have small : i % 16 * 2 + 1 < 32 := by have := Nat.mod_lt i (show 16 > 0 by decide); omega
    let value := random[i % 16 * 2].toUInt64 + 256 * random[i % 16 * 2 + 1].toUInt64
    return (← mulChecked preset.MAX_EFFECTIVE_BALANCE_ELECTRA value) ≤
      (← mulChecked effectiveBalance (2 ^ 16 - 1))
  else
    let value := (random[i % 32]'(Nat.mod_lt i (by decide))).toUInt64
    return (← mulChecked preset.MAX_EFFECTIVE_BALANCE value) ≤
      (← mulChecked effectiveBalance (2 ^ 8 - 1))

/-- Whether the draw for candidate number `i` accepts a candidate of an effective balance.

It reads the hash of the block of the draw. -/
def proposerDraw (preset : Preset) (fork : Base.Fork) (seed : Bytes32) (i : Nat)
    (effectiveBalance : Gwei) : Except AccessorError Bool :=
  drawAccepts preset fork (drawHash fork seed i) i effectiveBalance

/-- The search for a proposer, from candidate number `i` on.

Candidate `i` is the index at shuffled position `i mod n`, among `n` indices.

The counter is a 64-bit integer, so the search fails when it would reach `2^64`.

No bound below that is proved, since each draw depends on a hash.

The default index is never read, since each shuffled position is below the number of indices. -/
def proposerSearch (preset : Preset) (fork : Base.Fork) (validators : Array Validator)
    (indices : Array ValidatorIndex) (shuffled : Array UInt64) (seed : Bytes32) (i : Nat) :
    Except AccessorError ValidatorIndex := do
  let candidate := indices.getD (shuffled.getD (i % indices.size) 0).toNat 0
  let some validator := validators[candidate.toNat]? | throw (.indexOutOfRange candidate)
  if ← proposerDraw preset fork seed i validator.effectiveBalance then return candidate
  if next : i + 1 < 2 ^ 64 then proposerSearch preset fork validators indices shuffled seed (i + 1)
  else throw (.arith .overflow)
termination_by 2 ^ 64 - i

/-- A proposer drawn from some indices, with a chance that grows with its effective balance.

The draw walks the indices in shuffled order, and each candidate passes a weighted draw.

It fails as the shuffle does, for more than `2^40` indices. -/
def computeProposerIndex (state : BeaconState preset fork) (indices : Array ValidatorIndex)
    (seed : Bytes32) : Except AccessorError ValidatorIndex := do
  if indices.size = 0 then throw .noCandidates
  unless indices.size < 2 ^ 64 do throw (.arith .overflow)
  let shuffled ← (computeShuffledPermutation preset indices.size.toUInt64 seed).mapError .shuffle
  proposerSearch preset fork state.validators.data indices shuffled seed 0

/-- The proposer of the slot of a state.

Before Fulu, it is drawn from the active validators with a seed of the slot.

From Fulu, the state keeps the proposers of the coming slots, as [EIP-7917] specifies.

[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
-/
def getBeaconProposerIndex (state : BeaconState preset fork) :
    Except AccessorError ValidatorIndex := do
  if fulu : .fusaka ≤ fork then
    if nonzero : preset.SLOTS_PER_EPOCH = 0 then throw (.arith .divisionByZero)
    else
      return (state.proposerLookahead fulu)[(state.slot % preset.SLOTS_PER_EPOCH).toNat]'(
        Nat.lt_of_lt_of_le (toNat_mod_lt nonzero) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
  else
    let epoch := getCurrentEpoch state
    let epochSeed ← getSeed state epoch DOMAIN_BEACON_PROPOSER
    let seed := Cryptography.Hash.Sha256.hash32
      ⟨epochSeed.toArray ++ (uintToBytes 8 state.slot.toNat).toArray⟩
    computeProposerIndex state (getActiveValidatorIndices state epoch).toArray seed

/-- The signature domain of a kind of message in an epoch, by default the epoch of the state.

Before the epoch of the latest fork of the state, the previous fork version applies. -/
def getDomain (config : Config) (state : BeaconState preset fork) (domainType : DomainType)
    (epoch : Option Epoch := none) : Except AccessorError Domain :=
  let epoch := epoch.getD (getCurrentEpoch state)
  let version :=
    if epoch < state.forkVersions.epoch then state.forkVersions.previousVersion
    else state.forkVersions.currentVersion
  (computeDomain config domainType version state.genesisValidatorsRoot).mapError fun _ => .ssz

/-- From Electra: the indices of the committees whose bit is set, in increasing order. -/
def getCommitteeIndices {n : Nat} (bits : Bitvector n) : List CommitteeIndex :=
  bits.bits.toList.zipIdx.filterMap fun (bit, index) => if bit then some index.toUInt64 else none

/-- The members of a committee whose bit is set, with the committee's bits from an offset.

Each member needs a bit, so the bits must reach past the offset by the size of the committee.

The default bit is never read, since each position is then below the number of bits. -/
def committeeAttesters (bits : Array Bool) (offset : Nat) (committee : Array ValidatorIndex) :
    Except AccessorError (List ValidatorIndex) :=
  if 0 < committee.size ∧ bits.size < offset + committee.size then
    .error (.bitOutOfRange (max offset bits.size))
  else
    .ok (committee.toList.zipIdx.filterMap fun (member, position) =>
      if bits.getD (offset + position) false then some member else none)

/-- From Electra: the attesters of each committee in a list, whose bits follow one another. -/
def committeesAttesters (state : BeaconState preset fork) (slot : Slot) (bits : Array Bool) :
    List CommitteeIndex → Nat → Except AccessorError (List ValidatorIndex)
  | [], _ => .ok []
  | index :: rest, offset => do
    let committee ← getBeaconCommittee state slot index
    let here ← committeeAttesters bits offset committee
    return here ++ (← committeesAttesters state slot bits rest (offset + committee.size))

/-- The validators that an attestation shows as signers, as a set.

Before Electra, the bits run over one committee.

From Electra, they run over each committee of the committee bits in turn, as [EIP-7549] specifies.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/
def getAttestingIndices (state : BeaconState preset fork) (attestation : Attestation preset fork) :
    Except AccessorError (List ValidatorIndex) := do
  let bits := attestation.aggregationBits.bits
  if electra : .pectra ≤ fork then
    let committees := getCommitteeIndices (attestation.committeeBits electra)
    return sortedSet (← committeesAttesters state attestation.data.slot bits committees 0)
  else
    let committee ← getBeaconCommittee state attestation.data.slot attestation.data.index
    return sortedSet (← committeeAttesters bits 0 committee)

/-- An attestation with the sorted indices of its signers in place of its bits.

Before Gloas the list of indices has a limit, and from Gloas it has none. -/
def getIndexedAttestation (state : BeaconState preset fork)
    (attestation : Attestation preset fork) :
    Except AccessorError (IndexedAttestation preset fork) := do
  let indices ← getAttestingIndices state attestation
  if fits : fork < .glamsterdam → indices.length ≤ maxAttesters preset fork then
    return ⟨⟨indices.toArray, fun before => by simpa using fits before⟩, attestation.data,
      attestation.signature⟩
  else throw (.tooManyAttesters indices.length (maxAttesters preset fork))

end EthLib.Consensus
