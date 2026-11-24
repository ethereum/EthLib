module

public import EthLib.Base.ByteOrder
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

The members of the committees of a slot are cut from one shuffle, computed once for the slot.

From Electra, the committees of one attestation are cut from one shuffle too.

A caller that holds the shuffle of the epoch of the slot of an attestation can cut its signers.

A failed assertion of the rule, or a read past the end of a list, is an error.

A division by a parameter of the preset or the configuration assumes that it is not zero.

A read or a write of a circular buffer of length zero is an error.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

open scoped HexRepr

/-- An error of a state accessor. -/
inductive AccessorError where
  /-- A validator index names no validator of the registry. -/
  | indexOutOfRange (index : ValidatorIndex)
  /-- A total balance reaches 2^64.

  It holds that total. -/
  | balanceOverflow (total : Nat)
  /-- The slot is not one of the recent slots whose block root the state keeps. -/
  | slotOutOfRange (slot stateSlot : Slot)
  /-- A 64-bit operation has no result. -/
  | arith (error : ArithError)
  /-- A shuffle or a committee has no value. -/
  | shuffle (error : ShuffleError)
  /-- The root of a fork has no value.

  It holds the error of the root. -/
  | ssz (error : Err)
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
  /-- From Altair: the public keys to aggregate are none, or one of them is not valid.

  It holds the number of keys, and the position of the first key that is not valid, if any. -/
  | invalidPubkeys (count : Nat) (position : Option Nat)
  /-- From Altair: the source of an attestation is not the justified checkpoint it should vote for.

  It holds the epoch and root of the source, then those of the justified checkpoint. -/
  | wrongSource (sourceEpoch : Epoch) (sourceRoot : Root) (justifiedEpoch : Epoch)
      (justifiedRoot : Root)
  /-- From Gloas: an attestation for the block of its own slot has a nonzero index. -/
  | sameSlotIndexNotZero (index : CommitteeIndex)
  deriving DecidableEq, Repr

/-- Whether a validator is active in an epoch: from its activation epoch, before its exit epoch. -/
def isActiveValidator (validator : Validator) (epoch : Epoch) : Bool :=
  -- `activation ≤ e < exit`, for the epoch `e`.
  validator.activationEpoch ≤ epoch && epoch < validator.exitEpoch

variable {preset : Preset} {fork : Base.Fork}

/-- The epoch of the slot of a state. -/
def getCurrentEpoch (state : BeaconState preset fork) : Epoch :=
  -- `floor(s / SLOTS_PER_EPOCH)`, for the slot `s` of the state.
  computeEpochAtSlot preset state.slot

/-- The first slot of the current epoch of a state, as a natural number. -/
def currentEpochStart (state : BeaconState preset fork) : Nat :=
  (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat

/-- The indices of the validators active in an epoch, in increasing order.

An active position of `2^64` or more wraps modulo `2^64`, where the specification fails.

The transition guards each read with a checked form, or reads it only where the registry fits. -/
def getActiveValidatorIndices (state : BeaconState preset fork) (epoch : Epoch) :
    List ValidatorIndex :=
  -- The positions in the registry of the validators active in the epoch.
  state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isActiveValidator validator epoch then some index.toUInt64 else none

/-- An error of a 64-bit operation, as an error of an accessor. -/
def liftArith {α : Type} (result : Except ArithError α) : Except AccessorError α :=
  result.mapError .arith

/-- The active indices, or an error when an active position does not fit in 64 bits.

An inactive position is not converted, so it needs no bound. -/
def getActiveValidatorIndicesChecked (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError (List ValidatorIndex) :=
  liftArith ((state.validators.data.toList.zipIdx.filterMap fun (validator, position) =>
    if isActiveValidator validator epoch then some position else none).mapM ofNatChecked)

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
  -- Each index names a validator of the registry.
  if let some index := indices.find? (validators.size ≤ ·.toNat) then
    throw (.indexOutOfRange index)
  -- The sum of the effective balances over the set of indices, below `2^64`.
  let total := sumMarked validators (markIndices validators.size indices)
  if 2 ^ 64 ≤ total then throw (.balanceOverflow total)
  -- At least `EFFECTIVE_BALANCE_INCREMENT`, so that a division by it is never by zero.
  return max preset.EFFECTIVE_BALANCE_INCREMENT total.toUInt64

/-- The total effective balance of the validators active in the epoch of a state. -/
def getTotalActiveBalance (state : BeaconState preset fork) : Except AccessorError Gwei :=
  do
    -- The total balance of the validators active in the current epoch.
    let active ← getActiveValidatorIndicesChecked state (getCurrentEpoch state)
    getTotalBalance state active

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

From Electra it needs at least the activation balance, as [EIP-7251] specifies.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/
def isEligibleForActivationQueue (preset : Preset) (fork : Base.Fork) (validator : Validator) :
    Bool :=
  -- It is not in the queue yet: its activation eligibility epoch is `FAR_FUTURE_EPOCH`.
  validator.activationEligibilityEpoch == FAR_FUTURE_EPOCH &&
    -- From Electra its effective balance is at least `MIN_ACTIVATION_BALANCE`.
    if .pectra ≤ fork then preset.MIN_ACTIVATION_BALANCE ≤ validator.effectiveBalance
    -- Before Electra it is `MAX_EFFECTIVE_BALANCE`.
    else validator.effectiveBalance == preset.MAX_EFFECTIVE_BALANCE

/-- Whether a validator in the activation queue may be activated. -/
def isEligibleForActivation (state : BeaconState preset fork) (validator : Validator) : Bool :=
  -- Its place in the queue is finalized: its eligibility epoch is at most the finalized epoch.
  --
  -- It is not activated yet: its activation epoch is `FAR_FUTURE_EPOCH`.
  validator.activationEligibilityEpoch ≤ state.finalizedCheckpoint.epoch &&
    validator.activationEpoch == FAR_FUTURE_EPOCH

/-- Whether a validator may be slashed in an epoch. -/
def isSlashableValidator (validator : Validator) (epoch : Epoch) : Bool :=
  -- It is not slashed yet, and `activation ≤ e < withdrawable`, for the epoch `e`.
  !validator.slashed && validator.activationEpoch ≤ epoch && epoch < validator.withdrawableEpoch

/-- The epoch before the epoch of a state, or the genesis epoch at genesis. -/
def getPreviousEpoch (state : BeaconState preset fork) : Epoch :=
  -- `e - 1` for the current epoch `e`, and `GENESIS_EPOCH`, 0, at genesis.
  saturatingSub (getCurrentEpoch state) 1

/-- The root of the block at a recent slot. -/
def getBlockRootAtSlot (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError Root := do
  -- `x < s ≤ x + SLOTS_PER_HISTORICAL_ROOT`, for the slot `x` and the slot `s` of the state.
  unless slot < state.slot do throw (.slotOutOfRange slot state.slot)
  unless state.slot ≤ (← liftArith (addChecked slot preset.SLOTS_PER_HISTORICAL_ROOT)) do
    throw (.slotOutOfRange slot state.slot)
  -- Entry `x mod SLOTS_PER_HISTORICAL_ROOT` of the block roots.
  readCircular state.blockRoots.elements slot

/-- The root of the block at the first slot of a recent epoch. -/
def getBlockRoot (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError Root := do
  -- The block root at slot `e * SLOTS_PER_EPOCH`, for the epoch `e`.
  getBlockRootAtSlot state (← liftArith (computeStartSlotAtEpoch preset epoch))

/-- The RANDAO mix of a recent epoch. -/
def getRandaoMix (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError Bytes32 :=
  -- Entry `e mod EPOCHS_PER_HISTORICAL_VECTOR` of the mixes, for the epoch `e`.
  readCircular state.randaoMixes.elements epoch

/-- The most validators that may join, or leave, the active validators in one epoch.

Electra counts the churn in balance instead, as [EIP-7251] specifies.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/
def getValidatorChurnLimit (config : Config) (state : BeaconState preset fork) : UInt64 :=
  -- `max(MIN_PER_EPOCH_CHURN_LIMIT, floor(n / CHURN_LIMIT_QUOTIENT))`, for `n` active validators.
  max config.MIN_PER_EPOCH_CHURN_LIMIT
    ((getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64 /
      config.CHURN_LIMIT_QUOTIENT)

/-- From Deneb: the most validators that an epoch activates, as [EIP-7514] specifies.

[EIP-7514]: https://eips.ethereum.org/EIPS/eip-7514#specification
-/
def getValidatorActivationChurnLimit (config : Config) (state : BeaconState preset fork) :
    UInt64 :=
  -- The churn limit, capped at `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT`, as EIP-7514 specifies.
  min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT (getValidatorChurnLimit config state)

/-- From Electra: the sum of the amounts of the pending partial withdrawals of a validator.

A sum of 2^64 or more is an error. -/
def getPendingBalanceToWithdraw (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (index : ValidatorIndex) : Except AccessorError Gwei :=
  -- The sum, in natural numbers, of the amounts of the queued withdrawals of the validator.
  let total := ((state.pendingPartialWithdrawals electra).data.toList.map fun withdrawal =>
    if withdrawal.validatorIndex = index then withdrawal.amount.toNat else 0).sum
  if total < 2 ^ 64 then .ok total.toUInt64 else .error (.balanceOverflow total)

/-- The seed of an epoch for one kind of duty.

The mix is that of the epoch `MIN_SEED_LOOKAHEAD + 1` epochs before, so it is known in advance. -/
def getSeed (state : BeaconState preset fork) (epoch : Epoch) (domainType : DomainType) :
    Except AccessorError Bytes32 := do
  -- The length of the buffer comes first, so that no step goes below zero near genesis.
  let shifted ← liftArith do
    subChecked (← subChecked (← addChecked epoch preset.EPOCHS_PER_HISTORICAL_VECTOR)
      preset.MIN_SEED_LOOKAHEAD) 1
  -- Let `e` be the epoch and `V = EPOCHS_PER_HISTORICAL_VECTOR`.
  --
  -- The mix is that of epoch `e + V - MIN_SEED_LOOKAHEAD - 1`.
  let mix ← getRandaoMix state shifted
  -- `SHA-256(domain type || e as 8 bytes, little-endian || mix)`.
  return Cryptography.Hash.Sha256.hash32
    ⟨domainType.toArray ++ (ByteOrder.toLE 8 epoch.toNat).toArray ++ mix.toArray⟩

/-- The number of committees in each slot, for a number of active validators.

It aims at a target size of committee, from one up to the most committees in a slot. -/
def committeeCountOf (preset : Preset) (active : UInt64) : UInt64 :=
  -- Let `q = floor(floor(n / SLOTS_PER_EPOCH) / TARGET_COMMITTEE_SIZE)`, for `n` active validators.
  --
  -- The count is `max(1, min(MAX_COMMITTEES_PER_SLOT, q))`.
  max 1 (min preset.MAX_COMMITTEES_PER_SLOT
    (active / preset.SLOTS_PER_EPOCH / preset.TARGET_COMMITTEE_SIZE))

/-- The number of committees in each slot of an epoch. -/
def getCommitteeCountPerSlot (state : BeaconState preset fork) (epoch : Epoch) : UInt64 :=
  committeeCountOf preset (getActiveValidatorIndices state epoch).length.toUInt64

/-- The committee count, or an error when an active position or the active count needs 65 bits. -/
def getCommitteeCountPerSlotChecked (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError UInt64 := do
  let active ← getActiveValidatorIndicesChecked state epoch
  return committeeCountOf preset (← liftArith (ofNatChecked active.length))

/-- The committee of a slot with a given index, cut from active validators in a shuffled order.

The count of committees in each slot is an argument, so that a caller computes it once.

It is the committee of the rule when its inputs are those of the epoch of the slot.

The committees of an epoch are numbered across its slots, in the order of the slots. -/
def beaconCommitteeOf (preset : Preset) (slot : Slot) (index : CommitteeIndex) (perSlot : UInt64)
    (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    Except AccessorError (Array ValidatorIndex) := do
  -- Let `s` be the slot, `i` the index and `c` the count of committees per slot.
  --
  -- With `P = SLOTS_PER_EPOCH`, it is committee `(s mod P) * c + i` of the `c * P` of the epoch.
  let position ← liftArith do
    addChecked (← mulChecked (slot % preset.SLOTS_PER_EPOCH) perSlot) index
  let count ← liftArith (mulChecked perSlot preset.SLOTS_PER_EPOCH)
  (shuffledCommittee active shuffled position count).mapError .shuffle

/-- The active validators of an epoch, and their shuffle for the beacon committees.

It fails as the shuffle does, for more than `2^40` active validators.

It also fails at an active position or an active count of `2^64` or more. -/
def attesterShuffle (state : BeaconState preset fork) (epoch : Epoch) :
    Except AccessorError (Array ValidatorIndex × Array UInt64) := do
  -- The seed of the epoch for attesters, and the validators active in it.
  let seed ← getSeed state epoch DOMAIN_BEACON_ATTESTER
  let active := (← getActiveValidatorIndicesChecked state epoch).toArray
  -- The shuffled position of each of them.
  let count ← liftArith (ofNatChecked active.size)
  return (active, ← (computeShuffledPermutation preset count seed).mapError .shuffle)

/-- The committee of a slot with a given index, cut from the shuffled active validators.

The committees of an epoch are numbered across its slots, in the order of the slots.

It fails as the shuffle does, for more than `2^40` active validators. -/
def getBeaconCommittee (state : BeaconState preset fork) (slot : Slot) (index : CommitteeIndex) :
    Except AccessorError (Array ValidatorIndex) := do
  -- The shuffle of the epoch of the slot, then the committee cut from it.
  let epoch := computeEpochAtSlot preset slot
  let (active, shuffled) ← attesterShuffle state epoch
  beaconCommitteeOf preset slot index (getCommitteeCountPerSlot state epoch) active shuffled

/-- The members of the beacon committees of a slot, committee after committee.

They are cut from the given active validators and shuffle, with the given count of committees.

The caller computes the count once, since computing it reads the whole registry. -/
def slotCommitteeMembersOf (preset : Preset) (slot : Slot) (perSlot : UInt64)
    (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    Except AccessorError (Array ValidatorIndex) :=
  (List.range perSlot.toNat).foldlM
    (fun members index => do
      return members ++ (← beaconCommitteeOf preset slot index.toUInt64 perSlot active shuffled))
    #[]

/-- The members of the beacon committees of a slot, committee after committee.

The committees share one shuffle of the active validators, computed once for the slot. -/
def slotCommitteeMembers (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot preset slot
  let (active, shuffled) ← attesterShuffle state epoch
  slotCommitteeMembersOf preset slot (getCommitteeCountPerSlot state epoch) active shuffled

/-- The number of draws that read one hash: 16 from Electra, 32 before. -/
def drawsPerHash (fork : Base.Fork) : Nat :=
  -- From Electra a draw reads 2 of the 32 bytes of a hash, and before Electra 1.
  if .pectra ≤ fork then 16 else 32

/-- The input hashed for one block of draws: the seed, then the block number as eight bytes.

The bytes are little-endian. -/
def drawInput (seed : Bytes32) (block : Nat) : ByteArray :=
  ⟨seed.toArray ++ (ByteOrder.toLE 8 block).toArray⟩

/-- The hash that draw number `i` reads its random bytes from.

The draws come in blocks of the number of draws per hash, and each block has its own hash. -/
def drawHash (fork : Base.Fork) (seed : Bytes32) (i : Nat) : Bytes32 :=
  -- `SHA-256(seed || floor(i / k) as 8 bytes, little-endian)`, for `k` draws per hash.
  Cryptography.Hash.Sha256.hash32 (drawInput seed (i / drawsPerHash fork))

/-- A draw that does not start a block reads the hash of the draw before it. -/
theorem drawHash_succ {fork : Base.Fork} {seed : Bytes32} {i : Nat}
    (inside : (i + 1) % drawsPerHash fork ≠ 0) :
    drawHash fork seed (i + 1) = drawHash fork seed i := by
  have same : (i + 1) / drawsPerHash fork = i / drawsPerHash fork :=
    Nat.succ_div_of_not_dvd fun divides => inside (Nat.mod_eq_zero_of_dvd divides)
  simp only [drawHash, same]

/-- Whether draw number `i` accepts a candidate of an effective balance, from its hash.

It accepts when the fork's largest effective balance times the selected value is at most a bound.

The bound is the balance times `2^8 - 1` before Electra, and times `2^16 - 1` from Electra.

The comparison is inclusive, so a selected value of zero is accepted even at zero balance.

It fails when a product does not fit in 64 bits.

Before Electra it compares with byte `i mod 32` of the hash.

From Electra it compares with the two bytes from `2 * (i mod 16)`, little-endian.
-/
def drawAccepts (preset : Preset) (fork : Base.Fork) (random : Bytes32) (i : Nat)
    (effectiveBalance : Gwei) : Except AccessorError Bool := liftArith do
  -- Let `b` be the effective balance and `r` the random value of draw `i`.
  --
  -- From Electra, let `j = i mod 16`.
  --
  -- `r` is bytes `2j` and `2j + 1` of the hash, little-endian.
  --
  -- The draw accepts when `MAX_EFFECTIVE_BALANCE_ELECTRA * r ≤ b * (2^16 - 1)`.
  if .pectra ≤ fork then
    have small : i % 16 * 2 + 1 < 32 := by have := Nat.mod_lt i (show 16 > 0 by decide); omega
    let value := random[i % 16 * 2].toUInt64 + 256 * random[i % 16 * 2 + 1].toUInt64
    return (← mulChecked preset.MAX_EFFECTIVE_BALANCE_ELECTRA value) ≤
      (← mulChecked effectiveBalance (2 ^ 16 - 1))
  -- Before Electra, `r` is byte `i mod 32` of the hash.
  --
  -- The draw accepts when `MAX_EFFECTIVE_BALANCE * r ≤ b * (2^8 - 1)`.
  else
    let value := (random[i % 32]'(Nat.mod_lt i (by decide))).toUInt64
    return (← mulChecked preset.MAX_EFFECTIVE_BALANCE value) ≤
      (← mulChecked effectiveBalance (2 ^ 8 - 1))

/-- Whether the draw for candidate number `i` accepts a candidate of an effective balance.

It reads the hash of the block of the draw. -/
def proposerDraw (preset : Preset) (fork : Base.Fork) (seed : Bytes32) (i : Nat)
    (effectiveBalance : Gwei) : Except AccessorError Bool :=
  -- Draw `i` reads the hash of its block of draws.
  drawAccepts preset fork (drawHash fork seed i) i effectiveBalance

/-- The search for a proposer, from candidate number `i` on.

Candidate `i` is the index at position `order (i mod n)`, among `n` indices.

The counter is a 64-bit integer, so the search fails when it would reach `2^64`.

No bound below that is proved, since each draw depends on a hash.

The default index is never read when each position of the order is in range. -/
def proposerSearch (preset : Preset) (fork : Base.Fork) (validators : Array Validator)
    (indices : Array ValidatorIndex) (order : Nat → Nat) (seed : Bytes32) (i : Nat) :
    Except AccessorError ValidatorIndex := do
  -- Candidate `i` is the index at the shuffled position of `i mod n`, among `n` indices.
  let candidate := indices.getD (order (i % indices.size)) 0
  let some validator := validators[candidate.toNat]? | throw (.indexOutOfRange candidate)
  -- It is the proposer if draw `i` accepts its effective balance.
  if ← proposerDraw preset fork seed i validator.effectiveBalance then return candidate
  -- Else the search moves to candidate `i + 1`.
  if next : i + 1 < 2 ^ 64 then proposerSearch preset fork validators indices order seed (i + 1)
  else throw (.arith .overflow)
termination_by 2 ^ 64 - i

/-- A proposer drawn from some indices, with a chance that grows with its effective balance.

The draw walks the indices in shuffled order, and each candidate passes a weighted draw.

It shuffles only the positions that it reads, so no candidate costs more for more indices.

It fails as the shuffle does, for more than `2^40` indices. -/
def computeProposerIndex (state : BeaconState preset fork) (indices : Array ValidatorIndex)
    (seed : Bytes32) : Except AccessorError ValidatorIndex := do
  -- There is at least one candidate, and the count is below `2^64` and at most `2^40`.
  if indices.size = 0 then throw .noCandidates
  unless indices.size < 2 ^ 64 do throw (.arith .overflow)
  if 2 ^ 40 < indices.size then throw (.shuffle (.countTooLarge indices.size.toUInt64))
  -- The pivots depend only on the preset, the seed and the count, so the candidates share them.
  let pivots := Shuffle.pivots preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size
  proposerSearch preset fork state.validators.data indices
    (Shuffle.shuffledIndexBy pivots seed indices.size) seed 0

/-- The proposer of the slot of a state.

From Fulu, the state keeps the proposers of the coming slots, as [EIP-7917] specifies.

[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
-/
def getBeaconProposerIndex (state : BeaconState preset fork) :
    Except AccessorError ValidatorIndex := do
  -- From Fulu, entry `s mod SLOTS_PER_EPOCH` of the lookahead for the slot `s`, as EIP-7917 says.
  if fulu : .fusaka ≤ fork then
    if nonzero : preset.SLOTS_PER_EPOCH = 0 then throw (.arith .divisionByZero)
    else
      return (state.proposerLookahead fulu)[(state.slot % preset.SLOTS_PER_EPOCH).toNat]'(
        Nat.lt_of_lt_of_le (toNat_mod_lt nonzero) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
  else
    -- Before Fulu, a draw from the active validators of the epoch.
    --
    -- The seed is `SHA-256(epoch seed of proposers || s as 8 bytes, little-endian)`.
    let epoch := getCurrentEpoch state
    let epochSeed ← getSeed state epoch DOMAIN_BEACON_PROPOSER
    let seed := Cryptography.Hash.Sha256.hash32
      ⟨epochSeed.toArray ++ (ByteOrder.toLE 8 state.slot.toNat).toArray⟩
    computeProposerIndex state (← getActiveValidatorIndicesChecked state epoch).toArray seed

/-- The signature domain of a kind of message in an epoch, by default the epoch of the state.

Before the epoch of the latest fork of the state, the previous fork version applies. -/
def getDomain (config : Config) (state : BeaconState preset fork) (domainType : DomainType)
    (epoch : Option Epoch := none) : Except AccessorError Domain :=
  -- The previous fork version before the epoch of the fork of the state, else the current one.
  let version := state.forkVersions.versionAt (epoch.getD (getCurrentEpoch state))
  (computeDomain config domainType version state.genesisValidatorsRoot).mapError .ssz

/-- From Electra: the indices of the committees whose bit is set, in increasing order. -/
def getCommitteeIndices {n : Nat} (bits : Bitvector n) : List CommitteeIndex :=
  -- The positions `i` with bit `i` set.
  bits.bits.toList.zipIdx.filterMap fun (bit, index) => if bit then some index.toUInt64 else none

/-- The members of a committee whose bit is set, with the committee's bits from an offset.

Each member needs a bit, so the bits must reach past the offset by the size of the committee.

The default bit is never read, since each position is then below the number of bits. -/
def committeeAttesters (bits : Array Bool) (offset : Nat) (committee : Array ValidatorIndex) :
    Except AccessorError (List ValidatorIndex) :=
  -- A nonempty committee needs bits up to `o + m`, for the offset `o` and `m` members.
  if 0 < committee.size ∧ bits.size < offset + committee.size then
    .error (.bitOutOfRange (max offset bits.size))
  else
    -- Member `j` attests when bit `o + j` is set.
    .ok (committee.toList.zipIdx.filterMap fun (member, position) =>
      if bits.getD (offset + position) false then some member else none)

/-- From Electra: the attesters of each committee in a list, whose bits follow one another.

The committees are cut from the given active validators and shuffle.

The count of committees per slot is given too. -/
def committeesAttestersOf (preset : Preset) (slot : Slot) (bits : Array Bool) (perSlot : UInt64)
    (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    List CommitteeIndex → Nat → Except AccessorError (List ValidatorIndex)
  | [], _ => .ok []
  | index :: rest, offset => do
    -- The attesters of each committee, its bits from the offset.
    let committee ← beaconCommitteeOf preset slot index perSlot active shuffled
    let here ← committeeAttesters bits offset committee
    -- The offset then grows by the size of the committee.
    return here ++ (← committeesAttestersOf preset slot bits perSlot active shuffled rest
      (offset + committee.size))

/-- The validators that an attestation shows as signers, cut from a given shuffle, as a set.

The committees are cut from the given active validators, shuffle and count of committees per slot.

When these are the inputs of the epoch of the slot of the attestation, it is the set of the rule. -/
def attestingIndicesOf (attestation : Attestation preset fork) (perSlot : UInt64)
    (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    Except AccessorError (List ValidatorIndex) := do
  let bits := attestation.aggregationBits.bits
  -- From Electra, the attesters of each committee of the committee bits, as EIP-7549 specifies.
  if electra : .pectra ≤ fork then
    let committees := getCommitteeIndices (attestation.committeeBits electra)
    return sortedSet (← committeesAttestersOf preset attestation.data.slot bits perSlot active
      shuffled committees 0)
  -- Before Electra, the attesters of the committee of its index, as a set.
  else
    let committee ← beaconCommitteeOf preset attestation.data.slot attestation.data.index perSlot
      active shuffled
    return sortedSet (← committeeAttesters bits 0 committee)

/-- The validators that an attestation shows as signers, as a set.

From Electra, the bits run over each committee of the committee bits, as [EIP-7549] specifies.

The committees share one shuffle of the epoch of the slot, computed once.

From Electra, an attestation that names no committee computes no shuffle.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/
def getAttestingIndices (state : BeaconState preset fork) (attestation : Attestation preset fork) :
    Except AccessorError (List ValidatorIndex) :=
  -- The rule reads no committee for an empty list, so it reads no shuffle either.
  if ∃ electra : .pectra ≤ fork, getCommitteeIndices (attestation.committeeBits electra) = [] then
    .ok []
  else do
    let epoch := computeEpochAtSlot preset attestation.data.slot
    -- Each committee alone reads the shuffle before its cut, so reading it first changes no error.
    let (active, shuffled) ← attesterShuffle state epoch
    attestingIndicesOf attestation (getCommitteeCountPerSlot state epoch) active shuffled

/-- An attestation with the given indices of its signers in place of its bits.

The indices keep their given order.

Before Gloas a list of indices past its limit is an error, and from Gloas the list has no limit. -/
def indexedAttestationOf (attestation : Attestation preset fork) (indices : List ValidatorIndex) :
    Except AccessorError (IndexedAttestation preset fork) := do
  -- The indices, the data and the signature, with the indices within the limit before Gloas.
  if fits : fork < .glamsterdam → indices.length ≤ maxAttesters preset fork then
    return ⟨⟨indices.toArray, fun before => by simpa using fits before⟩, attestation.data,
      attestation.signature⟩
  else throw (.tooManyAttesters indices.length (maxAttesters preset fork))

/-- An attestation with the sorted indices of its signers in place of its bits.

Before Gloas the list of indices has a limit, and from Gloas it has none. -/
def getIndexedAttestation (state : BeaconState preset fork)
    (attestation : Attestation preset fork) :
    Except AccessorError (IndexedAttestation preset fork) := do
  indexedAttestationOf attestation (← getAttestingIndices state attestation)

end EthLib.Consensus
