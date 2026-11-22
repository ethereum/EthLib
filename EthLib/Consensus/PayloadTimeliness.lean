module

public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.PayloadTimeliness`

The balance-weighted selection, and from Gloas the payload timeliness committee.

A balance-weighted selection draws candidates with a chance that grows with their balance.

It walks the candidates in turn, in their order or in shuffled order, and may draw one twice.

Each draw is the draw of a proposer at the fork of the state.

From Electra, that draw reads two random bytes.

One hash gives the random bytes of 32 draws before Electra, and of 16 draws from Electra.

Gloas selects the proposers and the payload timeliness committee this way.

From Altair, the sync committee is a selection of this kind too.

The payload timeliness committee of a slot votes on whether the payload of its block arrived.

It is a balance-weighted selection of a fixed size from the beacon committees of the slot.

The state keeps the committees of the previous epoch, the current epoch and the lookahead.

That window moves by one epoch at each epoch boundary.

A vote of the committee names its members by bits, and its indexed form by sorted indices.

A failed assertion of the rule, a read past the end of a list, or a 64-bit overflow is an error.

A division by a parameter of the preset assumes that it is not zero.

[EIP-7732] adds the committee and its window.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The search of a balance-weighted selection, from draw number `i` on.

Draw `i` reads the candidate at position `order (i mod n)`, among `n` candidates.

It carries the hash of the block of draw `i`, and hashes again only when a new block starts.

The draw counter is a 64-bit integer, so the search fails when it would reach `2^64`.

The default candidate is never read when each position of the order is in range. -/
def balanceWeightedSearch (preset : Preset) (fork : Base.Fork) (indices : Array ValidatorIndex)
    (balances : Array Gwei) (order : Nat → Nat) (seed : Bytes32) (size : Nat)
    (selected : Array ValidatorIndex) (bound : selected.size ≤ size) (i : Nat)
    (random : { random // random = drawHash fork seed i }) :
    Except AccessorError (Vector ValidatorIndex size) :=
  -- The selection stops once it holds `size` candidates.
  if full : selected.size = size then .ok ⟨selected, full⟩
  else do
    -- Draw `i` reads the candidate at position `order(i mod n)`, and accepts it by its balance.
    let position := order (i % indices.size)
    let accepted ← drawAccepts preset fork random.1 i (balances.getD position 0)
    -- An accepted candidate joins the selection.
    let next : { next : Array ValidatorIndex // next.size ≤ size } :=
      if accepted then ⟨selected.push (indices.getD position 0), by simp; omega⟩
      else ⟨selected, bound⟩
    -- A new hash only when draw `i + 1` starts a new block of draws.
    let random : { random // random = drawHash fork seed (i + 1) } :=
      if start : (i + 1) % drawsPerHash fork = 0 then ⟨drawHash fork seed (i + 1), rfl⟩
      else ⟨random.1, random.2.trans (drawHash_succ start).symm⟩
    if i + 1 < 2 ^ 64 then
      balanceWeightedSearch preset fork indices balances order seed size next.1 next.2 (i + 1)
        random
    else throw (.arith .overflow)
termination_by 2 ^ 64 - i

/-- A list of `size` candidates, each drawn with a chance that grows with its effective balance.

The candidates are read in their order, or in the order of the shuffle of their positions.

A candidate may be drawn more than once.

There must be at least one candidate, and each must name a validator.

A shuffled draw takes the shuffled position of its candidate, which has no value above `2^40`.

So a shuffled selection fails for more than `2^40` candidates, before its first draw. -/
def computeBalanceWeightedSelection (state : BeaconState preset fork)
    (indices : Array ValidatorIndex) (seed : Bytes32) (size : UInt64) (shuffleIndices : Bool) :
    Except AccessorError (Vector ValidatorIndex size.toNat) := do
  -- There is at least one candidate.
  if indices.size = 0 then throw .noCandidates
  unless indices.size < 2 ^ 64 do throw (.arith .overflow)
  -- The effective balance of each candidate.
  let balances ← indices.mapM fun index => return (← getValidator state index).effectiveBalance
  if shuffleIndices ∧ size ≠ 0 ∧ 2 ^ 40 < indices.size then
    throw (.shuffle (.countTooLarge indices.size.toUInt64))
  -- Each draw shuffles only its own position, so a draw costs the same at any count.
  --
  -- The pivots depend only on the seed and the count, so the draws share them.
  let pivots := if shuffleIndices then
      Shuffle.pivots preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size
    else #[]
  -- The order of the candidates: shuffled, or as given.
  let order : Nat → Nat :=
    if shuffleIndices then Shuffle.shuffledIndexBy pivots seed indices.size else id
  -- The draws from draw 0.
  balanceWeightedSearch preset fork indices balances order seed size.toNat #[] (Nat.zero_le _) 0
    ⟨drawHash fork seed 0, rfl⟩

/-- The payload timeliness committee of a slot, from the seed of its epoch for this duty.

The beacon committees of the slot are cut from the given active validators and shuffle.

The count of those committees in the slot is given. -/
def computePtcOf (state : BeaconState preset fork) (slot : Slot) (epochSeed : Bytes32)
    (perSlot : UInt64) (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    Except AccessorError (PayloadTimelinessCommittee preset) := do
  -- The seed `SHA-256(epoch seed || s as 8 bytes, little-endian)`, for the slot `s`.
  let seed :=
    Cryptography.Hash.Sha256.hash32 ⟨epochSeed.toArray ++ (uintToBytes 8 slot.toNat).toArray⟩
  -- `PTC_SIZE` members, weighted by effective balance, from the slot's committees.
  --
  -- EIP-7732 specifies that sampling.
  --
  -- The members are read in committee order, not shuffled.
  let members ← slotCommitteeMembersOf preset slot perSlot active shuffled
  computeBalanceWeightedSelection state members seed preset.PTC_SIZE false

/-- The payload timeliness committee of a slot, which may hold a validator more than once. -/
def computePtc (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError (PayloadTimelinessCommittee preset) := do
  -- The seed of the epoch of the slot for this duty, and its shuffle of attesters.
  let epoch := computeEpochAtSlot preset slot
  let epochSeed ← getSeed state epoch DOMAIN_PTC_ATTESTER
  let (active, shuffled) ← attesterShuffle state epoch
  computePtcOf state slot epochSeed (getCommitteeCountPerSlot state epoch) active shuffled

/-- The position in the window of the committee of a slot.

The previous epoch comes first, then the current epoch and the lookahead.

The slot must be from the fork, and in one of those epochs. -/
def ptcWindowPosition (config : Config) (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError UInt64 := do
  let epoch := computeEpochAtSlot preset slot
  let outOfRange := AccessorError.ptcSlotOutOfRange slot state.slot
  -- The epoch `x` of the slot is at or after the first epoch of Gloas.
  unless config.GLOAS_FORK_EPOCH ≤ epoch do throw outOfRange
  let stateEpoch := getCurrentEpoch state
  -- Here `s` is the slot, `P = SLOTS_PER_EPOCH` and `e` the current epoch.
  --
  -- The previous epoch, `x + 1 = e`, takes position `s mod P`.
  if epoch < stateEpoch then
    unless epoch + 1 = stateEpoch do throw outOfRange
    return slot % preset.SLOTS_PER_EPOCH
  else
    -- Else `e ≤ x ≤ e + MIN_SEED_LOOKAHEAD`, at position `(x - e + 1) * P + s mod P`.
    unless epoch ≤ (← liftArith (addChecked stateEpoch preset.MIN_SEED_LOOKAHEAD)) do
      throw outOfRange
    let offset ← liftArith do
      mulChecked (← addChecked (epoch - stateEpoch) 1) preset.SLOTS_PER_EPOCH
    liftArith (addChecked offset (slot % preset.SLOTS_PER_EPOCH))

/-- The payload timeliness committee of a slot, as the window of the state keeps it. -/
def getPtc (config : Config) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (slot : Slot) : Except AccessorError (PayloadTimelinessCommittee preset) := do
  -- The committee at the position of the slot in the window.
  let position ← ptcWindowPosition config state slot
  match (state.ptcWindow gloas).elements[position.toNat]? with
  | some committee => return committee
  | none => throw (.ptcSlotOutOfRange slot state.slot)

/-- The members of a committee whose bit is set, in committee order. -/
def ptcAttesters (committee : PayloadTimelinessCommittee preset)
    (bits : PayloadTimelinessCommitteeBits preset) : List ValidatorIndex :=
  -- Member `j` attests when bit `j` is set.
  (committee.toList.zip bits.bits.toList).filterMap fun (member, bit) =>
    if bit then some member else none

/-- A committee has at most as many attesters as members. -/
theorem length_ptcAttesters_le (committee : PayloadTimelinessCommittee preset)
    (bits : PayloadTimelinessCommitteeBits preset) :
    (ptcAttesters committee bits).length ≤ preset.PTC_SIZE.toNat :=
  Nat.le_trans (List.length_filterMap_le _ _) (by simp)

/-- A vote of the committee with the sorted indices of its signers in place of its bits.

An index that appears twice in the committee appears twice in the indices. -/
def getIndexedPayloadAttestation (config : Config) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (attestation : PayloadAttestation preset) :
    Except AccessorError (IndexedPayloadAttestation preset) := do
  -- The attesters of the committee of the slot of the vote, sorted, with their repeats.
  let committee ← getPtc config state gloas attestation.data.slot
  let attesters := ptcAttesters committee attestation.aggregationBits
  let sorted := attesters.mergeSort (· ≤ ·)
  return ⟨⟨sorted.toArray, by simpa [sorted] using length_ptcAttesters_le committee _⟩,
    attestation.data, attestation.signature⟩

/-- Whether an indexed vote of the committee has signers, in sorted order, and a valid signature.

An index may repeat, since the committee may hold a validator twice. -/
def isValidIndexedPayloadAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (attestation : IndexedPayloadAttestation preset) :
    Except TransitionError Bool := do
  let indices := attestation.attestingIndices.data.toList
  -- The indices are nonempty and sorted, repeats allowed.
  if indices = [] ∨ indices ≠ indices.mergeSort (· ≤ ·) then return false
  -- The signature is the aggregate of the keys of the signers over the vote.
  --
  -- The domain is that of the committee, at the epoch of the slot of the vote.
  let pubkeys ← indices.toArray.mapM fun index => do
    return (← liftAccessor (getValidator state index)).pubkey
  let domain ← liftAccessor (getDomain config state DOMAIN_PTC_ATTESTER
    (some (computeEpochAtSlot preset attestation.data.slot)))
  let signingRoot ← liftSsz (computeSigningRoot attestation.data domain)
  return checks.fastAggregateVerify pubkeys (packBytes signingRoot)
    attestation.signature

/-- The state after a payload attestation of a block, which the state does not change. -/
def processPayloadAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (attestation : PayloadAttestation preset) :
    Except TransitionError (BeaconState preset fork) := do
  let data := attestation.data
  -- The vote is on the parent of the block.
  ensure (data.beaconBlockRoot = state.latestBlockHeader.parentRoot)
    (.payloadAttestationNotForParent data.beaconBlockRoot state.latestBlockHeader.parentRoot)
  -- Its slot is the slot before that of the state.
  ensure (data.slot.toNat + 1 = state.slot.toNat)
    (.payloadAttestationWrongSlot data.slot state.slot)
  -- Its signers sign it, as an indexed vote of the committee of that slot.
  let indexed ← liftAccessor (getIndexedPayloadAttestation config state gloas attestation)
  let valid ← isValidIndexedPayloadAttestation config checks state indexed
  ensure (valid = true) (.invalidPayloadAttestation data.slot indexed.attestingIndices.data.size)
  return state

/-- The slot at a position of the window, counted from the first slot of an epoch.

The epoch is that of the position after the first. -/
def ptcWindowSlot (preset : Preset) (firstEpoch : Epoch) (position : Nat) :
    Except AccessorError Slot := liftArith do
  -- Let `f` be the first epoch and `P = SLOTS_PER_EPOCH`.
  --
  -- Position `q` is slot `q mod P` of epoch `f + floor(q / P)`.
  let perEpoch := preset.SLOTS_PER_EPOCH.toNat
  let epoch ← addChecked firstEpoch (position / perEpoch).toUInt64
  addChecked (← computeStartSlotAtEpoch preset epoch) (position % perEpoch).toUInt64

/-- The window of committees when the field first appears, at the fork or at genesis.

The previous epoch holds committees whose every seat is validator 0.

The other epochs hold their computed committees.
-/
def initializePtcWindow (state : BeaconState preset fork) :
    Except AccessorError (PayloadTimelinessCommitteeWindow preset) :=
  let perEpoch := preset.SLOTS_PER_EPOCH.toNat
  let current := getCurrentEpoch state
  -- The committees of an epoch read the same two seeds, shuffle and count of committees per slot.
  --
  -- So these are computed once for the current epoch, and once for each epoch of the lookahead.
  let inputs : Array (Except AccessorError _) :=
    (Array.range (preset.MIN_SEED_LOOKAHEAD.toNat + 1)).map fun ahead => do
      -- This sum may wrap, but then the checked sum of each slot of that epoch fails first.
      let epoch := current + ahead.toUInt64
      return (← getSeed state epoch DOMAIN_PTC_ATTESTER, getCommitteeCountPerSlot state epoch,
        ← attesterShuffle state epoch)
  RootedVector.ofVector <$> (Vector.range _).mapM fun position => do
    -- The positions of the previous epoch hold committees whose every seat is validator 0.
    if position < perEpoch then return Vector.replicate _ 0
    -- Each later position holds the computed committee of its slot.
    let slot ← ptcWindowSlot preset current (position - perEpoch)
    match inputs[(position - perEpoch) / perEpoch]? with
    | some shared =>
      let (epochSeed, perSlot, active, shuffled) ← shared
      computePtcOf state slot epochSeed perSlot active shuffled
    -- Every position after the previous epoch reads an epoch of the inputs, so this never fails.
    | none => throw (.ptcSlotOutOfRange slot state.slot)

/-- The state with its window of committees moved by one epoch.

The last epoch of the window becomes the epoch after the lookahead, with its computed committees.
-/
def processPtcWindow (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Except AccessorError (BeaconState preset fork) := do
  let perEpoch := preset.SLOTS_PER_EPOCH.toNat
  -- The epoch `e + MIN_SEED_LOOKAHEAD + 1`, for the current epoch `e`.
  let nextEpoch ← liftArith do
    addChecked (← addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD) 1
  -- The new committees read the same two seeds, shuffle and count, so these are computed once.
  let inputs : Except AccessorError _ := do
    return (← getSeed state nextEpoch DOMAIN_PTC_ATTESTER, getCommitteeCountPerSlot state nextEpoch,
      ← attesterShuffle state nextEpoch)
  -- The committees of each slot of that epoch.
  let fresh ← (Vector.range perEpoch).mapM fun offset => do
    let slot ← ptcWindowSlot preset nextEpoch offset
    let (epochSeed, perSlot, active, shuffled) ← inputs
    computePtcOf state slot epochSeed perSlot active shuffled
  -- The window drops its first `SLOTS_PER_EPOCH` committees, and the new ones join its end.
  --
  -- The committees that stay keep their leaves in the tree of the window.
  --
  -- So only the new committees are hashed, with the levels above the leaves.
  --
  -- The window is bound here, once, so that each read of the field shares its tree.
  let moved := (state.ptcWindow gloas).shift fresh (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  return { state with ptcWindow := fun _ => moved }

end EthLib.Consensus
