module

public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.PayloadTimeliness`

The balance-weighted selection, and from Gloas the payload timeliness committee.

A balance-weighted selection draws candidates with a chance that grows with their balance.

It walks the candidates in turn, in their order or in shuffled order, and may draw one twice.

Each draw is the draw of a proposer at the fork of the state.

From Electra, that draw reads two random bytes.

Gloas selects the proposers and the payload timeliness committee this way.

From Altair, the sync committee is a selection of this kind too.

The payload timeliness committee of a slot votes on whether the payload of its block arrived.

It is a balance-weighted selection of a fixed size from the attestation committees of the slot.

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

The draw counter is a 64-bit integer, so the search fails when it would reach `2^64`.

The default candidate is never read when each position of the order is in range. -/
def balanceWeightedSearch (preset : Preset) (fork : Base.Fork) (indices : Array ValidatorIndex)
    (balances : Array Gwei) (order : Nat → Nat) (seed : Bytes32) (size : Nat)
    (selected : Array ValidatorIndex) (bound : selected.size ≤ size) (i : Nat) :
    Except AccessorError (Vector ValidatorIndex size) :=
  if full : selected.size = size then .ok ⟨selected, full⟩
  else do
    let position := order (i % indices.size)
    let accepted ← proposerDraw preset fork seed i (balances.getD position 0)
    let next : { next : Array ValidatorIndex // next.size ≤ size } :=
      if accepted then ⟨selected.push (indices.getD position 0), by simp; omega⟩
      else ⟨selected, bound⟩
    if i + 1 < 2 ^ 64 then
      balanceWeightedSearch preset fork indices balances order seed size next.1 next.2 (i + 1)
    else throw (.arith .overflow)
termination_by 2 ^ 64 - i

/-- A list of `size` candidates, each drawn with a chance that grows with its effective balance.

The candidates are read in their order, or in the order of the shuffle of their positions.

A candidate may be drawn more than once.

There must be at least one candidate, and each must name a validator. -/
def computeBalanceWeightedSelection (state : BeaconState preset fork)
    (indices : Array ValidatorIndex) (seed : Bytes32) (size : UInt64) (shuffleIndices : Bool) :
    Except AccessorError (Vector ValidatorIndex size.toNat) := do
  if indices.size = 0 then throw .noCandidates
  unless indices.size < 2 ^ 64 do throw (.arith .overflow)
  let balances ← indices.mapM fun index => return (← getValidator state index).effectiveBalance
  -- Each draw shuffles only its own position, so a draw costs the same at any count.
  let order : Nat → Nat :=
    if shuffleIndices then Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size
    else id
  balanceWeightedSearch preset fork indices balances order seed size.toNat #[] (Nat.zero_le _) 0

/-- The members of the attestation committees of a slot, committee after committee.

The committees share one shuffle of the active validators, computed once for the slot. -/
def slotCommitteeMembers (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError (Array ValidatorIndex) := do
  let epoch := computeEpochAtSlot preset slot
  let seed ← getSeed state epoch DOMAIN_BEACON_ATTESTER
  let active := (getActiveValidatorIndices state epoch).toArray
  let shuffled := computeShuffledPermutation preset (UInt64.ofNat active.size) seed
  (List.range (getCommitteeCountPerSlot state epoch).toNat).foldlM (fun members index => do
    return members ++ (← beaconCommitteeOf state slot index.toUInt64 active shuffled)) #[]

/-- The payload timeliness committee of a slot, which may hold a validator more than once.

It is drawn from the members of the attestation committees of the slot, in their order.

Its seed is the hash of the seed of the epoch for this duty and the slot as 8 bytes. -/
def computePtc (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError (PayloadTimelinessCommittee preset) := do
  let epochSeed ← getSeed state (computeEpochAtSlot preset slot) DOMAIN_PTC_ATTESTER
  let seed :=
    Cryptography.Hash.Sha256.hash32 ⟨epochSeed.toArray ++ (uintToBytes 8 slot.toNat).toArray⟩
  computeBalanceWeightedSelection state (← slotCommitteeMembers state slot) seed preset.PTC_SIZE
    false

/-- The position in the window of the committee of a slot.

The previous epoch comes first, then the current epoch and the lookahead.

The slot must be from the fork, and in one of those epochs. -/
def ptcWindowPosition (config : Config) (state : BeaconState preset fork) (slot : Slot) :
    Except AccessorError UInt64 := do
  let epoch := computeEpochAtSlot preset slot
  let outOfRange := AccessorError.ptcSlotOutOfRange slot state.slot
  unless config.GLOAS_FORK_EPOCH ≤ epoch do throw outOfRange
  let stateEpoch := getCurrentEpoch state
  if epoch < stateEpoch then
    unless epoch + 1 = stateEpoch do throw outOfRange
    return slot % preset.SLOTS_PER_EPOCH
  else
    unless epoch ≤ (← liftArith (addChecked stateEpoch preset.MIN_SEED_LOOKAHEAD)) do
      throw outOfRange
    let offset ← liftArith do
      mulChecked (← addChecked (epoch - stateEpoch) 1) preset.SLOTS_PER_EPOCH
    liftArith (addChecked offset (slot % preset.SLOTS_PER_EPOCH))

/-- The payload timeliness committee of a slot, as the window of the state keeps it. -/
def getPtc (config : Config) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (slot : Slot) : Except AccessorError (PayloadTimelinessCommittee preset) := do
  let position ← ptcWindowPosition config state slot
  match (state.ptcWindow gloas)[position.toNat]? with
  | some committee => return committee
  | none => throw (.ptcSlotOutOfRange slot state.slot)

/-- The members of a committee whose bit is set, in committee order. -/
def ptcAttesters (committee : PayloadTimelinessCommittee preset)
    (bits : PayloadTimelinessCommitteeBits preset) : List ValidatorIndex :=
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
  let committee ← getPtc config state gloas attestation.data.slot
  let attesters := ptcAttesters committee attestation.aggregationBits
  let sorted := attesters.mergeSort (· ≤ ·)
  return ⟨⟨sorted.toArray, by simpa [sorted] using length_ptcAttesters_le committee _⟩,
    attestation.data, attestation.signature⟩

/-- Whether an indexed vote of the committee has signers, in sorted order, and a valid signature.

The signature is an aggregate of the keys of the signers, over the vote, in the epoch of its slot.

An index may repeat, since the committee may hold a validator twice. -/
def isValidIndexedPayloadAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (attestation : IndexedPayloadAttestation preset) :
    Except TransitionError Bool := do
  let indices := attestation.attestingIndices.data.toList
  if indices = [] ∨ indices ≠ indices.mergeSort (· ≤ ·) then return false
  let pubkeys ← indices.toArray.mapM fun index => do
    return packBytes (← liftAccessor (getValidator state index)).pubkey
  let domain ← liftAccessor (getDomain config state DOMAIN_PTC_ATTESTER
    (some (computeEpochAtSlot preset attestation.data.slot)))
  let signingRoot ← liftSsz (computeSigningRoot attestation.data domain)
  return checks.fastAggregateVerify pubkeys (packBytes signingRoot)
    (packBytes attestation.signature)

/-- The state after a payload attestation of a block, which the state does not change.

The vote must be on the parent of the block, at the slot before that of the state.

Its signers must sign it, as an indexed vote of the committee of that slot. -/
def processPayloadAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (attestation : PayloadAttestation preset) :
    Except TransitionError (BeaconState preset fork) := do
  let data := attestation.data
  ensure (data.beaconBlockRoot = state.latestBlockHeader.parentRoot)
    .payloadAttestationNotForParent
  ensure (data.slot.toNat + 1 = state.slot.toNat)
    (.payloadAttestationWrongSlot data.slot state.slot)
  let indexed ← liftAccessor (getIndexedPayloadAttestation config state gloas attestation)
  let valid ← isValidIndexedPayloadAttestation config checks state indexed
  ensure (valid = true) .invalidPayloadAttestation
  return state

/-- The slot at a position of the window, counted from the first slot of an epoch.

The epoch is that of the position after the first. -/
def ptcWindowSlot (preset : Preset) (firstEpoch : Epoch) (position : Nat) :
    Except AccessorError Slot := liftArith do
  let perEpoch := preset.SLOTS_PER_EPOCH.toNat
  let epoch ← addChecked firstEpoch (position / perEpoch).toUInt64
  addChecked (← computeStartSlotAtEpoch preset epoch) (position % perEpoch).toUInt64

/-- The window of committees when the field first appears, at the fork or at genesis.

The previous epoch holds committees of index zero, and the other epochs their computed committees.
-/
def initializePtcWindow (state : BeaconState preset fork) :
    Except AccessorError (PayloadTimelinessCommitteeWindow preset) :=
  (Vector.range _).mapM fun position => do
    let perEpoch := preset.SLOTS_PER_EPOCH.toNat
    if position < perEpoch then return Vector.replicate _ 0
    computePtc state (← ptcWindowSlot preset (getCurrentEpoch state) (position - perEpoch))

/-- The state with its window of committees moved by one epoch.

The last epoch of the window becomes the epoch after the lookahead, with its computed committees.
-/
def processPtcWindow (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Except AccessorError (BeaconState preset fork) := do
  let window := state.ptcWindow gloas
  let perEpoch := preset.SLOTS_PER_EPOCH.toNat
  let nextEpoch ← liftArith do
    addChecked (← addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD) 1
  let moved ← (Vector.range _).mapM fun position =>
    if kept : position + perEpoch < _ then pure window[position + perEpoch]
    else do computePtc state (← ptcWindowSlot preset nextEpoch (position + perEpoch - window.size))
  return { state with ptcWindow := fun _ => moved }

end EthLib.Consensus
