module

public import EthLib.Base.LittleEndian
public import EthLib.Consensus.Preset
public import EthLib.Cryptography.Hash.Sha256

/-!
# `Consensus.Shuffle`

The beacon chain shuffles the active validators of an epoch with a public seed.

It cuts the shuffled list into committees, so each committee is a pseudorandom sample.

The shuffle is the swap-or-not cipher on a general domain, from [Hoang, Morris and Rogaway].

Each round draws a pivot, and pairs each index with its reflection about that pivot.

A pair swaps or not, by one pseudorandom bit that both members of the pair read.

[Hoang, Morris and Rogaway]: https://doi.org/10.1007/978-3-642-32009-5_1
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- Why a shuffle or a committee has no value. -/
inductive ShuffleError where
  /-- The index is not below the number of indices. -/
  | indexOutOfRange (index count : UInt64)
  /-- There are no committees to cut the indices into. -/
  | noCommittee
  /-- A bound of the committee is `2^64` or more. -/
  | overflow
  /-- The count is above `2^40`, so a position has a bucket number of more than 4 bytes. -/
  | countTooLarge (count : UInt64)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning.

The custody errors take the codes from 1, and the subnet errors from 101, in the same Python class.

So the shuffle errors take the codes from 201. -/
def ShuffleError.code : ShuffleError → UInt32
  | .indexOutOfRange _ _ => 201
  | .noCommittee => 202
  | .overflow => 203
  | .countTooLarge _ => 204

namespace Shuffle

/-- The seed followed by the round number, as one byte. -/
def roundInput (seed : Bytes32) (round : Nat) : ByteArray :=
  ⟨seed.toArray.push (UInt8.ofNat round)⟩

/-- The pivot of a round: the first eight bytes of a hash, little-endian, modulo the count. -/
def pivot (seed : Bytes32) (round count : Nat) : Nat :=
  bytesToUint ((Cryptography.Hash.Sha256.hash32 (roundInput seed round)).take 8) % count

/-- The 256 bits of a round that decide the positions of one bucket of 256 positions. -/
def bucketBits (seed : Bytes32) (round bucket : Nat) : ByteArray :=
  Cryptography.Hash.Sha256.hash
    ⟨(roundInput seed round).data ++ (uintToBytes 4 bucket).toArray⟩

/-- The bit of a position in the bits of its bucket, least significant first in each byte. -/
def bitAt (bits : ByteArray) (position : Nat) : Bool :=
  (bits.data.getD (position % 256 / 8) 0).toNat / 2 ^ (position % 8) % 2 == 1

/-- One round of swap-or-not on one index.

The index pairs with its reflection about the pivot, modulo the count.

The bit at the greater of the two decides the swap, so both read the same bit. -/
def swapOrNot (count pivot : Nat) (bit : Nat → Bool) (index : Nat) : Nat :=
  let flip := (pivot + count - index) % count
  if bit (max index flip) then flip else index

/-- One round on every index.

Each bucket of 256 positions is hashed once for the round. -/
def round (seed : Bytes32) (count roundNumber : Nat) (indices : Array Nat) : Array Nat :=
  let buckets := Array.ofFn (n := count / 256 + 1) fun bucket =>
    bucketBits seed roundNumber bucket.val
  let bit position := bitAt (buckets.getD (position / 256) .empty) position
  indices.map (swapOrNot count (pivot seed roundNumber count) bit)

/-- One round of swap-or-not on one index, hashing the bucket of its position directly. -/
def indexRound (seed : Bytes32) (count roundNumber index : Nat) : Nat :=
  swapOrNot count (pivot seed roundNumber count)
    (fun position => bitAt (bucketBits seed roundNumber (position / 256)) position) index

/-- Every round of a preset on one index, in order.

Each round hashes twice, for the pivot and for the bucket, whatever the count. -/
def shuffledIndex (rounds : Nat) (seed : Bytes32) (count index : Nat) : Nat :=
  (List.range rounds).foldl (fun index roundNumber => indexRound seed count roundNumber index) index

/-- Every round on each index below the count, in order, one round at a time for all of them. -/
def shuffledPositions (rounds : Nat) (seed : Bytes32) (count : Nat) : Array UInt64 :=
  ((List.range rounds).foldl (fun indices roundNumber => round seed count roundNumber indices)
    (Array.range count)).map UInt64.ofNat

end Shuffle

/-- The shuffled position of each index below the count, after every round of the preset.

The count must be at most `2^40`.

A shuffle of more indices reaches a position whose bucket number does not fit in 4 bytes.

The check comes before any round. -/
def computeShuffledPermutation (preset : Preset) (count : UInt64) (seed : Bytes32) :
    Except ShuffleError (Array UInt64) :=
  if count.toNat ≤ 2 ^ 40 then
    .ok (Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed count.toNat)
  else .error (.countTooLarge count)

/-- The shuffled position of one index, which must be below the count.

The count must be at most `2^40`.

A shuffle of more indices reaches a position whose bucket number does not fit in 4 bytes.

Both checks come before any round.

It runs the rounds on that index alone, so its cost does not grow with the count. -/
def computeShuffledIndex (preset : Preset) (index count : UInt64) (seed : Bytes32) :
    Except ShuffleError UInt64 :=
  if index < count then
    if count.toNat ≤ 2 ^ 40 then
      .ok (UInt64.ofNat
        (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed count.toNat index.toNat))
    else .error (.countTooLarge count)
  else .error (.indexOutOfRange index count)

/-- Committee `index` of `count`, cut from a list of indices in the order of shuffled positions.

It reads the shuffled positions from `len * index / count` up to `len * (index + 1) / count`.

A position past the last index is out of range, which happens only when `index ≥ count`.

An empty range has no position to read, so it gives an empty committee, even past the end.

The default value is never read when each shuffled position is below the length.

It takes the shuffled positions as an argument, so the committees of an epoch can share one shuffle.

It gives the committee of the rule when those positions are the shuffle of the list. -/
def shuffledCommittee (indices : Array ValidatorIndex) (shuffled : Array UInt64)
    (index count : UInt64) : Except ShuffleError (Array ValidatorIndex) := do
  if count = 0 then throw .noCommittee
  unless index.toNat + 1 < 2 ^ 64 ∧ indices.size * (index.toNat + 1) < 2 ^ 64 do
    throw .overflow
  let start := indices.size * index.toNat / count.toNat
  let stop := indices.size * (index.toNat + 1) / count.toNat
  -- The first position to shuffle at or past the length is the larger of the two.
  if start < stop ∧ indices.size < stop then
    throw (.indexOutOfRange (UInt64.ofNat (max start indices.size)) (UInt64.ofNat indices.size))
  return ((List.range (stop - start)).map fun i =>
    indices.getD (shuffled.getD (start + i) 0).toNat 0).toArray

/-- Committee `index` of `count`, cut from the shuffled list of indices.

It fails as the shuffle does, before it cuts the committee. -/
def computeCommittee (preset : Preset) (indices : Array ValidatorIndex) (seed : Bytes32)
    (index count : UInt64) : Except ShuffleError (Array ValidatorIndex) := do
  shuffledCommittee indices
    (← computeShuffledPermutation preset (UInt64.ofNat indices.size) seed) index count

end EthLib.Consensus
