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
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ShuffleError.code : ShuffleError → UInt32
  | .indexOutOfRange _ _ => 1
  | .noCommittee => 2
  | .overflow => 3

namespace Shuffle

/-- The seed followed by the round number, as one byte. -/
def roundInput (seed : Bytes32) (round : Nat) : ByteArray :=
  ⟨seed.toArray.push (UInt8.ofNat round)⟩

/-- The pivot of a round: the first eight bytes of a hash, little-endian, modulo the count. -/
def pivot (seed : Bytes32) (round count : Nat) : Nat :=
  let digest := Cryptography.Hash.Sha256.hash (roundInput seed round)
  bytesToUint (Vector.ofFn fun i : Fin 8 => digest.data.getD i.val 0) % count

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

end Shuffle

/-- The shuffled position of each index below the count, after every round of the preset. -/
def computeShuffledPermutation (preset : Preset) (count : UInt64) (seed : Bytes32) :
    Array UInt64 :=
  let rounds := (List.range preset.SHUFFLE_ROUND_COUNT.toNat).foldl
    (fun indices roundNumber => Shuffle.round seed count.toNat roundNumber indices)
    (Array.range count.toNat)
  rounds.map UInt64.ofNat

/-- The shuffled position of one index, which must be below the count. -/
def computeShuffledIndex (preset : Preset) (index count : UInt64) (seed : Bytes32) :
    Except ShuffleError UInt64 :=
  if index < count then .ok ((computeShuffledPermutation preset count seed).getD index.toNat 0)
  else .error (.indexOutOfRange index count)

/-- Committee `index` of `count`, cut from the shuffled list of indices.

It holds the shuffled indices from `len * index / count` up to `len * (index + 1) / count`.

The default value is never read, since each shuffled position is below the length. -/
def computeCommittee (preset : Preset) (indices : Array ValidatorIndex) (seed : Bytes32)
    (index count : UInt64) : Except ShuffleError (Array ValidatorIndex) := do
  if count = 0 then throw .noCommittee
  unless index.toNat + 1 < 2 ^ 64 ∧ indices.size * (index.toNat + 1) < 2 ^ 64 do
    throw .overflow
  let start := indices.size * index.toNat / count.toNat
  let stop := indices.size * (index.toNat + 1) / count.toNat
  let shuffled := computeShuffledPermutation preset (UInt64.ofNat indices.size) seed
  return ((List.range (stop - start)).map fun i =>
    indices.getD (shuffled.getD (start + i) 0).toNat 0).toArray

end EthLib.Consensus
