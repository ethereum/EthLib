module

public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Shuffle

/-!
# `Exports.Shuffle`

C-ABI exports of the swap-or-not shuffle, under the rounds of a named preset.

The exports take typed Python values, and the shuffled list comes back as a list of integers.

A seed that is not 32 bytes, or an unknown name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result PyValue pyExport)

open Lean Base

/-- The message of a shuffle error, for a Python traceback. -/
def shuffleErrorText : ShuffleError → String
  | .indexOutOfRange index count => s!"index {index} is not below the index count {count}"
  | .noCommittee => "the committee count is zero"
  | .overflow => "a committee bound is 2^64 or more"
  | .countTooLarge count => s!"the index count {count} is above 2^40"

/-- The shuffled position of every index below the count, which must be at most `2^40`. -/
def computeShuffledPermutationOf (args : String × UInt64 × Bytes32) : Result (List UInt64) := do
  let (name, count, seed) := args
  let preset ← presetOf name
  let shuffled ← (computeShuffledPermutation preset count seed).mapError
    fun e => (e.code, shuffleErrorText e)
  return shuffled.toList

/-- The shuffled position of every index below a count of at most `2^40`, as a list.

The arguments are the name of the preset, the count and the seed of 32 bytes. -/
@[export eth_consensus_compute_shuffled_permutation]
def computeShuffledPermutationExport (args : PyValue) : Result PyValue :=
  pyExport computeShuffledPermutationOf args

/-- The shuffled position of one index. -/
def computeShuffledIndexOf (args : String × UInt64 × UInt64 × Bytes32) : Result UInt64 := do
  let (name, index, count, seed) := args
  let preset ← presetOf name
  (computeShuffledIndex preset index count seed).mapError fun e => (e.code, shuffleErrorText e)

/-- The shuffled position of one index.

The arguments are the name of the preset, the index, the count and the seed of 32 bytes. -/
@[export eth_consensus_compute_shuffled_index]
def computeShuffledIndexExport (args : PyValue) : Result PyValue :=
  pyExport computeShuffledIndexOf args

end EthLib.Consensus.Exports
