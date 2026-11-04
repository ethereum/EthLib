module

public import EthLib.Base.Exports
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Shuffle

/-!
# `Exports.Shuffle`

C-ABI exports of the swap-or-not shuffle, under the rounds of a named preset.

The shuffled list comes back as a JSON list of integers.

A seed that is not 32 bytes, or an unknown name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result)

open Lean Base

/-- The message of a shuffle error, for a Python traceback. -/
def shuffleErrorText : ShuffleError → String
  | .indexOutOfRange index count => s!"index {index} is not below the index count {count}"
  | .noCommittee => "the committee count is zero"
  | .overflow => "a committee bound is 2^64 or more"

/-- The seed of 32 bytes. -/
def seedOf (seed : ByteArray) : Result Bytes32 :=
  if h : seed.size = 32 then return ⟨seed.data, by simpa using h⟩
  else throw (0, "a seed is 32 bytes")

/-- The shuffled position of every index below the count. -/
@[export eth_consensus_compute_shuffled_permutation]
def computeShuffledPermutationExport (name : ByteArray) (count : UInt64) (seed : ByteArray) :
    Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  return jsonBytes (toJson (computeShuffledPermutation preset count (← seedOf seed)).toList)

/-- The shuffled position of one index. -/
@[export eth_consensus_compute_shuffled_index]
def computeShuffledIndexExport (name : ByteArray) (index count : UInt64) (seed : ByteArray) :
    Result UInt64 := do
  let preset ← presetOf (← nameOf name)
  (computeShuffledIndex preset index count (← seedOf seed)).mapError
    fun e => (e.code, shuffleErrorText e)

end EthLib.Consensus.Exports
