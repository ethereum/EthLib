module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.ForkChoice.OptimisticSync

/-!
# `Exports.OptimisticSync`

C-ABI exports of the optimistic sync of Bellatrix.

The preset and the fork are named in UTF-8, at a fork from Bellatrix to Fulu.

A block comes as SSZ bytes, and a root or a list of roots as 32 bytes each.

An optimistic store is built from its blocks, each under the root of its SSZ bytes.

An input that does not decode, an unknown name or a fork without the rule has code 0.

A failed step has the code of its fork choice error.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result)

/-- The result of a step of optimistic sync, with the code of its error. -/
def runOptimistic {α : Type} (result : Except ForkChoiceError α) : Result α :=
  result.mapError fun e => (e.code, s!"optimistic sync failed with code {e.code}")

/-- The preset and the fork, which must be from Bellatrix to Fulu, or code 0. -/
def optimisticPresetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  let (preset, fork) ← transitionPresetAndFork name fork
  unless .bellatrix ≤ fork ∧ fork < .glamsterdam do
    throw (0, s!"no optimistic sync at {fork.name}")
  return (preset, fork)

/-- A root from 32 bytes, or code 0. -/
def optimisticRootOf (bytes : ByteArray) : Result Root :=
  if sized : bytes.size = 32 then return ⟨bytes.data, sized⟩
  else throw (0, s!"a root is 32 bytes, not {bytes.size}")

/-- A list of roots from their bytes, 32 bytes each, or code 0. -/
def optimisticRootsOf (bytes : ByteArray) : Result (List Root) := do
  unless bytes.size % 32 = 0 do throw (0, s!"a list of roots is 32 bytes each, not {bytes.size}")
  (List.range (bytes.size / 32)).mapM fun index =>
    optimisticRootOf (bytes.extract (32 * index) (32 * index + 32))

/-- The bytes of a list of roots, 32 bytes each, in order. -/
def optimisticRootsBytes (roots : List Root) : ByteArray :=
  roots.foldl (fun bytes root => bytes ++ Base.packBytes root) ByteArray.empty

/-- An optimistic store from its optimistic roots and the SSZ bytes of its blocks.

The head is the zero root, which no rule of these exports reads. -/
def optimisticStoreOf (preset : Preset) (fork : Fork) (blocks : Array ByteArray)
    (optimisticRoots : ByteArray) : Result (OptimisticStore preset fork) := do
  let decoded ← blocks.toList.mapM fun bytes => do
    let block ← decodeInput (BeaconBlock preset fork) bytes
    let root ← (SszType.hashTreeRoot block).mapError fun e => (0, s!"block rejected: {reprStr e}")
    return (root, block)
  return {
    optimisticRoots := ← optimisticRootsOf optimisticRoots
    headBlockRoot := Vector.replicate 32 0
    blocks := Std.TreeMap.ofList decoded }

/-- From Bellatrix: whether a block carries a payload other than the empty one. -/
@[export eth_consensus_is_execution_block]
def isExecutionBlockExport (name fork block : ByteArray) : Result Bool := do
  let (preset, fork) ← optimisticPresetAndFork name fork
  return isExecutionBlock (← decodeInput (BeaconBlock preset fork) block)

/-- From Bellatrix: whether a block may be imported optimistically, given the known blocks.

The clock is at a slot, and the user sets the number of slots to wait. -/
@[export eth_consensus_is_optimistic_candidate_block]
def isOptimisticCandidateBlockExport (name fork : ByteArray) (blocks : Array ByteArray)
    (currentSlot safeSlots : UInt64) (block : ByteArray) : Result Bool := do
  let (preset, fork) ← optimisticPresetAndFork name fork
  let store ← optimisticStoreOf preset fork blocks ByteArray.empty
  let block ← decodeInput (BeaconBlock preset fork) block
  runOptimistic (store.isOptimisticCandidateBlock currentSlot block safeSlots)

/-- From Bellatrix: the root of the latest block of a chain that is not optimistic. -/
@[export eth_consensus_latest_verified_ancestor]
def latestVerifiedAncestorExport (name fork : ByteArray) (blocks : Array ByteArray)
    (optimisticRoots root : ByteArray) : Result ByteArray := do
  let (preset, fork) ← optimisticPresetAndFork name fork
  let store ← optimisticStoreOf preset fork blocks optimisticRoots
  return Base.packBytes (← runOptimistic (store.latestVerifiedAncestor (← optimisticRootOf root)))

/-- From Bellatrix: the optimistic roots after the payload of a block is found valid. -/
@[export eth_consensus_on_valid_payload]
def onValidPayloadExport (name fork : ByteArray) (blocks : Array ByteArray)
    (optimisticRoots root : ByteArray) : Result ByteArray := do
  let (preset, fork) ← optimisticPresetAndFork name fork
  let store ← optimisticStoreOf preset fork blocks optimisticRoots
  let after ← runOptimistic (store.onValidPayload (← optimisticRootOf root))
  return optimisticRootsBytes after.optimisticRoots

/-- From Bellatrix: the optimistic roots after a block is found to be the first invalid one. -/
@[export eth_consensus_on_invalidated_payload]
def onInvalidatedPayloadExport (name fork : ByteArray) (blocks : Array ByteArray)
    (optimisticRoots first : ByteArray) : Result ByteArray := do
  let (preset, fork) ← optimisticPresetAndFork name fork
  let store ← optimisticStoreOf preset fork blocks optimisticRoots
  let after ← runOptimistic (store.onInvalidatedPayload (← optimisticRootOf first))
  return optimisticRootsBytes after.optimisticRoots

/-- Whether an optimistic validator may not sign under a domain type of 4 bytes. -/
@[export eth_consensus_is_optimistic_restricted_domain]
def isOptimisticRestrictedDomainExport (domainType : ByteArray) : Result Bool := do
  if sized : domainType.size = 4 then
    return isOptimisticRestrictedDomain ⟨domainType.data, sized⟩
  else throw (0, s!"a domain type is 4 bytes, not {domainType.size}")

end EthLib.Consensus.Exports
