module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.ForkChoice.OptimisticSync

/-!
# `Exports.OptimisticSync`

C-ABI exports of the optimistic sync of Bellatrix.

The preset and the fork are named, at a fork from Bellatrix to Fulu.

They are named by `str` in the exports that take typed values, and in UTF-8 in the others.

A block comes as SSZ bytes, and a root as 32 bytes.

The exports of the ancestor and of the payload verdicts take and return typed values.

They take the optimistic roots as a list.

An optimistic store is built from its blocks, each under the root of its SSZ bytes.

An input that does not decode, an unknown name or a fork without the rule has code 0.

A failed step has the code of its fork choice error.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- The result of a step of optimistic sync, with the code of its error. -/
def runOptimistic {α : Type} (result : Except ForkChoiceError α) : Result α :=
  result.mapError fun e => (e.code, s!"optimistic sync failed with code {e.code}")

/-- The preset and the fork, which must be from Bellatrix to Fulu, or code 0. -/
def optimisticPresetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  let (preset, fork) ← transitionPresetAndFork name fork
  unless .bellatrix ≤ fork ∧ fork < .glamsterdam do
    throw (0, s!"no optimistic sync at {fork.name}")
  return (preset, fork)

/-- An optimistic store from its optimistic roots and the SSZ bytes of its blocks.

The head is the zero root, which no rule of these exports reads. -/
def optimisticStoreOf (preset : Preset) (fork : Fork) (blocks : Array ByteArray)
    (optimisticRoots : List Root) : Result (OptimisticStore preset fork) := do
  let decoded ← blocks.toList.mapM fun bytes => do
    let block ← decodeInput (BeaconBlock preset fork) bytes
    let root ← (SszType.hashTreeRoot block).mapError fun e => (0, s!"block rejected: {reprStr e}")
    return (root, block)
  return {
    optimisticRoots := optimisticRoots
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
  let store ← optimisticStoreOf preset fork blocks []
  let block ← decodeInput (BeaconBlock preset fork) block
  runOptimistic (store.isOptimisticCandidateBlock currentSlot block safeSlots)

/-- From Bellatrix: the root of the latest block of a chain that is not optimistic. -/
def latestVerifiedAncestorOf (args : String × String × Array ByteArray × List Root × Root) :
    Result Root := do
  let (name, fork, blocks, optimisticRoots, root) := args
  let (preset, fork) ← optimisticPresetAndFork name.toUTF8 fork.toUTF8
  let store ← optimisticStoreOf preset fork blocks optimisticRoots
  runOptimistic (store.latestVerifiedAncestor root)

/-- From Bellatrix: the root of the latest block of a chain that is not optimistic.

The arguments are the names of the preset and the fork, the blocks and the optimistic roots.

Then comes the root of a block.
-/
@[export eth_consensus_latest_verified_ancestor]
def latestVerifiedAncestorExport (args : PyValue) : Result PyValue :=
  pyExport latestVerifiedAncestorOf args

/-- From Bellatrix: the optimistic roots after the payload of a block is found valid. -/
def onValidPayloadOf (args : String × String × Array ByteArray × List Root × Root) :
    Result (List Root) := do
  let (name, fork, blocks, optimisticRoots, root) := args
  let (preset, fork) ← optimisticPresetAndFork name.toUTF8 fork.toUTF8
  let store ← optimisticStoreOf preset fork blocks optimisticRoots
  return (← runOptimistic (store.onValidPayload root)).optimisticRoots

/-- From Bellatrix: the optimistic roots after the payload of a block is found valid, as a list.

The arguments are the names of the preset and the fork, the blocks and the optimistic roots.

Then comes the root of a block.
-/
@[export eth_consensus_on_valid_payload]
def onValidPayloadExport (args : PyValue) : Result PyValue := pyExport onValidPayloadOf args

/-- From Bellatrix: the optimistic roots after a block is found to be the first invalid one. -/
def onInvalidatedPayloadOf (args : String × String × Array ByteArray × List Root × Root) :
    Result (List Root) := do
  let (name, fork, blocks, optimisticRoots, first) := args
  let (preset, fork) ← optimisticPresetAndFork name.toUTF8 fork.toUTF8
  let store ← optimisticStoreOf preset fork blocks optimisticRoots
  return (← runOptimistic (store.onInvalidatedPayload first)).optimisticRoots

/-- From Bellatrix: the optimistic roots after a block is found the first invalid one, as a list.

The arguments are the names of the preset and the fork, the blocks and the optimistic roots.

Then comes the root of the first invalid block. -/
@[export eth_consensus_on_invalidated_payload]
def onInvalidatedPayloadExport (args : PyValue) : Result PyValue :=
  pyExport onInvalidatedPayloadOf args

/-- Whether an optimistic validator may not sign under a domain type of 4 bytes. -/
@[export eth_consensus_is_optimistic_restricted_domain]
def isOptimisticRestrictedDomainExport (domainType : ByteArray) : Result Bool := do
  if sized : domainType.size = 4 then
    return isOptimisticRestrictedDomain ⟨domainType.data, sized⟩
  else throw (0, s!"a domain type is 4 bytes, not {domainType.size}")

end EthLib.Consensus.Exports
