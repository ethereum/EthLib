module

public import EthLib.Consensus.Containers.Execution
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.Ssz`

A C-ABI export that reads the bytes of a beacon container, for the static SSZ test vectors.

The container is named as the source names it, at a preset and a fork.

The export decodes the bytes, then returns the root of the value and its bytes encoded again.

A name with no container at the fork comes back as code 0, since no error type covers it.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)
open Serialization.Ssz.Exports (runSsz)

/-- A container type of the beacon chain, with its SSZ codec. -/
structure Container where
  /-- The Lean type of the container. -/
  type : Type
  /-- Its SSZ codec. -/
  [codec : SszType type]

attribute [instance] Container.codec

/-- The container of a name at a preset and a fork, if the fork has one. -/
def containerOf (preset : Preset) (fork : Fork) : String → Option Container
  | "Withdrawal" => if .shapella ≤ fork then some ⟨Withdrawal⟩ else none
  | "ExecutionPayload" =>
    if .bellatrix ≤ fork then some ⟨ExecutionPayload preset fork⟩ else none
  | _ => none

/-- The root of the value that the bytes encode, then the bytes of that value.

The preset, the fork and the container are named in UTF-8. -/
@[export eth_consensus_ssz_static]
def sszStaticExport (name fork type data : ByteArray) : Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  let type ← nameOf type
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  let root ← runSsz "root rejected" (SszType.hashTreeRoot value)
  let bytes ← runSsz "value rejected" (SszType.serialize value)
  return ⟨root.toArray⟩ ++ bytes

end EthLib.Consensus.Exports
