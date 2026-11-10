module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.History.Era

/-!
# `Exports.Era`

C-ABI exports for era files, callable from the Python C extension.

A preset and a configuration are named together, by `mainnet` or `minimal`.

The configuration takes the replacements that a `dict` gives, such as the epochs of the forks.

A rejected file comes back as the code of its error, and a message that names the fault.
-/

public section

namespace EthLib.Consensus.History.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Consensus.Exports (configWithValue presetOf)
open Serialization.Ssz

/-- The SSZ bytes of a value of an accepted file, which encode again as they decoded. -/
def sszBytes {α : Type} [SszType α] (value : α) : Result ByteArray :=
  (SszType.serialize value).mapError fun e => (0, s!"value rejected: {reprStr e}")

/-- One block of a group, as plain values: its slot, its fork, its SSZ bytes and its root. -/
def blockOf {preset : Preset} (block : EraBlock preset) :
    Result (Nat × String × ByteArray × ByteArray) := do
  return (block.slot.toNat, block.fork.name, ← sszBytes block.block, ⟨block.root.toArray⟩)

/-- One group, as plain values.

They are the era, the blocks, the fork and SSZ bytes of the state, and the other records. -/
def groupOf {preset : Preset} (group : EraGroup preset) :
    Result (Nat × List (Nat × String × ByteArray × ByteArray) × String × ByteArray ×
      List (Nat × ByteArray)) := do
  return (group.era, ← group.blocks.mapM blockOf, group.fork.name, ← sszBytes group.state,
    group.others.map fun r => (r.type.toNat, r.data))

/-- The name of the file and its groups, as plain values.

A file whose name cannot be computed has none, as when the state of its highest era has no root.

A value that does not encode again has code 0. -/
def decodeEraOf (args : String × Option PyValue × ByteArray) :
    Result (Option String ×
      List (Nat × List (Nat × String × ByteArray × ByteArray) × String × ByteArray ×
        List (Nat × ByteArray))) := do
  let (name, replacements, bytes) := args
  let preset ← presetOf name
  let config ← configWithValue name replacements
  let groups ← (decodeEra preset config bytes).mapError fun e =>
    (e.code, s!"era file rejected: {repr e}")
  let fileName := match groups with
    | first :: rest => (eraFileName config first rest).toOption
    | [] => none
  return (fileName, ← groups.mapM groupOf)

/-- The name and the groups of an era file.

The arguments are the name of the preset and the configuration, the replacements, and the bytes.

Each group is its era, its blocks, the fork and SSZ bytes of its state, and its other records.

Each block is its slot, its fork, its SSZ bytes and its root.

Each other record is its type and its data.

The name is `None` when it cannot be computed, as when the state of the highest era has no root.

An argument of the wrong shape, or an unknown name, has code 0.

A file that is not a valid era file has the code of its fault. -/
@[export eth_era_decode]
def decodeEraExport (args : PyValue) : Result PyValue :=
  pyExport decodeEraOf args

end EthLib.Consensus.History.Exports
