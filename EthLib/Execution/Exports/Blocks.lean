module

public import EthLib.Execution.Blocks
public import EthLib.Serialization.Exports.Rlp

/-!
# `Exports.Blocks`

C-ABI exports for headers and blocks, callable from the Python C extension.

A fork crosses the boundary as the name of its case in Lean, such as `shapella`.

A header or a block crosses it as its RLP bytes.

Each operation decodes at the fork first, and a rejected input becomes an error.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Serialization.Rlp.Exports (runRlp)

/-- The fork with the given name, or an error.

The cases of the fork type are read through their positions, so no name is written twice. -/
def forkOfName (name : ByteArray) : IO Fork := do
  let some name := String.fromUTF8? name | throw (IO.userError "fork name is not UTF-8")
  -- Positions past the last case map to the last case, so 256 positions cover them all.
  let forks := (List.range 256).map Fork.ofNat
  match forks.find? (fun f => ((reprStr f).splitOn ".").getLast? == some name) with
  | some f => return f
  | none => throw (IO.userError s!"unknown fork {name}")

/-- The hash of a header in RLP form, after the decoder at the fork accepts it. -/
@[export eth_block_header_hash]
def headerHashExport (fork header : ByteArray) : IO ByteArray := do
  let fork ← forkOfName fork
  let h : Header fork ← runRlp "header rejected" (Codec.decode header)
  return ⟨(← runRlp "header has no hash" h.hash).toArray⟩

/-- The RLP form of a block, decoded at the fork and encoded again.

Each transaction stays the item that it is, so any transaction form passes. -/
@[export eth_block_reencode]
def reencodeExport (fork block : ByteArray) : IO ByteArray := do
  let fork ← forkOfName fork
  let b : Block fork Item ← runRlp "block rejected" (Codec.decode block)
  runRlp "block has no encoding" (Codec.encode b)

end EthLib.Execution.Blocks.Exports
