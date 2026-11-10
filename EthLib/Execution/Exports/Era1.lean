module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Execution.History.Era1

/-!
# `Exports.Era1`

C-ABI exports for era1 files, callable from the Python C extension.

A rejected file comes back as the code of its error, and a message that names the fault.
-/

public section

namespace EthLib.Execution.History.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- The contents of an era1 file, as plain values.

They are the first block number, the blocks, the other records and the accumulator.

Each block is its header, body and receipts as RLP, and its total difficulty.

Each other record is its type and its data. -/
def decodeEra1Of (bytes : ByteArray) :
    Result (Nat × List (ByteArray × ByteArray × ByteArray × Nat) × List (Nat × ByteArray) ×
      ByteArray) := do
  let era1 ← (decodeEra1 bytes).mapError fun e => (e.code, s!"era1 file rejected: {repr e}")
  return (era1.startingNumber,
    era1.blocks.map fun b => (b.header, b.body, b.receipts, b.totalDifficulty.toNat),
    era1.others.map fun r => (r.type.toNat, r.data),
    ⟨era1.accumulator.toArray⟩)

/-- The contents of an era1 file.

They are the first block number, the blocks, the other records and the accumulator.

Each block is its header, body and receipts as RLP, and its total difficulty.

Each other record is its type and its data.

An argument of the wrong shape has code 0.

A file that is not a valid era1 file has the code of its fault. -/
@[export eth_era1_decode]
def decodeEra1Export (args : PyValue) : Result PyValue :=
  pyExport decodeEra1Of args

end EthLib.Execution.History.Exports
