module

public import EthLib.Execution.Blocks
public import EthLib.Serialization.Exports.Rlp

/-!
# `Exports.Blocks`

C-ABI exports for headers and blocks, callable from the Python C extension.

A fork crosses the boundary as the name of its case in Lean, such as `shapella`.

A header, a block or a receipt crosses it as its bytes.

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

/-- The transaction type and the receipt that some bytes hold at the fork. -/
def decodeReceiptIO (fork : Fork) (receipt : ByteArray) : IO (UInt8 × Receipt fork) :=
  match decodeReceipt fork receipt with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"receipt rejected: {reprStr e}")

/-- The bytes of a receipt, decoded at the fork and encoded again with its transaction type. -/
@[export eth_receipt_reencode]
def receiptReencodeExport (fork receipt : ByteArray) : IO ByteArray := do
  let fork ← forkOfName fork
  let (type, r) ← decodeReceiptIO fork receipt
  runRlp "receipt has no encoding" (encodeReceipt type r)

/-- The logs Bloom filter of the logs of a receipt, decoded at the fork. -/
@[export eth_receipt_logs_bloom]
def receiptLogsBloomExport (fork receipt : ByteArray) : IO ByteArray := do
  let fork ← forkOfName fork
  let (_, r) ← decodeReceiptIO fork receipt
  return ⟨(logsBloom r.logs).toArray⟩

end EthLib.Execution.Blocks.Exports
