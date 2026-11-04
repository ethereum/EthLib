module

public import EthLib.Base.Exports
public import EthLib.Execution.Blocks
public import EthLib.Serialization.Exports.Rlp

/-!
# `Exports.Blocks`

C-ABI exports for headers and blocks, callable from the Python C extension.

A fork crosses the boundary as the name of its case in Lean, such as `shapella`.

A header, a block or a receipt crosses it as its bytes.

Each operation decodes at the fork first.

A rejected input comes back as the code and the message of its RLP error.

A receipt error has a code from 101, and a failed header check a code from 201.

An unknown fork name, or forks out of order, has code 0, since no error type covers it.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Exports (Result forkOfName)

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Serialization.Rlp.Exports (runRlp)

/-- Run a fallible decoding or encoding, with its error as a code and a message. -/
def runRlp {α : Type} (what : String) (act : Except RlpError α) : Result α :=
  act.mapError fun e => (e.code, s!"{what}: {reprStr e}")

/-- The hash of a header in RLP form, after the decoder at the fork accepts it. -/
@[export eth_block_header_hash]
def headerHashExport (fork header : ByteArray) : Result ByteArray := do
  let fork ← forkOfName fork
  let h : Header fork ← runRlp "header rejected" (Codec.decode header)
  return ⟨(← runRlp "header has no hash" h.hash).toArray⟩

/-- The RLP form of a block, decoded at the fork and encoded again.

Each transaction stays the item that it is, so any transaction form passes. -/
@[export eth_block_reencode]
def reencodeExport (fork block : ByteArray) : Result ByteArray := do
  let fork ← forkOfName fork
  let b : Block fork Item ← runRlp "block rejected" (Codec.decode block)
  runRlp "block has no encoding" (Codec.encode b)

/-- The transaction type and the receipt that some bytes hold at the fork. -/
def decodeReceiptAt (fork : Fork) (receipt : ByteArray) : Result (UInt8 × Receipt fork) :=
  (decodeReceipt fork receipt).mapError fun e => (e.code, s!"receipt rejected: {reprStr e}")

/-- The bytes of a receipt, decoded at the fork and encoded again with its transaction type. -/
@[export eth_receipt_reencode]
def receiptReencodeExport (fork receipt : ByteArray) : Result ByteArray := do
  let fork ← forkOfName fork
  let (type, r) ← decodeReceiptAt fork receipt
  runRlp "receipt has no encoding" (encodeReceipt type r)

/-- The logs Bloom filter of the logs of a receipt, decoded at the fork. -/
@[export eth_receipt_logs_bloom]
def receiptLogsBloomExport (fork receipt : ByteArray) : Result ByteArray := do
  let fork ← forkOfName fork
  let (_, r) ← decodeReceiptAt fork receipt
  return ⟨(logsBloom r.logs).toArray⟩

/-- Check a header at a fork against its parent at the parent's fork, from Paris on. -/
@[export eth_block_validate_header]
def validateHeaderExport (parentFork fork parent header : ByteArray) : Result UInt8 := do
  let parentFork ← forkOfName parentFork
  let fork ← forkOfName fork
  let parent : Header parentFork ← runRlp "parent rejected" (Codec.decode parent)
  let header : Header fork ← runRlp "header rejected" (Codec.decode header)
  if hLondon : .london ≤ parentFork then
    if hFork : parentFork ≤ fork then
      if hParis : .paris ≤ fork then
        (validateHeader hLondon hFork hParis parent header).map (fun () => 1) |>.mapError
          fun e => (e.code, s!"header invalid: {reprStr e}")
      else throw (0, "the fork is before Paris")
    else throw (0, "the parent's fork is after the fork")
  else throw (0, "the parent's fork is before London")

end EthLib.Execution.Blocks.Exports
