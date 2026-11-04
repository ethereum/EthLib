module

public import EthLib.Base.Exports
public import EthLib.Execution.Blocks
public import EthLib.Execution.Transactions.Envelope
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

So does a transaction of a block that does not decode, and a trie with an empty value.

A deposit log in another layout has a code from 301.

Every operation here holds up to Glamsterdam, and Hegotá is not yet specified.

Glamsterdam adds two header fields, by EIP-7928 and EIP-7843.

The encodings of the body and the receipt stay those of BPO2.

So do the checks of a header against its parent.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Exports (Result forkUpTo)

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Serialization.Rlp.Exports (runRlp)

/-- Run a fallible decoding or encoding, with its error as a code and a message. -/
def runRlp {α : Type} (what : String) (act : Except RlpError α) : Result α :=
  act.mapError fun e => (e.code, s!"{what}: {reprStr e}")

/-- The hash of a header in RLP form, after the decoder at the fork accepts it. -/
@[export eth_block_header_hash]
def headerHashExport (fork header : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let h : Header fork ← runRlp "header rejected" (Codec.decode header)
  return ⟨(← runRlp "header has no hash" h.hash).toArray⟩

/-- The RLP form of a block, decoded at the fork and encoded again.

Each transaction stays the item that it is, so any transaction form passes. -/
@[export eth_block_reencode]
def reencodeExport (fork block : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let b : Block fork Item ← runRlp "block rejected" (Codec.decode block)
  runRlp "block has no encoding" (Codec.encode b)

/-- The transaction type and the receipt that some bytes hold at the fork. -/
def decodeReceiptAt (fork : Fork) (receipt : ByteArray) : Result (UInt8 × Receipt fork) :=
  (decodeReceipt fork receipt).mapError fun e => (e.code, s!"receipt rejected: {reprStr e}")

/-- The bytes of a receipt, decoded at the fork and encoded again with its transaction type. -/
@[export eth_receipt_reencode]
def receiptReencodeExport (fork receipt : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let (type, r) ← decodeReceiptAt fork receipt
  runRlp "receipt has no encoding" (encodeReceipt type r)

/-- The logs Bloom filter of the logs of a receipt, decoded at the fork. -/
@[export eth_receipt_logs_bloom]
def receiptLogsBloomExport (fork receipt : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let (_, r) ← decodeReceiptAt fork receipt
  return ⟨(logsBloom r.logs).toArray⟩

/-- Check the RLP size of a block, decoded at the fork: from Fusaka, at most 8 MiB. -/
@[export eth_block_validate_size]
def validateSizeExport (fork block : ByteArray) : Result UInt8 := do
  let fork ← forkUpTo .glamsterdam fork
  let b : Block fork Item ← runRlp "block rejected" (Codec.decode block)
  (validateBlockSize b).map (fun () => 1) |>.mapError
    fun e => (e.code, s!"block invalid: {reprStr e}")

/-- Check a header at a fork against its parent at the parent's fork, at every fork. -/
@[export eth_block_validate_header]
def validateHeaderExport (parentFork fork parent header : ByteArray) : Result UInt8 := do
  let parentFork ← forkUpTo .glamsterdam parentFork
  let fork ← forkUpTo .glamsterdam fork
  let parent : Header parentFork ← runRlp "parent rejected" (Codec.decode parent)
  let header : Header fork ← runRlp "header rejected" (Codec.decode header)
  if hFork : parentFork ≤ fork then
    (validateHeader hFork parent header).map (fun () => 1) |>.mapError
      fun e => (e.code, s!"header invalid: {reprStr e}")
  else throw (0, "the parent's fork is after the fork")

/-- Check a header against its parent at two named forks, every check but the proof of work.

Test chains that run without proof of work check their headers this way. -/
@[export eth_block_check_header]
def checkHeaderExport (parentFork fork parent header : ByteArray) : Result UInt8 := do
  let parentFork ← forkUpTo .glamsterdam parentFork
  let fork ← forkUpTo .glamsterdam fork
  let parent : Header parentFork ← runRlp "parent rejected" (Codec.decode parent)
  let header : Header fork ← runRlp "header rejected" (Codec.decode header)
  if hFork : parentFork ≤ fork then
    (checkHeader hFork parent header).map (fun () => 1) |>.mapError
      fun e => (e.code, s!"header invalid: {reprStr e}")
  else throw (0, "the parent's fork is after the fork")

/-- The transaction that an item of a block holds at the fork.

A list is a legacy transaction, and a byte string is the bytes of a typed one. -/
def transactionOfItem (fork : Fork) (item : Item) : Result Transactions.Transaction := do
  let bytes ← match item with
    | .list _ => runRlp "transaction has no encoding" (encode item)
    | .bytes bytes =>
      if bytes.size > 0 ∧ bytes[0]! < 0xc0 then pure bytes
      else throw (0, "a typed transaction does not start with its type")
  (Transactions.decodeTransaction fork bytes).mapError
    fun e => (0, s!"transaction rejected: {reprStr e}")

/-- A root, or the code and the message of its trie error. -/
def runTrie (act : Except Trie.TrieError Hash32) : Result ByteArray :=
  match act with
  | .ok hash => return ⟨hash.toArray⟩
  | .error (.rlp e) => throw (e.code, s!"no root: {reprStr e}")
  | .error e => throw (0, s!"no root: {reprStr e}")

/-- The transactions root of the transactions of a block, decoded at the fork. -/
@[export eth_block_transactions_root]
def transactionsRootExport (fork block : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let b : Block fork Item ← runRlp "block rejected" (Codec.decode block)
  runTrie (transactionsRoot (← b.transactions.mapM (transactionOfItem fork)))

/-- The withdrawals root of the withdrawals of a block, decoded at a fork from Shapella. -/
@[export eth_block_withdrawals_root]
def withdrawalsRootExport (fork block : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let b : Block fork Item ← runRlp "block rejected" (Codec.decode block)
  if h : .shapella ≤ fork then runTrie (withdrawalsRoot (b.withdrawals h))
  else throw (0, "the fork is before Shapella")

/-- The data of the deposit requests of logs, given as the RLP list of the logs, in order. -/
@[export eth_block_deposit_requests]
def depositRequestsExport (logs : ByteArray) : Result ByteArray := do
  let logs : List Log ← runRlp "logs rejected" (Codec.decode logs)
  (depositRequests logs).mapError fun e => (e.code, s!"deposit log rejected: {reprStr e}")

/-- The requests hash of request lists, given as an RLP list of byte strings.

Each list is its type byte, then its data. -/
@[export eth_block_requests_hash]
def requestsHashExport (requests : ByteArray) : Result ByteArray := do
  let requests : List ByteArray ← runRlp "requests rejected" (Codec.decode requests)
  return requestsHash requests

end EthLib.Execution.Blocks.Exports
