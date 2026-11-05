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

So does a blob schedule that is not four integers, or whose bounds fail.

A deposit log in another layout has a code from 301.

A block access list that breaks a rule of its form has a code from 401.

Every operation here holds up to Glamsterdam, and Hegotá is not yet specified.

Glamsterdam adds two header fields, by EIP-7928 and EIP-7843.

The encodings of the body and the receipt stay those of BPO2.

So do the checks of a header against its parent.

The receipts of a block hold up to BPO5, since Glamsterdam changes the gas that a block counts.
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

/-- The blob schedules that a chain sets itself, from their RLP form.

Each is a list of four integers: activation time, target, maximum and update fraction. -/
def blobSchedulesOf (bytes : ByteArray) : Result (List (Activation × BlobSchedule)) := do
  let entries : List (List Nat) ← runRlp "blob schedules rejected" (Codec.decode bytes)
  entries.mapM fun
    | [time, target, max, fraction] =>
      if h : target ≤ max ∧ 0 < max ∧ 0 < fraction then
        pure (.time time, ⟨target, max, fraction, h.1, h.2.1, h.2.2⟩)
      -- No error type covers a blob schedule of the binding, so its code is 0.
      else throw (0, "a blob schedule needs target ≤ max, 0 < max and 0 < update fraction")
    | _ => throw (0, "a blob schedule is not a list of four integers")

/-- The parent and the header of a header check, decoded at their forks, and a blob schedule.

The schedule is the header's, on a chain that sets the given blob schedules. -/
def headerCheckInputs (parentFork fork parent header schedules : ByteArray) :
    Result ((parentFork fork : Fork) × Header parentFork × Header fork ×
      Since .dencun fork BlobSchedule) := do
  let parentFork ← forkUpTo .glamsterdam parentFork
  let fork ← forkUpTo .glamsterdam fork
  let parent : Header parentFork ← runRlp "parent rejected" (Codec.decode parent)
  let header : Header fork ← runRlp "header rejected" (Codec.decode header)
  -- The chain's forks and chain ID play no part in the blob schedule of the header.
  let config : ChainConfig :=
    { chainId := 0, activations := [], blobSchedules := (← blobSchedulesOf schedules) }
  return ⟨parentFork, fork, parent, header,
    Fees.BlobBaseFee.chainBlobSchedule config fork header.number header.timestamp.toNat⟩

/-- Check a header at a fork against its parent at the parent's fork, at every fork.

The header's blob schedule is the last given one that it has reached, else that of its fork. -/
@[export eth_block_validate_header]
def validateHeaderExport (parentFork fork parent header schedules : ByteArray) :
    Result UInt8 := do
  let ⟨parentFork, fork, parent, header, schedule⟩ ←
    headerCheckInputs parentFork fork parent header schedules
  if hFork : parentFork ≤ fork then
    (validateHeader hFork parent header schedule).map (fun () => 1) |>.mapError
      fun e => (e.code, s!"header invalid: {reprStr e}")
  else throw (0, "the parent's fork is after the fork")

/-- Check a header against its parent at two named forks, every check but the proof of work.

Test chains that run without proof of work check their headers this way.

The header's blob schedule is the last given one that it has reached, else that of its fork. -/
@[export eth_block_check_header]
def checkHeaderExport (parentFork fork parent header schedules : ByteArray) : Result UInt8 := do
  let ⟨parentFork, fork, parent, header, schedule⟩ ←
    headerCheckInputs parentFork fork parent header schedules
  if hFork : parentFork ≤ fork then
    (checkHeader hFork parent header schedule).map (fun () => 1) |>.mapError
      fun e => (e.code, s!"header invalid: {reprStr e}")
  else throw (0, "the parent's fork is after the fork")

/-- Whether a header has the extra data that the DAO Fork asks of its first ten blocks.

The chain activates the DAO Fork at block `daoBlock`, which is 1,920,000 on mainnet.

A header outside those ten blocks passes. -/
@[export eth_block_dao_extra_data_valid]
def daoExtraDataValidExport (daoBlock : UInt64) (fork header : ByteArray) : Result UInt8 := do
  let fork ← forkUpTo .glamsterdam fork
  let header : Header fork ← runRlp "header rejected" (Codec.decode header)
  let config : ChainConfig := { chainId := 1, activations := [(.daoFork, .block daoBlock.toNat)] }
  pure (if daoExtraDataValid config header then 1 else 0)

/-- The transaction that an item of a block holds at the fork. -/
def transactionOfItem (fork : Fork) (item : Item) : Result Transactions.Transaction :=
  (Transactions.decodeBodyTransaction fork item).mapError
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

/-- The hash of a block access list in RLP form, after the decoder accepts it. -/
@[export eth_block_access_list_hash]
def blockAccessListHashExport (bal : ByteArray) : Result ByteArray := do
  let bal : BlockAccessList ← runRlp "block access list rejected" (Codec.decode bal)
  return ⟨(← runRlp "block access list has no encoding" (BlockAccessList.hash bal)).toArray⟩

/-- Check a block access list in RLP form alone, in a block with a gas limit. -/
@[export eth_block_access_list_check]
def blockAccessListCheckExport (bal : ByteArray) (gasLimit : UInt64) : Result UInt8 := do
  let bal : BlockAccessList ← runRlp "block access list rejected" (Codec.decode bal)
  (BlockAccessList.check bal gasLimit.toNat).map (fun () => 1) |>.mapError
    fun e => (e.code, s!"block access list invalid: {reprStr e}")

/-- One transaction of a block: its type, its outcome, the gas it used and its logs.

The input is the RLP list of the four, where the outcome has the form it has in a receipt. -/
def resultOfItem (fork : Fork) (item : Item) : Result (UInt8 × Outcome fork × Nat × List Log) := do
  match ← runRlp "result rejected" (item.fields 4) with
  | [type, outcome, gas, logs] =>
    let type : Nat ← runRlp "type rejected" (Codec.ofItem type)
    -- No error type covers this bound of the binding, so its code is 0.
    if 256 ≤ type then throw (0, "type is 256 or more")
    return (type.toUInt8, ← runRlp "outcome rejected" (Codec.ofItem outcome),
      ← runRlp "gas rejected" (Codec.ofItem gas), ← runRlp "logs rejected" (Codec.ofItem logs))
  | _ => throw (0, "a result is not a list of four items")

/-- The receipts of the transactions of a block, and their receipts root.

The input is the RLP list of the results of the transactions, in order.

It returns the RLP list of the root and of the list of the bytes of each receipt. -/
@[export eth_block_make_receipts]
def makeReceiptsExport (fork results : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .bpo5 fork
  let items ← runRlp "results rejected" ((← runRlp "results rejected" (decode results)).toItems)
  let results ← items.mapM (resultOfItem fork)
  let receipts := makeReceipts (results.map fun (_, rest) => rest)
  let typed := (results.map (·.1)).zip receipts
  let root ← runTrie (receiptsRoot typed)
  let bytes ← typed.mapM fun (type, r) => runRlp "receipt has no encoding" (encodeReceipt type r)
  runRlp "output has no encoding" (encode (.list [.bytes root, .list (bytes.map .bytes)]))

end EthLib.Execution.Blocks.Exports
