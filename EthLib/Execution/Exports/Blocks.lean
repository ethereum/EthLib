module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Execution.Blocks
public import EthLib.Execution.Transactions.Envelope
public import EthLib.Serialization.Exports.Rlp

/-!
# `Exports.Blocks`

C-ABI exports for headers and blocks, callable from the Python C extension.

A fork crosses the boundary as the name of its case in Lean, such as `shapella`.

A header, a block or a receipt crosses it as its bytes.

Each operation decodes at the fork first, the ommers of a block too.

A rejected input comes back as the code and the message of its RLP error.

A receipt error has a code from 101, and a failed header check a code from 201.

An unknown fork name, or forks out of order, has code 0, since no error type covers it.

So does a transaction of a block that does not decode, and a trie with an empty value.

So does a blob schedule whose bounds fail, or an argument that Lean cannot read.

The header checks take and return typed Python values, and a blob schedule is four integers.

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

open EthLib.Exports (Result PyValue forkUpTo pyExport)

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
  let b : Block fork Item ← runRlp "block rejected" (Block.decode (fun _ => fork) block)
  runRlp "block has no encoding" b.encode

/-- The forks of a chain by block number, from their RLP form: a list of `[name, first block]`.

The first fork starts at block 0, so each block has a fork.

The chain ID, the deposit contract and the blob schedules play no part. -/
def chainOfForks (forks : ByteArray) : Result ChainConfig := do
  let entries : List (List Item) ← runRlp "forks rejected" (Codec.decode forks)
  let activations ← entries.mapM fun
    | [.bytes name, first] => do
      let fork ← forkUpTo .glamsterdam name
      let first : Nat ← runRlp "fork block rejected" (Codec.ofItem first)
      pure (fork, Activation.block first)
    | _ => throw (0, "a fork is not a list of a name and a block number")
  -- The chain ID and the deposit contract play no part in the order of the forks.
  let config : ChainConfig :=
    { chainId := 0, depositContractAddress := Vector.replicate 20 0, activations := activations }
  if !decide config.Ordered then throw (0, "the forks are not in the order of the timeline")
  match activations with
  | (_, .block 0) :: _ => pure config
  | _ => throw (0, "the first fork does not start at block 0")

/-- The fork of a block number, on a chain whose first fork starts at block 0. -/
def forkAtBlock (config : ChainConfig) (number : Nat) : Fork :=
  (config.activeFork number 0).getD .frontier

/-- A block in its RLP item, with each header at the fork of its own number on the chain. -/
def blockOnChain (config : ChainConfig) (item : Item) :
    Result ((fork : Fork) × Block fork Item) := do
  let number ← runRlp "block rejected" do
    let header :: _ ← item.toItems | .error (.wrongFieldCount 3 0)
    Header.numberOfItem header
  pure ⟨_, ← runRlp "block rejected"
    (Block.ofItem (fork := forkAtBlock config number) (forkAtBlock config) item)⟩

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
  let b : Block fork Item ← runRlp "block rejected" (Block.decode (fun _ => fork) block)
  (validateBlockSize b).map (fun () => 1) |>.mapError
    fun e => (e.code, s!"block invalid: {reprStr e}")

/-- The blob schedules that a chain sets itself.

Each is four integers: activation time, target, maximum and update fraction. -/
def blobSchedulesOf (entries : List (Nat × Nat × Nat × Nat)) :
    Result (List (Activation × BlobSchedule)) :=
  entries.mapM fun (time, target, max, fraction) =>
    if h : target ≤ max ∧ 0 < max ∧ 0 < fraction then
      pure (.time time, ⟨target, max, fraction, h.1, h.2.1, h.2.2⟩)
    -- No error type covers a blob schedule of the binding, so its code is 0.
    else throw (0, "a blob schedule needs target ≤ max, 0 < max and 0 < update fraction")

/-- The arguments of a header check.

They are the forks of the parent and of the header, then the parent and the header in RLP.

Last come the blob schedules of the chain. -/
abbrev HeaderCheckArgs := String × String × ByteArray × ByteArray × List (Nat × Nat × Nat × Nat)

/-- The parent and the header of a header check, decoded at their forks, and a blob schedule.

The schedule is the header's, on a chain that sets the given blob schedules. -/
def headerCheckInputs (args : HeaderCheckArgs) :
    Result ((parentFork fork : Fork) × Header parentFork × Header fork ×
      Since .dencun fork BlobSchedule) := do
  let (parentFork, fork, parent, header, schedules) := args
  let parentFork ← forkUpTo .glamsterdam parentFork.toUTF8
  let fork ← forkUpTo .glamsterdam fork.toUTF8
  let parent : Header parentFork ← runRlp "parent rejected" (Codec.decode parent)
  let header : Header fork ← runRlp "header rejected" (Codec.decode header)
  -- The chain's forks, chain ID and deposit contract play no part in the blob schedule.
  let schedules ← blobSchedulesOf schedules
  let config : ChainConfig :=
    { chainId := 0, depositContractAddress := Vector.replicate 20 0, activations := [],
      blobSchedules := schedules }
  return ⟨parentFork, fork, parent, header,
    Fees.BlobBaseFee.chainBlobSchedule config fork header.number header.timestamp.toNat⟩

/-- Check a header at a fork against its parent at the parent's fork, at every fork.

The header's blob schedule is the last given one that it has reached, else that of its fork. -/
def validateHeaderOf (args : HeaderCheckArgs) : Result Unit := do
  let ⟨parentFork, fork, parent, header, schedule⟩ ← headerCheckInputs args
  if hFork : parentFork ≤ fork then
    (validateHeader hFork parent header schedule).mapError
      fun e => (e.code, s!"header invalid: {reprStr e}")
  else throw (0, "the parent's fork is after the fork")

/-- Check a header at a fork against its parent at the parent's fork, at every fork.

The arguments are the forks of the parent and of the header, the parent and the header in RLP.

Last come the blob schedules that the chain sets, each four integers.

The header's blob schedule is the last given one that it has reached, else that of its fork. -/
@[export eth_block_validate_header]
def validateHeaderExport (args : PyValue) : Result PyValue :=
  pyExport validateHeaderOf args

/-- Check a header against its parent at two named forks, every check but the proof of work.

The header's blob schedule is the last given one that it has reached, else that of its fork. -/
def checkHeaderOf (args : HeaderCheckArgs) : Result Unit := do
  let ⟨parentFork, fork, parent, header, schedule⟩ ← headerCheckInputs args
  if hFork : parentFork ≤ fork then
    (checkHeader hFork parent header schedule).mapError
      fun e => (e.code, s!"header invalid: {reprStr e}")
  else throw (0, "the parent's fork is after the fork")

/-- Check a header against its parent at two named forks, every check but the proof of work.

Test chains that run without proof of work check their headers this way.

The arguments are those of the full check of a header.

The header's blob schedule is the last given one that it has reached, else that of its fork. -/
@[export eth_block_check_header]
def checkHeaderExport (args : PyValue) : Result PyValue :=
  pyExport checkHeaderOf args

/-- Whether a header has the extra data that the DAO Fork asks of its first ten blocks.

The chain activates the DAO Fork at block `daoBlock`, which is 1,920,000 on mainnet.

A header outside those ten blocks passes. -/
@[export eth_block_dao_extra_data_valid]
def daoExtraDataValidExport (daoBlock : UInt64) (fork header : ByteArray) : Result UInt8 := do
  let fork ← forkUpTo .glamsterdam fork
  let header : Header fork ← runRlp "header rejected" (Codec.decode header)
  let config : ChainConfig :=
    { chainId := 1, depositContractAddress := Vector.replicate 20 0,
      activations := [(.daoFork, .block daoBlock.toNat)] }
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
  let b : Block fork Item ← runRlp "block rejected" (Block.decode (fun _ => fork) block)
  runTrie (transactionsRoot (← b.transactions.mapM (transactionOfItem fork)))

/-- The withdrawals root of the withdrawals of a block, decoded at a fork from Shapella. -/
@[export eth_block_withdrawals_root]
def withdrawalsRootExport (fork block : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let b : Block fork Item ← runRlp "block rejected" (Block.decode (fun _ => fork) block)
  if h : .shapella ≤ fork then runTrie (withdrawalsRoot (b.withdrawals h))
  else throw (0, "the fork is before Shapella")

/-- The data of the deposit requests of logs, given as the RLP list of the logs, in order.

The first argument is the 20-byte address of the deposit contract of the chain. -/
@[export eth_block_deposit_requests]
def depositRequestsExport (depositContract logs : ByteArray) : Result ByteArray := do
  let address : Address ← if h : depositContract.data.size = 20 then pure ⟨depositContract.data, h⟩
    else throw (0, "the deposit contract address is not 20 bytes")
  let logs : List Log ← runRlp "logs rejected" (Codec.decode logs)
  (depositRequests address logs).mapError fun e => (e.code, s!"deposit log rejected: {reprStr e}")

/-- The requests hash of request lists, given as an RLP list of byte strings.

Each list is its type byte, then its data. -/
@[export eth_block_requests_hash]
def requestsHashExport (requests : ByteArray) : Result ByteArray := do
  let requests : List ByteArray ← runRlp "requests rejected" (Codec.decode requests)
  return ⟨(requestsHash requests).toArray⟩

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
