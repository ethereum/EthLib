module

public import EthLib.Execution.Blocks.DaoFork
public import EthLib.Execution.Blocks.Ommers
public import EthLib.Execution.Blocks.Rewards
public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Blocks.SystemCall

/-!
# `Blocks.Transition`

The state transition of a block: from the chain before it, the state after it, or why it fails.

Each failure has its own error.

An error that aborts the run, such as missing code, makes the block neither valid nor invalid.

Sections 4.4.4 and 12 of the Yellow Paper, Shanghai version, define it: [`Paper.tex`][yp].

Section 11 of the Berlin version defines it before Paris: [`Paper.tex`][yp-berlin].

No EIP or version of the Yellow Paper orders all the steps of a block together.

The step comments cite an EIP or the paper for each step that one writes out.

The EIPs that change it:

- [EIP-3675][eip-3675], no ommers and no reward from Paris
- [EIP-4895][eip-4895], the withdrawals
- [EIP-4844][eip-4844], the blob gas used
- [EIP-7685][eip-7685], the requests hash
- [EIP-7934][eip-7934], the most bytes of a block
- [EIP-7778][eip-7778], the gas of a block without the refunds, in Last Call
- [EIP-7928][eip-7928], the block access list, in Last Call
- [EIP-8037][eip-8037], the two counts of gas of a block and the gas of a receipt, in Last Call

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[yp-berlin]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#specification
[eip-4895]: https://eips.ethereum.org/EIPS/eip-4895#specification
[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#header-extension
[eip-7685]: https://eips.ethereum.org/EIPS/eip-7685#block-header
[eip-7934]: https://eips.ethereum.org/EIPS/eip-7934#specification
[eip-7778]: https://eips.ethereum.org/EIPS/eip-7778#specification
[eip-7928]: https://eips.ethereum.org/EIPS/eip-7928#state-transition-function
[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#block-level-gas-accounting
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState stateRoot)
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-! ## The chain -/

/-- The chain before a block: its configuration, its state and its recent blocks. -/
structure BlockChain where
  /-- The configuration of the chain. -/
  config : ChainConfig
  /-- The state after the last block. -/
  state : State
  /-- The recent blocks, oldest first, the last block last. -/
  recent : List RecentBlock

/-- The chain after a block that passes its transition.

It keeps the configuration and takes the state after the block.

It appends the block to the recent blocks, and keeps the last 255 of them.

The hashes of the blocks before the next block read only those 255, so no older block is needed.
-/
def BlockChain.addBlock (chain : BlockChain) {fork : Fork} (block : Block fork Transaction)
    (post : State) : BlockChain :=
  -- The block joins the recent blocks, last.
  let recent := chain.recent ++ [⟨fork, block.header, block.ommers⟩]
  -- Only the last 255 recent blocks stay.
  { chain with state := post, recent := recent.drop (recent.length - 255) }

/-- The hashes of the blocks before a block, oldest first, from the recent blocks of its chain.

They are the parent hash of each of the last 255 blocks, then the hash of the last block. -/
def recentHashes (recent : List RecentBlock) : Except BlockError (List Hash32) := do
  let last := recent.drop (recent.length - 255)
  match last.getLast? with
  | none => return []
  | some parent =>
    let hash ← parent.header.hash.mapError .encoding
    return last.map (·.header.parentHash) ++ [hash]

/-- The block environment of a block at `fork`, on the chain with configuration `config`.

`hashes` are the hashes of the blocks before it, oldest first.

A simulation can set the base fee per blob gas. -/
def blockEnvironment {fork : Fork} (config : ChainConfig) (hashes : List Hash32)
    (header : Header fork) (blobGasPrice : Option Nat := none) : BlockEnvironment fork where
  chainId := config.chainId
  coinbase := header.coinbase
  number := header.number
  gasLimit := header.gasLimit
  timestamp := header.timestamp
  difficulty := header.difficulty
  blockHashes := hashes
  baseFeePerGas := header.baseFeePerGas
  prevRandao := fun _ => header.prevRandao
  excessBlobGas := header.excessBlobGas
  parentBeaconBlockRoot := header.parentBeaconBlockRoot
  slotNumber := header.slotNumber
  -- From Dencun, the blob schedule of a block is the chain's own, as EIP-7892 lets a chain set it.
  blobSchedule :=
    Fees.BlobBaseFee.chainBlobSchedule config fork header.number header.timestamp.toNat
  blobGasPrice

/-! ## The body -/

/-- What a transaction of a body returns beside its receipt. -/
structure TransactionResult where
  /-- The output of its message: the data that it returned, or the data of its revert. -/
  output : ByteArray
  /-- The gas that it used before its refund, at least the call data floor from Pectra. -/
  gasBeforeRefund : Nat
  /-- The error that stopped its message, or none when the message succeeded. -/
  error : Option EvmError
  /-- The logs that a simulation with traced transfers reports for it, oldest first.

  Every run computes them, and no rule of the block reads them. -/
  simulatedLogs : List Log

/-- What the body of a block gives, at `fork`. -/
structure BodyOutput (fork : Fork) where
  /-- The block state and the builder of the block access list, after the body so far. -/
  body : BodyState
  /-- The gas counts of the transactions. -/
  gas : BlockGas
  /-- The gas that the transactions used, after their refunds, which the receipts add up. -/
  cumulativeGasUsed : Nat
  /-- The receipt of each transaction, with the type of the transaction. -/
  receipts : List (UInt8 × Receipt fork)
  /-- The logs of the transactions, oldest first. -/
  logs : List Log
  /-- The result of each transaction, oldest first, which no rule of the block reads. -/
  results : List TransactionResult

/-- The block state, with the writes of the body so far. -/
def BodyOutput.block {fork : Fork} (output : BodyOutput fork) : BlockState :=
  output.body.block

/-- What a simulation changes in the run of a body.

By default nothing changes, as in a real block.

The system calls of the block keep every precompile at its own address. -/
structure BodyOverrides where
  /-- The sender of the transaction at each index, given in place of its signature. -/
  senders : Nat → Option Address := fun _ => none
  /-- The address of the precompile that a call to each address runs, if any. -/
  precompiles : Address → Option Address := some
  /-- The rules of a transaction that the simulation lifts. -/
  lifted : LiftedRules := {}
  /-- Whether the block access list must fit the gas limit, as EIP-7928 asks. -/
  itemCap : Bool := true

/-- Run the transaction `tx`, the `index`-th of its block, after the transactions before it.

It fails when the transaction cannot enter the block. -/
def applyTransaction {fork : Fork} (env : BlockEnvironment fork) (index : Nat)
    (before : BodyOutput fork) (tx : Transaction) (overrides : BodyOverrides := {}) :
    Except BlockError (BodyOutput fork) := do
  -- The transaction must be able to enter the block.
  let included ← (checkInclusion env.chainId env before.gas
    (.ofBlock before.block) tx (overrides.senders index) overrides.lifted).mapError
    (.invalidTransaction index)
  let out ← (processTransaction env before.block included tx overrides.precompiles
    overrides.lifted).mapError .aborted
  -- The transaction runs at position `index + 1` of the block access list.
  let body ← ((before.body.beginIndex (index + 1)).join out.state).mapError .state
  -- The block counts the gas of the transaction by its counts of gas.
  let gas := before.gas.add out.blockGas
  -- The receipts add up the gas used after the refunds, as EIP-8037 keeps it.
  let cumulativeGasUsed := before.cumulativeGasUsed + out.gasUsed
  -- Before Byzantium, the receipt holds the state root after the transaction.
  let outcome : Outcome fork ← if h : .byzantium ≤ fork then pure (.status h out.error.isNone)
    else .postState (Nat.lt_of_not_le h) <$>
      (stateRoot keccak256 body.block.applyChanges).mapError .trie
  return { body, gas, cumulativeGasUsed
           receipts :=
             before.receipts ++ [(tx.type, makeReceipt outcome cumulativeGasUsed out.logs.toList)]
           logs := before.logs ++ out.logs.toList
           -- The result of the transaction is also recorded.
           results := before.results ++
             [⟨out.messageOutput, out.gasBeforeRefund, out.error, out.simulatedLogs.toList⟩] }

/-- Run the transactions of a block in order, from the body so far. -/
def applyTransactions {fork : Fork} (env : BlockEnvironment fork) (body : BodyState)
    (transactions : List Transaction) (overrides : BodyOverrides := {}) :
    Except BlockError (BodyOutput fork) :=
  transactions.zipIdx.foldlM
    (fun before (tx, index) => applyTransaction env index before tx overrides)
    ⟨body, .zero, 0, [], [], []⟩

/-- Run a writing step on a block state, as a transaction of its own. -/
def onBlock (block : BlockState)
    (step : TransactionState → Except State.StateError TransactionState) :
    Except BlockError BlockState := do
  let tx ← (step (.ofBlock block)).mapError .state
  return tx.incorporateTxIntoBlock.parent

/-- The block state at the start of a body at `fork`, after the DAO transfer if it runs there.

The transfer runs at the first block of the DAO Fork on the chain `config`, and only before Paris.

[EIP-779][eip-779] activates that fork at block 1,920,000 of Mainnet.

[eip-779]: https://eips.ethereum.org/EIPS/eip-779#specification -/
def daoTransfer (config : ChainConfig) (fork : Fork) (number : Nat) (start : BlockState) :
    Except BlockError BlockState :=
  -- EIP-779: at the beginning of block 1920000, all ether of the accounts in `L` moves.
  --
  -- Here it moves at the chain's DAO Fork block, before Paris, as the body starts.
  --
  -- The gate at Paris is a choice of this specification.
  --
  -- That gate keeps every later block from running the transfer.
  --
  -- The extra data rule of the fork has the same gate.
  if fork < .paris ∧ daoForkBlock config = some number then onBlock start (applyDaoFork fork)
  else pure start

/-- The requests of a block at `fork`, after its transactions and withdrawals.

The deposits come from the logs of the deposit contract at `depositContract`.

The other requests come from their contracts. -/
def blockRequests {fork : Fork} (depositContract : Address) (env : BlockEnvironment fork)
    (body : BodyState) (logs : List Log) : Except BlockError (BodyState × List ByteArray) := do
  if .pectra ≤ fork then
    -- The deposit requests, from the logs of the deposit contract.
    let deposits ← (depositRequests depositContract logs).mapError .deposit
    -- A checked system call to the withdrawal contract, then to the consolidation contract.
    --
    -- From Glamsterdam, then to the builder deposit and exit contracts.
    let (body, requests) ← readRequests env body
    -- EIP-7685: the requests are in ascending order of request type, so the deposits come first.
    return (body, requestList DEPOSIT_REQUEST_TYPE deposits ++ requests)
  else return (body, [])

/-- What the whole body of a block gives: the output of its transactions, and its requests. -/
structure BlockOutput (fork : Fork) extends BodyOutput fork where
  /-- The requests of the block, each list with its type byte first. -/
  requests : List ByteArray
  /-- The hash of the block access list, from Glamsterdam, and none before. -/
  accessListHash : Option Hash32

/-- The hash of the block access list of a body at `fork`, or none before Glamsterdam.

With `itemCap`, the list must fit the gas limit `gasLimit` of the block, as EIP-7928 asks.

Without it, as in a simulation without validation, the list is not checked.

A built list always passes the other checks of a list alone: its order and its uniqueness. -/
def accessListHashOf (fork : Fork) (body : BodyState) (gasLimit : Nat) (itemCap : Bool := true) :
    Except BlockError (Option Hash32) := do
  if fork ≥ .glamsterdam then
    -- The block access list, from the reads and writes of the body.
    let bal := body.builder.build
    -- The list must fit the gas limit of the block, unless the simulation lifts the cap.
    if itemCap then (BlockAccessList.check bal gasLimit).mapError .blockAccessList
    -- The hash of the list.
    --
    -- The body gives the hash, which the header check reads.
    some <$> (BlockAccessList.hash bal).mapError .encoding
  else return none

/-- Run the body of the block `block` on the block state `start`, at `fork`.

The body runs the system calls, the transactions, the withdrawals and the requests, in that order.

A simulation runs the transactions with its overrides. -/
def applyBody {fork : Fork} (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState) (overrides : BodyOverrides := {}) :
    Except BlockError (BlockOutput fork) := do
  -- Before Paris, at the first block of the DAO Fork of the chain, the DAO ether moves first.
  let state ← daoTransfer config fork block.header.number start
  -- EIP-4788, from Dencun, then EIP-2935, from Pectra: a system call each.
  --
  -- Each runs at the start of the block, before any transaction.
  --
  -- The system calls at the start run at position 0 of the block access list.
  let body ← (startSystemCalls env block.header.parentHash (.init state)).mapError .aborted
  -- Each transaction in order, with its index `i` in the block.
  --
  -- Transaction `i` runs at position `i + 1` of the block access list.
  let output ← applyTransactions env body block.transactions overrides
  -- EIP-7928: the operations after the `N` transactions use index `N + 1`.
  --
  -- The index is kept at every fork, and only a body from Glamsterdam builds the list.
  let body := output.body.beginIndex (block.transactions.length + 1)
  -- EIP-4895, from Shapella: the withdrawals apply after all the transactions.
  --
  -- The root of the withdrawals is computed with the other roots.
  let body ← if h : .shapella ≤ fork then do
      let tx ← (withdrawalState fork body.block (block.withdrawals h)).mapError .state
      (body.join tx).mapError .state
    else pure body
  -- The requests of EIP-7685, from Pectra; the builder requests join at Glamsterdam.
  let (body, requests) ← blockRequests config.depositContractAddress env body output.logs
  -- Before Paris, the Berlin paper's stage that applies the rewards, after the transactions.
  --
  -- The beneficiary and the ommers get their rewards here.
  let ommers := block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)
  let state ← onBlock body.block fun tx =>
    payRewards fork tx block.header.coinbase block.header.number ommers
  -- From Glamsterdam: the block access list, its gas limit check, then its hash.
  let accessListHash ← accessListHashOf fork body block.header.gasLimit overrides.itemCap
  return { output with body := { body with block := state }, requests, accessListHash }

/-! ## The checks -/

/-- The block with each transaction as its item in the body, for the RLP size of the block. -/
def bodyItems {fork : Fork} (block : Block fork Transaction) :
    Except BlockError (Block fork Serialization.Rlp.Item) := do
  let items ← (block.transactions.mapM bodyItem).mapError .encoding
  return { block with transactions := items }

/-- The checks of a block alone and against the recent chain, before its body runs.

The parent is the last recent block. With `checkSeal` off, the proof of work is left out. -/
def checkBlock {fork : Fork} (config : ChainConfig) (checkSeal : Bool)
    (recent : List RecentBlock) (block : Block fork Transaction) : Except BlockError Unit := do
  -- EIP-7934, from Fusaka: the RLP encoding of the block has at most `MAX_RLP_BLOCK_SIZE` bytes.
  validateBlockSize (← bodyItems block)
  -- The parent is the last recent block.
  --
  -- With no recent block there is no parent, and the block fails with its own error.
  let some parent := recent.getLast? | throw .noParent
  -- The checks of the header against its parent.
  --
  -- A parent at a later fork than the block fails as a wrong parent hash.
  if hFork : parent.fork ≤ fork then
    let schedule :=
      Fees.BlobBaseFee.chainBlobSchedule config fork block.header.number
        block.header.timestamp.toNat
    if checkSeal then validateHeader hFork parent.header block.header schedule
    else checkHeader hFork parent.header block.header schedule
  else throw (.wrongParentHash parent.header.hash.toOption block.header.parentHash)
  -- EIP-779: the blocks 1920000 to 1920009 must have `dao-hard-fork` as their extra data.
  --
  -- Here at the chain's DAO Fork block and its next nine, before Paris, after the seal check.
  unless daoExtraDataValid config block.header do
    throw (.wrongDaoExtraData block.header.extraData)
  -- Before Paris, the Berlin paper's stage that validates the ommers.
  if fork < .paris then
    (validateOmmers config checkSeal recent block.header block.ommers).mapError .ommers
  -- From Paris, a block has no ommer, by EIP-3675.
  else unless block.ommers.isEmpty do throw (.ommersAfterParis block.ommers.length)

/-- The roots of a block that its body gives, from the post-state `post`.

They are the transactions root, the state root and the receipts root.

From Shapella, the withdrawals root joins them. -/
structure OutputRoots where
  /-- The root of the transactions. -/
  transactions : Hash32
  /-- The root of the state after the block. -/
  state : Hash32
  /-- The root of the receipts. -/
  receipts : Hash32
  /-- The root of the withdrawals, from Shapella. -/
  withdrawals : Option Hash32

/-- The withdrawals root of a block at `fork`, from Shapella, or none before. -/
def withdrawalsRootOf {fork : Fork} (withdrawals : Since .shapella fork (List Withdrawal)) :
    Except BlockError (Option Hash32) :=
  if h : .shapella ≤ fork then some <$> (withdrawalsRoot (withdrawals h)).mapError .trie
  else .ok none

/-- Compute the roots of a block from its transactions, its output and the state after it. -/
def outputRoots {fork : Fork} (transactions : List Transaction)
    (withdrawals : Since .shapella fork (List Withdrawal)) (output : BlockOutput fork)
    (post : State) : Except BlockError OutputRoots := do
  let txRoot ← (transactionsRoot transactions).mapError .trie
  let postRoot ← (stateRoot keccak256 post).mapError .trie
  let receiptRoot ← (receiptsRoot output.receipts).mapError .trie
  let withdrawalRoot ← withdrawalsRootOf withdrawals
  return ⟨txRoot, postRoot, receiptRoot, withdrawalRoot⟩

/-- The checks of a block against what its body gave, in order, each with its error. -/
def outputChecks {fork : Fork} (header : Header fork) (output : BlockOutput fork)
    (roots : OutputRoots) : List (Bool × BlockError) :=
  -- EIP-8037, from Glamsterdam: the gas used is the larger of the execution gas and the state gas.
  --
  -- Before, it is the gas that the transactions used.
  --
  -- The receipts still add up the gas that each transaction used after its refund.
  let gasUsed := output.gas.gasUsed
  -- The gas used equals that of the header.
  [(decide (gasUsed = header.gasUsed), .wrongGasUsed header.gasUsed gasUsed),
    -- The transactions root equals that of the header.
    (decide (roots.transactions = header.transactionsRoot),
      .wrongTransactionsRoot header.transactionsRoot roots.transactions),
    -- The state root equals that of the header.
    (decide (roots.state = header.stateRoot), .wrongStateRoot header.stateRoot roots.state),
    -- The receipts root equals that of the header.
    (decide (roots.receipts = header.receiptRoot),
      .wrongReceiptRoot header.receiptRoot roots.receipts),
    -- The logs Bloom equals that of the header.
    (decide (logsBloom output.logs = header.bloom),
      .wrongBloom header.bloom (logsBloom output.logs))] ++
  -- From Shapella, the withdrawals root equals that of the header.
  (if h : .shapella ≤ fork then
    [(decide (roots.withdrawals = some (header.withdrawalsRoot h)),
      .wrongWithdrawalsRoot (header.withdrawalsRoot h) roots.withdrawals)]
  else []) ++
  -- From Dencun, the blob gas used equals that of the header.
  (if h : .dencun ≤ fork then
    [(decide (output.gas.blob = (header.blobGasUsed h).toNat),
      .wrongBlobGasUsed (header.blobGasUsed h).toNat output.gas.blob)]
  else []) ++
  -- From Pectra, the requests hash equals that of the header.
  (if h : .pectra ≤ fork then
    [(decide (requestsHash output.requests = header.requestsHash h),
      .wrongRequestsHash (header.requestsHash h) (requestsHash output.requests))]
  else []) ++
  -- From Glamsterdam, the hash of the block access list equals that of the header.
  (if h : .glamsterdam ≤ fork then
    [(decide (output.accessListHash = some (header.blockAccessListHash h)),
      .wrongBlockAccessListHash (header.blockAccessListHash h) output.accessListHash)]
  else [])

/-- What the body of a block gives on its chain: its output, and the roots of the header. -/
structure BodyResult (fork : Fork) where
  /-- What the body gave. -/
  output : BlockOutput fork
  /-- The roots of the transactions, the state after the block, the receipts and the withdrawals. -/
  roots : OutputRoots

/-- The state after a block whose body gave `result`. -/
def BodyResult.post {fork : Fork} (result : BodyResult fork) : State :=
  result.output.block.applyChanges

/-- Run the body of `block` on the state of the chain `chain`, and compute the roots it gives.

The body reads none of the header fields that it gives: the roots, the gas counts, the logs Bloom.

Nor does it read the requests hash and the block access list hash.

So a builder can run it before it fills those fields. -/
def runBody (chain : BlockChain) {fork : Fork} (block : Block fork Transaction)
    (overrides : BodyOverrides := {}) (blobGasPrice : Option Nat := none) :
    Except BlockError (BodyResult fork) := do
  -- The body runs in the environment of its header and of the recent hashes of the chain.
  let hashes ← recentHashes chain.recent
  -- A simulation sets its base fee per blob gas here.
  let env := blockEnvironment chain.config hashes block.header blobGasPrice
  -- A simulation runs the body with its overrides.
  let output ← applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩ overrides
  let roots ← outputRoots block.transactions block.withdrawals output output.block.applyChanges
  return ⟨output, roots⟩

/-- A header with the fields that the body of its block gives, as after a build or a simulation. -/
def fillHeader {fork : Fork} (header : Header fork) (output : BlockOutput fork)
    (roots : OutputRoots) : Header fork :=
  { header with
    stateRoot := roots.state
    transactionsRoot := roots.transactions
    receiptRoot := roots.receipts
    bloom := logsBloom output.logs
    gasUsed := output.gas.gasUsed
    withdrawalsRoot := fun _ => roots.withdrawals.getD 0
    blobGasUsed := fun _ => output.gas.blob.toUInt64
    requestsHash := fun _ => requestsHash output.requests
    blockAccessListHash := fun _ => output.accessListHash.getD 0 }

/-! ## The transition -/

/-- Run the state transition of `block` at `fork` on the chain `chain`, and give the state after.

The fork of the block must be the active fork of the chain at its number and its time.

With `checkSeal` off, the proof of work is left out, as for chains that run without one.

From Hegotá it fails, since the rules of that fork are not yet specified here. -/
def stateTransition (chain : BlockChain) {fork : Fork} (block : Block fork Transaction)
    (checkSeal : Bool := true) : Except BlockError State := do
  -- No EIP fixes the rules of Hegotá yet.
  if .hegota ≤ fork then throw (.aborted (.forkNotYetSpecified fork))
  -- The fork of the block is the one that the chain activates at it.
  let active := chain.config.activeFork block.header.number block.header.timestamp.toNat
  unless active = some fork do throw (.wrongFork active fork)
  -- The block is first checked alone and against its parent.
  --
  -- The checks of the block: the size, the header and the ommers.
  checkBlock chain.config checkSeal chain.recent block
  -- Then its body runs on the state after the parent, and gives the roots.
  let result ← runBody chain block
  -- Last, the block must agree with what the body gave.
  --
  -- The checks of the header against the output, in order.
  firstFailure (outputChecks block.header result.output result.roots)
  -- The changes of the block apply to the state of the chain.
  return result.post

end EthLib.Execution.Blocks
