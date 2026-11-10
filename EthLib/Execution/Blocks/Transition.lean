module

public import EthLib.Execution.Blocks.DaoFork
public import EthLib.Execution.Blocks.Ommers
public import EthLib.Execution.Blocks.Rewards
public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Blocks.SystemCall

/-!
# `Blocks.Transition`

The state transition of a block: from the chain before it, the state after it, or why it fails.

The block is first checked alone and against its parent.

- From Fusaka, its RLP form must fit the most bytes of EIP-7934.
- Its header must pass the checks against the parent's header.
- Before Paris, at the DAO Fork and its next nine blocks, the extra data must be `dao-hard-fork`.
- Before Paris its ommers must be valid, and from Paris it has none.

Then its body runs on the state after the parent.

- Before Paris, at the first block of the DAO Fork, the ether of the DAO accounts moves first.
- From Dencun, the system calls at the start of the block come next.
- Then each transaction must be able to enter the block, and runs.
- From Shapella, the withdrawals follow.
- From Pectra, the requests follow: the deposits, then the withdrawal and consolidation requests.
- From Glamsterdam, the builder deposit and exit requests follow them.
- Before Paris, the beneficiary and the ommers get their rewards last.

From Glamsterdam, the body also builds its block access list, which must fit the gas limit.

The body records its calls for that list at every fork, and only from Glamsterdam builds it.

The system calls at the start run at position 0 of that list, transaction `i` at `i + 1`.

The withdrawals and the requests run at position `n + 1`, after the last of `n` transactions.

From Glamsterdam, the gas used of the block is the larger of its execution and state gas.

The receipts still add up the gas that each transaction used after its refund.

Last, the block must agree with what the body gave, in this order:

- the gas used, then the transactions root, the state root, the receipts root and the Bloom filter;
- from Shapella the withdrawals root, from Dencun the blob gas used, from Pectra the requests hash;
- from Glamsterdam the hash of the block access list.

Each failure has its own error.

An error that aborts the run, such as missing code, makes the block neither valid nor invalid.

Before Byzantium, the receipt of a transaction holds the state root after it.

From Dencun, the blob schedule of a block is the chain's own, as EIP-7892 lets a chain set it.

Sections 4.4.4 and 12 of the Yellow Paper, Shanghai version, define it: [`Paper.tex`][yp].

Section 11 of the Berlin version defines it before Paris: [`Paper.tex`][yp-berlin].

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

`hashes` are the hashes of the blocks before it, oldest first. -/
def blockEnvironment {fork : Fork} (config : ChainConfig) (hashes : List Hash32)
    (header : Header fork) : BlockEnvironment fork where
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
  blobSchedule :=
    Fees.BlobBaseFee.chainBlobSchedule config fork header.number header.timestamp.toNat

/-! ## The body -/

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

/-- The block state, with the writes of the body so far. -/
def BodyOutput.block {fork : Fork} (output : BodyOutput fork) : BlockState :=
  output.body.block

/-- Run the transaction `tx`, the `index`-th of its block, after the transactions before it.

It fails when the transaction cannot enter the block.

It runs at position `index + 1` of the block access list.

The block counts the gas of the transaction by its counts of gas.

Its receipt adds up the gas used after the refunds, as EIP-8037 keeps it.

Before Byzantium, its receipt holds the state root after it. -/
def applyTransaction {fork : Fork} (env : BlockEnvironment fork) (index : Nat)
    (before : BodyOutput fork) (tx : Transaction) : Except BlockError (BodyOutput fork) := do
  let included ← (checkInclusion env.chainId env before.gas
    (.ofBlock before.block) tx).mapError (.invalidTransaction index)
  let out ← (processTransaction env before.block included tx).mapError .aborted
  let body ← ((before.body.beginIndex (index + 1)).join out.state).mapError .state
  let gas := before.gas.add out.blockGas
  let cumulativeGasUsed := before.cumulativeGasUsed + out.gasUsed
  let outcome : Outcome fork ← if h : .byzantium ≤ fork then pure (.status h out.error.isNone)
    else .postState (Nat.lt_of_not_le h) <$>
      (stateRoot keccak256 body.block.applyChanges).mapError .trie
  return { body, gas, cumulativeGasUsed
           receipts :=
             before.receipts ++ [(tx.type, makeReceipt outcome cumulativeGasUsed out.logs.toList)]
           logs := before.logs ++ out.logs.toList }

/-- Run the transactions of a block in order, from the body so far. -/
def applyTransactions {fork : Fork} (env : BlockEnvironment fork) (body : BodyState)
    (transactions : List Transaction) : Except BlockError (BodyOutput fork) :=
  transactions.zipIdx.foldlM (fun before (tx, index) => applyTransaction env index before tx)
    ⟨body, .zero, 0, [], []⟩

/-- Run a writing step on a block state, as a transaction of its own. -/
def onBlock (block : BlockState)
    (step : TransactionState → Except State.StateError TransactionState) :
    Except BlockError BlockState := do
  let tx ← (step (.ofBlock block)).mapError .state
  return tx.incorporateTxIntoBlock.parent

/-- The block state at the start of a body at `fork`, after the DAO transfer if it runs there.

The transfer runs at the first block of the DAO Fork on the chain `config`, and only before Paris.

[EIP-779][eip-779] activates that fork at block 1,920,000 of Mainnet.

The gate at Paris is a choice of this specification, so that no later block can run the transfer.

The extra data rule of the fork has the same gate.

[eip-779]: https://eips.ethereum.org/EIPS/eip-779#specification -/
def daoTransfer (config : ChainConfig) (fork : Fork) (number : Nat) (start : BlockState) :
    Except BlockError BlockState :=
  if fork < .paris ∧ daoForkBlock config = some number then onBlock start (applyDaoFork fork)
  else pure start

/-- The requests of a block at `fork`, after its transactions and withdrawals.

The deposits come from the logs of the deposit contract at `depositContract`.

The other requests come from their contracts. -/
def blockRequests {fork : Fork} (depositContract : Address) (env : BlockEnvironment fork)
    (body : BodyState) (logs : List Log) : Except BlockError (BodyState × List ByteArray) := do
  if .pectra ≤ fork then
    let deposits ← (depositRequests depositContract logs).mapError .deposit
    let (body, requests) ← readRequests env body
    return (body, requestList DEPOSIT_REQUEST_TYPE deposits ++ requests)
  else return (body, [])

/-- What the whole body of a block gives: the output of its transactions, and its requests. -/
structure BlockOutput (fork : Fork) extends BodyOutput fork where
  /-- The requests of the block, each list with its type byte first. -/
  requests : List ByteArray
  /-- The hash of the block access list, from Glamsterdam, and none before. -/
  accessListHash : Option Hash32

/-- The hash of the block access list of a body at `fork`, or none before Glamsterdam.

The list must fit the gas limit `gasLimit` of the block, as EIP-7928 asks. -/
def accessListHashOf (fork : Fork) (body : BodyState) (gasLimit : Nat) :
    Except BlockError (Option Hash32) := do
  if fork ≥ .glamsterdam then
    let bal := body.builder.build
    (BlockAccessList.check bal gasLimit).mapError .blockAccessList
    some <$> (BlockAccessList.hash bal).mapError .encoding
  else return none

/-- Run the body of the block `block` on the block state `start`, at `fork`.

Before Paris, at the first block of the DAO Fork on the chain `config`, the DAO ether moves first.

The system calls at the start run at position 0 of the block access list.

The withdrawals and the requests run at position `n + 1`, after the last of `n` transactions.

From Glamsterdam, the body then builds its block access list, which must fit the gas limit. -/
def applyBody {fork : Fork} (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState) :
    Except BlockError (BlockOutput fork) := do
  let state ← daoTransfer config fork block.header.number start
  let body ← (startSystemCalls env block.header.parentHash (.init state)).mapError .aborted
  let output ← applyTransactions env body block.transactions
  let body := output.body.beginIndex (block.transactions.length + 1)
  let body ← if h : .shapella ≤ fork then do
      let tx ← (withdrawalState fork body.block (block.withdrawals h)).mapError .state
      (body.join tx).mapError .state
    else pure body
  let (body, requests) ← blockRequests config.depositContractAddress env body output.logs
  let ommers := block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)
  let state ← onBlock body.block fun tx =>
    payRewards fork tx block.header.coinbase block.header.number ommers
  let accessListHash ← accessListHashOf fork body block.header.gasLimit
  return { output with body := { body with block := state }, requests, accessListHash }

/-! ## The checks -/

/-- The item of a transaction in the body of a block.

A legacy transaction is its RLP list, and a typed transaction the byte string of its bytes. -/
def bodyItem : Transaction → Except Serialization.Rlp.RlpError Serialization.Rlp.Item
  | .legacy tx => .ok (Serialization.Rlp.Codec.toItem tx)
  | tx => .bytes <$> encodeTransaction tx

/-- The block with each transaction as its item in the body, for the RLP size of the block. -/
def bodyItems {fork : Fork} (block : Block fork Transaction) :
    Except BlockError (Block fork Serialization.Rlp.Item) := do
  let items ← (block.transactions.mapM bodyItem).mapError .encoding
  return { block with transactions := items }

/-- The checks of a block alone and against the recent chain, before its body runs.

The parent is the last recent block. With `checkSeal` off, the proof of work is left out. -/
def checkBlock {fork : Fork} (config : ChainConfig) (checkSeal : Bool)
    (recent : List RecentBlock) (block : Block fork Transaction) : Except BlockError Unit := do
  validateBlockSize (← bodyItems block)
  let some parent := recent.getLast? | throw .noParent
  if hFork : parent.fork ≤ fork then
    let schedule :=
      Fees.BlobBaseFee.chainBlobSchedule config fork block.header.number
        block.header.timestamp.toNat
    if checkSeal then validateHeader hFork parent.header block.header schedule
    else checkHeader hFork parent.header block.header schedule
  else throw .wrongParentHash
  unless daoExtraDataValid config block.header do throw .wrongDaoExtraData
  if fork < .paris then
    (validateOmmers config checkSeal recent block.header block.ommers).mapError .ommers
  else unless block.ommers.isEmpty do throw .ommersAfterParis

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
  let gasUsed := output.gas.gasUsed
  [(decide (gasUsed = header.gasUsed), .wrongGasUsed header.gasUsed gasUsed),
    (decide (roots.transactions = header.transactionsRoot), .wrongTransactionsRoot),
    (decide (roots.state = header.stateRoot), .wrongStateRoot),
    (decide (roots.receipts = header.receiptRoot), .wrongReceiptRoot),
    (decide (logsBloom output.logs = header.bloom), .wrongBloom)] ++
  (if h : .shapella ≤ fork then
    [(decide (roots.withdrawals = some (header.withdrawalsRoot h)), .wrongWithdrawalsRoot)]
  else []) ++
  (if h : .dencun ≤ fork then
    [(decide (output.gas.blob = (header.blobGasUsed h).toNat),
      .wrongBlobGasUsed (header.blobGasUsed h).toNat output.gas.blob)]
  else []) ++
  (if h : .pectra ≤ fork then
    [(decide (requestsHash output.requests = header.requestsHash h),
      .wrongRequestsHash)]
  else []) ++
  (if h : .glamsterdam ≤ fork then
    [(decide (output.accessListHash = some (header.blockAccessListHash h)),
      .wrongBlockAccessListHash)]
  else [])

/-- What the body of a block gives on its chain: its output, and the roots from the state after it.
-/
structure BodyResult (fork : Fork) where
  /-- What the body gave. -/
  output : BlockOutput fork
  /-- The roots of the transactions, of the state after the block, of the receipts and more. -/
  roots : OutputRoots

/-- The state after a block whose body gave `result`. -/
def BodyResult.post {fork : Fork} (result : BodyResult fork) : State :=
  result.output.block.applyChanges

/-- Run the body of `block` on the state of the chain `chain`, and compute the roots it gives.

The body runs in the environment of its header and of the recent hashes of the chain.

The body reads none of the header fields that it gives: roots, gas counts, logs Bloom, hashes.

So a builder can run it before it fills those fields. -/
def runBody (chain : BlockChain) {fork : Fork} (block : Block fork Transaction) :
    Except BlockError (BodyResult fork) := do
  let hashes ← recentHashes chain.recent
  let env := blockEnvironment chain.config hashes block.header
  let output ← applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩
  let roots ← outputRoots block.transactions block.withdrawals output output.block.applyChanges
  return ⟨output, roots⟩

/-! ## The transition -/

/-- Run the state transition of `block` at `fork` on the chain `chain`, and give the state after.

The fork of the block must be the active fork of the chain at its number and its time.

With `checkSeal` off, the proof of work is left out, as for chains that run without one.

From Hegotá it fails, since the rules of that fork are not yet specified here. -/
def stateTransition (chain : BlockChain) {fork : Fork} (block : Block fork Transaction)
    (checkSeal : Bool := true) : Except BlockError State := do
  if .hegota ≤ fork then throw (.aborted (.forkNotYetSpecified fork))
  unless chain.config.activeFork block.header.number block.header.timestamp.toNat = some fork do
    throw .wrongFork
  checkBlock chain.config checkSeal chain.recent block
  let result ← runBody chain block
  firstFailure (outputChecks block.header result.output result.roots)
  return result.post

end EthLib.Execution.Blocks
