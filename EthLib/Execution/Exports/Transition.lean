module

public import EthLib.Base.Exports.ChainConfig
public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Exports.Transactions

/-!
# `Exports.Transition`

The C-ABI export of the state transition of a block, callable from the Python C extension.

The chain crosses the boundary as three inputs.

- Its configuration is JSON, in the form of the chain configuration exports.
- Its state takes the form of the state root export.
- Its recent blocks, oldest first, are an RLP list, each the fork name, the header and the ommers.

The block crosses it as the name of its fork and its RLP form.

A block that fails a check comes back as the code and the message of its block error.

So does a block or a transaction of its body that does not decode.

An input of the chain that does not decode has code 0, since the export reads it itself.

The transition holds up to BPO5, and fails from Glamsterdam as not yet specified.

The genesis export takes the name of a fork, the fields that the chain chooses and the state.

The fields cross as an RLP list, and the block comes back in RLP form.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Exports (Result forkUpTo)
open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Transactions.Exports (abortMessage inclusionMessage message oneLine
  stateEntryItem)

/-- A recent block from its item: the fork name, the header and the list of its ommers.

Each ommer is at the fork of its own number on the chain `config`. -/
def recentOfItem (config : ChainConfig) (item : Item) : Result RecentBlock := do
  match ← runRlp "recent block rejected" (item.fields 3) with
  | [name, header, ommers] =>
    let name : ByteArray ← runRlp "recent fork rejected" (Codec.ofItem name)
    let fork ← forkUpTo .glamsterdam name
    let ommers : List Item ← runRlp "recent ommers rejected" (Codec.ofItem ommers)
    return ⟨fork, ← runRlp "recent header rejected" (Codec.ofItem header),
      ← runRlp "recent ommers rejected" (ommers.mapM (Header.ofItemAtNumber (forkAtBlock config)))⟩
  | _ => throw (0, "a recent block is not a list of three items")

/-- A message for a block error, phrased for a Python traceback. -/
def blockErrorMessage : BlockError → String
  | .invalidTransaction index e => s!"transaction {index} rejected: {inclusionMessage e}"
  | .aborted e => abortMessage e
  | .systemCallFailed address e => s!"system call to {oneLine address} failed: {oneLine e}"
  | e => s!"block invalid: {(oneLine e).replace "EthLib.Execution.Blocks.BlockError." ""}"

/-- Run the state transition of a block on a chain, and give the state after it.

With `checkSeal` 0, the proof of work is left out, as for test chains that run without one.

It returns a list of two items: the state root, and the accounts of the state. -/
@[export eth_state_transition]
def stateTransitionExport (config state recent fork block : ByteArray) (checkSeal : UInt8) :
    Result ByteArray := do
  let config ← ChainConfig.Exports.configOfJson
    (← ChainConfig.Exports.parseJson "config" config)
  -- The chain is an input that the export reads itself, so its errors have code 0.
  let pre ← (State.Exports.ofInput state).mapError fun e => (0, e.message)
  let recentItems : List Item ← (Codec.decode recent).mapError
    fun e => (0, s!"recent blocks rejected: {reprStr e}")
  let recent ← (recentItems.mapM (recentOfItem config)).mapError fun (_, m) => (0, m)
  let fork ← forkUpTo .glamsterdam fork
  let raw : Block fork Item ← (Block.decode (forkAtBlock config) block).mapError
    fun e => ((BlockError.encoding e).code, s!"block rejected: {reprStr e}")
  let transactions ← raw.transactions.zipIdx.mapM fun (item, index) =>
    (Transactions.decodeBodyTransaction fork item).mapError fun e =>
      ((BlockError.undecodableTransaction index e).code,
        s!"transaction {index} does not decode: {message e}")
  let chain : BlockChain := ⟨config, pre, recent⟩
  let post ← (stateTransition chain { raw with transactions } (checkSeal ≠ 0)).mapError
    fun e => (e.code, blockErrorMessage e)
  let root ← State.Exports.rootOf post
  let accounts := post.accounts.toList.map fun (address, account) =>
    stateEntryItem post address account
  (encode (Item.list [Codec.toItem root, .list accounts])).mapError
    fun e => (0, s!"result: {reprStr e}")

/-- The fields of a genesis header that a chain chooses, from an RLP list.

They follow the order of the header.

The beneficiary, difficulty, gas limit, time, extra data, mix hash and nonce come first.

The base fee, the excess blob gas and the slot number follow. -/
def genesisParamsOfItem (item : Item) : Except RlpError GenesisParams := do
  let n := 10
  let items ← item.fields n
  let (coinbase, items) ← Item.readField (α := Address) n items
  let (difficulty, items) ← Item.readField (α := Nat) n items
  let (gasLimit, items) ← Item.readField (α := Nat) n items
  let (timestamp, items) ← Item.readField (α := U256) n items
  let (extraData, items) ← Item.readField (α := ByteArray) n items
  let (prevRandao, items) ← Item.readField (α := Bytes32) n items
  let (nonce, items) ← Item.readField (α := Bytes8) n items
  let (baseFeePerGas, items) ← Item.readField (α := Nat) n items
  let (excessBlobGas, items) ← Item.readField (α := UInt64) n items
  let (slotNumber, _) ← Item.readField (α := UInt64) n items
  return { coinbase, difficulty, gasLimit, timestamp, extraData, prevRandao, nonce, baseFeePerGas,
           excessBlobGas, slotNumber }

/-- The genesis block at a fork, in RLP form.

The chain chooses the fields `params` and starts with the state `state`. -/
@[export eth_genesis_block]
def genesisExport (fork params state : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  -- The inputs are read by the export itself, so their errors have code 0.
  let params ← (Codec.decode params >>= genesisParamsOfItem).mapError
    fun e => (0, s!"genesis fields rejected: {reprStr e}")
  let alloc ← (State.Exports.ofInput state).mapError fun e => (0, e.message)
  let block ← (genesis fork params alloc).mapError fun e => (e.code, blockErrorMessage e)
  -- The body is empty, so its transactions take the form of RLP items.
  ({ block with transactions := ([] : List Item) }.encode).mapError
    fun e => (0, s!"result: {reprStr e}")

end EthLib.Execution.Blocks.Exports
