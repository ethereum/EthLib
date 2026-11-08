module

public import EthLib.Base.Exports.ChainConfig
public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Exports.Transactions

/-!
# `Exports.Transition`

The C-ABI export of the state transition of a block, callable from the Python C extension.

The chain crosses the boundary as three inputs.

- Its configuration is the typed value of its JSON, in the form of the chain configuration exports.
- Its state takes the form of the state root export.
- Its recent blocks, oldest first, are an RLP list, each the fork name, the header and the ommers.

The block crosses it as the name of its fork and its RLP form.

A block that fails a check comes back as the code and the message of its block error.

So does a block or a transaction of its body that does not decode.

An input of the chain that does not decode has code 0, since the export reads it itself.

The transition holds up to Glamsterdam, and fails from Hegotá as not yet specified.

The genesis export takes the name of a fork, the fields that the chain chooses and the state.

The fields cross as a tuple of typed Python values, and the block comes back in RLP form.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Exports (Result PyValue forkUpTo pyExport)
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

Without the seal check, the proof of work is left out, as for test chains that run without one.

It returns the RLP list of two items: the state root, and the accounts of the state. -/
def stateTransitionOf (args : PyValue × ByteArray × ByteArray × String × ByteArray × Bool) :
    Result ByteArray := do
  let (config, state, recent, fork, block, checkSeal) := args
  let config ← ChainConfig.Exports.configOfJson config.toJson
  -- The chain is an input that the export reads itself, so its errors have code 0.
  let pre ← (State.Exports.ofInput state).mapError fun e => (0, e.message)
  let recentItems : List Item ← (Codec.decode recent).mapError
    fun e => (0, s!"recent blocks rejected: {reprStr e}")
  let recent ← (recentItems.mapM (recentOfItem config)).mapError fun (_, m) => (0, m)
  let fork ← forkUpTo .glamsterdam fork.toUTF8
  let raw : Block fork Item ← (Block.decode (forkAtBlock config) block).mapError
    fun e => ((BlockError.encoding e).code, s!"block rejected: {reprStr e}")
  let transactions ← raw.transactions.zipIdx.mapM fun (item, index) =>
    (Transactions.decodeBodyTransaction fork item).mapError fun e =>
      ((BlockError.undecodableTransaction index e).code,
        s!"transaction {index} does not decode: {message e}")
  let chain : BlockChain := ⟨config, pre, recent⟩
  let post ← (stateTransition chain { raw with transactions } checkSeal).mapError
    fun e => (e.code, blockErrorMessage e)
  let root ← State.Exports.rootOf post
  let accounts := post.accounts.toList.map fun (address, account) =>
    stateEntryItem post address account
  (encode (Item.list [Codec.toItem root, .list accounts])).mapError
    fun e => (0, s!"result: {reprStr e}")

/-- Run the state transition of a block on a chain, and give the state after it.

The arguments are the configuration of the chain, its state and its recent blocks.

Then come the fork and the block, and whether to check the seal of the proof of work.

It returns the RLP list of two items: the state root, and the accounts of the state. -/
@[export eth_state_transition]
def stateTransitionExport (args : PyValue) : Result PyValue :=
  pyExport stateTransitionOf args

/-- The fields of a genesis header that a chain chooses, in the order of the header.

They are the beneficiary, difficulty, gas limit, time, extra data, mix hash and nonce.

Then come the base fee, the excess blob gas and the slot number. -/
abbrev GenesisFields :=
  Address × Nat × Nat × U256 × ByteArray × Bytes32 × Bytes8 × Nat × UInt64 × UInt64

/-- The genesis block at a fork, in RLP form, with the fields that the chain chooses. -/
def genesisOf (args : String × GenesisFields × ByteArray) : Result ByteArray := do
  let (fork, fields, state) := args
  let (coinbase, difficulty, gasLimit, timestamp, extraData, prevRandao, nonce, baseFeePerGas,
    excessBlobGas, slotNumber) := fields
  let params : GenesisParams := {
    coinbase := coinbase, difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
    extraData := extraData, prevRandao := prevRandao, nonce := nonce,
    baseFeePerGas := baseFeePerGas, excessBlobGas := excessBlobGas, slotNumber := slotNumber }
  let fork ← forkUpTo .glamsterdam fork.toUTF8
  -- The state is read by the export itself, so its errors have code 0.
  let alloc ← (State.Exports.ofInput state).mapError fun e => (0, e.message)
  let block ← (genesis fork params alloc).mapError fun e => (e.code, blockErrorMessage e)
  -- The body is empty, so its transactions take the form of RLP items.
  ({ block with transactions := ([] : List Item) }.encode).mapError
    fun e => (0, s!"result: {reprStr e}")

/-- The genesis block at a fork, in RLP form.

The arguments are the fork, the fields of the header that the chain chooses, and the state.

The fields are in the order of the header, from the beneficiary to the slot number. -/
@[export eth_genesis_block]
def genesisExport (args : PyValue) : Result PyValue :=
  pyExport genesisOf args

end EthLib.Execution.Blocks.Exports
