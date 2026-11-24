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
- Its recent blocks, oldest first, are a list, each the fork name, the RLP header and RLP ommers.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Exports (Result PyValue UnreadArgument forkUpTo pyExport toResult)
open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Transactions.Exports (stateEntryItem)

/-- A recent block from its fork name, its header and its ommers, each header in RLP form.

Each ommer is at the fork of its own number on the chain `config`. -/
def recentOf (config : ChainConfig) (block : String × ByteArray × List ByteArray) :
    Result RecentBlock := do
  let (name, header, ommers) := block
  let fork ← forkUpTo .glamsterdam name.toUTF8
  return ⟨fork, ← toResult "recent header rejected" (Codec.decode header),
    ← toResult "recent ommers rejected" (ommers.mapM fun ommer => do
      Header.ofItemAtNumber (forkAtBlock config) (← decode ommer))⟩

/-- The chain that a configuration, a state and recent blocks give, as the exports take them.

The configuration is the typed value of its JSON, and the state takes the form of the root export.

A state or a recent block that does not decode has code 0, since the export reads it itself. -/
def chainOf (config : PyValue) (state : ByteArray)
    (recent : List (String × ByteArray × List ByteArray)) : Result BlockChain := do
  -- An input of the chain that does not decode has code 0, since the export reads it itself.
  let config ← ChainConfig.Exports.configOfJson config.toJson
  let pre ← toResult none
    ((State.Exports.ofInput state).mapError fun e => UnreadArgument.mk e.message)
  let recent ← toResult none
    ((recent.mapM (recentOf config)).mapError fun (_, m) => UnreadArgument.mk m)
  return ⟨config, pre, recent⟩

/-- The accounts of a state, as the list of entries of the state root export. -/
def accountsItem (state : Execution.State.State) : Item :=
  .list (state.accounts.toList.map fun (address, account) => stateEntryItem state address account)

/-- A block from the name of its fork and its RLP form, with its transactions decoded.

The block crosses the boundary in this form.

Each ommer is at the fork of its own number on the chain `config`.

A block or a transaction that does not decode has the code of its block error. -/
def blockOf (config : ChainConfig) (fork : String) (block : ByteArray) :
    Result ((fork : Fork) × Block fork Transactions.Transaction) := do
  -- The transition holds up to Glamsterdam, and fails from Hegotá as not yet specified.
  let fork ← forkUpTo .glamsterdam fork.toUTF8
  let raw : Block fork Item ← toResult none
    ((Block.decode (forkAtBlock config) block).mapError BlockError.encoding)
  let transactions ← raw.transactions.zipIdx.mapM fun (item, index) =>
    toResult none ((Transactions.decodeBodyTransaction fork item).mapError
      (BlockError.undecodableTransaction index))
  return ⟨fork, { raw with transactions }⟩

/-- Run the state transition of a block on a chain, and give the state after it.

Without the seal check, the proof of work is left out, as for test chains that run without one.

It returns the RLP list of two items: the state root, and the accounts of the state. -/
def stateTransitionOf
    (args : PyValue × ByteArray × List (String × ByteArray × List ByteArray) × String × ByteArray ×
      Bool) : Result ByteArray := do
  let (config, state, recent, fork, block, checkSeal) := args
  let chain ← chainOf config state recent
  let ⟨_, block⟩ ← blockOf chain.config fork block
  -- A block that fails a check comes back as the code and the message of its block error.
  let post ← toResult none (stateTransition chain block checkSeal)
  let root ← State.Exports.rootOf post
  toResult none ((encode (Item.list [Codec.toItem root, accountsItem post])).mapError
    fun e => UnreadArgument.mk s!"result: {reprStr e}")

/-- Run the state transition of a block on a chain, and give the state after it.

The arguments are the configuration of the chain, its state and its recent blocks.

Then come the fork and the block, and whether to check the seal of the proof of work.

It returns the RLP list of two items: the state root, and the accounts of the state. -/
@[export eth_state_transition]
def stateTransitionExport (args : PyValue) : Result PyValue :=
  pyExport stateTransitionOf args

/-- The fields of a genesis header that a chain chooses, in the order of the header.

They are the beneficiary, difficulty, gas limit, time, extra data, mix hash and nonce.

Then come the base fee, the excess blob gas and the slot number.

The fields cross as a tuple of typed Python values. -/
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
  let alloc ← toResult none
    ((State.Exports.ofInput state).mapError fun e => UnreadArgument.mk e.message)
  let block ← toResult none (genesis fork params alloc)
  -- The body is empty, so its transactions take the form of RLP items.
  toResult none (({ block with transactions := ([] : List Item) }.encode).mapError
    fun e => UnreadArgument.mk s!"result: {reprStr e}")

/-- The genesis block at a fork, in RLP form.

The arguments are the fork, the fields of the header that the chain chooses, and the state.

The fields are in the order of the header, from the beneficiary to the slot number. -/
@[export eth_genesis_block]
def genesisExport (args : PyValue) : Result PyValue :=
  pyExport genesisOf args

end EthLib.Execution.Blocks.Exports
