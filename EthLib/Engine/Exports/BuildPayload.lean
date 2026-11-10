module

public import EthLib.Engine.BuildPayload
public import EthLib.Engine.Exports.ForkchoiceUpdated

/-!
# `Exports.BuildPayload`

The C export of the payload build, on a chain that holds the parent.

The chain crosses the boundary as for `engine_newPayload` on a chain.

It is the configuration, the state in the form of the state root export, and the recent blocks.

The attributes cross as the value of their JSON, with the method of the forkchoice update.

They must pass the checks of that method against the last recent block, as the update runs them.

The builder's choices follow: the fee recipient, the extra data and the target gas limit.

The transactions are a list, each as an item of a block body in RLP form.

The result is the block in RLP form and the accounts after it, as the transition export gives.

Then come the requests of the block and its value in wei.

An error of the attributes has the code of its Engine API error, and a failed build its block error.

An input of the chain that does not decode has code 0, since the export reads it itself.

So do an empty chain, an unknown method and a parent number or time past 64 bits.

So does a result without an encoding.
-/

public section

namespace EthLib.Engine.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)
open EthLib.Execution.Blocks

/-- Build a payload on a chain, from attributes, the builder's choices and transactions.

The attributes are checked against the last recent block, as a forkchoice update checks them. -/
def buildPayloadOf
    (args : PyValue × ByteArray × List (String × ByteArray × List ByteArray) × String × PyValue ×
      Address × ByteArray × UInt64 × List ByteArray) :
    Result (ByteArray × ByteArray × List ByteArray × Nat) := do
  let (config, state, recent, method, attributes, feeRecipient, extraData, target, txs) := args
  let config ← configOfJson config.toJson
  -- The chain is an input that the export reads itself, so its errors have code 0.
  let pre ← (Execution.State.Exports.ofInput state).mapError fun e => (0, e.message)
  let recent ← (recent.mapM (Execution.Blocks.Exports.recentOf config)).mapError
    fun (_, m) => (0, m)
  let some parent := recent.getLast? | throw (0, "recent: no block")
  let some version := forkchoiceUpdatedVersion method | throw (0, s!"no method {method}")
  let engine {α : Type} (act : Except EngineError α) : Result α :=
    act.mapError fun e => (e.code, s!"engine error: {reprStr e}")
  let decoded ← engine (payloadAttributesOfVersion version attributes.toJson)
  -- The parent is the head that the update applies, so the checks read its number and time.
  unless parent.header.number < UInt64.size ∧ parent.header.timestamp.toNat < UInt64.size do
    throw (0, "recent: the parent's number or time does not fit 64 bits")
  let head : KnownPayload := ⟨parent.header.parentHash, true,
    UInt64.ofNat parent.header.number, UInt64.ofNat parent.header.timestamp.toNat⟩
  let ⟨fork, attributes⟩ ← engine (checkAttributes config version head decoded)
  let transactions ← txs.zipIdx.mapM fun (raw, index) => do
    let item ← Execution.Blocks.Exports.runRlp s!"transaction {index}"
      (Serialization.Rlp.decode raw)
    (Execution.Transactions.decodeBodyTransaction fork item).mapError fun e =>
      ((BlockError.undecodableTransaction index e).code,
        s!"transaction {index} does not decode: {Execution.Transactions.Exports.message e}")
  let choices : BuildChoices := ⟨feeRecipient, extraData, target⟩
  let built ← (buildPayload ⟨config, pre, recent⟩ attributes choices transactions).mapError
    fun e => (e.code, Execution.Blocks.Exports.blockErrorMessage e)
  let encoded : Except BlockError (ByteArray × ByteArray) := do
    let block ← bodyItems built.block
    let block ← (Block.encode block).mapError .encoding
    let accounts ← (Serialization.Rlp.encode (.list (built.state.accounts.toList.map
      fun (address, account) =>
        Execution.Transactions.Exports.stateEntryItem built.state address account))).mapError
      .encoding
    return (block, accounts)
  let (block, accounts) ← encoded.mapError fun e => (0, s!"result: {reprStr e}")
  return (block, accounts, built.requests, built.blockValue)

/-- Build a payload on a chain, from attributes, the builder's choices and transactions.

The arguments are the configuration, the state, the recent blocks, the method and the attributes.

Then come the fee recipient, the extra data, the target gas limit and the transactions.

It returns the block and the accounts after it in RLP form, the requests and the block value. -/
@[export eth_engine_build_payload]
def buildPayloadExport (args : PyValue) : Result PyValue :=
  pyExport buildPayloadOf args

end EthLib.Engine.Exports
