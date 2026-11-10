module

public import EthLib.Engine.BuildPayload
public import EthLib.Engine.Exports.ForkchoiceUpdated

/-!
# `Exports.BuildPayload`

The C export of the payload build, on a chain that holds the parent.

The build and its checks are those of the specification, and the export only reads and writes.
-/

public section

namespace EthLib.Engine.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Execution.Blocks

/-- Build a payload on a chain, from attributes, the builder's choices and transactions.

The chain crosses as for `engine_newPayload` on a chain: configuration, state and recent blocks.

The attributes cross as the value of their JSON, with the method of the forkchoice update.

The transactions are in the form of an execution payload.

The result is the block in RLP form and the accounts after it, as the transition export gives.

Then come the requests of the block and its value in wei.

An error has the code of its Engine API error, of the transaction, or of the block.

Code 0 is for a chain that does not decode, and for an unknown method.

It is also for a parent number or time past 64 bits, and for a result without an encoding. -/
def buildPayloadOf
    (args : PyValue × ByteArray × List (String × ByteArray × List ByteArray) × String × PyValue ×
      Address × ByteArray × UInt64 × List ByteArray) :
    Result (ByteArray × ByteArray × List ByteArray × Nat) := do
  let (config, state, recent, method, attributes, feeRecipient, extraData, target, txs) := args
  let chain ← Execution.Blocks.Exports.chainOf config state recent
  let some version := forkchoiceUpdatedVersion method | throw (0, s!"no method {method}")
  -- The payload tree holds 64-bit numbers and times, so a parent past them is malformed input.
  if let some parent := chain.recent.getLast? then
    unless parent.header.number < UInt64.size ∧ parent.header.timestamp.toNat < UInt64.size do
      throw (0, "recent: the parent's number or time does not fit 64 bits")
  let decoded ← (payloadAttributesOfVersion version attributes.toJson).mapError
    fun e => (e.code, s!"engine error: {reprStr e}")
  let ⟨_, built⟩ ← (buildPayloadOnChain chain version decoded ⟨feeRecipient, extraData, target⟩
    txs).mapError fun
      | .attributes e => (e.code, s!"engine error: {reprStr e}")
      | .transaction e => (e.code, s!"{e.code}: {reasonMessage e}")
      | .block e => (e.code, Execution.Blocks.Exports.blockErrorMessage e)
  let encoded : Except BlockError (ByteArray × ByteArray) := do
    let block ← (Block.encode (← bodyItems built.block)).mapError .encoding
    let accounts ← (Serialization.Rlp.encode
      (Execution.Blocks.Exports.accountsItem built.state)).mapError .encoding
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
