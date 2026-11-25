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

open EthLib.Exports (ExportError Result PyValue UnreadArgument pyExport rejectArgument toResult)
open EthLib.Base
open EthLib.Execution.Blocks

/-- A build that fails reaches Python with the code of the error it holds.

An error of the attributes reads as an Engine API error, and a transaction as its payload error.

An error of the block keeps the message of the block exports. -/
instance : ExportError BuildError where
  code := BuildError.code
  message
    | .attributes e => s!"engine error: {ExportError.message e}"
    | .transaction e => s!"{e.code}: {reasonMessage e}"
    | .block e => ExportError.message e

/-- Build a payload on a chain, from attributes, the builder's choices and transactions.

The result is the block in RLP form and the accounts after it, as the transition export gives.

Then come the requests of the block and its value in wei.

An error has the code of its Engine API error, of the transaction, or of the block. -/
def buildPayloadOf
    (args : PyValue × ByteArray × List (String × ByteArray × List ByteArray) × String × PyValue ×
      Address × ByteArray × UInt64 × List ByteArray) :
    Result (ByteArray × ByteArray × List ByteArray × Nat) := do
  let (config, state, recent, method, attributes, feeRecipient, extraData, target, txs) := args
  -- The chain crosses as for `engine_newPayload` on a chain.
  --
  -- It is the configuration, the state and the recent blocks.
  --
  -- A chain that does not decode has code 0.
  let chain ← Execution.Blocks.Exports.chainOf config state recent
  -- An unknown method has code 0.
  let some version := forkchoiceUpdatedVersion method | rejectArgument none s!"no method {method}"
  -- The attributes cross as the value of their JSON, with the method of the forkchoice update.
  let decoded ← toResult "engine error" (payloadAttributesOfVersion version attributes.toJson)
  -- The transactions are in the form of an execution payload.
  let ⟨_, built⟩ ← toResult none
    (buildPayloadOnChain chain version decoded ⟨feeRecipient, extraData, target⟩ txs)
  -- An account whose code the state after the block lacks fails with the code of its state error.
  let accounts ← toResult none (Execution.Blocks.Exports.accountsItem built.state)
  let encoded : Except BlockError (ByteArray × ByteArray) := do
    let block ← (Block.encode (← bodyItems built.block)).mapError .encoding
    let accounts ← (Serialization.Rlp.encode accounts).mapError .encoding
    return (block, accounts)
  -- A result with no encoding has code 0.
  let (block, accounts) ← toResult none
    (encoded.mapError fun e => UnreadArgument.mk s!"result: {reprStr e}")
  return (block, accounts, built.requests, built.blockValue)

/-- Build a payload on a chain, from attributes, the builder's choices and transactions.

The arguments are the configuration, the state, the recent blocks, the method and the attributes.

Then come the fee recipient, the extra data, the target gas limit and the transactions.

It returns the block and the accounts after it in RLP form, the requests and the block value. -/
@[export eth_engine_build_payload]
def buildPayloadExport (args : PyValue) : Result PyValue :=
  pyExport buildPayloadOf args

end EthLib.Engine.Exports
