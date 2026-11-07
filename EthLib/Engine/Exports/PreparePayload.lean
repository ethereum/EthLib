module

public import EthLib.Consensus.Exports.HonestProposer
public import EthLib.Engine.PreparePayload

/-!
# `Exports.PreparePayload`

The C export of the forkchoice update that an honest proposer sends, from Bellatrix to Fulu.

The state, the two block hashes, the fee recipient and each block of proof of work are SSZ bytes.

The preset, the configuration and the fork are named in UTF-8.

The configuration of the name holds, with its replacements.

The result is JSON text in UTF-8: `null`, or the forkchoice state and the payload attributes.

Their fields carry the names of the Engine API, with hex data and hex quantities.

The withdrawals appear from Capella, and the parent beacon block root from Deneb.

An input that does not decode, an unknown name or a fork outside Bellatrix to Fulu has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result)
open EthLib.Base
open EthLib.Consensus
open EthLib.Consensus.Exports

/-- Bytes as Engine API data: `0x`, then two hex digits per byte. -/
def dataJson (bytes : List UInt8) : Json :=
  .str (hexString bytes)

/-- A number as an Engine API quantity: `0x`, then its hex digits without leading zeros. -/
def quantityJson (n : Nat) : Json :=
  .str ("0x" ++ String.ofList (Nat.toDigits 16 n))

/-- A withdrawal as the Engine API writes it. -/
def withdrawalJson (w : Execution.Blocks.Withdrawal) : Json :=
  Json.mkObj [("index", quantityJson w.index.toNat),
    ("validatorIndex", quantityJson w.validatorIndex.toNat),
    ("address", dataJson w.address.toList), ("amount", quantityJson w.amount.toNat)]

/-- The forkchoice update of a proposer as JSON, with the fields of its fork. -/
def updateJson {fork : Fork} (update : ForkchoiceState) (attributes : PayloadAttributes fork) :
    Json :=
  let withdrawals := match sinceValue attributes.withdrawals with
    | some list => [("withdrawals", Json.arr (list.map withdrawalJson).toArray)]
    | none => []
  let parentRoot := match sinceValue attributes.parentBeaconBlockRoot with
    | some root => [("parentBeaconBlockRoot", dataJson root.toList)]
    | none => []
  Json.mkObj [
    ("forkchoiceState", Json.mkObj [
      ("headBlockHash", dataJson update.headBlockHash.toList),
      ("safeBlockHash", dataJson update.safeBlockHash.toList),
      ("finalizedBlockHash", dataJson update.finalizedBlockHash.toList)]),
    ("payloadAttributes", Json.mkObj ([
      ("timestamp", quantityJson attributes.timestamp.toNat),
      ("prevRandao", dataJson attributes.prevRandao.toList),
      ("suggestedFeeRecipient", dataJson attributes.suggestedFeeRecipient.toList)] ++
      withdrawals ++ parentRoot))]

/-- From Bellatrix to Fulu: the forkchoice update of a proposer, as JSON text.

It is `null` when the proposer asks for nothing, before the merge. -/
@[export eth_engine_prepare_execution_payload]
def prepareExecutionPayloadExport (name fork state replacements safe finalized : ByteArray)
    (feeRecipient : ByteArray) (powChain : Array ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let ⟨bellatrix⟩ ← holds (.bellatrix ≤ fork ∧ fork < .glamsterdam)
    s!"no payload preparation at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let safe ← decodeInput Root safe
  let finalized ← decodeInput Root finalized
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let powChain ← powChain.toList.mapM (decodeInput PowBlock)
  let prepared ← runProposer
    (prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain)
  let json := match prepared with
    | some (update, attributes) => updateJson update attributes
    | none => Json.null
  return json.compress.toUTF8

end EthLib.Engine.Exports
