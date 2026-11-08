module

public import EthLib.Consensus.Exports.ForkChoice
public import EthLib.Consensus.Exports.HonestProposer
public import EthLib.Engine.PreparePayload

/-!
# `Exports.PreparePayload`

The C exports of the forkchoice update that an honest proposer sends.

One covers Bellatrix to Fulu, and the other Gloas and Heze.

The state, the two block hashes, the fee recipient and each block of proof of work are SSZ bytes.

The preset, the configuration and the fork are named in UTF-8.

The configuration of the name holds, with its replacements.

The result is JSON text in UTF-8: `null`, or the forkchoice state and the payload attributes.

Their fields carry the names of the Engine API, with hex data and hex quantities.

The withdrawals appear from Capella, and the parent beacon block root from Deneb.

From Gloas the slot number and the target gas limit appear, and the custody columns are `null`.

The export from Gloas builds its store from an anchor state, an anchor block and steps.

Those steps take the form of the fork choice export.

Its arguments and its result are typed Python values, and the result is the `dict` of that JSON.

The head is a block root and a payload status: 0 empty, 1 full or 2 pending.

From Heze the result also holds the transactions of the inclusion lists, in hex.

The Engine API has no field for them, so they sit beside the payload attributes.

An input that does not decode, an unknown name or a fork that the export does not cover has code 0.

So do a step that does not read and a payload status above 2.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
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

/-- The forkchoice update of a proposer as JSON, with the fields of its fork and some others. -/
def updateJson {fork : Fork} (update : ForkchoiceState) (attributes : PayloadAttributes fork)
    (others : List (String × Json) := []) : Json :=
  let withdrawals := match sinceValue attributes.withdrawals with
    | some list => [("withdrawals", Json.arr (list.map withdrawalJson).toArray)]
    | none => []
  let parentRoot := match sinceValue attributes.parentBeaconBlockRoot with
    | some root => [("parentBeaconBlockRoot", dataJson root.toList)]
    | none => []
  let slotNumber := match sinceValue attributes.slotNumber with
    | some slot => [("slotNumber", quantityJson slot.toNat)]
    | none => []
  let targetGasLimit := match sinceValue attributes.targetGasLimit with
    | some limit => [("targetGasLimit", quantityJson limit.toNat)]
    | none => []
  Json.mkObj ([
    ("forkchoiceState", Json.mkObj [
      ("headBlockHash", dataJson update.headBlockHash.toList),
      ("safeBlockHash", dataJson update.safeBlockHash.toList),
      ("finalizedBlockHash", dataJson update.finalizedBlockHash.toList)]),
    ("payloadAttributes", Json.mkObj ([
      ("timestamp", quantityJson attributes.timestamp.toNat),
      ("prevRandao", dataJson attributes.prevRandao.toList),
      ("suggestedFeeRecipient", dataJson attributes.suggestedFeeRecipient.toList)] ++
      withdrawals ++ parentRoot ++ slotNumber ++ targetGasLimit))] ++ others)

/-- The arguments of the payload preparation of a proposer, from Bellatrix to Fulu.

They are the preset, the fork, the state in SSZ and replacements of values of the configuration.

Then come the safe and finalized block hashes, the fee recipient and the PoW blocks in SSZ. -/
abbrev PrepareArgs := String × String × ByteArray × Option PyValue × ByteArray × ByteArray ×
  ByteArray × List ByteArray

/-- From Bellatrix to Fulu: the forkchoice update of a proposer, as the value of its JSON.

It is `None` when the proposer asks for nothing, before the merge. -/
def prepareExecutionPayloadOf (args : PrepareArgs) : Result PyValue := do
  let (name, fork, state, replacements, safe, finalized, feeRecipient, powChain) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨bellatrix⟩ ← holds (.bellatrix ≤ fork ∧ fork < .glamsterdam)
    s!"no payload preparation at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let safe ← decodeInput Root safe
  let finalized ← decodeInput Root finalized
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let powChain ← powChain.mapM (decodeInput PowBlock)
  let prepared ← runProposer
    (prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain)
  return match prepared with
    | some (update, attributes) => .ofJson (updateJson update attributes)
    | none => .none

/-- From Bellatrix to Fulu: the forkchoice update of a proposer, as the value of its JSON.

The arguments are the preset, the fork, the state in SSZ, and replacements of the configuration.

Then come the safe and finalized block hashes, the fee recipient and the PoW blocks in SSZ.

It is `None` when the proposer asks for nothing, before the merge. -/
@[export eth_engine_prepare_execution_payload]
def prepareExecutionPayloadExport (args : PyValue) : Result PyValue :=
  pyExport prepareExecutionPayloadOf args

/-- The status of a payload from its code: 0 empty, 1 full and 2 pending. -/
def payloadStatusOfCode : UInt64 → Result Consensus.PayloadStatus
  | 0 => return .empty
  | 1 => return .full
  | 2 => return .pending
  | _ => throw (0, "a payload status is 0, 1 or 2")

/-- From Gloas: the forkchoice update of a proposer, as the value of its JSON.

The store comes from an anchor state, an anchor block and steps of the fork choice export.

The signature checks run unless the flag is false. -/
def preparePayloadOnStore
    (args : String × String × ByteArray × ByteArray × List ForkChoiceStep × ByteArray × UInt64 ×
      ByteArray × ByteArray × ByteArray × ByteArray × UInt64 × Bool × Option PyValue) :
    Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, headRoot, headStatus, state, safe, finalized,
    feeRecipient, targetGasLimit, verify, replacements) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨gloas⟩ ← holds (.glamsterdam ≤ fork) s!"no payload preparation on a store at {fork.name}"
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  let (store, _) ← replayForkChoice config checks anchorState anchorBlock steps
  let head : ForkChoiceNode :=
    { root := ← decodeInput Root headRoot, payloadStatus := ← payloadStatusOfCode headStatus }
  let state ← decodeInput (BeaconState preset fork) state
  let safe ← decodeInput Root safe
  let finalized ← decodeInput Root finalized
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let (update, attributes, transactions) ← runProposer (prepareExecutionPayloadGloas config checks
    store head state gloas safe finalized feeRecipient targetGasLimit)
  let lists := match sinceValue transactions with
    | some list =>
      [("inclusionListTransactions", Json.arr (list.map (dataJson ·.data.toList)).toArray)]
    | none => []
  return .ofJson (updateJson update attributes (("custodyColumns", Json.null) :: lists))

/-- From Gloas: the forkchoice update of a proposer, as the value of its JSON.

The arguments are the preset, the fork, the anchor state and the anchor block, and the steps.

Then come the head root and status, the state, the safe and finalized hashes and the fee recipient.

Then come the target gas limit, whether the signature checks run, and configuration replacements. -/
@[export eth_engine_prepare_execution_payload_gloas]
def prepareExecutionPayloadGloasExport (args : PyValue) : Result PyValue :=
  pyExport preparePayloadOnStore args

end EthLib.Engine.Exports
