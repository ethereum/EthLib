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

From Gloas the slot number and the target gas limit appear.

The custody columns are 16 bytes of an SSZ bitvector that the caller gives, else `null`.

The Engine API gives no bit order, so EthLib takes that of the bitvector, as for blob cells.

The export from Gloas builds its store from an anchor state, an anchor block and steps.

It reads the finalized block hash from that store.

Those steps take the form of the fork choice export.

Its arguments and its result are typed Python values, and the result is the `dict` of that JSON.

The head is a block root and a payload status: 0 empty, 1 full or 2 pending.

From Heze the result also holds the transactions of the inclusion lists, in hex.

The Engine API has no field for them, so they sit beside the payload attributes.

An input that does not decode, an unknown name or a fork that the export does not cover has code 0.

So do a step that does not read and a payload status above 2.

A third export gives the finalized block hash of a store, from Bellatrix.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Consensus
open EthLib.Consensus.Exports
open EthLib.Engine.Json (dataJson quantityJson withdrawalJson)

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

The finalized block hash is that of the store.

The custody columns are given as the SSZ bytes of their bitvector, or not at all.

The signature checks run unless the flag is false. -/
def preparePayloadOnStore
    (args : String × String × ByteArray × ByteArray × List ForkChoiceStep × ByteArray × UInt64 ×
      ByteArray × ByteArray × ByteArray × UInt64 × Option ByteArray × Bool × Option PyValue) :
    Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, headRoot, headStatus, state, safe,
    feeRecipient, targetGasLimit, custodyColumns, verify, replacements) := args
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
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let custody ← match custodyColumns with
    | some bytes => do
      let _ ← decodeInput (Serialization.Ssz.Bitvector preset.NUMBER_OF_COLUMNS.toNat) bytes
      pure (dataJson bytes.toList)
    | none => pure Json.null
  let finalized ← runProposer
    ((getFinalizedExecutionBlockHash store (Nat.le_trans (by decide) gloas)).mapError .forkChoice)
  let (update, attributes, transactions) ← runProposer (prepareExecutionPayloadGloas config checks
    store head state gloas safe finalized feeRecipient targetGasLimit)
  let lists := match sinceValue transactions with
    | some list =>
      [("inclusionListTransactions", Json.arr (list.map (dataJson ·.data.toList)).toArray)]
    | none => []
  return .ofJson (updateJson update attributes (("custodyColumns", custody) :: lists))

/-- From Gloas: the forkchoice update of a proposer, as the value of its JSON.

The arguments are the preset, the fork, the anchor state and the anchor block, and the steps.

Then come the head root and status, the state, the safe hash and the fee recipient.

Then come the target gas limit and the custody columns in SSZ, or `None`.

Last come whether the signature checks run, and configuration replacements.

The finalized hash is that of the store. -/
@[export eth_engine_prepare_execution_payload_gloas]
def prepareExecutionPayloadGloasExport (args : PyValue) : Result PyValue :=
  pyExport preparePayloadOnStore args

/-- From Bellatrix: the finalized block hash of a store, after the steps of a fork choice case.

The signature checks run unless the flag is false. -/
def finalizedExecutionBlockHashOf (args : String × String × ByteArray × ByteArray ×
    List ForkChoiceStep × Bool × Option PyValue) : Result ByteArray := do
  let (name, fork, anchorState, anchorBlock, steps, verify, replacements) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨bellatrix⟩ ← holds (.bellatrix ≤ fork) s!"no execution block hash at {fork.name}"
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  let (store, _) ← replayForkChoice config checks anchorState anchorBlock steps
  let hash ← runForkChoice (getFinalizedExecutionBlockHash store bellatrix)
  return ⟨hash.toArray⟩

/-- From Bellatrix: the 32 bytes of the finalized block hash of a store.

The arguments are the preset, the fork, the anchor state and the anchor block, and the steps.

Then come whether the signature checks run, and replacements of values of the configuration. -/
@[export eth_engine_finalized_execution_block_hash]
def finalizedExecutionBlockHashExport (args : PyValue) : Result PyValue :=
  pyExport finalizedExecutionBlockHashOf args

end EthLib.Engine.Exports
