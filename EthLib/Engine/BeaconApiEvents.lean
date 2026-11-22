module

public import EthLib.Consensus.BeaconApi.ChainEvents
public import EthLib.Engine.PreparePayload

/-!
# `Engine.BeaconApiEvents`

The event of the Beacon API that gives the payload attributes of a proposal.

It covers the forks from Bellatrix to Gloas.

A beacon node sends it when it has computed the attributes for a slot.

How often a node sends the event may depend on its configuration, so only its content is given.

The [event stream] gives the fields of the event, and a step comment names the field it follows.

[event stream]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/eventstream/index.yaml#L143
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Consensus
open EthLib.Consensus.BeaconApi
open EthLib.Serialization.JsonRpc
open Serialization.Ssz.SszType

variable {preset : Preset} {fork : Fork}

/-! ## The fields of the attributes, before they are spelled -/

/-- A value of one field of the payload attributes: an integer or bytes. -/
inductive AttributeScalar where
  /-- An integer. -/
  | quantity (n : Nat)
  /-- Bytes. -/
  | data (bytes : List UInt8)
  deriving DecidableEq, Repr

/-- The value of a field of the payload attributes.

It is one value, a list of objects, or a list of byte strings. -/
inductive AttributeValue where
  /-- One value. -/
  | scalar (value : AttributeScalar)
  /-- A list of objects, each with its named fields. -/
  | objects (items : List (List (String × AttributeScalar)))
  /-- A list of byte strings. -/
  | byteStrings (items : List (List UInt8))
  deriving DecidableEq, Repr

/-- The fields of a withdrawal, with the names of the Engine API. -/
def withdrawalFields (w : Execution.Blocks.Withdrawal) : List (String × AttributeScalar) :=
  [("index", .quantity w.index.toNat), ("validatorIndex", .quantity w.validatorIndex.toNat),
    ("address", .data w.address.toList), ("amount", .quantity w.amount.toNat)]

/-- The fields of payload attributes, with the names of the Engine API.

Each fork has the fields of its version of the structure. -/
def attributeFields (a : PayloadAttributes fork) : List (String × AttributeValue) :=
  -- `PayloadAttributesV1`: `timestamp`, `prevRandao` and `suggestedFeeRecipient`.
  [("timestamp", .scalar (.quantity a.timestamp.toNat)),
      ("prevRandao", .scalar (.data a.prevRandao.toList)),
      ("suggestedFeeRecipient", .scalar (.data a.suggestedFeeRecipient.toList))] ++
    -- `PayloadAttributesV2`, from Shapella, appends `withdrawals`.
    (if h : .shapella ≤ fork then
      [("withdrawals", .objects ((a.withdrawals h).map withdrawalFields))] else []) ++
    -- `PayloadAttributesV3`, from Dencun, appends `parentBeaconBlockRoot`.
    (if h : .dencun ≤ fork then
      [("parentBeaconBlockRoot", .scalar (.data (a.parentBeaconBlockRoot h).toList))]
      else []) ++
    -- `PayloadAttributesV4`, from Glamsterdam, appends `slotNumber` and `targetGasLimit`.
    (if h : .glamsterdam ≤ fork then
      [("slotNumber", .scalar (.quantity (a.slotNumber h).toNat)),
        ("targetGasLimit", .scalar (.quantity (a.targetGasLimit h).toNat))] else []) ++
    -- `PayloadAttributesV5`, from Hegota, appends `inclusionListTransactions`.
    (if h : .hegota ≤ fork then
      [("inclusionListTransactions",
        .byteStrings ((a.inclusionListTransactions h).map (·.data.toList)))] else [])

/-! ## The two spellings -/

/-- A camel-case name in snake case: each upper-case letter becomes `_` and its lower case.

The export derivation has the same function at compile time only, so a specification cannot call it.
-/
def snakeName (name : String) : String :=
  -- Difference 1: snake case identifiers rather than camel case.
  name.toList.foldl
    (fun out c => if c.isUpper then out ++ "_" ++ c.toLower.toString else out.push c) ""

/-- A value as the Engine API writes it: an integer in hexadecimal. -/
def AttributeScalar.engineJson : AttributeScalar → Json
  | .quantity n => quantityJson n
  | .data bytes => dataJson bytes

/-- A value as the Beacon API writes it: an integer as decimal text. -/
def AttributeScalar.apiJson : AttributeScalar → Json
  -- Difference 2: integers as quoted decimals rather than big-endian hex.
  | .quantity n => .str (toString n)
  | .data bytes => dataJson bytes

/-- Fields as an object of the Engine API, with their names. -/
def engineObject (fields : List (String × AttributeScalar)) : Json :=
  Json.mkObj (fields.map fun (name, value) => (name, value.engineJson))

/-- Fields as an object of the Beacon API, with their names in snake case. -/
def apiObject (fields : List (String × AttributeScalar)) : Json :=
  Json.mkObj (fields.map fun (name, value) => (snakeName name, value.apiJson))

/-- A field value as the Engine API writes it. -/
def AttributeValue.engineJson : AttributeValue → Json
  | .scalar value => value.engineJson
  | .objects items => .arr (items.toArray.map engineObject)
  | .byteStrings items => .arr (items.toArray.map dataJson)

/-- A field value as the Beacon API writes it. -/
def AttributeValue.apiJson : AttributeValue → Json
  | .scalar value => value.apiJson
  | .objects items => .arr (items.toArray.map apiObject)
  | .byteStrings items => .arr (items.toArray.map dataJson)

/-- Payload attributes as the Beacon API writes them: snake case keys and decimal integers. -/
def apiPayloadAttributesJson (a : PayloadAttributes fork) : Json :=
  -- The payload attributes: the Beacon API encoding of `PayloadAttributesV<N>` of the Engine API.
  --
  -- It has the fields of the Engine API object, with the two differences of spelling.
  Json.mkObj ((attributeFields a).map fun (name, value) => (snakeName name, value.apiJson))

/-! ## The event -/

/-- The payload attributes of a proposal, with the slot, the proposer and the parent block. -/
structure PayloadAttributesEvent (fork : Fork) where
  /-- The index of the proposer of the slot. -/
  proposerIndex : ValidatorIndex
  /-- The slot of the proposal. -/
  proposalSlot : Slot
  /-- Until Gloas: the number of the parent execution block. -/
  parentBlockNumber : Until .glamsterdam fork UInt64
  /-- The root of the parent beacon block. -/
  parentBlockRoot : Root
  /-- The hash of the parent execution block. -/
  parentBlockHash : Hash32
  /-- From Gloas: the safe block hash of the forkchoice update. -/
  safeBlockHash : Since .glamsterdam fork Hash32
  /-- From Gloas: the finalized block hash of the forkchoice update. -/
  finalizedBlockHash : Since .glamsterdam fork Hash32
  /-- The payload attributes. -/
  attributes : PayloadAttributes fork

/-- From Bellatrix to Fulu: the number of the execution block on which a proposer builds.

Once the merge is complete, and always from Capella, it is the number of the latest payload header.

Before that, the parent is the terminal block of proof of work, whose number the caller gives. -/
def parentBlockNumber (state : BeaconState preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) (terminalNumber : UInt64) : UInt64 :=
  if .shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true then
    (state.latestExecutionPayloadHeader bellatrix).blockNumber
  else terminalNumber

/-- From Bellatrix to Gloas: the event of the payload attributes of the update of a proposer.

The state must be at the slot of the proposal, after the empty slots and before its block.

Its latest block header then holds the state root of the parent, which the event does not check.

It fails when the proposer or the root of the header cannot be computed. -/
def payloadAttributesEvent (state : BeaconState preset fork)
    (forks : .bellatrix ≤ fork ∧ fork < .hegota)
    (update : ForkchoiceState) (attributes : PayloadAttributes fork) (terminalNumber : UInt64) :
    Except ProposerError (PayloadAttributesEvent fork) := do
  -- The proposer index: the proposer that the state at the proposal slot gives.
  let proposerIndex ← (getBeaconProposerIndex state).mapError .accessor
  -- The parent block root: the root of the latest block header of the state.
  let parentBlockRoot ← (hashTreeRoot state.latestBlockHeader).mapError .ssz
  -- The proposal slot is the slot of the state.
  return { proposerIndex, proposalSlot := state.slot, parentBlockRoot
           -- Until Gloas, the parent block number: that of the latest payload header of the state.
           --
           -- Before the merge, it is the number of the terminal block of proof of work.
           --
           -- The caller gives that number.
           parentBlockNumber := fun before =>
             parentBlockNumber state ⟨forks.1, before⟩ terminalNumber
           -- The parent block hash is the head of the update.
           parentBlockHash := update.headBlockHash
           -- From Gloas, the safe and the finalized block hashes that the update passes.
           safeBlockHash := fun _ => update.safeBlockHash
           finalizedBlockHash := fun _ => update.finalizedBlockHash, attributes }

namespace PayloadAttributesEvent

/-- The data of the event, as JSON. -/
def dataJson (e : PayloadAttributesEvent fork) : Json :=
  -- The proposer index and the proposal slot, as quoted decimals.
  Json.mkObj ([("proposer_index", uintJson e.proposerIndex),
      ("proposal_slot", uintJson e.proposalSlot)] ++
    -- The parent block number, removed from Gloas onwards.
    (if h : fork < .glamsterdam then [("parent_block_number", uintJson (e.parentBlockNumber h))]
      else []) ++
    -- The parent block root on the beacon chain, and the parent block hash on the execution chain.
    [("parent_block_root", ChainEvent.rootJson e.parentBlockRoot),
      ("parent_block_hash", Serialization.JsonRpc.dataJson e.parentBlockHash.toList)] ++
    -- The safe and the finalized block hashes, added from Gloas onwards.
    (if h : .glamsterdam ≤ fork then
      [("safe_block_hash", Serialization.JsonRpc.dataJson (e.safeBlockHash h).toList),
        ("finalized_block_hash", Serialization.JsonRpc.dataJson (e.finalizedBlockHash h).toList)]
      else []) ++
    [("payload_attributes", apiPayloadAttributesJson e.attributes)])

/-- The event of the stream, with the consensus version of the fork beside its data. -/
def toApiEvent (e : PayloadAttributesEvent fork) : ApiEvent :=
  -- The version is the beacon fork at the proposal slot, beside the data.
  ⟨.payloadAttributes,
    { version := fork.consensusVersion?, data := e.dataJson : ApiEnvelope }.toJson⟩

end PayloadAttributesEvent

end EthLib.Engine
