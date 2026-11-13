module

public import EthLib.Consensus.BeaconApi.ChainEvents
public import EthLib.Engine.PreparePayload

/-!
# `Engine.BeaconApiEvents`

The event of the Beacon API that gives the payload attributes of a proposal.

A beacon node sends it when it has computed the attributes for a slot.

Builders and relays read it to build or check a block at that slot.

It names the slot, the proposer, and the parent block on both layers.

From Gloas it also names the safe and the finalized block hashes of the forkchoice update.

The attributes are those of the Engine API, with two changes of spelling.

Keys are in snake case, and integers are decimal text instead of hexadecimal.

How often a node sends the event depends on its configuration, so only its content is given here.

The [event stream] gives the fields of the event.

[event stream]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/eventstream/index.yaml
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

/-- The value of a field of the payload attributes: one value, or a list of objects. -/
inductive AttributeValue where
  /-- One value. -/
  | scalar (value : AttributeScalar)
  /-- A list of objects, each with its named fields. -/
  | objects (items : List (List (String × AttributeScalar)))
  deriving DecidableEq, Repr

/-- The fields of a withdrawal, with the names of the Engine API. -/
def withdrawalFields (w : Execution.Blocks.Withdrawal) : List (String × AttributeScalar) :=
  [("index", .quantity w.index.toNat), ("validatorIndex", .quantity w.validatorIndex.toNat),
    ("address", .data w.address.toList), ("amount", .quantity w.amount.toNat)]

/-- The fields of payload attributes, with the names of the Engine API, in its order.

Each fork has the fields of its version of the structure. -/
def attributeFields (a : PayloadAttributes fork) : List (String × AttributeValue) :=
  [("timestamp", .scalar (.quantity a.timestamp.toNat)),
      ("prevRandao", .scalar (.data a.prevRandao.toList)),
      ("suggestedFeeRecipient", .scalar (.data a.suggestedFeeRecipient.toList))] ++
    (if h : .shapella ≤ fork then
      [("withdrawals", .objects ((a.withdrawals h).map withdrawalFields))] else []) ++
    (if h : .dencun ≤ fork then
      [("parentBeaconBlockRoot", .scalar (.data (a.parentBeaconBlockRoot h).toList))]
      else []) ++
    (if h : .glamsterdam ≤ fork then
      [("slotNumber", .scalar (.quantity (a.slotNumber h).toNat)),
        ("targetGasLimit", .scalar (.quantity (a.targetGasLimit h).toNat))] else [])

/-! ## The two spellings -/

/-- A name in camel case, in snake case: an upper-case letter becomes `_` and its lower case. -/
def snakeName (name : String) : String :=
  name.foldl (fun out c => if c.isUpper then out ++ "_" ++ c.toLower.toString else out.push c) ""

/-- A value as the Engine API writes it: an integer in hexadecimal. -/
def AttributeScalar.engineJson : AttributeScalar → Json
  | .quantity n => quantityJson n
  | .data bytes => dataJson bytes

/-- A value as the Beacon API writes it: an integer as decimal text. -/
def AttributeScalar.apiJson : AttributeScalar → Json
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

/-- A field value as the Beacon API writes it. -/
def AttributeValue.apiJson : AttributeValue → Json
  | .scalar value => value.apiJson
  | .objects items => .arr (items.toArray.map apiObject)

/-- Payload attributes as the Beacon API writes them: snake case keys and decimal integers. -/
def apiPayloadAttributesJson (a : PayloadAttributes fork) : Json :=
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

/-- The event of the payload attributes of a forkchoice update of a proposer.

The state is the one that the attributes read, at the slot of the proposal and before its block.

The slot is that of the state, and the proposer is the one that the state gives for it.

The parent root is the root of the latest block header of the state.

The parent block hash is the head of the update.

From Gloas the safe and the finalized block hashes are those of the update.

Until Gloas the number of the parent block is given, since the execution layer holds it.

It fails when the proposer or the root of the header cannot be computed. -/
def payloadAttributesEvent (state : BeaconState preset fork) (update : ForkchoiceState)
    (attributes : PayloadAttributes fork) (parentBlockNumber : Until .glamsterdam fork UInt64) :
    Except ProposerError (PayloadAttributesEvent fork) := do
  let proposerIndex ← (getBeaconProposerIndex state).mapError .accessor
  let parentBlockRoot ← (hashTreeRoot state.latestBlockHeader).mapError .ssz
  return { proposerIndex, proposalSlot := state.slot, parentBlockNumber, parentBlockRoot
           parentBlockHash := update.headBlockHash
           safeBlockHash := fun _ => update.safeBlockHash
           finalizedBlockHash := fun _ => update.finalizedBlockHash, attributes }

namespace PayloadAttributesEvent

/-- The data of the event, as JSON. -/
def dataJson (e : PayloadAttributesEvent fork) : Json :=
  Json.mkObj ([("proposer_index", uintJson e.proposerIndex),
      ("proposal_slot", uintJson e.proposalSlot)] ++
    (if h : fork < .glamsterdam then [("parent_block_number", uintJson (e.parentBlockNumber h))]
      else []) ++
    [("parent_block_root", ChainEvent.rootJson e.parentBlockRoot),
      ("parent_block_hash", Serialization.JsonRpc.dataJson e.parentBlockHash.toList)] ++
    (if h : .glamsterdam ≤ fork then
      [("safe_block_hash", Serialization.JsonRpc.dataJson (e.safeBlockHash h).toList),
        ("finalized_block_hash", Serialization.JsonRpc.dataJson (e.finalizedBlockHash h).toList)]
      else []) ++
    [("payload_attributes", apiPayloadAttributesJson e.attributes)])

/-- The event of the stream, with the consensus version of the fork beside its data. -/
def toApiEvent (e : PayloadAttributesEvent fork) : ApiEvent :=
  ⟨.payloadAttributes,
    { version := fork.consensusVersion?, data := e.dataJson : ApiEnvelope }.toJson⟩

end PayloadAttributesEvent

end EthLib.Engine
