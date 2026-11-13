module

public import EthLib.Engine.BeaconApiEvents

/-!
# Proofs: the event of the payload attributes

The Engine API and the Beacon API write the same fields of payload attributes, in the same order.

Each name of the Beacon API is that of the Engine API in snake case.

Each value is the same, as decimal text instead of hexadecimal for an integer.

The event names the slot of the state, its proposer, and the root of its latest block header.

Its parent block hash is the head of the forkchoice update, and its attributes are those given.
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Consensus
open Serialization.Ssz.SszType

variable {preset : Preset} {fork : Fork}

/-- The two APIs write the fields of payload attributes in one order, each in its own spelling.

The Engine API keeps the names and writes integers in hexadecimal.

The Beacon API writes the names in snake case and integers as decimal text. -/
theorem payloadAttributesEvent_fields (a : PayloadAttributes fork) :
    payloadAttributesJson a =
        Json.mkObj ((attributeFields a).map fun (name, value) => (name, value.engineJson)) ∧
      apiPayloadAttributesJson a =
        Json.mkObj ((attributeFields a).map fun (name, value) =>
          (snakeName name, value.apiJson)) := by
  refine ⟨?_, rfl⟩
  unfold payloadAttributesJson attributeFields
  congr 1
  simp only [List.map_append]
  split <;> split <;> split <;>
    simp [AttributeValue.engineJson, AttributeScalar.engineJson, Execution.Rpc.withdrawalJson,
      engineObject, withdrawalFields, Serialization.JsonRpc.listJson]

/-- The event of a forkchoice update reads the proposer and the latest block header of the state.

Its slot is that of the state, its parent block hash the head of the update.

Its attributes and the number of its parent block are those given. -/
theorem payloadAttributesEvent_spec {state : BeaconState preset fork} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork} {number : Until .glamsterdam fork UInt64}
    {event : PayloadAttributesEvent fork}
    (made : payloadAttributesEvent state update attributes number = .ok event) :
    getBeaconProposerIndex state = .ok event.proposerIndex ∧
      hashTreeRoot state.latestBlockHeader = .ok event.parentBlockRoot ∧
      event.proposalSlot = state.slot ∧ event.parentBlockHash = update.headBlockHash ∧
      event.attributes = attributes ∧ event.parentBlockNumber = number := by
  unfold payloadAttributesEvent at made
  rcases h1 : getBeaconProposerIndex state with _ | proposer <;>
    rcases h2 : hashTreeRoot state.latestBlockHeader with _ | root <;>
    simp only [h1, h2, Except.mapError, bind, Except.bind, pure, Except.pure, reduceCtorEq,
      Except.ok.injEq] at made
  subst made
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end EthLib.Engine
