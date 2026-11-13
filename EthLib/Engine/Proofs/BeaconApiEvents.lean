module

public import EthLib.Engine.BeaconApiEvents
public import EthLib.Engine.Proofs.PreparePayload

/-!
# Proofs: the event of the payload attributes

The Engine API and the Beacon API write the same fields of payload attributes, from one list.

Each name of the Beacon API is that of the Engine API in snake case.

Each value is the same, as decimal text instead of hexadecimal for an integer.

The event names the slot of the state, its proposer, and the root of its latest block header.

Its parent block hash is the head of the forkchoice update, and its attributes are those given.

For the update of a proposer, the event and the attributes name one parent, before and from Gloas.
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Consensus
open Serialization.Ssz.SszType

variable {preset : Preset} {fork : Fork}

/-- The two APIs write the fields of payload attributes from one list, each in its own spelling.

The Engine API keeps the names and writes integers in hexadecimal.

The Beacon API writes the names in snake case and integers as decimal text.

The second half holds by definition, and the first is the content. -/
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

/-- The proposer of the event is the one that the state gives for its slot.

Its parent root is the root of the latest block header of the state.

Its slot is that of the state, its parent block hash the head of the update.

From Gloas its safe and finalized block hashes are those of the update.

Its attributes are those given, and until Gloas its parent number is read from the state. -/
theorem payloadAttributesEvent_spec {state : BeaconState preset fork}
    {forks : .bellatrix ≤ fork ∧ fork < .hegota} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork} {terminalNumber : UInt64}
    {event : PayloadAttributesEvent fork}
    (made : payloadAttributesEvent state forks update attributes terminalNumber = .ok event) :
    getBeaconProposerIndex state = .ok event.proposerIndex ∧
      hashTreeRoot state.latestBlockHeader = .ok event.parentBlockRoot ∧
      event.proposalSlot = state.slot ∧ event.parentBlockHash = update.headBlockHash ∧
      (∀ h, event.safeBlockHash h = update.safeBlockHash) ∧
      (∀ h, event.finalizedBlockHash h = update.finalizedBlockHash) ∧
      event.attributes = attributes ∧
      ∀ h, event.parentBlockNumber h = parentBlockNumber state ⟨forks.1, h⟩ terminalNumber := by
  unfold payloadAttributesEvent at made
  rcases h1 : getBeaconProposerIndex state with _ | proposer <;>
    rcases h2 : hashTreeRoot state.latestBlockHeader with _ | root <;>
    simp only [h1, h2, Except.mapError, bind, Except.bind, pure, Except.pure, reduceCtorEq,
      Except.ok.injEq] at made
  subst made
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl⟩

/-- Before Gloas, the event of the update of a proposer and its attributes name one parent.

Its parent block hash is the head that the proposer chose.

From Deneb, its parent root is the parent beacon block root of the attributes.

Its slot gives the timestamp of the attributes. -/
theorem payloadAttributesEvent_prepareExecutionPayload {config : Config}
    {state : BeaconState preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    {safeBlockHash finalizedBlockHash : Hash32} {suggestedFeeRecipient : ExecutionAddress}
    {powChain : List PowBlock} {update : ForkchoiceState} {attributes : PayloadAttributes fork}
    {forks : .bellatrix ≤ fork ∧ fork < .hegota} {terminalNumber : UInt64}
    {event : PayloadAttributesEvent fork}
    (prepared : prepareExecutionPayload config state bellatrix safeBlockHash finalizedBlockHash
      suggestedFeeRecipient powChain = .ok (some (update, attributes)))
    (made : payloadAttributesEvent state forks update attributes terminalNumber =
      .ok event) :
    payloadHeadBlockHash config state bellatrix powChain = .ok (some event.parentBlockHash) ∧
      (∀ h, attributes.parentBeaconBlockRoot h = event.parentBlockRoot) ∧
      computeTimeAtSlot config state.genesisTime event.proposalSlot =
        .ok attributes.timestamp := by
  obtain ⟨-, hroot, hslot, hhash, -⟩ := payloadAttributesEvent_spec made
  unfold prepareExecutionPayload at prepared
  rcases hh : payloadHeadBlockHash config state bellatrix powChain with _ | _ | head <;>
    simp only [hh, bind, Except.bind, pure, Except.pure, reduceCtorEq,
      Except.ok.injEq] at prepared
  rcases ht : computeTimeAtSlot config state.genesisTime state.slot with _ | time <;>
    simp only [ht, Except.mapError, reduceCtorEq] at prepared
  rcases hr : getRandaoMix state (getCurrentEpoch state) with _ | mix <;>
    simp only [hr, reduceCtorEq] at prepared
  rcases hw : payloadAttributesWithdrawals state with _ | wd <;>
    simp only [hw, reduceCtorEq] at prepared
  rcases hp : payloadAttributesParentRoot state with _ | pr <;>
    simp only [hp, reduceCtorEq, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at prepared
  obtain ⟨rfl, rfl⟩ := prepared
  refine ⟨?_, ?_, ?_⟩
  · simp [hhash]
  · intro h
    unfold payloadAttributesParentRoot at hp
    rcases hr' : hashTreeRoot state.latestBlockHeader with _ | r <;>
      simp only [h, ↓reduceDIte, Except.mapError, bind, Except.bind, pure, Except.pure, hr',
        reduceCtorEq] at hp
    obtain rfl := Except.ok.inj hp
    simp only [hr', Except.ok.injEq] at hroot
    exact hroot
  · rw [hslot]
    simpa using ht

/-- From Gloas, the event of the update of a proposer and its attributes name one parent.

The event reads the state of the attributes, the one on which the proposer builds.

Its parent block hash is the execution block on which the proposer builds.

Its safe and finalized block hashes are those given.

Its parent root is the parent beacon block root of the attributes.

Its slot is the slot number of the attributes, and gives their timestamp. -/
theorem payloadAttributesEvent_prepareExecutionPayloadGloas {config : Config}
    {checks : SignatureChecks} {store : Store preset fork} {head : ForkChoiceNode}
    {state base : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {safe finalized : Hash32} {feeRecipient : ExecutionAddress} {targetGasLimit : UInt64}
    {update : ForkchoiceState} {attributes : PayloadAttributes fork}
    {transactions : Since .hegota fork (List InclusionListTransaction)}
    {withdrawals : Array Consensus.Withdrawal} {parentHash : Hash32}
    {forks : .bellatrix ≤ fork ∧ fork < .hegota} {terminalNumber : UInt64}
    {event : PayloadAttributesEvent fork}
    (prepared : prepareExecutionPayloadGloas config checks store head state gloas safe finalized
      feeRecipient targetGasLimit = .ok (update, attributes, transactions))
    (parented : payloadParentGloas config checks store head state gloas =
      .ok (base, withdrawals, parentHash))
    (made : payloadAttributesEvent base forks update attributes terminalNumber = .ok event) :
    event.parentBlockHash = parentHash ∧ event.safeBlockHash gloas = safe ∧
      event.finalizedBlockHash gloas = finalized ∧
      (∀ deneb, attributes.parentBeaconBlockRoot deneb = event.parentBlockRoot) ∧
      attributes.slotNumber gloas = event.proposalSlot ∧
      computeTimeAtSlot config base.genesisTime event.proposalSlot = .ok attributes.timestamp := by
  obtain ⟨base', withdrawals', parented', hsafe, hfinalized, timed, -, -, -, rooted, slotted, -⟩ :=
    prepareExecutionPayloadGloas_eq_ok prepared
  rw [parented] at parented'
  simp only [Except.ok.injEq, Prod.mk.injEq] at parented'
  obtain ⟨rfl, -, hparent⟩ := parented'
  obtain ⟨-, hroot, hslot, hhash, hsafe', hfinalized', -⟩ := payloadAttributesEvent_spec made
  refine ⟨hhash.trans hparent.symm, (hsafe' gloas).trans hsafe,
    (hfinalized' gloas).trans hfinalized, fun deneb => ?_, slotted.trans hslot.symm,
    hslot ▸ timed⟩
  have same := (rooted deneb).symm.trans hroot
  simpa using same

end EthLib.Engine
