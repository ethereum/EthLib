module

public import EthLib.Consensus.BeaconApi.ObjectEvents
public import EthLib.Consensus.Proofs.BeaconApi.Publish
public import EthLib.Consensus.Proofs.ForkChoice.Handlers

/-!
# Proofs: the events for a received object

An object whose topic has an event gives it exactly when gossip accepts the object.

A message that passes the gossip check of an endpoint gives the events it gives from a peer.

An object that a publish endpoint integrates also gives the events of an import.

A block event names a block that is new to the store, and that the store then holds.

From Gloas it names the builder and the block hash of the bid of the block.

An envelope is imported exactly when the envelope handler accepts it.

The store then counts its payload as verified, and a new payload gives its payload event.

-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-! ## Gossip -/

/-- An object whose topic has an event gives it exactly when gossip accepts the object. -/
theorem eventsOfGossip_accept {outcome : ValidationResult} {message : GossipMessage preset fork}
    {event : ObjectEvent preset fork} (found : objectEventOf message = .ok (some event)) :
    eventsOfGossip outcome message = .ok [event] ↔ outcome = .accept := by
  cases outcome <;>
    simp [eventsOfGossip, ValidationResult.isAccept, found, bind, Except.bind, pure, Except.pure]

/-- An object that gossip does not accept gives no event. -/
theorem eventsOfGossip_of_not_accept {outcome : ValidationResult}
    {message : GossipMessage preset fork} (refused : outcome ≠ .accept) :
    eventsOfGossip outcome message = .ok [] := by
  cases outcome <;> simp_all [eventsOfGossip, ValidationResult.isAccept, pure, Except.pure]

/-- A received message gives an event only when the dispatch of gossip accepts it. -/
theorem receiveGossip_accept {context : SubmitContext preset fork} {seen after : Seen}
    {message : GossipMessage preset fork} {outcome : ValidationResult}
    {event : ObjectEvent preset fork} {rest : List (ObjectEvent preset fork)}
    (received : receiveGossip context seen message = .ok (outcome, after, event :: rest)) :
    outcome = .accept ∧ validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs message = .ok (.accept, after) := by
  unfold receiveGossip at received
  rcases gossip : validateGossipMessage context.config context.checks context.setup seen
    context.store context.statuses context.currentTimeMs message with error | ⟨judged, keys⟩
  · simp [gossip, bind, Except.bind] at received
  · rw [gossip] at received
    by_cases accepted : judged = .accept
    · subst accepted
      cases events : eventsOfGossip .accept message <;>
        simp_all [bind, Except.bind, Except.mapError, pure, Except.pure]
    · simp [eventsOfGossip_of_not_accept accepted, bind, Except.bind, Except.mapError, pure,
        Except.pure] at received

/-- A message that passes gossip gives the event of its topic, with the messages seen after it.

A pool endpoint and the publish endpoints judge their objects by this same check. -/
theorem receiveGossip_of_pass {context : SubmitContext preset fork} {seen after : Seen}
    {message : GossipMessage preset fork}
    (passes : messageFailure context seen message = (none, after)) :
    receiveGossip context seen message =
      ((objectEventOf message).mapError .ssz).map fun event => (.accept, after, event.toList) := by
  unfold messageFailure at passes
  rcases gossip : validateGossipMessage context.config context.checks context.setup seen
    context.store context.statuses context.currentTimeMs message with error | ⟨judged, keys⟩
  · simp [gossip] at passes
  · simp only [gossip, Prod.mk.injEq] at passes
    obtain ⟨reason, rfl⟩ := passes
    cases judged <;> simp [failureReason] at reason
    simp only [receiveGossip, gossip, eventsOfGossip, ValidationResult.isAccept]
    cases objectEventOf message <;> rfl

/-- An object that a publish endpoint does not refuse gives the events it gives from a peer.

The messages seen after it are those that the endpoint keeps. -/
theorem publish_receiveGossip {context : SubmitContext preset fork} {seen : Seen}
    {level : BroadcastValidation} {message : GossipMessage preset fork}
    {consensus : Unit → Option String} {rival : Unit → Bool}
    {integrate : Unit → Except ForkChoiceError (Store preset fork)}
    (notRefused : ∀ reason,
      (publish context seen level message consensus rival integrate).1 ≠ .refused reason) :
    receiveGossip context seen message =
      ((objectEventOf message).mapError .ssz).map fun event =>
        (.accept, (publish context seen level message consensus rival integrate).2.2,
          event.toList) :=
  receiveGossip_of_pass (by simp [messageFailure, (publish_passes notRefused).2, failureReason])

/-! ## Imports -/

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {store after : Store preset fork} {optimistic : Root → Bool}

/-- An imported block has a root, and the store after it is the one that the block handler gives.

The block event comes when the store did not hold that root before. -/
theorem eventsOfBlockImport_ok {signed : SignedBeaconBlock preset fork}
    {events : List (ObjectEvent preset fork)}
    (imported : eventsOfBlockImport config checks sources store optimistic signed =
      .ok (after, events)) :
    ∃ root, SszType.hashTreeRoot signed.message = .ok root ∧
      store.onBlock config checks sources signed = .ok after ∧
      events = if store.blocks.contains root then [] else
        [.block ⟨signed.message.slot, root, optimistic root, blockBid signed.message⟩] := by
  unfold eventsOfBlockImport blockEvent? at imported
  rcases rooted : SszType.hashTreeRoot signed.message with error | root
  · simp [rooted, bind, Except.bind, Except.mapError] at imported
  refine ⟨root, rfl, ?_⟩
  rcases handled : store.onBlock config checks sources signed with error | stored <;>
    cases known : store.blocks.contains root <;>
    simp_all [bind, Except.bind, Except.mapError, pure, Except.pure]

/-- A block event names a block that is new to the store, and that the store then holds.

It carries the slot and the root of that block. -/
theorem eventsOfBlockImport_block {signed : SignedBeaconBlock preset fork}
    {events : List (ObjectEvent preset fork)} {event : BlockEvent}
    (imported : eventsOfBlockImport config checks sources store optimistic signed =
      .ok (after, events))
    (emitted : .block event ∈ events) :
    SszType.hashTreeRoot signed.message = .ok event.block ∧ event.slot = signed.message.slot ∧
      store.blocks[event.block]? = none ∧ after.blocks[event.block]? = some signed.message := by
  obtain ⟨root, rooted, handled, rfl⟩ := eventsOfBlockImport_ok imported
  cases known : store.blocks.contains root
  · simp only [known, Bool.false_eq_true, ↓reduceIte, List.mem_singleton,
      ObjectEvent.block.injEq] at emitted
    subst emitted
    have new : ¬ store.blocks.contains root := by simp [known]
    exact ⟨rooted, rfl, Std.TreeMap.getElem?_eq_none_of_contains_eq_false known,
      (Store.onBlock_new rooted new handled).2.1⟩
  · simp [known] at emitted

/-- A new block that the handler accepts gives its block event. -/
theorem eventsOfBlockImport_new {signed : SignedBeaconBlock preset fork} {root : Root}
    (rooted : SszType.hashTreeRoot signed.message = .ok root) (new : ¬ store.blocks.contains root)
    (handled : store.onBlock config checks sources signed = .ok after) :
    eventsOfBlockImport config checks sources store optimistic signed =
      .ok (after,
        [.block ⟨signed.message.slot, root, optimistic root, blockBid signed.message⟩]) := by
  simp [eventsOfBlockImport, blockEvent?, rooted, handled, new, bind, Except.bind, Except.mapError,
    pure, Except.pure]

/-- From Gloas, a block event names the builder and the block hash of the bid of its block.

Before Gloas it names neither. -/
theorem blockEvent_gloas {signed : SignedBeaconBlock preset fork}
    {events : List (ObjectEvent preset fork)} {event : BlockEvent}
    (imported : eventsOfBlockImport config checks sources store optimistic signed =
      .ok (after, events))
    (emitted : .block event ∈ events) :
    event.bid = if gloas : .glamsterdam ≤ fork then
      some ((signed.message.body.signedExecutionPayloadBid gloas).message.builderIndex,
        (signed.message.body.signedExecutionPayloadBid gloas).message.blockHash)
    else none := by
  obtain ⟨root, -, -, rfl⟩ := eventsOfBlockImport_ok imported
  cases known : store.blocks.contains root
  · simp only [known, Bool.false_eq_true, ↓reduceIte, List.mem_singleton,
      ObjectEvent.block.injEq] at emitted
    subst emitted
    rfl
  · simp [known] at emitted

/-- From Gloas, the handler accepted an imported envelope.

The store after it counts its payload as verified.

Its payload event comes when the store before it had no payload for its block. -/
theorem eventsOfEnvelopeImport_ok {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork}
    {events : List (ObjectEvent preset fork)}
    (imported : eventsOfEnvelopeImport config checks sources store optimistic gloas signed =
      .ok (after, events)) :
    store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after ∧
      events = (envelopeEvent? store optimistic gloas signed.message).toList ∧
      after.isPayloadVerified gloas signed.message.beaconBlockRoot = true := by
  unfold eventsOfEnvelopeImport at imported
  rcases handled : store.onExecutionPayloadEnvelope config checks sources gloas signed with
    error | stored
  · simp [handled, bind, Except.bind] at imported
  · simp only [handled, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at imported
    obtain ⟨rfl, rfl⟩ := imported
    exact ⟨rfl, rfl, Store.onExecutionPayloadEnvelope_verified handled⟩

/-- From Gloas, an envelope that the handler accepts is imported, with its payload event if any.
-/
theorem eventsOfEnvelopeImport_of_accepted {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork}
    (handled : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    eventsOfEnvelopeImport config checks sources store optimistic gloas signed =
      .ok (after, (envelopeEvent? store optimistic gloas signed.message).toList) := by
  simp [eventsOfEnvelopeImport, handled, bind, Except.bind, pure, Except.pure]

/-- From Gloas, an envelope gives a payload event exactly when its payload is new to the store.

The event names the payload of the envelope and the optimistic flag of its block. -/
theorem envelopeEvent?_eq_some {gloas : .glamsterdam ≤ fork}
    {envelope : ExecutionPayloadEnvelope preset fork} {event : ObjectEvent preset fork} :
    envelopeEvent? store optimistic gloas envelope = some event ↔
      (store.payloads gloas).contains envelope.beaconBlockRoot = false ∧
        event = .executionPayload gloas (payloadEvent gloas envelope)
          (optimistic envelope.beaconBlockRoot) := by
  unfold envelopeEvent?
  cases h : (store.payloads gloas).contains envelope.beaconBlockRoot
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, true_and]
    exact ⟨Eq.symm, Eq.symm⟩
  · simp [h]

/-! ## Publication -/

/-- A message that passes gossip gives the event of its topic, as an item of its own. -/
theorem itemEvents_singleton_of_pass {context : SubmitContext preset fork} {seen after : Seen}
    {message : GossipMessage preset fork}
    (passes : messageFailure context seen message = (none, after)) :
    itemEvents context seen [message] = (objectEventOf message).map Option.toList := by
  simp only [itemEvents, passes, Option.isNone_none, ↓reduceIte]
  cases objectEventOf message <;> simp [bind, Except.bind, pure, Except.pure, Except.map]

/-- A message that fails gossip gives no event, as an item of its own. -/
theorem itemEvents_singleton_of_fail {context : SubmitContext preset fork} {seen : Seen}
    {message : GossipMessage preset fork} {reason : String}
    (fails : (messageFailure context seen message).1 = some reason) :
    itemEvents context seen [message] = .ok [] := by
  rcases h : messageFailure context seen message with ⟨reason', after⟩
  rw [h] at fails
  subst fails
  simp [itemEvents, h, bind, Except.bind, pure, Except.pure]

/-- An object that fails gossip is refused, with the reason of gossip, at any level. -/
theorem publish_of_fail {context : SubmitContext preset fork} {seen : Seen}
    {level : BroadcastValidation} {message : GossipMessage preset fork}
    {consensus : Unit → Option String} {rival : Unit → Bool}
    {integrate : Unit → Except ForkChoiceError (Store preset fork)} {reason : String}
    (fails : (messageFailure context seen message).1 = some reason) :
    (publish context seen level message consensus rival integrate).1 = .refused reason := by
  unfold publish
  rcases h : messageFailure context seen message with ⟨reason', after⟩
  rw [h] at fails
  subst fails
  simp [levelFailure]

variable {context : SubmitContext preset fork} {seen : Seen} {level : BroadcastValidation}

/-- A block that a publish endpoint integrates gives the store of an import and its block event.
-/
theorem publishBlock_eventsOfBlockImport {signed : SignedBeaconBlock preset fork}
    {event : Option BlockEvent}
    (integrated : (publishBlock context sources seen level signed).1 = .integrated)
    (found : blockEvent? context.store optimistic signed = .ok event) :
    eventsOfBlockImport context.config context.checks sources context.store optimistic signed =
      .ok ((publishBlock context sources seen level signed).2.1, (event.map .block).toList) := by
  unfold eventsOfBlockImport
  rw [found]
  simp only [Except.mapError, bind, Except.bind, publishBlock_integrated integrated, pure,
    Except.pure]

/-- A block that a publish endpoint integrates gives its gossip event, then its block event. -/
theorem publishBlockEvents_integrated {signed : SignedBeaconBlock preset fork}
    {event : Option BlockEvent}
    (integrated : (publishBlock context sources seen level signed).1 = .integrated)
    (found : blockEvent? context.store optimistic signed = .ok event) :
    publishBlockEvents context seen optimistic signed
        (publishBlock context sources seen level signed).1 =
      (objectEventOf (.beaconBlock signed : GossipMessage preset fork)).map fun gossip =>
        gossip.toList ++ (event.map .block).toList := by
  have notRefused : ∀ reason,
      (publishBlock context sources seen level signed).1 ≠ .refused reason := by
    intro reason refused
    rw [integrated] at refused
    cases refused
  have passes := itemEvents_singleton_of_pass (messageFailure_of_ok (publish_passes notRefused).2)
  rw [integrated]
  simp only [publishBlockEvents, passes, found]
  cases objectEventOf (.beaconBlock signed : GossipMessage preset fork) <;>
    simp [bind, Except.bind, pure, Except.pure, Except.map]

/-- A block that fails gossip gives no event at a publish endpoint. -/
theorem publishBlockEvents_of_fail {signed : SignedBeaconBlock preset fork} {reason : String}
    (fails : (messageFailure context seen (.beaconBlock signed)).1 = some reason) :
    publishBlockEvents context seen optimistic signed
      (publishBlock context sources seen level signed).1 = .ok [] := by
  rw [show (publishBlock context sources seen level signed).1 = .refused reason from
    publish_of_fail fails]
  simp [publishBlockEvents, itemEvents_singleton_of_fail fails, bind, Except.bind, pure,
    Except.pure]

/-- From Gloas, an envelope that a publish endpoint integrates gives the events of an import. -/
theorem publishEnvelope_eventsOfEnvelopeImport {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork}
    (integrated : (publishEnvelope context sources seen level gloas signed).1 = .integrated) :
    eventsOfEnvelopeImport context.config context.checks sources context.store optimistic gloas
        signed =
      .ok ((publishEnvelope context sources seen level gloas signed).2.1,
        (envelopeEvent? context.store optimistic gloas signed.message).toList) := by
  unfold eventsOfEnvelopeImport
  simp only [bind, Except.bind, publishEnvelope_integrated integrated, pure, Except.pure]

/-- From Gloas, an envelope that a publish endpoint integrates gives its gossip and payload events.
-/
theorem publishEnvelopeEvents_integrated {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork}
    (integrated : (publishEnvelope context sources seen level gloas signed).1 = .integrated) :
    publishEnvelopeEvents context seen optimistic gloas signed
        (publishEnvelope context sources seen level gloas signed).1 =
      (objectEventOf (.executionPayloadEnvelope gloas signed : GossipMessage preset fork)).map
        fun gossip => gossip.toList ++
          (envelopeEvent? context.store optimistic gloas signed.message).toList := by
  have notRefused : ∀ reason,
      (publishEnvelope context sources seen level gloas signed).1 ≠ .refused reason := by
    intro reason refused
    rw [integrated] at refused
    cases refused
  have passes := itemEvents_singleton_of_pass (messageFailure_of_ok (publish_passes notRefused).2)
  rw [integrated]
  simp only [publishEnvelopeEvents, passes]
  cases objectEventOf (.executionPayloadEnvelope gloas signed : GossipMessage preset fork) <;>
    simp [bind, Except.bind, pure, Except.pure, Except.map]

/-- From Gloas, an envelope that fails gossip gives no event at a publish endpoint. -/
theorem publishEnvelopeEvents_of_fail {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork} {reason : String}
    (fails : (messageFailure context seen (.executionPayloadEnvelope gloas signed)).1 =
      some reason) :
    publishEnvelopeEvents context seen optimistic gloas signed
      (publishEnvelope context sources seen level gloas signed).1 = .ok [] := by
  rw [show (publishEnvelope context sources seen level gloas signed).1 = .refused reason from
    publish_of_fail fails]
  simp [publishEnvelopeEvents, itemEvents_singleton_of_fail fails, bind, Except.bind, pure,
    Except.pure]

end EthLib.Consensus.BeaconApi
