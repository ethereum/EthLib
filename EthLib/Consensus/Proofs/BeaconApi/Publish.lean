module

public import EthLib.Consensus.BeaconApi.Publish
public import EthLib.Consensus.Proofs.BeaconApi.Submit
public import EthLib.Consensus.Proofs.Gossip.Message

/-!
# Proofs: the answer to a block or an envelope to publish

A refused object leaves the fork choice store and the messages seen as they were.

Any other answer means that the gossip checks of its topic accept it, and records their keys.

Above the gossip level, it also means that the consensus checks of the object pass.

At the highest level, it also means that the store holds no rival of its block.

An object that passes its level is integrated exactly when the handler of the fork choice succeeds.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Networking.Gossip

variable {preset : Preset} {fork : Fork} {context : SubmitContext preset fork} {seen : Seen}
  {level : BroadcastValidation} {message : GossipMessage preset fork}
  {consensus : Unit → Option String} {rival : Unit → Bool}
  {integrate : Unit → Except ForkChoiceError (Store preset fork)}

/-! ## Any object -/

/-- The loop that searches a list for a match gives whether some element matches. -/
private theorem list_any_forIn {α : Type} (l : List α) (q : α → Bool) :
    (do
      let s ← forIn l ((none : Option Bool), ()) fun x _ =>
        if q x = true then pure (ForInStep.done (some true, ()))
        else pure (ForInStep.yield (none, ()))
      match s.fst with
        | some r => pure r
        | none => pure false : Id Bool) = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : q a = true
    · simp [h]; rfl
    · simp [h, ← ih]

/-- A tree map has an entry that matches exactly when its list of entries has one. -/
private theorem treeMap_any {α β : Type} {cmp : α → α → Ordering} (t : Std.TreeMap α β cmp)
    (p : α → β → Bool) : t.any p = t.toList.any (fun x => p x.1 x.2) := by
  unfold Std.TreeMap.any Std.DTreeMap.any
  simp only [Std.DTreeMap.Internal.Impl.any]
  have h := Std.DTreeMap.forIn_eq_forIn_toList (m := Id) (t := t.inner)
    (f := fun x s => if p x.1 x.2 = true then pure (ForInStep.done ((some true : Option Bool), ()))
      else pure (ForInStep.yield (none, ()))) (init := ((none : Option Bool), ()))
  have h2 := list_any_forIn t.inner.toList (fun x => p x.1 x.2)
  have h3 : t.toList = t.inner.toList.map (fun x => (x.1, x.2)) := by
    simp only [Std.TreeMap.toList, Std.DTreeMap.Const.toList, Std.DTreeMap.toList,
      Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map,
      Std.DTreeMap.Internal.Impl.toList_eq_toListModel]
  rw [h3, List.any_map]
  change _ = t.inner.toList.any (fun x => p x.1 x.2)
  rw [← h2, ← h]
  simp only [Id.run]
  congr 1
  funext s
  rcases s with ⟨_ | _, _⟩ <;> rfl

/-- A store holds a rival of a block exactly when it holds another root with its slot and proposer.
-/
theorem hasRival_iff {store : Store preset fork} {root : Root} {block : BeaconBlock preset fork} :
    hasRival store root block = true ↔
      ∃ other held, store.blocks[other]? = some held ∧ other ≠ root ∧
        held.slot = block.slot ∧ held.proposerIndex = block.proposerIndex := by
  rw [hasRival, treeMap_any, List.any_eq_true]
  constructor
  · rintro ⟨⟨other, held⟩, mem, h⟩
    rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some] at mem
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    exact ⟨other, held, mem, h.1.1, h.1.2, h.2⟩
  · rintro ⟨other, held, mem, h1, h2, h3⟩
    refine ⟨(other, held), ?_, ?_⟩
    · rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some]; exact mem
    · simp [h1, h2, h3]

/-- An object passes its level exactly when its gossip checks and the later checks of it pass. -/
theorem levelFailure_eq_none_iff {gossip : Option String} :
    levelFailure level gossip consensus rival = none ↔
      gossip = none ∧ (level ≠ .gossip → consensus () = none) ∧
        (level = .consensusAndEquivocation → rival () = false) := by
  cases gossip <;> cases level <;> cases passes : consensus () <;>
    cases rivals : rival () <;> simp [levelFailure, passes, rivals]

/-- A refused object leaves the store and the messages seen as they were. -/
theorem publish_refused {reason : String}
    (refused : (publish context seen level message consensus rival integrate).1 = .refused reason) :
    (publish context seen level message consensus rival integrate).2 = (context.store, seen) := by
  simp only [publish] at refused ⊢
  cases hl : levelFailure level (messageFailure context seen message).1 consensus rival with
  | none => cases h : integrate () <;> simp [hl, h] at refused
  | some reason => simp

/-- An object that passes its level is integrated exactly when the handler succeeds on it.

It is then answered with the store of the handler, and otherwise with the store as it was. -/
theorem publish_of_pass {after : Seen}
    (gossip : validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs message = .ok (.accept, after))
    (passes : levelFailure level none consensus rival = none) :
    publish context seen level message consensus rival integrate =
      match integrate () with
      | .ok store => (.integrated, store, after)
      | .error _ => (.broadcastNotIntegrated, context.store, after) := by
  have hm := messageFailure_of_ok gossip
  simp only [failureReason] at hm
  simp only [publish, hm, passes]
  cases h : integrate () <;> simp

/-- An object that is not refused passes gossip and its level, with some keys after. -/
private theorem publish_gossip
    (notRefused : ∀ reason,
      (publish context seen level message consensus rival integrate).1 ≠ .refused reason) :
    ∃ after, validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs message = .ok (.accept, after) ∧
      levelFailure level none consensus rival = none := by
  unfold publish at notRefused
  rcases hg : validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs message with error | ⟨outcome, after⟩
  · rw [messageFailure_of_error hg] at notRefused
    exact absurd rfl (notRefused _)
  · rw [messageFailure_of_ok hg] at notRefused
    cases outcome with
    | accept =>
      refine ⟨after, rfl, ?_⟩
      cases hl : levelFailure level none consensus rival with
      | none => rfl
      | some reason => simp [failureReason, hl] at notRefused
    | ignore reason => simp [failureReason, levelFailure] at notRefused
    | reject reason => simp [failureReason, levelFailure] at notRefused

/-- An object that is not refused passes its level, and gossip accepts its message.

The messages seen after it are those after gossip accepts it. -/
theorem publish_passes
    (notRefused : ∀ reason,
      (publish context seen level message consensus rival integrate).1 ≠ .refused reason) :
    levelFailure level none consensus rival = none ∧
      validateGossipMessage context.config context.checks context.setup seen context.store
        context.statuses context.currentTimeMs message =
        .ok (.accept, (publish context seen level message consensus rival integrate).2.2) := by
  obtain ⟨after, gossip, passes⟩ := publish_gossip notRefused
  rw [publish_of_pass gossip passes]
  refine ⟨passes, ?_⟩
  rw [gossip]
  split <;> rfl

/-- An object that is not refused above the gossip level passes its consensus check. -/
private theorem publish_consensus_none (above : level ≠ .gossip)
    (notRefused : ∀ reason,
      (publish context seen level message consensus rival integrate).1 ≠ .refused reason) :
    consensus () = none :=
  (levelFailure_eq_none_iff.mp (publish_gossip notRefused).choose_spec.2).2.1 above

/-- An object that is not refused at the highest level has no rival. -/
private theorem publish_rival_false
    (notRefused : ∀ reason, (publish context seen .consensusAndEquivocation message consensus
      rival integrate).1 ≠ .refused reason) :
    rival () = false :=
  (levelFailure_eq_none_iff.mp (publish_gossip notRefused).choose_spec.2).2.2 rfl

/-- The handler of the fork choice succeeds on an integrated object, with the store of the answer.
-/
private theorem publish_integrated_eq
    (integrated : (publish context seen level message consensus rival integrate).1 = .integrated) :
    integrate () = .ok (publish context seen level message consensus rival integrate).2.1 := by
  have notRefused : ∀ reason,
      (publish context seen level message consensus rival integrate).1 ≠ .refused reason := by
    intro reason h; rw [integrated] at h; cases h
  obtain ⟨after, gossip, passes⟩ := publish_gossip notRefused
  rw [publish_of_pass gossip passes] at integrated ⊢
  cases h : integrate () <;> simp [h] at integrated ⊢

/-- An object broadcast but not integrated fails its handler, and keeps the store as it was. -/
private theorem publish_broadcast_eq
    (broadcast :
      (publish context seen level message consensus rival integrate).1 = .broadcastNotIntegrated) :
    (∃ error, integrate () = .error error) ∧
      (publish context seen level message consensus rival integrate).2.1 = context.store := by
  have notRefused : ∀ reason,
      (publish context seen level message consensus rival integrate).1 ≠ .refused reason := by
    intro reason h; rw [broadcast] at h; cases h
  obtain ⟨after, gossip, passes⟩ := publish_gossip notRefused
  rw [publish_of_pass gossip passes] at broadcast ⊢
  cases h : integrate () with
  | ok store => simp [h] at broadcast
  | error e => simp

/-- A check with no reason of failure succeeded. -/
private theorem checkFailure_eq_none {label : String} {result : Except ForkChoiceError Unit}
    (none' : checkFailure label result = none) : result = .ok () := by
  rcases result with error | ⟨⟩
  · simp [checkFailure] at none'
  · rfl

/-! ## Blocks -/

variable {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}

/-- A refused block leaves the store and the messages seen as they were. -/
theorem publishBlock_refused_store {reason : String}
    (refused : (publishBlock context sources seen level signed).1 = .refused reason) :
    (publishBlock context sources seen level signed).2 = (context.store, seen) :=
  publish_refused refused

/-- A block that is not refused passes the gossip checks of its topic.

The messages seen after it hold its slot and its proposer. -/
theorem publishBlock_gossip
    (notRefused : ∀ reason, (publishBlock context sources seen level signed).1 ≠ .refused reason) :
    validateBeaconBlock context.config context.checks seen context.store context.statuses signed
        context.currentTimeMs = .ok .accept ∧
      (publishBlock context sources seen level signed).2.2 = seen.recordBeaconBlock signed := by
  obtain ⟨after, gossip, -⟩ := publish_gossip notRefused
  have valid := validateGossipMessage_outcome gossip
  have snd := (publish_passes notRefused).2
  rw [gossip] at snd
  have recorded : (GossipMessage.beaconBlock signed).record context.config context.store seen =
      .ok (seen.recordBeaconBlock signed) := rfl
  have hk := validateGossipMessage_of_accept valid recorded
  rw [hk] at gossip
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at gossip snd
  exact ⟨valid, snd.symm.trans gossip.symm⟩

/-- A block that is not refused above the gossip level passes the transition from its parent. -/
theorem publishBlock_consensus (above : level ≠ .gossip)
    (notRefused : ∀ reason, (publishBlock context sources seen level signed).1 ≠ .refused reason) :
    blockConsensus context sources signed = .ok () :=
  checkFailure_eq_none (publish_consensus_none above notRefused)

/-- A block that is not refused at the highest level has no rival in the store. -/
theorem publishBlock_noRival {root : Root}
    (rooted : Serialization.Ssz.SszType.hashTreeRoot signed.message = .ok root)
    (notRefused : ∀ reason, (publishBlock context sources seen .consensusAndEquivocation
      signed).1 ≠ .refused reason) :
    hasRival context.store root signed.message = false := by
  have none := publish_rival_false notRefused
  simpa [blockHasRival, rooted] using none

/-- A block that gossip accepts and that passes its level is broadcast.

It is integrated exactly when the block handler succeeds, with the store of the handler. -/
theorem publishBlock_of_pass {after : Seen}
    (gossip : validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs (.beaconBlock signed) =
        .ok (.accept, after))
    (passes : levelFailure level none
      (fun _ => checkFailure "consensus" (blockConsensus context sources signed))
      (fun _ => blockHasRival context.store signed.message) = none) :
    publishBlock context sources seen level signed =
      match context.store.onBlock context.config context.checks sources signed with
      | .ok store => (.integrated, store, after)
      | .error _ => (.broadcastNotIntegrated, context.store, after) :=
  publish_of_pass gossip passes

/-- An integrated block gives the store of the block handler of the fork choice. -/
theorem publishBlock_integrated
    (integrated : (publishBlock context sources seen level signed).1 = .integrated) :
    context.store.onBlock context.config context.checks sources signed =
      .ok (publishBlock context sources seen level signed).2.1 :=
  publish_integrated_eq integrated

/-- A block broadcast but not integrated fails the block handler, and keeps the store as it was.
-/
theorem publishBlock_broadcastNotIntegrated
    (broadcast : (publishBlock context sources seen level signed).1 = .broadcastNotIntegrated) :
    (∃ error,
      context.store.onBlock context.config context.checks sources signed = .error error) ∧
      (publishBlock context sources seen level signed).2.1 = context.store :=
  publish_broadcast_eq broadcast

/-! ## Envelopes -/

variable {gloas : .glamsterdam ≤ fork} {envelope : SignedExecutionPayloadEnvelope preset fork}

/-- A refused envelope leaves the store and the messages seen as they were. -/
theorem publishEnvelope_refused_store {reason : String}
    (refused : (publishEnvelope context sources seen level gloas envelope).1 = .refused reason) :
    (publishEnvelope context sources seen level gloas envelope).2 = (context.store, seen) :=
  publish_refused refused

/-- An envelope that is not refused passes the gossip checks of its topic.

The messages seen after it hold its block, its builder, and the hash and gas limit of its payload.
-/
theorem publishEnvelope_gossip
    (notRefused : ∀ reason,
      (publishEnvelope context sources seen level gloas envelope).1 ≠ .refused reason) :
    validateExecutionPayloadEnvelope context.config context.checks seen context.store gloas
        envelope = .ok .accept ∧
      (publishEnvelope context sources seen level gloas envelope).2.2 =
        seen.recordExecutionPayloadEnvelope envelope := by
  obtain ⟨after, gossip, -⟩ := publish_gossip notRefused
  have valid := validateGossipMessage_outcome gossip
  have snd := (publish_passes notRefused).2
  rw [gossip] at snd
  have recorded : (GossipMessage.executionPayloadEnvelope gloas envelope).record context.config
      context.store seen = .ok (seen.recordExecutionPayloadEnvelope envelope) := rfl
  have hk := validateGossipMessage_of_accept valid recorded
  rw [hk] at gossip
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at gossip snd
  exact ⟨valid, snd.symm.trans gossip.symm⟩

/-- An envelope that is not refused above the gossip level passes its checks against the state. -/
theorem publishEnvelope_consensus (above : level ≠ .gossip)
    (notRefused : ∀ reason,
      (publishEnvelope context sources seen level gloas envelope).1 ≠ .refused reason) :
    envelopeConsensus context sources gloas envelope = .ok () :=
  checkFailure_eq_none (publish_consensus_none above notRefused)

/-- An envelope that is not refused at the highest level names a block with no rival. -/
theorem publishEnvelope_noRival {block : BeaconBlock preset fork}
    (notRefused : ∀ reason, (publishEnvelope context sources seen .consensusAndEquivocation gloas
      envelope).1 ≠ .refused reason)
    (held : context.store.blocks[envelope.message.beaconBlockRoot]? = some block) :
    hasRival context.store envelope.message.beaconBlockRoot block = false := by
  have none := publish_rival_false notRefused
  simpa [envelopeHasRival, held] using none

/-- An envelope that gossip accepts and that passes its level is broadcast.

It is integrated exactly when the envelope handler succeeds, with the store of the handler. -/
theorem publishEnvelope_of_pass {after : Seen}
    (gossip : validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs
        (.executionPayloadEnvelope gloas envelope) = .ok (.accept, after))
    (passes : levelFailure level none
      (fun _ => checkFailure "consensus" (envelopeConsensus context sources gloas envelope))
      (fun _ => envelopeHasRival context.store envelope) = none) :
    publishEnvelope context sources seen level gloas envelope =
      match context.store.onExecutionPayloadEnvelope context.config context.checks sources gloas
          envelope with
      | .ok store => (.integrated, store, after)
      | .error _ => (.broadcastNotIntegrated, context.store, after) :=
  publish_of_pass gossip passes

/-- An integrated envelope gives the store of the envelope handler of the fork choice. -/
theorem publishEnvelope_integrated
    (integrated : (publishEnvelope context sources seen level gloas envelope).1 = .integrated) :
    context.store.onExecutionPayloadEnvelope context.config context.checks sources gloas envelope =
      .ok (publishEnvelope context sources seen level gloas envelope).2.1 :=
  publish_integrated_eq integrated

/-- An envelope broadcast but not integrated fails the envelope handler, and keeps the store.
-/
theorem publishEnvelope_broadcastNotIntegrated
    (broadcast :
      (publishEnvelope context sources seen level gloas envelope).1 = .broadcastNotIntegrated) :
    (∃ error, context.store.onExecutionPayloadEnvelope context.config context.checks sources gloas
        envelope = .error error) ∧
      (publishEnvelope context sources seen level gloas envelope).2.1 = context.store :=
  publish_broadcast_eq broadcast

end EthLib.Consensus.BeaconApi
