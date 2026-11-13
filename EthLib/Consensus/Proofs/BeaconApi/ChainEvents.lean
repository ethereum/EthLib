module

public import EthLib.Consensus.BeaconApi.ChainEvents
public import EthLib.Consensus.Proofs.BeaconApi.Duties
public import EthLib.Consensus.Proofs.ForkChoice.Network

/-!
# Proofs: the events of the fork choice

A head event names the head of the store after the change, with the status of its payload.

Its two dependent roots are those that the attester duties give for its epoch and the next one.

So a validator client can compare them to know when its duties change.

A finalized event comes exactly when the finalized checkpoint changes.

Each handler of the fork choice keeps the finalized checkpoint or moves it to a greater epoch.

When the stores are so related, the epoch of a finalized event is above the one before.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork}

/-- The root without a lag for an epoch is the root with a lag of one for the next epoch.

The next epoch must fit in 64 bits. -/
theorem dependentRoot_succ_of_ok {state : BeaconState preset fork} {epoch : Epoch}
    {genesisRoot root : Root} (room : epoch.toNat + 1 < 2 ^ 64)
    (read : dependentRoot state 0 epoch genesisRoot = .ok root) :
    dependentRoot state 1 (epoch + 1) genesisRoot = .ok root := by
  have next : (epoch + 1).toNat = epoch.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have back : epoch + 1 - (1 : Nat).toUInt64 = epoch := by simp
  have same : epoch - (0 : Nat).toUInt64 = epoch := by simp
  have lagged : ¬epoch.toNat + 1 < 1 := by omega
  unfold dependentRoot at read ⊢
  simp only [next, back, same, lagged, Nat.not_lt_zero, ite_false] at read ⊢
  rcases start : computeStartSlotAtEpoch preset epoch with _ | first <;>
    simp only [start, Except.mapError, bind, Except.bind, pure, Except.pure,
      reduceCtorEq] at read ⊢
  by_cases zero : first = 0
  · simp only [zero, ite_true] at read ⊢
    exact read
  · simp only [zero, ite_false] at read ⊢
    rcases found : getBlockRootAtSlot state (first - 1) with _ | value <;>
      simp only [found, reduceCtorEq] at read ⊢
    exact read

/-- A head event of a change of the fork choice is that of the head of the store after it. -/
private theorem chainEvents_head_event {config : Config} {optimistic : Root → Bool}
    {genesisRoot : Root} {before after : Store preset fork} {events : List ChainEvent}
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    {event : HeadEvent} (listed : .head event ∈ events) :
    ∃ head previous, after.getHead config = .ok head ∧
      headEvent after optimistic genesisRoot previous head = .ok event := by
  unfold chainEvents at made
  rcases h1 : before.getHead config with _ | oldHead <;>
    rcases h2 : after.getHead config with _ | newHead <;>
    simp [h1, h2, Except.mapError, bind, Except.bind, pure, Except.pure] at made
  refine ⟨newHead, ?_⟩
  simp only [true_and]
  repeat' split at made
  all_goals try (cases made; done)
  all_goals
    injection made with made
    subst made
    simp only [List.mem_cons, List.mem_nil_iff, ChainEvent.head.injEq, reduceCtorEq,
      or_false] at listed
    try (subst listed; exact ⟨_, by assumption⟩)

/-- A head event reads the head block, its state, and the two dependent roots of that state. -/
private theorem headEvent_spec {store : Store preset fork} {optimistic : Root → Bool}
    {genesisRoot : Root} {previous : Slot} {head : ForkChoiceNode} {event : HeadEvent}
    (made : headEvent store optimistic genesisRoot previous head = .ok event) :
    ∃ state, store.blockState head.root = .ok state ∧ event.block = head.root ∧
      event.payloadStatus = apiPayloadStatus fork head.payloadStatus ∧
      dependentRoot state 1 (computeEpochAtSlot preset event.slot) genesisRoot =
        .ok event.currentEpochDependentRoot ∧
      dependentRoot state 0 (computeEpochAtSlot preset event.slot) genesisRoot =
        .ok event.nextEpochDependentRoot := by
  unfold headEvent at made
  rcases h1 : store.block head.root with _ | block <;>
    rcases h2 : store.blockState head.root with _ | state <;>
    simp only [h1, h2, Except.mapError, bind, Except.bind, pure, Except.pure,
      reduceCtorEq] at made
  rcases h3 : dependentRoot state 1 (computeEpochAtSlot preset block.slot) genesisRoot
    with _ | current <;>
    rcases h4 : dependentRoot state 0 (computeEpochAtSlot preset block.slot) genesisRoot
      with _ | next <;>
    simp only [h3, h4, reduceCtorEq, Except.ok.injEq] at made
  subst made
  exact ⟨state, rfl, rfl, rfl, h3, h4⟩


/-- An answer of the attester duties carries the dependent root of its epoch. -/
private theorem dutiesResponse_attester {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root}
    {envelope : ApiEnvelope}
    (made : dutiesResponse config state .attester epoch indices genesisRoot = .ok envelope) :
    ∃ root, dependentRoot state 1 epoch genesisRoot = .ok root ∧
      envelope.dependentRoot = some root := by
  simp only [dutiesResponse, bind, Except.bind, pure, Except.pure] at made
  rcases duties : attesterDuties state epoch indices with _ | list <;>
    rcases root : dependentRoot state 1 epoch genesisRoot with _ | found <;>
    simp only [duties, root, reduceCtorEq, Except.ok.injEq] at made
  exact ⟨found, rfl, by rw [← made]⟩

/-- A head event names the head of the store after the change, and the status of its payload. -/
theorem chainEvents_head {config : Config} {optimistic : Root → Bool} {genesisRoot : Root}
    {before after : Store preset fork} {events : List ChainEvent}
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    {event : HeadEvent} (listed : .head event ∈ events) :
    ∃ head, after.getHead config = .ok head ∧ event.block = head.root ∧
      event.payloadStatus = apiPayloadStatus fork head.payloadStatus := by
  obtain ⟨head, previous, got, made⟩ := chainEvents_head_event made listed
  obtain ⟨-, -, block, status, -⟩ := headEvent_spec made
  exact ⟨head, got, block, status⟩

/-- A head event comes exactly when the head block changes, or its payload moves from empty to full.
-/
theorem chainEvents_head_iff {config : Config} {optimistic : Root → Bool} {genesisRoot : Root}
    {before after : Store preset fork} {events : List ChainEvent} {old new : ForkChoiceNode}
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    (oldHead : before.getHead config = .ok old) (newHead : after.getHead config = .ok new) :
    (∃ event, .head event ∈ events) ↔ headChanged old new = true := by
  unfold chainEvents at made
  simp only [oldHead, newHead, Except.mapError, bind, Except.bind, pure, Except.pure] at made
  rcases ancestor : after.isAncestor new ⟨old.root, .pending⟩ with _ | flag <;>
    simp only [ancestor] at made
  all_goals repeat' split at made
  all_goals try (cases made; done)
  all_goals
    injection made with made
    subst made
    simp_all

/-- A reorganization comes exactly when the head changes and leaves the old head block behind.

The old head block is then not an ancestor of the new head. -/
theorem chainEvents_reorg_iff {config : Config} {optimistic : Root → Bool} {genesisRoot : Root}
    {before after : Store preset fork} {events : List ChainEvent} {old new : ForkChoiceNode}
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    (oldHead : before.getHead config = .ok old) (newHead : after.getHead config = .ok new) :
    (∃ event, .chainReorg event ∈ events) ↔
      headChanged old new = true ∧ after.isAncestor new ⟨old.root, .pending⟩ = .ok false := by
  unfold chainEvents at made
  simp only [oldHead, newHead, Except.mapError, bind, Except.bind, pure, Except.pure] at made
  rcases ancestor : after.isAncestor new ⟨old.root, .pending⟩ with _ | flag <;>
    simp only [ancestor] at made
  all_goals repeat' split at made
  all_goals try (cases made; done)
  all_goals
    injection made with made
    subst made
    simp_all


/-- With at least two slots in an epoch, the epoch after that of any slot fits in 64 bits. -/
theorem computeEpochAtSlot_succ_lt (slot : Slot) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    (computeEpochAtSlot preset slot).toNat + 1 < 2 ^ 64 := by
  unfold computeEpochAtSlot
  rw [UInt64.toNat_div]
  have := slot.toNat_lt
  have : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat / 2 :=
    Nat.div_le_div_left twoSlots (by omega)
  omega

/-- The dependent roots of a head event are those of the attester duties, from the head state.

The first is that of the duties of the epoch of the head, and the second that of the next epoch.

The second needs the next epoch to fit in 64 bits, as it does with at least two slots in an epoch.
-/
theorem chainEvents_dependent_roots_duties {config : Config} {optimistic : Root → Bool}
    {genesisRoot : Root} {before after : Store preset fork} {events : List ChainEvent}
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    {event : HeadEvent} (listed : .head event ∈ events) :
    ∃ state, after.blockState event.block = .ok state ∧
      (∀ indices envelope, dutiesResponse config state .attester
          (computeEpochAtSlot preset event.slot) indices genesisRoot = .ok envelope →
        envelope.dependentRoot = some event.currentEpochDependentRoot) ∧
      ((computeEpochAtSlot preset event.slot).toNat + 1 < 2 ^ 64 →
        ∀ indices envelope, dutiesResponse config state .attester
          (computeEpochAtSlot preset event.slot + 1) indices genesisRoot = .ok envelope →
        envelope.dependentRoot = some event.nextEpochDependentRoot) := by
  obtain ⟨head, previous, -, made⟩ := chainEvents_head_event made listed
  obtain ⟨state, got, block, -, current, next⟩ := headEvent_spec made
  refine ⟨state, by rw [block]; exact got, ?_, ?_⟩
  · intro indices envelope answer
    obtain ⟨root, read, carried⟩ := dutiesResponse_attester answer
    rw [carried, Except.ok.inj (read.symm.trans current)]
  · intro room indices envelope answer
    obtain ⟨root, read, carried⟩ := dutiesResponse_attester answer
    rw [carried, Except.ok.inj (read.symm.trans (dependentRoot_succ_of_ok room next))]

/-- A finalized event comes exactly when the finalized checkpoint changes. -/
theorem chainEvents_finalized_iff {config : Config} {optimistic : Root → Bool}
    {genesisRoot : Root} {before after : Store preset fork} {events : List ChainEvent}
    (made : chainEvents config optimistic genesisRoot before after = .ok events) :
    (∃ event, .finalizedCheckpoint event ∈ events) ↔
      before.finalizedCheckpoint ≠ after.finalizedCheckpoint := by
  unfold chainEvents at made
  rcases h1 : before.getHead config with _ | old <;>
    rcases h2 : after.getHead config with _ | new <;>
    simp only [h1, h2, Except.mapError, bind, Except.bind, pure, Except.pure,
      reduceCtorEq] at made
  all_goals repeat' split at made
  all_goals try (cases made; done)
  all_goals
    injection made with made
    subst made
    simp_all

/-- A finalized event names the finalized checkpoint of the store after the change. -/
theorem chainEvents_finalized {config : Config} {optimistic : Root → Bool}
    {genesisRoot : Root} {before after : Store preset fork} {events : List ChainEvent}
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    {event : FinalizedCheckpointEvent} (listed : .finalizedCheckpoint event ∈ events) :
    event.block = after.finalizedCheckpoint.root ∧
      event.epoch = after.finalizedCheckpoint.epoch := by
  unfold chainEvents at made
  rcases h1 : before.getHead config with _ | old <;>
    rcases h2 : after.getHead config with _ | new <;>
    simp only [h1, h2, Except.mapError, bind, Except.bind, pure, Except.pure,
      reduceCtorEq] at made
  all_goals repeat' split at made
  all_goals try (cases made; done)
  all_goals
    injection made with made
    subst made
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, reduceCtorEq, or_false,
      false_or, ChainEvent.finalizedCheckpoint.injEq] at listed
  all_goals (subst listed; exact ⟨rfl, rfl⟩)

/-- A finalized event has an epoch above the finalized epoch before the change.

That holds when the finalized checkpoint advances from one store to the other.

Each handler of the fork choice makes it advance.
-/
theorem chainEvents_finalized_epoch {config : Config} {optimistic : Root → Bool}
    {genesisRoot : Root} {before after : Store preset fork} {events : List ChainEvent}
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    (advance : CheckpointAdvances before.finalizedCheckpoint after.finalizedCheckpoint)
    {event : FinalizedCheckpointEvent} (listed : .finalizedCheckpoint event ∈ events) :
    before.finalizedCheckpoint.epoch < event.epoch := by
  rw [(chainEvents_finalized made listed).2]
  exact advance.epoch_lt ((chainEvents_finalized_iff made).mp ⟨event, listed⟩)

/-- After one move of a store of the fork choice, a finalized event has a greater epoch. -/
theorem chainEvents_finalized_epoch_of_handles {config : Config} {optimistic : Root → Bool}
    {genesisRoot : Root} {checks : SignatureChecks} {sources : BlockSources preset fork}
    {time : ℕ} {view : Set (Models.Network.Message preset fork)}
    {before after : Store preset fork} {events : List ChainEvent}
    (step : Models.Network.Handles config checks sources time view before after)
    (made : chainEvents config optimistic genesisRoot before after = .ok events)
    {event : FinalizedCheckpointEvent} (listed : .finalizedCheckpoint event ∈ events) :
    before.finalizedCheckpoint.epoch < event.epoch :=
  chainEvents_finalized_epoch made step.checkpointsAdvance.2 listed

/-- The event of a run of the fast confirmation rule names the confirmed block and its slot. -/
theorem fastConfirmationEvent_block {store : Store preset fork} {fcr : FastConfirmationStore}
    {currentSlot : Slot} {event : FastConfirmationEvent}
    (made : fastConfirmationEvent store fcr currentSlot = .ok event) :
    ∃ block, store.block fcr.confirmedRoot = .ok block ∧
      event = ⟨fcr.confirmedRoot, block.slot, currentSlot⟩ := by
  unfold fastConfirmationEvent at made
  cases h : store.block fcr.confirmedRoot <;>
    simp [h, bind, Except.bind, pure, Except.pure] at made
  exact ⟨_, rfl, made.symm⟩

end EthLib.Consensus.BeaconApi
