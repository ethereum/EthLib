module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the answers of the Beacon API that read one field of a state

In a store that the handlers reach, each state that it keeps has the state root of its block.

So the root that the API reports for a state named by its root is that same root.

The genesis state from deposits has its three finality checkpoints at epoch 0 with the zero root.

From epoch 2, justification copies checkpoints or justifies an epoch after 0; other steps keep them.

So along a chain from that state, each checkpoint at epoch 0 keeps the zero root.

Such a state before finalization then reports epoch 0 and the zero root.

A justified checkpoint at epoch 0 is reported with the zero root too.

A field that a fork adds gives the error with code 400 exactly for a state before that fork.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- A store built from an anchor has an anchor state with the state root of the anchor block. -/
private theorem anchor_stateRoot
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    stateRoot anchorState = .ok anchorBlock.stateRoot := by
  cases hashed : SszType.hashTreeRoot anchorState with
  | error e => simp [getForkchoiceStore, hashed, bind, Except.bind, Except.mapError] at made
  | ok root =>
    by_cases same : anchorBlock.stateRoot = root
    · simp [stateRoot, hashed, same]
    · rw [getForkchoiceStore_mismatch hashed same] at made
      cases made

/-- In a reachable store, the anchor state has the state root of the anchor block. -/
private theorem reachable_anchor_stateRoot
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    stateRoot anchorState = .ok anchorBlock.stateRoot := by
  induction reachable with
  | anchor made => exact anchor_stateRoot made
  | _ => assumption

/-- In a reachable store, the state after a known block has the state root of the block. -/
theorem stateRoot_blockStates (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {state : BeaconState preset fork} {block : BeaconBlock preset fork}
    (stateFound : store.blockStates[root]? = some state)
    (blockFound : store.blocks[root]? = some block) :
    stateRoot state = .ok block.stateRoot := by
  obtain ⟨kept, keptFound, isAnchor, notAnchor⟩ := reachable.blockStatesFromParents blockFound
  rw [stateFound, Option.some.injEq] at keptFound
  subst keptFound
  by_cases same : block = anchorBlock
  · rw [isAnchor same, same]
    exact reachable_anchor_stateRoot reachable
  · obtain ⟨_, _, _, _, -, message, -, transition⟩ := notAnchor same
    obtain ⟨-, -, -, -, -, hashed⟩ := stateTransition_ok transition
    rw [message] at hashed
    exact hashed rfl

/-- In a reachable store, a state named by its root has that root. -/
theorem stateRoot_resolveStateId_root
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root blockRoot : Root} {state : BeaconState preset fork}
    (resolved : resolveStateId config store (.root root) = some (blockRoot, state)) :
    stateRoot state = .ok root := by
  simp only [resolveStateId, blockOfStateRoot, stateAfter, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at resolved
  obtain ⟨found, ⟨⟨key, block⟩, hfind, rfl⟩, stateFound, eq⟩ := resolved
  have mem := List.mem_of_find?_eq_some hfind
  have hroot := List.find?_some hfind
  simp only [Std.TreeMap.mem_toList_iff_getElem?_eq_some] at mem
  obtain ⟨hst, pair⟩ := eq
  simp only [Prod.mk.injEq] at pair
  obtain ⟨-, rfl⟩ := pair
  have := stateRoot_blockStates reachable hst mem
  have hr : block.stateRoot = root := of_decide_eq_true hroot
  rw [hr] at this
  exact this

/-- The genesis state from deposits has each finality checkpoint at epoch 0 with the zero root.

Only Phase 0 has a genesis state from deposits. -/
theorem finalityCheckpoints_genesis {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit} {state : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    finalityCheckpoints state =
      { previousJustified := ⟨0, Vector.replicate 32 0⟩
        currentJustified := ⟨0, Vector.replicate 32 0⟩
        finalized := ⟨0, Vector.replicate 32 0⟩ } := by
  obtain ⟨-, previous, current⟩ := initializeBeaconStateFromEth1_checkpoints computed
  obtain ⟨-, finalized⟩ := initializeBeaconStateFromEth1_finality computed
  simp only [finalityCheckpoints, previous, current, finalized]
  rfl

/-- Each of the three finality checkpoints of the state has the zero root when its epoch is 0. -/
def GenesisCheckpointsZero (state : BeaconState preset fork) : Prop :=
  ∀ checkpoint ∈ [state.previousJustifiedCheckpoint, state.currentJustifiedCheckpoint,
      state.finalizedCheckpoint],
    checkpoint.epoch = 0 → checkpoint.root = Vector.replicate 32 0

/-- A new state has the zero root at epoch 0 when an old state has it.

Each checkpoint of the new state must be one of the old state, or be after epoch 0. -/
private theorem GenesisCheckpointsZero.of_mem {post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (holds : GenesisCheckpointsZero state)
    (among : ∀ checkpoint ∈ [after.previousJustifiedCheckpoint, after.currentJustifiedCheckpoint,
        after.finalizedCheckpoint],
      checkpoint ∈ [state.previousJustifiedCheckpoint, state.currentJustifiedCheckpoint,
          state.finalizedCheckpoint] ∨ checkpoint.epoch ≠ 0) :
    GenesisCheckpointsZero after := fun checkpoint member zero =>
  (among checkpoint member).elim (fun old => holds checkpoint old zero) (absurd zero)

/-- A state with the three checkpoints of another state keeps the zero root at epoch 0. -/
private theorem GenesisCheckpointsZero.of_eq {post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (holds : GenesisCheckpointsZero state)
    (previous : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (current : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint)
    (finalized : after.finalizedCheckpoint = state.finalizedCheckpoint) :
    GenesisCheckpointsZero after :=
  holds.of_mem fun _ member => .inl (by rwa [previous, current, finalized] at member)

/-- Justification and finalization keep the zero root at epoch 0.

From the third epoch on, they may justify the previous or the current epoch, both after epoch 0.

Each other checkpoint that they write is one of the state before. -/
private theorem GenesisCheckpointsZero.of_processJustificationAndFinalization
    {state after : BeaconState preset fork} (holds : GenesisCheckpointsZero state)
    (computed : processJustificationAndFinalization state = .ok after) :
    GenesisCheckpointsZero after := by
  rcases processJustificationAndFinalization_reads computed with ⟨-, rfl⟩ |
    ⟨late, _, _, _, _, _, -, -, -, -, -, weighed⟩
  · exact holds
  obtain ⟨previous, current, finalized, -⟩ := weighJustificationAndFinalization_checkpoints weighed
  have lateNat : 1 < (getCurrentEpoch state).toNat := by
    simpa [GENESIS_EPOCH] using UInt64.lt_iff_toNat_lt.mp late
  have previousNat := getPreviousEpoch_toNat state
  refine holds.of_mem fun checkpoint member => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  rcases member with rfl | rfl | rfl
  · exact .inl (.inr (.inl previous))
  · rcases current with same | same | same
    · exact .inl (.inr (.inl same))
    · refine .inr fun zero => ?_
      rw [same] at zero
      rw [zero, UInt64.toNat_zero] at previousNat
      omega
    · refine .inr fun zero => ?_
      rw [same] at zero
      rw [zero, UInt64.toNat_zero] at lateNat
      omega
  · rcases finalized with same | same | same
    · exact .inl (.inr (.inr same))
    · exact .inl (.inl same)
    · exact .inl (.inr (.inl same))

/-- One slot keeps the zero root at epoch 0.

It caches the roots, may run the epoch transition, then moves the slot on. -/
private theorem GenesisCheckpointsZero.of_advanceSlot {state after : BeaconState preset fork}
    (holds : GenesisCheckpointsZero state)
    (computed : advanceSlot config checks state = .ok after) : GenesisCheckpointsZero after := by
  obtain ⟨_, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have frame := frame_processSlot cachedOk
  have cachedHolds := holds.of_eq frame.previousJustified frame.currentJustified frame.finalized
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, epochFrame⟩ := processEpoch_frame epochedOk
    exact (cachedHolds.of_processJustificationAndFinalization justifiedOk).of_eq
      epochFrame.previousJustified epochFrame.currentJustified epochFrame.finalized
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact cachedHolds

/-- One step of a chain keeps the zero root at epoch 0.

A slot keeps it, and the upgrades and the blocks copy the checkpoints. -/
private theorem GenesisCheckpointsZero.of_chainStep {forked after : ForkedBeaconState preset}
    (holds : GenesisCheckpointsZero forked.state) (step : ChainStep config checks forked after) :
    GenesisCheckpointsZero after.state := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    have advancedHolds : GenesisCheckpointsZero advanced := holds.of_advanceSlot advancedOk
    exact processUpgrades_induction (property := fun next => GenesisCheckpointsZero next.state)
      (fun kept stepOk =>
        have frame := upgradeFrame_upgradeNext stepOk
        GenesisCheckpointsZero.of_eq kept frame.previousJustified frame.currentJustified
          frame.finalized)
      (forked := ⟨forked.fork, advanced⟩) advancedHolds upgraded
  | block engine signed validateResult computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    have frame := frame_processBlock blockOk
    exact holds.of_eq frame.previousJustified frame.currentJustified frame.finalized

/-- Along a run of steps of a chain, each checkpoint at epoch 0 keeps the zero root.

It needs each checkpoint of the first state at epoch 0 to have the zero root. -/
theorem GenesisCheckpointsZero.of_chainSteps {first last : ForkedBeaconState preset}
    (holds : GenesisCheckpointsZero first.state)
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    GenesisCheckpointsZero last.state := by
  induction steps with
  | refl => exact holds
  | tail _ step more => exact more.of_chainStep step

/-- In the genesis state from deposits, each checkpoint at epoch 0 has the zero root. -/
theorem GenesisCheckpointsZero.of_initializeBeaconStateFromEth1 {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {state : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    GenesisCheckpointsZero state := by
  have reported := finalityCheckpoints_genesis computed
  simp only [finalityCheckpoints, FinalityCheckpoints.mk.injEq] at reported
  obtain ⟨previous, current, finalized⟩ := reported
  intro checkpoint member _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [previous]
  · rw [current]
  · rw [finalized]

/-- Along a chain from genesis, a state before finalization reports epoch 0 and the zero root.

The genesis state is the one that deposits build.

Before finalization, the finalized epoch of the state is still 0.

A justified checkpoint at epoch 0 is reported with the zero root too. -/
theorem finalityCheckpoints_of_genesis_chainSteps {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {genesis : BeaconState preset fork}
    {last : ForkedBeaconState preset}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok genesis)
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, genesis⟩ last) :
    (last.state.finalizedCheckpoint.epoch = 0 →
        (finalityCheckpoints last.state).finalized = ⟨0, Vector.replicate 32 0⟩) ∧
      (last.state.previousJustifiedCheckpoint.epoch = 0 →
        (finalityCheckpoints last.state).previousJustified = ⟨0, Vector.replicate 32 0⟩) ∧
      (last.state.currentJustifiedCheckpoint.epoch = 0 →
        (finalityCheckpoints last.state).currentJustified = ⟨0, Vector.replicate 32 0⟩) := by
  have start : GenesisCheckpointsZero (⟨fork, genesis⟩ : ForkedBeaconState preset).state :=
    GenesisCheckpointsZero.of_initializeBeaconStateFromEth1 computed
  have holds := start.of_chainSteps steps
  -- A checkpoint at epoch 0 with the zero root is the zero checkpoint.
  have zero : ∀ checkpoint ∈ [last.state.previousJustifiedCheckpoint,
      last.state.currentJustifiedCheckpoint, last.state.finalizedCheckpoint],
      checkpoint.epoch = 0 → checkpoint = ⟨0, Vector.replicate 32 0⟩ := by
    rintro ⟨epoch, root⟩ member early
    obtain rfl : epoch = 0 := early
    obtain rfl : root = Vector.replicate 32 0 := holds _ member rfl
    rfl
  exact ⟨zero _ (by simp), zero _ (by simp), zero _ (by simp)⟩

/-- A field that a fork adds is the error with code 400 exactly when the state is before it. -/
theorem sinceFork_error_iff {α : Type} {query : String} {first : Fork}
    (field : Since first fork α) :
    sinceFork query first field = .error (beforeFork query first) ↔ ¬first ≤ fork := by
  unfold sinceFork
  by_cases since : first ≤ fork <;> simp [since]

/-- A field that a fork adds is the field itself from that fork. -/
theorem sinceFork_ok {α : Type} {query : String} {first : Fork} (field : Since first fork α)
    (since : first ≤ fork) : sinceFork query first field = .ok (field since) := by
  simp [sinceFork, since]

/-- The pending deposits are the error with code 400 exactly when the state is before Electra. -/
theorem pendingDeposits_error_iff (state : BeaconState preset fork) :
    pendingDeposits state = .error (beforeFork "pending_deposits" .pectra) ↔
      ¬.pectra ≤ fork :=
  sinceFork_error_iff _

/-- The pending partial withdrawals are the error with code 400 exactly before Electra. -/
theorem pendingPartialWithdrawals_error_iff (state : BeaconState preset fork) :
    pendingPartialWithdrawals state =
        .error (beforeFork "pending_partial_withdrawals" .pectra) ↔
      ¬.pectra ≤ fork :=
  sinceFork_error_iff _

/-- The pending consolidations are the error with code 400 exactly before Electra. -/
theorem pendingConsolidations_error_iff (state : BeaconState preset fork) :
    pendingConsolidations state = .error (beforeFork "pending_consolidations" .pectra) ↔
      ¬.pectra ≤ fork :=
  sinceFork_error_iff _

/-- The proposer lookahead is the error with code 400 exactly when the state is before Fulu. -/
theorem proposerLookahead_error_iff (state : BeaconState preset fork) :
    proposerLookahead state = .error (beforeFork "proposer_lookahead" .fusaka) ↔
      ¬.fusaka ≤ fork :=
  sinceFork_error_iff _

/-- The pending payments of builders are the error with code 400 exactly before Gloas. -/
theorem builderPendingPayments_error_iff (state : BeaconState preset fork) :
    builderPendingPayments state = .error (beforeFork "builder_pending_payments" .glamsterdam) ↔
      ¬.glamsterdam ≤ fork :=
  sinceFork_error_iff _

/-- The pending withdrawals of builders are the error with code 400 exactly before Gloas. -/
theorem builderPendingWithdrawals_error_iff (state : BeaconState preset fork) :
    builderPendingWithdrawals state =
        .error (beforeFork "builder_pending_withdrawals" .glamsterdam) ↔
      ¬.glamsterdam ≤ fork :=
  sinceFork_error_iff _

end EthLib.Consensus.BeaconApi
