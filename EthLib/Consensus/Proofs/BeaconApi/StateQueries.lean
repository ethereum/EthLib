module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the answers of the Beacon API that read one field of a state

In a store that the handlers reach, each state that it keeps has the state root of its block.

So the root that the API reports for a state named by its root is that same root.

The genesis state from deposits has its three finality checkpoints at epoch 0 with the zero root.

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
