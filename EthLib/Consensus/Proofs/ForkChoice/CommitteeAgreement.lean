module

public import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins

/-!
# Proofs: the target state of a vote and the head state agree on the committees of its epoch

A vote passed the committee check in the state of its target.

The fast confirmation rule reads the committees of the slot of the vote in the state of the head.

Take a block that both the voted block and the head descend from.

When the vote is at most one epoch after that block, the two states agree on those committees.

They also agree on the count of committees per slot of the epoch of the vote.

The store must run every handler with one setting of the signature checks.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- A node that descends from a known pending node walks back to its root.

The walk stops at the slot of the block of that root. -/
private theorem Store.getAncestor_of_isAncestor {node : ForkChoiceNode} {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (descends : store.isAncestor node ⟨root, .pending⟩ = .ok true) :
    ∃ reached, store.getAncestor node block.slot = .ok reached ∧ reached.root = root := by
  simp only [Store.isAncestor, Store.block_ok_iff.mpr found, bind, Except.bind] at descends
  cases walk : store.getAncestor node block.slot with
  | error e => simp [walk] at descends
  | ok reached =>
    refine ⟨reached, rfl, ?_⟩
    rw [walk] at descends
    by_cases gloas : .glamsterdam ≤ fork <;> simp_all [pure, Except.pure]

/-- A walk from another payload status of the start reaches the same root. -/
private theorem Store.getAncestor_ok_of_status {node reached : ForkChoiceNode} {slot : Slot}
    (status : PayloadStatus) (walk : store.getAncestor node slot = .ok reached) :
    ∃ other, store.getAncestor ⟨node.root, status⟩ slot = .ok other ∧
      other.root = reached.root := by
  have same := Store.getAncestor_root (store := store) node status slot
  rw [walk] at same
  cases other : store.getAncestor ⟨node.root, status⟩ slot with
  | error e => simp [other, Functor.map, Except.map] at same
  | ok other' =>
    rw [other] at same
    simp only [Functor.map, Except.map, Except.ok.injEq] at same
    exact ⟨other', rfl, same.symm⟩

/-- A state at or after the start of the epoch of a slot is in that epoch or later. -/
private theorem epochAtSlot_le_of_start_le {slot start : Slot} {state : BeaconState preset fork}
    (startOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok start)
    (le : start ≤ state.slot) :
    (computeEpochAtSlot preset slot).toNat ≤ (getCurrentEpoch state).toNat := by
  obtain ⟨-, value⟩ := computeStartSlotAtEpoch_ok_iff.mp startOk
  rw [getCurrentEpoch_toNat]
  rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
  · rw [computeEpochAtSlot, UInt64.toNat_div, zero, Nat.div_zero]
    exact Nat.zero_le _
  · exact (Nat.le_div_iff_mul_le positive).mpr (value ▸ UInt64.le_iff_toNat_le.mp le)

/-- A state at the start of the epoch of a slot is in that epoch. -/
private theorem getCurrentEpoch_eq_of_start {slot start : Slot} {state : BeaconState preset fork}
    (startOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok start)
    (atStart : state.slot = start) :
    (getCurrentEpoch state).toNat = (computeEpochAtSlot preset slot).toNat := by
  obtain ⟨-, value⟩ := computeStartSlotAtEpoch_ok_iff.mp startOk
  rw [getCurrentEpoch_toNat, atStart, value]
  rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
  · rw [computeEpochAtSlot, UInt64.toNat_div, zero, Nat.div_zero, Nat.div_zero]
  · exact Nat.mul_div_cancel _ positive

/-- An epoch at most one after the current epoch is within the fixed epoch of activity. -/
private theorem le_activityFixedEpoch {state : BeaconState preset fork} {epoch : Epoch}
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (near : epoch.toNat ≤ (getCurrentEpoch state).toNat + 1) :
    epoch ≤ activityFixedEpoch state := by
  rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
  have := epoch.toNat_lt
  omega

/-- The target state of a vote and the state of the head agree on the committees of its epoch.

They also agree on the count of committees per slot of that epoch.

The voted node and the head descend from a known block.

The epoch of the vote is at most one after the epoch of that block.

The store is built with one setting of the checks, and the anchor block is not after its state.

Both lookaheads of the seed are at least one epoch.

The ring of mixes is longer than the minimum lookahead plus one epoch.

The head state must be before the mix that the seed of the epoch reads is written again. -/
theorem Store.ForwardReachableWith.committeesKept_of_voteOrigin {checks : SignatureChecks}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {root head : Root} {block : BeaconBlock preset fork} {voted : ForkChoiceNode}
    {validator : ValidatorIndex} {attestation : Attestation preset fork}
    {targetState headState : BeaconState preset fork}
    (found : store.blocks[root]? = some block)
    (headDescends : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (origin : store.VoteOrigin config validator attestation)
    (votedRoot : voted.root = attestation.data.beaconBlockRoot)
    (voteDescends : store.isAncestor voted ⟨root, .pending⟩ = .ok true)
    (near : (computeEpochAtSlot preset attestation.data.slot).toNat ≤
      (computeEpochAtSlot preset block.slot).toNat + 1)
    (targetFound : store.checkpointStates[attestation.data.target]? = some targetState)
    (headFound : store.blockStates[head]? = some headState)
    (headInRing : (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      (computeEpochAtSlot preset attestation.data.slot).toNat +
        preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    CommitteesKept (computeEpochAtSlot preset attestation.data.slot) targetState headState ∧
      getCommitteeCountPerSlot headState (computeEpochAtSlot preset attestation.data.slot) =
        getCommitteeCountPerSlot targetState (computeEpochAtSlot preset attestation.data.slot) := by
  have reachable := reached.reachable
  -- The target is the ancestor of the voted block at the start of the epoch of the vote.
  have targetWalk := origin.targetRoot
  simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
    Except.ok.injEq] at targetWalk
  obtain ⟨start, startOk, node, walk, rooted⟩ := targetWalk
  have startEpoch := startOk
  rw [origin.targetEpoch] at startEpoch
  -- The voted block and the head walk back to the block at its slot.
  obtain ⟨votedReach, votedWalk, votedRooted⟩ := Store.getAncestor_of_isAncestor found voteDescends
  obtain ⟨voteReach, voteWalk, voteRooted⟩ :=
    Store.getAncestor_ok_of_status .pending votedWalk
  rw [votedRoot] at voteWalk
  obtain ⟨headReach, headWalk, headRooted⟩ := Store.getAncestor_of_isAncestor found headDescends
  obtain ⟨headBlock, headBlockFound, headAbove⟩ := Store.slot_le_of_isAncestor found headDescends
  -- The target state is the state of the target block, perhaps processed to the start.
  obtain ⟨base, start', baseFound, startOk', fromBlock⟩ :=
    reached.checkpointStatesFromBlocks targetFound
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  have targetLe : start ≤ targetState.slot := by
    rcases fromBlock with ⟨baseLe, rfl⟩ | ⟨-, _, -, slotsOk⟩
    · exact baseLe
    · exact (processSlots_slot slotsOk).2 ▸ UInt64.le_refl _
  have targetEpochLe := epochAtSlot_le_of_start_le startEpoch targetLe
  by_cases low : block.slot ≤ start
  · -- The block is the ancestor of the target block at its slot: both states run from its state.
    rw [Store.getAncestor_trans low walk] at voteWalk
    rw [← rooted] at baseFound
    obtain ⟨targetBlock, targetBlockFound, targetBlockLe⟩ := Store.getAncestor_le walk
    obtain ⟨common, commonFound, -, -⟩ := reachable.blockStatesFromParents found
    have commonLe := reachable.slot_le_of_blockState anchorSlot found commonFound
    have blockEpochLe : (computeEpochAtSlot preset block.slot).toNat ≤
        (getCurrentEpoch common).toNat := by
      rw [getCurrentEpoch_toNat, computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp commonLe)
    have final : (computeEpochAtSlot preset attestation.data.slot).toNat ≤
        (getCurrentEpoch common).toNat + preset.MIN_SEED_LOOKAHEAD.toNat := by omega
    have fixed := le_activityFixedEpoch (state := common)
      (epoch := computeEpochAtSlot preset attestation.data.slot) maxLookahead (by omega)
    rw [← votedRooted, ← voteRooted] at commonFound
    have toTarget := reachable.runKept_of_getAncestor anchorSlot voteWalk baseFound commonFound
    rw [voteRooted, votedRooted, ← headRooted] at commonFound
    have toHead := reachable.runKept_of_getAncestor anchorSlot headWalk headFound commonFound
    rcases fromBlock with ⟨baseLe, rfl⟩ | ⟨-, _, -, slotsOk⟩
    · by_cases anchor : targetBlock = anchorBlock
      · -- The target block is the anchor, so it is the block, and the target state runs on.
        have anchorLe := reachable.anchorSlot_le anchorSlot found
        rw [Store.getAncestor_of_le targetBlockFound (anchor ▸ anchorLe), Except.ok.injEq]
          at voteWalk
        subst voteWalk
        rw [voteRooted, votedRooted, ← headRooted] at baseFound
        have run := reachable.runKept_of_getAncestor anchorSlot headWalk headFound baseFound
        exact run.committees_count (by omega) (le_activityFixedEpoch maxLookahead (by omega))
          headInRing
      · -- Otherwise the target state is at the slot of the target block, the start.
        obtain ⟨kept, keptFound, -, notAnchor⟩ := reachable.blockStatesFromParents targetBlockFound
        rw [baseFound, Option.some.injEq] at keptFound
        subst keptFound
        obtain ⟨_, _, _, _, -, message, -, transition⟩ := notAnchor anchor
        have atStart : targetState.slot = start := UInt64.le_antisymm
          ((stateTransition_slot transition).2 ▸ message ▸ targetBlockLe) baseLe
        have := getCurrentEpoch_eq_of_start startEpoch atStart
        exact toTarget.committees_agree toHead final fixed (by omega) headInRing
    · have := getCurrentEpoch_eq_of_start startEpoch (processSlots_slot slotsOk).2
      exact (toTarget.trans (runKept_processSlots slotsOk)).committees_agree toHead final fixed
        (by omega) headInRing
  · -- The target block is the ancestor of the head at the start, so the target state runs on.
    have above := UInt64.not_le.mp low
    have voteTrans := Store.getAncestor_trans (UInt64.le_of_lt above) voteWalk
    rw [walk] at voteTrans
    obtain ⟨reach, reachWalk, reachRooted⟩ :=
      Store.getAncestor_ok_of_status headReach.payloadStatus voteTrans.symm
    have sameNode : (⟨voteReach.root, headReach.payloadStatus⟩ : ForkChoiceNode) = headReach := by
      rw [voteRooted, votedRooted, ← headRooted]
    rw [sameNode] at reachWalk
    have checkpoint : store.getCheckpointBlock head attestation.data.target.epoch =
        .ok attestation.data.target.root := by
      simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq]
      exact ⟨start, startOk, reach,
        (Store.getAncestor_trans (UInt64.le_of_lt above) headWalk).trans reachWalk,
        reachRooted.trans rooted⟩
    have run := reached.runKept_of_checkpointState anchorSlot checkpoint headBlockFound startOk
      (UInt64.le_trans (UInt64.le_of_lt above) headAbove) targetFound headFound
    exact run.committees_count (by omega) (le_activityFixedEpoch maxLookahead (by omega))
      headInRing

end EthLib.Consensus
