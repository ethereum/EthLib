module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
import EthLib.Consensus.Proofs.ForkChoice.CommitteeAgreement
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes

/-!
# Proofs: the target count of the rule from the votes of the store

The rule counts the honest votes that the target of the current epoch will get, at the least.

It takes the votes so far for the target, less the adversary.

It adds the honest share of the slots still to come.

The first lemma reads the votes so far as the stake of a list of voters.

The second reads the count as those votes less the adversary, plus the honest share.

A signed vote shows that its voter signed the target.

A voter for the target of the head is in the committees that the rule reads.

This holds when the block of the target is near, or when the head is in the current epoch.

The theorem derives the honest count `HonestTargetVotes` from a bound on the Byzantine stake.

The bound is on the committees of the epoch so far.

The honest stake of the slots still to come is bounded below.

A head with an old block needs the premise `StaleHeadVotersInWindow`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The target score is a sum of balances over the successful latest-target tests. -/
private theorem getCurrentTargetScore_eq_sum
    {head : Root} {state : BeaconState preset fork} {target : Checkpoint} {score : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (targetOk : store.getCurrentTarget config head = .ok target)
    (scoreOk : store.getCurrentTargetScore config head = .ok score) :
    ∃ counted : List ValidatorIndex,
      (getActiveValidatorIndices state (getCurrentEpoch state)).filterM
        (fun index => return !(← validatorAt state index).slashed) =
          (Except.ok counted : Except ForkChoiceError (List ValidatorIndex)) ∧
      score.toNat = (counted.map fun index =>
        match store.latestMessages[index]? with
        | none => 0
        | some message =>
          if index ∈ store.equivocatingIndices then 0
          else if (store.getCheckpointForBlock message.root
            (getLatestMessageEpoch preset message)).toOption = some target
          then balanceAt state index.toNat else 0).sum := by
  simp only [getCurrentTargetScore, targetOk, stateOk, bind_ok_iff] at scoreOk
  obtain ⟨t, tOk, s, sOk, counted, countedOk, summed⟩ := scoreOk
  cases Except.ok.inj tOk
  cases Except.ok.inj sOk
  refine ⟨counted, countedOk, toNat_eq_of_sumGwei summed ?_⟩
  intro index member computed valueOk
  cases latest : store.latestMessages[index]? with
  | none =>
    have zero : computed = 0 := by simpa [latest, pure, Except.pure] using valueOk.symm
    simp [zero]
  | some message =>
    by_cases equivocating : index ∈ store.equivocatingIndices
    · have zero : computed = 0 := by
        simpa [latest, equivocating, pure, Except.pure] using valueOk.symm
      simp [equivocating, zero]
    · simp only [latest, equivocating, ite_false, bind_ok_iff] at valueOk
      obtain ⟨checkpoint, checkpointOk, valueOk⟩ := valueOk
      by_cases same : target = checkpoint
      · subst checkpoint
        simp only [ite_true] at valueOk
        simpa [latest, equivocating, checkpointOk, Except.toOption] using
          toNat_eq_balanceAt_of_effectiveBalance valueOk
      · have zero : computed = 0 := by simpa [same, pure, Except.pure] using valueOk.symm
        simp [equivocating, checkpointOk, Ne.symm same, zero, Except.toOption]

/-- A successful total-balance read makes the target score a finite stake, without duplicates. -/
private theorem getCurrentTargetScore_eq_stake
    {head : Root} {state : BeaconState preset fork} {target : Checkpoint} {score total : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (targetOk : store.getCurrentTarget config head = .ok target)
    (totalOk : getTotalActiveBalance state = .ok total)
    (scoreOk : store.getCurrentTargetScore config head = .ok score) :
    ∃ counted : List ValidatorIndex,
      (getActiveValidatorIndices state (getCurrentEpoch state)).filterM
        (fun index => return !(← validatorAt state index).slashed) =
          (Except.ok counted : Except ForkChoiceError (List ValidatorIndex)) ∧
      counted.Nodup ∧
      score.toNat = stake (fun v => balanceAt state v.toNat)
        (counted.toFinset.filter fun index => (match store.latestMessages[index]? with
          | none => false
          | some message => decide (index ∉ store.equivocatingIndices ∧
            (store.getCheckpointForBlock message.root
              (getLatestMessageEpoch preset message)).toOption = some target)) = true) := by
  obtain ⟨counted, countedOk, summed⟩ := getCurrentTargetScore_eq_sum stateOk targetOk scoreOk
  simp only [getTotalActiveBalance, bind_ok_iff] at totalOk
  obtain ⟨active, activeOk, _⟩ := totalOk
  -- The active indices are sorted, so without duplicates, and a filter keeps that.
  have distinct : (getActiveValidatorIndices state (getCurrentEpoch state)).Nodup := by
    have sorted := sorted_of_getActiveValidatorIndicesChecked_ok activeOk
    rw [getActiveValidatorIndicesChecked_ok activeOk] at sorted
    exact sorted.imp UInt64.ne_of_lt
  have keptDistinct := (sublist_of_filterM_ok countedOk).nodup distinct
  refine ⟨counted, countedOk, keptDistinct, ?_⟩
  rw [stake, Finset.sum_filter, List.sum_toFinset _ keptDistinct, summed]
  congr 1
  apply List.map_congr_left
  intro index _
  cases store.latestMessages[index]? with
  | none => simp
  | some message =>
    by_cases equiv : index ∈ store.equivocatingIndices <;> simp [equiv]

/-- A successful target-support count is the discounted score plus the remaining honest share.

The count reads the total balance, and the weight of the committees so far, as it does so.
-/
private theorem computeHonestFfgSupportForCurrentTarget_eq
    {head : Root} {state : BeaconState preset fork} {slot : Slot} {support : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (slotOk : store.getCurrentSlot config = .ok slot)
    (supportOk : store.computeHonestFfgSupportForCurrentTarget config head = .ok support) :
    ∃ total soFar epochStart lastSlot score adversary,
      getTotalActiveBalance state = .ok total ∧
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart ∧
      subChecked slot 1 = .ok lastSlot ∧
      store.computeCommitteeWeightBetweenSlots head state epochStart lastSlot = .ok soFar ∧
      store.getCurrentTargetScore config head = .ok score ∧
      store.computeAdversarialWeight config head state epochStart lastSlot = .ok adversary ∧
      support.toNat = score.toNat - adversary.toNat +
        (total.toNat - soFar.toNat) / 100 *
          (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by
  simp only [computeHonestFfgSupportForCurrentTarget, slotOk, stateOk,
    mapError_ok_iff, bind_ok_iff] at supportOk
  obtain ⟨s, sOk, st, stOk, t, tOk, score, scoreOk, first, firstOk, last, lastOk',
    weight, weightOk, remaining, remainingOk, share, shareOk, future, futureOk,
    adversary, adversaryOk, sumOk⟩ := supportOk
  cases Except.ok.inj sOk
  cases Except.ok.inj stOk
  have remainingNat := (subChecked_ok_iff.mp remainingOk).2
  have shareNat := (subChecked_ok_iff.mp shareOk).2
  have futureNat := (mulChecked_ok_iff.mp futureOk).2
  have sumNat := (addChecked_ok_iff.mp sumOk).2
  refine ⟨t, weight, first, last, score, adversary, tOk, firstOk, lastOk', weightOk, scoreOk,
    adversaryOk, ?_⟩
  simpa only [toNat_saturatingSub, futureNat, UInt64.toNat_div, remainingNat, shareNat,
    UInt64.toNat_ofNat] using sumNat

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A voter for the target of the current epoch is in the committees that the rule reads.

This is the premise for a head with an old block.

The block of such a head is before the start of the current epoch.

It is also at least two epochs before the current epoch.

The rule reads the committees of the current epoch from the state of the head.

That state has not processed the epochs in between.

An assumption on the run: the committees that this state gives still hold the voter.

It buys the honest target count for such a head; for any other head the fact is proved.

Limitation: runs where those committees miss a voter for the head's target are not covered.

A rule that read these committees from the pulled-up state of the head would not need it.
-/
def StaleHeadVotersInWindow (last : ℕ) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
    ∀ (head : ForkChoiceNode) (headBlock : BeaconBlock preset fork)
      (slot first lastSlot : Slot) (participants : Std.TreeSet ValidatorIndex)
      (v : ValidatorIndex) (attestation : Attestation preset fork),
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).blocks[head.root]? = some headBlock →
    ((e.world k).state w).getCurrentSlot config = .ok slot →
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first →
    headBlock.slot < first →
    (computeEpochAtSlot preset headBlock.slot).toNat + 1 <
      (computeEpochAtSlot preset slot).toNat →
    subChecked slot 1 = .ok lastSlot →
    ((e.world k).state w).getCommitteesBetweenSlots head.root first lastSlot = .ok participants →
    ((e.world k).state w).getCurrentTarget config head.root = .ok attestation.data.target →
    ((e.world k).state w).VoteOrigin config v attestation →
    v ∈ participants

/-- The Byzantine stake that the count of a call assumes, for the reads of one head at one event.

The state is the pulled-up state of the head.

The Byzantine validators hold at most the threshold share of the stake of the active members.

Those members are in the committees of the epoch so far.

This is Assumption 2 of the paper.

The honest validators of the slots still to come hold what the rule counts for them.

They hold a third of the margin on top of it.

An assumption on the run: the rule checks neither bound.

It buys the honest target count of a call, `HonestTargetVotes`.

Limitation: runs whose adversary holds more than the threshold share so far are not covered.

Nor are runs whose honest validators of the slots to come hold less than the rule counts.
-/
def TargetCountBounds [DecidablePred (· ∈ J)] (margin : ℕ) (u : ValidatorIndex) (n : ℕ)
    (head : Root) : Prop :=
  ∀ (state : BeaconState preset fork) (total soFar : Gwei) (slot epochStart lastSlot : Slot)
    (participants : Std.TreeSet ValidatorIndex),
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
    subChecked slot 1 = .ok lastSlot →
    ((e.world n).state u).computeCommitteeWeightBetweenSlots head state epochStart lastSlot =
      .ok soFar →
    ((e.world n).state u).getCommitteesBetweenSlots head epochStart lastSlot = .ok participants →
    ByzantineStakeAtMost (fun v => balanceAt state v.toNat)
      (Store.activeMembers state participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100 ∧
    3 * ((total.toNat - soFar.toNat) / 100 *
        (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat)) + margin ≤
      3 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∉ participants ∧ v ∈ J}

/-- A latest vote's checkpoint target has been signed by the event that holds the vote.

The vote comes from an attestation with that target, which has an origin in the store.
-/
private theorem Execution.exists_attestation_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {n : ℕ} {v : ValidatorIndex} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message)
    {target : Checkpoint}
    (targetOk : ((e.world n).state u).getCheckpointForBlock message.root
      (getLatestMessageEpoch preset message) = .ok target) :
    ∃ attestation : Attestation preset fork, attestation.data.target = target ∧
      ((e.world n).state u).VoteOrigin config v attestation ∧
      SignsTarget e v target (e.world n).time := by
  obtain ⟨attestation, m, seen, same, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start caller found
  have epoch : getLatestMessageEpoch preset message = attestation.data.target.epoch := by
    rw [same]
    unfold getLatestMessageEpoch LatestMessage.ofAttestation
    split
    · exact origin.targetEpoch.symm
    · rfl
  have root : message.root = attestation.data.beaconBlockRoot := by rw [same]; rfl
  rw [epoch, root] at targetOk
  have targetEq : attestation.data.target = target := by
    simpa [Store.getCheckpointForBlock, origin.targetRoot] using targetOk
  exact ⟨attestation, targetEq, origin,
    n, le_rfl, m, e.view_subset_sent n u seen, attestation.data, signed, targetEq⟩

/-- A voter for the target of the head is in the committees that the rule reads.

The target is the one of the current epoch, in the chain of the head.

The rule reads the committees of the current epoch so far, in the state of the head.

The target state and the state of the head must agree on the committees of the epoch of the vote.

That holds in two cases.

The block of the target is at most one epoch before the current epoch.

Then the vote and the head descend from that block, so the store's committee agreement applies.

Or the block of the head is in the current epoch.

Then the state of the target checkpoint runs on to the state of the head.

The head state must be before the mix that the seed of the epoch reads is written again.
-/
private theorem Execution.mem_window_of_target {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (preGloas : fork < .glamsterdam)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} {head : ForkChoiceNode}
    {slot first lastSlot : Slot} {participants : Std.TreeSet ValidatorIndex}
    {v : ValidatorIndex} {attestation : Attestation preset fork}
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first lastSlot =
      .ok participants)
    (targetOk : ((e.world k).state w).getCurrentTarget config head.root =
      .ok attestation.data.target)
    (origin : ((e.world k).state w).VoteOrigin config v attestation)
    (inReach : (∀ rootBlock : BeaconBlock preset fork,
      ((e.world k).state w).blocks[attestation.data.target.root]? = some rootBlock →
      (computeEpochAtSlot preset slot).toNat ≤
        (computeEpochAtSlot preset rootBlock.slot).toNat + 1) ∨
      ∀ headBlock : BeaconBlock preset fork,
        ((e.world k).state w).blocks[head.root]? = some headBlock → first ≤ headBlock.slot) :
    v ∈ participants := by
  have reached := e.forwardReachableWith
    (fun u member => (start u member) ▸ Store.ForwardReachableWith.anchor anchored) k w honest
  -- The target is the current one, so its epoch is the epoch of the slot.
  obtain ⟨epoch, targetRoot, -, headTarget, targetEq⟩ :=
    Store.getCurrentTarget_eq_ok_iff.mp targetOk
  have epochRead : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have targetEpoch := Store.epoch_eq_of_getCurrentTarget epochRead targetOk
  have rootEq : attestation.data.target.root = targetRoot := congrArg Checkpoint.root targetEq
  obtain ⟨_, rootBlock, _, rootFound, _, headDescends⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas headTarget
  have voteTarget := origin.targetRoot
  rw [rootEq] at voteTarget
  obtain ⟨_, _, _, _, _, voteDescends⟩ := Store.isAncestor_of_getCheckpointBlock preGloas voteTarget
  rw [← rootEq] at rootFound headDescends voteDescends
  -- The head has a state, at or before the current slot.
  obtain ⟨headBlock, headBlockFound, -⟩ := Store.slot_le_of_isAncestor rootFound headDescends
  obtain ⟨headState, headFound, -, -⟩ := reached.reachable.blockStatesFromParents headBlockFound
  have headLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot headFound slotOk
  have headCurrent :
      (getCurrentEpoch headState).toNat ≤ (computeEpochAtSlot preset slot).toNat := by
    rw [getCurrentEpoch_toNat]
    exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp headLe)
  have voteEpoch :
      computeEpochAtSlot preset attestation.data.slot = computeEpochAtSlot preset slot :=
    origin.targetEpoch.symm.trans targetEpoch
  -- The target state and the state of the head agree on the committees of the vote.
  obtain ⟨targetState, index, committee, targetFound, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  have agree : CommitteesKept (computeEpochAtSlot preset attestation.data.slot) targetState
        headState ∧
      getCommitteeCountPerSlot headState (computeEpochAtSlot preset attestation.data.slot) =
        getCommitteeCountPerSlot targetState (computeEpochAtSlot preset attestation.data.slot) := by
    rcases inReach with near | atOrAfter
    · exact reached.committeesKept_of_voteOrigin anchorSlot minLookahead maxLookahead (by omega)
        rootFound headDescends origin rfl voteDescends
        (by rw [voteEpoch]; exact near rootBlock rootFound) targetFound headFound
        (by rw [voteEpoch]; omega)
    · -- The state of the target checkpoint runs on to the state of the head.
      have startOk : computeStartSlotAtEpoch preset attestation.data.target.epoch = .ok first := by
        rw [targetEpoch]
        exact firstOk
      have checkpoint : ((e.world k).state w).getCheckpointBlock head.root
          attestation.data.target.epoch = .ok attestation.data.target.root := by
        rw [targetEq]
        exact headTarget
      have run := reached.runKept_of_checkpointState anchorSlot checkpoint headBlockFound startOk
        (atOrAfter headBlock headBlockFound) targetFound headFound
      -- The target state is in the epoch of the vote or a later one.
      have targetEpochLe := reached.epoch_le_of_checkpointState targetFound origin.targetEpoch
      exact run.committees_count (by omega) (le_activityFixedEpoch maxLookahead (by omega))
        (by rw [voteEpoch]; omega)
  obtain ⟨kept, count⟩ := agree
  -- The slot of the vote is in the range that the rule reads.
  have low : first ≤ attestation.data.slot := by
    have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
    have divLe := Nat.div_mul_le_self attestation.data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    change (computeEpochAtSlot preset attestation.data.slot).toNat *
      preset.SLOTS_PER_EPOCH.toNat ≤ attestation.data.slot.toNat at divLe
    rw [voteEpoch] at divLe
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have high : attestation.data.slot ≤ lastSlot := by
    obtain ⟨current, currentOk, past⟩ := origin.past
    have currentEq := Except.ok.inj (currentOk.symm.trans slotOk)
    subst current
    have lastNat := (subChecked_ok_iff.mp lastOk).2
    have pastNat := UInt64.lt_iff_toNat_lt.mp past
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_one] at lastNat
    omega
  exact Store.mem_getCommitteesBetweenSlots windowOk low high
    (Store.blockState_ok_iff.mpr headFound) (count ▸ below)
    ((kept _ _ rfl).trans committeeOk) member

/-- A voter for the target of the head is in the committees that the rule reads.

The head is stale when its block is at least two epochs before the current epoch.

Then the premise on stale heads gives the membership.

For a head with a block in the current epoch, or a block at most one epoch back, it is proved.
-/
private theorem Execution.mem_window_of_target_or_stale {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (preGloas : fork < .glamsterdam)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {limit : ℕ} (stale : StaleHeadVotersInWindow (e := e) limit)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {head : ForkChoiceNode} {slot first lastSlot : Slot}
    {participants : Std.TreeSet ValidatorIndex} {v : ValidatorIndex}
    {attestation : Attestation preset fork}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first lastSlot =
      .ok participants)
    (targetOk : ((e.world k).state w).getCurrentTarget config head.root =
      .ok attestation.data.target)
    (origin : ((e.world k).state w).VoteOrigin config v attestation) :
    v ∈ participants := by
  by_cases atOrAfter : ∀ headBlock : BeaconBlock preset fork,
      ((e.world k).state w).blocks[head.root]? = some headBlock → first ≤ headBlock.slot
  · exact Execution.mem_window_of_target anchored start anchorSlot preGloas minLookahead
      maxLookahead ring honest slotOk firstOk lastOk windowOk targetOk origin (.inr atOrAfter)
  -- The block of the head is before the start of the epoch, so it is the block of the target.
  obtain ⟨headBlock, headFound, below⟩ : ∃ headBlock : BeaconBlock preset fork,
      ((e.world k).state w).blocks[head.root]? = some headBlock ∧ headBlock.slot < first := by
    simp only [not_forall] at atOrAfter
    obtain ⟨headBlock, found, not_le⟩ := atOrAfter
    exact ⟨headBlock, found, UInt64.not_le.mp not_le⟩
  obtain ⟨epoch, targetRoot, epochOk, headTarget, targetEq⟩ :=
    Store.getCurrentTarget_eq_ok_iff.mp targetOk
  have epochEq : epoch = computeEpochAtSlot preset slot :=
    Store.getCurrentStoreEpoch_eq slotOk epochOk
  have rootIsHead : attestation.data.target.root = head.root := by
    rw [targetEq]
    simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at headTarget
    obtain ⟨boundary, boundaryOk, ancestor, walk, rooted⟩ := headTarget
    rw [epochEq, firstOk, Except.ok.injEq] at boundaryOk
    subst boundaryOk
    rw [Store.getAncestor_of_le (node := ⟨head.root, .pending⟩) headFound (UInt64.le_of_lt below),
      Except.ok.injEq] at walk
    subst walk
    exact rooted.symm
  by_cases near : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset headBlock.slot).toNat + 1
  · refine Execution.mem_window_of_target anchored start anchorSlot preGloas minLookahead
      maxLookahead ring honest slotOk firstOk lastOk windowOk targetOk origin (.inl ?_)
    intro rootBlock found
    rw [rootIsHead, headFound, Option.some.injEq] at found
    subst found
    exact near
  · exact stale w honest k bounded head headBlock slot first lastSlot participants v attestation
      headOk headFound slotOk firstOk below (by omega) lastOk windowOk targetOk origin

/-- Honest validators hold the count that the rule makes for the target, with a margin.

The Byzantine validators hold at most the threshold share of the committees of the epoch so far.

The honest validators of the slots still to come hold the share that the rule counts for them.

They hold a third of the margin on top of it.

The stake is read in the pulled-up state of the head.

The anchor's invariant and the preset's aligned maximum balances give that state aligned balances.

The second is a preset fact, proved for mainnet and minimal.

Heads with a block at least two epochs before the current epoch have the premise on stale heads. -/
theorem Execution.honestTargetVotes_of_byzantineStakeAtMost [DecidablePred (· ∈ J)]
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (sound : Invariant anchorState) (maxAligned : MaxEffectiveBalancesAligned preset)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {limit : ℕ} (stale : StaleHeadVotersInWindow (e := e) limit)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    {margin : ℕ} {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (bounded : (e.world n).time ≤ limit)
    {head : Root}
    (headOk : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (bounds : TargetCountBounds (e := e) margin u n head) :
    HonestTargetVotes e margin u n head := by
  classical
  intro state support target slot epochStart lastSlot participants stateOk supportOk targetOk
    slotOk startOk lastOk participantsOk
  obtain ⟨node, headRead, rfl⟩ := headOk
  obtain ⟨total, soFar, epochStart', lastSlot', score, adversary, totalOk, startOk', lastOk',
    soFarOk, scoreOk, adversaryOk, supportEq⟩ :=
    Store.computeHonestFfgSupportForCurrentTarget_eq stateOk slotOk supportOk
  obtain rfl := Except.ok.inj (startOk'.symm.trans startOk)
  obtain rfl := Except.ok.inj (lastOk'.symm.trans lastOk)
  obtain ⟨byzantine, remaining⟩ := bounds state total soFar slot epochStart' lastSlot'
    participants stateOk totalOk slotOk startOk lastOk soFarOk participantsOk
  have aligned := (e.reachable (fun w honest => (start w honest) ▸ Store.Reachable.anchor anchored)
    n u caller).getPulledUpHeadState_aligned sound maxAligned stateOk
  have dishonest : ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J :=
    e.equivocatingIndices_honest slots (fun w honest v member => by
      rw [start w honest, Store.getForkchoiceStore_equivocatingIndices anchored] at member
      simp at member) n caller
  obtain ⟨counted, countedOk, _, scoreEq⟩ :=
    Store.getCurrentTargetScore_eq_stake stateOk targetOk totalOk scoreOk
  let scored := counted.toFinset.filter fun index => (match
      ((e.world n).state u).latestMessages[index]? with
    | none => false
    | some message => decide (index ∉ ((e.world n).state u).equivocatingIndices ∧
        (((e.world n).state u).getCheckpointForBlock message.root
          (getLatestMessageEpoch preset message)).toOption = some target)) = true
  let outside := {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset |
    v ∉ participants ∧ v ∈ J}
  let honest := scored.filter (· ∈ J)
  have totalRead := totalOk
  simp only [getTotalActiveBalance, bind_ok_iff] at totalRead
  obtain ⟨active, activeOk, _⟩ := totalRead
  have activeEq := getActiveValidatorIndicesChecked_ok activeOk
  have countedActive : ∀ v ∈ counted,
      v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset := by
    intro v member
    exact List.mem_toFinset.mpr (mem_of_filterM_ok countedOk member)
  have countedFound : ∀ v ∈ counted, ∃ validator,
      state.validators.data[v.toNat]? = some validator ∧
      isActiveValidator validator (getCurrentEpoch state) = true := by
    intro v member
    apply (mem_iff_of_getActiveValidatorIndicesChecked_ok activeOk).mp
    rw [activeEq]
    exact mem_of_filterM_ok countedOk member
  have scoredMessage : ∀ v ∈ scored, ∃ message,
      ((e.world n).state u).latestMessages[v]? = some message ∧
      v ∉ ((e.world n).state u).equivocatingIndices ∧
      ((e.world n).state u).getCheckpointForBlock message.root
        (getLatestMessageEpoch preset message) = .ok target := by
    intro v member
    have test := (Finset.mem_filter.mp member).2
    cases found : ((e.world n).state u).latestMessages[v]? with
    | none => simp [found] at test
    | some message =>
      simp only [found, decide_eq_true_eq] at test
      refine ⟨message, rfl, test.1, ?_⟩
      cases read : ((e.world n).state u).getCheckpointForBlock message.root
          (getLatestMessageEpoch preset message) with
      | error error => simp [read, Except.toOption] at test
      | ok checkpoint =>
        have eq : checkpoint = target := by simpa [read, Except.toOption] using test.2
        exact congrArg Except.ok eq
  -- Each scored voter is in the committees that the rule reads, since it voted for the target.
  have scoredIn : scored ⊆ Store.activeMembers state participants := by
    intro v member
    obtain ⟨message, latest, _, checkpointOk⟩ := scoredMessage v member
    obtain ⟨attestation, targetEq, origin, _⟩ :=
      Execution.exists_attestation_of_latestMessages anchored start caller latest checkpointOk
    have currentTarget : ((e.world n).state u).getCurrentTarget config node.root =
        .ok attestation.data.target := by
      rw [targetEq]
      exact targetOk
    exact Store.mem_activeMembers.mpr
      ⟨Execution.mem_window_of_target_or_stale anchored start anchorSlot preGloas minLookahead
        maxLookahead ring stale caller bounded headRead slotOk startOk lastOk participantsOk
        currentTarget origin,
        countedFound v (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)⟩
  -- The Byzantine cap covers counted Byzantine voters and the disjoint known equivocators.
  obtain ⟨weight, equivocation, weightOk, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok adversaryOk
  obtain ⟨readMembers, readMembersOk, equivocationEq⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have readMembersEq := Except.ok.inj
    (readMembersOk.symm.trans participantsOk)
  subst readMembers
  have cap := Store.threshold_mul_stake_le_of_computeAdversarialWeight weightOk equivocationOk
    adversaryOk (Store.stake_le_computeCommitteeWeightBetweenSlots participantsOk weightOk
      fun _ member => Store.mem_activeMembers.mp member)
      (fun _ _ => Nat.mod_eq_zero_of_dvd
        (dvd_balanceAt_of_aligned aligned (Nat.dvd_of_mod_eq_zero increment) _))
  have badIn : scored.filter (· ∉ J) ∪ ((e.world n).state u).equivocatorsOf state participants ⊆
      (Store.activeMembers state participants).filter (· ∉ J) := by
    intro v member
    rcases Finset.mem_union.mp member with member | member
    · exact Finset.mem_filter.mpr ⟨scoredIn (Finset.mem_filter.mp member).1,
        (Finset.mem_filter.mp member).2⟩
    · have parts := Finset.mem_filter.mp member
      exact Finset.mem_filter.mpr ⟨parts.1, dishonest v parts.2⟩
  have apart : Disjoint (scored.filter (· ∉ J))
      (((e.world n).state u).equivocatorsOf state participants) := by
    apply Finset.disjoint_left.mpr
    intro v member equiv
    exact (scoredMessage v (Finset.mem_filter.mp member).1).choose_spec.2.1
      (Finset.mem_filter.mp equiv).2
  have badBound := stake_mono (w := fun v => balanceAt state v.toNat) badIn
  rw [stake, Finset.sum_union apart, ← stake, ← stake, equivocationEq] at badBound
  have badLe : stake (fun v => balanceAt state v.toNat) (scored.filter (· ∉ J)) ≤
      adversary.toNat := by
    have byzantineBound := byzantine.2
    nlinarith
  have splitStake : stake (fun v => balanceAt state v.toNat) honest +
      stake (fun v => balanceAt state v.toNat) (scored.filter (· ∉ J)) =
      stake (fun v => balanceAt state v.toNat) scored :=
    Finset.sum_filter_add_sum_filter_not scored (· ∈ J) _
  have outsideActive : ∀ v ∈ outside,
      v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset := by
    intro v member
    obtain ⟨validator, found, active, -⟩ :=
      (mem_unslashedActiveBalances_iff (BeaconState.registryWithinLimit_of_lt preGloas state)).mp
        (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)
    apply List.mem_toFinset.mpr
    apply mem_getActiveValidatorIndices_of_isActiveAt
    exact isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩
  -- A scored voter is in the committees, so no honest scored voter is outside them.
  have disjoint : Disjoint honest outside := by
    apply Finset.disjoint_left.mpr
    intro v member other
    exact (Finset.mem_filter.mp other).2.1
      (Store.mem_activeMembers.mp (scoredIn (Finset.mem_filter.mp member).1)).1
  refine ⟨honest ∪ outside, ?_, ?_⟩
  · intro v member
    rcases Finset.mem_union.mp member with member | member
    · obtain ⟨scoredMem, honestMem⟩ := Finset.mem_filter.mp member
      obtain ⟨message, latest, _, checkpointOk⟩ := scoredMessage v scoredMem
      obtain ⟨_, _, _, signs⟩ :=
        Execution.exists_attestation_of_latestMessages anchored start caller latest checkpointOk
      exact ⟨honestMem, countedActive v
        (List.mem_toFinset.mp (Finset.mem_filter.mp scoredMem).1), Or.inl signs⟩
    · exact ⟨(Finset.mem_filter.mp member).2.2, outsideActive v member,
        Or.inr (Finset.mem_filter.mp member).2.1⟩
  · have unionStake : stake (fun v => balanceAt state v.toNat) (honest ∪ outside) =
        stake (fun v => balanceAt state v.toNat) honest +
        stake (fun v => balanceAt state v.toNat) outside := Finset.sum_union disjoint
    change score.toNat = stake (fun v => balanceAt state v.toNat) scored at scoreEq
    rw [unionStake, supportEq]
    change 3 * _ + margin ≤ 3 * stake _ outside at remaining
    omega

end Models.Network

end EthLib.Consensus
