module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.Transition.IncludedTargetVotes
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification

/-!
# Voting sources above a block that holds a target's votes

A held block may hold the counted votes of a target, or have justified the target already.

Each block state above it in its epoch keeps those votes, or has justified the target.

So the last slot of the epoch justifies the target, and voting sources above the block reach it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Each held state of a reachable store reads its pending attestations at their own epoch.

This holds for the attestations after the anchor epoch. -/
private theorem Store.Reachable.pendingAtOwnEpoch {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    {root : Root} {state : BeaconState preset fork}
    (found : store.blockStates[root]? = some state) :
    PendingAtOwnEpoch (getCurrentEpoch anchorState) state :=
  reachable.blockState_induction reachable.blockStatesFromParents
    (fun _ st => PendingAtOwnEpoch (getCurrentEpoch anchorState) st)
    (fun _ _ _ recent later => by
      have bound := getPreviousEpoch_le anchorState
      cases recent <;> simp only [Bool.false_eq_true, ↓reduceIte] at later
      · exact (UInt64.not_lt.mpr bound later).elim
      · exact (UInt64.lt_irrefl _ later).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ parentHeld transition ih =>
      pendingAtOwnEpoch_stateTransition ih ((reachable.ordered sound).2 parentHeld) transition)
    found

namespace Models.Network

/-- Above a seed, each block state keeps its votes within that epoch, or has justified it.

The weighing at the last slot of the seed's epoch is the hypothesis `weigh`. -/
private theorem includedVotes_carry {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {seed : ForkChoiceNode} {seedSlot : Slot} {seedState : BeaconState preset fork}
    (anchorBelow : anchorBlock.slot ≤ seedSlot)
    (seedStored : store.blockStates[seed.root]? = some seedState)
    {epoch : Epoch} {root : Root} {recent : Bool}
    (near : (getCurrentEpoch seedState).toNat ≤ epoch.toNat + 1)
    (seedRead : getBlockRoot seedState epoch = .ok root)
    (weigh : ∀ (parent : Root) (status : PayloadStatus)
        (parentState state after : BeaconState preset fork)
        (child : Root) (childBlock : BeaconBlock preset fork) (other : SignatureChecks),
      store.blockStates[parent]? = some parentState →
      store.getAncestor ⟨parent, status⟩ seedSlot = .ok seed →
      store.blocks[child]? = some childBlock → childBlock.parentRoot = parent →
      getCurrentEpoch parentState = getCurrentEpoch seedState →
      (state = parentState ∨ ∃ slot, slot ≤ childBlock.slot ∧
        processSlots config checks parentState slot = .ok state) →
      (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
        getBlockRoot state epoch = .ok root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair recent) position →
          TargetFlagAt (recentParticipation state altair recent) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
          pending ∈ recentPending state before recent)) →
      advanceSlot config other state = .ok after →
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      epoch ≤ after.currentJustifiedCheckpoint.epoch)
    {node : ForkChoiceNode} {state : BeaconState preset fork}
    (held : store.blockStates[node.root]? = some state)
    (walk : store.getAncestor node seedSlot = .ok seed) :
    (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
      getBlockRoot state epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
        TargetFlagAt (recentParticipation seedState altair recent) position →
        TargetFlagAt (recentParticipation state altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
        pending ∈ recentPending state before recent)) ∨
      epoch ≤ state.currentJustifiedCheckpoint.epoch := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  by_cases low : block.slot ≤ seedSlot
  · rw [Store.getAncestor_of_le found low] at walk
    cases walk
    rw [held, Option.some.injEq] at seedStored
    subst seedStored
    exact .inl ⟨RunKept.refl _, rfl, seedRead, fun _ _ _ flagged => flagged,
      fun _ _ member => member⟩
  have other : block ≠ anchorBlock := fun same => low (same ▸ anchorBelow)
  obtain ⟨post, postOk, -, notAnchor⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  obtain ⟨parentState, blockChecks, engine, signed, -, message, parentHeld, transition⟩ :=
    notAnchor other
  rw [Store.getAncestor] at walk
  split at walk
  · simp_all
  rename_i b same
  rw [found, Option.some.injEq] at same
  subst b
  simp only [low, ↓reduceIte] at walk
  split at walk
  · simp [throw, throwThe, MonadExceptOf.throw] at walk
  rename_i parent parentFound
  split at walk
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at walk
  have parentInv := (reachable.ordered sound).2 parentHeld
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transition
  have slotBounds := stateTransition_slot transition
  rw [message] at slotsOk blockOk slotBounds
  have cjEq : state.currentJustifiedCheckpoint = advanced.currentJustifiedCheckpoint :=
    (frame_processBlock blockOk).currentJustified
  rcases includedVotes_carry reachable sound positive window anchorBelow seedStored
      near seedRead weigh parentHeld walk with kept | justified
  swap
  · exact .inr (UInt64.le_trans justified
      (stateTransition_currentJustified_mono parentInv transition))
  have parentEpochNat := getCurrentEpoch_toNat parentState
  have parentHigh : parentState.slot.toNat <
      ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [parentEpochNat, Nat.add_mul, Nat.one_mul]
    have := Nat.lt_div_mul_add (a := parentState.slot.toNat) positive
    omega
  have blockAfter := UInt64.lt_iff_toNat_lt.mp slotBounds.1
  have blockFits := block.slot.toNat_lt
  by_cases inEpoch : block.slot.toNat <
      ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat
  · simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, advancedOk⟩ := slotsOk
    have slotsKeep := (advanceSlots_keepsVotes positive window (epoch := epoch) (root := root)
      advancedOk (by omega)).2
    exact .inl (keptVotes_trans near (keptVotes_trans near kept slotsKeep)
      (processBlock_keepsVotes blockOk))
  obtain ⟨middle, middleShape, middleSlot, middleKept, middleRest⟩ : ∃ middle,
      (middle = parentState ∨ ∃ slot, slot ≤ block.slot ∧
        processSlots config checks parentState slot = .ok middle) ∧
      middle.slot.toNat + 1 =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ∧
      (RunKept seedState middle ∧ getCurrentEpoch middle = getCurrentEpoch seedState ∧
        getBlockRoot middle epoch = .ok root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair recent) position →
          TargetFlagAt (recentParticipation middle altair recent) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
          pending ∈ recentPending middle before recent)) ∧
      processSlots config blockChecks middle block.slot = .ok advanced := by
    by_cases atEnd : parentState.slot.toNat + 1 =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat
    · exact ⟨parentState, .inl rfl, atEnd, kept, slotsOk⟩
    have lastNat : (UInt64.ofNat (((getCurrentEpoch parentState).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat - 1)).toNat =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat - 1 := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨middle, firstOk, restOk⟩ := processSlots_split
      (UInt64.lt_iff_toNat_lt.mpr (by rw [lastNat]; omega))
      (UInt64.lt_iff_toNat_lt.mpr (by rw [lastNat]; omega)) slotsOk
    have middleSlot := (processSlots_slot firstOk).2
    have firstCopy := firstOk
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at firstCopy
    obtain ⟨u, lt, advancing⟩ := firstCopy
    obtain ⟨others, keep⟩ := advanceSlots_keepsVotes positive window (epoch := epoch) (root := root)
      advancing (by rw [lastNat]; omega)
    have firstChecks : processSlots config checks parentState
        (UInt64.ofNat (((getCurrentEpoch parentState).toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat - 1)) = .ok middle := by
      simp only [processSlots, bind_ok_iff, ensure_ok_iff]
      exact ⟨u, lt, others checks⟩
    refine ⟨middle, .inr ⟨_, UInt64.le_iff_toNat_le.mpr (by rw [lastNat]; omega), firstChecks⟩,
      by rw [middleSlot, lastNat]; omega, keptVotes_trans near kept keep, restOk⟩
  have middleInv : Invariant middle := by
    rcases middleShape with same | ⟨_, _, ok⟩
    · exact same ▸ parentInv
    · exact (processSlots_invariant parentInv ok).1
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at middleRest
  obtain ⟨_, _, restAdvance⟩ := middleRest
  have countPos : block.slot.toNat - middle.slot.toNat =
      (block.slot.toNat - middle.slot.toNat - 1) + 1 := by omega
  rw [countPos] at restAdvance
  simp only [advanceSlots, bind_ok_iff] at restAdvance
  obtain ⟨next, nextOk, tail⟩ := restAdvance
  have justified := weigh _ _ parentState middle next node.root block blockChecks parentHeld
    walk found rfl kept.2.1
    middleShape middleKept nextOk (by rw [middleSlot]; exact Nat.mul_mod_left _ _)
  have nextInv := (advanceSlot_invariant middleInv nextOk).1
  rw [cjEq]
  exact .inr (UInt64.le_trans justified (advanceSlots_currentJustified_mono nextInv tail))
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transition
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A seed that holds the counted target votes lifts each voting source above it to the target.

The votes are included in the seed, or the seed has justified the target already.

Each counted state above the seed in its epoch weighs the voters at two thirds, unslashed. -/
theorem includedVotes_votingSource_ge {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {seed : Root} {seedBlock : BeaconBlock preset fork} {seedState : BeaconState preset fork}
    (seedHeld : store.blocks[seed]? = some seedBlock)
    (seedStored : store.blockStates[seed]? = some seedState)
    {target : Checkpoint}
    (targetLate : GENESIS_EPOCH + 1 < target.epoch)
    (anchorBefore : getCurrentEpoch anchorState < target.epoch)
    (seedLower : target.epoch ≤ computeEpochAtSlot preset seedBlock.slot)
    (seedUpper : (computeEpochAtSlot preset seedBlock.slot).toNat < target.epoch.toNat + 2)
    (seedRead : getBlockRoot seedState target.epoch = .ok target.root)
    {voters : Finset ValidatorIndex}
    -- The store is past the seed's epoch, so a tip of the seed's epoch reads its pull-up.
    {current : Epoch} (storeEpoch : store.getCurrentStoreEpoch config = .ok current)
    (late : computeEpochAtSlot preset seedBlock.slot < current)
    (seedVotes : target.epoch ≤ seedState.currentJustifiedCheckpoint.epoch ∨
      (∃ altair : .altair ≤ fork, ∀ v ∈ voters,
        TargetFlagAt (recentParticipation seedState altair
          (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) v.toNat) ∨
      ∃ before : fork < .altair, ∀ v ∈ voters,
        ∃ pending ∈ recentPending seedState before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
          pending.data.target = target ∧
          ∃ indices, getPendingAttestingIndices seedState pending = .ok indices ∧ v ∈ indices)
    -- The voters are active at the target epoch in each block state above the seed.
    (active : ∀ (P : Root) (Ps : BeaconState preset fork), store.blockStates[P]? = some Ps →
      store.isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      ∀ v ∈ voters, v ∈ getActiveValidatorIndices Ps target.epoch)
    -- A counted state above the seed in its epoch weighs the voters at two thirds, unslashed.
    (quorum : ∀ (P : Root) (Ps W : BeaconState preset fork) (total : Gwei),
      store.blockStates[P]? = some Ps →
      store.isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      CountedState store config W →
      (W = Ps ∨ ∃ slot, processSlots config checks Ps slot = .ok W) →
      getCurrentEpoch W = getCurrentEpoch seedState →
      getTotalActiveBalance W = .ok total →
      2 * total.toNat ≤ 3 * stake (fun v => balanceAt W v.toNat) voters ∧
        ∀ v ∈ voters, (slashedFlagAt W v.toNat).getD false = false) :
    ∀ (tip : Root) (source : Checkpoint),
      store.isAncestor ⟨tip, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      store.getVotingSource config tip = .ok source →
      target.epoch ≤ source.epoch := by
  intro tip source tipAbove sourceOk
  have realizedLeSource {root tip : Root} {block : BeaconBlock preset fork}
      {base : BeaconState preset fork} {source : Checkpoint}
      (held : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some base)
      (above : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
      (read : store.getVotingSource config tip = .ok source) :
      base.currentJustifiedCheckpoint.epoch ≤ source.epoch :=
    reachable.realized_le_source sound (UInt64.le_of_eq anchorSlot) held stored above read
  rcases seedVotes with realizedSeed | seedVotes
  · exact UInt64.le_trans realizedSeed (realizedLeSource seedHeld seedStored tipAbove sourceOk)
  have seedEpochEq : getCurrentEpoch seedState = computeEpochAtSlot preset seedBlock.slot := by
    simp only [getCurrentEpoch,
      reachable.blockState_slot_eq anchorSlot seedHeld seedStored]
  have near : (getCurrentEpoch seedState).toNat ≤ target.epoch.toNat + 1 := by
    rw [seedEpochEq]
    omega
  have listEpoch : ∀ X : BeaconState preset fork,
      getCurrentEpoch X = computeEpochAtSlot preset seedBlock.slot →
      (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch) then getCurrentEpoch X
        else getPreviousEpoch X) = target.epoch := by
    intro X epochEq
    have list := recentEpoch_eq (state := X) (by rw [epochEq]; exact seedLower)
      (by rw [epochEq]; exact seedUpper)
    rw [epochEq] at list ⊢
    exact list
  have seedSelf : store.isAncestor ⟨seed, .pending⟩ ⟨seed, .pending⟩ = .ok true :=
    Store.isAncestor_self (node := ⟨seed, .pending⟩) seedHeld
  -- A state that keeps the seed's votes and that the store counts can weigh them.
  have weighAt : ∀ (P : Root) (Ps W : BeaconState preset fork) (total : Gwei),
      store.blockStates[P]? = some Ps →
      store.isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      CountedState store config W →
      (W = Ps ∨ ∃ slot, processSlots config checks Ps slot = .ok W) →
      getCurrentEpoch Ps = getCurrentEpoch seedState →
      (RunKept seedState W ∧ getCurrentEpoch W = getCurrentEpoch seedState ∧
        getBlockRoot W target.epoch = .ok target.root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ),
          position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position →
          TargetFlagAt (recentParticipation W altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
          pending ∈ recentPending W before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)))) →
      getTotalActiveBalance W = .ok total →
      getBlockRoot W (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)
        then getCurrentEpoch W else getPreviousEpoch W) = .ok target.root ∧
      2 * total.toNat ≤ 3 * stake (fun v => balanceAt W v.toNat) voters ∧
      ∀ v ∈ voters,
        v ∈ getActiveValidatorIndices W
          (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)
            then getCurrentEpoch W else getPreviousEpoch W) ∧
        UnslashedAt W v ∧
        ((∃ altair : .altair ≤ fork, TargetFlagAt (recentParticipation W altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) v.toNat) ∨
          ∃ before : fork < .altair, ∃ pending ∈ recentPending W before
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
            pending.data.target.root = target.root ∧
            ∃ indices, getPendingAttestingIndices W pending = .ok indices ∧ v ∈ indices) := by
    intro P Ps W total stored aboveSeed counts shape epochP kept totalOk
    obtain ⟨run, epochW, readW, flagsW, pendingW⟩ := kept
    have epochSeed := epochW.trans seedEpochEq
    have list := listEpoch W epochSeed
    obtain ⟨enough, clean⟩ := quorum P Ps W total stored aboveSeed counts shape epochW totalOk
    have activeW : ∀ v ∈ voters, v ∈ getActiveValidatorIndices W target.epoch := by
      intro v member
      rcases shape with same | ⟨_, ok⟩
      · exact same ▸ active P Ps stored aboveSeed v member
      · rw [(runKept_processSlots ok).active.getActiveValidatorIndices_eq
          (UInt64.le_trans (by rw [epochP, seedEpochEq]; exact seedLower)
            (getCurrentEpoch_le_activityFixedEpoch Ps))]
        exact active P Ps stored aboveSeed v member
    have epochWNat : (getCurrentEpoch W).toNat ≤ target.epoch.toNat + 1 := by
      rw [epochSeed]
      omega
    refine ⟨by rw [list]; exact readW, enough,
      fun v member => ⟨by rw [list]; exact activeW v member, clean v member, ?_⟩⟩
    rcases seedVotes with ⟨altair, flags⟩ | ⟨before, pendings⟩
    · exact .inl ⟨altair, flagsW altair v.toNat (lt_size_of_mem_getActiveValidatorIndices
        (active seed seedState seedStored seedSelf v member)) (flags v member)⟩
    · obtain ⟨pending, pendingMember, pendingTarget, indices, indicesOk, mem⟩ :=
        pendings v member
      obtain ⟨-, slotEpoch⟩ := reachable.pendingAtOwnEpoch sound seedStored before
        (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))
        (by rw [listEpoch seedState seedEpochEq]; exact anchorBefore) pending pendingMember
      refine .inr ⟨before, pending, pendingW before pending pendingMember,
        by rw [pendingTarget], indices, ?_, mem⟩
      rw [run.getPendingAttestingIndices_eq retained
        (by rw [slotEpoch, pendingTarget, seedEpochEq]; exact seedLower)
        (by rw [slotEpoch, pendingTarget]; exact epochWNat)]
      exact indicesOk
  -- The tip's walk reaches the seed's root, at a node of some payload status.
  obtain ⟨seedNode, tipWalk, seedNodeRoot⟩ := Store.getAncestor_of_isAncestor seedHeld tipAbove
  -- The last slot of the seed's epoch justifies the target.
  have weigh : ∀ (parent : Root) (status : PayloadStatus)
      (parentState state after : BeaconState preset fork)
      (child : Root) (childBlock : BeaconBlock preset fork) (other : SignatureChecks),
      store.blockStates[parent]? = some parentState →
      store.getAncestor ⟨parent, status⟩ seedBlock.slot = .ok seedNode →
      store.blocks[child]? = some childBlock → childBlock.parentRoot = parent →
      getCurrentEpoch parentState = getCurrentEpoch seedState →
      (state = parentState ∨ ∃ slot, slot ≤ childBlock.slot ∧
        processSlots config checks parentState slot = .ok state) →
      (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
        getBlockRoot state target.epoch = .ok target.root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ),
          position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position →
          TargetFlagAt (recentParticipation state altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
          pending ∈ recentPending state before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)))) →
      advanceSlot config other state = .ok after →
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      target.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
    intro parent status parentState state after child childBlock other stored walk childHeld
      childParent epochP shape kept advanced lastSlot
    -- The walk from the parent's pending node reaches the seed's root too.
    obtain ⟨atSeed, pendingWalk, atSeedRoot⟩ := Store.getAncestor_pending_root walk
    have aboveSeed := Store.isAncestor_of_getAncestor_root seedHeld rfl pendingWalk
      (atSeedRoot.trans seedNodeRoot)
    have epochSeed := kept.2.1.trans seedEpochEq
    have counted : GENESIS_EPOCH + 1 < getCurrentEpoch state :=
      UInt64.lt_of_lt_of_le targetLate (by rw [epochSeed]; exact seedLower)
    obtain ⟨total, totalOk⟩ := advanceSlot_total_of_last advanced lastSlot counted
    obtain ⟨rootOk, enough, votedW⟩ := weighAt parent parentState state total stored aboveSeed
      ⟨parent, parentState, stored, shape.imp_right fun ⟨slot, le, ok⟩ =>
        ⟨checks, slot, child, childBlock, childHeld, childParent, le, ok⟩⟩
      (shape.imp_right fun ⟨slot, _, ok⟩ => ⟨slot, ok⟩) epochP kept totalOk
    have result := advanceSlot_justifies positive window advanced lastSlot counted _ rootOk
      totalOk enough votedW
    rwa [listEpoch state epochSeed] at result
  -- The tip keeps the seed's votes, or has justified the target.
  have voting := sourceOk
  unfold Store.getVotingSource at voting
  simp only [bind_ok_iff] at voting
  obtain ⟨tipBlock, tipRead, tipEpoch, tipEpochOk, voting⟩ := voting
  have tipKnown := Store.block_ok_iff.mp tipRead
  obtain ⟨tipState, tipStored, -⟩ := reachable.blockStatesFromParents tipKnown
  have anchorBelow : anchorBlock.slot ≤ seedBlock.slot :=
    reachable.anchorSlot_le (UInt64.le_of_eq anchorSlot) seedHeld
  rcases includedVotes_carry reachable sound positive window
      (seed := seedNode) anchorBelow (seedNodeRoot ▸ seedStored) near seedRead weigh
      (node := ⟨tip, .pending⟩) tipStored tipWalk with kept | justified
  swap
  · exact UInt64.le_trans justified (realizedLeSource tipKnown tipStored
      (Store.isAncestor_self (node := ⟨tip, .pending⟩) tipKnown) sourceOk)
  -- The tip is of the seed's epoch, so its source is its pull-up, which weighs the votes.
  have tipEpochState := kept.2.1.trans seedEpochEq
  have tipSlot := reachable.blockState_slot_eq anchorSlot tipKnown tipStored
  have epochSame := Except.ok.inj (tipEpochOk.symm.trans storeEpoch)
  subst tipEpoch
  have tipEarly : computeEpochAtSlot preset tipBlock.slot < current := by
    have eq : computeEpochAtSlot preset tipBlock.slot = getCurrentEpoch tipState := by
      simp only [getCurrentEpoch, tipSlot]
    rw [eq, tipEpochState]
    exact late
  simp only [tipEarly, ↓reduceIte] at voting
  cases entry : store.unrealizedJustifications[tip]? with
  | none => simp [entry, throw, throwThe, MonadExceptOf.throw] at voting
  | some checkpoint =>
    simp only [entry, pure, Except.pure, Except.ok.injEq] at voting
    subst source
    rcases reachable.unrealizedJustification_origin entry with ⟨-, held⟩ |
      ⟨st, pulled, held, run, same⟩
    · rw [tipStored, Option.some.injEq] at held
      rw [held] at tipEpochState
      rw [tipEpochState] at anchorBefore
      exact absurd seedLower (UInt64.not_le.mpr anchorBefore)
    · rw [tipStored, Option.some.injEq] at held
      subst st
      have counted : GENESIS_EPOCH + 1 < getCurrentEpoch tipState :=
        UInt64.lt_of_lt_of_le targetLate (by rw [tipEpochState]; exact seedLower)
      obtain ⟨total, totalOk⟩ := processJustificationAndFinalization_totalActiveBalance run counted
      obtain ⟨rootOk, enough, votedW⟩ := weighAt tip tipState tipState total tipStored
        tipAbove ⟨tip, tipState, tipStored, .inl rfl⟩ (.inl rfl) kept.2.1 kept totalOk
      have result := processJustificationAndFinalization_justifies run counted _ rootOk
        totalOk enough votedW
      rw [listEpoch tipState tipEpochState] at result
      rw [same]
      exact result

end Models.Network

end EthLib.Consensus
