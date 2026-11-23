module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
import EthLib.Consensus.Proofs.ForkChoice.CheckpointAncestry
import EthLib.Consensus.Proofs.ForkChoice.SiblingCap
import EthLib.Consensus.Proofs.Transition.PendingTail
import EthLib.Consensus.Proofs.Transition.SlashedFlags

/-!
# Checked reads for historical-anchor transport

A receiver can read the weight of an older committee window in its own balance state.

The caller's successful read supplies the arithmetic at the first slot.

The receiver's longer committee window supplies the shorter window and its final-slot arithmetic.

Successful registry lookups and an active total then supply the checked balance read.
-/

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- A successful checked predecessor has the original slot as its checked successor. -/
private theorem addChecked_one_of_subChecked {a b : Slot}
    (read : subChecked a 1 = .ok b) : addChecked b 1 = .ok a := by
  obtain ⟨positive, value⟩ := subChecked_ok_iff.mp read
  apply addChecked_ok_iff.mpr
  have bound := a.toNat_lt
  simp only [UInt64.reduceToNat] at positive value ⊢
  constructor <;> omega


/-- Registry lookups and a checked active total supply a checked filtered total. -/
private theorem filteredTotal_exists {state : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (read : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ active result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) =
        .ok active ∧ getTotalBalance state active = .ok result := by
  obtain ⟨active, filtered⟩ := filterM_exists_ok (test := fun index => do
    return isActiveValidator (← validatorAt state index) (getCurrentEpoch state))
    (list := participants.toList) (fun v member => by
      obtain ⟨validator, found⟩ := inside v (Std.TreeSet.mem_toList.mp member)
      exact ⟨isActiveValidator validator (getCurrentEpoch state), by simp [found]⟩)
  obtain ⟨result, resultOk⟩ := getTotalBalance_exists_of_subset
    (indices := active) (getTotalActiveBalance_ok read) (fun v member => by
      have passed := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passed
      obtain ⟨validator, found, isActive⟩ := passed
      exact mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, isActive⟩))
  exact ⟨active, result, filtered, resultOk⟩

/-- An uncached checkpoint prefix comes from the first actual descendant's slot processing. -/
private theorem relation_of_checkpoint_lookahead {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (R : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ s, R s s) (trans : ∀ {s m t}, R s m → R m t → R s t)
    (edge : ∀ {s t : BeaconState preset fork} {checks' : SignatureChecks}
      {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork},
      stateTransition config checks' engine s signed true = .ok t → R s t)
    (fromPrefix : ∀ {s mid t : BeaconState preset fork} {middle : Slot}
      {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork},
      processSlots config checks s middle = .ok mid → middle ≤ signed.message.slot →
      stateTransition config checks engine s signed true = .ok t → R mid t)
    (slots : ∀ {s t : BeaconState preset fork} {slot : Slot},
      processSlots config checks s slot = .ok t → R s t)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {checkpoint : Checkpoint} {root : Root} {block : BeaconBlock preset fork}
    {start target : Slot} {base source after : BeaconState preset fork}
    (walk : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (bound : start ≤ max block.slot target)
    (baseFound : store.blockStates[checkpoint.root]? = some base)
    (sourceFound : store.blockStates[root]? = some source)
    (advanced : lookaheadState config checks source target = .ok after) :
    ∃ boundary, lookaheadState config checks base start = .ok boundary ∧ R boundary after := by
  by_cases atBlock : start ≤ block.slot
  · obtain ⟨boundary, boundaryOk, related⟩ := reached.relation_of_checkpointPrefix R refl trans
      edge fromPrefix anchorSlot walk found startOk atBlock baseFound sourceFound
    refine ⟨boundary, boundaryOk, trans related ?_⟩
    unfold lookaheadState at advanced
    split at advanced
    · exact slots (mapError_ok_iff.mp advanced)
    · cases advanced; exact refl _
  have below : block.slot < start := UInt64.not_le.mp atBlock
  have rootEq : root = checkpoint.root := by
    simpa [Store.getCheckpointBlock, startOk, Except.mapError,
      Store.getAncestor_of_le (node := ⟨root, .pending⟩) found (UInt64.le_of_lt below),
      bind, Except.bind,
      pure, Except.pure] using walk
  rw [rootEq, baseFound, Option.some.injEq] at sourceFound
  subst source
  have targetBound : start ≤ target := by
    have := UInt64.le_iff_toNat_le.mp bound
    have := UInt64.lt_iff_toNat_lt.mp below
    simp only [toNat_max] at *
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  by_cases before : base.slot < start
  · have advancing : base.slot < target := UInt64.lt_of_lt_of_le before targetBound
    have slotsOk : processSlots config checks base target = .ok after := by
      simpa [lookaheadState, advancing, mapError_ok_iff] using advanced
    rcases UInt64.lt_or_eq_of_le targetBound with strict | rfl
    · obtain ⟨boundary, boundaryOk, rest⟩ := processSlots_split before strict slotsOk
      exact ⟨boundary, by simp [lookaheadState, before, boundaryOk, Except.mapError], slots rest⟩
    · exact ⟨after, advanced, refl _⟩
  · refine ⟨base, by simp [lookaheadState, before, pure, Except.pure], ?_⟩
    unfold lookaheadState at advanced
    split at advanced
    · exact slots (mapError_ok_iff.mp advanced)
    · cases advanced; exact refl _

/-- An uncached checkpoint prefix comes from the first actual descendant's slot processing. -/
private theorem pendingTailRun_checkpointPrefix {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {checkpoint : Checkpoint} {root : Root} {block : BeaconBlock preset fork}
    {start slot : Slot} {source base after : BeaconState preset fork} {epoch : Epoch} {count : Nat}
    (target : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (atOrAfter : start ≤ max block.slot slot)
    (baseFound : store.blockStates[checkpoint.root]? = some base)
    (sourceFound : store.blockStates[root]? = some source)
    (advanced : lookaheadState config checks source slot = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) :
    ∃ boundary, lookaheadState config checks base start = .ok boundary ∧
      PendingTailRun count epoch boundary after := by
  exact relation_of_checkpoint_lookahead (PendingTailRun count epoch)
    PendingTailRun.refl (fun one two => one.trans two)
    (fun ok => pendingTailRun_stateTransition finite ok)
    (fun slots bound ok => relation_of_processSlots_of_stateTransition (PendingTailRun count epoch)
      (fun one two => one.trans two) (fun rest => pendingTailRun_processSlots finite rest)
      (fun step => pendingTailRun_processBlock finite step) slots bound ok)
    (fun ok => pendingTailRun_processSlots finite ok)
    anchorSlot reached target found startOk atOrAfter baseFound sourceFound advanced

/-- A held checkpoint bounds every finitely activated source position in the receiver registry.

The source lookahead transports its tail, while the receiver lookahead supplies the prefix size.

Historical applicability is still required separately; no validator identity is inferred. -/
private theorem registry_of_checkpointPrefix {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorInvariant : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH)
    {checkpoint : Checkpoint} {root sourceRoot : Root}
    {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    {source advancedSource base cached : BeaconState preset fork}
    {sourceTarget : Slot}
    (walk : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (bound : start ≤ max block.slot target)
    (baseFound : store.blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceRun : lookaheadState config checks source sourceTarget = .ok advancedSource)
    (sourceWalk : store.getCheckpointBlock sourceRoot checkpoint.epoch = .ok checkpoint.root)
    (sourceBlockFound : store.blocks[sourceRoot]? = some sourceBlock)
    (sourceBound : start ≤ max sourceBlock.slot sourceTarget)
    (sourceFound : store.blockStates[sourceRoot]? = some source)
    (finalized : advancedSource.finalizedCheckpoint.epoch ≤ checkpoint.epoch)
    (finite : checkpoint.epoch < FAR_FUTURE_EPOCH) :
    ∀ epoch position, isActiveAt advancedSource epoch position = true →
      ∃ validator, cached.validators.data[position]? = some validator := by
  -- The checkpoint block is held, so the store holds its state.
  obtain ⟨-, checkpointBlock, -, checkpointFound, -, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock sourceWalk
  obtain ⟨boundaryBase, boundaryBaseFound, -, -⟩ :=
    reached.reachable.blockStatesFromParents checkpointFound
  obtain ⟨boundary, boundaryRun, receiverRun⟩ := relation_of_checkpoint_lookahead
    RunKept RunKept.refl (fun one two => one.trans two)
    (fun ok => runKept_stateTransition ok)
    (fun slots bound ok => runKept_of_processSlots_of_stateTransition slots bound ok)
    (fun ok => runKept_processSlots ok)
    anchorSlot reached walk found startOk bound boundaryBaseFound baseFound advanced
  obtain ⟨sourceBoundary, sourceBoundaryRun, related⟩ := pendingTailRun_checkpointPrefix
    (count := boundary.validators.data.size) anchorSlot reached sourceWalk
    sourceBlockFound startOk sourceBound boundaryBaseFound sourceFound sourceRun finite
  have same : sourceBoundary = boundary :=
    Except.ok.inj (sourceBoundaryRun.symm.trans boundaryRun)
  subst sourceBoundary
  have holds : Invariant boundary := by
    have baseInv := (reached.reachable.ordered anchorInvariant).2 boundaryBaseFound
    unfold lookaheadState at boundaryRun
    split at boundaryRun
    · exact (processSlots_invariant baseInv (mapError_ok_iff.mp boundaryRun)).1
    · cases boundaryRun; exact baseInv
  obtain ⟨_, _, transport⟩ := related.2 holds
  have low : checkpoint.epoch ≤ getCurrentEpoch boundary := by
    have slotBound : start ≤ boundary.slot := by
      unfold lookaheadState at boundaryRun
      split at boundaryRun
      · exact UInt64.le_of_eq (processSlots_slot (mapError_ok_iff.mp boundaryRun)).2.symm
      · cases boundaryRun
        exact UInt64.not_lt.mp ‹¬ _›
    rw [← computeEpochAtSlot_computeStartSlotAtEpoch positive startOk]
    exact UInt64.le_iff_toNat_le.mpr
      (Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp slotBound))
  have tail : PendingTail boundary.validators.data.size checkpoint.epoch advancedSource :=
    transport low finalized (fun i v outside found => by
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      omega)
  intro epoch position active
  exact active_registry_of_pendingTail tail receiverRun.grows active

/-- The maximum succeeds when its arithmetic, committee, registry and total reads succeed. -/
private theorem maximum_exists_of_total {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei} {covered : Bool}
    (coverage : isFullValidatorSetCovered preset first last = .ok covered)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ maximum, store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum := by
  by_cases empty : last < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  cases covered
  · obtain ⟨active, result, filtered, resultOk⟩ := filteredTotal_exists totalOk inside
    simp only [bind, Except.bind, pure, Except.pure] at filtered
    exact ⟨result, by
      simp only [Store.computeCommitteeWeightBetweenSlots, Store.computeCommitteeWeightAndMembers,
        empty, ↓reduceIte, coverage, bind, Except.bind, Bool.false_eq_true, windowOk,
        filtered, resultOk, Except.mapError, pure, Except.pure]⟩
  · exact ⟨total, by
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered coverage]
      rw [totalOk]; rfl⟩

/-- A nonempty maximum supplies first-slot arithmetic for another range with the same start. -/
private theorem coverage_exists_of_maximum {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last otherLast afterOther : Slot} {maximum : Gwei}
    (nonempty : first ≤ last)
    (read : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (afterOk : addChecked otherLast 1 = .ok afterOther) :
    ∃ covered, isFullValidatorSetCovered preset first otherLast = .ok covered := by
  have notEmpty : ¬last < first := UInt64.not_lt.mpr nonempty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff] at read
  obtain ⟨result, read, -⟩ := read
  simp only [Store.computeCommitteeWeightAndMembers, notEmpty, ↓reduceIte,
    bind_ok_iff] at read
  obtain ⟨covered, coverage, -⟩ := read
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at coverage
  obtain ⟨afterFirst, firstOk, lastFirst, lastFirstOk, _, _, -⟩ := coverage
  refine ⟨decide (computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterOther), ?_⟩
  simp only [isFullValidatorSetCovered, firstOk, lastFirstOk, afterOk, Except.mapError,
    bind, Except.bind, pure, Except.pure]


/-- Folding a committee into a set preserves a property held by both inputs. -/
private theorem members_array_insert {committee : Array ValidatorIndex}
    {members : Std.TreeSet ValidatorIndex} (P : ValidatorIndex → Prop)
    (old : ∀ v ∈ members, P v) (new : ∀ v ∈ committee, P v) :
    ∀ v ∈ committee.foldl (·.insert ·) members, P v := by
  apply Array.foldl_induction (fun _ set => ∀ v ∈ set, P v) old
  intro i set held v member
  rcases Std.TreeSet.mem_insert.mp member with same | previous
  · have same : committee[i] = v := Std.LawfulEqCmp.compare_eq_iff_eq.mp same
    exact same ▸ new _ (Array.getElem_mem i.isLt)
  · exact held v previous

/-- Every member of a successful slot committee is active at that slot in the head state. -/
private theorem active_of_slotCommittee {store : Store preset fork} {head : Root} {slot : Slot}
    {state : BeaconState preset fork} {members : Std.TreeSet ValidatorIndex}
    (within : state.RegistryWithinLimit) (held : store.blockState head = .ok state)
    (read : store.getSlotCommittee head slot = .ok members) :
    ∀ v ∈ members, isActiveAt state (computeEpochAtSlot preset slot) v.toNat = true := by
  simp only [Store.getSlotCommittee, held, bind, Except.bind] at read
  apply foldlM_ok_invariant
    (fun set => ∀ v ∈ set, isActiveAt state (computeEpochAtSlot preset slot) v.toNat = true)
    (fun set index next old step => ?_) (by simp) read
  obtain ⟨committee, computed, result⟩ := bind_ok_iff.mp step
  cases result
  apply members_array_insert _ old
  intro v member
  exact isActiveAt_eq_true_iff.mpr
    ((mem_getActiveValidatorIndices within).mp
      (mem_getActiveValidatorIndices_of_getBeaconCommittee (mapError_ok_iff.mp computed) member))

/-- A window member is active at a queried epoch of the held head state. -/
private theorem active_of_committeeWindow {store : Store preset fork} {head : Root}
    {first last : Slot} {state : BeaconState preset fork} {members : Std.TreeSet ValidatorIndex}
    (within : state.RegistryWithinLimit) (held : store.blockState head = .ok state)
    (read : store.getCommitteesBetweenSlots head first last = .ok members) :
    ∀ v ∈ members, ∃ epoch, isActiveAt state epoch v.toNat = true := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨_, _, folded⟩ := read
  intro v member
  rcases (mem_foldlM_committees_iff folded).mp member with empty | ⟨offset, _, set, read, inside⟩
  · simp at empty
  · exact ⟨_, active_of_slotCommittee within held read v inside⟩

/-- Lookahead preserves unslashedness without a committee, chain or honest-set premise. -/
private theorem notSlashed_lookahead {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) :
    ∀ v : ValidatorIndex, (slashedFlagAt after v.toNat).getD false = false ↔
      (slashedFlagAt state v.toNat).getD false = false := by
  intro v
  unfold lookaheadState at run
  split at run
  · rw [slashedFlagAt_processSlots (mapError_ok_iff.mp run) v.toNat]
  · cases run; rfl

/-- A held block's checked predecessor is no later than the current slot's predecessor. -/
public theorem Store.ForwardReachableWith.previousBlockSlot_le_previousCurrentSlot
    {config : Config} {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {root : Root} {block : BeaconBlock preset fork} {current first last : Slot}
    (found : store.blocks[root]? = some block)
    (slotRead : store.getCurrentSlot config = .ok current)
    (blockLast : subChecked block.slot 1 = .ok first)
    (currentLast : subChecked current 1 = .ok last) : first ≤ last := by
  obtain ⟨state, stateFound, _, _⟩ := reached.reachable.blockStatesFromParents found
  have blockLe := reached.reachable.slot_le_of_blockState anchorSlot found stateFound
  have stateLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot
    stateFound slotRead
  have := (subChecked_ok_iff.mp blockLast).2
  have := (subChecked_ok_iff.mp currentLast).2
  have := UInt64.le_iff_toNat_le.mp blockLe
  have := UInt64.le_iff_toNat_le.mp stateLe
  exact UInt64.le_iff_toNat_le.mpr (by omega)

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A near vote below an ancestor of the head lies in the head's window after that ancestor.

Its target is at most one epoch after the ancestor, so the two states agree on its committees. -/
private theorem mem_window_of_near_vote {store : Store preset fork} {v : ValidatorIndex}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {head : ForkChoiceNode} {headState : BeaconState preset fork} {parentRoot : Root}
    {parent : BeaconBlock preset fork} {current first finish : Slot} {epoch : Epoch}
    {members : Std.TreeSet ValidatorIndex} {attestation : Attestation preset fork}
    (headFound : store.blockState head.root = .ok headState)
    (parentFound : store.blocks[parentRoot]? = some parent)
    (descends : store.isAncestor ⟨head.root, .pending⟩ ⟨parentRoot, .pending⟩ = .ok true)
    (slotRead : store.getCurrentSlot config = .ok current)
    (epochRead : store.getCurrentStoreEpoch config = .ok epoch)
    (horizon : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (window : store.getCommitteesBetweenSlots head.root first finish = .ok members)
    (origin : store.VoteOrigin config v attestation)
    (voteDescends : store.isAncestor ⟨attestation.data.beaconBlockRoot, .pending⟩
      ⟨parentRoot, .pending⟩ = .ok true)
    (low : first ≤ attestation.data.slot) (high : attestation.data.slot ≤ finish)
    (near : attestation.data.target.epoch.toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1) :
    v ∈ members := by
  have headLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot
    (Store.blockState_ok_iff.mp headFound) slotRead
  have epochEq : computeEpochAtSlot preset current = epoch := by
    simpa [Store.getCurrentStoreEpoch, slotRead, bind, Except.bind, pure, Except.pure]
      using epochRead
  have headEpoch : (getCurrentEpoch headState).toNat ≤ epoch.toNat := by
    rw [← epochEq, getCurrentEpoch_toNat]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp headLe)
  have parentVote : (computeEpochAtSlot preset parent.slot).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat := by
    have start := (addChecked_ok_iff.mp firstOk).2
    have low := UInt64.le_iff_toNat_le.mp low
    simp only [UInt64.toNat_one] at start
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (by omega)
  obtain ⟨targetState, index, committee, stored, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  obtain ⟨kept, count⟩ := reached.committeesKept_of_voteOrigin anchorSlot minLookahead
    maxLookahead (by omega) parentFound descends origin
    (voted := ⟨attestation.data.beaconBlockRoot, .pending⟩) rfl voteDescends
    (origin.targetEpoch ▸ near) stored (Store.blockState_ok_iff.mp headFound) (by omega)
  exact Store.mem_getCommitteesBetweenSlots window low high headFound (count ▸ below)
    ((kept _ _ rfl).trans committeeOk) member

/-- The head of a store with an ancestor that it descends from has a stored state. -/
public theorem headState_of_descends {store : Store preset fork}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {head : ForkChoiceNode} {parentRoot : Root} {parent : BeaconBlock preset fork}
    (parentFound : store.blocks[parentRoot]? = some parent)
    (descends : store.isAncestor ⟨head.root, .pending⟩ ⟨parentRoot, .pending⟩ = .ok true) :
    ∃ headState, store.blockState head.root = .ok headState := by
  obtain ⟨headBlock, headKnown, _⟩ := Store.slot_le_of_isAncestor parentFound descends
  obtain ⟨headState, headStored, _, _⟩ := reached.reachable.blockStatesFromParents headKnown
  exact ⟨headState, Store.blockState_ok_iff.mpr headStored⟩

/-- Each voter below the parent is in the head's window, given the premise for newly active ones.

A vote two epochs after the parent has a window that holds the whole epoch before its target. -/
public theorem Execution.votersInHeadWindow_of_newlyActive {anchor : Store preset fork}
    {parentRoot : Root} {first last : Nat}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (newVoters : NewlyActiveVotersInHeadWindow (e := e) parentRoot first last) :
    VotersInHeadWindow (e := e) parentRoot first last := by
  intro w honest k after time parent members v attestation inWindow
  obtain ⟨head, current, first, finish, epoch, headRead, parentFound, descends, slotRead,
    epochRead, horizon, firstOk, lastOk, window, origin, voteDescends, low, high⟩ := id inWindow
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore) k w
    honest
  obtain ⟨headState, headFound⟩ := headState_of_descends reached parentFound descends
  by_cases near : attestation.data.target.epoch.toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1
  · exact mem_window_of_near_vote reached anchorSlot minLookahead maxLookahead ring headFound
      parentFound descends slotRead epochRead horizon firstOk window origin voteDescends low high
      near
  -- The target is the current epoch, two epochs after the ancestor.
  obtain ⟨slot, slotOk, past⟩ := origin.past
  rw [slotRead, Except.ok.injEq] at slotOk
  subst slot
  have epochEq : computeEpochAtSlot preset current = epoch := by
    simpa [Store.getCurrentStoreEpoch, slotRead, bind, Except.bind, pure, Except.pure]
      using epochRead
  have targetNat : attestation.data.target.epoch.toNat =
      attestation.data.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [origin.targetEpoch, computeEpochAtSlot, UInt64.toNat_div]
  have currentNat : epoch.toNat = current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [← epochEq, computeEpochAtSlot, UInt64.toNat_div]
  have parentNat : (computeEpochAtSlot preset parent.slot).toNat =
      parent.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [computeEpochAtSlot, UInt64.toNat_div]
  have targetLe : attestation.data.target.epoch.toNat ≤ epoch.toNat := by
    rw [targetNat, currentNat]
    exact Nat.div_le_div_right (UInt64.le_of_lt past |> UInt64.le_iff_toNat_le.mp)
  have far : (computeEpochAtSlot preset parent.slot).toNat + 2 =
      attestation.data.target.epoch.toNat := by omega
  obtain ⟨targetState, -, stored, -⟩ := origin.committees
  let previous : Epoch := attestation.data.target.epoch - 1
  have previousNat : previous.toNat + 1 = attestation.data.target.epoch.toNat := by
    have one : (1 : Epoch) ≤ attestation.data.target.epoch :=
      UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.toNat_one]; omega)
    simp only [previous, UInt64.toNat_sub_of_le _ _ one, UInt64.toNat_one]
    omega
  rcases reached.active_or_newlyActive_of_voteOrigin anchorSlot maxLookahead parentFound descends
      origin voteDescends (by omega) previousNat stored (Store.blockState_ok_iff.mp headFound)
    with active | ⟨voter, voterFound, fresh⟩
  · -- The window holds the whole epoch before the target.
    have firstNat := (addChecked_ok_iff.mp firstOk).2
    have finishNat := (subChecked_ok_iff.mp lastOk)
    simp only [UInt64.toNat_one] at firstNat finishNat
    have parentLt : parent.slot.toNat < previous.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      have := Nat.lt_div_mul_add (a := parent.slot.toNat) positive
      rw [← parentNat] at this
      have same : previous.toNat = (computeEpochAtSlot preset parent.slot).toNat + 1 := by omega
      rw [same, Nat.succ_mul]
      exact this
    have currentLe : attestation.data.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        current.toNat := by
      have := Nat.div_mul_le_self current.toNat preset.SLOTS_PER_EPOCH.toNat
      rw [← currentNat] at this
      exact Nat.le_trans (Nat.mul_le_mul_right _ targetLe) this
    exact Store.mem_getCommitteesBetweenSlots_of_active positive window headFound
      (by omega) (by rw [previousNat]; omega) active
  · exact newVoters w honest k after time parent members v attestation targetState voter inWindow
      far stored voterFound fresh

/-- Every child supporter lies in the actual window, through the window-membership premise. -/
private theorem mem_window_of_mem_supporters {since last n : Nat} {u : ValidatorIndex}
    {parentRoot : Root} (membership : VotersInHeadWindow (e := e) parentRoot since last)
    (honest : u ∈ J) (after : since ≤ (e.world n).time) (time : (e.world n).time ≤ last)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock
      ((e.world n).state u))
    (lower : ((e.world n).state u).ParentsBelow)
    {head : ForkChoiceNode} {parent : BeaconBlock preset fork}
    {current first finish : Slot} {epoch : Epoch} {members : Std.TreeSet ValidatorIndex}
    {nodes : List ForkChoiceNode} {state : BeaconState preset fork} {c : Option Root} {i : Nat}
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (parentFound : ((e.world n).state u).blocks[parentRoot]? = some parent)
    (descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨parentRoot, .pending⟩ = .ok true)
    (slotRead : ((e.world n).state u).getCurrentSlot config = .ok current)
    (epochRead : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (horizon : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked current 1 = .ok finish)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first finish =
      .ok members)
    (child : (Store.blockTree lower).IsChild c (some parentRoot))
    (supporter : i ∈ Models.ForkChoice.supporters (Store.voters state)
      (Store.view lower nodes) c) : i.toUInt64 ∈ members := by
  obtain ⟨childRoot, childBlock, attestation, -, childFound, childParent, origin, above⟩ :=
    reached.exists_voteOrigin_of_mem_supporters child supporter
  obtain ⟨low, high⟩ := Store.slot_mem_range_of_voteOrigin lower parentFound childFound childParent
    slotRead firstOk lastOk origin above
  obtain ⟨voted, votedFound, -⟩ := origin.voted
  have isChild : (Store.blockTree lower).IsChild (some childRoot) (some parentRoot) :=
    Store.blockTree_isChild_iff.mpr ⟨childBlock, childFound, childParent⟩
  have voteDescends := Store.isAncestor_of_blockTree_ancestor (lower := lower)
    votedFound parentFound (isChild.ancestor.trans above)
  exact membership u honest n after time parent members _ attestation
    ⟨head, current, first, finish, epoch, headRead, parentFound, descends, slotRead, epochRead,
      horizon, firstOk, lastOk, window, origin, voteDescends, low, high⟩

open Models.ForkChoice in
/-- From Gloas, each supporter of a strict descendant of the parent's pending node is in the window.

Its vote is for the parent with a payload status after the parent's slot, or for a later block. -/
private theorem mem_window_of_mem_nodeSupporters {since last n : Nat} {u : ValidatorIndex}
    {parentRoot : Root} (membership : VotersInHeadWindow (e := e) parentRoot since last)
    (honest : u ∈ J) (after : since ≤ (e.world n).time) (time : (e.world n).time ≤ last)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock
      ((e.world n).state u))
    (lower : ((e.world n).state u).ParentsBelow) (gloas : .glamsterdam ≤ fork)
    {head : ForkChoiceNode} {parent : BeaconBlock preset fork}
    {current first finish : Slot} {epoch : Epoch} {members : Std.TreeSet ValidatorIndex}
    {nodes : List ForkChoiceNode} {state : BeaconState preset fork}
    {c : Option Root × Status} {i : Nat}
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (parentFound : ((e.world n).state u).blocks[parentRoot]? = some parent)
    (descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨parentRoot, .pending⟩ = .ok true)
    (slotRead : ((e.world n).state u).getCurrentSlot config = .ok current)
    (epochRead : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (horizon : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked current 1 = .ok finish)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first finish =
      .ok members)
    (below : (Store.nodeTree lower).Ancestor (some parentRoot, none) c)
    (strict : c ≠ (some parentRoot, none))
    (supporter : i ∈ supporters (Store.voters state) (Store.nodeView lower nodes) c) :
    i.toUInt64 ∈ members := by
  classical
  simp only [supporters, Finset.mem_filter] at supporter
  obtain ⟨-, m, latest, above⟩ := supporter
  change ((e.world n).state u).latestNode i.toUInt64 = some m at latest
  unfold Store.latestNode at latest
  split at latest
  · exact absurd latest (by simp)
  cases messageFound : ((e.world n).state u).latestMessages[i.toUInt64]? with
  | none => simp [messageFound] at latest
  | some message =>
  cases supportedOk : ((e.world n).state u).getSupportedNode message with
  | error err => simp [messageFound, supportedOk, Except.toOption] at latest
  | ok node =>
  simp only [messageFound, supportedOk, Option.bind_some, Except.toOption, Option.map_some,
    Option.some.injEq] at latest
  subst latest
  obtain ⟨attestation, rfl, origin⟩ := reached.forwardReachable.votesHaveOrigins messageFound
  have rooted : node.root = attestation.data.beaconBlockRoot :=
    Store.getSupportedNode_root supportedOk
  have blockBelow : (Store.blockTree lower).Ancestor (some parentRoot)
      (some attestation.data.beaconBlockRoot) :=
    rooted ▸ BlockTree.payloadTree_ancestor_fst (below.trans above)
  obtain ⟨voted, votedFound, votedLe⟩ := origin.voted
  have voteDescends := Store.isAncestor_of_blockTree_ancestor (lower := lower)
    votedFound parentFound blockBelow
  obtain ⟨current', currentOk, past⟩ := origin.past
  rw [slotRead] at currentOk
  cases currentOk
  have firstNat := Uint64.addChecked_ok_iff.mp firstOk
  obtain ⟨le, eq⟩ := subChecked_ok_iff.mp lastOk
  have pastNat := UInt64.lt_iff_toNat_lt.mp past
  simp only [UInt64.toNat_one] at le eq firstNat
  have high : attestation.data.slot ≤ finish := by
    rw [UInt64.le_iff_toNat_le]
    omega
  -- The vote is after the parent's slot: a payload node of the parent, or a later block.
  have later : parent.slot < attestation.data.slot := by
    by_cases same : attestation.data.beaconBlockRoot = parentRoot
    · by_contra notLater
      have pending := Store.getSupportedNode_of_same_slot gloas
        (message := LatestMessage.ofAttestation attestation)
        (by simpa [LatestMessage.ofAttestation, same] using parentFound)
        (by simpa [LatestMessage.ofAttestation] using UInt64.not_lt.mp notLater)
      rw [supportedOk, Except.ok.injEq] at pending
      subst pending
      apply strict
      have top : (ForkChoiceNode.toModel ⟨(LatestMessage.ofAttestation attestation).root,
          .pending⟩) = (some parentRoot, none) := by
        simp [ForkChoiceNode.toModel, LatestMessage.ofAttestation, same, PayloadStatus.toStatus]
      rw [top] at above
      exact (below.antisymm above).symm
    · obtain ⟨child, isChild, chain⟩ := blockBelow.exists_child (by simpa using Ne.symm same)
      rcases child with _ | childRoot
      · exact absurd rfl isChild.1
      obtain ⟨childBlock, childFound, childParent⟩ := Store.blockTree_isChild_iff.mp isChild
      have parentLower := lower _ childBlock parent childFound (childParent ▸ parentFound)
      have heights := chain.height_le
      rw [Store.blockTree_height_of childFound, Store.blockTree_height_of votedFound] at heights
      exact UInt64.lt_of_lt_of_le parentLower
        (UInt64.le_trans (UInt64.le_iff_toNat_le.mpr (by omega)) votedLe)
  have low : first ≤ attestation.data.slot := by
    have := UInt64.lt_iff_toNat_lt.mp later
    rw [UInt64.le_iff_toNat_le]
    omega
  exact membership u honest n after time parent members _ attestation
    ⟨head, current, first, finish, epoch, headRead, parentFound, descends, slotRead, epochRead,
      horizon, firstOk, lastOk, window, origin, voteDescends, low, high⟩

open Models.ForkChoice in
/-- The model weight includes every honest supporter counted by the store. -/
private theorem honest_supporters_le_weight [DecidablePred (· ∈ J)]
    {store : Store preset fork} {state : BeaconState preset fork} {root : Root}
    {block : BeaconBlock preset fork} (lower : store.ParentsBelow)
    (within : state.RegistryWithinLimit)
    (found : store.blocks[root]? = some block) (nodes : List ForkChoiceNode) :
    stake (fun v => balanceAt state v.toNat)
        {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J} ≤
      weight (Store.voters state) (balanceAt state) (Store.view lower nodes) (some root) := by
  classical
  let S := {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J}
  have inside : S.image UInt64.toNat ⊆
      supporters (Store.voters state) (Store.view lower nodes) (some root) := by
    intro i member
    obtain ⟨v, inS, rfl⟩ := Finset.mem_image.mp member
    have supporter := (Finset.mem_filter.mp inS).1
    have counts := Store.voteCountsFor_of_mem_supportersOf supporter
    obtain ⟨message, supported, latest, clean, supportedOk, descends⟩ :=
      store.exists_of_voteCountsFor counts
    have pendingDescends := (Store.isAncestor_getSupportedNode supportedOk root) ▸ descends
    have ancestry := (Store.isAncestor_iff (lower := lower) found rfl pendingDescends).mp rfl
    simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at supporter
    obtain ⟨⟨index, balance⟩, ⟨entry, _⟩, same⟩ := supporter
    simp only at same
    subst index
    obtain ⟨validator, found, active, unslashed⟩ :=
      (mem_unslashedActiveBalances_iff within).mp (List.mem_map.mpr ⟨_, entry, rfl⟩)
    have voter : v.toNat ∈ Store.voters state := by
      simp only [Store.voters, Finset.mem_filter, Finset.mem_range]
      exact ⟨(Array.getElem?_eq_some_iff.mp found).1, by
        simp [Store.counts, found, active, unslashed]⟩
    refine Finset.mem_filter.mpr ⟨voter, ?_⟩
    refine ⟨some message.root, ?_, ancestry⟩
    change store.latestVote v.toNat.toUInt64 = some (some message.root)
    have notEquivocating : v ∉ store.equivocatingIndices := by simpa using clean
    simp [Store.latestVote, latest, notEquivocating]
  have summed : stake (balanceAt state) (S.image UInt64.toNat) =
      stake (fun v => balanceAt state v.toNat) S := by
    unfold stake
    rw [Finset.sum_image]
    exact fun _ _ _ _ same => UInt64.toNat_inj.mp same
  rw [← summed]
  exact stake_mono inside

open Models.ForkChoice in
/-- A visited parent selects its strictly heaviest child. -/
private theorem ancestor_ghost_of_visited_parent {ν β ρ : Type*} [DecidableEq β]
    [LinearOrder ρ] {T : BlockTree β} (V : Finset ν) (w : ν → Nat) (G : View ν β T)
    (key : β → ρ) {parent child start : β} (member : child ∈ children G parent)
    (above : T.Ancestor start parent)
    (visited : T.Ancestor parent (ghost V w G key start))
    (heavier : ∀ sibling ∈ children G parent, sibling ≠ child →
      weight V w G sibling < weight V w G child) :
    T.Ancestor child (ghost V w G key start) := by
  classical
  induction start using ghost.induct V w G key with
  | case1 start nonempty next =>
    let chosen := heaviestChild V w G key start nonempty
    have chosenChild := (mem_children.mp (heaviestChild_spec V w G key start nonempty).1).2
    have walked := ghost_of_nonempty V w G key nonempty
    change ghost V w G key start = ghost V w G key chosen at walked
    by_cases same : start = parent
    · subst start
      have direct := (mem_children.mp member).2
      apply ancestor_ghost_of_heavier V w G key (mem_children.mp member).1 direct.ancestor
      intro middle fromParent toChild different sibling siblingMember distinct
      rcases toChild.eq_or_parent with sameChild | belowParent
      · subst middle
        simpa only [direct.2] using heavier sibling (direct.2 ▸ siblingMember) distinct
      · rw [direct.2] at belowParent
        exact False.elim (different (belowParent.antisymm fromParent))
    · have through : T.Ancestor chosen parent := by
        have both := (ancestor_ghost V w G key chosen).total (walked ▸ visited)
        rcases both with through | past
        · exact through
        · rcases past.eq_or_parent with equal | back
          · exact equal ▸ BlockTree.Ancestor.refl parent
          · rw [chosenChild.2] at back
            exact False.elim (same (above.antisymm back))
      rw [walked]
      exact next through (walked ▸ visited)
  | case2 start empty =>
    rw [ghost_of_not_nonempty V w G key empty] at visited
    have same := above.antisymm visited
    exact False.elim (empty ⟨child, same ▸ member⟩)

open Models.ForkChoice in
/-- A node between the two ends of a path of two steps is one of its three nodes. -/
private theorem eq_of_path_two {β : Type} {T : BlockTree β} {start mid target x : β}
    (toMid : T.parent target = mid) (toStart : T.parent mid = start)
    (low : T.Ancestor start x) (high : T.Ancestor x target) :
    x = start ∨ x = mid ∨ x = target := by
  obtain ⟨k, walk⟩ := high
  match k, walk with
  | 0, walk => exact .inr (.inr walk.symm)
  | 1, walk => exact .inr (.inl (by simpa [toMid] using walk.symm))
  | k + 2, walk =>
    left
    have up : T.Ancestor x start := ⟨k, by
      rw [← walk, Function.iterate_add_apply]
      simp [toMid, toStart]⟩
    exact up.antisymm low

open Models.ForkChoice in
/-- From Gloas, a counted voter whose clean vote is for a descendant of a node supports that node.

The support is read in the tree of nodes. -/
private theorem toNat_mem_nodeSupporters {store : Store preset fork}
    (lower : store.ParentsBelow) (gloas : .glamsterdam ≤ fork)
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode}
    {target : ForkChoiceNode} {targetBlock : BeaconBlock preset fork}
    (targetFound : store.blocks[target.root]? = some targetBlock)
    {v : ValidatorIndex} {validator : Validator}
    (atIndex : state.validators.data[v.toNat]? = some validator)
    (active : isActiveValidator validator (getCurrentEpoch state) = true)
    (unslashed : validator.slashed = false)
    {message : LatestMessage fork} {supported : ForkChoiceNode}
    (latest : store.latestMessages[v]? = some message)
    (clean : store.equivocatingIndices.contains v = false)
    (supportedOk : store.getSupportedNode message = .ok supported)
    (descends : store.isAncestor supported target = .ok true) :
    v.toNat ∈ supporters (Store.voters state) (Store.nodeView lower nodes) target.toModel := by
  classical
  have same : v.toNat.toUInt64 = v := UInt64.ofNat_toNat
  refine Finset.mem_filter.mpr ⟨?_, supported.toModel, ?_,
    (Store.isAncestor_iff_of_gloas (lower := lower) gloas targetFound descends).mp rfl⟩
  · simp only [Store.voters, Finset.mem_filter, Finset.mem_range]
    exact ⟨(Array.getElem?_eq_some_iff.mp atIndex).1, by
      simp [Store.counts, atIndex, active, unslashed]⟩
  · show store.latestNode v.toNat.toUInt64 = _
    rw [same]
    have notIn : v ∉ store.equivocatingIndices := by simpa using clean
    simp [Store.latestNode, latest, notIn, supportedOk, Except.toOption]

open Models.ForkChoice in
/-- A clean latest vote supports only the ancestors of the node it supports. -/
private theorem ancestor_of_mem_nodeSupporters {store : Store preset fork}
    {lower : store.ParentsBelow} {state : BeaconState preset fork} {nodes : List ForkChoiceNode}
    {v : ValidatorIndex} {message : LatestMessage fork} {supported : ForkChoiceNode}
    {x : Option Root × Status}
    (latest : store.latestMessages[v]? = some message)
    (clean : store.equivocatingIndices.contains v = false)
    (supportedOk : store.getSupportedNode message = .ok supported)
    (supporter : v.toNat ∈ supporters (Store.voters state) (Store.nodeView lower nodes) x) :
    (Store.nodeTree lower).Ancestor x supported.toModel := by
  simp only [supporters, Finset.mem_filter] at supporter
  obtain ⟨-, m, vote, above⟩ := supporter
  change store.latestNode v.toNat.toUInt64 = some m at vote
  simp only [Store.latestNode, UInt64.ofNat_toNat, clean, latest, supportedOk, Except.toOption,
    Bool.false_eq_true, ↓reduceIte, Option.bind_some, Option.map_some, Option.some.injEq] at vote
  exact vote ▸ above

open Models.ForkChoice in
/-- The stake of validators that each support a model node is at most that node's weight. -/
private theorem stake_le_of_mem_supporters {β : Type} {T : BlockTree β}
    (G : Models.ForkChoice.View ℕ β T) {state : BeaconState preset fork}
    {X : Finset ValidatorIndex} {x : β}
    (inside : ∀ v ∈ X, v.toNat ∈ Models.ForkChoice.supporters (Store.voters state) G x) :
    stake (fun v => balanceAt state v.toNat) X ≤
      Models.ForkChoice.weight (Store.voters state) (balanceAt state) G x := by
  classical
  have summed : stake (balanceAt state) (X.image UInt64.toNat) =
      stake (fun v => balanceAt state v.toNat) X := by
    unfold stake
    rw [Finset.sum_image]
    exact fun _ _ _ _ same => UInt64.toNat_inj.mp same
  rw [← summed]
  exact stake_mono fun i member => by
    obtain ⟨v, inX, rfl⟩ := Finset.mem_image.mp member
    exact inside v inX

open Models.ForkChoice in
/-- From Gloas, a receiver margin makes the path child below the parent outweigh each rival.

The path runs from the parent's pending node to the block's pending node.

It passes the node of the status that the block builds on.

The margin counts the window, the score, twice the honest supporters and the honest parent voters.

Every competing voter is a window member outside those sets, and the boost is at most the score.

It also gives the block's honest supporters positive stake, and the path child positive weight. -/
private theorem sibling_bound_of_window_margin [DecidablePred (· ∈ J)]
    {store : Store preset fork} (lower : store.ParentsBelow) (gloas : .glamsterdam ≤ fork)
    {state : BeaconState preset fork} (within : state.RegistryWithinLimit)
    {nodes : List ForkChoiceNode} {root : Root} {block parent : BeaconBlock preset fork}
    {members participants : Std.TreeSet ValidatorIndex} {score : Nat}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (inWindow : ∀ c, (Store.nodeTree lower).Ancestor (some block.parentRoot, none) c →
      c ≠ (some block.parentRoot, none) →
      ∀ i ∈ supporters (Store.voters state) (Store.nodeView lower nodes) c, i.toUInt64 ∈ members)
    (shortInside : ∀ v ∈ participants, v ∈ members)
    (boostLe : store.boostScoreOfGloas config gloas ≤ score)
    (margin : stake (fun v => balanceAt state v.toNat) (Store.activeMembers state members) +
        score <
      2 * stake (fun v =>
        if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0)
        {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J} +
      stake (fun v =>
        if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0)
        {v ∈ store.parentVotersOf state participants block parent | v ∈ J}) :
    0 < stake (fun v =>
        if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0)
        {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J} ∧
    ∀ p c d : Option Root × Status,
      (Store.nodeTree lower).Ancestor (some block.parentRoot, none) p →
      (Store.nodeTree lower).IsChild c p → (Store.nodeTree lower).IsChild d p →
      (Store.nodeTree lower).Ancestor c (some root, none) → d ≠ c →
      weight (Store.voters state).insertNone
          (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
          ((Store.nodeView lower nodes).withBoost (store.boostedNode config gloas)) d <
        weight (Store.voters state).insertNone
          (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
          ((Store.nodeView lower nodes).withBoost (store.boostedNode config gloas)) c ∧
      0 < weight (Store.voters state).insertNone
          (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
          ((Store.nodeView lower nodes).withBoost (store.boostedNode config gloas)) c := by
  classical
  set G := Store.nodeView lower nodes with hG
  set boost := store.boostScoreOfGloas config gloas
  let wb := fun x => weight (Store.voters state).insertNone (boostStake (balanceAt state) boost)
    (G.withBoost (store.boostedNode config gloas)) x
  set guard := fun v : ValidatorIndex =>
    if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset then balanceAt state v.toNat else 0
    with hguard
  set S := {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J} with hS
  set V := {v ∈ store.parentVotersOf state participants block parent | v ∈ J} with hV
  set W := Store.activeMembers state members with hW
  -- The three nodes of the path.
  set start : Option Root × Status := (some block.parentRoot, none)
  set mid : Option Root × Status :=
    (some block.parentRoot, some (Store.parentPayloadStatus block parent == .full))
  set target : Option Root × Status := (some root, none)
  have toMid : (Store.nodeTree lower).parent target = mid :=
    Store.nodeTree_parent_of found parentFound
  have toStart : (Store.nodeTree lower).parent mid = start := BlockTree.payloadTree_parent_some _ _
  have targetChild : (Store.nodeTree lower).IsChild target mid :=
    ⟨fun same => Option.some_ne_none _ (Prod.mk.inj same).1, toMid⟩
  have midChild : (Store.nodeTree lower).IsChild mid start :=
    ⟨fun same => Option.some_ne_none _ (Prod.mk.inj same).1, toStart⟩
  -- Guarded stakes are at most plain stakes.
  have guardLe (X : Finset ValidatorIndex) :
      stake guard X ≤ stake (fun v => balanceAt state v.toNat) X := by
    apply Finset.sum_le_sum
    intro v _
    simp only [guard]
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  -- A parent voter's clean latest vote is for the parent's pending node or for `mid`.
  have parentVote : ∀ v ∈ V, ∃ message supported, store.latestMessages[v]? = some message ∧
      store.equivocatingIndices.contains v = false ∧
      store.getSupportedNode message = .ok supported ∧
      (Store.nodeTree lower).Ancestor supported.toModel mid := by
    intro v member
    obtain ⟨-, -, honestVote, message, supported, latest, supportedOk, isParent⟩ :=
      Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1
    refine ⟨message, supported, latest, by simpa using honestVote, supportedOk, ?_⟩
    rcases isParent with rfl | rfl
    · exact midChild.ancestor
    · have statusEq : (Store.parentPayloadStatus block parent).toStatus =
          some (Store.parentPayloadStatus block parent == .full) := by
        have ne := Store.parentPayloadStatus_ne_pending (block := block) (parent := parent) gloas
        revert ne
        cases Store.parentPayloadStatus block parent <;> simp [PayloadStatus.toStatus]
      show (Store.nodeTree lower).Ancestor (some block.parentRoot, _) mid
      rw [statusEq]
      exact .refl _
  -- So a parent voter supports only ancestors of `mid`.
  have parentAbove : ∀ v ∈ V, ∀ x, v.toNat ∈ supporters (Store.voters state) G x →
      (Store.nodeTree lower).Ancestor x mid := by
    intro v member x supporter
    obtain ⟨message, supported, latest, clean, supportedOk, up⟩ := parentVote v member
    exact (ancestor_of_mem_nodeSupporters latest clean supportedOk supporter).trans up
  -- Each honest supporter of the block supports its pending node in the model.
  have supportInside : ∀ v ∈ S, v.toNat ∈ supporters (Store.voters state) G target := by
    intro v member
    have supported := (Finset.mem_filter.mp member).1
    obtain ⟨message, node, latest, clean, supportedOk, descends⟩ :=
      store.exists_of_voteCountsFor (Store.voteCountsFor_of_mem_supportersOf supported)
    obtain ⟨validator, atIndex, active, unslashed⟩ :=
      (mem_unslashedActiveBalances_iff within).mp
        (List.mem_map.mpr (by
          simp only [Store.supportersOf, List.mem_toFinset, List.mem_map,
            List.mem_filter] at supported
          obtain ⟨entry, ⟨inside, -⟩, same⟩ := supported
          exact ⟨entry, inside, same⟩))
    exact toNat_mem_nodeSupporters (target := ⟨root, .pending⟩) lower gloas found atIndex active
      unslashed latest clean supportedOk descends
  -- Members of the window: competitors below the parent, and parent voters.
  have activeOf : ∀ i ∈ Store.voters state, i.toUInt64 ∈ members → i.toUInt64 ∈ W := by
    intro i voter member
    obtain ⟨small, validator, atIndex, active⟩ := Store.active_of_mem_voters voter
    have back := toNat_toUInt64_of_lt within small
    exact Store.mem_activeMembers.mpr ⟨member, validator, by simpa only [back] using atIndex,
      active⟩
  have strictInside : ∀ x, (Store.nodeTree lower).Ancestor start x → x ≠ start →
      ∀ i ∈ supporters (Store.voters state) G x, i.toUInt64 ∈ W :=
    fun x low ne i member => activeOf i (Finset.mem_of_mem_filter _ member)
      (inWindow x low ne i member)
  have parentInside : ∀ X ⊆ V, X ⊆ W := by
    intro X sub v member
    obtain ⟨inShort, validator, _⟩ := Store.mem_parentVotersOf.mp
      (Finset.mem_filter.mp (sub member)).1
    obtain ⟨entry, atIndex, _, active⟩ := validator
    exact Store.mem_activeMembers.mpr ⟨shortInside v inShort, entry, atIndex, active⟩
  have vInside := (guardLe V).trans (stake_mono (parentInside V (subset_refl _)))
  have positiveS : 0 < stake guard S := by omega
  refine ⟨positiveS, fun p c d below isChild siblingIsChild onPath distinct => ?_⟩
  have strictOf : ∀ x, (Store.nodeTree lower).IsChild x p →
      (Store.nodeTree lower).Ancestor start x ∧ x ≠ start := fun x child =>
    ⟨below.trans child.ancestor, fun same => by
      have := (below.trans child.ancestor).height_le
      have := child.height_lt
      rw [same] at this
      exact absurd below.height_le (by omega)⟩
  have boostedLe : ∀ x, weight (Store.voters state) (balanceAt state) G x ≤ wb x := by
    intro x
    simp only [wb, weight_withBoost]
    omega
  have totalBound := Store.weight_add_weight_add_stake_le_stake_withBoost_of_isChild G within
  -- The parent node is the parent's pending node or `mid`.
  have pAbove : (Store.nodeTree lower).Ancestor p target := isChild.ancestor.trans onPath
  have pNotTarget : p ≠ target := fun same => by
    have := isChild.height_lt
    have := onPath.height_le
    rw [same] at *
    omega
  rcases eq_of_path_two toMid toStart below pAbove with rfl | rfl | rfl
  · -- At the parent's pending node, the child toward the block is `mid`.
    have cMid : c = mid := by
      by_contra ne
      have cAbove : (Store.nodeTree lower).Ancestor c mid := by
        rcases onPath.eq_or_parent with same | up
        · have parentEq := isChild.2
          rw [same, toMid] at parentEq
          simp [mid, start] at parentEq
        · rwa [toMid] at up
      exact isChild.disjoint midChild ne cAbove (.refl _)
    subst cMid
    set M := V.filter fun v => v.toNat ∈ supporters (Store.voters state) G mid
    set Pend := V.filter fun v => v.toNat ∉ supporters (Store.voters state) G mid
    have split : stake guard V = stake guard M + stake guard Pend := by
      simp only [stake, M, Pend]
      exact (Finset.sum_filter_add_sum_filter_not V _ _).symm
    have apart : Disjoint S M := by
      refine Finset.disjoint_left.mpr fun v inS inM => ?_
      have up := parentAbove v (Finset.mem_filter.mp inM).1 target (supportInside v inS)
      exact absurd up.height_le (Nat.not_le.mpr targetChild.height_lt)
    have lowerBound : stake guard S + stake guard M ≤ wb mid := by
      have unionEq : stake guard (S ∪ M) = stake guard S + stake guard M := Finset.sum_union apart
      rw [← unionEq]
      refine (guardLe _).trans ((stake_le_of_mem_supporters G fun v member => ?_).trans
        (boostedLe mid))
      rcases Finset.mem_union.mp member with inS | inM
      · have sup := supportInside v inS
        simp only [supporters, Finset.mem_filter] at sup ⊢
        obtain ⟨voter, m, vote, up⟩ := sup
        exact ⟨voter, m, vote, targetChild.ancestor.trans up⟩
      · exact (Finset.mem_filter.mp inM).2
    have bound := totalBound (store.boostedNode config gloas) boost (N := Pend) (window := W)
      midChild siblingIsChild distinct
      (fun i member => by
        rcases Finset.mem_union.mp member with inC | inD
        · exact strictInside mid midChild.ancestor (fun same => by
            simp [mid, start] at same) i inC
        · exact strictInside d siblingIsChild.ancestor (strictOf d siblingIsChild).2 i inD)
      (parentInside Pend (Finset.filter_subset _ _))
      (fun v member => ⟨(Finset.mem_filter.mp member).2, fun supporter =>
        siblingIsChild.disjoint midChild distinct
          (parentAbove v (Finset.mem_filter.mp member).1 d supporter) (.refl _)⟩)
    have pendLe := guardLe Pend
    simp only [wb] at lowerBound
    constructor <;> omega
  · -- At `mid`, the child toward the block is the block's pending node.
    have cTarget : c = target := by
      by_contra ne
      exact isChild.disjoint targetChild ne onPath (.refl _)
    subst cTarget
    have lowerBound : stake guard S ≤ wb target :=
      (guardLe S).trans ((stake_le_of_mem_supporters G supportInside).trans (boostedLe target))
    have bound := totalBound (store.boostedNode config gloas) boost (N := V) (window := W)
      targetChild siblingIsChild distinct
      (fun i member => by
        rcases Finset.mem_union.mp member with inC | inD
        · exact strictInside target (midChild.ancestor.trans targetChild.ancestor)
            (fun same => by
              have := targetChild.height_lt
              have := midChild.height_lt
              rw [same] at *; omega) i inC
        · exact strictInside d (midChild.ancestor.trans siblingIsChild.ancestor)
            (fun same => by
              have := siblingIsChild.height_lt
              have := midChild.height_lt
              rw [same] at *; omega) i inD)
      (parentInside V (subset_refl _))
      (fun v member =>
        ⟨fun supporter => absurd (parentAbove v member _ supporter).height_le
          (Nat.not_le.mpr targetChild.height_lt),
        fun supporter => absurd (parentAbove v member _ supporter).height_le
          (Nat.not_le.mpr siblingIsChild.height_lt)⟩)
    have vLe := guardLe V
    simp only [wb] at lowerBound
    constructor <;> omega
  · exact absurd rfl pNotTarget

open Models.ForkChoice in
/-- A finite-window margin makes a block heavier than a sibling, including the boost. -/
private theorem sibling_weight_lt_of_window_margin [DecidablePred (· ∈ J)]
    {since last n : Nat} {u : ValidatorIndex} {root : Root} {block parent : BeaconBlock preset fork}
    (membership : VotersInHeadWindow (e := e) block.parentRoot since last) (honest : u ∈ J)
    (after : since ≤ (e.world n).time) (time : (e.world n).time ≤ last)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock
      ((e.world n).state u))
    (lower : ((e.world n).state u).ParentsBelow)
    {head : ForkChoiceNode} {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit)
    (nodes : List ForkChoiceNode) (boosted : Option (Option Root)) (score : Nat)
    {sibling : Option Root}
    {current first finish shortLast : Slot} {epoch : Epoch}
    {members participants : Std.TreeSet ValidatorIndex}
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (parentFound : ((e.world n).state u).blocks[block.parentRoot]? = some parent)
    (descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨block.parentRoot, .pending⟩ = .ok true)
    (slotRead : ((e.world n).state u).getCurrentSlot config = .ok current)
    (epochRead : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (horizon : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked current 1 = .ok finish)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first finish =
      .ok members)
    (shortWindow : ((e.world n).state u).getCommitteesBetweenSlots head.root first shortLast =
      .ok participants)
    (shortBefore : shortLast ≤ finish)
    (siblingChild : sibling ∈ children (Store.view lower nodes) (some block.parentRoot))
    (distinct : sibling ≠ some root)
    (margin : stake (fun v => balanceAt state v.toNat) (Store.activeMembers state members) +
      score < 2 * weight (Store.voters state).insertNone (boostStake (balanceAt state) score)
        ((Store.view lower nodes).withBoost boosted) (some root) +
      stake (fun v => balanceAt state v.toNat)
        {v ∈ ((e.world n).state u).parentVotersOf state participants block parent | v ∈ J}) :
    weight (Store.voters state).insertNone (boostStake (balanceAt state) score)
        ((Store.view lower nodes).withBoost boosted) sibling <
      weight (Store.voters state).insertNone (boostStake (balanceAt state) score)
        ((Store.view lower nodes).withBoost boosted) (some root) := by
  classical
  have bound := Store.weight_add_weight_add_stake_le_stake_withBoost lower within nodes boosted
    score found rfl siblingChild distinct (window := Store.activeMembers state members)
    (fun i member => by
      have child : ∃ c, (Store.blockTree lower).IsChild c (some block.parentRoot) ∧
          i ∈ supporters (Store.voters state) (Store.view lower nodes) c := by
        rcases Finset.mem_union.mp member with first | second
        · exact ⟨_, Store.blockTree_isChild_iff.mpr ⟨block, found, rfl⟩, first⟩
        · exact ⟨_, (mem_children.mp siblingChild).2, second⟩
      obtain ⟨c, isChild, supporter⟩ := child
      have member := mem_window_of_mem_supporters membership honest after time reached
        lower headRead parentFound descends slotRead epochRead horizon firstOk lastOk window
        isChild supporter
      obtain ⟨below, validator, atIndex, active⟩ :=
        Store.active_of_mem_voters (Finset.mem_of_mem_filter _ supporter)
      have back := toNat_toUInt64_of_lt within below
      exact Store.mem_activeMembers.mpr ⟨member, validator, by simpa only [back] using atIndex,
        active⟩)
    (N := {v ∈ ((e.world n).state u).parentVotersOf state participants block parent | v ∈ J})
    (fun v member => by
      obtain ⟨inShort, validator, _⟩ := Store.mem_parentVotersOf.mp
        (Finset.mem_filter.mp member).1
      obtain ⟨entry, atIndex, _, active⟩ := validator
      exact Store.mem_activeMembers.mpr
        ⟨Store.mem_getCommitteesBetweenSlots_of_le shortWindow window shortBefore inShort,
          entry, atIndex, active⟩)
    (fun v member =>
      ⟨Store.not_mem_supporters_of_mem_parentVotersOf
        (Store.blockTree_isChild_iff.mpr ⟨block, found, rfl⟩) (Finset.mem_filter.mp member).1,
      Store.not_mem_supporters_of_mem_parentVotersOf (mem_children.mp siblingChild).2
        (Finset.mem_filter.mp member).1⟩)
  omega

/-- A receiver's ancestor parent agrees with the caller's parent or supplies a block collision. -/
public theorem parent_read_or_collision {caller receiver : Store preset fork}
    (callerReached : Store.Reachable config anchorState anchorBlock caller)
    (receiverReached : Store.Reachable config anchorState anchorBlock receiver)
    {parent : BeaconBlock preset fork} {parentRoot : Root} {head : ForkChoiceNode}
    (callerParentFound : caller.blocks[parentRoot]? = some parent)
    (parentSafe : receiver.isAncestor head ⟨parentRoot, .pending⟩ = .ok true) :
    receiver.blocks[parentRoot]? = some parent ∨ ∃ leftBlock rightBlock,
      Store.findBlockCollision caller receiver [parentRoot] =
        some (parentRoot, leftBlock, rightBlock) ∧ leftBlock ≠ rightBlock ∧
      Serialization.Ssz.SszType.hashTreeRoot leftBlock = .ok parentRoot ∧
      Serialization.Ssz.SszType.hashTreeRoot rightBlock = .ok parentRoot := by
  have parentRead := parentSafe
  unfold Store.isAncestor at parentRead
  obtain ⟨receiverParent, parentOk, _⟩ := bind_ok_iff.mp parentRead
  have receiverParentFound := Store.block_ok_iff.mp parentOk
  by_cases same : parent = receiverParent
  · exact .inl (same ▸ receiverParentFound)
  have searched : Store.findBlockCollision caller receiver [parentRoot] =
      some (parentRoot, parent, receiverParent) := by
    simp [Store.findBlockCollision, callerParentFound, receiverParentFound, same]
  have valid := Store.findBlockCollision_valid callerReached receiverReached searched
  exact .inr ⟨parent, receiverParent, searched, valid⟩

private theorem guarded_stake_le {state : BeaconState preset fork}
    {left right : Finset ValidatorIndex}
    (inside : ∀ v ∈ left, v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ right) :
    stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0) left ≤
    stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0) right := by
  classical
  apply Finset.sum_le_sum_of_ne_zero
  intro v member nonzero
  have active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
    by_contra absent
    simp [absent] at nonzero
  exact inside v member active

private theorem guarded_supporters_le [DecidablePred (· ∈ J)]
    {store : Store preset fork} {state source : BeaconState preset fork}
    {node : ForkChoiceNode} :
    stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0) {v ∈ store.supportersOf source node | v ∈ J} ≤
    stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0) {v ∈ store.supportersOf state node | v ∈ J} := by
  classical
  apply guarded_stake_le
  intro v member active
  obtain ⟨supported, honest⟩ := Finset.mem_filter.mp member
  have counted := Store.voteCountsFor_of_mem_supportersOf supported
  obtain ⟨entry, entryOk, indexEq⟩ := List.mem_map.mp (List.mem_toFinset.mp active)
  apply Finset.mem_filter.mpr
  refine ⟨?_, honest⟩
  simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨entry, ⟨entryOk, indexEq ▸ counted⟩, indexEq⟩

private theorem guarded_parentVoters_le [DecidablePred (· ∈ J)]
    {store : Store preset fork} {state source : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {block parent : BeaconBlock preset fork}
    (within : state.RegistryWithinLimit) :
    stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0)
      {v ∈ store.parentVotersOf source participants block parent | v ∈ J} ≤
    stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0)
      {v ∈ store.parentVotersOf state participants block parent | v ∈ J} := by
  classical
  apply guarded_stake_le
  intro v member active
  obtain ⟨member, honest⟩ := Finset.mem_filter.mp member
  obtain ⟨inCommittee, _, clean, vote⟩ := Store.mem_parentVotersOf.mp member
  obtain ⟨validator, found, isActive, unslashed⟩ :=
    (mem_unslashedActiveBalances_iff within).mp (List.mem_toFinset.mp active)
  exact Finset.mem_filter.mpr ⟨Store.mem_parentVotersOf.mpr
    ⟨inCommittee, ⟨validator, found, unslashed, isActive⟩, clean, vote⟩, honest⟩

/-- A source margin and approved drift give head ancestry or a collision at the caller's parent.

The voters below the parent lie in the head's window by the window-membership premise.

From Gloas, honest justified states' registries must stay within the limit through `last`. -/
public theorem ancestor_head_of_window_margin [DecidablePred (· ∈ J)]
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {last n call : Nat} {u : ValidatorIndex} {root : Root} {block parent : BeaconBlock preset fork}
    (membership : VotersInHeadWindow (e := e) block.parentRoot (e.world call).time last)
    (honest : u ∈ J) (time : (e.world n).time ≤ last)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (absent : AnchorParentAbsent (e := e) last)
    {head : ForkChoiceNode} {state : BeaconState preset fork}
    {current first finish shortLast : Slot} {epoch : Epoch}
    {members participants : Std.TreeSet ValidatorIndex} {nodes : List ForkChoiceNode}
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (stateRead : ((e.world n).state u).checkpointState
      ((e.world n).state u).justifiedCheckpoint = .ok state)
    (tree : ((e.world n).state u).getFilteredNodeTree config = .ok nodes)
    (found : ((e.world n).state u).blocks[root]? = some block)
    {caller : ValidatorIndex}
    (callerHonest : caller ∈ J) (callerTime : (e.world call).time ≤ last)
    (later : (e.world call).time ≤ (e.world n).time)
    {source : BeaconState preset fork} {shift : Nat}
    (drift : WindowMarginDrift (e := e) call last source shift)
    (callerParentFound : ((e.world call).state caller).blocks[block.parentRoot]? = some parent)
    (slotRead : ((e.world n).state u).getCurrentSlot config = .ok current)
    (epochRead : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (horizon : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked current 1 = .ok finish)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first finish =
      .ok members)
    (shortWindow : ((e.world n).state u).getCommitteesBetweenSlots head.root first shortLast =
      .ok participants)
    (shortLastOk : subChecked block.slot 1 = .ok shortLast)
    (route : (((e.world n).state u).isAncestor
        ⟨((e.world n).state u).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true) ∨
      ((⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes ∧
        ((e.world n).state u).isAncestor head
          ⟨block.parentRoot, .pending⟩ = .ok true ∧
        ∃ maximum sourceMaximum sourceScore,
      ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root state first finish =
        .ok maximum ∧
      ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root source first finish =
        .ok sourceMaximum ∧
      computeProposerScore config source = .ok sourceScore ∧
      sourceMaximum.toNat + sourceScore.toNat + shift <
      2 * Models.stake (fun v =>
        if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
        then balanceAt source v.toNat else 0)
        {v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩ | v ∈ J} +
      Models.stake (fun v =>
        if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
        then balanceAt source v.toNat else 0)
        {v ∈ ((e.world n).state u).parentVotersOf source participants block parent | v ∈ J}))
    (scoreOk : computeProposerScore config state = .ok (score : Gwei))
    (registries : .glamsterdam ≤ fork → ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
      ∀ state : BeaconState preset fork, ((e.world k).state w).checkpointState
        ((e.world k).state w).justifiedCheckpoint = .ok state → state.RegistryWithinLimit) :
    ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true ∨
    HonestCollision (e := e) last := by
  classical
  rcases route with justifiedAbove |
    ⟨viable, descends, maximum, sourceMaximum, sourceScore, maximumOk, sourceMaximumOk,
      sourceScoreOk, sourceMargin⟩
  · obtain ⟨justified, justifiedKnown⟩ := Store.filterNodeTree_known tree
    exact .inl (Store.isAncestor_trans justifiedKnown found
      (Store.isAncestor_getHead headRead) justifiedAbove)
  let store := (e.world n).state u
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  have callerReached := e.reachable
    (fun w member => (anchored w member) ▸ Store.Reachable.anchor anchorStore)
    call caller callerHonest
  rcases parent_read_or_collision callerReached reached.reachable callerParentFound descends with
    parentFound | collision
  swap
  · obtain ⟨leftBlock, rightBlock, searched, _, _, _⟩ := collision
    exact .inr ⟨caller, callerHonest, u, honest, call, n, callerTime, time, block.parentRoot,
      (block.parentRoot, leftBlock, rightBlock), searched⟩
  left
  have transported := drift u honest n head state score sourceScore first finish maximum
    sourceMaximum later time headRead stateRead scoreOk sourceScoreOk maximumOk sourceMaximumOk
    {v ∈ store.supportersOf source ⟨root, .pending⟩ | v ∈ J}
    {v ∈ store.parentVotersOf source participants block parent | v ∈ J}
    (fun _ member => (Finset.mem_filter.mp member).2)
    (fun _ member => (Finset.mem_filter.mp member).2)
  -- The justified state's registry is within the limit: by its type before Gloas.
  have within : state.RegistryWithinLimit := by
    by_cases gloas : .glamsterdam ≤ fork
    · exact registries gloas u honest n time state stateRead
    · exact BeaconState.registryWithinLimit_of_lt (Nat.lt_of_not_le gloas) state
  have supportTransport := guarded_supporters_le (J := J) (store := store)
    (state := state) (source := source) (node := ⟨root, .pending⟩)
  have parentTransport := guarded_parentVoters_le (J := J) (store := store)
    (source := source) (participants := participants) (block := block) (parent := parent) within
  have windowBound := Store.stake_le_computeCommitteeWeightBetweenSlots window maximumOk
    (fun _ member => Store.mem_activeMembers.mp member)
  have margin : Models.stake (fun v => balanceAt state v.toNat)
        (Store.activeMembers state members) + score.toNat <
      2 * Models.stake (fun v =>
        if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0)
        {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J} +
      Models.stake (fun v =>
        if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0)
        {v ∈ store.parentVotersOf state participants block parent | v ∈ J} := by
    dsimp only at transported
    dsimp only [store] at transported supportTransport parentTransport ⊢
    omega
  have lower := reached.reachable.parentsBelow anchorSlot (absent u honest n time)
  have shortBefore := reached.previousBlockSlot_le_previousCurrentSlot anchorSlot
    found slotRead shortLastOk lastOk
  have boostBound : store.boostScore config ≤ score.toNat := by
    dsimp only [store]
    simp only [Store.boostScore]
    split
    · exact Nat.zero_le _
    · simp [Store.getProposerScore, stateRead, scoreOk, bind, Except.bind]
  by_cases gloas : .glamsterdam ≤ fork
  · -- From Gloas the head's walk passes the parent's pending node, where the path bound applies.
    have headDescends : store.isAncestor ⟨head.root, .pending⟩ ⟨block.parentRoot, .pending⟩ =
        .ok true := by
      rw [← Store.isAncestor_getHead_root headRead]
      exact descends
    obtain ⟨positiveS, bound⟩ := sibling_bound_of_window_margin (J := J) lower gloas within
      (nodes := nodes) found parentFound
      (fun c low ne i member => mem_window_of_mem_nodeSupporters membership honest later time
        reached lower gloas headRead parentFound headDescends slotRead epochRead horizon firstOk
        lastOk window low ne member)
      (fun v member => Store.mem_getCommitteesBetweenSlots_of_le shortWindow window shortBefore
        member)
      ((Store.boostScoreOfGloas_le_boostScore gloas).trans boostBound) margin
    -- A supporter's counted vote puts the block before the current slot.
    obtain ⟨supporter, supporterIn, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (Nat.pos_iff_ne_zero.mp positiveS)
    have rootEarly := reached.forwardReachable.votesHaveOrigins.slot_lt_of_voteCountsFor
      slotRead found (Store.voteCountsFor_of_mem_supportersOf
        (Finset.mem_filter.mp supporterIn).1)
    have parentEarly := lower _ block parent found parentFound
    have currentFits := UInt64.toNat_lt current
    have rootNat := UInt64.lt_iff_toNat_lt.mp rootEarly
    have parentNat := UInt64.lt_iff_toNat_lt.mp parentEarly
    -- The three nodes of the path, from the parent's pending node to the block's.
    set start : Option Root × Models.ForkChoice.Status := (some block.parentRoot, none)
    set mid : Option Root × Models.ForkChoice.Status :=
      (some block.parentRoot, some (Store.parentPayloadStatus block parent == .full))
    set target : Option Root × Models.ForkChoice.Status := (some root, none)
    have toMid : (Store.nodeTree lower).parent target = mid :=
      Store.nodeTree_parent_of found parentFound
    have toStart : (Store.nodeTree lower).parent mid = start :=
      Models.ForkChoice.BlockTree.payloadTree_parent_some _ _
    have onPath : (Store.nodeTree lower).Ancestor start target := ⟨2, by simp [toMid, toStart]⟩
    have noDecision : ∀ x ∈ nodes, (Store.nodeTree lower).Ancestor start x.toModel →
        (Store.nodeTree lower).Ancestor x.toModel target →
        store.isPreviousSlotPayloadDecision config x = .ok false := by
      intro x _ low high
      obtain ⟨xRoot, xStatus⟩ := x
      rcases eq_of_path_two toMid toStart low high with same | same | same <;>
        simp only [ForkChoiceNode.toModel, start, mid, target, Prod.mk.injEq,
          Option.some.injEq] at same <;> obtain ⟨rfl, statusEq⟩ := same
      · exact Store.isPreviousSlotPayloadDecision_eq_false parentFound slotRead (by omega)
          (.inl (PayloadStatus.toStatus_injective statusEq))
      · exact Store.isPreviousSlotPayloadDecision_eq_false parentFound slotRead (by omega)
          (.inr (by omega))
      · exact Store.isPreviousSlotPayloadDecision_eq_false found slotRead (by omega)
          (.inl (PayloadStatus.toStatus_injective statusEq))
    -- The block descends from the justified node; when they coincide, the head descends from it.
    have closed := Store.filterNodeTree_closed (T := Store.nodeTree lower) (·.toModel) tree
      fun _ _ _ ok _ mem => Store.isChild_of_mem_getNodeChildren gloas ok mem
    have rootBelow : (Store.nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none)
        target := (closed _ viable).1
    by_cases atJustified : store.justifiedCheckpoint.root = root
    · have up := Store.isAncestor_getHead headRead
      rw [atJustified] at up
      exact up
    have justifiedAbove : (Store.nodeTree lower).Ancestor
        (some store.justifiedCheckpoint.root, none) start := by
      rcases rootBelow.eq_or_parent with same | up
      · exact absurd (Option.some.inj (Prod.mk.inj same).1) atJustified
      rw [toMid] at up
      rcases up.eq_or_parent with same | up
      · simp [mid] at same
      rwa [toStart] at up
    have nonempty : nodes.isEmpty = false := by
      cases nodes with
      | nil => cases viable
      | cons _ _ => rfl
    have walk : store.getHeadFrom config store.justifiedTally nodes
        ⟨store.justifiedCheckpoint.root, .pending⟩ = .ok head := by
      simpa [Store.getHead, tree, nonempty, bind, Except.bind] using headRead
    have parentBelowHead : (Store.nodeTree lower).Ancestor start head.toModel :=
      (Store.isAncestor_iff_of_gloas (lower := lower) gloas parentFound descends).mp rfl
    have cut := Store.getHeadFrom_of_visited (middle := ⟨block.parentRoot, .pending⟩) lower gloas
      parentBelowHead walk justifiedAbove
    exact Store.isAncestor_getHeadFrom_of_sibling_bound (start := ⟨block.parentRoot, .pending⟩)
      lower gloas tree stateRead viable
      justifiedAbove onPath noDecision
      (fun _ _ _ _ _ _ low isChild siblingIsChild path distinct =>
        ⟨fun _ => (bound _ _ _ low isChild siblingIsChild path distinct).1,
          (bound _ _ _ low isChild siblingIsChild path distinct).2⟩) cut
  have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
  have pending := Store.getHead_pending before headRead
  have pendingHead : (⟨head.root, .pending⟩ : ForkChoiceNode) = head := by
    cases head
    simp_all only
  rw [← pendingHead] at descends
  -- The visited parent makes the head known.
  obtain ⟨headBlock, headKnown, _⟩ := Store.slot_le_of_isAncestor parentFound descends
  have supportBound := honest_supporters_le_weight (J := J) lower within found nodes
  have boostedBound := Models.ForkChoice.weight_withBoost
    (V := Store.voters state) (w := balanceAt state) (G := Store.view lower nodes)
    store.boostedRoot (store.boostScore config) (some root)
  have guarded (voters : Finset ValidatorIndex) :
      Models.stake (fun v =>
        if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0) voters ≤
      Models.stake (fun v => balanceAt state v.toNat) voters := by
    apply Finset.sum_le_sum
    intro v _
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  have supportGuard := guarded
    {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J}
  have parentGuard := guarded
    {v ∈ store.parentVotersOf state participants block parent | v ∈ J}
  have modelMargin : Models.stake (fun v => balanceAt state v.toNat)
        (Store.activeMembers state members) + store.boostScore config <
      2 * Models.ForkChoice.weight (Store.voters state).insertNone
        (Models.ForkChoice.boostStake (balanceAt state) (store.boostScore config))
        ((Store.view lower nodes).withBoost store.boostedRoot) (some root) +
      Models.stake (fun v => balanceAt state v.toNat)
        {v ∈ store.parentVotersOf state participants block parent | v ∈ J} := by
    dsimp only [store] at margin boostBound boostedBound supportGuard parentGuard ⊢
    omega
  have ghostEq := Store.getHead_eq_ghost_withBoost lower before stateRead tree headRead
  have ancestry := (Store.filterNodeTree_ancestor (lower := lower) before tree _ viable).1
  have child := (Store.blockTree_isChild_iff (lower := lower)).mpr ⟨block, found, rfl⟩
  have inView : some root ∈ (Store.view lower nodes).blocks := by
    simp only [Store.view, Models.ForkChoice.View.mem_ofBlocks, List.mem_toFinset, List.mem_map]
    exact ⟨_, ⟨_, viable, rfl⟩, .refl _⟩
  have result : (Store.blockTree lower).Ancestor (some root) (some head.root) := by
    rcases ancestry.eq_or_parent with same | above
    · rw [← same, ← ghostEq]
      exact Models.ForkChoice.ancestor_ghost _ _ _ _ _
    · rw [Store.blockTree_parent_of found] at above
      have visited := (Store.isAncestor_iff (lower := lower) parentFound rfl descends).mp rfl
      rw [← ghostEq]
      apply ancestor_ghost_of_visited_parent _ _
        ((Store.view lower nodes).withBoost store.boostedRoot) _
        (Models.ForkChoice.mem_children.mpr ⟨inView, child⟩) above
        (ghostEq ▸ visited)
      intro sibling member distinct
      exact sibling_weight_lt_of_window_margin membership honest later time reached
        lower within nodes store.boostedRoot
        (store.boostScore config) headRead found parentFound descends slotRead
        epochRead horizon firstOk lastOk window shortWindow shortBefore member distinct modelMargin
  have answer := Store.isAncestor_of_blockTree_ancestor (lower := lower) headKnown
    found result
  obtain ⟨headRoot, status⟩ := head
  simp only at pending
  subst status
  exact answer

/-- Held-state finality supplies the source bound at the store's realized checkpoint.

The two ancestry reads remain separate inputs; this does not bound cached-output finality. -/
private theorem registry_of_honest_block {store : Store preset fork}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    {source base cached : BeaconState preset fork}
    {root sourceRoot : Root} {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    (startOk : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch =
      .ok start)
    (walk : store.getCheckpointBlock root
      store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root)
    (found : store.blocks[root]? = some block)
    (bound : start ≤ max block.slot target)
    (baseFound : store.blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceWalk : store.getCheckpointBlock sourceRoot
      store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root)
    (sourceBlockFound : store.blocks[sourceRoot]? = some sourceBlock)
    (sourceFound : store.blockStates[sourceRoot]? = some source)
    (sourceBound : start ≤ sourceBlock.slot)
    (finite : store.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH) :
    ∀ epoch position, isActiveAt source epoch position = true →
      ∃ validator, cached.validators.data[position]? = some validator := by
  have finalized := (reached.reachable.ordered_finalized anchorInvariant).2 sourceFound
  have identity : lookaheadState config checks source source.slot = .ok source := by
    simp [lookaheadState, pure, Except.pure]
  have sourceStart : start ≤ max sourceBlock.slot source.slot := by
    rw [UInt64.le_iff_toNat_le, toNat_max]
    exact Nat.le_trans (UInt64.le_iff_toNat_le.mp sourceBound) (Nat.le_max_left _ _)
  exact registry_of_checkpointPrefix anchorSlot reached anchorInvariant positive
    walk found startOk bound baseFound advanced identity sourceWalk
    sourceBlockFound sourceStart sourceFound finalized finite

/-- An invariant state's three old checkpoints are below the far-future epoch. -/
private theorem oldCheckpoints_finite {state : BeaconState preset fork}
    (holds : Invariant state) :
    state.currentJustifiedCheckpoint.epoch < FAR_FUTURE_EPOCH ∧
      state.previousJustifiedCheckpoint.epoch < FAR_FUTURE_EPOCH ∧
      state.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH := by
  have settled := UInt64.le_iff_toNat_le.mp holds.settled
  rw [getPreviousEpoch_toNat] at settled
  have current := (getCurrentEpoch state).toNat_lt
  have previous := UInt64.le_iff_toNat_le.mp holds.ordered.2
  have finalized := UInt64.le_iff_toNat_le.mp holds.ordered.1
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  simp only [UInt64.lt_iff_toNat_lt, far]
  omega

/-- Exact checkpoint origins preserve finite finality from a finite anchor epoch. -/
private theorem finalized_finite_of_anchor {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (anchorFinite : getCurrentEpoch anchorState < FAR_FUTURE_EPOCH) :
    store.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH := by
  rcases reached.finalized_origins _ (.inl rfl) with
    ⟨_, _, same⟩ | ⟨_, state, held, same⟩ | ⟨_, state, pulled, held, run, same⟩
  · simpa only [same] using anchorFinite
  · simpa only [same] using (oldCheckpoints_finite ((reached.ordered sound).2 held)).2.2
  · rw [same]
    have old := oldCheckpoints_finite ((reached.ordered sound).2 held)
    rcases processJustificationAndFinalization_ok run with rfl | ⟨_, _, _, weighed⟩
    · exact old.2.2
    · rcases (weighJustificationAndFinalization_checkpoints weighed).2.2.1 with same | same | same
      · exact same ▸ old.2.2
      · exact same ▸ old.2.1
      · exact same ▸ old.1

/-- A held block with a checked successor excludes the far-future anchor epoch. -/
private theorem anchor_finite_of_parentNext {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    {parent : BeaconBlock preset fork} {root : Root} {first : Slot}
    (parentFound : store.blocks[root]? = some parent)
    (anchorParentAbsent : store.blocks[anchorBlock.parentRoot]? = none)
    (parentNext : addChecked parent.slot 1 = .ok first) :
    getCurrentEpoch anchorState < FAR_FUTURE_EPOCH := by
  obtain ⟨_, _, anchorFound⟩ := reached.anchor_known
  have anchorLe := reached.orphans_le (UInt64.le_of_eq anchorSlot)
    anchorFound anchorParentAbsent parentFound
  have step := (addChecked_ok_iff.mp parentNext).1
  have le := UInt64.le_iff_toNat_le.mp anchorLe
  have epoch := getCurrentEpoch_toNat_le_slot anchorState
  rw [anchorSlot] at le
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  rw [UInt64.lt_iff_toNat_lt, far]
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [one] at step
  omega

/-- An actual lookahead preserves the run relation in both slot branches. -/
private theorem runKept_lookahead {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) : RunKept state after := by
  unfold lookaheadState at run
  split at run
  · exact runKept_processSlots (mapError_ok_iff.mp run)
  · cases run
    exact RunKept.refl _

/-- A growing registry retains every index read in the earlier state. -/
private theorem registry_of_runKept {state after : BeaconState preset fork}
    (run : RunKept state after) {epoch : Epoch} {position : Nat}
    (active : isActiveAt state epoch position = true) :
    ∃ validator, after.validators.data[position]? = some validator := by
  obtain ⟨validator, held, _⟩ := isActiveAt_eq_true_iff.mp active
  have inside := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp held).1 run.grows
  exact ⟨after.validators.data[position], Array.getElem?_eq_getElem inside⟩

/-- A validator active in a held block's state at its epoch has its index in a checkpoint state.

The store is built with one setting of the checks.

The two blocks read one checkpoint at its epoch, and the state's finality is not past it.

The checkpoint state is the receiver's state processed to the start of its epoch, or later. -/
public theorem _root_.EthLib.Consensus.Store.ForwardReachableWith.registered_of_shared_checkpoint
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorInvariant : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH)
    {checkpoint : Checkpoint} {root sourceRoot : Root}
    {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    {source base cached : BeaconState preset fork}
    (walk : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (bound : start ≤ max block.slot target)
    (baseFound : store.blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceWalk : store.getCheckpointBlock sourceRoot checkpoint.epoch = .ok checkpoint.root)
    (sourceBlockFound : store.blocks[sourceRoot]? = some sourceBlock)
    (sourceFound : store.blockStates[sourceRoot]? = some source)
    (finalized : source.finalizedCheckpoint.epoch ≤ checkpoint.epoch)
    {position : Nat} {validator : Validator}
    (registered : source.validators.data[position]? = some validator)
    (active : isActiveValidator validator (computeEpochAtSlot preset sourceBlock.slot) = true) :
    position < cached.validators.data.size := by
  by_cases atBlock : start ≤ sourceBlock.slot
  · -- The pending tail at the checkpoint's epoch carries the position into the receiver.
    have finite : checkpoint.epoch < FAR_FUTURE_EPOCH := by
      have activeBound := UInt64.lt_iff_toNat_lt.mp
        (by simpa [isActiveValidator] using active : _ ∧ _).2
      have exitBound := validator.exitEpoch.toNat_lt
      have epochLe := epoch_le_of_slot_le (preset := preset) _ _ (UInt64.le_iff_toNat_le.mp atBlock)
      rw [computeEpochAtSlot_computeStartSlotAtEpoch positive startOk] at epochLe
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      rw [UInt64.lt_iff_toNat_lt, far]
      omega
    have identity : lookaheadState config checks source source.slot = .ok source := by
      simp [lookaheadState, pure, Except.pure]
    have sourceStart : start ≤ max sourceBlock.slot source.slot := by
      rw [UInt64.le_iff_toNat_le, toNat_max]
      exact Nat.le_trans (UInt64.le_iff_toNat_le.mp atBlock) (Nat.le_max_left _ _)
    obtain ⟨_, inside⟩ := registry_of_checkpointPrefix anchorSlot reached anchorInvariant positive
      walk found startOk bound baseFound advanced identity sourceWalk
      sourceBlockFound sourceStart sourceFound finalized finite _ position
      (isActiveAt_eq_true_iff.mpr ⟨validator, registered, active⟩)
    exact (Array.getElem?_eq_some_iff.mp inside).1
  · -- A source block before the epoch's start is the checkpoint block itself.
    have rootEq : sourceRoot = checkpoint.root := by
      simpa [Store.getCheckpointBlock, startOk, Except.mapError,
        Store.getAncestor_of_le (node := ⟨sourceRoot, .pending⟩) sourceBlockFound
          (UInt64.le_of_lt (UInt64.not_le.mp atBlock)),
        bind, Except.bind, pure, Except.pure] using sourceWalk
    rw [rootEq] at sourceFound
    obtain ⟨boundary, boundaryRun, receiverRun⟩ := relation_of_checkpoint_lookahead
      RunKept RunKept.refl (fun one two => one.trans two)
      (fun ok => runKept_stateTransition ok)
      (fun slots bound ok => runKept_of_processSlots_of_stateTransition slots bound ok)
      (fun ok => runKept_processSlots ok)
      anchorSlot reached walk found startOk bound sourceFound baseFound advanced
    exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp registered).1
      ((runKept_lookahead boundaryRun).grows.trans receiverRun.grows)

/-- A window at the justified root has successful registry reads in its actual cached state.

The cached state may process empty slots beyond the block at that root. -/
private theorem registry_of_justified_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    (heldWithin : HeldRegistriesWithinLimit ((e.world n).state u))
    {head : ForkChoiceNode} {state : BeaconState preset fork}
    {first finish : Slot} {members : Std.TreeSet ValidatorIndex}
    (same : head.root = ((e.world n).state u).justifiedCheckpoint.root)
    (cached : ((e.world n).state u).checkpointState
      ((e.world n).state u).justifiedCheckpoint = .ok state)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first finish =
      .ok members) :
    ∀ v ∈ members, ∃ validator, validatorAt state v = .ok validator := by
  obtain ⟨base, start, baseFound, _, advanced⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp cached)
  have held : ((e.world n).state u).blockState head.root = .ok base :=
    Store.blockState_ok_iff.mpr (same ▸ baseFound)
  intro v member
  obtain ⟨epoch, active⟩ := active_of_committeeWindow (heldWithin _ _ (same ▸ baseFound)) held
    window v member
  obtain ⟨validator, found⟩ := registry_of_runKept (runKept_lookahead advanced) active
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- Genesis finality supplies the actual head and cache walks through the anchor. -/
private theorem registry_of_genesis_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    (heldWithin : HeldRegistriesWithinLimit ((e.world n).state u))
    {head : ForkChoiceNode} {headBlock : BeaconBlock preset fork}
    {headState state : BeaconState preset fork} {first last : Slot}
    {members : Std.TreeSet ValidatorIndex}
    (genesis : ((e.world n).state u).finalizedCheckpoint.epoch = GENESIS_EPOCH)
    (unknown : ((e.world n).state u).blocks[anchorBlock.parentRoot]? = none)
    (headFound : ((e.world n).state u).blocks[head.root]? = some headBlock)
    (headStateFound : ((e.world n).state u).blockStates[head.root]? = some headState)
    (cached : ((e.world n).state u).checkpointState
      ((e.world n).state u).justifiedCheckpoint = .ok state)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok members) :
    ∀ v ∈ members, ∃ validator, validatorAt state v = .ok validator := by
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  have atAnchor : ((e.world n).state u).finalizedCheckpoint.epoch ≤
      getCurrentEpoch anchorState := by rw [genesis]; exact UInt64.zero_le
  obtain ⟨epochEq, hashed⟩ := reached.reachable.finalized_eq_anchor_of_epoch_le atAnchor
  obtain ⟨base, target, baseFound, _, advanced⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp cached)
  obtain ⟨block, found⟩ := reached.reachable.known_of_blockState baseFound
  have startOk : computeStartSlotAtEpoch preset
      ((e.world n).state u).finalizedCheckpoint.epoch = .ok 0 := by
    simp [genesis, GENESIS_EPOCH, computeStartSlotAtEpoch, mulChecked]
  have walk := reached.reachable.getCheckpointBlock_anchor anchorSlot boundary unknown found hashed
  have headWalk := reached.reachable.getCheckpointBlock_anchor anchorSlot boundary unknown
    headFound hashed
  rw [← epochEq] at walk headWalk
  have inside := registry_of_honest_block reached anchorInvariant
    (UInt64.le_of_eq anchorSlot) positive startOk walk found
    UInt64.zero_le baseFound advanced headWalk headFound headStateFound
    UInt64.zero_le (by rw [genesis]; decide)
  intro v member
  obtain ⟨epoch, active⟩ := active_of_committeeWindow (heldWithin _ _ headStateFound)
    (Store.blockState_ok_iff.mpr headStateFound) window v member
  obtain ⟨validator, found⟩ := inside epoch v.toNat active
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- A nonidentity head supplies registry containment through its realized finalized boundary.

A head at the finalized root uses prefix growth, even when its block precedes the boundary. -/
private theorem registry_of_nongenesis_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    (heldWithin : HeldRegistriesWithinLimit ((e.world n).state u))
    (walk : ((e.world n).state u).getCheckpointBlock
      ((e.world n).state u).justifiedCheckpoint.root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    {head : ForkChoiceNode} {headState state : BeaconState preset fork}
    {first last : Slot} {members : Std.TreeSet ValidatorIndex}
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (different : head.root ≠ ((e.world n).state u).justifiedCheckpoint.root)
    (notGenesis : ((e.world n).state u).finalizedCheckpoint.epoch ≠ GENESIS_EPOCH)
    (headStateFound : ((e.world n).state u).blockStates[head.root]? = some headState)
    {parent : BeaconBlock preset fork} {parentRoot : Root}
    (parentFound : ((e.world n).state u).blocks[parentRoot]? = some parent)
    (unknown : ((e.world n).state u).blocks[anchorBlock.parentRoot]? = none)
    (parentNext : addChecked parent.slot 1 = .ok first)
    (cached : ((e.world n).state u).checkpointState
      ((e.world n).state u).justifiedCheckpoint = .ok state)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok members) :
    ∀ v ∈ members, ∃ validator, validatorAt state v = .ok validator := by
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  have viable : ((e.world n).state u).isViableLeaf config head = .ok true := by
    rcases Store.getHead_viable headRead with viable | ⟨_, same⟩
    · exact viable
    · exact False.elim (different (congrArg ForkChoiceNode.root same))
  have headWalk := (Store.isViableLeaf_finalized viable).resolve_left notGenesis
  obtain ⟨headBlock, headFound⟩ := reached.reachable.known_of_blockState headStateFound
  obtain ⟨base, target, baseFound, targetOk, advanced⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp cached)
  obtain ⟨block, found⟩ := reached.reachable.known_of_blockState baseFound
  have ordered := reached.reachable.finalized_le_justified anchorInvariant
  obtain ⟨start, boundaryBlock, startOk, boundaryFound, _, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock walk
  obtain ⟨boundaryBase, boundaryBaseFound, _, _⟩ :=
    reached.reachable.blockStatesFromParents boundaryFound
  have bound : start ≤ max block.slot target := by
    have le := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (UInt64.le_iff_toNat_le.mp ordered)
    rw [← (computeStartSlotAtEpoch_ok_iff.mp startOk).2,
      ← (computeStartSlotAtEpoch_ok_iff.mp targetOk).2] at le
    rw [UInt64.le_iff_toNat_le, toNat_max]
    exact Nat.le_trans le (Nat.le_max_right _ _)
  by_cases same : head.root = ((e.world n).state u).finalizedCheckpoint.root
  · rw [same, boundaryBaseFound, Option.some.injEq] at headStateFound
    subst headState
    obtain ⟨boundaryState, boundaryRun, run⟩ := relation_of_checkpoint_lookahead
      RunKept RunKept.refl (fun one two => one.trans two)
      (fun ok => runKept_stateTransition ok)
      (fun slotsOk le ok => runKept_of_processSlots_of_stateTransition slotsOk le ok)
      (fun ok => runKept_processSlots ok) (UInt64.le_of_eq anchorSlot) reached walk found
      startOk bound boundaryBaseFound baseFound advanced
    intro v member
    obtain ⟨epoch, active⟩ := active_of_committeeWindow
      (heldWithin _ _ (same ▸ boundaryBaseFound))
      (Store.blockState_ok_iff.mpr (same ▸ boundaryBaseFound)) window v member
    obtain ⟨validator, held⟩ := registry_of_runKept
      ((runKept_lookahead boundaryRun).trans run) active
    exact ⟨validator, validatorAt_ok_iff.mpr held⟩
  have headBound : start ≤ headBlock.slot := by
    by_contra below
    apply same
    simpa [Store.getCheckpointBlock, startOk, Except.mapError,
      Store.getAncestor_of_le (node := ⟨head.root, .pending⟩) headFound
        (UInt64.le_of_lt (UInt64.not_le.mp below)), bind, Except.bind,
      pure, Except.pure] using headWalk
  have finite := finalized_finite_of_anchor reached.reachable anchorInvariant
    (anchor_finite_of_parentNext reached.reachable anchorSlot parentFound unknown parentNext)
  have inside := registry_of_honest_block reached anchorInvariant
    (UInt64.le_of_eq anchorSlot) positive startOk walk found
    bound baseFound advanced headWalk headFound headStateFound headBound finite
  intro v member
  obtain ⟨epoch, active⟩ := active_of_committeeWindow (heldWithin _ _ headStateFound)
    (Store.blockState_ok_iff.mpr headStateFound) window v member
  obtain ⟨validator, held⟩ := inside epoch v.toNat active
  exact ⟨validator, validatorAt_ok_iff.mpr held⟩

/-- The actual head selects identity, genesis or finalized-prefix registry transport. -/
private theorem registry_of_head_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    (heldWithin : HeldRegistriesWithinLimit ((e.world n).state u))
    (walk : ((e.world n).state u).getCheckpointBlock
      ((e.world n).state u).justifiedCheckpoint.root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    {head : ForkChoiceNode} {state : BeaconState preset fork}
    {first last : Slot} {members : Std.TreeSet ValidatorIndex}
    {parent : BeaconBlock preset fork} {parentRoot : Root}
    (parentFound : ((e.world n).state u).blocks[parentRoot]? = some parent)
    (unknown : ((e.world n).state u).blocks[anchorBlock.parentRoot]? = none)
    (parentNext : addChecked parent.slot 1 = .ok first)
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (cached : ((e.world n).state u).checkpointState
      ((e.world n).state u).justifiedCheckpoint = .ok state)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok members) :
    ∀ v ∈ members, ∃ validator, validatorAt state v = .ok validator := by
  by_cases same : head.root = ((e.world n).state u).justifiedCheckpoint.root
  · exact registry_of_justified_window anchorStore anchored honest heldWithin same cached window
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  obtain ⟨base, _, baseFound, _, _⟩ := e.checkpointStates_fixedChecks anchorStore anchored honest
    (Store.checkpointState_ok_iff.mp cached)
  obtain ⟨justified, justifiedFound⟩ := reached.reachable.known_of_blockState baseFound
  obtain ⟨headBlock, headFound, _⟩ := Store.slot_le_of_isAncestor justifiedFound
    (Store.isAncestor_getHead headRead)
  obtain ⟨headState, headStateFound, _, _⟩ := reached.reachable.blockStatesFromParents headFound
  by_cases genesis : ((e.world n).state u).finalizedCheckpoint.epoch = GENESIS_EPOCH
  · exact registry_of_genesis_window anchorStore anchored anchorInvariant anchorSlot boundary
      positive honest heldWithin genesis unknown headFound headStateFound cached window
  exact registry_of_nongenesis_window anchorStore anchored anchorInvariant anchorSlot positive
    honest heldWithin walk headRead same genesis headStateFound parentFound unknown parentNext
    cached window

/-- Held-state flags suffice for a cached checkpoint through its fixed-check lookahead origin. -/
public theorem Execution.notSlashed_checkpointState {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u : ValidatorIndex} (honest : u ∈ J) {n : ℕ}
    (flags : ∀ (root : Root) (base : BeaconState preset fork),
      ((e.world n).state u).blockStates[root]? = some base →
      ∀ v ∈ J, (slashedFlagAt base v.toNat).getD false = false)
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (read : ((e.world n).state u).checkpointState checkpoint = .ok state) :
    ∀ v ∈ J, (slashedFlagAt state v.toNat).getD false = false := by
  obtain ⟨base, slot, stored, _, advanced⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp read)
  intro v member
  exact (notSlashed_lookahead advanced v).mpr (flags checkpoint.root base stored v member)

/-- Equal-rank honest latest votes agree, even across different stores.

From Gloas the rank is the slot. -/
public theorem Execution.latest_eq_of_rank_eq (slots : 0 < config.SLOT_DURATION_MS)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J)
    {n k : ℕ} {first second : LatestMessage fork}
    (firstOk : ((e.world n).state u).latestMessages[v]? = some first)
    (secondOk : ((e.world k).state w).latestMessages[v]? = some second)
    (rank : first.rank = second.rank) : first = second := by
  obtain ⟨a, firstMessage, seenFirst, rfl, signedFirst, firstOrigin⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller firstOk
  obtain ⟨b, secondMessage, seenSecond, rfl, signedSecond, secondOrigin⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored receiver secondOk
  have epoch : a.data.target.epoch = b.data.target.epoch := by
    by_cases gloas : .glamsterdam ≤ fork
    · -- Equal slots put both targets in the epoch of that slot.
      have slotEq : a.data.slot = b.data.slot := by
        simpa [LatestMessage.rank, LatestMessage.ofAttestation, gloas] using rank
      rw [firstOrigin.targetEpoch, secondOrigin.targetEpoch, slotEq]
    · simpa [LatestMessage.rank, LatestMessage.ofAttestation, gloas] using rank
  have same := Execution.data_eq_of_signed_of_target_epoch slots
    (e.view_subset_sent n u seenFirst) (e.view_subset_sent k w seenSecond)
    signedFirst signedSecond honest epoch
  simp only [LatestMessage.ofAttestation, same]

/-- A nonempty caller range supplies arithmetic for the receiver's full-window maximum.

The receiver's own finalized checkpoint must be on the chain of its own justified checkpoint.

From Gloas, honest registries must stay within the limit through `time`. -/
public theorem receiver_fullMaximum_of_head_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {time : Nat}
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (registries : .glamsterdam ≤ fork → HonestRegistriesWithinLimit (e := e) time)
    (absent : AnchorParentAbsent (e := e) time)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : Nat}
    (callerTime : (e.world n).time ≤ time) (inTime : (e.world k).time ≤ time)
    (finalizedRead : ((e.world k).state w).getCheckpointBlock
      ((e.world k).state w).justifiedCheckpoint.root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root)
    {head : ForkChoiceNode} {state source : BeaconState preset fork} {callerHead : Root}
    {parent : BeaconBlock preset fork} {parentRoot : Root}
    {current first last finish : Slot}
    {window : Std.TreeSet ValidatorIndex} {maximum : Gwei}
    (parentOk : ((e.world n).state u).block parentRoot = .ok parent)
    (parentSafe : ((e.world k).state w).isAncestor head ⟨parentRoot, .pending⟩ = .ok true)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (cached : ((e.world k).state w).checkpointState
      ((e.world k).state w).justifiedCheckpoint = .ok state)
    (lastOk : subChecked current 1 = .ok finish)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first finish =
      .ok window)
    (nonempty : first ≤ last)
    (read : ((e.world n).state u).computeCommitteeWeightBetweenSlots callerHead source
      first last = .ok maximum) :
    (∃ result, ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state
      first finish = .ok result) ∨
    HonestCollision (e := e) time := by
  have forward v (honest : v ∈ J) m := e.forwardReachableWith
    (fun a ha => (anchored a ha) ▸ Store.ForwardReachableWith.anchor anchorStore) m v honest
  rcases parent_read_or_collision (forward u caller n).reachable
      (forward w receiver k).reachable (Store.block_ok_iff.mp parentOk) parentSafe with
    parentFound | collision
  swap
  · obtain ⟨leftBlock, rightBlock, found, _, _, _⟩ := collision
    exact .inr ⟨u, caller, w, receiver, n, k, callerTime, inTime, parentRoot,
      (parentRoot, leftBlock, rightBlock), found⟩
  left
  have afterOk := addChecked_one_of_subChecked lastOk
  -- Only the range arithmetic is reused; the balance state and committee read are the receiver's.
  obtain ⟨covered, coverage⟩ := coverage_exists_of_maximum nonempty read afterOk
  have stakeBound := ceiling w receiver k _ state inTime cached
  obtain ⟨heldWithin, within⟩ := honestRegistries_of_gated registries w receiver k inTime
  obtain ⟨total, totalOk⟩ := getTotalActiveBalance_exists
    (within state cached) (by change _ ≤ _ at stakeBound; omega)
  exact maximum_exists_of_total coverage windowOk totalOk
    (registry_of_head_window anchorStore anchored sound anchorSlot boundary
      (UInt64.lt_iff_toNat_lt.mpr positive) receiver heldWithin finalizedRead parentFound
      (absent w receiver k inTime) firstOk headOk cached windowOk)

end Models.Network

end EthLib.Consensus
