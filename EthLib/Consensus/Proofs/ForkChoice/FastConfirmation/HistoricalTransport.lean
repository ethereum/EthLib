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
    (early : fork < .glamsterdam)
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
    (fun ok => pendingTailRun_stateTransition early finite ok)
    (fun slots bound ok => relation_of_processSlots_of_stateTransition (PendingTailRun count epoch)
      (fun one two => one.trans two) (fun rest => pendingTailRun_processSlots finite rest)
      (fun step => pendingTailRun_processBlock early finite step) slots bound ok)
    (fun ok => pendingTailRun_processSlots finite ok)
    anchorSlot reached target found startOk atOrAfter baseFound sourceFound advanced

/-- A held checkpoint bounds every finitely activated source position in the receiver registry.

The source lookahead transports its tail, while the receiver lookahead supplies the prefix size.

Historical applicability is still required separately; no validator identity is inferred. -/
private theorem registry_of_checkpointPrefix {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} (early : fork < .glamsterdam)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorInvariant : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH)
    {checkpoint : Checkpoint} {root sourceRoot : Root}
    {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    {source advancedSource boundaryBase base cached : BeaconState preset fork}
    {sourceTarget : Slot}
    (walk : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (bound : start ≤ max block.slot target)
    (baseFound : store.blockStates[root]? = some base)
    (boundaryBaseFound : store.blockStates[checkpoint.root]? = some boundaryBase)
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
  obtain ⟨boundary, boundaryRun, receiverRun⟩ := relation_of_checkpoint_lookahead
    RunKept RunKept.refl (fun one two => one.trans two)
    (fun ok => runKept_stateTransition ok)
    (fun slots bound ok => runKept_of_processSlots_of_stateTransition slots bound ok)
    (fun ok => runKept_processSlots ok)
    anchorSlot reached walk found startOk bound boundaryBaseFound baseFound advanced
  obtain ⟨sourceBoundary, sourceBoundaryRun, related⟩ := pendingTailRun_checkpointPrefix
    (count := boundary.validators.data.size) early anchorSlot reached sourceWalk
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
    (early : fork < .glamsterdam) (held : store.blockState head = .ok state)
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
    ((mem_getActiveValidatorIndices (BeaconState.registryWithinLimit_of_lt early state)).mp
      (mem_getActiveValidatorIndices_of_getBeaconCommittee (mapError_ok_iff.mp computed) member))

/-- A window member is active at a queried epoch of the held head state. -/
private theorem active_of_committeeWindow {store : Store preset fork} {head : Root}
    {first last : Slot} {state : BeaconState preset fork} {members : Std.TreeSet ValidatorIndex}
    (early : fork < .glamsterdam) (held : store.blockState head = .ok state)
    (read : store.getCommitteesBetweenSlots head first last = .ok members) :
    ∀ v ∈ members, ∃ epoch, isActiveAt state epoch v.toNat = true := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨_, _, folded⟩ := read
  intro v member
  rcases (mem_foldlM_committees_iff folded).mp member with empty | ⟨offset, _, set, read, inside⟩
  · simp at empty
  · exact ⟨_, active_of_slotCommittee early held read v inside⟩

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
    (before : fork < .glamsterdam) (lower : ((e.world n).state u).ParentsBelow)
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
  have voteDescends := Store.isAncestor_of_blockTree_ancestor (lower := lower) before
    votedFound parentFound (isChild.ancestor.trans above)
  exact membership u honest n after time parent members _ attestation
    ⟨head, current, first, finish, epoch, headRead, parentFound, descends, slotRead, epochRead,
      horizon, firstOk, lastOk, window, origin, voteDescends, low, high⟩

open Models.ForkChoice in
/-- The model weight includes every honest supporter counted by the store. -/
private theorem honest_supporters_le_weight [DecidablePred (· ∈ J)]
    {store : Store preset fork} {state : BeaconState preset fork} {root : Root}
    {block : BeaconBlock preset fork} (lower : store.ParentsBelow)
    (before : fork < .glamsterdam) (within : state.RegistryWithinLimit)
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
    rw [Store.getSupportedNode_of_lt before, Except.ok.injEq] at supportedOk
    subst supported
    have ancestry := (Store.isAncestor_iff (lower := lower) before found rfl descends).mp rfl
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
/-- A finite-window margin makes a block heavier than a sibling, including the boost. -/
private theorem sibling_weight_lt_of_window_margin [DecidablePred (· ∈ J)]
    {since last n : Nat} {u : ValidatorIndex} {root : Root} {block parent : BeaconBlock preset fork}
    (membership : VotersInHeadWindow (e := e) block.parentRoot since last) (honest : u ∈ J)
    (after : since ≤ (e.world n).time) (time : (e.world n).time ≤ last)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock
      ((e.world n).state u))
    (before : fork < .glamsterdam) (lower : ((e.world n).state u).ParentsBelow)
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
      have member := mem_window_of_mem_supporters membership honest after time reached before
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

The voters below the parent lie in the head's window by the window-membership premise. -/
public theorem ancestor_head_of_window_margin [DecidablePred (· ∈ J)]
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {last n call : Nat} {u : ValidatorIndex} {root : Root} {block parent : BeaconBlock preset fork}
    (membership : VotersInHeadWindow (e := e) block.parentRoot (e.world call).time last)
    (honest : u ∈ J) (time : (e.world n).time ≤ last)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) (before : fork < .glamsterdam)
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
    (scoreOk : computeProposerScore config state = .ok (score : Gwei)) :
    ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true ∨
    HonestCollision (e := e) last := by
  classical
  rcases route with justifiedAbove |
    ⟨viable, descends, maximum, sourceMaximum, sourceScore, maximumOk, sourceMaximumOk,
      sourceScoreOk, sourceMargin⟩
  · obtain ⟨justified, justifiedKnown⟩ := Store.filterNodeTree_known tree
    exact .inl (Store.isAncestor_trans_of_lt before justifiedKnown found
      (Store.isAncestor_getHead_of_lt_gloas before headRead) justifiedAbove)
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
  have within := BeaconState.registryWithinLimit_of_lt before state
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
  have pending := Store.getHead_pending before headRead
  have pendingHead : (⟨head.root, .pending⟩ : ForkChoiceNode) = head := by
    cases head
    simp_all only
  rw [← pendingHead] at descends
  -- The visited parent makes the head known.
  obtain ⟨headBlock, headKnown, _⟩ := Store.slot_le_of_isAncestor parentFound descends
  have boostBound : store.boostScore config ≤ score.toNat := by
    dsimp only [store]
    simp only [Store.boostScore]
    split
    · exact Nat.zero_le _
    · simp [Store.getProposerScore, stateRead, scoreOk, bind, Except.bind]
  have supportBound := honest_supporters_le_weight (J := J) lower before within found nodes
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
      have visited := (Store.isAncestor_iff (lower := lower) before parentFound rfl descends).mp rfl
      rw [← ghostEq]
      apply ancestor_ghost_of_visited_parent _ _
        ((Store.view lower nodes).withBoost store.boostedRoot) _
        (Models.ForkChoice.mem_children.mpr ⟨inView, child⟩) above
        (ghostEq ▸ visited)
      intro sibling member distinct
      exact sibling_weight_lt_of_window_margin membership honest later time reached before
        lower within nodes store.boostedRoot
        (store.boostScore config) headRead found parentFound descends slotRead
        epochRead horizon firstOk lastOk window shortWindow shortBefore member distinct modelMargin
  have answer := Store.isAncestor_of_blockTree_ancestor (lower := lower) before headKnown
    found result
  obtain ⟨headRoot, status⟩ := head
  simp only at pending
  subst status
  exact answer

/-- Held-state finality supplies the source bound at the store's realized checkpoint.

The two ancestry reads remain separate inputs; this does not bound cached-output finality. -/
private theorem registry_of_honest_block {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH) (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
    {boundaryBase source base cached : BeaconState preset fork}
    {root sourceRoot : Root} {block sourceBlock : BeaconBlock preset fork} {start target : Slot}
    (boundaryBaseFound : ((e.world n).state u).blockStates[
      ((e.world n).state u).finalizedCheckpoint.root]? = some boundaryBase)
    (startOk : computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch =
      .ok start)
    (walk : ((e.world n).state u).getCheckpointBlock root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (bound : start ≤ max block.slot target)
    (baseFound : ((e.world n).state u).blockStates[root]? = some base)
    (advanced : lookaheadState config checks base target = .ok cached)
    (sourceWalk : ((e.world n).state u).getCheckpointBlock sourceRoot
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root)
    (sourceBlockFound : ((e.world n).state u).blocks[sourceRoot]? = some sourceBlock)
    (sourceFound : ((e.world n).state u).blockStates[sourceRoot]? = some source)
    (sourceBound : start ≤ sourceBlock.slot)
    (finite : ((e.world n).state u).finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH) :
    ∀ epoch position, isActiveAt source epoch position = true →
      ∃ validator, cached.validators.data[position]? = some validator := by
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  have finalized := (reached.reachable.ordered_finalized anchorInvariant).2 sourceFound
  have identity : lookaheadState config checks source source.slot = .ok source := by
    simp [lookaheadState, pure, Except.pure]
  have sourceStart : start ≤ max sourceBlock.slot source.slot := by
    rw [UInt64.le_iff_toNat_le, toNat_max]
    exact Nat.le_trans (UInt64.le_iff_toNat_le.mp sourceBound) (Nat.le_max_left _ _)
  exact registry_of_checkpointPrefix early anchorSlot reached anchorInvariant positive
    walk found startOk bound baseFound boundaryBaseFound advanced identity sourceWalk
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

/-- A window at the justified root has successful registry reads in its actual cached state.

The cached state may process empty slots beyond the block at that root. -/
private theorem registry_of_justified_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
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
  obtain ⟨epoch, active⟩ := active_of_committeeWindow early held window v member
  obtain ⟨validator, found⟩ := registry_of_runKept (runKept_lookahead advanced) active
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- Genesis finality supplies the actual head and cache walks through the anchor. -/
private theorem registry_of_genesis_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH) (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
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
  obtain ⟨anchorRoot, anchorHash, anchorFound⟩ := reached.reachable.anchor_known
  have sameRoot := Except.ok.inj (anchorHash.symm.trans hashed)
  rw [sameRoot] at anchorFound
  obtain ⟨boundaryBase, boundaryBaseFound, _, _⟩ :=
    reached.reachable.blockStatesFromParents anchorFound
  have startOk : computeStartSlotAtEpoch preset
      ((e.world n).state u).finalizedCheckpoint.epoch = .ok 0 := by
    simp [genesis, GENESIS_EPOCH, computeStartSlotAtEpoch, mulChecked]
  have walk := reached.reachable.getCheckpointBlock_anchor anchorSlot boundary unknown found hashed
  have headWalk := reached.reachable.getCheckpointBlock_anchor anchorSlot boundary unknown
    headFound hashed
  rw [← epochEq] at walk headWalk
  have inside := registry_of_honest_block anchorStore anchored anchorInvariant
    (UInt64.le_of_eq anchorSlot) positive early honest boundaryBaseFound startOk walk found
    UInt64.zero_le baseFound advanced headWalk headFound headStateFound
    UInt64.zero_le (by rw [genesis]; decide)
  intro v member
  obtain ⟨epoch, active⟩ := active_of_committeeWindow early
    (Store.blockState_ok_iff.mpr headStateFound) window v member
  obtain ⟨validator, found⟩ := inside epoch v.toNat active
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- A nonidentity head supplies registry containment through its realized finalized boundary.

A head at the finalized root uses prefix growth, even when its block precedes the boundary. -/
private theorem registry_of_nongenesis_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH) (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
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
    Store.isAncestor_of_getCheckpointBlock early walk
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
    obtain ⟨epoch, active⟩ := active_of_committeeWindow early
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
  have inside := registry_of_honest_block anchorStore anchored anchorInvariant
    (UInt64.le_of_eq anchorSlot) positive early honest boundaryBaseFound startOk walk found
    bound baseFound advanced headWalk headFound headStateFound headBound finite
  intro v member
  obtain ⟨epoch, active⟩ := active_of_committeeWindow early
    (Store.blockState_ok_iff.mpr headStateFound) window v member
  obtain ⟨validator, held⟩ := inside epoch v.toNat active
  exact ⟨validator, validatorAt_ok_iff.mpr held⟩

/-- The actual head selects identity, genesis or finalized-prefix registry transport. -/
private theorem registry_of_head_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorInvariant : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH) (early : fork < .glamsterdam)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat}
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
  · exact registry_of_justified_window anchorStore anchored early honest same cached window
  have reached := e.forwardReachableWith
    (fun w member => (anchored w member) ▸ Store.ForwardReachableWith.anchor anchorStore)
    n u honest
  obtain ⟨base, _, baseFound, _, _⟩ := e.checkpointStates_fixedChecks anchorStore anchored honest
    (Store.checkpointState_ok_iff.mp cached)
  obtain ⟨justified, justifiedFound⟩ := reached.reachable.known_of_blockState baseFound
  obtain ⟨headBlock, headFound, _⟩ := Store.slot_le_of_isAncestor justifiedFound
    (Store.isAncestor_getHead_of_lt_gloas early headRead)
  obtain ⟨headState, headStateFound, _, _⟩ := reached.reachable.blockStatesFromParents headFound
  by_cases genesis : ((e.world n).state u).finalizedCheckpoint.epoch = GENESIS_EPOCH
  · exact registry_of_genesis_window anchorStore anchored anchorInvariant anchorSlot boundary
      positive early honest genesis unknown headFound headStateFound cached window
  exact registry_of_nongenesis_window anchorStore anchored anchorInvariant anchorSlot positive
    early honest walk headRead same genesis headStateFound parentFound unknown parentNext cached
    window

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

/-- Equal-rank honest latest votes agree before Gloas, even across different stores. -/
public theorem Execution.latest_eq_of_rank_eq (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J)
    {n k : ℕ} {first second : LatestMessage fork}
    (firstOk : ((e.world n).state u).latestMessages[v]? = some first)
    (secondOk : ((e.world k).state w).latestMessages[v]? = some second)
    (rank : first.rank = second.rank) : first = second := by
  obtain ⟨a, firstMessage, seenFirst, rfl, signedFirst, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller firstOk
  obtain ⟨b, secondMessage, seenSecond, rfl, signedSecond, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored receiver secondOk
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have epoch : a.data.target.epoch = b.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  have same := Execution.data_eq_of_signed_of_target_epoch slots
    (e.view_subset_sent n u seenFirst) (e.view_subset_sent k w seenSecond)
    signedFirst signedSecond honest epoch
  simp only [LatestMessage.ofAttestation, same]

/-- A nonempty caller range supplies arithmetic for the receiver's full-window maximum.

The receiver's own finalized checkpoint must be on the chain of its own justified checkpoint. -/
public theorem receiver_fullMaximum_of_head_window {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (early : fork < .glamsterdam) {time : Nat}
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
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
  obtain ⟨total, totalOk⟩ := getTotalActiveBalance_exists
    (BeaconState.registryWithinLimit_of_lt early state) (by change _ ≤ _ at stakeBound; omega)
  exact maximum_exists_of_total coverage windowOk totalOk
    (registry_of_head_window anchorStore anchored sound anchorSlot boundary
      (UInt64.lt_iff_toNat_lt.mpr positive) early receiver finalizedRead parentFound
      (absent w receiver k inTime) firstOk headOk cached windowOk)

end Models.Network

end EthLib.Consensus
