module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.ForkChoice.ProposerHead
public import EthLib.Consensus.Proofs.ForkChoice.Handlers

/-!
# Proofs: the head on which a proposer builds

The proposer builds on the head or on its parent, and on nothing else.

It skips the head only when the head is weak.

It never answers while the head still holds the boost.

An exact statement gives when it answers and which node it takes, from its tests.

The parent node has the payload status that the head builds on.

So from Gloas a proposer whose head is not pending never builds on a pending node.

Each test has an exact statement of when it answers and what it returns.

The shuffling test always passes from Fulu, and before Fulu it reads the slot in its epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- From Fulu the shuffling test always lets a re-org happen. -/
theorem shufflingAllowsReorg_of_fulu {slot : Slot} (fulu : .fusaka ≤ fork) :
    shufflingAllowsReorg preset fork slot = .ok true := by
  simp [shufflingAllowsReorg, fulu, pure, Except.pure]

/-- Before Fulu a re-org waits for a slot that does not start an epoch. -/
theorem shufflingAllowsReorg_of_lt {slot : Slot} (before : fork < .fusaka)
    (positive : preset.SLOTS_PER_EPOCH ≠ 0) :
    shufflingAllowsReorg preset fork slot = .ok (slot % preset.SLOTS_PER_EPOCH ≠ 0) := by
  have later : ¬ .fusaka ≤ fork := Nat.not_le_of_lt before
  simp [shufflingAllowsReorg, isShufflingStable, later, positive, pure, Except.pure]

/-- The shuffling test answers exactly as above, and fails only before Fulu with empty epochs. -/
theorem shufflingAllowsReorg_ok_iff {slot : Slot} {allows : Bool} :
    shufflingAllowsReorg preset fork slot = .ok allows ↔
      (.fusaka ≤ fork ∧ allows = true) ∨
        (fork < .fusaka ∧ preset.SLOTS_PER_EPOCH ≠ 0 ∧
          allows = decide (slot % preset.SLOTS_PER_EPOCH ≠ 0)) := by
  by_cases fulu : .fusaka ≤ fork
  · have later : ¬ fork < .fusaka := Nat.not_lt_of_le fulu
    simp [shufflingAllowsReorg_of_fulu fulu, fulu, later, eq_comm]
  have before : fork < .fusaka := Nat.lt_of_not_le fulu
  by_cases positive : preset.SLOTS_PER_EPOCH = 0
  · simp [shufflingAllowsReorg, isShufflingStable, fulu, positive, throw, throwThe,
      MonadExceptOf.throw]
  · simp [shufflingAllowsReorg_of_lt before positive, fulu, before, positive, eq_comm]

/-- The sum of the effective balances, in a state, of the equivocators among some validators.

An index outside the state adds nothing, so a statement must also require each equivocator known. -/
def equivocatorWeight (equivocators : List ValidatorIndex) (state : BeaconState preset fork)
    (validators : List ValidatorIndex) : Nat :=
  (((validators.filter equivocators.contains).filterMap fun validator =>
    state.validators.data[validator.toNat]?).map (·.effectiveBalance.toNat)).sum

namespace Store

variable {config : Config} {store : Store preset fork}

/-- A head is late exactly when the store records that it was not timely.

From Gloas that record is the timeliness for the attestation deadline. -/
theorem isHeadLate_ok_iff {root : Root} {late : Bool} :
    store.isHeadLate root = .ok late ↔
      ∃ timely, store.blockTimeliness[root]? = some timely ∧ late = !timely := by
  unfold isHeadLate
  cases store.blockTimeliness[root]? <;>
    simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure, eq_comm]

/-- A head and a parent compete exactly when their unrealized justified checkpoints are equal. -/
theorem isFfgCompetitive_ok_iff {head parent : Root} {competitive : Bool} :
    store.isFfgCompetitive head parent = .ok competitive ↔
      ∃ first second, store.unrealizedJustifications[head]? = some first ∧
        store.unrealizedJustifications[parent]? = some second ∧
        competitive = decide (first = second) := by
  unfold isFfgCompetitive unrealizedJustification
  cases store.unrealizedJustifications[head]? with
  | none => simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  | some first =>
    cases store.unrealizedJustifications[parent]? with
    | none => simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure, bind, Except.bind]
    | some second =>
      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨first, second, rfl, rfl, rfl⟩
      · rintro ⟨_, _, rfl, rfl, rfl⟩
        rfl

/-- Finality is recent exactly when its epoch is at most the limit behind the epoch of the slot.

A finalized epoch after that of the slot fails. -/
theorem isFinalizationOk_ok_iff {slot : Slot} {recent : Bool} :
    store.isFinalizationOk config slot = .ok recent ↔
      store.finalizedCheckpoint.epoch.toNat ≤ (computeEpochAtSlot preset slot).toNat ∧
        recent = decide ((computeEpochAtSlot preset slot).toNat ≤
          store.finalizedCheckpoint.epoch.toNat +
            config.REORG_MAX_EPOCHS_SINCE_FINALIZATION.toNat) := by
  simp only [isFinalizationOk, bind_ok_iff, mapError_ok_iff, Uint64.subChecked_ok_iff, pure,
    Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨difference, ⟨below, value⟩, rfl⟩
    refine ⟨below, ?_⟩
    simp only [decide_eq_decide, UInt64.le_iff_toNat_le, value]
    omega
  · rintro ⟨below, rfl⟩
    refine ⟨computeEpochAtSlot preset slot - store.finalizedCheckpoint.epoch,
      ⟨below, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr below)⟩, ?_⟩
    simp only [decide_eq_decide, UInt64.le_iff_toNat_le,
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr below)]
    omega

/-- A proposer is on time exactly when the time into the current slot is at most the cutoff. -/
theorem isProposingOnTime_ok_iff {onTime : Bool} :
    store.isProposingOnTime config = .ok onTime ↔
      ∃ time cutoff, store.getTimeIntoSlotMs config = .ok time ∧
        getProposerReorgCutoffMs config = .ok cutoff ∧ onTime = decide (time ≤ cutoff) := by
  simp only [isProposingOnTime, bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨time, clock, cutoff, computed, rfl⟩
    exact ⟨time, cutoff, clock, computed, rfl⟩
  · rintro ⟨time, cutoff, clock, computed, rfl⟩
    exact ⟨time, clock, cutoff, computed, rfl⟩

/-- A parent is strong exactly when the votes for its pending node exceed the threshold.

Both come from the justified state. -/
theorem isParentStrong_ok_iff {root : Root} {strong : Bool} :
    store.isParentStrong config root = .ok strong ↔
      ∃ justified threshold block votes,
        store.checkpointStates[store.justifiedCheckpoint]? = some justified ∧
        calculateCommitteeFraction justified config.REORG_PARENT_WEIGHT_THRESHOLD =
          .ok threshold ∧
        store.blocks[root]? = some block ∧
        store.getAttestationScore ⟨block.parentRoot, .pending⟩ justified = .ok votes ∧
        strong = decide (threshold < votes) := by
  simp only [isParentStrong, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    checkpointState_ok_iff, block_ok_iff]
  constructor
  · rintro ⟨justified, known, threshold, computed, block, found, votes, score, rfl⟩
    exact ⟨justified, threshold, block, votes, known, computed, found, score, rfl⟩
  · rintro ⟨justified, threshold, block, votes, known, computed, found, score, rfl⟩
    exact ⟨justified, known, threshold, computed, block, found, votes, score, rfl⟩

/-- A proposer equivocated exactly when another known block has its proposer and its slot. -/
theorem isProposerEquivocation_ok_iff {root : Root} {equivocation : Bool} :
    store.isProposerEquivocation root = .ok equivocation ↔
      ∃ block, store.blocks[root]? = some block ∧
        (equivocation = true ↔ ∃ other otherBlock, other ≠ root ∧
          store.blocks[other]? = some otherBlock ∧
          otherBlock.proposerIndex = block.proposerIndex ∧ otherBlock.slot = block.slot) := by
  simp only [isProposerEquivocation, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    block_ok_iff]
  refine exists_congr fun block => and_congr_right fun known => ?_
  generalize matching : List.filter (fun entry : Root × BeaconBlock preset fork =>
    decide (entry.2.proposerIndex = block.proposerIndex ∧ entry.2.slot = block.slot))
    store.blocks.toList = entries
  have member : ∀ entry, entry ∈ entries ↔ store.blocks[entry.1]? = some entry.2 ∧
      entry.2.proposerIndex = block.proposerIndex ∧ entry.2.slot = block.slot := by
    rintro ⟨key, value⟩
    simp [← matching, List.mem_filter, Std.TreeMap.mem_toList_iff_getElem?_eq_some]
  -- The entries of a map have distinct roots, and so do those that the filter keeps.
  have distinct : entries.Pairwise fun first second => first.1 ≠ second.1 := by
    rw [← matching]
    refine (Std.TreeMap.distinct_keys_toList (t := store.blocks)).filter _ |>.imp ?_
    intro first second different same
    exact different (by rw [same]; exact Std.ReflCmp.compare_self)
  have many : 1 < entries.length ↔ ∃ other otherBlock, other ≠ root ∧
      store.blocks[other]? = some otherBlock ∧
      otherBlock.proposerIndex = block.proposerIndex ∧ otherBlock.slot = block.slot := by
    constructor
    · intro long
      -- A list longer than one starts with two entries.
      match entries, long, member, distinct with
      | first :: second :: _, _, member, distinct =>
        -- Two entries have distinct roots, so one of them is not the root of the block.
        have different : first.1 ≠ second.1 :=
          (List.pairwise_cons.mp distinct).1 second List.mem_cons_self
        by_cases same : first.1 = root
        · exact ⟨second.1, second.2, fun back => different (same.trans back.symm),
            (member second).mp (by simp)⟩
        · exact ⟨first.1, first.2, same, (member first).mp (by simp)⟩
    · rintro ⟨other, otherBlock, different, found, proposer, slot⟩
      -- The block matches itself, so another root makes a second entry.
      have one : (root, block) ∈ entries := (member _).mpr ⟨known, rfl, rfl⟩
      have two : (other, otherBlock) ∈ entries := (member _).mpr ⟨found, proposer, slot⟩
      match entries, one, two with
      | [_], one, two =>
        simp only [List.mem_singleton] at one two
        exact absurd (congrArg Prod.fst (two.trans one.symm)) different
      | _ :: _ :: _, _, _ => simp
  cases equivocation <;> simp [many]

/-- A sum over the validators of two lists adds the sums over each list. -/
private theorem equivocatorWeight_append {equivocators : List ValidatorIndex}
    {state : BeaconState preset fork} {first second : List ValidatorIndex} :
    equivocatorWeight equivocators state (first ++ second) =
      equivocatorWeight equivocators state first + equivocatorWeight equivocators state second := by
  simp [equivocatorWeight]

/-- One step of the walk over a committee in the weak test. -/
private abbrev equivocatorStep (store : Store preset fork) (state : BeaconState preset fork)
    (validator : ValidatorIndex) (weight : Nat) : Except ForkChoiceError (ForInStep Nat) :=
  if store.equivocatingIndices.contains validator = true then
    match state.validators.data[validator.toNat]? with
    | some known => Except.ok (ForInStep.yield (weight + known.effectiveBalance.toNat))
    -- The step after the throw is how the loop of the rule elaborates.
    | none => do
      throw (ForkChoiceError.accessor (AccessorError.indexOutOfRange validator))
      Except.ok (ForInStep.yield weight)
  else Except.ok (ForInStep.yield weight)

/-- A walk over validators adds the balances of the equivocators.

It succeeds exactly when the state holds each of them. -/
private theorem forIn_equivocators_ok_iff {state : BeaconState preset fork}
    {validators : List ValidatorIndex} {start stop : Nat} :
    forIn validators start (equivocatorStep store state) = .ok stop ↔
      (∀ validator ∈ validators, store.equivocatingIndices.contains validator = true →
        state.validators.data[validator.toNat]?.isSome) ∧
      stop = start + equivocatorWeight store.equivocatingIndices state validators := by
  induction validators generalizing start with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq, List.not_mem_nil,
      false_imp_iff, implies_true, true_and, equivocatorWeight, List.filter_nil,
      List.filterMap_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    exact eq_comm
  | cons validator rest ih =>
    rw [List.forIn_cons, bind_ok_iff, List.forall_mem_cons]
    by_cases contained : store.equivocatingIndices.contains validator = true
    · cases found : state.validators.data[validator.toNat]? with
      | none =>
        simp only [equivocatorStep, contained, found, ↓reduceIte]
        simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      | some known =>
        have weight : equivocatorWeight store.equivocatingIndices state (validator :: rest) =
            known.effectiveBalance.toNat +
              equivocatorWeight store.equivocatingIndices state rest := by
          simp only [equivocatorWeight, List.filter_cons, contained, ↓reduceIte,
            List.filterMap_cons, found, List.map_cons, List.sum_cons]
        simp only [equivocatorStep, contained, found, ↓reduceIte, Except.ok.injEq,
          exists_eq_left', ih, weight, Option.isSome_some, forall_const, true_and, Nat.add_assoc]
    · have weight : equivocatorWeight store.equivocatingIndices state (validator :: rest) =
          equivocatorWeight store.equivocatingIndices state rest := by
        simp only [equivocatorWeight, List.filter_cons, contained, Bool.false_eq_true, ↓reduceIte]
      simp only [equivocatorStep, contained, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
        exists_eq_left', ih, weight, false_imp_iff, true_and]

/-- A walk over the committees of some indices adds the balances of their equivocators.

It succeeds exactly when each committee is found, each equivocator is known, and the sum fits. -/
private theorem forIn_committees_ok_iff {state justified : BeaconState preset fork} {slot : Slot}
    {indices : List Nat} {start stop : Nat} (small : start < 2 ^ 64) :
    forIn indices start (fun (index weight : Nat) => do
        let committee ← Except.mapError ForkChoiceError.accessor
          (getBeaconCommittee state slot index.toUInt64)
        let next ← forIn committee weight (equivocatorStep store justified)
        if 2 ^ 64 ≤ next then do
          throw (ForkChoiceError.arith ArithError.overflow)
          Except.ok (ForInStep.yield next)
        else Except.ok (ForInStep.yield next)) = .ok stop ↔
      ∃ committees, indices.mapM (fun index => getBeaconCommittee state slot index.toUInt64) =
          .ok committees ∧
        (∀ validator ∈ committees.flatMap Array.toList,
          store.equivocatingIndices.contains validator = true →
            justified.validators.data[validator.toNat]?.isSome) ∧
        stop = start + equivocatorWeight store.equivocatingIndices justified
          (committees.flatMap Array.toList) ∧
        stop < 2 ^ 64 := by
  induction indices generalizing start with
  | nil =>
    simp only [List.forIn_nil, List.mapM_nil, pure, Except.pure, Except.ok.injEq, exists_eq_left',
      List.flatMap_nil, List.not_mem_nil, false_imp_iff, implies_true, true_and, equivocatorWeight,
      List.filter_nil, List.filterMap_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    constructor
    · rintro rfl
      exact ⟨rfl, small⟩
    · rintro ⟨rfl, _⟩
      rfl
  | cons index rest ih =>
    rw [List.forIn_cons, bind_ok_iff]
    constructor
    · rintro ⟨step, first, walk⟩
      -- The walk over a committee reads its array as a list.
      simp only [bind_ok_iff, mapError_ok_iff, ← Array.forIn_toList,
        forIn_equivocators_ok_iff] at first
      obtain ⟨committee, found, next, ⟨known, value⟩, check⟩ := first
      -- A sum over the limit fails, so this one fits.
      split at check
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at check
      rename_i fits
      cases check
      obtain ⟨committees, mapped, knownRest, valueRest, smallRest⟩ :=
        (ih (Nat.lt_of_not_le fits)).mp walk
      refine ⟨committee :: committees, mapM_cons_ok.mpr ⟨committee, committees, found, mapped, rfl⟩,
        ?_, ?_, smallRest⟩
      · simp only [List.flatMap_cons, List.forall_mem_append]
        exact ⟨known, knownRest⟩
      · rw [List.flatMap_cons, equivocatorWeight_append, valueRest, value, Nat.add_assoc]
    · rintro ⟨committees, mapped, known, value, fits⟩
      obtain ⟨committee, others, found, mappedRest, rfl⟩ := mapM_cons_ok.mp mapped
      simp only [List.flatMap_cons, List.forall_mem_append] at known
      rw [List.flatMap_cons, equivocatorWeight_append, ← Nat.add_assoc] at value
      -- The sum only grows, so a sum that fits at the end fits after each committee.
      have within : start +
          equivocatorWeight store.equivocatingIndices justified committee.toList < 2 ^ 64 := by
        omega
      refine ⟨.yield
          (start + equivocatorWeight store.equivocatingIndices justified committee.toList), ?_,
        (ih within).mpr ⟨others, mappedRest, known.2, value, fits⟩⟩
      simp only [bind_ok_iff, mapError_ok_iff, ← Array.forIn_toList,
        forIn_equivocators_ok_iff]
      refine ⟨committee, found, _, ⟨known.1, rfl⟩, ?_⟩
      rw [ite_eq_right_iff.mpr (fun above => absurd above (Nat.not_le_of_lt within))]

/-- A head is weak exactly when its votes and equivocators weigh below the threshold.

Its equivocators are those of the committees of its slot, in the state of the head.

Its votes and the balances of its equivocators come from the justified state.

That state must hold each equivocator.

The weight must fit in 64 bits. -/
theorem isHeadWeak_ok_iff {root : Root} {weak : Bool} :
    store.isHeadWeak config root = .ok weak ↔
      ∃ justified threshold state block votes committees,
        store.checkpointStates[store.justifiedCheckpoint]? = some justified ∧
        calculateCommitteeFraction justified config.REORG_HEAD_WEIGHT_THRESHOLD = .ok threshold ∧
        store.blockStates[root]? = some state ∧
        store.blocks[root]? = some block ∧
        store.getAttestationScore ⟨root, .pending⟩ justified = .ok votes ∧
        (List.range
            (getCommitteeCountPerSlot state (computeEpochAtSlot preset block.slot)).toNat).mapM
          (fun index => getBeaconCommittee state block.slot index.toUInt64) = .ok committees ∧
        (∀ validator ∈ committees.flatMap Array.toList,
          store.equivocatingIndices.contains validator = true →
            justified.validators.data[validator.toNat]?.isSome) ∧
        votes.toNat + equivocatorWeight store.equivocatingIndices justified
          (committees.flatMap Array.toList) < 2 ^ 64 ∧
        weak = decide (votes.toNat + equivocatorWeight store.equivocatingIndices justified
            (committees.flatMap Array.toList) < threshold.toNat) := by
  simp only [isHeadWeak, bind_ok_iff, pure, Except.pure, Except.ok.injEq, checkpointState_ok_iff,
    blockState_ok_iff, block_ok_iff]
  constructor
  · rintro ⟨justified, known, threshold, computed, state, stateKnown, block, blockKnown, votes,
      score, weight, walk, rfl⟩
    obtain ⟨committees, mapped, each, value, fits⟩ :=
      (forIn_committees_ok_iff votes.toNat_lt).mp walk
    subst value
    exact ⟨justified, threshold, state, block, votes, committees, known, computed, stateKnown,
      blockKnown, score, mapped, each, fits, rfl⟩
  · rintro ⟨justified, threshold, state, block, votes, committees, known, computed, stateKnown,
      blockKnown, score, mapped, each, fits, rfl⟩
    exact ⟨justified, known, threshold, computed, state, stateKnown, block, blockKnown, votes,
      score, _, (forIn_committees_ok_iff votes.toNat_lt).mpr
        ⟨committees, mapped, each, rfl, fits⟩, rfl⟩

/-- The checked sum of a slot and one answers exactly when the sum fits in 64 bits. -/
private theorem next_slot_ok_iff {first next : Slot} :
    (Uint64.addChecked first 1).mapError ForkChoiceError.arith = .ok next ↔
      first.toNat + 1 < 2 ^ 64 ∧ next.toNat = first.toNat + 1 := by
  rw [mapError_ok_iff, Uint64.addChecked_ok_iff]
  rfl

/-- Two tests in a row that lead to one node act as one test that either can pass. -/
private theorem ite_ite_eq_ite_or {α : Type} {first second firstNat secondNat : Prop}
    [Decidable first] [Decidable second] [Decidable (firstNat ∨ secondNat)] {node other : α}
    (sameFirst : first ↔ firstNat) (sameSecond : second ↔ secondNat) :
    (if first then node else if second then node else other) =
      if firstNat ∨ secondNat then node else other := by
  by_cases one : firstNat <;> by_cases two : secondNat <;> simp [sameFirst, sameSecond, one, two]

/-- The exact choice of a proposer.

It answers when the boost has worn off and the store holds the head and its parent.

Each test must answer, and the slot of each block plus one must fit in 64 bits.

It takes the parent when either list of tests passes, and the head otherwise.

The parent node has the payload status that the head builds on.

The first list is for a late head.

The second list is for a weak head of the previous slot whose proposer equivocated. -/
theorem getProposerHead_ok_iff {headNode chosen : ForkChoiceNode} {slot : Slot} :
    store.getProposerHead config headNode slot = .ok chosen ↔
      store.proposerBoostRoot ≠ headNode.root ∧
      ∃ head parent late shuffling competitive recent onTime weak strong equivocation,
        store.blocks[headNode.root]? = some head ∧
        store.blocks[head.parentRoot]? = some parent ∧
        store.isHeadLate headNode.root = .ok late ∧
        shufflingAllowsReorg preset fork slot = .ok shuffling ∧
        store.isFfgCompetitive headNode.root head.parentRoot = .ok competitive ∧
        store.isFinalizationOk config slot = .ok recent ∧
        store.isProposingOnTime config = .ok onTime ∧
        parent.slot.toNat + 1 < 2 ^ 64 ∧
        head.slot.toNat + 1 < 2 ^ 64 ∧
        store.isHeadWeak config headNode.root = .ok weak ∧
        store.isParentStrong config headNode.root = .ok strong ∧
        store.isProposerEquivocation headNode.root = .ok equivocation ∧
        chosen =
          if (late ∧ shuffling ∧ competitive ∧ recent ∧ onTime ∧
                (parent.slot.toNat + 1 = head.slot.toNat ∧ head.slot.toNat + 1 = slot.toNat) ∧
                weak ∧ strong) ∨
              (weak ∧ head.slot.toNat + 1 = slot.toNat ∧ equivocation)
          then ⟨head.parentRoot, parentPayloadStatus head parent⟩
          else headNode := by
  simp only [getProposerHead, bind_ok_iff, block_ok_iff]
  constructor
  · rintro ⟨head, headKnown, parent, parentKnown, late, lateFound, shuffling, shufflingFound,
      competitive, competitiveFound, recent, recentFound, onTime, onTimeFound, parentNext,
      parentNextFound, headNext, headNextFound, found⟩
    -- A head with the boost fails, so the boost has worn off.
    split at found
    · simp [throw, throwThe, MonadExceptOf.throw] at found
    rename_i unboosted
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at found
    obtain ⟨weak, weakFound, strong, strongFound, equivocation, equivocationFound, rfl⟩ := found
    obtain ⟨parentFits, parentValue⟩ := next_slot_ok_iff.mp parentNextFound
    obtain ⟨headFits, headValue⟩ := next_slot_ok_iff.mp headNextFound
    have parentSlots : parentNext = head.slot ↔ parent.slot.toNat + 1 = head.slot.toNat := by
      rw [← UInt64.toNat_inj, parentValue]
    have headSlots : headNext = slot ↔ head.slot.toNat + 1 = slot.toNat := by
      rw [← UInt64.toNat_inj, headValue]
    exact ⟨unboosted, head, parent, late, shuffling, competitive, recent, onTime, weak, strong,
      equivocation, headKnown, parentKnown, lateFound, shufflingFound, competitiveFound,
      recentFound, onTimeFound, parentFits, headFits, weakFound, strongFound, equivocationFound,
      ite_ite_eq_ite_or (by rw [parentSlots, headSlots]) (by rw [headSlots])⟩
  · rintro ⟨unboosted, head, parent, late, shuffling, competitive, recent, onTime, weak, strong,
      equivocation, headKnown, parentKnown, lateFound, shufflingFound, competitiveFound,
      recentFound, onTimeFound, parentFits, headFits, weakFound, strongFound, equivocationFound,
      rfl⟩
    have parentValue : (parent.slot + 1).toNat = parent.slot.toNat + 1 :=
      Uint64.toNat_add_of_lt parentFits
    have headValue : (head.slot + 1).toNat = head.slot.toNat + 1 :=
      Uint64.toNat_add_of_lt headFits
    have parentSlots : parent.slot + 1 = head.slot ↔ parent.slot.toNat + 1 = head.slot.toNat := by
      rw [← UInt64.toNat_inj, parentValue]
    have headSlots : head.slot + 1 = slot ↔ head.slot.toNat + 1 = slot.toNat := by
      rw [← UInt64.toNat_inj, headValue]
    refine ⟨head, headKnown, parent, parentKnown, late, lateFound, shuffling, shufflingFound,
      competitive, competitiveFound, recent, recentFound, onTime, onTimeFound, _,
      next_slot_ok_iff.mpr ⟨parentFits, parentValue⟩, _,
      next_slot_ok_iff.mpr ⟨headFits, headValue⟩, ?_⟩
    simp only [unboosted, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq]
    exact ⟨weak, weakFound, strong, strongFound, equivocation, equivocationFound,
      ite_ite_eq_ite_or (by rw [parentSlots, headSlots]) (by rw [headSlots])⟩

/-- The choice of a proposer, from the answers of its tests.

Let the boost have worn off, and let the store hold the head and its parent.

Let each test answer, and let the slot of each block plus one fit in 64 bits.

Then the choice is the parent when either list of tests passes, and the head otherwise. -/
theorem getProposerHead_eq {headNode : ForkChoiceNode} {slot : Slot}
    {head parent : BeaconBlock preset fork}
    {late shuffling competitive recent onTime weak strong equivocation : Bool}
    (unboosted : store.proposerBoostRoot ≠ headNode.root)
    (headKnown : store.blocks[headNode.root]? = some head)
    (parentKnown : store.blocks[head.parentRoot]? = some parent)
    (lateFound : store.isHeadLate headNode.root = .ok late)
    (shufflingFound : shufflingAllowsReorg preset fork slot = .ok shuffling)
    (competitiveFound : store.isFfgCompetitive headNode.root head.parentRoot = .ok competitive)
    (recentFound : store.isFinalizationOk config slot = .ok recent)
    (onTimeFound : store.isProposingOnTime config = .ok onTime)
    (parentFits : parent.slot.toNat + 1 < 2 ^ 64) (headFits : head.slot.toNat + 1 < 2 ^ 64)
    (weakFound : store.isHeadWeak config headNode.root = .ok weak)
    (strongFound : store.isParentStrong config headNode.root = .ok strong)
    (equivocationFound : store.isProposerEquivocation headNode.root = .ok equivocation) :
    store.getProposerHead config headNode slot = .ok
      (if (late ∧ shuffling ∧ competitive ∧ recent ∧ onTime ∧
            (parent.slot.toNat + 1 = head.slot.toNat ∧ head.slot.toNat + 1 = slot.toNat) ∧
            weak ∧ strong) ∨
          (weak ∧ head.slot.toNat + 1 = slot.toNat ∧ equivocation)
        then ⟨head.parentRoot, parentPayloadStatus head parent⟩
        else headNode) :=
  getProposerHead_ok_iff.mpr ⟨unboosted, head, parent, late, shuffling, competitive,
    recent, onTime, weak, strong, equivocation, headKnown, parentKnown, lateFound, shufflingFound,
    competitiveFound, recentFound, onTimeFound, parentFits, headFits, weakFound, strongFound,
    equivocationFound, rfl⟩

/-- The proposer builds on the head, or on the parent of its block.

It builds on the parent only when the head is weak.

The parent node has the payload status that the head builds on. -/
theorem getProposerHead_ok {headNode chosen : ForkChoiceNode} {slot : Slot}
    (found : store.getProposerHead config headNode slot = .ok chosen) :
    chosen = headNode ∨
      ∃ block parent, store.blocks[headNode.root]? = some block ∧
        store.blocks[block.parentRoot]? = some parent ∧
        chosen = ⟨block.parentRoot, parentPayloadStatus block parent⟩ ∧
        store.isHeadWeak config headNode.root = .ok true := by
  obtain ⟨_, head, parent, _, _, _, _, _, weak, _, _, known, parentKnown, _, _, _, _, _, _, _,
    weakFound, _, _, rfl⟩ := getProposerHead_ok_iff.mp found
  split
  · rename_i passed
    have isWeak : weak = true := by
      rcases passed with ⟨_, _, _, _, _, _, isWeak, _⟩ | ⟨isWeak, _, _⟩ <;> exact isWeak
    exact .inr ⟨head, parent, known, parentKnown, rfl, isWeak ▸ weakFound⟩
  · exact .inl rfl

/-- From Gloas a proposer whose head is not pending never builds on a pending node. -/
theorem getProposerHead_ne_pending {headNode chosen : ForkChoiceNode} {slot : Slot}
    (gloas : .glamsterdam ≤ fork) (notPending : headNode.payloadStatus ≠ .pending)
    (found : store.getProposerHead config headNode slot = .ok chosen) :
    chosen.payloadStatus ≠ .pending := by
  rcases getProposerHead_ok found with rfl | ⟨_, _, _, _, rfl, _⟩
  · exact notPending
  · exact parentPayloadStatus_ne_pending gloas

/-- The proposer gets no answer while the head still holds the boost. -/
theorem getProposerHead_boosted {headNode chosen : ForkChoiceNode} {slot : Slot}
    (boosted : store.proposerBoostRoot = headNode.root) :
    store.getProposerHead config headNode slot ≠ .ok chosen :=
  fun found => (getProposerHead_ok_iff.mp found).1 boosted

end Store

end EthLib.Consensus
