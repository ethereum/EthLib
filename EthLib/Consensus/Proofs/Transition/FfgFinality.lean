module

public import EthLib.Consensus.Proofs.Transition.FfgRoots

/-!
# Proofs: justification keeps the finalized checkpoint slack-finalized in Casper FFG

The epoch step finalizes by four rules on the bits of justification.

Between two slots, bit `i` of a state stands for the epoch `i + 1` before the current one.

Within the step, after the shift, bit `i` stands for the epoch `i` before the current one.

Each rule finalizes an old justified checkpoint one, two or three epochs back.

In the model, each rule is `k`-finalization with `k = 1` or `k = 2`, as in Gasper Definition 4.9.

- The rule on bits 0 and 1 finalizes the old current justified checkpoint with `k = 1`.
- The rule on bits 0 to 2 finalizes it with `k = 2`.
- The rule on bits 1 and 2 finalizes the old previous justified checkpoint with `k = 1`.
- The rule on bits 1 to 3 finalizes it with `k = 2`.

The links come from the votes that justify the newer epochs.

The rule on bits 0 to 2 reads the previous epoch as justified.

When the step justifies the current epoch too, the checkpoint of the previous epoch is in no field.

So the step needs the sets and weights of the model to match for both recent epochs.

The rule on bits 1 to 3 reads the epoch two back as justified.

So the bits carry facts of the model from one step to the next.

- A set bit 0 means a slack link from the previous to the current justified checkpoint.
- A set bit 1 means that the checkpoint of its epoch is slack-justified.

Bits 2 and 3 need no fact: the rule on bits 1 to 3 finalizes a checkpoint already justified.

The proof names the middle checkpoint of the rule on bits 1 to 3 by the root of the epoch two back.

So the buffer of roots must cover three epochs, while the step itself needs two.

Both presets meet that.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {β : Type*} [Preorder β]
  {attested : Set (ValidatorIndex × AttestationData)}
  {V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex}
  {W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)} {genesis : β}
  {votes : Set (Vote ValidatorIndex β)}

/-- The two newest bits of justification of a state carry facts of the model.

Bit `i` stands for the epoch `i + 1` before a given epoch.

Between two slots, the given epoch is the current epoch of the state.

Right after the epoch step, it is the epoch after the one of the step.

Each root maps to a block of the model. -/
structure SlackBits (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)) (genesis : β)
    (votes : Set (Vote ValidatorIndex β)) (block : Root → β) (epoch : ℕ)
    (state : BeaconState preset fork) : Prop where
  /-- Up to epoch 2, justification has changed nothing, and the two newest bits are clear. -/
  early : epoch ≤ 2 →
    state.justificationBits.bits[0] = false ∧ state.justificationBits.bits[1] = false
  /-- A set bit 0 gives a slack link from the previous to the current justified checkpoint.

  The current justified checkpoint is then that of the epoch before the given one.

  Its root is the root that the state records for the start of its epoch. -/
  current : state.justificationBits.bits[0] = true →
    state.currentJustifiedCheckpoint.epoch.toNat + 1 = epoch ∧
      getBlockRoot state state.currentJustifiedCheckpoint.epoch =
        .ok state.currentJustifiedCheckpoint.root ∧
      SlackLink V U W votes (state.previousJustifiedCheckpoint.toFfg block)
        (state.currentJustifiedCheckpoint.toFfg block)
  /-- A set bit 1 makes the checkpoint two epochs before the given one slack-justified.

  Its root is the root that the state records for the start of its epoch. -/
  previous : state.justificationBits.bits[1] = true → ∀ (older : Epoch) (root : Root),
    older.toNat + 2 = epoch → getBlockRoot state older = .ok root →
      SlackJustified V U W genesis votes ⟨block root, older.toNat⟩

/-- The epoch after genesis is epoch 1. -/
private theorem toNat_genesisEpoch_add_one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by
  decide

/-- Two epochs before an epoch past the first two is two less as a number. -/
private theorem toNat_sub_two {epoch : Epoch} (late : GENESIS_EPOCH + 1 < epoch) :
    (epoch - 2).toNat = epoch.toNat - 2 := by
  have late' := UInt64.lt_iff_toNat_lt.mp late
  rw [toNat_genesisEpoch_add_one] at late'
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
  simp

/-- Justification keeps the facts of the bits and the finalized checkpoint slack-finalized.

The hypotheses on the votes and the stake are those of the bound of a link up to churn.

The current justified epoch must be at most the previous epoch.

Once justification runs, the previous justified epoch must be below the previous epoch.

The sets and weights of the model must match the state for both recent epochs.

Take a justified checkpoint and an epoch, from its own epoch on and at most two back.

The block of the checkpoint must be below that of the root the state records for that epoch.

The blocks of the roots that the state records for epochs at most two back must be in order.

Once justification runs, a root recorded for the previous epoch needs one for the epoch two back.

The two justified checkpoints must be slack-justified.

The bits must carry their facts for the current epoch.

The finalized checkpoint must be slack-finalized.

Then the bits carry their facts for the next epoch after the step.

The finalized checkpoint after the step is slack-finalized. -/
theorem processJustificationAndFinalization_slackBits
    (flagsVoted : TargetFlagsVoted attested state)
    (pendingVoted : PendingVoted attested state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β)
    (contains : ffgVotes block attested ⊆ votes)
    (settled : JustifiedSettled state)
    (separated : JustifiedSeparated state)
    (sets : ∀ current : Bool, TargetSetsMatch V U W block state
      (if current then getCurrentEpoch state else getPreviousEpoch state))
    (chain : ∀ (current : Bool) (epoch : Epoch) (root : Root),
      (recentJustified state current).epoch ≤ epoch →
      (getCurrentEpoch state).toNat ≤ epoch.toNat + 2 →
      getBlockRoot state epoch = .ok root →
        block (recentJustified state current).root ≤ block root)
    (ordered : ∀ (older newer : Epoch) (olderRoot newerRoot : Root), older ≤ newer →
      (getCurrentEpoch state).toNat ≤ older.toNat + 2 →
      getBlockRoot state older = .ok olderRoot → getBlockRoot state newer = .ok newerRoot →
        block olderRoot ≤ block newerRoot)
    (recorded : GENESIS_EPOCH + 1 < getCurrentEpoch state →
      (∃ root, getBlockRoot state (getPreviousEpoch state) = .ok root) →
      ∃ root, getBlockRoot state (getCurrentEpoch state - 2) = .ok root)
    (holds : SlackJustifiedCheckpoints V U W genesis votes block state)
    (bits : SlackBits V U W genesis votes block (getCurrentEpoch state).toNat state)
    (finalized : SlackFinalized V U W genesis votes (state.finalizedCheckpoint.toFfg block))
    (computed : processJustificationAndFinalization state = .ok after) :
    SlackBits V U W genesis votes block ((getCurrentEpoch state).toNat + 1) after ∧
      SlackFinalized V U W genesis votes (after.finalizedCheckpoint.toFfg block) := by
  rcases processJustificationAndFinalization_weighed (votes := votes) flagsVoted pendingVoted
    large block contains computed with ⟨early, rfl⟩ | ⟨late, total, previousBalance,
      currentBalance, -, weighed, link⟩
  · -- The first two epochs change nothing, and the bits stay clear.
    have small := UInt64.le_iff_toNat_le.mp early
    rw [toNat_genesisEpoch_add_one] at small
    obtain ⟨clear0, clear1⟩ := bits.early (by omega)
    refine ⟨⟨fun _ => ⟨clear0, clear1⟩, fun set => ?_, fun set => ?_⟩, finalized⟩
    · rw [clear0] at set
      cases set
    · rw [clear1] at set
      cases set
  have two := toNat_sub_two late
  have late' := UInt64.lt_iff_toNat_lt.mp late
  rw [toNat_genesisEpoch_add_one] at late'
  obtain ⟨threshold, previousWeight, currentWeight, thresholdOk, previousOk, currentOk, newCurrent,
    newPrevious, newOlder, finalizedCases⟩ := weighJustificationAndFinalization_bits weighed
  obtain ⟨previousJustified, -, -, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
  -- The step keeps the slot and the buffer of roots.
  have rootsEq : ∀ epoch, getBlockRoot after epoch = getBlockRoot state epoch := by
    obtain ⟨-, roots, -⟩ := processJustificationAndFinalization_keeps computed
    have slot : after.slot = state.slot := by rw [← rest]
    intro epoch
    simp only [getBlockRoot, getBlockRootAtSlot_congr slot roots]
  have previousNat := getPreviousEpoch_toNat state
  have settled' := UInt64.le_iff_toNat_le.mp settled
  have below := UInt64.lt_iff_toNat_lt.mp (separated late)
  -- A passing test of the current epoch gives a slack link from the old current justified one.
  have currentLink : ∀ root, threshold ≤ currentWeight →
      getBlockRoot state (getCurrentEpoch state) = .ok root →
        SlackLink V U W votes (state.currentJustifiedCheckpoint.toFfg block)
          ⟨block root, (getCurrentEpoch state).toNat⟩ := by
    intro root passed rootOk
    have bound := link true threshold currentWeight root thresholdOk currentOk passed rootOk
    simp only [↓reduceIte] at bound
    exact bound.slackLink (sets true) rootOk (by simp only [Checkpoint.toFfg]; omega)
      (chain true (getCurrentEpoch state) root
        (UInt64.le_iff_toNat_le.mpr (by simp only [recentJustified, ↓reduceIte]; omega))
        (by omega) rootOk)
  -- A passing test of the previous epoch gives a slack link from the old previous justified one.
  have previousLink : ∀ root, threshold ≤ previousWeight →
      getBlockRoot state (getPreviousEpoch state) = .ok root →
        SlackLink V U W votes (state.previousJustifiedCheckpoint.toFfg block)
          ⟨block root, (getPreviousEpoch state).toNat⟩ := by
    intro root passed rootOk
    have bound := link false threshold previousWeight root thresholdOk previousOk passed rootOk
    simp only [Bool.false_eq_true, ↓reduceIte] at bound
    exact bound.slackLink (sets false) rootOk (by simp only [Checkpoint.toFfg]; omega)
      (chain false (getPreviousEpoch state) root (UInt64.le_iff_toNat_le.mpr
        (by simp only [recentJustified, Bool.false_eq_true, ↓reduceIte]; omega))
        (by omega) rootOk)
  -- A set new bit 1 gives a slack link from the old previous justified checkpoint.
  have newPreviousLink : after.justificationBits.bits[1] = true → ∃ root,
      getBlockRoot state (getPreviousEpoch state) = .ok root ∧
        SlackLink V U W votes (state.previousJustifiedCheckpoint.toFfg block)
          ⟨block root, (getPreviousEpoch state).toNat⟩ := by
    intro set
    rcases newPrevious set with ⟨passed, root, rootOk⟩ | old
    · exact ⟨root, rootOk, previousLink root passed rootOk⟩
    obtain ⟨epoch, rootOk, slack⟩ := bits.current old
    have same : state.currentJustifiedCheckpoint.epoch = getPreviousEpoch state :=
      UInt64.toNat_inj.mp (by omega)
    refine ⟨_, by rw [← same]; exact rootOk, ?_⟩
    have target : state.currentJustifiedCheckpoint.toFfg block =
        ⟨block state.currentJustifiedCheckpoint.root, (getPreviousEpoch state).toNat⟩ := by
      simp only [Checkpoint.toFfg, same]
    rw [← target]
    exact slack
  refine ⟨⟨fun small => absurd small (by omega), fun set => ?_,
    fun set older root epoch rootOk => ?_⟩, ?_⟩
  · -- The new bit 0 comes from the link of the current epoch.
    obtain ⟨passed, root, rootOk, checkpoint⟩ := newCurrent set
    rw [checkpoint, previousJustified]
    exact ⟨rfl, by rw [rootsEq]; exact rootOk, currentLink root passed rootOk⟩
  · -- The new bit 1 justifies the checkpoint of the previous epoch.
    have same : older = getPreviousEpoch state := UInt64.toNat_inj.mp (by omega)
    rw [same, rootsEq] at rootOk
    obtain ⟨found, foundOk, slack⟩ := newPreviousLink set
    rw [rootOk, Except.ok.injEq] at foundOk
    subst foundOk
    rw [same]
    exact .link holds.1 slack
  have previousLe := UInt64.le_iff_toNat_le.mp (getPreviousEpoch_le state)
  rcases finalizedCases with same | ⟨same, set0, rule⟩ | ⟨same, set1, rule⟩
  · rw [same]
    exact finalized
  · -- The old current justified checkpoint, with a link to the current epoch.
    rw [same]
    obtain ⟨passed, rootE, rootEOk, -⟩ := newCurrent set0
    have linkE := currentLink rootE passed rootEOk
    rcases rule with sum | ⟨set1, sum⟩
    · exact FinalizedBy.of_one holds.2 linkE.2.1 (by simp only [Checkpoint.toFfg]; omega) linkE
    obtain ⟨rootP, rootPOk, linkP⟩ := newPreviousLink set1
    exact FinalizedBy.of_two holds.2 (.link holds.1 linkP)
      (chain true (getPreviousEpoch state) rootP settled (by omega) rootPOk)
      (ordered _ _ rootP rootE (getPreviousEpoch_le state) (by omega) rootPOk rootEOk)
      (by simp only [Checkpoint.toFfg]; omega) (by simp only [Checkpoint.toFfg]; omega) linkE
  · -- The old previous justified checkpoint, with a link to the previous epoch.
    rw [same]
    obtain ⟨rootP, rootPOk, linkP⟩ := newPreviousLink set1
    rcases rule with sum | ⟨set2, sum⟩
    · exact FinalizedBy.of_one holds.1 linkP.2.1 (by simp only [Checkpoint.toFfg]; omega) linkP
    -- The checkpoint two epochs back is justified by the old bit 1.
    obtain ⟨rootO, rootOOk⟩ := recorded late ⟨rootP, rootPOk⟩
    have justifiedO := bits.previous (newOlder ▸ set2) _ rootO (by omega) rootOOk
    exact FinalizedBy.of_two holds.1 justifiedO
      (chain false _ rootO (UInt64.le_iff_toNat_le.mpr (by
        simp only [recentJustified, Bool.false_eq_true, ↓reduceIte]; omega)) (by omega) rootOOk)
      (ordered _ _ rootO rootP (UInt64.le_iff_toNat_le.mpr (by omega)) (by omega) rootOOk rootPOk)
      (by simp only [Checkpoint.toFfg]; omega) (by simp only [Checkpoint.toFfg]; omega) linkP


/-- One slot keeps the facts of the bits and the finalized checkpoint slack-finalized.

When the slot ends an epoch, justification runs at the state after the caching of the slot.

That caching keeps the roots of the three latest epochs, the flags, the checkpoints and the stakes.

So the hypotheses of justification are asked of the state before the slot.

The bound on the active stake and the sets are asked only when the slot ends an epoch.

The buffer of roots must cover three epochs, as both presets do, so that the caching keeps them.

The current justified epoch must be at most the previous epoch.

The previous justified epoch must be below the previous epoch once justification runs.

Each justified checkpoint must be below the roots that the state records from its epoch on.

The map from roots to blocks must keep in order the roots recorded at consecutive slots.

Then the bits carry their facts for the current epoch after the slot.

The finalized checkpoint after the slot is slack-finalized. -/
theorem advanceSlot_slackBits
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (flagsVoted : TargetFlagsVoted attested state)
    (pendingVoted : PendingVoted attested state)
    (large : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt state index.toNat)
          (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β)
    (contains : ffgVotes block attested ⊆ votes)
    (settled : JustifiedSettled state) (separated : JustifiedSeparated state)
    (sets : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 → ∀ current : Bool,
      TargetSetsMatch V U W block state
        (if current then getCurrentEpoch state else getPreviousEpoch state))
    (roots : RootsAbove block state)
    (links : ∀ link ∈ rootLinks state, block link.1 ≤ block link.2)
    (holds : SlackJustifiedCheckpoints V U W genesis votes block state)
    (bits : SlackBits V U W genesis votes block (getCurrentEpoch state).toNat state)
    (finalized : SlackFinalized V U W genesis votes (state.finalizedCheckpoint.toFfg block))
    (computed : advanceSlot config checks state = .ok after) :
    SlackBits V U W genesis votes block (getCurrentEpoch after).toNat after ∧
      SlackFinalized V U W genesis votes (after.finalizedCheckpoint.toFfg block) := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, afterEq⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  obtain ⟨cached', cachedOk', -, afterRoots, -, -, -, afterSlot⟩ :=
    advanceSlot_cachedRoots computed
  rw [cachedOk, Except.ok.injEq] at cachedOk'
  subst cachedOk'
  have validators : cached.validators = state.validators := by rw [cachedEq]
  have currentEq : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, cachedFrame.slot]
  have previousEq : getPreviousEpoch cached = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  have startLe : (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      state.slot.toNat := by
    rw [getCurrentEpoch_toNat]
    exact Nat.div_mul_le_self _ _
  -- The caching keeps the roots of the three latest epochs.
  have cachedRoots : ∀ epoch : Epoch, 0 < preset.SLOTS_PER_EPOCH.toNat →
      (getCurrentEpoch state).toNat ≤ epoch.toNat + 2 →
        getBlockRoot cached epoch = getBlockRoot state epoch := fun epoch positive near =>
    getBlockRoot_processSlot cachedOk (slot_lt_epoch_add_historical_of_le positive 2 window near)
  -- The state after the slot reads the roots of the cached state, before its slot.
  have afterIff : ∀ (epoch : Epoch) (root : Root), 0 < preset.SLOTS_PER_EPOCH.toNat →
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat →
      (getCurrentEpoch state).toNat ≤ epoch.toNat + 2 →
        (getBlockRoot after epoch = .ok root ↔ getBlockRoot cached epoch = .ok root) := by
    intro epoch root positive before near
    refine getBlockRoot_succ_iff afterRoots (by rw [afterSlot, cachedFrame.slot]) ?_ ?_
    · rw [cachedFrame.slot]
      exact before
    · rw [cachedFrame.slot]
      exact slot_lt_epoch_add_historical_of_le positive 2 window near
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have positive := slotsPerEpoch_pos_of_mod sum boundary
    have window' : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
      omega
    have last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := by
      have nextEq : next = state.slot + 1 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_one, ← sum, Nat.mod_eq_of_lt next.toNat_lt]
      rw [← nextEq]
      exact boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have afterEpoch : (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1 := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, afterEq]
      exact epochs
    -- The slot is the last one of its epoch.
    have lastSlot : state.slot.toNat + 1 =
        ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
      have split := Nat.div_add_mod next.toNat preset.SLOTS_PER_EPOCH.toNat
      have zero : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
        have mod := congrArg UInt64.toNat boundary
        rwa [UInt64.toNat_mod] at mod
      rw [zero, epochs, ← getCurrentEpoch_toNat, Nat.mul_comm] at split
      omega
    rw [Nat.add_mul, Nat.one_mul] at lastSlot
    have active : ∀ epoch, getActiveValidatorIndices cached epoch =
        getActiveValidatorIndices state epoch := by
      intro epoch
      unfold getActiveValidatorIndices
      rw [validators]
    have balances : ∀ index, balanceAt cached index = balanceAt state index := by
      intro index
      unfold balanceAt
      rw [validators]
    have recentEq : ∀ current, recentJustified cached current = recentJustified state current := by
      intro current
      simp only [recentJustified, cachedFrame.currentJustified, cachedFrame.previousJustified]
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    have justifiedSlot : justified.slot = cached.slot := by
      rcases processJustificationAndFinalization_ok justifiedOk with same | ⟨_, _, _, weighed⟩
      · rw [same]
      · obtain ⟨-, -, -, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
        rw [← rest]
    obtain ⟨-, justifiedRoots, -⟩ := processJustificationAndFinalization_keeps justifiedOk
    have justifiedReads : ∀ epoch, getBlockRoot justified epoch = getBlockRoot cached epoch := by
      intro epoch
      simp only [getBlockRoot, getBlockRootAtSlot_congr justifiedSlot justifiedRoots]
    have step := processJustificationAndFinalization_slackBits
      (flagsVoted.of_processSlot positive window' cachedOk)
      (pendingVoted.of_processSlot cachedOk) (by
        simp only [balances, active, currentEq]
        exact large last) block contains (by
        unfold JustifiedSettled
        rw [cachedFrame.currentJustified, previousEq]
        exact settled) (separated.of_frame cachedFrame) (fun current root read => ?_)
      (fun current epoch root le near read => ?_)
      (fun older newer olderRoot newerRoot le near olderRead newerRead => ?_)
      (fun late previous => ?_) (by
        unfold SlackJustifiedCheckpoints
        rw [cachedFrame.previousJustified, cachedFrame.currentJustified]
        exact holds) ?_ (by rw [cachedFrame.finalized]; exact finalized) justifiedOk
    · -- The epoch step carries over to the state after the slot.
      obtain ⟨newBits, newFinalized⟩ := step
      rw [currentEq] at newBits
      have bitsEq : after.justificationBits = justified.justificationBits := by
        rw [afterEq]
        exact frame.justificationBits
      have currentJustifiedEq : after.currentJustifiedCheckpoint =
          justified.currentJustifiedCheckpoint := by
        rw [afterEq]
        exact frame.currentJustified
      have previousJustifiedEq : after.previousJustifiedCheckpoint =
          justified.previousJustifiedCheckpoint := by
        rw [afterEq]
        exact frame.previousJustified
      have finalizedEq : after.finalizedCheckpoint = justified.finalizedCheckpoint := by
        rw [afterEq]
        exact frame.finalized
      rw [afterEpoch, finalizedEq]
      refine ⟨⟨fun small => ?_, fun set => ?_, fun set older root epoch read => ?_⟩,
        newFinalized⟩
      · rw [bitsEq]
        exact newBits.early small
      · rw [bitsEq] at set
        rw [currentJustifiedEq, previousJustifiedEq]
        obtain ⟨epoch, read, slack⟩ := newBits.current set
        refine ⟨epoch, ?_, slack⟩
        rw [justifiedReads] at read
        rw [afterIff _ _ positive
          (by rw [← cachedFrame.slot]; exact getBlockRoot_start_lt read) (by omega)]
        exact read
      · rw [bitsEq] at set
        have scaled : (older.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat =
            (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat := by
          rw [show older.toNat + 1 = (getCurrentEpoch state).toNat by omega]
        rw [Nat.add_mul, Nat.one_mul] at scaled
        rw [afterIff _ _ positive (by omega) (by omega), ← justifiedReads] at read
        exact newBits.previous set older root epoch read
    · -- The sets of the model match the cached state.
      have previousNat := getPreviousEpoch_toNat state
      have near : (getCurrentEpoch state).toNat ≤
          (if current then getCurrentEpoch state else getPreviousEpoch state).toNat + 2 := by
        cases current
        · simp only [Bool.false_eq_true, ↓reduceIte]
          omega
        · simp only [↓reduceIte]
          omega
      rw [currentEq, previousEq] at read ⊢
      rw [cachedRoots _ positive near] at read
      simp only [active, balances]
      exact sets last current root read
    · -- Each justified checkpoint is below the roots that the cached state records.
      rw [currentEq] at near
      rw [cachedRoots _ positive near] at read
      rw [recentEq] at le ⊢
      exact roots.le_of_epoch_le current le read
    · -- The cached state records roots in order.
      rw [currentEq] at near
      have newerNear : (getCurrentEpoch state).toNat ≤ newer.toNat + 2 := by
        have := UInt64.le_iff_toNat_le.mp le
        omega
      rw [cachedRoots _ positive near] at olderRead
      rw [cachedRoots _ positive newerNear] at newerRead
      exact le_of_rootLinks_getBlockRoot links le olderRead newerRead
    · -- A read of the previous epoch shows that the epoch two back fits in the buffer too.
      obtain ⟨rootP, readP⟩ := previous
      rw [currentEq] at late ⊢
      rw [previousEq] at readP
      have two := toNat_sub_two late
      have late' := UInt64.lt_iff_toNat_lt.mp late
      rw [toNat_genesisEpoch_add_one] at late'
      have previousNat := getPreviousEpoch_toNat state
      have beforeP := getBlockRoot_start_lt readP
      obtain ⟨startP, startPOk, readP⟩ := getBlockRoot_ok_iff.mp readP
      have startPEq := (mulChecked_ok_iff.mp startPOk).2
      obtain ⟨-, fitsP, -, -⟩ := getBlockRootAtSlot_ok_iff.mp readP
      rw [cachedFrame.slot, previousNat] at beforeP
      rw [previousNat] at startPEq
      -- The epoch two back starts one epoch before the previous one, and two before the current.
      have oneBack : ((getCurrentEpoch state).toNat - 1) * preset.SLOTS_PER_EPOCH.toNat =
          ((getCurrentEpoch state).toNat - 2) * preset.SLOTS_PER_EPOCH.toNat +
            preset.SLOTS_PER_EPOCH.toNat := by
        rw [← Nat.succ_mul]
        congr 1
        omega
      have twoBack : (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat =
          ((getCurrentEpoch state).toNat - 2) * preset.SLOTS_PER_EPOCH.toNat +
            2 * preset.SLOTS_PER_EPOCH.toNat := by
        rw [← Nat.add_mul]
        congr 1
        omega
      rw [← two] at oneBack twoBack
      exact getBlockRoot_exists (by rw [cachedFrame.slot]; omega) (by omega)
        (by rw [cachedFrame.slot]; omega)
    · -- The bits carry their facts at the cached state.
      rw [currentEq]
      refine ⟨fun small => ?_, fun set => ?_, fun set older root epoch read => ?_⟩
      · rw [cachedFrame.justificationBits]
        exact bits.early small
      · rw [cachedFrame.justificationBits] at set
        rw [cachedFrame.currentJustified, cachedFrame.previousJustified]
        obtain ⟨epoch, read, slack⟩ := bits.current set
        refine ⟨epoch, ?_, slack⟩
        rw [cachedRoots _ positive (by omega)]
        exact read
      · rw [cachedFrame.justificationBits] at set
        rw [cachedRoots _ positive (by omega)] at read
        exact bits.previous set older root epoch read
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have afterEpoch : (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, afterEq]
      exact nextSlot_epoch_of_inside sum inside
    have positive : 1 ≤ (getCurrentEpoch state).toNat → 0 < preset.SLOTS_PER_EPOCH.toNat := by
      intro one
      refine Nat.pos_of_ne_zero fun zero => ?_
      rw [getCurrentEpoch_toNat, zero, Nat.div_zero] at one
      omega
    have bitsEq : after.justificationBits = state.justificationBits := by
      rw [afterEq]
      exact cachedFrame.justificationBits
    have currentJustifiedEq : after.currentJustifiedCheckpoint =
        state.currentJustifiedCheckpoint := by
      rw [afterEq]
      exact cachedFrame.currentJustified
    have previousJustifiedEq : after.previousJustifiedCheckpoint =
        state.previousJustifiedCheckpoint := by
      rw [afterEq]
      exact cachedFrame.previousJustified
    have finalizedEq : after.finalizedCheckpoint = state.finalizedCheckpoint := by
      rw [afterEq]
      exact cachedFrame.finalized
    rw [afterEpoch, finalizedEq]
    refine ⟨⟨fun small => ?_, fun set => ?_, fun set older root epoch read => ?_⟩, finalized⟩
    · rw [bitsEq]
      exact bits.early small
    · -- The current justified checkpoint keeps its root.
      rw [bitsEq] at set
      rw [currentJustifiedEq, previousJustifiedEq]
      obtain ⟨epoch, read, slack⟩ := bits.current set
      refine ⟨epoch, ?_, slack⟩
      have positive' := positive (by omega)
      rw [afterIff _ _ positive' (getBlockRoot_start_lt read) (by omega),
        cachedRoots _ positive' (by omega)]
      exact read
    · -- The root of the epoch two back stays.
      rw [bitsEq] at set
      have positive' := positive (by omega)
      have scaled : (older.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat := by
        rw [epoch]
        exact startLe
      rw [Nat.add_mul] at scaled
      rw [afterIff _ _ positive' (by omega) (by omega),
        cachedRoots _ positive' (by omega)] at read
      exact bits.previous set older root epoch read

end EthLib.Consensus
