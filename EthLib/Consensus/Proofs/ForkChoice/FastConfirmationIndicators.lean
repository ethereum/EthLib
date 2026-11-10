module

public import EthLib.Base.Proofs.FilterM
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation
public import EthLib.Consensus.Proofs.Models.ForkChoice.HonestSupport
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Proofs: the indicators that the fast confirmation rule computes

The rule confirms a block when its support from the store exceeds its safety threshold.

That check is Definition 4 of the fast confirmation paper, [arXiv 2405.00549v4][fcr].

The paper writes it, in its equation (5), as `S > Φ / 2 + β W - I`.

Here `S` is the support of the block, and `I` the stake of the known equivocators.

`W` is the weight of the committees from the slot of the block to the last slot.

`Φ` is the largest weight that could still vote for a sibling, plus the boost, less a discount.

The store computes each term in Gwei, with its own roundings.

It weighs the committees of a range exactly, from the effective balances of their active members.

A range with a whole epoch weighs the total active balance instead, which is no smaller.

Its `Φ` is the committee weight since the parent, plus the boost.

A discount is then taken off.

It comes from the votes for the parent in the empty slots before the block.

Its share of the adversary is the committee weight of `W`, divided by 100 and rounded down.

That share is then multiplied by the threshold in percent, and the equivocators are taken off.

So the weight covers the stake of `W`, and the share covers β of it for balances in 100 Gwei.

An average weight per slot in place of the exact one would not cover it.

With that cover, Lemmas 4 and 3 of the paper give the honest support of a confirmed block.

Twice that support, plus the discount, exceeds the committee weight and the boost.

The range of slots of the adversary starts at the block, or at its epoch when its parent is older.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The store's adversary for a range of slots, step by step.

It is the share of the committee weight, less the known equivocators of the committees. -/
theorem computeAdversarialWeight_steps {head : Root} {balanceSource : BeaconState preset fork}
    {startSlot endSlot : Slot} {adversary : Gwei}
    (result : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary) :
    ∃ weight share equivocation,
      store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
        .ok weight ∧
      mulChecked (weight / 100) config.CONFIRMATION_BYZANTINE_THRESHOLD = .ok share ∧
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation ∧
      adversary = saturatingSub share equivocation := by
  simp only [computeAdversarialWeight, bind_ok_iff, mapError_ok_iff] at result
  obtain ⟨⟨weight, members⟩, pairOk, share, shareOk, rest⟩ := result
  -- The members come from the weight, or are read again when the weight did not need them.
  obtain ⟨participants, found, rest⟩ :
      ∃ participants, store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants ∧
        ∃ equivocation,
          store.getEquivocationScoreOf balanceSource participants = .ok equivocation ∧
            adversary = saturatingSub share equivocation := by
    cases members with
    | none =>
      simp only [bind_ok_iff] at rest
      obtain ⟨participants, found, equivocation, equivocationOk, final⟩ := rest
      simp only [pure, Except.pure, Except.ok.injEq] at final
      exact ⟨participants, found, equivocation, equivocationOk, final.symm⟩
    | some members =>
      simp only [pure, Except.pure, bind, Except.bind] at rest
      split at rest
      · cases rest
      · rename_i equivocation equivocationOk
        simp only [Except.ok.injEq] at rest
        exact ⟨members, getCommitteesBetweenSlots_of_computeCommitteeWeightAndMembers pairOk,
          equivocation, equivocationOk, rest.symm⟩
  obtain ⟨equivocation, equivocationOk, final⟩ := rest
  refine ⟨weight, share, equivocation, ?_, shareOk, ?_, final⟩
  · simp [computeCommitteeWeightBetweenSlots, pairOk, bind, Except.bind, pure, Except.pure]
  · simp [getEquivocationScore, found, equivocationOk, bind, Except.bind]

/-- The store's adversary for a range of slots: its share of the weight, less the equivocators.

The share is the weight of the committees divided by 100, rounded down, times the threshold.

The share is then at most the adversary plus the stake of the equivocators. -/
theorem computeAdversarialWeight_share {head : Root} {balanceSource : BeaconState preset fork}
    {startSlot endSlot : Slot} {weight equivocation adversary : Gwei}
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight)
    (equivocationOk :
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation)
    (result : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary) :
    weight.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤
      adversary.toNat + equivocation.toNat := by
  obtain ⟨e, share, q, eOk, shareOk, qOk, rfl⟩ := computeAdversarialWeight_steps result
  rw [weightOk, Except.ok.injEq] at eOk
  subst eOk
  rw [equivocationOk, Except.ok.injEq] at qOk
  subst qOk
  rw [mulChecked_ok_iff] at shareOk
  rw [toNat_saturatingSub, shareOk.2, UInt64.toNat_div]
  have hundred : UInt64.toNat 100 = 100 := rfl
  rw [hundred]
  omega

/-- The adversary of a block in a later epoch than its parent counts from the start of its epoch.

The range of slots ends at the last slot before the current one. -/
theorem getAdversarialWeight_of_lt {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot startSlot lastSlot : Slot} {block : BeaconBlock preset fork}
    {epoch parentEpoch : Epoch}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (epochOk : store.getBlockEpoch root = .ok epoch)
    (parentEpochOk : store.getBlockEpoch block.parentRoot = .ok parentEpoch)
    (later : parentEpoch < epoch)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok startSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot) :
    store.getAdversarialWeight config head balanceSource root =
      store.computeAdversarialWeight config head balanceSource startSlot lastSlot := by
  simp [getAdversarialWeight, slotOk, blockOk, epochOk, parentEpochOk, later, startOk, lastOk,
    bind, Except.bind, Except.mapError]

/-- The adversary of a block in the epoch of its parent counts from the slot of the block.

The range of slots ends at the last slot before the current one. -/
theorem getAdversarialWeight_of_not_lt {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot lastSlot : Slot} {block : BeaconBlock preset fork} {epoch parentEpoch : Epoch}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (epochOk : store.getBlockEpoch root = .ok epoch)
    (parentEpochOk : store.getBlockEpoch block.parentRoot = .ok parentEpoch)
    (notLater : ¬parentEpoch < epoch)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot) :
    store.getAdversarialWeight config head balanceSource root =
      store.computeAdversarialWeight config head balanceSource block.slot lastSlot := by
  simp [getAdversarialWeight, slotOk, blockOk, epochOk, parentEpochOk, notLater, lastOk,
    bind, Except.bind, pure, Except.pure, Except.mapError]

/-- The store's safety threshold, doubled, covers its terms, up to the discount and one Gwei.

The terms are the committee weight since the parent, the boost and twice the adversary.

The halving of the threshold rounds down, which loses at most one Gwei. -/
theorem computeSafetyThreshold_bound {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary threshold : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (result : store.computeSafetyThreshold config head root balanceSource = .ok threshold) :
    maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat ≤
      2 * threshold.toNat + discount.toNat + 1 := by
  simp only [computeSafetyThreshold, bind_ok_iff, mapError_ok_iff] at result
  obtain ⟨c, cOk, b, bOk, pb, pbOk, ps, psOk, f, fOk, l, lOk, m, mOk, d, dOk, a, aOk,
    wb, wbOk, db, dbOk, bd, bdOk, done⟩ := result
  rw [slotOk, Except.ok.injEq] at cOk
  subst cOk
  rw [blockOk, Except.ok.injEq] at bOk
  subst bOk
  rw [parentOk, Except.ok.injEq] at pbOk
  subst pbOk
  rw [boostOk, Except.ok.injEq] at psOk
  subst psOk
  rw [firstOk, Except.ok.injEq] at fOk
  subst fOk
  rw [lastOk, Except.ok.injEq] at lOk
  subst lOk
  rw [weightOk, Except.ok.injEq] at mOk
  subst mOk
  rw [discountOk, Except.ok.injEq] at dOk
  subst dOk
  rw [adversaryOk, Except.ok.injEq] at aOk
  subst aOk
  rw [addChecked_ok_iff] at wbOk bdOk
  rw [mulChecked_ok_iff] at dbOk
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  have two : UInt64.toNat 2 = 2 := rfl
  rw [two] at dbOk
  split_ifs with lower
  · rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lower), two]
    rw [UInt64.lt_iff_toNat_lt] at lower
    omega
  · rw [UInt64.lt_iff_toNat_lt] at lower
    simp only [UInt64.toNat_zero]
    omega

/-- The terms of a safety threshold that the store computes, each from its own step.

They are the current slot, the block and its parent, and the boost.

They are also the first and last slots of the range since the parent, and its committee weight.

They are also the discount and the adversary of the block. -/
theorem computeSafetyThreshold_eq_ok {head root : Root} {balanceSource : BeaconState preset fork}
    {threshold : Gwei}
    (result : store.computeSafetyThreshold config head root balanceSource = .ok threshold) :
    ∃ currentSlot block parentBlock proposerScore firstSlot lastSlot maximumSupport
      discount adversary,
      store.getCurrentSlot config = .ok currentSlot ∧ store.block root = .ok block ∧
      store.block block.parentRoot = .ok parentBlock ∧
      computeProposerScore config balanceSource = .ok proposerScore ∧
      addChecked parentBlock.slot 1 = .ok firstSlot ∧ subChecked currentSlot 1 = .ok lastSlot ∧
      store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
        .ok maximumSupport ∧
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount ∧
      store.getAdversarialWeight config head balanceSource root = .ok adversary := by
  have steps := result
  simp only [computeSafetyThreshold, bind_ok_iff, mapError_ok_iff] at steps
  obtain ⟨c, cOk, b, bOk, pb, pbOk, ps, psOk, f, fOk, l, lOk, m, mOk, d, dOk, a, aOk,
    -⟩ := steps
  exact ⟨c, b, pb, ps, f, l, m, d, a, cOk, bOk, pbOk, psOk, fOk, lOk, mOk, dOk, aOk⟩

/-- The range of slots of the adversary of a block, and the adversary over it.

The range ends at the last slot before the current one.

It starts at the slot of the block, or at the start of the epoch of the block. -/
theorem getAdversarialWeight_eq_ok {head root : Root} {balanceSource : BeaconState preset fork}
    {adversary : Gwei}
    (result : store.getAdversarialWeight config head balanceSource root = .ok adversary) :
    ∃ currentSlot block startSlot lastSlot,
      store.getCurrentSlot config = .ok currentSlot ∧ store.block root = .ok block ∧
      subChecked currentSlot 1 = .ok lastSlot ∧
      (startSlot = block.slot ∨
        computeStartSlotAtEpoch preset (computeEpochAtSlot preset block.slot) = .ok startSlot) ∧
      store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
        .ok adversary := by
  have steps := result
  simp only [getAdversarialWeight, bind_ok_iff] at steps
  obtain ⟨c, cOk, b, bOk, e, eOk, pe, -, range⟩ := steps
  have epoch : computeEpochAtSlot preset b.slot = e := by
    simpa [getBlockEpoch, bOk, bind, Except.bind, pure, Except.pure] using eOk
  split_ifs at range
  · simp only [bind_ok_iff, mapError_ok_iff] at range
    obtain ⟨start, startOk, l, lOk, done⟩ := range
    exact ⟨c, b, start, l, cOk, bOk, lOk, .inr (epoch ▸ startOk), done⟩
  · simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at range
    obtain ⟨start, startOk, l, lOk, done⟩ := range
    exact ⟨c, b, start, l, cOk, bOk, lOk, .inl startOk.symm, done⟩

/-- The terms of the store's adversary over a range of slots, each from its own step.

They are the weight of the committees of the range, and the known equivocators. -/
theorem computeAdversarialWeight_eq_ok {head : Root} {balanceSource : BeaconState preset fork}
    {startSlot endSlot : Slot} {adversary : Gwei}
    (result : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary) :
    ∃ weight equivocation,
      store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
        .ok weight ∧
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation := by
  obtain ⟨weight, -, equivocation, weightOk, -, equivocationOk, -⟩ :=
    computeAdversarialWeight_steps result
  exact ⟨weight, equivocation, weightOk, equivocationOk⟩

/-- A block is confirmed when its support and its threshold are computed, the first above. -/
theorem isOneConfirmed_eq_ok_true_iff {head root : Root}
    {balanceSource : BeaconState preset fork} {tally : VoteTally} :
    store.isOneConfirmed config head balanceSource tally root = .ok true ↔
      ∃ support threshold, store.scoreFromTally tally ⟨root, .pending⟩ = .ok support ∧
        store.computeSafetyThreshold config head root balanceSource = .ok threshold ∧
        threshold < support := by
  simp [isOneConfirmed, bind_ok_iff, pure, Except.pure]

/-- A confirmed block has support above its safety threshold. -/
theorem threshold_lt_of_isOneConfirmed {head root : Root} {balanceSource : BeaconState preset fork}
    {tally : VoteTally} {support threshold : Gwei}
    (supportOk : store.scoreFromTally tally ⟨root, .pending⟩ = .ok support)
    (thresholdOk : store.computeSafetyThreshold config head root balanceSource = .ok threshold)
    (confirmed : store.isOneConfirmed config head balanceSource tally root = .ok true) :
    threshold.toNat < support.toNat := by
  simp only [isOneConfirmed, supportOk, thresholdOk, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, decide_eq_true_eq] at confirmed
  exact UInt64.lt_iff_toNat_lt.mp confirmed

/-- A total balance of some indices covers the stake of a set among them. -/
theorem stake_le_of_getTotalBalance {balanceSource : BeaconState preset fork}
    {indices : List ValidatorIndex} {total : Gwei} {W : Finset ValidatorIndex}
    (totalOk : getTotalBalance balanceSource indices = .ok total) (among : ∀ v ∈ W, v ∈ indices) :
    stake (fun v => balanceAt balanceSource v.toNat) W ≤ total.toNat := by
  obtain ⟨-, -, total⟩ := getTotalBalance_ok_iff_stake.mp totalOk
  rw [total]
  exact le_max_of_le_right (stake_mono fun v member => List.mem_toFinset.mpr (among v member))

/-- The store's weight of the committees of a range covers the stake of their active members.

A member weighs its effective balance in the source of balances.

It is active when that source holds it, active in the epoch of that source. -/
theorem stake_le_computeCommitteeWeightBetweenSlots {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    {participants : Std.TreeSet ValidatorIndex} {weight : Gwei} {W : Finset ValidatorIndex}
    (participantsOk : store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight)
    (inside : ∀ v ∈ W, v ∈ participants ∧ ∃ validator,
      balanceSource.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch balanceSource) = true) :
    stake (fun v => balanceAt balanceSource v.toNat) W ≤ weight.toNat := by
  by_cases empty : endSlot < startSlot
  · rw [getCommitteesBetweenSlots_of_gt empty, Except.ok.injEq] at participantsOk
    have : W = ∅ := Finset.eq_empty_of_forall_notMem fun v member => by
      have := (inside v member).1
      simp [← participantsOk] at this
    simp [this, stake_empty]
  have notGt : ¬startSlot > endSlot := empty
  simp only [computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at weightOk
  obtain ⟨⟨_, members⟩, weightOk, rfl⟩ := weightOk
  simp only [computeCommitteeWeightAndMembers, notGt, ↓reduceIte, bind_ok_iff] at weightOk
  obtain ⟨covered, -, weightOk⟩ := weightOk
  cases covered
  · -- The members of the committees count once each, when active.
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff] at weightOk
    obtain ⟨found, foundOk, active, activeOk, total, totalOk, final⟩ := weightOk
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, -⟩ := final
    rw [participantsOk, Except.ok.injEq] at foundOk
    subst foundOk
    refine stake_le_of_getTotalBalance totalOk fun v member => ?_
    obtain ⟨inParticipants, validator, atIndex, isActive⟩ := inside v member
    refine mem_filterM_ok_of_test activeOk (Std.TreeSet.mem_toList.mpr inParticipants) ?_
    simp [validatorAt, atIndex, isActive, bind, Except.bind, pure, Except.pure]
  · -- A whole epoch weighs the total active balance, which counts every active validator.
    simp only [↓reduceIte, bind_ok_iff, mapError_ok_iff] at weightOk
    obtain ⟨total, totalOk, final⟩ := weightOk
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, -⟩ := final
    refine stake_le_of_getTotalBalance totalOk fun v member => ?_
    obtain ⟨-, validator, atIndex, isActive⟩ := inside v member
    simp only [getActiveValidatorIndices, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, List.mem_zipIdx_iff_getElem?, Prod.exists]
    exact ⟨validator, v.toNat, by simpa using atIndex, isActive, by simp⟩

/-- Lemmas 4 and 3 for a block that the store confirms: honest support above half of `Φ`.

Here `Φ` is the store's: the committee weight since the parent, plus the boost.

The discount is taken off it, and is added to the other side so that nothing truncates.

A validator weighs its effective balance in the source of balances.

The supporters are validators whose stake is the support of the block in the store.

The equivocators are validators whose stake is that of the known equivocators in the store.

Both lie in a set `W` of members of the committees of a range of slots.

Each member of `W` is active in the source of balances.

The supporters and the equivocators are apart.

The store's adversary over that range must be its adversary for the block.

The range that the store uses for the block is one such range.

Assume that the Byzantine validators hold at most β of the stake of `W`.

That is Assumption 2 when `W` holds every active member of the committees of the range.

Here β is the threshold of the configuration, in percent, and no equivocator is honest.

Assume also that each effective balance in `W` is a whole number of 100 Gwei.

The store rounds the weight down to 100 Gwei for its adversary, and this keeps β of `W` below it.

Effective balances are whole increments, and an increment is 10^9 Gwei in the presets.

When the discount exceeds the committee weight and the boost, this says nothing on the support. -/
theorem lt_two_mul_honest_support_of_isOneConfirmed {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] {W supporters equivocators : Finset ValidatorIndex} {head root : Root}
    {balanceSource : BeaconState preset fork} {tally : VoteTally}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {participants : Std.TreeSet ValidatorIndex}
    {proposerScore maximumSupport discount adversary threshold support weight equivocation : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (participantsOk : store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot lastSlot =
      .ok weight)
    (equivocationOk :
      store.getEquivocationScore head balanceSource startSlot lastSlot = .ok equivocation)
    (thresholdOk : store.computeSafetyThreshold config head root balanceSource = .ok threshold)
    (supportOk : store.scoreFromTally tally ⟨root, .pending⟩ = .ok support)
    (confirmed : store.isOneConfirmed config head balanceSource tally root = .ok true)
    (supportStake : stake (fun v => balanceAt balanceSource v.toNat) supporters = support.toNat)
    (equivocationStake :
      stake (fun v => balanceAt balanceSource v.toNat) equivocators = equivocation.toNat)
    (supportersIn : supporters ⊆ W) (equivocatorsIn : equivocators ⊆ W)
    (inside : ∀ v ∈ W, v ∈ participants ∧ ∃ validator,
      balanceSource.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch balanceSource) = true)
    (aligned : ∀ v ∈ W, balanceAt balanceSource v.toNat % 100 = 0)
    (apart : Disjoint supporters equivocators) (dishonest : ∀ v ∈ equivocators, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat) W J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ supporters | v ∈ J} := by
  set w := fun v : ValidatorIndex => balanceAt balanceSource v.toNat
  have bound := computeSafetyThreshold_bound slotOk blockOk parentOk boostOk firstOk lastOk
    maximumOk discountOk adversaryOk thresholdOk
  have above := threshold_lt_of_isOneConfirmed supportOk thresholdOk confirmed
  have share := computeAdversarialWeight_share weightOk equivocationOk rangeOk
  -- The weight covers the stake of `W`, and that stake is a whole number of 100 Gwei.
  have covered := stake_le_computeCommitteeWeightBetweenSlots participantsOk weightOk inside
  have whole : 100 ∣ stake w W := Finset.dvd_sum fun v member => Nat.dvd_of_mod_eq_zero
    (aligned v member)
  have cover : stake w W ≤ weight.toNat / 100 * 100 := by
    obtain ⟨k, hk⟩ := whole
    rw [hk] at covered ⊢
    rw [Nat.mul_comm 100 k]
    exact Nat.mul_le_mul_right 100 ((Nat.le_div_iff_mul_le (by norm_num)).mpr
      (by rw [Nat.mul_comm]; exact covered))
  -- The cover of the stake gives the cover of its Byzantine share.
  replace cover : config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake w W ≤
      100 * (weight.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by
    calc config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake w W
        ≤ config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * (weight.toNat / 100 * 100) :=
          Nat.mul_le_mul_left _ cover
      _ = 100 * (weight.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by
          ring
  -- A discount above the other terms makes the bound hold at once.
  by_cases large : maximumSupport.toNat + proposerScore.toNat < discount.toNat
  · omega
  have phi := Nat.sub_add_cancel (Nat.le_of_not_lt large)
  suffices maximumSupport.toNat + proposerScore.toNat - discount.toNat <
      2 * stake w {v ∈ supporters | v ∈ J} by omega
  generalize maximumSupport.toNat + proposerScore.toNat - discount.toNat = Φ at phi ⊢
  refine lt_two_mul_honest_support byzantine supportersIn equivocatorsIn apart dishonest ?_
  rw [supportStake, equivocationStake, Nat.mul_assoc 2]
  generalize config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake w W = byzantineShare at cover ⊢
  generalize weight.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat = storeShare
    at cover share ⊢
  omega

end Store

end EthLib.Consensus
