module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation
public import EthLib.Consensus.Proofs.Models.ForkChoice.HonestSupport

/-!
# Proofs: the indicators that the fast confirmation rule computes

The rule confirms a block when its support from the store exceeds its safety threshold.

That check is Definition 4 of the fast confirmation paper, [arXiv 2405.00549v4][fcr].

The paper writes it, in its equation (5), as `S > Φ / 2 + β W - I`.

Here `S` is the support of the block, and `I` the stake of the known equivocators.

`W` is the weight of the committees from the slot of the block to the last slot.

`Φ` is the largest weight that could still vote for a sibling, plus the boost, less a discount.

The store computes each term in Gwei, with its own estimates and roundings.

Its estimate of `Φ` is the estimated committee weight since the parent, plus the boost.

A discount is taken off that estimate.

It comes from the votes for the parent in the empty slots before the block.

Its share of the adversary is the estimated weight of `W`, divided by 100 and rounded down.

That share is then multiplied by the threshold in percent, and the equivocators are taken off.

So a confirmed block meets the condition of the paper with the store's estimates in it.

It meets the paper's condition on `β W` when the estimate covers the true stake of `W`.

The estimate does not always cover it, since it is the average weight of a committee.

So that cover is a hypothesis of the last theorem, with the estimate rounded down to 100 Gwei.

With it, Lemmas 4 and 3 of the paper give the honest support of the block.

That support exceeds half of the store's estimate of `Φ`.

The range of slots of the adversary starts at the block, or at its epoch when its parent is older.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The store's adversary for a range of slots: its share of the estimate, less the equivocators.

The share is the estimate divided by 100, rounded down, times the threshold in percent.

The share is then at most the adversary plus the stake of the equivocators. -/
theorem computeAdversarialWeight_share {head : Root} {balanceSource : BeaconState preset fork}
    {startSlot endSlot : Slot} {total estimate equivocation adversary : Gwei}
    (totalOk : getTotalActiveBalance balanceSource = .ok total)
    (estimateOk : estimateCommitteeWeightBetweenSlots preset total startSlot endSlot = .ok estimate)
    (equivocationOk :
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation)
    (result : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary) :
    estimate.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤
      adversary.toNat + equivocation.toNat := by
  simp only [computeAdversarialWeight, bind_ok_iff, mapError_ok_iff] at result
  obtain ⟨t, tOk, e, eOk, share, shareOk, q, qOk, done⟩ := result
  rw [totalOk, Except.ok.injEq] at tOk
  subst tOk
  rw [estimateOk, Except.ok.injEq] at eOk
  subst eOk
  rw [equivocationOk, Except.ok.injEq] at qOk
  subst qOk
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
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

The terms are the estimated committee weight since the parent, the boost and twice the adversary.

The halving of the threshold rounds down, which loses at most one Gwei. -/
theorem computeSafetyThreshold_bound {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {total proposerScore maximumSupport discount adversary threshold : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (totalOk : getTotalActiveBalance balanceSource = .ok total)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (estimateOk :
      estimateCommitteeWeightBetweenSlots preset total firstSlot lastSlot = .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (result : store.computeSafetyThreshold config head root balanceSource = .ok threshold) :
    maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat ≤
      2 * threshold.toNat + discount.toNat + 1 := by
  simp only [computeSafetyThreshold, bind_ok_iff, mapError_ok_iff] at result
  obtain ⟨c, cOk, b, bOk, pb, pbOk, t, tOk, ps, psOk, f, fOk, l, lOk, m, mOk, d, dOk, a, aOk,
    wb, wbOk, db, dbOk, bd, bdOk, done⟩ := result
  rw [slotOk, Except.ok.injEq] at cOk
  subst cOk
  rw [blockOk, Except.ok.injEq] at bOk
  subst bOk
  rw [parentOk, Except.ok.injEq] at pbOk
  subst pbOk
  rw [totalOk, Except.ok.injEq] at tOk
  subst tOk
  rw [boostOk, Except.ok.injEq] at psOk
  subst psOk
  rw [firstOk, Except.ok.injEq] at fOk
  subst fOk
  rw [lastOk, Except.ok.injEq] at lOk
  subst lOk
  rw [estimateOk, Except.ok.injEq] at mOk
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

They are the current slot, the block and its parent, the total active balance and the boost.

They are also the first and last slots of the range since the parent, and its estimated weight.

They are also the discount and the adversary of the block. -/
theorem computeSafetyThreshold_eq_ok {head root : Root} {balanceSource : BeaconState preset fork}
    {threshold : Gwei}
    (result : store.computeSafetyThreshold config head root balanceSource = .ok threshold) :
    ∃ currentSlot block parentBlock total proposerScore firstSlot lastSlot maximumSupport
      discount adversary,
      store.getCurrentSlot config = .ok currentSlot ∧ store.block root = .ok block ∧
      store.block block.parentRoot = .ok parentBlock ∧
      getTotalActiveBalance balanceSource = .ok total ∧
      computeProposerScore config balanceSource = .ok proposerScore ∧
      addChecked parentBlock.slot 1 = .ok firstSlot ∧ subChecked currentSlot 1 = .ok lastSlot ∧
      estimateCommitteeWeightBetweenSlots preset total firstSlot lastSlot = .ok maximumSupport ∧
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount ∧
      store.getAdversarialWeight config head balanceSource root = .ok adversary := by
  have steps := result
  simp only [computeSafetyThreshold, bind_ok_iff, mapError_ok_iff] at steps
  obtain ⟨c, cOk, b, bOk, pb, pbOk, t, tOk, ps, psOk, f, fOk, l, lOk, m, mOk, d, dOk, a, aOk,
    -⟩ := steps
  exact ⟨c, b, pb, t, ps, f, l, m, d, a, cOk, bOk, pbOk, tOk, psOk, fOk, lOk, mOk, dOk, aOk⟩

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

/-- Lemmas 4 and 3 for a block that the store confirms: honest support above half of `Φ`.

Here `Φ` is the store's estimate: the committee weight since the parent, plus the boost.

The discount is taken off it, and is added to the other side so that nothing truncates.

The supporters are validators whose stake is the support of the block in the store.

The equivocators are validators whose stake is that of the known equivocators in the store.

Both lie in the committees `W` of a range of slots, and they are apart.

The store's adversary over that range must be its adversary for the block.

The range that the store uses for the block is one such range.

Assume that the Byzantine validators hold at most β of the stake of `W`, as in Assumption 2.

Here β is the threshold of the configuration, in percent, and no equivocator is honest.

Assume also that the store's estimate for that range covers the stake of `W`.

The estimate is rounded down to 100 Gwei there, as the store's share of the adversary rounds it.

The store does not check that cover, and it can fail within one epoch. -/
theorem lt_two_mul_honest_support_of_isOneConfirmed {ν : Type*} {w : ν → ℕ} {J : Set ν}
    [DecidablePred (· ∈ J)] {W supporters equivocators : Finset ν} {head root : Root}
    {balanceSource : BeaconState preset fork} {tally : VoteTally}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {total proposerScore maximumSupport discount adversary threshold support estimate
      equivocation : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (totalOk : getTotalActiveBalance balanceSource = .ok total)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk :
      estimateCommitteeWeightBetweenSlots preset total firstSlot lastSlot = .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (estimateOk :
      estimateCommitteeWeightBetweenSlots preset total startSlot lastSlot = .ok estimate)
    (equivocationOk :
      store.getEquivocationScore head balanceSource startSlot lastSlot = .ok equivocation)
    (thresholdOk : store.computeSafetyThreshold config head root balanceSource = .ok threshold)
    (supportOk : store.scoreFromTally tally ⟨root, .pending⟩ = .ok support)
    (confirmed : store.isOneConfirmed config head balanceSource tally root = .ok true)
    (supportStake : stake w supporters = support.toNat)
    (equivocationStake : stake w equivocators = equivocation.toNat)
    (supportersIn : supporters ⊆ W) (equivocatorsIn : equivocators ⊆ W)
    (apart : Disjoint supporters equivocators) (dishonest : ∀ v ∈ equivocators, v ∉ J)
    (byzantine : ByzantineStakeAtMost w W J config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (cover : stake w W ≤ estimate.toNat / 100 * 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake w {v ∈ supporters | v ∈ J} := by
  have bound := computeSafetyThreshold_bound slotOk blockOk parentOk totalOk boostOk firstOk lastOk
    maximumOk discountOk adversaryOk thresholdOk
  have above := threshold_lt_of_isOneConfirmed supportOk thresholdOk confirmed
  have share := computeAdversarialWeight_share totalOk estimateOk equivocationOk rangeOk
  -- The cover of the stake gives the cover of its Byzantine share.
  replace cover : config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake w W ≤
      100 * (estimate.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by
    calc config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake w W
        ≤ config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * (estimate.toNat / 100 * 100) :=
          Nat.mul_le_mul_left _ cover
      _ = 100 * (estimate.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by
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
  generalize estimate.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat = storeShare
    at cover share ⊢
  omega

end Store

end EthLib.Consensus
