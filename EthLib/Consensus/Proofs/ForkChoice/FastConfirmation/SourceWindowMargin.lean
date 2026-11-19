module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.DutyWindows
import EthLib.Consensus.Proofs.ForkChoice.CommitteeAgreement
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Source surplus for historical-anchor transport

A caller confirms a block with a guarded margin over its own window of committees.

This module shows that a later receiver then has its own surplus over the same source of balances.

Otherwise the receiver's justified block descends from the block, or two honest stores collide.

The runs since the anchor may also give direct-safety evidence instead.

That evidence is relative to the anchor, and with enough churn it holds with no accountable key.
-/

namespace EthLib.Consensus.Models.Network
open Models

private theorem window_reserve_core {β a n q j r Wa X : ℕ} (half : 2 * β ≤ 100)
    (resV : 100 * (a + n + q) + 50 * X ≤ β * (Wa + j + n + r + q))
    (resA : Wa = 0 ∨ 100 * a + 50 * X ≤ β * Wa) (aLe : a ≤ Wa) :
    100 * n + 200 * a + 100 * X ≤ 100 * (j + r) + 2 * β * Wa := by
  rcases resA with zero | resA
  · subst zero
    obtain rfl : a = 0 := by omega
    nlinarith
  · nlinarith

private theorem source_surplus_of_sets {ν : Type*} [DecidableEq ν] {J : Set ν}
    [DecidablePred (· ∈ J)] {w : ν → ℕ}
    {Wadv Wc Xm Sup I Hd P Q : Finset ν} {β maximum boost shift A D sM X : ℕ}
    (half : 2 * β ≤ 100)
    (margin : maximum + boost + 2 * A + shift < D + 2 * stake w Sup)
    (supIn : Sup ⊆ Wadv) (equivocatorsIn : I ⊆ Wadv) (apart : Disjoint Sup I)
    (equivocatorsDishonest : ∀ v ∈ I, v ∉ J)
    (cover : β * stake w Wadv ≤ 100 * (A + stake w I))
    (discount : D ≤ stake w Hd)
    (reserveAdv : stake w Wadv = 0 ∨
      100 * stake w {v ∈ Wadv | v ∉ J} + 50 * X ≤ β * stake w Wadv)
    (reserveV : 100 * stake w {v ∈ Wadv ∪ Xm | v ∉ J} + 50 * X ≤ β * stake w (Wadv ∪ Xm))
    (advIn : Wadv ⊆ Wc) (parentIn : Hd ⊆ Wc)
    (weight : sM + stake w Wc ≤ maximum + stake w (Wc ∪ Xm) + X)
    (supportersReach : {v ∈ Sup | v ∈ J} ⊆ P) (parentReach : Hd ⊆ P ∪ Q)
    (newReach : {v ∈ Xm \ Wadv | v ∈ J} ⊆ P) (callerApart : Disjoint {v ∈ Sup | v ∈ J} Hd) :
    sM + boost + shift < 2 * stake w P + stake w Q := by
  classical
  set Hs := {v ∈ Sup | v ∈ J}
  set Y := {v ∈ Xm \ Wadv | v ∈ J}
  -- The honest receiver gains: supporters twice, new honest window members, parent voters.
  have gains : 2 * stake w Hs + stake w Hd + 2 * stake w (Y \ Wc) + stake w (Y ∩ Wc) ≤
      2 * stake w P + stake w Q := by
    have hsY : Disjoint Hs Y := Finset.disjoint_left.mpr fun v hs hy =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
        (supIn (Finset.mem_filter.mp hs).1)
    have hsRest : Disjoint Hs ((Y \ Wc) ∪ ((Y ∩ Wc) ∪ (Hd ∩ P))) := by
      refine Finset.disjoint_union_right.mpr ⟨?_, Finset.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
      · exact Finset.disjoint_of_subset_right Finset.sdiff_subset hsY
      · exact Finset.disjoint_of_subset_right Finset.inter_subset_left hsY
      · exact Finset.disjoint_of_subset_right Finset.inter_subset_left callerApart
    have newRest : Disjoint (Y \ Wc) ((Y ∩ Wc) ∪ (Hd ∩ P)) := by
      refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
      · exact Finset.disjoint_left.mpr fun v one two =>
          (Finset.mem_sdiff.mp one).2 (Finset.mem_inter.mp two).2
      · exact Finset.disjoint_left.mpr fun v one two =>
          (Finset.mem_sdiff.mp one).2 (parentIn (Finset.mem_inter.mp two).1)
    have inP : Hs ∪ ((Y \ Wc) ∪ ((Y ∩ Wc) ∪ (Hd ∩ P))) ⊆ P := by
      intro v member
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at member
      rcases member with hs | (⟨y, _⟩ | (⟨y, _⟩ | ⟨_, p⟩))
      · exact supportersReach hs
      · exact newReach y
      · exact newReach y
      · exact p
    have inQ : Hd \ P ⊆ Q := fun v member => by
      obtain ⟨parent, notP⟩ := Finset.mem_sdiff.mp member
      rcases Finset.mem_union.mp (parentReach parent) with p | q
      · exact absurd p notP
      · exact q
    have pBound := stake_mono (w := w) inP
    have qBound := stake_mono (w := w) inQ
    have unionY := stake_mono (w := w) (Finset.subset_union_left (s₁ := Y ∩ Wc) (s₂ := Hd ∩ P))
    have unionD := stake_mono (w := w) (Finset.subset_union_right (s₁ := Y ∩ Wc) (s₂ := Hd ∩ P))
    have parentSplit : stake w (Hd ∩ P) + stake w (Hd \ P) = stake w Hd :=
      Finset.sum_inter_add_sum_sdiff Hd P w
    -- The three disjoint parts of the reached set weigh as much as their sum.
    unfold stake at pBound qBound unionY unionD parentSplit ⊢
    rw [Finset.sum_union hsRest, Finset.sum_union newRest] at pBound
    omega
  -- The caller's Byzantine supporters and equivocators fit in the adversary range.
  have byzantine := ForkChoice.byzantine_support_add_le (w := w) (J := J) supIn equivocatorsIn
    apart equivocatorsDishonest
  have supSplit : stake w {v ∈ Sup | v ∈ J} + stake w {v ∈ Sup | v ∉ J} = stake w Sup :=
    Finset.sum_filter_add_sum_filter_not Sup (· ∈ J) w
  -- The receiver window splits into the caller window and its new members.
  have windowSplit : stake w (Wc ∪ Xm) = stake w Wc + stake w (Xm \ Wc) := by
    rw [← Finset.union_sdiff_self_eq_union]
    exact Finset.sum_union Finset.disjoint_sdiff
  -- The reserve window splits into the adversary range, the new members and the repeats.
  have vEq : Wadv ∪ Xm = Wadv ∪ ((Xm \ Wc) ∪ ((Xm \ Wadv) ∩ Wc)) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro (h | h)
      · exact .inl h
      · by_cases a : v ∈ Wadv
        · exact .inl a
        · by_cases c : v ∈ Wc
          · exact .inr (.inr ⟨⟨h, a⟩, c⟩)
          · exact .inr (.inl ⟨h, c⟩)
    · rintro (h | (⟨h, _⟩ | ⟨⟨h, _⟩, _⟩))
      · exact .inl h
      · exact .inr h
      · exact .inr h
  have vApart : Disjoint Wadv ((Xm \ Wc) ∪ ((Xm \ Wadv) ∩ Wc)) := by
    refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
    · exact Finset.disjoint_left.mpr fun v a x => (Finset.mem_sdiff.mp x).2 (advIn a)
    · exact Finset.disjoint_left.mpr fun v a x =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp x).1).2 a
  have xApart : Disjoint (Xm \ Wc) ((Xm \ Wadv) ∩ Wc) :=
    Finset.disjoint_left.mpr fun v x y => (Finset.mem_sdiff.mp x).2 (Finset.mem_inter.mp y).2
  have vStake : stake w (Wadv ∪ Xm) =
      stake w Wadv + stake w (Xm \ Wc) + stake w ((Xm \ Wadv) ∩ Wc) := by
    unfold stake
    rw [vEq, Finset.sum_union vApart, Finset.sum_union xApart, Nat.add_assoc]
  have vFilter : {v ∈ Wadv ∪ Xm | v ∉ J} =
      {v ∈ Wadv | v ∉ J} ∪ ({v ∈ Xm \ Wc | v ∉ J} ∪ {v ∈ (Xm \ Wadv) ∩ Wc | v ∉ J}) := by
    rw [vEq, Finset.filter_union, Finset.filter_union]
  have vDishonest : stake w {v ∈ Wadv ∪ Xm | v ∉ J} = stake w {v ∈ Wadv | v ∉ J} +
      stake w {v ∈ Xm \ Wc | v ∉ J} + stake w {v ∈ (Xm \ Wadv) ∩ Wc | v ∉ J} := by
    unfold stake
    rw [vFilter, Finset.sum_union, Finset.sum_union, Nat.add_assoc]
    · exact Finset.disjoint_filter_filter xApart
    · rw [← Finset.filter_union]; exact Finset.disjoint_filter_filter vApart
  -- The honest new and repeated members are exactly the parts of `Y`.
  have newHonest : {v ∈ Xm \ Wc | v ∈ J} = Y \ Wc := by
    ext v
    simp only [Y, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨x, c⟩, h⟩
      exact ⟨⟨⟨x, fun a => c (advIn a)⟩, h⟩, c⟩
    · rintro ⟨⟨⟨x, _⟩, h⟩, c⟩
      exact ⟨⟨x, c⟩, h⟩
  have repeatHonest : {v ∈ (Xm \ Wadv) ∩ Wc | v ∈ J} = Y ∩ Wc := by
    ext v
    simp only [Y, Finset.mem_filter, Finset.mem_inter]
    tauto
  have newSplit : stake w {v ∈ Xm \ Wc | v ∈ J} + stake w {v ∈ Xm \ Wc | v ∉ J} =
      stake w (Xm \ Wc) := Finset.sum_filter_add_sum_filter_not (Xm \ Wc) (· ∈ J) w
  have repeatSplit : stake w {v ∈ (Xm \ Wadv) ∩ Wc | v ∈ J} +
      stake w {v ∈ (Xm \ Wadv) ∩ Wc | v ∉ J} = stake w ((Xm \ Wadv) ∩ Wc) :=
    Finset.sum_filter_add_sum_filter_not ((Xm \ Wadv) ∩ Wc) (· ∈ J) w
  rw [newHonest] at newSplit
  rw [repeatHonest] at repeatSplit
  have aLe : stake w {v ∈ Wadv | v ∉ J} ≤ stake w Wadv := stake_mono (Finset.filter_subset _ _)
  have core := window_reserve_core (β := β) (a := stake w {v ∈ Wadv | v ∉ J})
    (n := stake w {v ∈ Xm \ Wc | v ∉ J}) (q := stake w {v ∈ (Xm \ Wadv) ∩ Wc | v ∉ J})
    (j := stake w (Y \ Wc)) (r := stake w (Y ∩ Wc)) (Wa := stake w Wadv) (X := X) half
    (by
      rw [vDishonest, vStake, ← newSplit, ← repeatSplit] at reserveV
      convert reserveV using 2; ring) reserveAdv aLe
  rw [windowSplit] at weight
  have parentSmall := stake_mono (w := w) parentIn
  have advSmall := stake_mono (w := w) advIn
  have honestSmall := stake_mono (w := w) (Finset.filter_subset (· ∈ J) Sup)
  have supSmall := stake_mono (w := w) supIn
  nlinarith

/-- A caller margin needs an honest supporter or a parent voter.

Without them the discount is zero and the supporters are Byzantine, so the adversary covers them.
-/
private theorem honest_vote_of_margin {ν : Type*} [DecidableEq ν] {J : Set ν}
    [DecidablePred (· ∈ J)] {w : ν → ℕ} {Wadv Sup I Hd : Finset ν}
    {β maximum boost shift A D : ℕ}
    (margin : maximum + boost + 2 * A + shift < D + 2 * stake w Sup)
    (supIn : Sup ⊆ Wadv) (equivocatorsIn : I ⊆ Wadv) (apart : Disjoint Sup I)
    (equivocatorsDishonest : ∀ v ∈ I, v ∉ J)
    (cover : β * stake w Wadv ≤ 100 * (A + stake w I))
    (discount : D ≤ stake w Hd)
    (reserveAdv : stake w Wadv = 0 ∨ 100 * stake w {v ∈ Wadv | v ∉ J} ≤ β * stake w Wadv) :
    (∃ v ∈ Sup, v ∈ J) ∨ Hd.Nonempty := by
  by_contra none
  obtain ⟨noSupporter, noVoter⟩ := not_or.mp none
  have empty : Hd = ∅ := Finset.not_nonempty_iff_eq_empty.mp noVoter
  have noHonest : {v ∈ Sup | v ∈ J} = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun v member honest => noSupporter ⟨v, member, honest⟩
  have supSplit : stake w {v ∈ Sup | v ∈ J} + stake w {v ∈ Sup | v ∉ J} = stake w Sup :=
    Finset.sum_filter_add_sum_filter_not Sup (· ∈ J) w
  rw [noHonest] at supSplit
  have zeroHonest : stake w (∅ : Finset ν) = 0 := Finset.sum_empty
  have zeroVoters : stake w Hd = 0 := by rw [empty]; exact Finset.sum_empty
  have byzantine := ForkChoice.byzantine_support_add_le (w := w) (J := J) supIn equivocatorsIn
    apart equivocatorsDishonest
  have supSmall := stake_mono (w := w) supIn
  rcases reserveAdv with zero | reserveAdv
  · omega
  · omega

end EthLib.Consensus.Models.Network

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- Two heads that descend from one parent state agree on the committees near that parent.

The heads may be held by two stores that hold the same parent state. -/
private theorem committeesKept_of_parentState {caller receiver : Store preset fork}
    (callerReached : Store.Reachable config anchorState anchorBlock caller)
    (receiverReached : Store.Reachable config anchorState anchorBlock receiver)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) (before : fork < .glamsterdam)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {parentRoot callerHead receiverHead : Root} {parent : BeaconBlock preset fork}
    {parentState callerState receiverState : BeaconState preset fork}
    (callerParent : caller.blocks[parentRoot]? = some parent)
    (receiverParent : receiver.blocks[parentRoot]? = some parent)
    (callerParentState : caller.blockStates[parentRoot]? = some parentState)
    (receiverParentState : receiver.blockStates[parentRoot]? = some parentState)
    (callerDescends : caller.isAncestor ⟨callerHead, .pending⟩ ⟨parentRoot, .pending⟩ = .ok true)
    (receiverDescends :
      receiver.isAncestor ⟨receiverHead, .pending⟩ ⟨parentRoot, .pending⟩ = .ok true)
    (callerFound : caller.blockStates[callerHead]? = some callerState)
    (receiverFound : receiver.blockStates[receiverHead]? = some receiverState)
    {epoch : Epoch}
    (near : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 1)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (callerRing : (getCurrentEpoch callerState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (receiverRing : (getCurrentEpoch receiverState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    CommitteesKept epoch callerState receiverState ∧
      getCommitteeCountPerSlot receiverState epoch =
        getCommitteeCountPerSlot callerState epoch := by
  -- Both head states run on from the parent state.
  have callerWalk := Store.getAncestor_of_isAncestor_of_lt before callerParent callerDescends
  have receiverWalk := Store.getAncestor_of_isAncestor_of_lt before receiverParent
    receiverDescends
  have toCaller := callerReached.runKept_of_getAncestor anchorSlot callerWalk callerFound
    callerParentState
  have toReceiver := receiverReached.runKept_of_getAncestor anchorSlot receiverWalk receiverFound
    receiverParentState
  -- The parent state is at or after the parent's slot, so the epoch is within its lookahead.
  have parentLe := callerReached.slot_le_of_blockState anchorSlot callerParent callerParentState
  have parentEpoch : (computeEpochAtSlot preset parent.slot).toNat ≤
      (getCurrentEpoch parentState).toNat := by
    exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp parentLe)
  have fixed : epoch ≤ activityFixedEpoch parentState := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := epoch.toNat_lt
    omega
  exact toCaller.committees_agree toReceiver (by omega) fixed callerRing receiverRing

/-- A partial range weighs its active members, raised to one increment. -/
private theorem weight_le_activeMembers {store : Store preset fork} {head : Root}
    {source : BeaconState preset fork} {first last : Slot} {weight : Gwei}
    {participants : Std.TreeSet ValidatorIndex}
    (participantsOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (weightOk : store.computeCommitteeWeightBetweenSlots head source first last = .ok weight)
    (notCovered : isFullValidatorSetCovered preset first last = .ok false) :
    weight.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source participants)) := by
  by_cases empty : last < first
  · rw [Store.computeCommitteeWeightBetweenSlots_of_gt empty, Except.ok.injEq] at weightOk
    subst weightOk
    exact Nat.zero_le _
  have notGt : ¬first > last := empty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at weightOk
  obtain ⟨⟨_, members⟩, weightOk, rfl⟩ := weightOk
  simp only [Store.computeCommitteeWeightAndMembers, notGt, ↓reduceIte, bind_ok_iff] at weightOk
  obtain ⟨covered, coveredOk, weightOk⟩ := weightOk
  rw [notCovered, Except.ok.injEq] at coveredOk
  subst coveredOk
  simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff] at weightOk
  obtain ⟨found, foundOk, active, activeOk, total, totalOk, final⟩ := weightOk
  rw [participantsOk, Except.ok.injEq] at foundOk
  subst foundOk
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
  obtain ⟨rfl, -⟩ := final
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp totalOk
  rw [totalEq]
  refine max_le_max le_rfl (stake_mono fun v member => ?_)
  -- Each index that passes the filter is an active member of the committees.
  have inList := List.mem_toFinset.mp member
  have passed := passes_of_mem_filterM_ok activeOk inList
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passed
  obtain ⟨validator, validatorOk, isActive⟩ := passed
  exact Store.mem_activeMembers.mpr ⟨Std.TreeSet.mem_toList.mp
    ((sublist_of_filterM_ok activeOk).subset inList), validator,
    validatorAt_ok_iff.mp validatorOk, isActive⟩

/-- A covering range weighs the active validators of the source, raised to one increment. -/
private theorem weight_le_activeVoters {store : Store preset fork} {head : Root}
    {source : BeaconState preset fork} {first last : Slot} {weight : Gwei}
    (covered : isFullValidatorSetCovered preset first last = .ok true)
    (weightOk : store.computeCommitteeWeightBetweenSlots head source first last = .ok weight) :
    weight.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (stake (fun v => balanceAt source v.toNat) (Models.Network.activeVoters source)) := by
  rw [Store.computeCommitteeWeightBetweenSlots_of_covered covered, mapError_ok_iff] at weightOk
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok weightOk)
  rw [totalEq]
  rfl

/-- Each supporter of a block is a member of the committees of a range that the head reads.

The range starts at or before the slot of the block and ends at the slot before the current one.

The current epoch is at most one after the epoch of the parent of the block.

So every vote is near the parent, and the head state agrees with its target state. -/
private theorem supportersOf_mem_range_of_near_parent {checks : SignatureChecks}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (before : fork < .glamsterdam)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {head root : Root} {block parent : BeaconBlock preset fork}
    {balanceSource : BeaconState preset fork}
    {currentSlot startSlot lastSlot : Slot} {participants : Std.TreeSet ValidatorIndex}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot)
    (startLe : startSlot ≤ block.slot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (near : (computeEpochAtSlot preset currentSlot).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1)
    (participantsOk : store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants) :
    ∀ v ∈ store.supportersOf balanceSource ⟨root, .pending⟩, v ∈ participants := by
  intro v supporter
  have found : store.blocks[root]? = some block := Store.block_ok_iff.mp blockOk
  -- The vote of the supporter comes from an attestation of a slot of the range.
  obtain ⟨attestation, latest, origin, low, high⟩ :=
    reached.forwardReachable.votesHaveOrigins.slot_mem_range_of_mem_supportersOf blockOk startLe
      slotOk lastOk supporter
  -- It votes for a node that descends from the block, so from its parent.
  obtain ⟨message, voted, latest', -, supported, voteDescends⟩ :=
    store.exists_of_voteCountsFor (store.voteCountsFor_of_mem_supportersOf supporter)
  rw [latest, Option.some.injEq] at latest'
  subst latest'
  have votedRoot : voted.root = attestation.data.beaconBlockRoot :=
    Store.getSupportedNode_root supported
  have rootParent := Store.isAncestor_pending_parent_of_slot_lt (node := ⟨root, .pending⟩)
    found parentFound lower
  have headParent := Store.isAncestor_trans_of_lt before found parentFound descends rootParent
  obtain ⟨votedBlock, votedFound, votedAbove⟩ := Store.slot_le_of_isAncestor found voteDescends
  have voteParent := Store.isAncestor_trans_of_lt before found parentFound voteDescends rootParent
  -- The head has a state, at or before the current slot.
  obtain ⟨headBlock, headBlockFound, -⟩ := Store.slot_le_of_isAncestor found descends
  obtain ⟨headState, headFound, -, -⟩ := reached.reachable.blockStatesFromParents headBlockFound
  have headLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot headFound
    slotOk
  -- The vote and the head state are both near the parent.
  obtain ⟨lastLe, lastValue⟩ := subChecked_ok_iff.mp lastOk
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [one] at lastLe lastValue
  have lowNat := UInt64.le_iff_toNat_le.mp low
  have highNat := UInt64.le_iff_toNat_le.mp high
  have headNat := UInt64.le_iff_toNat_le.mp headLe
  have startNat := UInt64.le_iff_toNat_le.mp startLe
  have lowerNat := UInt64.lt_iff_toNat_lt.mp lower
  have pred := Nat.sub_le currentSlot.toNat 1
  have voteCurrent := epoch_le_of_slot_le (preset := preset) attestation.data.slot currentSlot
    (by omega)
  -- The vote is for a block at or after the block, so after the parent.
  obtain ⟨tip, tipFound, tipLe⟩ := origin.voted
  rw [← votedRoot, votedFound, Option.some.injEq] at tipFound
  subst tipFound
  have tipNat := UInt64.le_iff_toNat_le.mp tipLe
  have parentVote := epoch_le_of_slot_le (preset := preset) parent.slot attestation.data.slot (by
    have := UInt64.le_iff_toNat_le.mp votedAbove
    omega)
  have headCurrent : (getCurrentEpoch headState).toNat ≤
      (computeEpochAtSlot preset currentSlot).toNat := by
    exact epoch_le_of_slot_le _ _ headNat
  -- The target state and the head state agree on the committees of the vote.
  obtain ⟨targetState, index, committee, targetFound, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  obtain ⟨kept, count⟩ := reached.committeesKept_of_voteOrigin anchorSlot minLookahead
    maxLookahead (by omega) parentFound headParent origin votedRoot voteParent (by omega)
    targetFound headFound (by omega)
  exact Store.mem_getCommitteesBetweenSlots participantsOk low high
    (Store.blockState_ok_iff.mpr headFound) (count ▸ below)
    ((kept _ _ rfl).trans committeeOk) member

/-- A caller margin needs a nonempty window: `first ≤ last`. -/
private theorem first_le_last_of_margin {checks : SignatureChecks}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (absent : store.blocks[anchorBlock.parentRoot]? = none)
    {head root : Root} {block parent : BeaconBlock preset fork}
    {source : BeaconState preset fork} {slot first last : Slot}
    {boost maximum support discount adversary : Gwei} {shift : ℕ}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parent)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked slot 1 = .ok last)
    (supportOk : store.scoreFromTally (store.tallyVotes source) ⟨root, .pending⟩ = .ok support)
    (discountOk : store.computeEmptySlotSupportDiscount config head source root = .ok discount)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat) :
    first ≤ last := by
  classical
  by_contra notLe
  have empty : last < first := by
    rw [UInt64.lt_iff_toNat_lt]
    rw [UInt64.le_iff_toNat_le] at notLe
    omega
  have lower := reached.reachable.parentsBelow anchorSlot absent root block parent
    (Store.block_ok_iff.mp blockOk) (Store.block_ok_iff.mp parentOk)
  have next := (addChecked_ok_iff.mp firstOk).2
  have previous := (subChecked_ok_iff.mp lastOk).2
  simp only [UInt64.toNat_one] at next previous
  have firstLe : first ≤ block.slot := by
    have := UInt64.lt_iff_toNat_lt.mp lower
    rw [UInt64.le_iff_toNat_le]
    omega
  have noSupport : ∀ v ∈ store.supportersOf source ⟨root, .pending⟩, False := by
    intro v member
    obtain ⟨attestation, _, _, starts, ends⟩ :=
      reached.forwardReachable.votesHaveOrigins.slot_mem_range_of_mem_supportersOf
        blockOk firstLe slotOk lastOk member
    have chain := UInt64.le_trans starts ends
    rw [UInt64.le_iff_toNat_le] at chain
    rw [UInt64.lt_iff_toNat_lt] at empty
    omega
  have zeroSupport : support.toNat = 0 := by
    rw [store.getAttestationScore_toNat_eq_sum supportOk]
    apply List.sum_eq_zero
    intro weight member
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp member
    have noVote : store.voteCountsFor ⟨root, .pending⟩ entry.1 = false := by
      apply Bool.eq_false_iff.mpr
      intro counts
      apply noSupport entry.1
      simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter]
      exact ⟨entry, ⟨inside, counts⟩, rfl⟩
    simp [noVote]
  obtain ⟨current, currentOk, blocks, _⟩ := reached.forwardReachable.slots_le_current
    (Store.slotDuration_pos slotOk) anchorSlot
  rw [slotOk, Except.ok.injEq] at currentOk
  subst current
  have blockLe := blocks root block (Store.block_ok_iff.mp blockOk)
  have same : first = block.slot := by
    have := UInt64.lt_iff_toNat_lt.mp empty
    have := UInt64.le_iff_toNat_le.mp blockLe
    have := UInt64.le_iff_toNat_le.mp firstLe
    apply UInt64.toNat_inj.mp
    omega
  have zeroDiscount : discount = 0 := by
    have computed : store.computeEmptySlotSupportDiscount config head source root = .ok 0 := by
      simp only [Store.computeEmptySlotSupportDiscount, blockOk, parentOk, firstOk,
        Except.mapError, bind, Except.bind, same, ↓reduceIte, pure, Except.pure]
    exact Except.ok.inj (discountOk.symm.trans computed)
  rw [zeroDiscount, zeroSupport] at margin
  simp at margin

/-- The range of the adversary of a block starts after its parent and at or before the block.

The start is in the epoch of the block or a later one.

The block is above its parent, and the range ends at the slot before the current one. -/
public theorem Store.adversaryRange_start {store : Store preset fork} {head root : Root}
    {source : BeaconState preset fork} {slot first last : Slot}
    {block parent : BeaconBlock preset fork} {adversary : Gwei}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parent)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked slot 1 = .ok last)
    (lower : parent.slot < block.slot)
    (adversaryOk : store.getAdversarialWeight config head source root = .ok adversary) :
    ∃ startSlot, first ≤ startSlot ∧ startSlot ≤ block.slot ∧
      (computeEpochAtSlot preset block.slot).toNat ≤
        (computeEpochAtSlot preset startSlot).toNat ∧
      store.computeAdversarialWeight config head source startSlot last = .ok adversary := by
  have next := (addChecked_ok_iff.mp firstOk).2
  simp only [UInt64.toNat_one] at next
  have parentEpoch : store.getBlockEpoch block.parentRoot =
      .ok (computeEpochAtSlot preset parent.slot) := by
    simp [Store.getBlockEpoch, parentOk, bind, Except.bind, pure, Except.pure]
  have blockEpoch : store.getBlockEpoch root = .ok (computeEpochAtSlot preset block.slot) := by
    simp [Store.getBlockEpoch, blockOk, bind, Except.bind, pure, Except.pure]
  by_cases later : computeEpochAtSlot preset parent.slot < computeEpochAtSlot preset block.slot
  · let start := block.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH
    have startOk := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) block.slot
    have startValue := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
    change start.toNat = _ at startValue
    have laterNat := UInt64.lt_iff_toNat_lt.mp later
    simp only [computeEpochAtSlot, UInt64.toNat_div] at laterNat startValue
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
      by_contra zero
      have : preset.SLOTS_PER_EPOCH.toNat = 0 := by omega
      simp [this] at laterNat
    have parentBelow : parent.slot.toNat < start.toNat := by
      rw [startValue]
      exact (Nat.div_lt_iff_lt_mul positive).mp laterNat
    have startBelow : start.toNat ≤ block.slot.toNat := by
      rw [startValue]
      exact Nat.div_mul_le_self _ _
    refine ⟨start, ?_, UInt64.le_iff_toNat_le.mpr startBelow, ?_, ?_⟩
    · rw [UInt64.le_iff_toNat_le]
      omega
    · simp only [computeEpochAtSlot, UInt64.toNat_div]
      rw [startValue, Nat.mul_div_cancel _ positive]
    · rw [← Store.getAdversarialWeight_of_lt slotOk blockOk blockEpoch parentEpoch later startOk
        lastOk]
      exact adversaryOk
  · refine ⟨block.slot, ?_, UInt64.le_refl _, le_rfl, ?_⟩
    · have := UInt64.lt_iff_toNat_lt.mp lower
      rw [UInt64.le_iff_toNat_le]
      omega
    · rw [← Store.getAdversarialWeight_of_not_lt slotOk blockOk blockEpoch parentEpoch later
        lastOk]
      exact adversaryOk

/-- The caller's reads in terms of sets of validators. -/
private theorem caller_margin_sets {checks : SignatureChecks}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (absent : store.blocks[anchorBlock.parentRoot]? = none)
    (before : fork < .glamsterdam)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {head root : Root} {block parent : BeaconBlock preset fork}
    {source : BeaconState preset fork} {slot first last : Slot}
    {support adversary : Gwei}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parent)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked slot 1 = .ok last)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (near : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1)
    (registry : source.RegistryWithinLimit) (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : store.scoreFromTally (store.tallyVotes source) ⟨root, .pending⟩ = .ok support)
    (adversaryOk : store.getAdversarialWeight config head source root = .ok adversary) :
    ∃ startSlot advParticipants, ∃ I : Finset ValidatorIndex,
      first ≤ startSlot ∧ (startSlot ≤ last ∨ Store.activeMembers source advParticipants = ∅) ∧
      store.getCommitteesBetweenSlots head startSlot last = .ok advParticipants ∧
      support.toNat = stake (fun v => balanceAt source v.toNat)
        (store.supportersOf source ⟨root, .pending⟩) ∧
      store.supportersOf source ⟨root, .pending⟩ ⊆ Store.activeMembers source advParticipants ∧
      I ⊆ Store.activeMembers source advParticipants ∧
      (∀ v ∈ I, v ∈ store.equivocatingIndices) ∧
      Disjoint (store.supportersOf source ⟨root, .pending⟩) I ∧
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
          stake (fun v => balanceAt source v.toNat) (Store.activeMembers source advParticipants) ≤
        100 * (adversary.toNat + stake (fun v => balanceAt source v.toNat) I) := by
  classical
  have lower := reached.reachable.parentsBelow anchorSlot absent root block parent
    (Store.block_ok_iff.mp blockOk) (Store.block_ok_iff.mp parentOk)
  obtain ⟨start, firstLe, startLe, -, rangeOk⟩ :=
    Store.adversaryRange_start slotOk blockOk parentOk firstOk lastOk lower adversaryOk
  obtain ⟨weight, equivocation, weightOk, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨participants, participantsOk, equivocators⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have inRange := supportersOf_mem_range_of_near_parent anchorSlot reached before
    minLookahead maxLookahead ring slotOk blockOk (Store.block_ok_iff.mp parentOk) lower startLe
    lastOk descends near participantsOk (balanceSource := source)
  have whole : ∀ v ∈ Store.activeMembers source participants,
      balanceAt source v.toNat % 100 = 0 := fun v _ =>
    Nat.mod_eq_zero_of_dvd
      (dvd_balanceAt_of_aligned aligned (Nat.dvd_of_mod_eq_zero increment) _)
  have cover := Store.threshold_mul_stake_le_of_computeAdversarialWeight weightOk equivocationOk
    rangeOk (Store.stake_le_computeCommitteeWeightBetweenSlots participantsOk weightOk
      fun v member => Store.mem_activeMembers.mp member) whole
  rw [← equivocators] at cover
  refine ⟨start, participants, store.equivocatorsOf source participants, firstLe, ?_,
    participantsOk, (Store.stake_supportersOf registry supportOk).symm, ?_,
    Store.equivocatorsOf_subset_activeMembers, ?_, Store.disjoint_supportersOf_equivocatorsOf,
    cover⟩
  · by_cases ordered : start ≤ last
    · exact .inl ordered
    · right
      have empty : last < start := by
        rw [UInt64.lt_iff_toNat_lt]
        rw [UInt64.le_iff_toNat_le] at ordered
        omega
      rw [Store.getCommitteesBetweenSlots_of_gt empty, Except.ok.injEq] at participantsOk
      subst participants
      simp [Store.activeMembers]
  · intro v supporter
    rw [Store.activeMembers, Finset.mem_filter, List.mem_toFinset, Std.TreeSet.mem_toList]
    exact ⟨inRange v supporter, Store.isActiveAt_of_mem_supportersOf registry supporter⟩
  · intro v member
    exact (Finset.mem_filter.mp member).2

/-- A successful window reads every window inside it. -/
private theorem window_ok_of_inside {store : Store preset fork} {head : Root}
    {first last low high : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (lowLe : first ≤ low) (highLe : high ≤ last) :
    ∃ inner, store.getCommitteesBetweenSlots head low high = .ok inner ∧
      ∀ v ∈ inner, v ∈ members := by
  -- The end of the outer window has a successor, so the inner end has one too.
  have outer := read
  unfold Store.getCommitteesBetweenSlots at outer
  obtain ⟨after, afterOk, -⟩ := bind_ok_iff.mp outer
  have afterNat := (addChecked_ok_iff.mp (mapError_ok_iff.mp afterOk)).1
  have highNat := UInt64.le_iff_toNat_le.mp highLe
  obtain ⟨inner, innerOk⟩ := Store.getCommitteesBetweenSlots_ok_of_slots (after := high + 1)
    (addChecked_of_lt (by simp only [UInt64.toNat_one] at afterNat ⊢; omega))
    fun slot low' high' => Store.getSlotCommittee_ok_of_getCommitteesBetweenSlots read
      (UInt64.le_trans lowLe low') (UInt64.le_trans high' highLe)
  refine ⟨inner, innerOk, fun v member => ?_⟩
  obtain ⟨slot, low', high', committee, committeeOk, inside⟩ :=
    (Store.mem_getCommitteesBetweenSlots_iff innerOk v).mp member
  exact (Store.mem_getCommitteesBetweenSlots_iff read v).mpr ⟨slot, UInt64.le_trans lowLe low',
    UInt64.le_trans high' highLe, committee, committeeOk, inside⟩

/-- The members of a window are those of its two halves, split after a middle slot. -/
private theorem mem_window_split {store : Store preset fork} {head : Root}
    {first middle next last : Slot} {members left right : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (leftOk : store.getCommitteesBetweenSlots head first middle = .ok left)
    (rightOk : store.getCommitteesBetweenSlots head next last = .ok right)
    (nextOk : addChecked middle 1 = .ok next) (middleLe : middle ≤ last) (firstLe : first ≤ next)
    (v : ValidatorIndex) :
    v ∈ members ↔ v ∈ left ∨ v ∈ right := by
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  rw [Store.mem_getCommitteesBetweenSlots_iff read, Store.mem_getCommitteesBetweenSlots_iff leftOk,
    Store.mem_getCommitteesBetweenSlots_iff rightOk]
  constructor
  · rintro ⟨slot, low, high, rest⟩
    by_cases before : slot ≤ middle
    · exact .inl ⟨slot, low, before, rest⟩
    · refine .inr ⟨slot, ?_, high, rest⟩
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp before)
      exact UInt64.le_iff_toNat_le.mpr (by omega)
  · rintro (⟨slot, low, high, rest⟩ | ⟨slot, low, high, rest⟩)
    · exact ⟨slot, low, UInt64.le_trans high middleLe, rest⟩
    · exact ⟨slot, UInt64.le_trans firstLe low, high, rest⟩

private theorem window_weight_le {store : Store preset fork} {head : Root}
    {source : BeaconState preset fork} {parentSlot first last : Slot} {weight : Gwei}
    {window : Std.TreeSet ValidatorIndex} {exitAllowance : ℕ}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (firstOk : addChecked parentSlot 1 = .ok first)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok window)
    (weightOk : store.computeCommitteeWeightBetweenSlots head source first last = .ok weight)
    (exit : Models.Network.WindowExitBoundWith store source head first last exitAllowance) :
    ∃ finish members, finish ≤ last ∧
      (computeEpochAtSlot preset finish).toNat ≤ (computeEpochAtSlot preset parentSlot).toNat + 1 ∧
      store.getCommitteesBetweenSlots head first finish = .ok members ∧
      (weight.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members)) ∨
        isFullValidatorSetCovered preset first finish = .ok true ∧
        weight.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members)) +
        exitAllowance) := by
  have firstNat := (addChecked_ok_iff.mp firstOk).2
  simp only [UInt64.toNat_one] at firstNat
  have epochBound (x : Slot) (le : x.toNat ≤ parentSlot.toNat + preset.SLOTS_PER_EPOCH.toNat) :
      (computeEpochAtSlot preset x).toNat ≤ (computeEpochAtSlot preset parentSlot).toNat + 1 := by
    simpa only [computeEpochAtSlot, UInt64.toNat_div, Nat.add_div_right _ positive] using
      Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) le
  by_cases empty : last < first
  · have zero := weightOk
    rw [Store.computeCommitteeWeightBetweenSlots_of_gt empty, Except.ok.injEq] at zero
    refine ⟨last, window, UInt64.le_refl _, epochBound _ ?_, windowOk, ?_⟩
    · have := UInt64.lt_iff_toNat_lt.mp empty
      omega
    · exact .inl (by simp only [← zero, UInt64.toNat_zero]; omega)
  have notGt : ¬ first > last := empty
  have coverage := weightOk
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff] at coverage
  obtain ⟨result, coverage, -⟩ := coverage
  simp only [Store.computeCommitteeWeightAndMembers, notGt, ↓reduceIte, bind_ok_iff] at coverage
  obtain ⟨covered, coveredOk, -⟩ := coverage
  have arithmetic := coveredOk
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at arithmetic
  obtain ⟨afterFirst, afterFirstOk, lastFirst, lastFirstOk, afterLast, afterLastOk, test⟩ :=
    arithmetic
  have afterFirstNat := (addChecked_ok_iff.mp afterFirstOk).2
  have lastFirstNat := (subChecked_ok_iff.mp lastFirstOk).2
  have afterLastNat := (addChecked_ok_iff.mp afterLastOk).2
  simp only [UInt64.toNat_one] at lastFirstNat afterLastNat
  have lastFirstEq : lastFirst.toNat = parentSlot.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    omega
  have lastFirstEpoch : (computeEpochAtSlot preset lastFirst).toNat =
      parentSlot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
    simp only [computeEpochAtSlot, UInt64.toNat_div, lastFirstEq, Nat.add_div_right _ positive]
  cases covered
  · have epochs : afterLast.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
        lastFirst.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      have notLt : ¬ computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterLast :=
        of_decide_eq_false (Except.ok.inj test)
      exact UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp notLt)
    have lastEpoch := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (show last.toNat ≤ afterLast.toNat by omega)
    refine ⟨last, window, UInt64.le_refl _, ?_, windowOk, ?_⟩
    · simpa only [computeEpochAtSlot, UInt64.toNat_div] using
        (lastEpoch.trans epochs).trans_eq lastFirstEpoch
    · exact .inl (weight_le_activeMembers windowOk weightOk coveredOk)
  · have epochs : lastFirst.toNat / preset.SLOTS_PER_EPOCH.toNat <
        afterLast.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simpa only [pure, Except.pure, Except.ok.injEq, decide_eq_true_eq,
        computeEpochAtSlot, UInt64.lt_iff_toNat_lt, UInt64.toNat_div] using test
    let epoch := computeEpochAtSlot preset lastFirst
    let epochStart := lastFirst / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH
    have startOk : computeStartSlotAtEpoch preset epoch = .ok epochStart :=
      computeStartSlotAtEpoch_computeEpochAtSlot lastFirst
    have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
    change epochStart.toNat = (computeEpochAtSlot preset lastFirst).toNat *
      preset.SLOTS_PER_EPOCH.toNat at startNat
    have startLow : first.toNat ≤ epochStart.toNat := by
      have floor := Nat.lt_div_mul_add (a := parentSlot.toNat) positive
      rw [startNat, lastFirstEpoch, Nat.add_mul]
      omega
    have nextLe : epochStart.toNat + preset.SLOTS_PER_EPOCH.toNat ≤ afterLast.toNat := by
      have mult := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
        (Nat.succ_le_of_lt epochs)
      have floor := Nat.div_mul_le_self afterLast.toNat preset.SLOTS_PER_EPOCH.toNat
      rw [startNat]
      simp only [computeEpochAtSlot, UInt64.toNat_div] at *
      rw [Nat.succ_mul] at mult
      omega
    have nextFits : epochStart.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 :=
      lt_of_le_of_lt nextLe afterLast.toNat_lt
    let next := epochStart + preset.SLOTS_PER_EPOCH
    have nextOk : addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next :=
      addChecked_of_lt nextFits
    have nextNat := (addChecked_ok_iff.mp nextOk).2
    let finish := next - 1
    have finishOk : subChecked next 1 = .ok finish :=
      subChecked_ok_iff.mpr ⟨by simp only [UInt64.toNat_one]; omega,
        UInt64.toNat_sub_of_le _ _
          (UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.toNat_one]; omega))⟩
    have finishNat := (subChecked_ok_iff.mp finishOk).2
    simp only [UInt64.toNat_one] at finishNat
    have finishLe : finish ≤ last := UInt64.le_iff_toNat_le.mpr (by omega)
    have finishAfter : addChecked finish 1 = .ok next :=
      addChecked_ok_iff.mpr ⟨by simp only [UInt64.toNat_one]; have := next.toNat_lt; omega,
        by simp only [UInt64.toNat_one]; omega⟩
    have prefixCovered : isFullValidatorSetCovered preset first finish = .ok true := by
      have later : computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset next := by
        apply UInt64.lt_iff_toNat_lt.mpr
        simp only [computeEpochAtSlot, UInt64.toNat_div, nextNat, startNat,
          Nat.add_div_right _ positive, Nat.mul_div_cancel _ positive]
        omega
      simp only [isFullValidatorSetCovered, afterFirstOk, lastFirstOk, finishAfter,
        Except.mapError, bind, Except.bind, later, decide_true, pure, Except.pure]
    have finishEpoch : (computeEpochAtSlot preset finish).toNat ≤
        (computeEpochAtSlot preset parentSlot).toNat + 1 := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul positive).mpr
      have sn : epochStart.toNat =
          (parentSlot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat :=
        startNat.trans (congrArg (· * preset.SLOTS_PER_EPOCH.toNat) lastFirstEpoch)
      rw [Nat.succ_mul]
      omega
    obtain ⟨members, membersOk⟩ := Store.getCommitteesBetweenSlots_ok_of_slots finishAfter
      (fun slot low high => Store.getSlotCommittee_ok_of_getCommitteesBetweenSlots windowOk low
        (UInt64.le_trans high finishLe))
    obtain ⟨epochMembers, epochMembersOk⟩ :=
      Store.getCommitteesBetweenSlots_ok_of_slots finishAfter (fun slot low high =>
        Store.getSlotCommittee_ok_of_getCommitteesBetweenSlots windowOk
          (UInt64.le_trans (UInt64.le_iff_toNat_le.mpr startLow) low)
          (UInt64.le_trans high finishLe))
    have reserve := exit epoch epochStart next finish epochMembers startOk nextOk finishOk
      (UInt64.le_iff_toNat_le.mpr startLow) finishLe epochMembersOk
    have totalOk := weightOk
    rw [Store.computeCommitteeWeightBetweenSlots_of_covered coveredOk, mapError_ok_iff] at totalOk
    obtain ⟨indices, checked, -⟩ := bind_ok_iff.mp totalOk
    have activeIn : ∀ v ∈ Models.Network.activeVoters source,
        ∃ validator, source.validators.data[v.toNat]? = some validator ∧
          isActiveValidator validator (getCurrentEpoch source) = true := by
      intro v member
      rw [getActiveValidatorIndicesChecked_ok checked] at checked
      exact (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp
        (List.mem_toFinset.mp member)
    let kept := {v ∈ Models.Network.activeVoters source | v ∈ epochMembers}
    have keptIn : kept ⊆ Store.activeMembers source members := by
      intro v member
      obtain ⟨active, inEpoch⟩ := Finset.mem_filter.mp member
      obtain ⟨slot, low, high, committee, read, inCommittee⟩ :=
        (Store.mem_getCommitteesBetweenSlots_iff epochMembersOk v).mp inEpoch
      exact Store.mem_activeMembers.mpr
        ⟨(Store.mem_getCommitteesBetweenSlots_iff membersOk v).mpr
          ⟨slot, UInt64.le_trans (UInt64.le_iff_toNat_le.mpr startLow) low, high, committee, read,
            inCommittee⟩, activeIn v active⟩
    have split : Models.Network.activeVoters source =
        kept ∪ {v ∈ Models.Network.activeVoters source | v ∉ epochMembers} := by
      ext v
      simp only [kept, Finset.mem_union, Finset.mem_filter]
      tauto
    have stakeBound :
        stake (fun v => balanceAt source v.toNat) (Models.Network.activeVoters source) ≤
        stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members) +
          exitAllowance := by
      calc
        _ = stake (fun v => balanceAt source v.toNat)
            (kept ∪ {v ∈ Models.Network.activeVoters source | v ∉ epochMembers}) :=
          congrArg _ split
        _ ≤ _ := (stake_union_le _ _).trans (Nat.add_le_add (stake_mono keptIn) reserve)
    refine ⟨finish, members, finishLe, finishEpoch, membersOk, .inr ⟨prefixCovered, ?_⟩⟩
    have weightBound := weight_le_activeVoters coveredOk weightOk
    omega

/-- A nonempty range weighs at least one increment. -/
private theorem increment_le_weight {store : Store preset fork} {head : Root}
    {source : BeaconState preset fork} {first last : Slot} {weight : Gwei}
    (nonempty : first ≤ last)
    (weightOk : store.computeCommitteeWeightBetweenSlots head source first last = .ok weight) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ weight.toNat := by
  have notGt : ¬first > last := UInt64.not_lt.mpr nonempty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at weightOk
  obtain ⟨⟨_, members⟩, weightOk, rfl⟩ := weightOk
  simp only [Store.computeCommitteeWeightAndMembers, notGt, ↓reduceIte, bind_ok_iff] at weightOk
  obtain ⟨covered, -, weightOk⟩ := weightOk
  cases covered
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff] at weightOk
    obtain ⟨found, -, active, -, total, totalOk, final⟩ := weightOk
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, -⟩ := final
    rw [(getTotalBalance_ok_iff_stake.mp totalOk).2.2]
    exact le_max_left _ _
  · simp only [↓reduceIte, bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at weightOk
    obtain ⟨total, totalOk, rfl, -⟩ := weightOk
    rw [(getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)).2.2]
    exact le_max_left _ _

/-- A range that covers a whole epoch still covers one when it ends later. -/
private theorem covered_of_le {first finish last after : Slot}
    (covered : isFullValidatorSetCovered preset first finish = .ok true)
    (finishLe : finish ≤ last) (afterOk : addChecked last 1 = .ok after) :
    isFullValidatorSetCovered preset first last = .ok true := by
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at covered ⊢
  obtain ⟨afterFirst, firstOk, lastOfFirst, lastOfFirstOk, afterFinish, afterFinishOk,
    later⟩ := covered
  refine ⟨afterFirst, firstOk, lastOfFirst, lastOfFirstOk, after, afterOk, ?_⟩
  simp only [pure, Except.pure, Except.ok.injEq, decide_eq_true_eq] at later ⊢
  have finishNat := (addChecked_ok_iff.mp afterFinishOk).2
  have lastNat := (addChecked_ok_iff.mp afterOk).2
  have le := UInt64.le_iff_toNat_le.mp finishLe
  rw [UInt64.lt_iff_toNat_lt] at later ⊢
  simp only [computeEpochAtSlot, UInt64.toNat_div, UInt64.toNat_one] at later finishNat lastNat ⊢
  exact Nat.lt_of_lt_of_le later (Nat.div_le_div_right (by omega))

/-- The active members of a window inside another are active members of the other. -/
private theorem activeMembers_mono_of_window {store : Store preset fork} {head : Root}
    {source : BeaconState preset fork} {lowA highA lowB highB : Slot}
    {A B : Std.TreeSet ValidatorIndex}
    (readA : store.getCommitteesBetweenSlots head lowA highA = .ok A)
    (readB : store.getCommitteesBetweenSlots head lowB highB = .ok B)
    (low : lowB ≤ lowA) (high : highA ≤ highB) :
    Store.activeMembers source A ⊆ Store.activeMembers source B := by
  intro v member
  obtain ⟨inA, active⟩ := Store.mem_activeMembers.mp member
  obtain ⟨s, sLow, sHigh, rest⟩ := (Store.mem_getCommitteesBetweenSlots_iff readA v).mp inA
  exact Store.mem_activeMembers.mpr ⟨(Store.mem_getCommitteesBetweenSlots_iff readB v).mpr
    ⟨s, UInt64.le_trans low sLow, UInt64.le_trans sHigh high, rest⟩, active⟩

open Serialization.Ssz SszType

namespace Models.Network

variable {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A checkpoint read is a walk back to the first slot of the epoch. -/
private theorem getCheckpointBlock_walk {store : Store preset fork} {root checkpoint : Root}
    {epoch : Epoch} (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    ∃ start ancestor, computeStartSlotAtEpoch preset epoch = .ok start ∧
      store.getAncestor ⟨root, .pending⟩ start = .ok ancestor ∧ ancestor.root = checkpoint := by
  unfold Store.getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨start, startOk, ancestor, walk, eq⟩ := read
  exact ⟨start, ancestor, mapError_ok_iff.mp startOk, walk, eq⟩

/-- A block below a descendant reads the descendant's checkpoint block at an earlier epoch. -/
private theorem getCheckpointBlock_of_below {store : Store preset fork}
    (before : fork < .glamsterdam)
    {tip below checkpoint : Root} {belowBlock : BeaconBlock preset fork} {epoch : Epoch}
    {start : Slot} (belowFound : store.blocks[below]? = some belowBlock)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨below, .pending⟩ = .ok true)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    (within : start ≤ belowBlock.slot)
    (read : store.getCheckpointBlock tip epoch = .ok checkpoint) :
    store.getCheckpointBlock below epoch = .ok checkpoint := by
  obtain ⟨start', ancestor, startOk', walk, rooted⟩ := getCheckpointBlock_walk read
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  have toBelow := Store.getAncestor_of_isAncestor_of_lt before belowFound descends
  rw [Store.getAncestor_trans within toBelow] at walk
  simp [Store.getCheckpointBlock, startOk, walk, rooted, Except.mapError, bind, Except.bind,
    pure, Except.pure]

/-- The caller's finalized checkpoints from any earlier event fit a block below its head.

The block's epoch is at least one before the caller's current epoch.

So each finalized boundary lies at or before the block.

The block's walk back then reaches the finalized block.

It passes through the justified block when that block covers it.

Otherwise it passes through the viable head. -/
private theorem caller_fits_below_head {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (sound : Invariant anchorState)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (before : fork < .glamsterdam) {last : ℕ}
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ last →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (absent : ∀ a ∈ J, ∀ i, (e.world i).time ≤ last →
      ((e.world i).state a).blocks[anchorBlock.parentRoot]? = none)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (bounded : (e.world n).time ≤ last)
    {head : ForkChoiceNode} (headOk : ((e.world n).state u).getHead config = .ok head)
    {below : Root} {belowBlock : BeaconBlock preset fork}
    (belowFound : ((e.world n).state u).blocks[below]? = some belowBlock)
    (headDescends : ((e.world n).state u).isAncestor head ⟨below, .pending⟩ = .ok true)
    {epoch : Epoch} (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (near : epoch.toNat ≤ (computeEpochAtSlot preset belowBlock.slot).toNat + 1) :
    ∀ k' ≤ n, ∃ boundary,
      computeStartSlotAtEpoch preset ((e.world k').state u).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ belowBlock.slot ∧
      ((e.world n).state u).getCheckpointBlock below
        ((e.world k').state u).finalizedCheckpoint.epoch =
          .ok ((e.world k').state u).finalizedCheckpoint.root := by
  intro k' le
  set store := (e.world n).state u
  have forward := e.forwardReachable
    (fun w hw => (start w hw) ▸ Store.ForwardReachable.anchor anchored) n u caller
  have reached := forward.reachable
  -- The finalized epoch is at most the current one's predecessor, or the anchor's.
  have finalBound := forward.finalized_epoch_le_previous sound slots (UInt64.le_of_eq anchorSlot)
    epochOk
  have advanced := (e.checkpointsAdvance_of_le u le).2.epoch_le
  have earlier := UInt64.le_iff_toNat_le.mp advanced
  have anchorBelow := reached.anchorSlot_le (UInt64.le_of_eq anchorSlot) belowFound
  have anchorEpoch : (getCurrentEpoch anchorState).toNat ≤
      (computeEpochAtSlot preset belowBlock.slot).toNat := by
    rw [getCurrentEpoch, ← anchorSlot]
    exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp anchorBelow)
  set finalEpoch := ((e.world k').state u).finalizedCheckpoint.epoch
  have epochLe : finalEpoch.toNat ≤ (computeEpochAtSlot preset belowBlock.slot).toNat := by
    have := Nat.le_trans earlier finalBound
    omega
  -- The boundary of that epoch exists and lies at or before the block.
  have boundaryFits : finalEpoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ belowBlock.slot.toNat := by
    have scaled := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochLe
    simp only [computeEpochAtSlot, UInt64.toNat_div] at scaled
    exact scaled.trans (Nat.div_mul_le_self _ _)
  have boundaryOk : computeStartSlotAtEpoch preset finalEpoch =
      .ok (finalEpoch * preset.SLOTS_PER_EPOCH) := by
    have := belowBlock.slot.toNat_lt
    refine computeStartSlotAtEpoch_ok_iff.mpr ⟨by omega, ?_⟩
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have boundaryLe : finalEpoch * preset.SLOTS_PER_EPOCH ≤ belowBlock.slot := by
    have := belowBlock.slot.toNat_lt
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega)]
    exact boundaryFits
  refine ⟨_, boundaryOk, boundaryLe, ?_⟩
  -- The justified block reads the finalized block at that epoch.
  have justifiedRead := chain u caller k' n le bounded
  have lower := reached.parentsBelow (UInt64.le_of_eq anchorSlot) (absent u caller n bounded)
  -- The head is the justified block or a viable node of the filtered tree.
  have pending := Store.getHead_pending before headOk
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  obtain ⟨headBlock, headFound, -⟩ := Store.slot_le_of_isAncestor belowFound headDescends
  unfold Store.getHead at headOk
  cases tree : store.getFilteredNodeTree config with
  | error err => simp [store, tree, bind, Except.bind] at headOk
  | ok nodes =>
    simp only [store, tree, bind, Except.bind, notGloas, false_and, ↓reduceIte] at headOk
    have headRoot : head = ⟨head.root, .pending⟩ := by
      cases head
      simp_all
    have covered : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
          ⟨head.root, .pending⟩ = .ok true ∨ (⟨head.root, .pending⟩ : ForkChoiceNode) ∈ nodes := by
      rcases Store.getHeadFrom_mem headOk with same | member
      · left
        have justifiedFound : store.blocks[store.justifiedCheckpoint.root]? = some headBlock := by
          rw [same] at headFound
          exact headFound
        rw [same]
        exact Store.isAncestor_self justifiedFound
      · right
        rwa [← headRoot]
    rcases rootFinal_or_justified_covers anchored start anchorSlot before chain caller bounded
        lower headFound tree covered with justifiedCovers | fits
    · -- The justified block descends from the head, so from the block below it.
      have belowJustified := Store.isAncestor_trans_of_lt (middle := ⟨head.root, .pending⟩)
        before headFound belowFound justifiedCovers (headRoot ▸ headDescends)
      exact getCheckpointBlock_of_below before belowFound belowJustified boundaryOk boundaryLe
        justifiedRead
    · obtain ⟨boundary', boundaryOk', -, headRead⟩ := fits k' le
      exact getCheckpointBlock_of_below before belowFound (headRoot ▸ headDescends) boundaryOk
        boundaryLe headRead

end Models.Network

end EthLib.Consensus

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- An honest signature delivered by a time comes from the signer's validated duty vote.

The signer signed at the deadline of its duty, which is before the next slot starts. -/
private theorem exists_dutyVote_of_signed {Δ time : ℕ}
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    {v : ValidatorIndex} (honest : v ∈ J) {j : ℕ} {message : Message preset fork}
    {attestation : Attestation preset fork} (sent : message ∈ (e.world j).sent)
    (signed : (v, attestation.data) ∈ statements config checks anchorState anchorBlock message)
    {next : Slot} {nextTime : UInt64}
    (nextOk : addChecked attestation.data.slot 1 = .ok next)
    (nextTimeOk : computeTimeAtSlotMs config genesisTimeMs next = .ok nextTime)
    (bound : nextTime.toNat ≤ time) :
    ∃ slotTime deadline,
      computeTimeAtSlotMs config genesisTimeMs attestation.data.slot = .ok slotTime ∧
      IsAttestationDeadline fork config genesisTimeMs attestation.data.slot deadline ∧
      e.startTime ≤ deadline ∧
      attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot ∧
      ∃ n committee duty indexed, VoteAt e v attestation.data.slot committee deadline n duty
        indexed ∧
        ∀ withTarget targetState,
          ((e.world n).state v).storeTargetCheckpointState config checks duty.data.target =
            .ok withTarget →
          withTarget.checkpointState duty.data.target = .ok targetState →
          checkAttestationCommittees targetState duty = .ok () := by
  -- The signer signed at the deadline of a duty of the slot of the vote.
  obtain ⟨signer, -, committee, assigned, deadlineOk, -, -, honestData, -⟩ :=
    e.exists_maySign_of_signed sent signed honest
  obtain ⟨_, _, _, _, _, _, _, _, made⟩ := honestData
  -- The duty's deadline is before the next slot starts, so the duty vote exists.
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  obtain ⟨slotTime, slotTimeOk, -, -⟩ := exists_timeAtSlotMs_of_le
    (slot := attestation.data.slot) (UInt64.le_iff_toNat_le.mpr (by omega)) nextTimeOk
  have beforeBoundary := fits.before_boundary nextOk slotTimeOk nextTimeOk deadlineOk
  have started : e.startTime ≤ (e.world signer).time := by
    have := e.monotone_time (Nat.zero_le signer)
    simpa [Execution.world_zero, World.initial] using this
  obtain ⟨n, duty, indexed, vote, committees⟩ := votes v honest _ committee _ assigned deadlineOk
    started (by omega)
  exact ⟨slotTime, _, slotTimeOk, deadlineOk, started, target_epoch_eq_of_getAttestationData made,
    n, committee, duty, indexed, vote, committees⟩

/-- A delivered honest signature reaches a receiver's latest votes, with at least its rank.

The signer signed it at the deadline of its duty, so its validated duty vote carries its data.

The voted block descends from a root that the receiver holds, as some honest store reads it.

Otherwise the receiver's justified block descends from the root.

A finalized checkpoint then fits neither the root nor the voted block.

Bounded honest stores may also collide instead. -/
private theorem latest_rank_of_signed {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ValidatedDutyVotes (e := e) time)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {v w a : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) (holder : a ∈ J)
    {j i : ℕ} {message : Message preset fork} {attestation : Attestation preset fork}
    (sent : message ∈ (e.world j).sent)
    (signed : (v, attestation.data) ∈ statements config checks anchorState anchorBlock message)
    {next : Slot} {nextTime : UInt64}
    (nextOk : addChecked attestation.data.slot 1 = .ok next)
    (nextTimeOk : computeTimeAtSlotMs config genesisTimeMs next = .ok nextTime)
    {k : ℕ} (boundaryLe : nextTime.toNat ≤ (e.world k).time) (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) {root : Root} {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (heldTime : (e.world i).time ≤ time)
    (heldRoot : ((e.world i).state a).blocks[root]? = some rootBlock)
    (heldDescends : ((e.world i).state a).isAncestor ⟨attestation.data.beaconBlockRoot, .pending⟩
      ⟨root, .pending⟩ = .ok true)
    (rootFinal : ∀ k' ≤ k,
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      ((∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ rootBlock.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
        ∀ u ∈ J, ∀ j, (e.world j).time ≤ time → ∀ b,
          ((e.world j).state u).blocks[attestation.data.beaconBlockRoot]? = some b →
          ((e.world j).state u).getCheckpointBlock attestation.data.beaconBlockRoot
            ((e.world k').state w).finalizedCheckpoint.epoch =
              .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) :
    ((∃ latest, ((e.world k).state w).latestMessages[v]? = some latest ∧
      attestation.data.target.epoch ≤ latest.rank) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true ∧
      ∃ k' ≤ k, UpToDate config checks sources (e.world k').time ((e.world k').view w)
          ((e.world k').state w) ∧
        ¬ ((∃ boundary,
          computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok boundary ∧ boundary ≤ rootBlock.slot ∧
          ((e.world k).state w).getCheckpointBlock root
            ((e.world k').state w).finalizedCheckpoint.epoch =
              .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
          ∀ u ∈ J, ∀ j, (e.world j).time ≤ time → ∀ b,
            ((e.world j).state u).blocks[attestation.data.beaconBlockRoot]? = some b →
            ((e.world j).state u).getCheckpointBlock attestation.data.beaconBlockRoot
              ((e.world k').state w).finalizedCheckpoint.epoch =
                .ok ((e.world k').state w).finalizedCheckpoint.root)) ∨
    HonestCollision (e := e) time := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agree | collision
  swap
  · obtain ⟨⟨u, n⟩, ⟨hu, hn⟩, ⟨v, m⟩, ⟨hv, hm⟩, root, collision, found⟩ := collision
    exact .inr ⟨u, hu, v, hv, n, m, hn, hm, root, collision, found⟩
  have reached := fun u hu j => e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) j u hu
  obtain ⟨slotTime, deadline, slotTimeOk, deadlineOk, started, signedEpoch, n, committee, duty,
    indexed, vote, committees⟩ := exists_dutyVote_of_signed votes fits honest sent signed nextOk
      nextTimeOk (atTime ▸ boundaryLe)
  obtain ⟨due, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextOk slotTimeOk nextTimeOk dueOk
  obtain ⟨dataSlot, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, -⟩ :=
    vote.data_head anchored (UInt64.le_of_eq anchorSlot) start honest deadlineOk dueOk dueLt
  -- The duty vote and the signature share the target epoch, so they carry one data.
  obtain ⟨dutySent, dutySigned⟩ := vote.signed_sent anchored start honest
  have sameData := Execution.data_eq_of_signed_of_target_epoch slots dutySent sent dutySigned
    signed honest (by rw [dataEpoch, signedEpoch])
  -- The signer's head at the duty is the voted block, which descends from the root.
  have pending := Store.getHead_pending preGloas headOk
  have headEq : head = ⟨attestation.data.beaconBlockRoot, .pending⟩ := by
    cases head
    simp_all
  have beforeBoundary := fits.before_boundary nextOk slotTimeOk nextTimeOk deadlineOk
  have dutyTime : (e.world n).time ≤ time := by rw [vote.atTime]; omega
  have supports : ∀ h, ((e.world n).state v).getHead config = .ok h →
      ((e.world n).state v).isAncestor h ⟨root, .pending⟩ = .ok true := by
    intro h hOk
    rw [headOk, Except.ok.injEq] at hOk
    subst hOk
    rw [headEq]
    exact Store.isAncestor_of_same_blocks (reached v honest n) preGloas
      (agree (a, i) ⟨holder, heldTime⟩ (v, n) ⟨honest, dutyTime⟩) heldRoot
      ((reached a holder i).anchorSlot_le (UInt64.le_of_eq anchorSlot) heldRoot)
      ⟨headBlock, by rw [← sameData, dataRoot]; exact headKnown⟩ heldDescends
  -- A fit of the voted block in every honest store is a fit of the signer's head.
  have headFits : ∀ {epoch : Epoch} {checkpoint : Root},
      (∀ u ∈ J, ∀ j, (e.world j).time ≤ time → ∀ b,
        ((e.world j).state u).blocks[attestation.data.beaconBlockRoot]? = some b →
        ((e.world j).state u).getCheckpointBlock attestation.data.beaconBlockRoot epoch =
          .ok checkpoint) →
      ∀ h, ((e.world n).state v).getHead config = .ok h →
        ((e.world n).state v).getCheckpointBlock h.root epoch = .ok checkpoint := by
    intro epoch checkpoint fits h hOk
    rw [headOk, Except.ok.injEq] at hOk
    subst hOk
    rw [headEq]
    exact fits v honest n dutyTime headBlock (by rw [← sameData, dataRoot]; exact headKnown)
  rw [← sameData]
  rw [← sameData] at nextOk
  have slotEq := dataSlot
  rcases e.latest_rank_of_voteAt sync slots preGloas admitted fits prompt anchored anchorSlot
      anchorBoundary start chain nonzero honest receiver vote committees
      (dataSlot ▸ nextOk) (dataSlot ▸ (sameData ▸ slotTimeOk)) nextTimeOk deadlineOk started
      boundaryLe atTime upToDate known supports
      (fun k' le _ current => (rootFinal k' le current).imp_left (Or.imp_right headFits)) with
    (latest | ⟨covered, k', le, -, current, unfit⟩) | collision
  · exact .inl (.inl latest)
  · exact .inl (.inr ⟨covered, k', le, current,
      fun fits => by rw [sameData] at fits; exact unfit (fits.imp_right headFits)⟩)
  · exact .inr collision

/-- A supporter of a store is active and not slashed in its source of balances. -/
private theorem active_of_mem_supportersOf {store : Store preset fork}
    {state : BeaconState preset fork} {node : ForkChoiceNode} {v : ValidatorIndex}
    (member : v ∈ store.supportersOf state node) :
    v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
  simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at member
  obtain ⟨entry, ⟨inList, -⟩, rfl⟩ := member
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, inList, rfl⟩)

/-- A receiver's later honest vote has only origins from the caller's slot on, or stores collide.

The receiver's vote outranks the caller's latest vote.

That vote is from a slot at or after a historical block below the caller's head.

An older origin would have reached the caller first.

From the caller's epoch on, honest heads descend from the historical block.

The caller holds the finalized prefix of that block. -/
private theorem receiver_origins_fresh {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ValidatedDutyVotes (e := e) time)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (absent : AnchorParentAbsent (e := e) time)
    {u w v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J)
    {n k : ℕ} (callerTime : (e.world n).time ≤ time)
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {slot : Slot} {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    {head : ForkChoiceNode} (headOk : ((e.world n).state u).getHead config = .ok head)
    {historical : Root} {historicalBlock : BeaconBlock preset fork}
    (historicalFound : ((e.world n).state u).blocks[historical]? = some historicalBlock)
    (headHistorical : ((e.world n).state u).isAncestor head ⟨historical, .pending⟩ = .ok true)
    {callerEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (near : callerEpoch.toNat ≤ (computeEpochAtSlot preset historicalBlock.slot).toNat + 1)
    {epochStart : Slot} {epochStartTime : UInt64}
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    {attestation : Attestation preset fork}
    (latest : ((e.world n).state u).latestMessages[v]? =
      some (LatestMessage.ofAttestation attestation))
    (targetEpoch : attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot)
    (voteAbove : (computeEpochAtSlot preset historicalBlock.slot).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat)
    {received : LatestMessage fork}
    (greater : (LatestMessage.ofAttestation (fork := fork) attestation).rank < received.rank) :
    (∀ (later : Attestation preset fork) (laterIn : Message preset fork)
      (laterTime : UInt64), received = LatestMessage.ofAttestation later →
      laterIn ∈ (e.world k).view w →
      (v, later.data) ∈ statements config checks anchorState anchorBlock laterIn →
      computeTimeAtSlotMs config genesisTimeMs later.data.slot = .ok laterTime →
      (e.world n).time ≤ laterTime.toNat) ∨
    HonestCollision (e := e) time := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agree | collision
  swap
  · obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, evidence, searched⟩ := collision
    exact .inr ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have upToTime : (e.world n).time ≤ time := callerTime
  by_cases allFresh : ∀ (later : Attestation preset fork) (laterIn : Message preset fork)
      (laterTime : UInt64), received = LatestMessage.ofAttestation later →
      laterIn ∈ (e.world k).view w →
      (v, later.data) ∈ statements config checks anchorState anchorBlock laterIn →
      computeTimeAtSlotMs config genesisTimeMs later.data.slot = .ok laterTime →
      (e.world n).time ≤ laterTime.toNat
  · exact .inl allFresh
  -- Otherwise some origin is older than the call; it then reached the caller first.
  push Not at allFresh
  obtain ⟨later, laterIn, laterTime, receivedEq, laterSeen, laterSigned, laterTimeOk, stale⟩ :=
    allFresh
  subst receivedEq
  have laterBefore : later.data.slot < slot := by
    refine UInt64.not_le.mp fun atLeast => ?_
    obtain ⟨begin', beginOk', -, beginLe⟩ := exists_timeAtSlotMs_of_le atLeast laterTimeOk
    rw [beginOk, Except.ok.injEq] at beginOk'
    subst begin'
    have := UInt64.le_iff_toNat_le.mp beginLe
    omega
  -- The signer voted at the deadline of the later slot, from a head above the historical block.
  obtain ⟨signer, -, committee, -, deadlineOk, -, signerUpToDate, honestData, -⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent k w laterSeen) laterSigned honest
  obtain ⟨signerHead, _, _, _, signerHeadOk, _, _, _, made⟩ := honestData
  have laterRoot := (getAttestationData_eq_ok_iff.mp made).2.2.2.1
  have laterEpoch := target_epoch_eq_of_getAttestationData made
  have laterRank : (LatestMessage.ofAttestation (fork := fork) later).rank =
      later.data.target.epoch := by
    simp [LatestMessage.rank, LatestMessage.ofAttestation, notGloas]
  have earlierRank : (LatestMessage.ofAttestation (fork := fork) attestation).rank =
      attestation.data.target.epoch := by
    simp [LatestMessage.rank, LatestMessage.ofAttestation, notGloas]
  rw [laterRank, earlierRank, laterEpoch, targetEpoch] at greater
  -- The later slot is in the caller's epoch, since the earlier vote is after the historical block.
  have laterEpochGe := UInt64.lt_iff_toNat_lt.mp greater
  have startLe : epochStart ≤ later.data.slot := by
    have startNat := (computeStartSlotAtEpoch_ok_iff.mp epochStartOk).2
    rw [UInt64.le_iff_toNat_le, startNat]
    have floor := Nat.div_mul_le_self later.data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have scaled := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (show callerEpoch.toNat ≤ (computeEpochAtSlot preset later.data.slot).toNat by omega)
    simp only [computeEpochAtSlot, UInt64.toNat_div] at scaled
    exact scaled.trans floor
  -- The deadline is inside the historical cover, and before the call.
  obtain ⟨startTime, due', startOk, dueOk', signerTime⟩ := deadlineOk
  obtain ⟨epochStartTime', epochStartOk', -, epochStartLe⟩ :=
    exists_timeAtSlotMs_of_le startLe startOk
  rw [epochStartTimeOk, Except.ok.injEq] at epochStartOk'
  subst epochStartTime'
  have laterNextFits : later.data.slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := slot.toNat_lt
    have := UInt64.lt_iff_toNat_lt.mp laterBefore
    simp only [UInt64.toNat_one]
    omega
  have laterNextOk := addChecked_of_lt laterNextFits
  have laterNextNat := (addChecked_ok_iff.mp laterNextOk).2
  simp only [UInt64.toNat_one] at laterNextNat
  obtain ⟨laterNextTime, laterNextTimeOk, -, laterNextLe⟩ := exists_timeAtSlotMs_of_le
    (slot := later.data.slot + 1)
    (UInt64.le_iff_toNat_le.mpr (by have := UInt64.lt_iff_toNat_lt.mp laterBefore; omega))
    beginOk
  have deadlineBefore := fits.before_boundary laterNextOk startOk laterNextTimeOk
    ⟨startTime, due', startOk, dueOk', signerTime⟩
  have laterNextLeNat := UInt64.le_iff_toNat_le.mp laterNextLe
  have signerBefore : (e.world signer).time < (e.world n).time := by omega
  have signerAfter : epochStartTime.toNat ≤ (e.world signer).time := by
    have := UInt64.le_iff_toNat_le.mp epochStartLe
    omega
  have signerDescends := historyCovers (e.world signer).time signerAfter signerBefore v honest
    signer signerHead rfl signerUpToDate signerHeadOk
  have signerPending := Store.getHead_pending preGloas signerHeadOk
  have signerHeadEq : signerHead = ⟨later.data.beaconBlockRoot, .pending⟩ := by
    cases signerHead
    simp_all
  rw [signerHeadEq] at signerDescends
  -- The signer holds the historical block, the same block as the caller.
  have signerHistorical :
      ((e.world signer).state v).blocks[historical]? = some historicalBlock := by
    have test := signerDescends
    unfold Store.isAncestor at test
    simp only [bind_ok_iff] at test
    obtain ⟨held, heldOk, _⟩ := test
    have heldFound := Store.block_ok_iff.mp heldOk
    have same := agree (v, signer) ⟨honest, signerBefore.le.trans callerTime⟩ (u, n)
      ⟨caller, callerTime⟩ historical
      held historicalBlock heldFound historicalFound
    exact same ▸ heldFound
  -- The caller then records the later vote, against its latest vote.
  have chainBefore : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ (e.world n).time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root :=
    fun w hw i k le bounded => chain w hw i k le (bounded.trans upToTime)
  have absentBefore : ∀ a ∈ J, ∀ i, (e.world i).time ≤ (e.world n).time →
      ((e.world i).state a).blocks[anchorBlock.parentRoot]? = none :=
    fun a ha i bounded => absent a ha i (bounded.trans upToTime)
  have fitsHistorical := caller_fits_below_head anchored start sound slots anchorSlot preGloas
    chainBefore absentBefore caller (le_refl _) headOk historicalFound headHistorical
    callerEpochOk near
  rcases latest_rank_of_signed sync slots preGloas
      (fun a ha b hb i j bounded => admitted a ha b hb i j (bounded.trans upToTime))
      (fun a ha s c d assigned deadline started bounded =>
        votes a ha s c d assigned deadline started (bounded.trans upToTime))
      fits (prompt.of_le upToTime) anchored anchorSlot anchorBoundary start chainBefore
      (fun a ha i bounded => nonzero a ha i (bounded.trans upToTime))
      honest caller honest (e.view_subset_sent k w laterSeen) laterSigned laterNextOk
      laterNextTimeOk (by omega) rfl callerUpToDate historicalFound signerBefore.le
      signerHistorical signerDescends (fun k' le _ => .inl (.inl (fitsHistorical k' le))) with
    (⟨again, againOk, againRank⟩ | ⟨-, k', le, -, unfit⟩) | ⟨a, ha, b, hb, i, j, hi, hj, r, ev, s⟩
  · rw [latest, Option.some.injEq] at againOk
    subst againOk
    rw [earlierRank, targetEpoch, laterEpoch] at againRank
    exact absurd (UInt64.le_iff_toNat_le.mp againRank) (by omega)
  · exact (unfit (.inl (fitsHistorical k' le))).elim
  · exact .inr ⟨a, ha, b, hb, i, j, hi.trans upToTime, hj.trans upToTime, r, ev, s⟩

private theorem historical_stores_or_collision {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) (time : ℕ) :
    ((∀ a ∈ J, ∀ i, Store.Reachable config anchorState anchorBlock ((e.world i).state a)) ∧
      ∀ i : ValidatorIndex × ℕ, i.1 ∈ J ∧ (e.world i.2).time ≤ time →
        ∀ j : ValidatorIndex × ℕ, j.1 ∈ J ∧ (e.world j.2).time ≤ time →
          ∀ (r : Root) (left right : BeaconBlock preset fork),
            ((e.world i.2).state i.1).blocks[r]? = some left →
            ((e.world j.2).state j.1).blocks[r]? = some right → left = right) ∨
      HonestCollision (e := e) time := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agree | collision
  · exact .inl ⟨fun a ha i => e.reachable
      (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) i a ha, agree⟩
  · obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, evidence, searched⟩ := collision
    exact .inr ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩

private theorem signed_origin_before_slot {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {n : ℕ} {v : ValidatorIndex} {message : LatestMessage fork} {slot : Slot}
    (latest : ((e.world n).state u).latestMessages[v]? = some message)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) :
    ∃ attestation : Attestation preset fork, ∃ m ∈ (e.world n).view u,
      message = LatestMessage.ofAttestation attestation ∧
      (v, attestation.data) ∈ statements config checks anchorState anchorBlock m ∧
      ((e.world n).state u).VoteOrigin config v attestation ∧ attestation.data.slot < slot := by
  obtain ⟨attestation, m, seen, same, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start caller latest
  obtain ⟨current, currentOk, past⟩ := origin.past
  rw [slotOk, Except.ok.injEq] at currentOk
  subst currentOk
  exact ⟨attestation, m, seen, same, signed, origin, past⟩

private theorem successor_time_of_past {vote slot : Slot} {begin : UInt64}
    (past : vote < slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin) :
    addChecked vote 1 = .ok (vote + 1) ∧
      ∃ nextTime, computeTimeAtSlotMs config genesisTimeMs (vote + 1) = .ok nextTime ∧
        nextTime.toNat ≤ begin.toNat := by
  have pastNat := UInt64.lt_iff_toNat_lt.mp past
  have nextFits : vote.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := slot.toNat_lt
    simp only [UInt64.toNat_one]
    omega
  have nextOk := addChecked_of_lt nextFits
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  obtain ⟨nextTime, nextTimeOk, -, nextLe⟩ := exists_timeAtSlotMs_of_le
    (slot := vote + 1) (UInt64.le_iff_toNat_le.mpr (by omega)) beginOk
  exact ⟨nextOk, nextTime, nextTimeOk, UInt64.le_iff_toNat_le.mp nextLe⟩

/-- An honest supporter of the caller supports the root at the receiver.

Otherwise the receiver's justified block descends from the root, or bounded honest stores collide.

The caller reads at the start of its slot.

The receiver records the supporter's vote, and its later votes after the call support the root.

A later vote before the call would have reached the caller.

From the caller's epoch on, honest heads descend from a block below the parent.

The caller holds the finalized prefix of that block. -/
private theorem caller_supporter_reaches {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ValidatedDutyVotes (e := e) time)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (absent : AnchorParentAbsent (e := e) time)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J)
    {n k : ℕ} (callerTime : (e.world n).time ≤ time)
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {slot : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    {head : ForkChoiceNode} (headOk : ((e.world n).state u).getHead config = .ok head)
    {root : Root} {block parent : BeaconBlock preset fork}
    (found : ((e.world n).state u).blocks[root]? = some block)
    (parentFound : ((e.world n).state u).blocks[block.parentRoot]? = some parent)
    (headDescends : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    {historical : Root} {historicalBlock : BeaconBlock preset fork}
    (historicalFound : ((e.world n).state u).blocks[historical]? = some historicalBlock)
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    {callerEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (near : callerEpoch.toNat ≤ (computeEpochAtSlot preset historicalBlock.slot).toNat + 1)
    {epochStart : Slot} {epochStartTime : UInt64}
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    (rootCovers : HonestHeadsCover (e := e) root (e.world n).time time)
    (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finality : ReceiverFinalityCovers (e := e) w k root block)
    {source : BeaconState preset fork}
    (supporter : v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩) :
    (v ∈ ((e.world k).state w).supportersOf source ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) ∨
    HonestCollision (e := e) time := by
  rcases historical_stores_or_collision anchored start time with ⟨reached, agree⟩ | collision
  swap
  · exact .inr collision
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  set callerStore := (e.world n).state u
  -- The supporter's latest vote at the caller is an honest signature for a block above the root.
  obtain ⟨message, supported, latest, clean, supportedOk, voteDescends⟩ :=
    callerStore.exists_of_voteCountsFor (Store.voteCountsFor_of_mem_supportersOf supporter)
  rw [Store.getSupportedNode_of_lt preGloas, Except.ok.injEq] at supportedOk
  subst supportedOk
  obtain ⟨attestation, signedIn, seen, messageEq, signed, origin, past⟩ :=
    signed_origin_before_slot anchored start caller latest slotOk
  subst messageEq
  have rootOfMessage : (LatestMessage.ofAttestation (fork := fork) attestation).root =
      attestation.data.beaconBlockRoot := rfl
  rw [rootOfMessage] at voteDescends
  -- The vote is before the caller's slot, and at or after the root's slot.
  obtain ⟨voted, votedFound, votedLe⟩ := origin.voted
  obtain ⟨votedBlock, votedFound', votedAbove⟩ := Store.slot_le_of_isAncestor found voteDescends
  rw [votedFound, Option.some.injEq] at votedFound'
  subst votedFound'
  have pastNat := UInt64.lt_iff_toNat_lt.mp past
  obtain ⟨nextOk, nextTime, nextTimeOk, nextLeNat⟩ := successor_time_of_past past beginOk
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  -- The receiver records the vote, or its justified block descends from the root.
  rcases latest_rank_of_signed sync slots preGloas admitted votes fits prompt anchored anchorSlot
      anchorBoundary start chain nonzero honest receiver caller
      (e.view_subset_sent n u seen) signed nextOk nextTimeOk (by omega) atTime upToDate known
      callerTime found voteDescends
      (fun k' le current => (finality k' le current).imp_left .inl) with
    (⟨received, receivedOk, rank⟩ | ⟨covered, -⟩) | collision
  rotate_left
  · exact .inl (.inr covered)
  · exact .inr collision
  have counted := e.equivocatingIndices_honest slots
    (fun a ha b hb => by
      simp [start a ha, Store.getForkchoiceStore_equivocatingIndices anchored] at hb)
    k receiver v
  have notCounted : v ∉ ((e.world k).state w).equivocatingIndices :=
    fun member => counted member honest
  have active := active_of_mem_supportersOf supporter
  set receiverStore := (e.world k).state w
  have rankLe : (LatestMessage.ofAttestation (fork := fork) attestation).rank ≤ received.rank := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  rcases UInt64.lt_or_eq_of_le rankLe with greater | same
  swap
  · -- The same rank gives the same vote, which supports the root at the receiver too.
    have sameVote := Execution.latest_eq_of_rank_eq slots preGloas anchored start caller receiver
      honest latest receivedOk same
    subst sameVote
    obtain ⟨other, otherIn, otherSeen, otherEq, -, otherOrigin⟩ :=
      e.exists_signed_origin_of_latestMessages anchored start receiver receivedOk
    obtain ⟨tip, tipFound, -⟩ := otherOrigin.voted
    have tipRoot : other.data.beaconBlockRoot = attestation.data.beaconBlockRoot := by
      have := congrArg LatestMessage.root otherEq
      simpa [LatestMessage.ofAttestation] using this.symm
    rw [tipRoot] at tipFound
    have receiverDescends := Store.isAncestor_of_same_blocks (reached w receiver k) preGloas
      (agree (u, n) ⟨caller, callerTime⟩ (w, k) ⟨receiver, le_of_eq atTime⟩) found
      ((reached u caller n).anchorSlot_le (UInt64.le_of_eq anchorSlot) found) ⟨tip, tipFound⟩
      voteDescends
    left
    left
    have check : receiverStore.voteCountsFor ⟨root, .pending⟩ v = true := by
      apply Store.voteCountsFor_of_check _ receivedOk (by simpa using notCounted)
      simpa only [Store.getSupportedNode_of_lt preGloas, bind, Except.bind,
        LatestMessage.ofAttestation] using receiverDescends
    simp only [List.mem_toFinset, List.mem_map] at active
    obtain ⟨entry, member, eq⟩ := active
    simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter]
    exact ⟨entry, ⟨member, eq ▸ check⟩, eq⟩
  -- A higher rank: every signed origin of the receiver's vote is from the caller's slot on.
  obtain ⟨due, dueOk⟩ := fits.1
  obtain ⟨voteTime, voteTimeOk, -, -⟩ := exists_timeAtSlotMs_of_le
    (slot := attestation.data.slot) (UInt64.le_iff_toNat_le.mpr (by omega)) nextTimeOk
  have dueLt := fits.due_lt_slot nextOk voteTimeOk nextTimeOk dueOk
  have rootAbove := (reached w receiver k).anchorSlot_le (UInt64.le_of_eq anchorSlot) known
  -- The vote is after the historical block, which is below the caller's head.
  have lower := (reached u caller n).parentsBelow (UInt64.le_of_eq anchorSlot)
    (absent u caller n callerTime)
  have parentBelow := lower root block parent found parentFound
  obtain ⟨parent', parentFound', historicalLe⟩ :=
    Store.slot_le_of_isAncestor historicalFound historicalBelow
  rw [parentFound, Option.some.injEq] at parentFound'
  subst parentFound'
  have voteAbove : (computeEpochAtSlot preset historicalBlock.slot).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat := by
    apply epoch_le_of_slot_le
    have := UInt64.le_iff_toNat_le.mp historicalLe
    have := UInt64.lt_iff_toNat_lt.mp parentBelow
    have := UInt64.le_iff_toNat_le.mp votedAbove
    have := UInt64.le_iff_toNat_le.mp votedLe
    omega
  have headHistorical : ((e.world n).state u).isAncestor head ⟨historical, .pending⟩ = .ok true :=
    Store.isAncestor_trans_of_lt preGloas parentFound historicalFound
      (Store.isAncestor_trans_of_lt preGloas found parentFound headDescends
        (Store.isAncestor_pending_parent_of_slot_lt (node := ⟨root, .pending⟩) found parentFound
          parentBelow))
      historicalBelow
  rcases receiver_origins_fresh sync slots preGloas admitted votes fits prompt anchored sound
      anchorSlot anchorBoundary start chain nonzero absent caller honest callerTime
      callerUpToDate beginOk timeEq headOk historicalFound headHistorical callerEpochOk near
      epochStartOk epochStartTimeOk historyCovers latest origin.targetEpoch voteAbove greater
      (w := w) (k := k) with allFresh | collision
  swap
  · exact .inr collision
  rcases Execution.mem_supportersOf_of_latest_signed anchored start preGloas honest receiver
      receivedOk notCounted upToDate (le_of_eq atTime) dueOk dueLt allFresh
      (fun earlier low high => rootCovers earlier low (atTime ▸ high)) known rootAbove active
    with member | ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩
  · exact .inl (.inl member)
  · exact .inr ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩

/-- An honest active committee member is unslashed in the caller's checkpoint state. -/
private theorem honest_unslashedActive_of_checkpointState {time : ℕ}
    (counted : HonestCountedStatesUnslashed (e := e) time) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerTime : (e.world n).time ≤ time) {checkpoint : Checkpoint}
    {source : BeaconState preset fork}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    {participants : Std.TreeSet ValidatorIndex} {v : ValidatorIndex} (honest : v ∈ J)
    (member : v ∈ Store.activeMembers source participants) :
    v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset := by
  have unslashed := Execution.notSlashed_checkpointState anchored start caller
    (fun root base found => counted u caller n base callerTime ⟨root, base, found, .inl rfl⟩)
    sourceOk v honest
  obtain ⟨_, validator, found, active⟩ := Store.mem_activeMembers.mp member
  have flag : validator.slashed = false := by
    simpa [slashedFlagAt, found] using unslashed
  exact List.mem_toFinset.mpr (mem_unslashedActiveBalances_of_found found active flag)

/-- An honest parent voter of the caller supports the root or the parent at the receiver.

Otherwise the receiver's justified block descends from the root, or bounded honest stores collide.

The receiver holds the parent, which fits each of its finalized checkpoints.

A boundary at or below the parent passes the root's fit to the parent.

A boundary past the parent makes the checkpoint the parent itself, or the root.

A vote of the same rank is the caller's vote for the parent, in both windows.

A later vote supports the root, as for the caller's supporters. -/
private theorem caller_parent_voter_reaches {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ValidatedDutyVotes (e := e) time)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    (windows : AssignmentWindowAgreement (e := e) time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (absent : AnchorParentAbsent (e := e) time)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J)
    {n k : ℕ} (callerTime : (e.world n).time ≤ time)
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {slot last : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (lastOk : subChecked slot 1 = .ok last)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    {head : ForkChoiceNode} (headOk : ((e.world n).state u).getHead config = .ok head)
    {root : Root} {block parent : BeaconBlock preset fork}
    (found : ((e.world n).state u).blocks[root]? = some block)
    (parentFound : ((e.world n).state u).blocks[block.parentRoot]? = some parent)
    (headDescends : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    {historical : Root} {historicalBlock : BeaconBlock preset fork}
    (historicalFound : ((e.world n).state u).blocks[historical]? = some historicalBlock)
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    {callerEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (near : callerEpoch.toNat ≤ (computeEpochAtSlot preset historicalBlock.slot).toNat + 1)
    {epochStart : Slot} {epochStartTime : UInt64}
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    (rootCovers : HonestHeadsCover (e := e) root (e.world n).time time)
    (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finality : ReceiverFinalityCovers (e := e) w k root block)
    {receiverHead : ForkChoiceNode}
    (receiverHeadOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (receiverParent : ((e.world k).state w).isAncestor receiverHead
      ⟨block.parentRoot, .pending⟩ = .ok true)
    {current receiverLast : Slot} {receiverEpoch : Epoch}
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (receiverNear : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (receiverLastOk : subChecked current 1 = .ok receiverLast)
    {first beforeBlock : Slot} (firstOk : addChecked parent.slot 1 = .ok first)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    {parentParticipants participants : Std.TreeSet ValidatorIndex}
    (callerParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first
      beforeBlock = .ok parentParticipants)
    (participantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      beforeBlock = .ok participants)
    {source : BeaconState preset fork}
    (voter : v ∈ ((e.world n).state u).parentVotersOf source parentParticipants block parent) :
    (v ∈ ((e.world k).state w).supportersOf source ⟨root, .pending⟩ ∨
      v ∈ ((e.world k).state w).parentVotersOf source participants block parent ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) ∨
    HonestCollision (e := e) time := by
  rcases historical_stores_or_collision anchored start time with ⟨reached, agree⟩ | collision
  swap
  · exact .inr collision
  have forward := fun a ha i => e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) i a ha
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have receiverTime : (e.world k).time ≤ time := le_of_eq atTime
  set callerStore := (e.world n).state u
  set receiverStore := (e.world k).state w
  -- The voter's latest vote at the caller is an honest signature for the parent.
  obtain ⟨inside, ⟨validator, validatorFound, unslashed, isActive⟩, notKnown, message, supported,
    latest, supportedOk, isParent⟩ := Store.mem_parentVotersOf.mp voter
  rw [Store.getSupportedNode_of_lt preGloas, Except.ok.injEq] at supportedOk
  subst supportedOk
  rw [Store.parentPayloadStatus_of_lt preGloas, or_self] at isParent
  obtain ⟨attestation, signedIn, seen, messageEq, signed, origin, past⟩ :=
    signed_origin_before_slot anchored start caller latest slotOk
  subst messageEq
  have votedRoot : attestation.data.beaconBlockRoot = block.parentRoot := by
    have := congrArg ForkChoiceNode.root isParent
    simpa [LatestMessage.ofAttestation] using this
  -- The vote is before the caller's slot, and at or after the parent's slot.
  obtain ⟨voted, votedFound, votedLe⟩ := origin.voted
  rw [votedRoot, parentFound, Option.some.injEq] at votedFound
  subst votedFound
  have pastNat := UInt64.lt_iff_toNat_lt.mp past
  obtain ⟨nextOk, nextTime, nextTimeOk, nextLeNat⟩ := successor_time_of_past past beginOk
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  -- The receiver holds the parent, below the root.
  have parentKnown : receiverStore.blocks[block.parentRoot]? = some parent := by
    have test := receiverParent
    unfold Store.isAncestor at test
    simp only [bind_ok_iff] at test
    obtain ⟨held, heldOk, _⟩ := test
    have heldFound := Store.block_ok_iff.mp heldOk
    have eq := agree (u, n) ⟨caller, callerTime⟩ (w, k) ⟨receiver, receiverTime⟩
      block.parentRoot parent held parentFound heldFound
    exact eq ▸ heldFound
  have lower := (reached u caller n).parentsBelow (UInt64.le_of_eq anchorSlot)
    (absent u caller n callerTime)
  have parentBelow := lower root block parent found parentFound
  have rootParent := Store.isAncestor_pending_parent_of_slot_lt (node := ⟨root, .pending⟩)
    known parentKnown parentBelow
  -- At each finalized checkpoint, the parent fits it, or the checkpoint descends from the root.
  have parentCases : ∀ k' ≤ k,
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      ((∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ parent.slot ∧
        receiverStore.getCheckpointBlock block.parentRoot
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
        ∀ a ∈ J, ∀ j, (e.world j).time ≤ time → ∀ b,
          ((e.world j).state a).blocks[attestation.data.beaconBlockRoot]? = some b →
          ((e.world j).state a).getCheckpointBlock attestation.data.beaconBlockRoot
            ((e.world k').state w).finalizedCheckpoint.epoch =
              .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      receiverStore.isAncestor ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
    intro k' le current
    rcases finality k' le current with ⟨boundary, boundaryOk, boundaryLe, checkpoint⟩ | covers
    swap
    · exact .inr covers
    by_cases below : boundary ≤ parent.slot
    · exact .inl (.inl ⟨boundary, boundaryOk, below,
        getCheckpointBlock_of_below preGloas parentKnown rootParent boundaryOk below checkpoint⟩)
    obtain ⟨boundary', ancestor, boundaryOk', walk, rooted⟩ := getCheckpointBlock_walk checkpoint
    rw [boundaryOk, Except.ok.injEq] at boundaryOk'
    subst boundaryOk'
    by_cases atBlock : block.slot ≤ boundary
    · -- The checkpoint is the root itself.
      rw [Store.getAncestor_of_le known atBlock, Except.ok.injEq] at walk
      subst walk
      rw [← rooted]
      exact .inr (Store.isAncestor_self known)
    · -- The checkpoint is the parent, which every honest store reads as its own checkpoint.
      have aboveParent : parent.slot ≤ boundary := UInt64.le_of_lt (UInt64.not_le.mp below)
      rw [Store.getAncestor_step known atBlock parentKnown parentBelow,
        Store.getAncestor_of_le parentKnown aboveParent, Except.ok.injEq] at walk
      subst walk
      refine .inl (.inr fun a ha j hj b held => ?_)
      rw [votedRoot] at held ⊢
      have same := agree (u, n) ⟨caller, callerTime⟩ (a, j) ⟨ha, hj⟩ block.parentRoot parent b
        parentFound held
      subst same
      have stays := Store.getAncestor_of_le (node := ⟨block.parentRoot, .pending⟩) held
        aboveParent
      rw [← rooted]
      simp [Store.getCheckpointBlock, boundaryOk, stays, Except.mapError, bind, Except.bind,
        pure, Except.pure]
  -- The receiver records the vote, or its justified block descends from the root.
  rcases latest_rank_of_signed sync slots preGloas admitted votes fits prompt anchored anchorSlot
      anchorBoundary start chain nonzero honest receiver caller
      (e.view_subset_sent n u seen) signed nextOk nextTimeOk (by omega) atTime upToDate
      parentKnown callerTime parentFound
      (by rw [votedRoot]; exact Store.isAncestor_self parentFound)
      (fun k' le current => (parentCases k' le current).imp_right fun covers =>
        Store.isAncestor_trans_of_lt preGloas known parentKnown covers rootParent) with
    (⟨received, receivedOk, rank⟩ | ⟨-, k', le, current, unfit⟩) | collision
  rotate_left
  · -- The checkpoint descends from the root, and the justified block from the checkpoint.
    have covers := (parentCases k' le current).resolve_left unfit
    have checkpoint := chain w receiver k' k le receiverTime
    obtain ⟨_, finalized, _, held, _, descends⟩ :=
      Store.isAncestor_of_getCheckpointBlock checkpoint
    exact .inl (.inr (.inr (Store.isAncestor_trans_of_lt preGloas held known descends covers)))
  · exact .inr collision
  have counted := e.equivocatingIndices_honest slots
    (fun a ha b hb => by
      simp [start a ha, Store.getForkchoiceStore_equivocatingIndices anchored] at hb)
    k receiver v
  have notCounted : v ∉ receiverStore.equivocatingIndices :=
    fun member => counted member honest
  have rankLe : (LatestMessage.ofAttestation (fork := fork) attestation).rank ≤ received.rank := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  -- The parent's epoch bounds the epochs of both heads, so both windows read one assignment.
  have firstNat := (addChecked_ok_iff.mp firstOk).2
  simp only [UInt64.toNat_one] at firstNat
  have parentFirst := epoch_le_of_slot_le (preset := preset) parent.slot first (by omega)
  rcases UInt64.lt_or_eq_of_le rankLe with greater | same
  swap
  · -- The same rank gives the same vote, for the parent at the receiver too.
    have sameVote := Execution.latest_eq_of_rank_eq slots preGloas anchored start caller receiver
      honest latest receivedOk same
    subst sameVote
    obtain ⟨historicalParent, historicalParentFound, historicalLe⟩ :=
      Store.slot_le_of_isAncestor historicalFound historicalBelow
    rw [parentFound, Option.some.injEq] at historicalParentFound
    subst historicalParentFound
    have callerEpochEq : computeEpochAtSlot preset slot = callerEpoch := by
      simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
        using callerEpochOk
    have receiverEpochEq : computeEpochAtSlot preset current = receiverEpoch := by
      simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
        using receiverEpochOk
    have historicalParent := epoch_le_of_slot_le (preset := preset) historicalBlock.slot parent.slot
      (UInt64.le_iff_toNat_le.mp historicalLe)
    have callerBefore := (forward u caller n).previousBlockSlot_le_previousCurrentSlot
      (UInt64.le_of_eq anchorSlot) found slotOk beforeOk lastOk
    have receiverBefore := (forward w receiver k).previousBlockSlot_le_previousCurrentSlot
      (UInt64.le_of_eq anchorSlot) known currentOk beforeOk receiverLastOk
    have lastNat := (subChecked_ok_iff.mp lastOk).2
    have receiverLastNat := (subChecked_ok_iff.mp receiverLastOk).2
    have lastLe := (subChecked_ok_iff.mp lastOk).1
    have receiverLastLe := (subChecked_ok_iff.mp receiverLastOk).1
    simp only [UInt64.toNat_one] at lastNat receiverLastNat lastLe receiverLastLe
    have callerBeforeNat := UInt64.le_iff_toNat_le.mp callerBefore
    have receiverBeforeNat := UInt64.le_iff_toNat_le.mp receiverBefore
    have inWindow := (windows w receiver k receiverTime receiverHead current first beforeBlock
        participants receiverHeadOk currentOk (UInt64.lt_iff_toNat_lt.mpr (by omega))
        (fun headState headRead => by
          have := (forward w receiver k).forwardReachable.headState_epoch_le currentOk headRead
          rw [receiverEpochEq] at this
          omega)
        participantsOk v honest).mpr
      ((windows u caller n callerTime head slot first beforeBlock parentParticipants headOk
        slotOk (UInt64.lt_iff_toNat_lt.mpr (by omega))
        (fun headState headRead => by
          have := (forward u caller n).forwardReachable.headState_epoch_le slotOk headRead
          rw [callerEpochEq] at this
          omega)
        callerParticipantsOk v honest).mp inside)
    refine .inl (.inr (.inl (Store.mem_parentVotersOf.mpr ⟨inWindow,
      ⟨validator, validatorFound, unslashed, isActive⟩, notCounted, _, _, receivedOk,
      Store.getSupportedNode_of_lt preGloas, .inl isParent⟩)))
  -- A higher rank: every signed origin of the receiver's vote is from the caller's slot on.
  obtain ⟨due, dueOk⟩ := fits.1
  obtain ⟨voteTime, voteTimeOk, -, -⟩ := exists_timeAtSlotMs_of_le
    (slot := attestation.data.slot) (UInt64.le_iff_toNat_le.mpr (by omega)) nextTimeOk
  have dueLt := fits.due_lt_slot nextOk voteTimeOk nextTimeOk dueOk
  have rootAbove := (reached w receiver k).anchorSlot_le (UInt64.le_of_eq anchorSlot) known
  obtain ⟨parent', parentFound', historicalLe⟩ :=
    Store.slot_le_of_isAncestor historicalFound historicalBelow
  rw [parentFound, Option.some.injEq] at parentFound'
  subst parentFound'
  have voteAbove : (computeEpochAtSlot preset historicalBlock.slot).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat :=
    epoch_le_of_slot_le (preset := preset) _ _ (by
      have := UInt64.le_iff_toNat_le.mp historicalLe
      have := UInt64.le_iff_toNat_le.mp votedLe
      omega)
  have headHistorical : callerStore.isAncestor head ⟨historical, .pending⟩ = .ok true :=
    Store.isAncestor_trans_of_lt preGloas parentFound historicalFound
      (Store.isAncestor_trans_of_lt preGloas found parentFound headDescends
        (Store.isAncestor_pending_parent_of_slot_lt (node := ⟨root, .pending⟩) found parentFound
          parentBelow))
      historicalBelow
  rcases receiver_origins_fresh sync slots preGloas admitted votes fits prompt anchored sound
      anchorSlot anchorBoundary start chain nonzero absent caller honest callerTime
      callerUpToDate beginOk timeEq headOk historicalFound headHistorical callerEpochOk near
      epochStartOk epochStartTimeOk historyCovers latest origin.targetEpoch voteAbove greater
      (w := w) (k := k) with allFresh | collision
  swap
  · exact .inr collision
  rcases Execution.mem_supportersOf_of_latest_signed anchored start preGloas honest receiver
      receivedOk notCounted upToDate receiverTime dueOk dueLt allFresh
      (fun earlier low high => rootCovers earlier low (atTime ▸ high)) known rootAbove
      (List.mem_toFinset.mpr
        (mem_unslashedActiveBalances_of_found validatorFound isActive unslashed))
    with member | ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩
  · exact .inl (.inl member)
  · exact .inr ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩

/-- Validated duty votes give the honest votes of every slot range that ends by their horizon.

The range ends when its last slot does, and the votes of that slot are due before then. -/
public theorem ValidatedDutyVotes.votesInSlots {Δ last : ℕ}
    (votes : ValidatedDutyVotes (e := e) last) (fits : DelayFits fork config genesisTimeMs Δ)
    {begin next : Slot} {endTime : UInt64}
    (endTimeOk : computeTimeAtSlotMs config genesisTimeMs next = .ok endTime)
    (complete : endTime.toNat ≤ last) :
    VotesInSlots e begin next := by
  intro a honestA dutySlot committee deadline _ before assigned deadlineOk begun
  have nextFits : dutySlot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have lt := UInt64.lt_iff_toNat_lt.mp before
    have bound := next.toNat_lt
    simp only [UInt64.toNat_one]
    omega
  have nextOk := addChecked_of_lt nextFits
  have nextLe : dutySlot + 1 ≤ next := by
    have lt := UInt64.lt_iff_toNat_lt.mp before
    have value := (addChecked_ok_iff.mp nextOk).2
    rw [UInt64.le_iff_toNat_le, value]
    simp only [UInt64.toNat_one]
    omega
  obtain ⟨following, followingOk, _, followingLe⟩ :=
    exists_timeAtSlotMs_of_le nextLe endTimeOk
  obtain ⟨startTime, startOk, _, _⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt before) endTimeOk
  have dueBound := fits.before_boundary nextOk startOk followingOk deadlineOk
  apply votes a honestA dutySlot committee deadline assigned deadlineOk begun
  have followingLe := UInt64.le_iff_toNat_le.mp followingLe
  omega

/-- An honest member of the receiver's window from the caller's slot supports the root there.

Otherwise the receiver's justified block descends from the root, or bounded honest stores collide.

The window ends before the receiver's current slot, so its duties are due by the receiver's time.

They are after the caller's time, when honest heads descend from the root. -/
private theorem receiver_window_member_reaches {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ValidatedDutyVotes (e := e) time)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    (windows : AssignmentWindowAgreement (e := e) time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {w v : ValidatorIndex} (receiver : w ∈ J) (honest : v ∈ J) {n k : ℕ}
    {slot : Slot} {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    {root : Root} {block : BeaconBlock preset fork}
    (rootCovers : HonestHeadsCover (e := e) root (e.world n).time time)
    (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (genesisEq : ((e.world k).state w).genesisTimeMs = genesisTimeMs)
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finality : ReceiverFinalityCovers (e := e) w k root block)
    {receiverHead : ForkChoiceNode}
    (receiverHeadOk : ((e.world k).state w).getHead config = .ok receiverHead)
    {current finish : Slot}
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (finishLt : finish < current)
    (receiverNear : ∀ headState,
      ((e.world k).state w).blockState receiverHead.root = .ok headState →
      (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        (computeEpochAtSlot preset slot).toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {window : Std.TreeSet ValidatorIndex}
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root slot finish =
      .ok window)
    {source : BeaconState preset fork}
    (active : v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset)
    (member : v ∈ window) :
    (v ∈ ((e.world k).state w).supportersOf source ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) ∨
    HonestCollision (e := e) time := by
  -- The member has a duty in the window.
  obtain ⟨dutySlot, committee, low, high, assigned⟩ :=
    (windows w receiver k (le_of_eq atTime) receiverHead current slot finish window
      receiverHeadOk currentOk finishLt receiverNear windowOk v honest).mp member
  -- The slot after the window starts by the receiver's time.
  have finishNat := UInt64.lt_iff_toNat_lt.mp finishLt
  have nextFits : finish.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := current.toNat_lt
    simp only [UInt64.toNat_one]
    omega
  have nextOk := addChecked_of_lt nextFits
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  obtain ⟨endTime, endTimeOk, endLe⟩ := slotStart_le_clock genesisEq currentOk
    (target := finish + 1) (UInt64.le_iff_toNat_le.mpr (by omega))
  have started : e.startTime ≤ (e.world n).time := by
    have := e.monotone_time (Nat.zero_le n)
    simpa [Execution.world_zero, World.initial] using this
  have windowVotes := votes.votesInSlots fits (begin := slot) endTimeOk
    (by rw [upToDate.1, atTime] at endLe; exact endLe)
  exact e.mem_supportersOf_of_duty_interval_core sync slots preGloas admitted fits prompt
    anchored anchorSlot anchorBoundary start started chain nonzero windowVotes beginOk endTimeOk
    (le_of_eq timeEq) (by rw [← atTime, ← upToDate.1]; exact endLe) rootCovers receiver atTime
    upToDate known (fun k' le _ current => finality k' le current) honest active
    ⟨dutySlot, committee, low, UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.le_iff_toNat_le.mp high
      omega), assigned⟩

/-- The caller's head and the receiver's head read the same committees near the parent.

Both heads descend from the parent, whose state both stores hold alike.

Each slot of the range is at most one epoch after the parent.

So the parent state fixes its committees. -/
private theorem committee_reads_agree (preGloas : fork < .glamsterdam)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (agree : ∀ (r : Root) b c, ((e.world n).state u).blocks[r]? = some b →
      ((e.world k).state w).blocks[r]? = some c → b = c)
    {callerHead receiverHead parentRoot : Root} {parent : BeaconBlock preset fork}
    (callerParent : ((e.world n).state u).blocks[parentRoot]? = some parent)
    (receiverParent : ((e.world k).state w).blocks[parentRoot]? = some parent)
    (callerDescends : ((e.world n).state u).isAncestor ⟨callerHead, .pending⟩
      ⟨parentRoot, .pending⟩ = .ok true)
    (receiverDescends : ((e.world k).state w).isAncestor ⟨receiverHead, .pending⟩
      ⟨parentRoot, .pending⟩ = .ok true)
    {callerCurrent receiverCurrent : Slot}
    (callerCurrentOk : ((e.world n).state u).getCurrentSlot config = .ok callerCurrent)
    (receiverCurrentOk : ((e.world k).state w).getCurrentSlot config = .ok receiverCurrent)
    (callerNear : (computeEpochAtSlot preset callerCurrent).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 2)
    (receiverNear : (computeEpochAtSlot preset receiverCurrent).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 2)
    {first last : Slot} (above : parent.slot ≤ first)
    (lastNear : (computeEpochAtSlot preset last).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1) :
    ((e.world k).state w).getCommitteesBetweenSlots receiverHead first last =
      ((e.world n).state u).getCommitteesBetweenSlots callerHead first last := by
  have reached := fun a ha i => e.reachable
    (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) i a ha
  have forward := fun a ha i => e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored) i a ha
  -- Both stores hold one parent state, and a state for each head.
  obtain ⟨callerParentState, callerParentFound, -⟩ :=
    (reached u caller n).blockStatesFromParents callerParent
  obtain ⟨receiverParentState, receiverParentFound, -⟩ :=
    (reached w receiver k).blockStatesFromParents receiverParent
  have sameParent := e.blockStates_eq anchored (start u caller)
    (start w receiver) agree callerParentFound receiverParentFound
  subst sameParent
  obtain ⟨callerBlock, callerFound, -⟩ := Store.slot_le_of_isAncestor callerParent callerDescends
  obtain ⟨receiverBlock, receiverFound, -⟩ :=
    Store.slot_le_of_isAncestor receiverParent receiverDescends
  obtain ⟨callerState, callerStateFound, -⟩ :=
    (reached u caller n).blockStatesFromParents callerFound
  obtain ⟨receiverState, receiverStateFound, -⟩ :=
    (reached w receiver k).blockStatesFromParents receiverFound
  -- Each head state is at or before its store's current slot.
  have epochOf : ∀ (s : BeaconState preset fork) (current : Slot), s.slot ≤ current →
      (getCurrentEpoch s).toNat ≤ (computeEpochAtSlot preset current).toNat := by
    intro s current le
    exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp le)
  have callerEpoch := epochOf _ _ ((forward u caller n).slot_le_of_blockState_of_getCurrentSlot
    callerStateFound callerCurrentOk)
  have receiverEpoch := epochOf _ _
    ((forward w receiver k).slot_le_of_blockState_of_getCurrentSlot receiverStateFound
      receiverCurrentOk)
  refine Store.getCommitteesBetweenSlots_congr (Store.blockState_ok_iff.mpr callerStateFound)
    (Store.blockState_ok_iff.mpr receiverStateFound) fun slot low high => ?_
  have parentSlot := epoch_le_of_slot_le (preset := preset) parent.slot slot
    (UInt64.le_iff_toNat_le.mp (UInt64.le_trans above low))
  have slotLast := epoch_le_of_slot_le (preset := preset) slot last (UInt64.le_iff_toNat_le.mp high)
  exact committeesKept_of_parentState (reached u caller n) (reached w receiver k)
    (UInt64.le_of_eq anchorSlot) preGloas maxLookahead callerParent receiverParent
    callerParentFound receiverParentFound callerDescends receiverDescends callerStateFound
    receiverStateFound (by omega) minLookahead (by omega) (by omega)

/-- Honest stores follow the model's time of genesis once a caller holds an honest latest vote.

The vote is before the caller's slot, so its signer's duty vote has passed, on the model's clock.
-/
private theorem genesis_of_honest_latest {Δ time : ℕ}
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J) {n : ℕ}
    (callerTime : (e.world n).time ≤ time) {slot : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat) {message : LatestMessage fork}
    (latest : ((e.world n).state u).latestMessages[v]? = some message) (k : ℕ) :
    ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
  obtain ⟨attestation, signedIn, seen, -, signed, _, past⟩ :=
    signed_origin_before_slot anchored start caller latest slotOk
  obtain ⟨nextOk, nextTime, nextTimeOk, nextLeNat⟩ := successor_time_of_past past beginOk
  obtain ⟨_, _, _, _, _, _, n', _, _, _, vote, _⟩ := exists_dutyVote_of_signed votes fits honest
    (e.view_subset_sent n u seen) signed nextOk nextTimeOk (by omega)
  exact e.genesisTimeMs_eq_of_honest start honest vote.genesis receiver k

/-- On validators the source counts as unslashed and active, its counted weight is its balance. -/
private theorem stake_counted_eq {source : BeaconState preset fork}
    {S : Finset ValidatorIndex}
    (inside : ∀ v ∈ S, v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset) :
    Models.stake (fun v =>
        if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
        then balanceAt source v.toNat else 0) S =
      Models.stake (fun v => balanceAt source v.toNat) S :=
  Finset.sum_congr rfl fun v member => by simp only [inside v member, ↓reduceIte]

/-- A caller supporter of a block does not vote for the block's parent. -/
private theorem not_parentVoter_of_supporter {store : Store preset fork}
    (preGloas : fork < .glamsterdam) {root : Root} {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) {source : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {v : ValidatorIndex}
    (supporter : v ∈ store.supportersOf source ⟨root, .pending⟩)
    (voter : v ∈ store.parentVotersOf source participants block parent) : False := by
  obtain ⟨message, supported, latest, -, supportedOk, descends⟩ :=
    store.exists_of_voteCountsFor (Store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨-, -, -, message', supported', latest', supportedOk', isParent⟩ :=
    Store.mem_parentVotersOf.mp voter
  rw [latest, Option.some.injEq] at latest'
  subst latest'
  rw [supportedOk, Except.ok.injEq] at supportedOk'
  subst supportedOk'
  rw [Store.parentPayloadStatus_of_lt preGloas, or_self] at isParent
  subst isParent
  obtain ⟨parent', parentFound', above⟩ := Store.slot_le_of_isAncestor found descends
  rw [parentFound, Option.some.injEq] at parentFound'
  subst parentFound'
  exact absurd (UInt64.lt_of_lt_of_le lower above) (UInt64.lt_irrefl _)

/-- The reserves and the weight bound of the source surplus, from the reads of both heads.

The exit reserve enters only when the receiver's first epochs run past the caller's window.

Then the reserve set is the adversary range with the new members, one window of the caller.

Otherwise the receiver's first epochs lie in the caller's window.

Then the receiver's weight is at most the caller's. -/
private theorem window_reserves_and_weight [DecidablePred (· ∈ J)] {n : ℕ}
    {source : BeaconState preset fork} {u : ValidatorIndex} {callerHead : Root}
    {receiverStore : Store preset fork} {receiverHead : Root}
    {first last slot startSlot finish receiverLast current : Slot} {exitAllowance : ℕ}
    (reserve : SourceWindowReserveWith (J := J) (config := config) ((e.world n).state u)
      callerHead source first receiverLast exitAllowance)
    {maximum sourceMaximum : Gwei}
    {advParticipants wcParticipants xParticipants members : Std.TreeSet ValidatorIndex}
    (slotNext : addChecked last 1 = .ok slot)
    (currentNext : addChecked receiverLast 1 = .ok current)
    (nonempty : first ≤ last) (firstStart : first ≤ startSlot) (lastLe : last ≤ receiverLast)
    (startCases : startSlot ≤ last ∨ Store.activeMembers source advParticipants = ∅)
    (finishLe : finish ≤ receiverLast)
    (advOk : ((e.world n).state u).getCommitteesBetweenSlots callerHead startSlot last =
      .ok advParticipants)
    (wcCaller : ((e.world n).state u).getCommitteesBetweenSlots callerHead first last =
      .ok wcParticipants)
    (xCaller : ((e.world n).state u).getCommitteesBetweenSlots callerHead slot finish =
      .ok xParticipants)
    (wcReceiver : receiverStore.getCommitteesBetweenSlots receiverHead first last =
      .ok wcParticipants)
    (xReceiver : receiverStore.getCommitteesBetweenSlots receiverHead slot finish =
      .ok xParticipants)
    (membersOk : receiverStore.getCommitteesBetweenSlots receiverHead first finish = .ok members)
    (vRead : startSlot ≤ last → last < finish → ∃ vParticipants,
      ((e.world n).state u).getCommitteesBetweenSlots callerHead startSlot finish =
        .ok vParticipants)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots callerHead source first
      last = .ok maximum)
    (sourceMaximumOk : receiverStore.computeCommitteeWeightBetweenSlots receiverHead source first
      receiverLast = .ok sourceMaximum)
    (weightCases : sourceMaximum.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members)) ∨
      isFullValidatorSetCovered preset first finish = .ok true ∧
      sourceMaximum.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members)) +
      exitAllowance) :
    ∃ X,
      (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source advParticipants) = 0 ∨
        100 * stake (fun v => balanceAt source v.toNat)
            {v ∈ Store.activeMembers source advParticipants | v ∉ J} + 50 * X ≤
          config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
            stake (fun v => balanceAt source v.toNat)
              (Store.activeMembers source advParticipants)) ∧
      100 * stake (fun v => balanceAt source v.toNat)
          {v ∈ Store.activeMembers source advParticipants ∪
            Store.activeMembers source xParticipants | v ∉ J} + 50 * X ≤
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake (fun v => balanceAt source v.toNat)
          (Store.activeMembers source advParticipants ∪
            Store.activeMembers source xParticipants) ∧
      sourceMaximum.toNat +
            stake (fun v => balanceAt source v.toNat) (Store.activeMembers source wcParticipants) ≤
          maximum.toNat + stake (fun v => balanceAt source v.toNat)
            (Store.activeMembers source wcParticipants ∪
              Store.activeMembers source xParticipants) + X := by
  have slotNat := (addChecked_ok_iff.mp slotNext).2
  simp only [UInt64.toNat_one] at slotNat
  have firstSlot : first ≤ slot := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.le_iff_toNat_le.mp nonempty
    omega)
  -- The caller's window weighs at least its members and one increment.
  have wcLe := Store.stake_le_computeCommitteeWeightBetweenSlots wcCaller maximumOk
    (W := Store.activeMembers source wcParticipants)
    fun v member => Store.mem_activeMembers.mp member
  have incrementLe := increment_le_weight nonempty maximumOk
  have wcUnion := stake_mono (w := fun v => balanceAt source v.toNat)
    (Finset.subset_union_left (s₁ := Store.activeMembers source wcParticipants)
      (s₂ := Store.activeMembers source xParticipants))
  by_cases longer : last < finish
  · -- The reserve set runs from the adversary range through the new members.
    have reserveV : 100 * stake (fun v => balanceAt source v.toNat)
          {v ∈ Store.activeMembers source advParticipants ∪
            Store.activeMembers source xParticipants | v ∉ J} + 50 * exitAllowance ≤
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
          stake (fun v => balanceAt source v.toNat)
            (Store.activeMembers source advParticipants ∪
              Store.activeMembers source xParticipants) := by
      rcases startCases with ordered | empty
      · obtain ⟨vParticipants, vCaller⟩ := vRead ordered longer
        have vEq : Store.activeMembers source vParticipants =
            Store.activeMembers source advParticipants ∪
              Store.activeMembers source xParticipants := by
          ext v
          simp only [Finset.mem_union, Store.mem_activeMembers,
            mem_window_split vCaller advOk xCaller slotNext (UInt64.le_of_lt longer)
              (UInt64.le_trans ordered (UInt64.le_iff_toNat_le.mpr (by omega)))]
          exact or_and_right
        rw [← vEq]
        exact reserve startSlot finish vParticipants firstStart
          (UInt64.le_trans ordered (UInt64.le_of_lt longer)) finishLe vCaller
      · rw [empty, Finset.empty_union]
        exact reserve slot finish xParticipants firstSlot
          (UInt64.le_iff_toNat_le.mpr (by
            have := UInt64.lt_iff_toNat_lt.mp longer
            omega)) finishLe xCaller
    -- The receiver's first epochs are the caller's window and the new members.
    have membersIn : Store.activeMembers source members ⊆
        Store.activeMembers source wcParticipants ∪ Store.activeMembers source xParticipants := by
      intro v member
      obtain ⟨inMembers, active⟩ := Store.mem_activeMembers.mp member
      rcases (mem_window_split membersOk wcReceiver xReceiver slotNext (UInt64.le_of_lt longer)
        firstSlot v).mp inMembers with left | right
      · exact Finset.mem_union_left _ (Store.mem_activeMembers.mpr ⟨left, active⟩)
      · exact Finset.mem_union_right _ (Store.mem_activeMembers.mpr ⟨right, active⟩)
    have membersLe := stake_mono (w := fun v => balanceAt source v.toNat) membersIn
    have weightLe : sourceMaximum.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members)) +
        exitAllowance := by
      rcases weightCases with bound | ⟨-, bound⟩ <;> omega
    refine ⟨exitAllowance, ?_, reserveV, ?_⟩
    · rcases startCases with ordered | empty
      · exact .inr (reserve startSlot last advParticipants firstStart ordered lastLe advOk)
      · left
        simp [empty]
    · rcases Nat.le_total preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members)) with
        large | small
      · rw [Nat.max_eq_right large] at weightLe
        omega
      · rw [Nat.max_eq_left small] at weightLe
        omega
  · -- No new members: the receiver's first epochs lie in the caller's window.
    have finishLast : finish ≤ last := UInt64.not_lt.mp longer
    have xEmpty : Store.activeMembers source xParticipants = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v member => ?_
      obtain ⟨s, low, high, -⟩ :=
        (Store.mem_getCommitteesBetweenSlots_iff xCaller v).mp
          (Store.mem_activeMembers.mp member).1
      have := UInt64.le_iff_toNat_le.mp low
      have := UInt64.le_iff_toNat_le.mp high
      have := UInt64.le_iff_toNat_le.mp finishLast
      omega
    have advByzantine : 100 * stake (fun v => balanceAt source v.toNat)
          {v ∈ Store.activeMembers source advParticipants | v ∉ J} ≤
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
          stake (fun v => balanceAt source v.toNat)
            (Store.activeMembers source advParticipants) := by
      rcases startCases with ordered | empty
      · have := reserve startSlot last advParticipants firstStart ordered lastLe advOk
        omega
      · simp [empty]
    refine ⟨0, .inr (by omega), by rw [xEmpty, Finset.union_empty]; omega, ?_⟩
    rcases weightCases with bound | ⟨covered, -⟩
    · have membersIn := activeMembers_mono_of_window (source := source) membersOk wcReceiver
        (UInt64.le_refl first) finishLast
      have membersLe := stake_mono (w := fun v => balanceAt source v.toNat) membersIn
      rcases Nat.le_total preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (stake (fun v => balanceAt source v.toNat) (Store.activeMembers source members)) with
        large | small
      · rw [Nat.max_eq_right large] at bound
        omega
      · rw [Nat.max_eq_left small] at bound
        omega
    · -- Both windows cover a whole epoch, so both weigh the source's total active balance.
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered
        (covered_of_le covered finishLast slotNext)] at maximumOk
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered
        (covered_of_le covered finishLe currentNext)] at sourceMaximumOk
      have same : sourceMaximum = maximum := Except.ok.inj (sourceMaximumOk.symm.trans maximumOk)
      subst same
      omega

/-- A caller's guarded margin gives a receiver its own source surplus, at any one reserve value.

The caller's window reserve and the receiver's exit bound read one reserve value.

The receiver's justified block may instead descend from the block.

Bounded honest stores may instead collide, or `HistoricalDirectSafetyEvidence` holds. -/
public theorem Execution.source_surplus_or_historical_evidence_with [DecidablePred (· ∈ J)]
    {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {block parent : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {boost maximum : Gwei}
    (headNode : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    {checkpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    (boostOk : computeProposerScore config source = .ok boost)
    (firstOk : addChecked parent.slot 1 = .ok first) (lastOk : subChecked slot 1 = .ok last)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head first
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei} (registry : source.RegistryWithinLimit)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head source root =
      .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head source root =
      .ok adversary)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (callerTime : (e.world n).time ≤ time) (sourceReads : SourceWindowReads (e := e) n time source)
    {receiverLast : Slot} {exitAllowance : ℕ}
    (reserve : SourceWindowReserveWith (J := J) (config := config) ((e.world n).state u) head
      source first receiverLast exitAllowance) {horizon : Epoch}
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (rootCovers : HonestHeadsCover (e := e) root (e.world n).time time)
    (headDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (near : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finality : ReceiverFinalityCovers (e := e) w k root block)
    {receiverHead : ForkChoiceNode} {state : BeaconState preset fork}
    {current : Slot} {receiverEpoch : Epoch}
    {window participants : Std.TreeSet ValidatorIndex}
    (receiverHeadOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (receiverParent : ((e.world k).state w).isAncestor receiverHead
      ⟨block.parentRoot, .pending⟩ = .ok true)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (receiverNear : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (receiverLastOk : subChecked current 1 = .ok receiverLast)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      receiverLast = .ok window)
    (participantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      beforeBlock = .ok participants)
    (exit : WindowExitBoundWith ((e.world k).state w) source receiverHead.root first receiverLast
      exitAllowance)
    (absent : AnchorParentAbsent (e := e) time) :
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (∃ receiverMaximum sourceMaximum sourceScore,
        ((e.world k).state w).computeCommitteeWeightBetweenSlots receiverHead.root state
          first receiverLast = .ok receiverMaximum ∧
        ((e.world k).state w).computeCommitteeWeightBetweenSlots receiverHead.root source
          first receiverLast = .ok sourceMaximum ∧
        computeProposerScore config source = .ok sourceScore ∧
        sourceMaximum.toNat + sourceScore.toNat + shift <
          2 * Models.stake (fun v =>
            if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
            then balanceAt source v.toNat else 0)
            {v ∈ ((e.world k).state w).supportersOf source ⟨root, .pending⟩ | v ∈ J} +
          Models.stake (fun v =>
            if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
            then balanceAt source v.toNat else 0)
            {v ∈ ((e.world k).state w).parentVotersOf source participants block parent |
              v ∈ J}) ∨
      HonestCollision (e := e) time ∨ HistoricalDirectSafetyEvidence (e := e) pre time := by
  classical
  set callerStore := (e.world n).state u
  set receiverStore := (e.world k).state w
  -- The finalized prefixes form one family, or the runs from the anchor give evidence.
  rcases e.finalizedFamily_or_historical_evidence anchored start sound anchorSlot anchorBoundary
      slots bounded roots absent parameters genesis pre heldEarly enough terminal caller
      callerTime with family | evidence
  swap
  · exact .inr (.inr (.inr evidence))
  -- Bounded honest stores agree on blocks, or two of them collide.
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agree | collision
  swap
  · obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, evidence, searched⟩ := collision
    exact .inr (.inr (.inl ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩))
  have receiverTime : (e.world k).time ≤ time := le_of_eq atTime
  have callerReceiver := agree (u, n) ⟨caller, callerTime⟩ (w, k) ⟨receiver, receiverTime⟩
  have reached := fun a ha i => e.reachable
    (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) i a ha
  have forward := fun a ha i => e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) i a ha
  obtain ⟨callerHead, headOk, rfl⟩ := headNode
  have found := Store.block_ok_iff.mp blockOk
  have parentFound := Store.block_ok_iff.mp parentOk
  have callerAbsent := absent u caller n callerTime
  have parentBelow := (reached u caller n).parentsBelow (UInt64.le_of_eq anchorSlot) callerAbsent
    root block parent found parentFound
  -- The caller's window is nonempty.
  have nonempty := first_le_last_of_margin (UInt64.le_of_eq anchorSlot) (forward u caller n)
    callerAbsent slotOk blockOk parentOk firstOk lastOk supportOk discountOk margin
  -- The receiver reads its full maximum, then the source maximum and score.
  rcases receiver_fullMaximum_of_head_window anchored start sound anchorSlot anchorBoundary
      positive preGloas ceiling absent caller receiver callerTime receiverTime
      (family w receiver k k le_rfl receiverTime) parentOk receiverParent firstOk receiverHeadOk
      stateOk receiverLastOk windowOk nonempty maximumOk with
    ⟨receiverMaximum, receiverMaximumOk⟩ | collision
  swap
  · exact .inr (.inr (.inl collision))
  obtain ⟨receiverLastLe, receiverLastNat⟩ := subChecked_ok_iff.mp receiverLastOk
  obtain ⟨lastLe, lastNat⟩ := subChecked_ok_iff.mp lastOk
  obtain ⟨-, firstNat⟩ := addChecked_ok_iff.mp firstOk
  simp only [UInt64.toNat_one] at receiverLastLe receiverLastNat lastLe lastNat firstNat
  have finishLt : receiverLast < current := UInt64.lt_iff_toNat_lt.mpr (by omega)
  obtain ⟨sourceMaximum, sourceScore, sourceMaximumOk, sourceScoreOk⟩ :=
    sourceReads w receiver k receiverHead state current first receiverLast receiverMaximum
      (by rw [atTime]; exact callerTime) receiverTime receiverHeadOk currentOk finishLt stateOk
      receiverMaximumOk
  have scoreEq : sourceScore = boost := Except.ok.inj (sourceScoreOk.symm.trans boostOk)
  subst scoreEq
  -- Each remaining alternative is a disjunct of the conclusion.
  by_cases alternative : receiverStore.isAncestor
      ⟨receiverStore.justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
    HonestCollision (e := e) time
  · rcases alternative with justified | collision
    · exact .inl justified
    · exact .inr (.inr (.inl collision))
  obtain ⟨notJustified, notCollision⟩ := not_or.mp alternative
  refine .inr (.inl ⟨receiverMaximum, sourceMaximum, sourceScore, receiverMaximumOk,
    sourceMaximumOk, sourceScoreOk, ?_⟩)
  -- Results with an alternative reduce to their main part.
  have main : ∀ {X : Prop}, (X ∨ receiverStore.isAncestor
      ⟨receiverStore.justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true) ∨
      HonestCollision (e := e) time → X :=
    fun result => (result.resolve_right notCollision).resolve_right notJustified
  -- Epochs: the caller is at most one epoch after the parent, the receiver at most two.
  obtain ⟨historicalBlock, historicalBlockOk, historicalEq⟩ :
      ∃ b, callerStore.block historical = .ok b ∧
        computeEpochAtSlot preset b.slot = historicalEpoch := by
    simp only [Store.getBlockEpoch, bind_ok_iff, pure, Except.pure, Except.ok.injEq]
      at historicalEpochOk
    exact historicalEpochOk
  have historicalFound := Store.block_ok_iff.mp historicalBlockOk
  obtain ⟨parent', parentFound', historicalLe⟩ :=
    Store.slot_le_of_isAncestor historicalFound historicalBelow
  rw [parentFound, Option.some.injEq] at parentFound'
  subst parentFound'
  have callerEpochEq : computeEpochAtSlot preset slot = callerEpoch := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
      using callerEpochOk
  have receiverEpochEq : computeEpochAtSlot preset current = receiverEpoch := by
    simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
      using receiverEpochOk
  have historicalParent := epoch_le_of_slot_le (preset := preset) _ _
    (UInt64.le_iff_toNat_le.mp historicalLe)
  have callerNear : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1 := by
    rw [callerEpochEq]
    rw [← historicalEq] at near
    omega
  have historicalNear : callerEpoch.toNat ≤
      (computeEpochAtSlot preset historicalBlock.slot).toNat + 1 := historicalEq ▸ near
  -- Slot order: the caller's last slot is no later than the receiver's.
  have lastBefore := Execution.previousSlot_le_of_time_le start caller receiver
    (by rw [atTime]; exact callerTime) upToDate slotOk currentOk lastOk receiverLastOk
  have lastBeforeNat := UInt64.le_iff_toNat_le.mp lastBefore
  have beforeLast := (forward u caller n).previousBlockSlot_le_previousCurrentSlot
    (UInt64.le_of_eq anchorSlot) found slotOk beforeOk lastOk
  have parentBelowNat := UInt64.lt_iff_toNat_lt.mp parentBelow
  -- The receiver holds the parent, below both heads.
  have receiverParentFound : receiverStore.blocks[block.parentRoot]? = some parent := by
    have test := receiverParent
    unfold Store.isAncestor at test
    simp only [bind_ok_iff] at test
    obtain ⟨held, heldOk, _⟩ := test
    have heldFound := Store.block_ok_iff.mp heldOk
    exact (callerReceiver block.parentRoot parent held parentFound heldFound) ▸ heldFound
  have rootParent := Store.isAncestor_pending_parent_of_slot_lt (node := ⟨root, .pending⟩)
    found parentFound parentBelow
  have callerHeadPending := Store.getHead_pending preGloas headOk
  have callerHeadEq : (⟨callerHead.root, .pending⟩ : ForkChoiceNode) = callerHead := by
    rw [← callerHeadPending]
  have receiverHeadEq : (⟨receiverHead.root, .pending⟩ : ForkChoiceNode) = receiverHead := by
    rw [← Store.getHead_pending preGloas receiverHeadOk]
  have callerDescends := Store.isAncestor_trans_of_lt preGloas found parentFound headDescends
    rootParent
  have agreeReads := fun {a b : Slot} (above : parent.slot ≤ a)
      (endNear : (computeEpochAtSlot preset b).toNat ≤
        (computeEpochAtSlot preset parent.slot).toNat + 1) =>
    committee_reads_agree preGloas minLookahead maxLookahead ring anchored anchorSlot
      start caller receiver callerReceiver parentFound receiverParentFound callerDescends
      (receiverHeadEq ▸ receiverParent) slotOk currentOk (by omega)
      (by rw [receiverEpochEq]; exact receiverNear) above endNear
  -- The receiver's window reads every window inside it, as the caller does near the parent.
  have firstAbove : parent.slot ≤ first := UInt64.le_iff_toNat_le.mpr (by omega)
  have inside := fun {a b : Slot} (low : first ≤ a) (high : b ≤ receiverLast) =>
    window_ok_of_inside windowOk low high
  have slotNext : addChecked last 1 = .ok slot :=
    (addChecked_ok_iff.mpr ⟨by have := slot.toNat_lt; simp only [UInt64.toNat_one]; omega,
      by simp only [UInt64.toNat_one]; omega⟩)
  -- The caller's window, read by both heads.
  obtain ⟨wcParticipants, wcReceiver, -⟩ :=
    inside (UInt64.le_refl first) lastBefore
  have wcCaller : callerStore.getCommitteesBetweenSlots callerHead.root first last =
      .ok wcParticipants := by
    rw [← agreeReads firstAbove (by
      have := epoch_le_of_slot_le (preset := preset) last slot (by omega)
      omega)]
    exact wcReceiver
  -- The caller's reads, in sets.
  obtain ⟨startSlot, advParticipants, I, firstStart, startCases, advOk, supportEq, supIn,
    equivocatorsIn, equivocators, apart, cover⟩ :=
    caller_margin_sets (UInt64.le_of_eq anchorSlot) (forward u caller n) callerAbsent preGloas
      minLookahead maxLookahead ring slotOk blockOk parentOk firstOk lastOk
      (callerHeadEq ▸ headDescends) callerNear registry aligned increment supportOk adversaryOk
  have anchorEmpty := Store.getForkchoiceStore_equivocatingIndices anchored
  have equivocatorsDishonest : ∀ v ∈ I, v ∉ J := fun v member =>
    e.equivocatingIndices_honest slots
      (fun a ha b hb => by simp [start a ha, anchorEmpty] at hb) n caller v (equivocators v member)
  -- The Byzantine stake of a caller window is within its share.
  have byzantineOf : ∀ {low high : Slot} {A : Std.TreeSet ValidatorIndex},
      first ≤ low → high ≤ receiverLast →
      callerStore.getCommitteesBetweenSlots callerHead.root low high = .ok A →
      (low ≤ high ∨ Store.activeMembers source A = ∅) →
      100 * stake (fun v => balanceAt source v.toNat) {v ∈ Store.activeMembers source A | v ∉ J} ≤
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
          stake (fun v => balanceAt source v.toNat) (Store.activeMembers source A) := by
    intro low high A lowLe highLe read cases
    rcases cases with ordered | empty
    · have := reserve low high A lowLe ordered highLe read
      omega
    · simp [empty]
  -- The caller's discount is at most its honest parent voters.
  have discountHonest := Store.le_honest_parentVotersOf_of_computeEmptySlotSupportDiscount
    (J := J) blockOk parentOk firstOk beforeOk parentParticipantsOk discountOk aligned increment
    (fun v member => e.equivocatingIndices_honest slots
      (fun a ha b hb => by simp [start a ha, anchorEmpty] at hb) n caller v member)
    ⟨by norm_num, byzantineOf (UInt64.le_refl first) (UInt64.le_trans beforeLast lastBefore)
      parentParticipantsOk (by
      by_cases ordered : first ≤ beforeBlock
      · exact .inl ordered
      · right
        rw [Store.getCommitteesBetweenSlots_of_gt (UInt64.not_le.mp ordered),
          Except.ok.injEq] at parentParticipantsOk
        subst parentParticipantsOk
        rfl)⟩
  -- The receiver's window weighs at most its first epochs, with the exit reserve if covered.
  obtain ⟨finish, members, finishLe, finishNear, membersOk, weightCases⟩ :=
    window_weight_le positive firstOk windowOk sourceMaximumOk exit
  have slotAbove : first ≤ slot := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.le_iff_toNat_le.mp nonempty
    omega)
  have parentSlotLe : parent.slot ≤ slot := UInt64.le_trans firstAbove slotAbove
  -- The new members of the receiver's window, read by both heads.
  obtain ⟨xParticipants, xReceiver, -⟩ := inside slotAbove finishLe
  have xCaller : callerStore.getCommitteesBetweenSlots callerHead.root slot finish =
      .ok xParticipants := by
    rw [← agreeReads parentSlotLe finishNear]
    exact xReceiver
  -- Honest caller supporters support the root at the receiver.
  have supportersReach : {v ∈ callerStore.supportersOf source ⟨root, .pending⟩ | v ∈ J} ⊆
      {v ∈ receiverStore.supportersOf source ⟨root, .pending⟩ | v ∈ J} := by
    intro v member
    obtain ⟨supporter, honest⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨main (caller_supporter_reaches sync slots preGloas admitted
      votes fits prompt anchored sound anchorSlot anchorBoundary start family roots absent caller
      receiver honest callerTime callerUpToDate slotOk beginOk timeEq headOk found parentFound
      (callerHeadEq ▸ headDescends) historicalFound historicalBelow callerEpochOk historicalNear
      epochStartOk epochStartTimeOk historyCovers rootCovers atTime upToDate known finality
      supporter), honest⟩
  -- Honest caller parent voters support the root or vote for the parent at the receiver.
  have parentReach :
      {v ∈ callerStore.parentVotersOf source parentParticipants block parent | v ∈ J} ⊆
        {v ∈ receiverStore.supportersOf source ⟨root, .pending⟩ | v ∈ J} ∪
          {v ∈ receiverStore.parentVotersOf source participants block parent | v ∈ J} := by
    intro v member
    obtain ⟨voter, honest⟩ := Finset.mem_filter.mp member
    rcases caller_parent_voter_reaches sync slots preGloas ring admitted votes fits prompt windows
        anchored sound anchorSlot anchorBoundary start family roots absent caller receiver honest
        callerTime callerUpToDate slotOk lastOk beginOk timeEq headOk found parentFound
        (callerHeadEq ▸ headDescends) historicalFound historicalBelow callerEpochOk historicalNear
        epochStartOk epochStartTimeOk historyCovers rootCovers atTime upToDate known finality
        receiverHeadOk receiverParent currentOk receiverEpochOk receiverNear receiverLastOk
        firstOk beforeOk parentParticipantsOk participantsOk voter with
      (supporter | parentVoter | justified) | collision
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨supporter, honest⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨parentVoter, honest⟩)
    · exact absurd justified notJustified
    · exact absurd collision notCollision
  -- A caller supporter is no parent voter.
  have callerApart : Disjoint {v ∈ callerStore.supportersOf source ⟨root, .pending⟩ | v ∈ J}
      {v ∈ callerStore.parentVotersOf source parentParticipants block parent | v ∈ J} :=
    Finset.disjoint_left.mpr fun v supporter voter =>
      not_parentVoter_of_supporter preGloas found parentFound parentBelow
        (Finset.mem_filter.mp supporter).1 (Finset.mem_filter.mp voter).1
  have advIn := activeMembers_mono_of_window (source := source) advOk wcCaller firstStart
    (UInt64.le_refl last)
  have parentIn :
      {v ∈ callerStore.parentVotersOf source parentParticipants block parent | v ∈ J} ⊆
        Store.activeMembers source wcParticipants := by
    intro v member
    obtain ⟨inside, ⟨validator, validatorFound, -, active⟩, -⟩ :=
      Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1
    exact activeMembers_mono_of_window parentParticipantsOk wcCaller (UInt64.le_refl first)
      beforeLast (Store.mem_activeMembers.mpr ⟨inside, validator, validatorFound, active⟩)
  -- The reserves and the weight, with the exit reserve only when the receiver's window is longer.
  have currentNext : addChecked receiverLast 1 = .ok current :=
    addChecked_ok_iff.mpr ⟨by have := current.toNat_lt; simp only [UInt64.toNat_one]; omega,
      by simp only [UInt64.toNat_one]; omega⟩
  obtain ⟨X, reserveAdv, reserveV, weight⟩ := window_reserves_and_weight reserve
    slotNext currentNext nonempty firstStart lastBefore startCases finishLe advOk wcCaller xCaller
    wcReceiver xReceiver membersOk
    (fun ordered _ => by
      obtain ⟨vParticipants, vReceiver, -⟩ := inside firstStart finishLe
      exact ⟨vParticipants, (agreeReads (UInt64.le_trans firstAbove firstStart) finishNear) ▸
        vReceiver⟩)
    maximumOk sourceMaximumOk weightCases
  -- An honest vote at the caller fixes the model's time of genesis for honest stores.
  have genesisEq : receiverStore.genesisTimeMs = genesisTimeMs := by
    rcases honest_vote_of_margin (J := J) (w := fun v => balanceAt source v.toNat)
        (by rw [← supportEq]; exact margin) supIn equivocatorsIn apart equivocatorsDishonest cover
        discountHonest (by
          rcases startCases with ordered | empty
          · exact .inr (byzantineOf firstStart lastBefore advOk (.inl ordered))
          · left
            simp [empty]) with ⟨v, supporter, honest⟩ | ⟨v, voter⟩
    · obtain ⟨message, -, latest, -⟩ :=
        callerStore.exists_of_voteCountsFor (Store.voteCountsFor_of_mem_supportersOf supporter)
      exact genesis_of_honest_latest votes fits anchored start caller receiver honest callerTime
        slotOk beginOk timeEq latest k
    · obtain ⟨voterIn, honest⟩ := Finset.mem_filter.mp voter
      obtain ⟨-, -, -, message, -, latest, -⟩ := Store.mem_parentVotersOf.mp voterIn
      exact genesis_of_honest_latest votes fits anchored start caller receiver honest callerTime
        slotOk beginOk timeEq latest k
  -- Honest new members of the receiver's window support the root there.
  have newReach : {v ∈ Store.activeMembers source xParticipants \
      Store.activeMembers source advParticipants | v ∈ J} ⊆
        {v ∈ receiverStore.supportersOf source ⟨root, .pending⟩ | v ∈ J} := by
    intro v member
    obtain ⟨inX, honest⟩ := Finset.mem_filter.mp member
    have inXm := (Finset.mem_sdiff.mp inX).1
    have active := honest_unslashedActive_of_checkpointState unslashed anchored start caller
      callerTime sourceOk honest inXm
    have receiverRing : ∀ headState,
        receiverStore.blockState receiverHead.root = .ok headState →
        (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
          (computeEpochAtSlot preset slot).toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := by
      intro headState headRead
      have := (forward w receiver k).forwardReachable.headState_epoch_le currentOk headRead
      rw [receiverEpochEq] at this
      have := epoch_le_of_slot_le (preset := preset) parent.slot slot
        (UInt64.le_iff_toNat_le.mp parentSlotLe)
      omega
    exact Finset.mem_filter.mpr ⟨main (receiver_window_member_reaches sync slots preGloas
      admitted votes fits prompt windows anchored anchorSlot anchorBoundary start family roots
      receiver honest beginOk timeEq rootCovers atTime upToDate genesisEq known finality
      receiverHeadOk currentOk (UInt64.lt_of_le_of_lt finishLe finishLt) receiverRing xReceiver
      active (Store.mem_activeMembers.mp inXm).1), honest⟩
  -- The caller's surplus moves to the receiver's sets.
  have surplus := source_surplus_of_sets (J := J) (w := fun v => balanceAt source v.toNat) half
    (by rw [← supportEq]; exact margin) supIn equivocatorsIn apart equivocatorsDishonest cover
    discountHonest reserveAdv reserveV advIn parentIn weight supportersReach parentReach newReach
    callerApart
  rw [stake_counted_eq fun v member => active_of_mem_supportersOf (Finset.mem_filter.mp member).1,
    stake_counted_eq fun v member => by
      obtain ⟨-, ⟨validator, validatorFound, unslashedV, activeV⟩, -⟩ :=
        Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1
      exact List.mem_toFinset.mpr
        (mem_unslashedActiveBalances_of_found validatorFound activeV unslashedV)]
  exact surplus

/-- A caller's guarded margin for a block gives a receiver its own source surplus.

The receiver's justified block may instead descend from the block.

Bounded honest stores may instead collide.

Two runs from the anchor may instead give direct-safety evidence.

That evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key.

The stake ceiling of `2 * 10^17` Gwei is `2 * 10^8` ETH, above mainnet's active stake.

The ceiling serves only to keep the checked total below `2^64` Gwei. -/
public theorem Execution.source_surplus_or_historical_evidence [DecidablePred (· ∈ J)] {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {block parent : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {boost maximum : Gwei}
    (headNode : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    {checkpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    (boostOk : computeProposerScore config source = .ok boost)
    (firstOk : addChecked parent.slot 1 = .ok first) (lastOk : subChecked slot 1 = .ok last)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head first
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei} (registry : source.RegistryWithinLimit)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head source root =
      .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head source root =
      .ok adversary)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (callerTime : (e.world n).time ≤ time) (sourceReads : SourceWindowReads (e := e) n time source)
    {receiverLast : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first receiverLast) {horizon : Epoch}
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (rootCovers : HonestHeadsCover (e := e) root (e.world n).time time)
    (headDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (near : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finality : ReceiverFinalityCovers (e := e) w k root block)
    {receiverHead : ForkChoiceNode} {state : BeaconState preset fork}
    {current : Slot} {receiverEpoch : Epoch}
    {window participants : Std.TreeSet ValidatorIndex}
    (receiverHeadOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (receiverParent : ((e.world k).state w).isAncestor receiverHead
      ⟨block.parentRoot, .pending⟩ = .ok true)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (receiverNear : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (receiverLastOk : subChecked current 1 = .ok receiverLast)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      receiverLast = .ok window)
    (participantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      beforeBlock = .ok participants)
    (exit : WindowExitBound (config := config) ((e.world k).state w) source receiverHead.root
      first receiverLast)
    (absent : AnchorParentAbsent (e := e) time) :
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (∃ receiverMaximum sourceMaximum sourceScore,
        ((e.world k).state w).computeCommitteeWeightBetweenSlots receiverHead.root state
          first receiverLast = .ok receiverMaximum ∧
        ((e.world k).state w).computeCommitteeWeightBetweenSlots receiverHead.root source
          first receiverLast = .ok sourceMaximum ∧
        computeProposerScore config source = .ok sourceScore ∧
        sourceMaximum.toNat + sourceScore.toNat + shift <
          2 * Models.stake (fun v =>
            if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
            then balanceAt source v.toNat else 0)
            {v ∈ ((e.world k).state w).supportersOf source ⟨root, .pending⟩ | v ∈ J} +
          Models.stake (fun v =>
            if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
            then balanceAt source v.toNat else 0)
            {v ∈ ((e.world k).state w).parentVotersOf source participants block parent |
              v ∈ J}) ∨
      HonestCollision (e := e) time ∨ HistoricalDirectSafetyEvidence (e := e) pre time := by
  exact e.source_surplus_or_historical_evidence_with sync slots positive minLookahead maxLookahead
    ring preGloas admitted half votes fits prompt windows anchored sound anchorSlot anchorBoundary
    start caller callerUpToDate headNode slotOk beginOk timeEq blockOk parentOk sourceOk boostOk
    firstOk lastOk beforeOk maximumOk parentParticipantsOk registry aligned increment supportOk
    discountOk adversaryOk margin callerTime sourceReads reserve bounded roots unslashed ceiling
    parameters genesis pre heldEarly enough terminal rootCovers headDescends historicalBelow
    callerEpochOk historicalEpochOk near epochStartOk epochStartTimeOk historyCovers receiver
    atTime upToDate known finality receiverHeadOk receiverParent stateOk currentOk receiverEpochOk
    receiverNear receiverLastOk windowOk participantsOk exit absent

/-- A caller margin with the window reserve has an honest supporter of the root.

That supporter sent a vote, by the call, for a block above the root, before the call's slot.

The discount is at most the window's weight, since the root is not a future block.

So without an honest supporter the adversary pays for every supporter, against the margin.

The reserve bounds the Byzantine stake of the adversary's window, which ends by `finish`.

The supporter's latest message gives the vote, which the caller saw. -/
public theorem Execution.honest_vote_of_caller_margin [DecidablePred (· ∈ J)]
    (slots : 0 < config.SLOT_DURATION_MS)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    {head root : Root} {source : BeaconState preset fork}
    {slot first last : Slot} {block parent : BeaconBlock preset fork} {boost maximum : Gwei}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    (firstOk : addChecked parent.slot 1 = .ok first) (lastOk : subChecked slot 1 = .ok last)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum)
    {shift : ℕ} {support discount adversary : Gwei} (registry : source.RegistryWithinLimit)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head source root =
      .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head source root =
      .ok adversary)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (callerTime : (e.world n).time ≤ time)
    {finish : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first finish)
    {x : ValidatorIndex} (reference : x ∈ J) {m : ℕ} (referenceTime : time ≤ (e.world m).time)
    (referenceUpToDate : UpToDate config checks sources (e.world m).time ((e.world m).view x)
      ((e.world m).state x))
    {referenceSlot : Slot}
    (referenceSlotOk : ((e.world m).state x).getCurrentSlot config = .ok referenceSlot)
    (finishOk : subChecked referenceSlot 1 = .ok finish)
    (headDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch}
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (near : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (absent : AnchorParentAbsent (e := e) time) :
    ∃ v ∈ J, ∃ i, (e.world i).time ≤ (e.world n).time ∧ ∃ m ∈ (e.world i).sent, ∃ data,
      (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot ∧
      ((e.world n).state u).isAncestor ⟨data.beaconBlockRoot, .pending⟩ ⟨root, .pending⟩ =
        .ok true := by
  classical
  have reached := e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) n u caller
  have parentFound := Store.block_ok_iff.mp parentOk
  -- The call's epoch is at most one after the parent's, through the historical block.
  have callerEq : computeEpochAtSlot preset slot = callerEpoch := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
      using callerEpochOk
  subst callerEq
  obtain ⟨historicalBlock, historicalBlockOk, historicalEq⟩ :
      ∃ b, ((e.world n).state u).block historical = .ok b ∧
        computeEpochAtSlot preset b.slot = historicalEpoch := by
    simp only [Store.getBlockEpoch, bind_ok_iff, pure, Except.pure, Except.ok.injEq]
      at historicalEpochOk
    exact historicalEpochOk
  obtain ⟨parent', parentFound', historicalLe⟩ :=
    Store.slot_le_of_isAncestor (Store.block_ok_iff.mp historicalBlockOk) historicalBelow
  rw [parentFound, Option.some.injEq] at parentFound'
  subst parentFound'
  have historicalParent := epoch_le_of_slot_le (preset := preset) historicalBlock.slot
    parent.slot (UInt64.le_iff_toNat_le.mp historicalLe)
  rw [historicalEq] at historicalParent
  have nearParent : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset parent.slot).toNat + 1 := by omega
  obtain ⟨startSlot, advParticipants, I, firstLe, ordered, advOk, supportEq, supIn, equivIn,
    equivAre, apart, cover⟩ := caller_margin_sets (UInt64.le_of_eq anchorSlot) reached
      (absent u caller n callerTime) preGloas minLookahead maxLookahead ring slotOk blockOk
      parentOk firstOk lastOk headDescends nearParent registry aligned increment supportOk
      adversaryOk
  -- The adversary's window ends by the reserve's end.
  have lastLe : last ≤ finish := e.previousSlot_le_of_time_le start caller reference
    (callerTime.trans referenceTime) referenceUpToDate slotOk referenceSlotOk lastOk finishOk
  have reserveAdv : stake (fun v => balanceAt source v.toNat)
      (Store.activeMembers source advParticipants) = 0 ∨
      100 * stake (fun v => balanceAt source v.toNat)
        {v ∈ Store.activeMembers source advParticipants | v ∉ J} ≤
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
        stake (fun v => balanceAt source v.toNat) (Store.activeMembers source advParticipants) := by
    rcases ordered with ordered | empty
    · have bound := reserve startSlot last advParticipants firstLe ordered lastLe advOk
      exact .inr (by omega)
    · left
      rw [empty]
      rfl
  -- No known equivocator is honest.
  have dishonest : ∀ v ∈ I, v ∉ J := fun v member =>
    e.equivocatingIndices_honest slots (fun a ha v member => by
      simp [start a ha, Store.getForkchoiceStore_equivocatingIndices anchored] at member)
      n caller v (equivAre v member)
  -- The discount is at most the window's weight, as the root is not a future block.
  obtain ⟨current, currentOk, blocksLe, -⟩ := reached.forwardReachable.slots_le_current slots
    (UInt64.le_of_eq anchorSlot)
  rw [slotOk, Except.ok.injEq] at currentOk
  subst currentOk
  have discountLe := UInt64.le_iff_toNat_le.mp
    (Store.computeEmptySlotSupportDiscount_le blockOk parentOk firstOk lastOk maximumOk discountOk
      (blocksLe root block (Store.block_ok_iff.mp blockOk)))
  -- Without an honest supporter, the Byzantine supporters are paid by the adversary.
  have supporter : ∃ v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩, v ∈ J := by
    by_contra none
    have noHonest : {v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩ | v ∉ J} =
        ((e.world n).state u).supportersOf source ⟨root, .pending⟩ :=
      Finset.filter_true_of_mem fun v member honest => none ⟨v, member, honest⟩
    have byzantine := ForkChoice.byzantine_support_add_le (w := fun v => balanceAt source v.toNat)
      (J := J) supIn equivIn apart dishonest
    rw [noHonest, ← supportEq] at byzantine
    have byzLe : stake (fun v => balanceAt source v.toNat)
        {v ∈ Store.activeMembers source advParticipants | v ∉ J} ≤
        stake (fun v => balanceAt source v.toNat) (Store.activeMembers source advParticipants) :=
      stake_mono (Finset.filter_subset _ _)
    generalize config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
      stake (fun v => balanceAt source v.toNat) (Store.activeMembers source advParticipants) = P
      at cover reserveAdv
    rcases reserveAdv with zero | reserveAdv <;> omega
  obtain ⟨v, member, honest⟩ := supporter
  -- The supporter's latest vote comes from a message the caller saw, before the call slot.
  obtain ⟨message, supported, latest, -, supportedOk, descends⟩ :=
    ((e.world n).state u).exists_of_voteCountsFor (Store.voteCountsFor_of_mem_supportersOf member)
  obtain ⟨attestation, sent, seen, same, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start caller latest
  obtain ⟨readSlot, readOk, past⟩ := origin.past
  rw [slotOk, Except.ok.injEq] at readOk
  subst readOk
  rw [Store.getSupportedNode_of_lt preGloas, Except.ok.injEq] at supportedOk
  subst supportedOk
  subst same
  exact ⟨v, honest, n, le_rfl, sent, e.view_subset_sent n u seen, attestation.data, signed, past,
    descends⟩

end EthLib.Consensus.Models.Network
