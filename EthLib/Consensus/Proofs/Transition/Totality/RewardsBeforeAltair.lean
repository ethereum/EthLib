module

public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
import EthLib.Base.Proofs.FilterM
import EthLib.Consensus.Proofs.Transition.RewardDeltas

/-!
# Proofs: the rewards and penalties succeed before Altair

Before Altair the step sums four lists of rewards and four lists of penalties, then applies them.

The rewards and penalties of the source, target and head votes each depend on matching votes.

A vote matches the target when its target is the block root at the first slot of the previous epoch.

It matches the head when its head is also the block root at its own slot.

The inclusion rewards go to each signer and to the proposer of its earliest inclusion.

In a leak the inactivity penalties fall on each eligible validator.

A base reward is an effective balance times a fixed factor, over the square root of the total.

It is then divided among the four parts of an epoch reward.

The total is at least one increment, so a base reward is at most its value there.

A reward for a kind of vote multiplies the base reward by the increments that cast it.

These increments are those of the previous epoch, so the budget bounds them, not the total.

A proposer can earn a share of the base reward of every signer, once for each signer.

So its inclusion reward is at most the bound on base rewards at the sum of the effective balances.

The inactivity penalty multiplies an effective balance by the delay of finality.

That delay is at most the current epoch, which the theorem bounds.

The reads of block roots need the step to run at the last slot of an epoch.

The slot of each matching vote is in the previous epoch, as inclusion in a block checked.

The buffer of block roots then reaches it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

/-- Before Altair, a bound on the base reward of an effective balance.

It is the balance times the base reward factor, over the square root of one increment.

That is its value at the smallest total active balance, one increment.

It is then divided among the four parts of an epoch reward. -/
def Preset.baseRewardBoundBeforeAltair (preset : Preset) (balance : Nat) : Nat :=
  balance * preset.BASE_REWARD_FACTOR.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt /
    BASE_REWARDS_PER_EPOCH.toNat

/-- Before Altair, the bounds under which the rewards and penalties fit in 64 bits.

The budget bounds the balances and the sum of the effective balances.

The epoch bound bounds the current epoch, and so the delay of finality.

The largest cap times the base reward factor must fit.

A balance of the budget plus all the rewards of a validator must fit.

The rewards of the source, target and head votes are each at most one product.

That product is the bound on the base reward of the largest cap, times the increments of the budget.

The inclusion rewards of a validator are at most the bound on the base reward of the budget.

All the penalties of a validator must fit.

They are at most seven bounds on the base reward of the largest cap.

They add the largest cap times the epoch bound. -/
structure RewardsFitBeforeAltair (preset : Preset) (budget epochBound : Nat) : Prop where
  product : preset.largestEffectiveBalance * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64
  rewards : budget + 3 * preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance *
    preset.budgetIncrements budget + preset.baseRewardBoundBeforeAltair budget < 2 ^ 64
  penalties : 7 * preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance +
    preset.largestEffectiveBalance * epochBound < 2 ^ 64

/-- Under the bounds before Altair, the budget is below 2^64. -/
theorem RewardsFitBeforeAltair.budget_lt {preset : Preset} {budget epochBound : Nat}
    (fit : RewardsFitBeforeAltair preset budget epochBound) : budget < 2 ^ 64 := by
  have := fit.rewards
  omega

/-- The rewards of mainnet before Altair fit under a budget of 2^57 Gwei, for 2^21 epochs.

That budget is about 1.44 * 10^8 ETH, and 2^21 epochs are about 25 years. -/
theorem rewardsFitBeforeAltair_mainnet :
    RewardsFitBeforeAltair Preset.mainnet (2 ^ 57) (2 ^ 21) := by
  have root : (Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat).sqrt = 31622 :=
    (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  constructor
  · decide
  · simp only [Preset.baseRewardBoundBeforeAltair, root]
    decide
  · simp only [Preset.baseRewardBoundBeforeAltair, root]
    decide

/-- The rewards of minimal before Altair fit under a budget of 2^57 Gwei, for 2^21 epochs. -/
theorem rewardsFitBeforeAltair_minimal :
    RewardsFitBeforeAltair Preset.minimal (2 ^ 57) (2 ^ 21) := by
  have root : (Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat).sqrt = 31622 :=
    (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  constructor
  · decide
  · simp only [Preset.baseRewardBoundBeforeAltair, root]
    decide
  · simp only [Preset.baseRewardBoundBeforeAltair, root]
    decide

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- Before Altair, each recent pending attestation is as inclusion in a block stored it.

Its slot is in the epoch of the list that holds it, the previous or the current epoch.

Its inclusion delay is not zero, as the least inclusion delay of mainnet and minimal ensures.

The proposer that included it is a validator of the registry.

The epoch step moves the list of the current epoch to that of the previous epoch.

The property should hold again once the slot moves into the next epoch; no theorem proves it yet. -/
def PendingWellFormed (state : BeaconState preset fork) : Prop :=
  ∀ before : fork < .altair,
    (∀ attestation ∈ (state.previousEpochAttestations before).data,
      computeEpochAtSlot preset attestation.data.slot = getPreviousEpoch state ∧
        attestation.inclusionDelay ≠ 0 ∧
        attestation.proposerIndex.toNat < state.validators.data.size) ∧
    ∀ attestation ∈ (state.currentEpochAttestations before).data,
      computeEpochAtSlot preset attestation.data.slot = getCurrentEpoch state ∧
        attestation.inclusionDelay ≠ 0 ∧
        attestation.proposerIndex.toNat < state.validators.data.size

/-- The bound on a base reward before Altair grows with the balance. -/
private theorem baseRewardBoundBeforeAltair_mono {a b : Nat} (le : a ≤ b) :
    preset.baseRewardBoundBeforeAltair a ≤ preset.baseRewardBoundBeforeAltair b :=
  Nat.div_le_div_right (Nat.div_le_div_right (Nat.mul_le_mul_right _ le))

/-- The bounds on the base rewards of some balances sum to at most the bound of their sum. -/
private theorem sum_map_baseRewardBoundBeforeAltair_le {α : Type} (balance : α → Nat) :
    ∀ list : List α, (list.map fun x => preset.baseRewardBoundBeforeAltair (balance x)).sum ≤
      preset.baseRewardBoundBeforeAltair (list.map balance).sum
  | [] => by simp [Preset.baseRewardBoundBeforeAltair]
  | x :: rest => by
    have split : preset.baseRewardBoundBeforeAltair (balance x) +
        preset.baseRewardBoundBeforeAltair (rest.map balance).sum ≤
          preset.baseRewardBoundBeforeAltair (balance x + (rest.map balance).sum) := by
      simp only [Preset.baseRewardBoundBeforeAltair, Nat.div_div_eq_div_mul, Nat.add_mul]
      exact Nat.div_add_div_le_add_div
    have := sum_map_baseRewardBoundBeforeAltair_le balance rest
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Before Altair, the base reward of a validator under the largest cap succeeds.

The total must be at least one positive increment.

The largest cap times the base reward factor must fit.

The reward is then at most the bound at the effective balance of the validator. -/
private theorem getBaseReward_le_of_lt_altair (before : fork < .altair)
    (positive : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (product : preset.largestEffectiveBalance * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    {total : Gwei} (low : preset.EFFECTIVE_BALANCE_INCREMENT ≤ total)
    {index : ValidatorIndex} {validator : Validator}
    (found : state.validators.data[index.toNat]? = some validator)
    (capped : validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance) :
    ∃ base, getBaseReward state total index = .ok base ∧
      base.toNat ≤ preset.baseRewardBoundBeforeAltair validator.effectiveBalance.toNat := by
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have root := toNat_integerSquareroot total
  have rootLow := Nat.sqrt_le_sqrt (UInt64.le_iff_toNat_le.mp low)
  have rootPos := Nat.sqrt_pos.mpr incPos
  have nonzero : integerSquareroot total ≠ 0 := fun zero => by
    rw [zero, UInt64.toNat_zero] at root
    omega
  have fits : validator.effectiveBalance.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ capped) product
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  refine ⟨validator.effectiveBalance * preset.BASE_REWARD_FACTOR / integerSquareroot total /
    BASE_REWARDS_PER_EPOCH, ?_, ?_⟩
  · simp only [getBaseReward, getValidator, found, notAltair, ↓reduceIte, liftArith,
      mulChecked_of_lt fits, divChecked, nonzero, bind, Except.bind, Except.mapError, pure,
      Except.pure]
  · rw [UInt64.toNat_div, UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt fits, root]
    exact Nat.div_le_div_right (Nat.div_le_div_left rootLow rootPos)

/-- The proposer share of a base reward is at most that base reward. -/
private theorem toNat_proposerReward_le (base : Gwei) :
    (proposerReward preset base).toNat ≤ base.toNat := by
  unfold proposerReward
  rw [UInt64.toNat_div]
  exact Nat.div_le_self _ _

/-- After genesis, the current epoch is not zero. -/
private theorem getCurrentEpoch_toNat_ne_zero (genesis : getCurrentEpoch state ≠ GENESIS_EPOCH) :
    (getCurrentEpoch state).toNat ≠ 0 := fun zero =>
  genesis (UInt64.toNat_inj.mp (by simpa [GENESIS_EPOCH] using zero))

/-- After genesis, the votes with a source in the previous epoch are the list of that epoch. -/
private theorem previousSource_eq (before : fork < .altair)
    (genesis : getCurrentEpoch state ≠ GENESIS_EPOCH) :
    (if getPreviousEpoch state = getCurrentEpoch state then
      (state.currentEpochAttestations before).data
      else (state.previousEpochAttestations before).data) =
        (state.previousEpochAttestations before).data := by
  have ne : getPreviousEpoch state ≠ getCurrentEpoch state := fun same => by
    have value := congrArg UInt64.toNat same
    rw [getPreviousEpoch_toNat] at value
    have := getCurrentEpoch_toNat_ne_zero genesis
    omega
  simp [ne]

/-- At the last slot of an epoch after genesis, the root of a slot of the previous epoch succeeds.

The buffer of block roots must reach the epoch before, and the slot plus its length must fit. -/
private theorem getBlockRootAtSlot_previous_exists (roots : preset.RootsReachPreviousEpoch)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (genesis : getCurrentEpoch state ≠ GENESIS_EPOCH) {slot : Slot}
    (inEpoch : computeEpochAtSlot preset slot = getPreviousEpoch state) :
    ∃ root, getBlockRootAtSlot state slot = .ok root := by
  have twoSlots := roots.twoSlots
  have reach := roots.reach
  have decomposed := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [slot_mod_eq_of_last twoSlots last, ← getCurrentEpoch_toNat] at decomposed
  have epochNat := congrArg UInt64.toNat inEpoch
  rw [getPreviousEpoch_toNat] at epochNat
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
  have slotDecomposed := Nat.div_add_mod slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have slotMod := Nat.mod_lt slot.toNat (by omega : 0 < preset.SLOTS_PER_EPOCH.toNat)
  rw [epochNat, Nat.mul_sub_one] at slotDecomposed
  have nonzero := getCurrentEpoch_toNat_ne_zero genesis
  have atLeast : preset.SLOTS_PER_EPOCH.toNat ≤
      preset.SLOTS_PER_EPOCH.toNat * (getCurrentEpoch state).toNat :=
    Nat.le_mul_of_pos_right _ (by omega)
  exact getBlockRootAtSlot_exists (by omega) (by omega) (by omega) (by omega)

/-- After genesis, the attestations that match the head of the previous epoch succeed.

The step must run at the last slot of an epoch, and the buffer of block roots must reach back.

Each recent pending attestation must be as inclusion in a block stored it.

Only the list of the previous epoch is read; the other half keeps the property through an epoch.

They come from the list of the previous epoch. -/
private theorem getMatchingHeadAttestations_previous (before : fork < .altair)
    (roots : preset.RootsReachPreviousEpoch)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (genesis : getCurrentEpoch state ≠ GENESIS_EPOCH) (wellFormed : PendingWellFormed state) :
    ∃ head, getMatchingHeadAttestations state before (getPreviousEpoch state) = .ok head ∧
      ∀ attestation ∈ head, attestation ∈ (state.previousEpochAttestations before).data := by
  obtain ⟨target, targetOk, targetIn⟩ := getMatchingTargetAttestations_exists_ok before
    (.inl rfl) (getBlockRoot_exists_ok roots last room (.inl rfl))
  simp only [previousSource_eq before genesis] at targetIn
  unfold getMatchingHeadAttestations
  rw [targetOk]
  show ∃ head, Array.filterM (m := Except TransitionError) _ target = Except.ok head ∧ _
  rw [← Array.toArray_toList (xs := target), List.filterM_toArray]
  obtain ⟨out, outOk⟩ := filterM_exists_ok (list := target.toList)
    (test := fun attestation : PendingAttestation preset => (do
      let root ← liftAccessor (getBlockRootAtSlot state attestation.data.slot)
      pure (attestation.data.beaconBlockRoot == root) : Except TransitionError Bool))
    fun attestation member => by
      have inEpoch := ((wellFormed before).1 attestation
        (targetIn attestation (Array.mem_toList_iff.mp member))).1
      obtain ⟨root, read⟩ := getBlockRootAtSlot_previous_exists roots last room genesis inEpoch
      exact ⟨attestation.data.beaconBlockRoot == root, by
        simp [read, liftAccessor, Except.mapError, bind, Except.bind, pure, Except.pure]⟩
  refine ⟨out.toArray, by rw [outOk]; rfl, fun attestation member => targetIn attestation
    (Array.mem_toList_iff.mp (mem_of_filterM_ok outOk (by simpa using member)))⟩

/-- Before Altair, the reward and the penalty of one kind of vote succeed for one validator.

The test for a leak must succeed.

The base reward times the attesting increments must fit. -/
private theorem componentDelta_exists_ok {leak : Bool}
    (leaking : isInInactivityLeak state = .ok leak) (matched : Bool)
    {base attestingBalance total : Gwei}
    (fits : base.toNat * (attestingBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat < 2 ^ 64) :
    ∃ result, componentDelta state matched base attestingBalance total = .ok result := by
  unfold componentDelta
  cases matched
  · exact ⟨_, rfl⟩
  · simp only [↓reduceIte, leaking, bind, Except.bind]
    cases leak
    · simp [liftAccessor, liftArith, mulChecked_of_lt fits, Except.mapError, pure, Except.pure]
    · exact ⟨_, rfl⟩

/-- Before Altair, the rewards and penalties of one kind of vote succeed, under bounds.

The signers of each matching attestation must succeed.

Each base reward of the registry must succeed, at most a bound.

That bound times the increments of the budget must fit.

Each reward is then at most that product, and each penalty at most the bound. -/
private theorem getAttestationComponentDeltas_exists_le {budget ceiling : Nat}
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state ≤ budget)
    (budgetLt : budget < 2 ^ 64) (finalized : FinalizedSettled state) {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (baseOk : ∀ index : ValidatorIndex, index.toNat < state.validators.data.size →
      ∃ base, getBaseReward state total index = .ok base ∧ base.toNat ≤ ceiling)
    (one : 1 ≤ preset.budgetIncrements budget)
    (fits : ceiling * preset.budgetIncrements budget < 2 ^ 64)
    {attestations : Array (PendingAttestation preset)}
    (resolved : ∀ attestation ∈ attestations,
      ∃ signers, getPendingAttestingIndices state attestation = .ok signers) :
    ∃ rewards penalties,
      getAttestationComponentDeltas state attestations = .ok (rewards, penalties) ∧
      ∀ j < state.validators.data.size,
        (rewards.getD j 0).toNat ≤ ceiling * preset.budgetIncrements budget ∧
          (penalties.getD j 0).toNat ≤ ceiling := by
  obtain ⟨attesters, attestersOk, inside⟩ := getUnslashedAttestingIndices_exists_ok within resolved
  obtain ⟨attestingBalance, balanceOk, balanceLe⟩ :=
    getTotalBalance_exists_ok inside (Nat.lt_of_le_of_lt summed budgetLt)
  have incrementsLe : (attestingBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat ≤
      preset.budgetIncrements budget :=
    toNat_div_le_budgetIncrements (le_trans balanceLe (max_le_max (le_refl _) summed))
  obtain ⟨eligible, eligibleOk⟩ := getEligibleValidatorIndices_exists_ok within
  have distinct := (getEligibleValidatorIndices_ok eligibleOk).1
  have eligibleLt := getEligibleValidatorIndices_lt within eligibleOk
  have leakOk := isInInactivityLeak_eq_ok finalized
  obtain ⟨⟨rewards, penalties⟩, computed⟩ :
      ∃ out, getAttestationComponentDeltas state attestations = .ok out := by
    simp only [getAttestationComponentDeltas, liftAccessor, totalOk, attestersOk, balanceOk,
      eligibleOk, Except.mapError, bind, Except.bind]
    refine foldlM_exists_ok_of_distinct UInt64.toNat
      (fun (last : Array Gwei × Array Gwei) (index : ValidatorIndex) =>
        index.toNat < state.validators.data.size ∧ index.toNat < last.1.size ∧
          index.toNat < last.2.size ∧ last.1.getD index.toNat 0 = 0 ∧
            last.2.getD index.toNat 0 = 0)
      (fun ⟨rewards, penalties⟩ index ⟨lt, insideRewards, insidePenalties, zeroRewards,
          zeroPenalties⟩ => ?_) eligible _ distinct (fun index member => by
        have lt := eligibleLt index member
        exact ⟨lt, by simpa using lt, by simpa using lt, replicate_getD_zero _ _,
          replicate_getD_zero _ _⟩)
    obtain ⟨base, based, baseLe⟩ := baseOk index lt
    obtain ⟨⟨reward, penalty⟩, deltaOk⟩ := componentDelta_exists_ok leakOk
      ((markIndices state.validators.data.size attesters).getD index.toNat false)
      (attestingBalance := attestingBalance) (total := total)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul baseLe incrementsLe) fits)
    obtain ⟨rewarded, rewardedOk⟩ := addDelta_exists_ok_of_zero reward insideRewards zeroRewards
    obtain ⟨penalized, penalizedOk⟩ :=
      addDelta_exists_ok_of_zero penalty insidePenalties zeroPenalties
    refine ⟨(rewarded, penalized), ?_, fun other ne ⟨lt', insideRewards', insidePenalties',
      zeroRewards', zeroPenalties'⟩ => ⟨lt', ?_, ?_, ?_, ?_⟩⟩
    · simp only [based, deltaOk, rewardedOk, penalizedOk]
      rfl
    · rw [addDelta_size rewardedOk]
      exact insideRewards'
    · rw [addDelta_size penalizedOk]
      exact insidePenalties'
    · rw [addDelta_getD_of_ne rewardedOk ne]
      exact zeroRewards'
    · rw [addDelta_getD_of_ne penalizedOk ne]
      exact zeroPenalties'
  refine ⟨rewards, penalties, computed, fun j inside => ?_⟩
  obtain ⟨total', attesters', attestingBalance', totalOk', attestersOk', balanceOk', entries⟩ :=
    getAttestationComponentDeltas_getD within computed
  obtain rfl : total = total' := Except.ok.inj (totalOk.symm.trans totalOk')
  obtain rfl : attesters = attesters' := Except.ok.inj (attestersOk.symm.trans attestersOk')
  obtain rfl : attestingBalance = attestingBalance' :=
    Except.ok.inj (balanceOk.symm.trans balanceOk')
  obtain ⟨eligible, -, notEligible, isEligible⟩ := entries j inside
  cases eligible
  · rw [(notEligible rfl).1, (notEligible rfl).2]
    simp
  · obtain ⟨base, based, present, absent⟩ := isEligible rfl
    obtain ⟨base', based', baseLe⟩ := baseOk j.toUInt64
      (by rw [toNat_toUInt64_of_lt within inside]; exact inside)
    obtain rfl : base = base' := Except.ok.inj (based.symm.trans based')
    by_cases member : j.toUInt64 ∈ attesters
    · obtain ⟨leak, -, value, zero⟩ := present member
      rw [value, zero]
      refine ⟨?_, by simp⟩
      split
      · exact le_trans baseLe (Nat.le_mul_of_pos_right _ one)
      · rw [UInt64.toNat_div] at incrementsLe
        exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul baseLe incrementsLe)
    · rw [(absent member).1, (absent member).2]
      exact ⟨by simp, baseLe⟩

/-- The effective balances of distinct validators of the registry sum to at most all of them. -/
private theorem sum_effectiveBalance_le {indices : List Nat} (distinct : indices.Nodup)
    (inside : ∀ j ∈ indices, j < state.validators.data.size) :
    (indices.map fun j =>
      ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0).sum ≤
        effectiveBalanceSum state := by
  rw [effectiveBalanceSum_eq_sum_range]
  obtain ⟨middle, perm, sub⟩ :=
    List.subperm_of_subset distinct fun j member => List.mem_range.mpr (inside j member)
  rw [← (perm.map _).sum_eq]
  exact (sub.map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- One inclusion reward succeeds, for an attester with an earliest inclusion.

Its proposer and the attester must be in the rewards, and its delay must not be zero.

Each entry plus the base reward of the attester must fit.

The size stays, and each entry rises by at most that base reward. -/
private theorem addInclusionReward_exists_le {total : Gwei}
    {earliest : Array (Option (PendingAttestation preset))} {rewards : Array Gwei}
    {index : ValidatorIndex} {attestation : PendingAttestation preset} {base : Gwei}
    (inside : index.toNat < rewards.size)
    (found : earliest.getD index.toNat none = some attestation)
    (proposer : attestation.proposerIndex.toNat < rewards.size)
    (delayed : attestation.inclusionDelay ≠ 0)
    (based : getBaseReward state total index = .ok base)
    (fits : ∀ j, (rewards.getD j 0).toNat + base.toNat < 2 ^ 64) :
    ∃ next, addInclusionReward state total earliest rewards index = .ok next ∧
      next.size = rewards.size ∧
      ∀ j, (next.getD j 0).toNat ≤ (rewards.getD j 0).toNat + base.toNat := by
  have share := toNat_proposerReward_le (preset := preset) base
  have shareLe : proposerReward preset base ≤ base := UInt64.le_iff_toNat_le.mpr share
  obtain ⟨raised, raisedOk⟩ := addDelta_exists_ok (amount := proposerReward preset base) proposer
    (by have := fits attestation.proposerIndex.toNat; omega)
  have raisedEntry := addDelta_getD raisedOk
  have subOk : subChecked base (proposerReward preset base) =
      .ok (base - proposerReward preset base) := by
    simp only [subChecked, shareLe, ↓reduceIte]
  have rest : ((base - proposerReward preset base) / attestation.inclusionDelay).toNat ≤
      base.toNat - (proposerReward preset base).toNat := by
    rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ shareLe]
    exact Nat.div_le_self _ _
  obtain ⟨next, nextOk⟩ := addDelta_exists_ok (deltas := raised)
    (amount := (base - proposerReward preset base) / attestation.inclusionDelay)
    (by rw [addDelta_size raisedOk]; exact inside)
    (by
      rw [raisedEntry]
      have := fits index.toNat
      by_cases same : attestation.proposerIndex.toNat = index.toNat <;>
        simp only [same, ↓reduceIte] <;> omega)
  have ensured : ensure (attestation.inclusionDelay ≠ 0) TransitionError.zeroInclusionDelay =
      .ok () := ensure_ok_iff.mpr delayed
  refine ⟨next, ?_, by rw [addDelta_size nextOk, addDelta_size raisedOk], fun j => ?_⟩
  · simp only [addInclusionReward, found, liftAccessor, based, raisedOk, liftArith, subOk,
      ensured, nextOk, Except.mapError, bind, Except.bind]
  · rw [addDelta_getD nextOk, raisedEntry]
    by_cases first : attestation.proposerIndex.toNat = j <;>
      by_cases second : index.toNat = j <;> simp only [first, second, ↓reduceIte] <;> omega

/-- A fold of inclusion rewards succeeds when each attester is ready and the entries have room.

Each attester must have an earliest inclusion, with its proposer in the rewards and a delay.

Its base reward must succeed, at most its weight.

Each entry plus the sum of the weights must fit.

Each entry then rises by at most that sum. -/
private theorem foldlM_addInclusionReward_exists_le {total : Gwei}
    {earliest : Array (Option (PendingAttestation preset))} (weight : ValidatorIndex → Nat) :
    ∀ (attesters : List ValidatorIndex) (start : Array Gwei),
      (∀ index ∈ attesters, index.toNat < start.size ∧
        (∃ attestation, earliest.getD index.toNat none = some attestation ∧
          attestation.proposerIndex.toNat < start.size ∧ attestation.inclusionDelay ≠ 0) ∧
        ∃ base, getBaseReward state total index = .ok base ∧ base.toNat ≤ weight index) →
      (∀ j, (start.getD j 0).toNat + (attesters.map weight).sum < 2 ^ 64) →
      ∃ result, attesters.foldlM (addInclusionReward state total earliest) start = .ok result ∧
        ∀ j, (result.getD j 0).toNat ≤ (start.getD j 0).toNat + (attesters.map weight).sum
  | [], start, _, _ => ⟨start, rfl, fun j => by simp⟩
  | index :: rest, start, ready, fits => by
    obtain ⟨inside, ⟨attestation, found, proposer, delayed⟩, base, based, baseLe⟩ :=
      ready index List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at fits ⊢
    obtain ⟨middle, stepped, sized, raised⟩ := addInclusionReward_exists_le inside found proposer
      delayed based fun j => by have := fits j; omega
    obtain ⟨result, folded, bounded⟩ := foldlM_addInclusionReward_exists_le weight rest middle
      (fun other member => by
        rw [sized]
        exact ready other (List.mem_cons_of_mem _ member))
      fun j => by have := fits j; have := raised j; omega
    refine ⟨result, by rw [List.foldlM_cons, stepped]; exact folded, fun j => ?_⟩
    have := bounded j
    have := raised j
    omega

/-- Before Altair and after genesis, the inclusion rewards succeed under bounds.

Each base reward must succeed, at most the bound at the effective balance of its validator.

The sum of the effective balances must be at most the budget, whose bound must fit.

The signers of each recent pending attestation must succeed, as inclusion in a block stored it.

Each reward is then at most the bound at the budget. -/
private theorem getInclusionDelayDeltas_exists_le {budget : Nat} (before : fork < .altair)
    (genesis : getCurrentEpoch state ≠ GENESIS_EPOCH) (within : state.RegistryWithinLimit)
    (summed : effectiveBalanceSum state ≤ budget)
    (fits : preset.baseRewardBoundBeforeAltair budget < 2 ^ 64) {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (baseOk : ∀ (index : ValidatorIndex) (validator : Validator),
      state.validators.data[index.toNat]? = some validator →
      ∃ base, getBaseReward state total index = .ok base ∧
        base.toNat ≤ preset.baseRewardBoundBeforeAltair validator.effectiveBalance.toNat)
    (resolved : PendingResolved state) (wellFormed : PendingWellFormed state) :
    ∃ rewards penalties, getInclusionDelayDeltas state before = .ok (rewards, penalties) ∧
      ∀ j, (rewards.getD j 0).toNat ≤ preset.baseRewardBoundBeforeAltair budget := by
  have sourceOk := getMatchingSourceAttestations_eq_ok (state := state) before (.inl rfl)
  rw [previousSource_eq before genesis] at sourceOk
  obtain ⟨signers, signersOk⟩ := mapM_exists_ok
    (xs := (state.previousEpochAttestations before).data.toList)
    (f := getPendingAttestingIndices state) fun attestation member =>
      resolved before attestation (.inl (Array.mem_toList_iff.mp member))
  obtain ⟨attesters, attestersOk, inside⟩ := getUnslashedAttestingIndices_exists_ok within
    (attestations := (state.previousEpochAttestations before).data)
    fun attestation member => resolved before attestation (.inl member)
  have amongOk : unslashedAmong state signers = .ok attesters := by
    unfold getUnslashedAttestingIndices at attestersOk
    rw [signersOk] at attestersOk
    exact attestersOk
  have filtered := amongOk
  unfold unslashedAmong at filtered
  -- The attesters are distinct, since they come in increasing order.
  have distinct : (attesters.map UInt64.toNat).Nodup :=
    List.pairwise_map.mpr (((sortedSet_sorted _).sublist (sublist_of_filterM_ok filtered)).imp
      fun lt => Nat.ne_of_lt (UInt64.lt_iff_toNat_lt.mp lt))
  let balanceAt : Nat → Nat := fun j =>
    ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0
  let earliest := earliestInclusions state.validators.data.size
    ((state.previousEpochAttestations before).data.zip signers.toArray)
  obtain ⟨sizeEq, origin⟩ := earliestInclusions_size_and_mem (size := state.validators.data.size)
    (signed := (state.previousEpochAttestations before).data.zip signers.toArray)
  have lengths := mapM_ok_length signersOk
  -- Each attester has an earliest inclusion, from the list of the previous epoch.
  have ready : ∀ index ∈ attesters,
      index.toNat < (Array.replicate state.validators.data.size (0 : Gwei)).size ∧
      (∃ attestation, earliest.getD index.toNat none = some attestation ∧
        attestation.proposerIndex.toNat <
          (Array.replicate state.validators.data.size (0 : Gwei)).size ∧
        attestation.inclusionDelay ≠ 0) ∧
      ∃ base, getBaseReward state total index = .ok base ∧
        base.toNat ≤ preset.baseRewardBoundBeforeAltair (balanceAt index.toNat) := by
    intro index member
    have lt := inside index member
    have listed : earliest.getD index.toNat none ≠ none := fun empty => by
      obtain ⟨list, listMember, indexMember⟩ :=
        List.mem_flatten.mp (mem_sortedSet.mp (mem_of_filterM_ok filtered member))
      obtain ⟨k, small, rfl⟩ := List.getElem_of_mem listMember
      refine (earliestInclusions_getD lt).1.mp empty
        ((state.previousEpochAttestations before).data.toList[k]'(by omega), signers[k]) ?_
        index indexMember rfl
      rw [Array.toList_zip]
      have sized : signers.length = (state.previousEpochAttestations before).data.size := by
        simpa using lengths
      exact List.mem_iff_getElem.mpr ⟨k, by simp only [List.length_zip, Array.length_toList]; omega,
        by simp⟩
    obtain ⟨attestation, found⟩ := Option.ne_none_iff_exists'.mp listed
    have stored : earliest[index.toNat]? = some (some attestation) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [sizeEq]; exact lt)]
        at found
      rw [Array.getElem?_eq_getElem (by rw [sizeEq]; exact lt)]
      simpa using found
    obtain ⟨_, pair⟩ := origin _ _ stored
    rw [Array.toList_zip] at pair
    obtain ⟨-, delayed, proposer⟩ :=
      (wellFormed before).1 attestation (Array.mem_toList_iff.mp (List.of_mem_zip pair).1)
    obtain ⟨base, based, baseLe⟩ := baseOk index _ (Array.getElem?_eq_getElem lt)
    refine ⟨by simpa using lt, ⟨attestation, found, by simpa using proposer, delayed⟩, base,
      based, ?_⟩
    simpa [balanceAt, Array.getElem?_eq_getElem lt] using baseLe
  -- The weights of the attesters sum to at most the bound at the budget.
  have weights : (attesters.map fun index =>
      preset.baseRewardBoundBeforeAltair (balanceAt index.toNat)).sum ≤
        preset.baseRewardBoundBeforeAltair budget := by
    have mapped : (attesters.map fun index =>
        preset.baseRewardBoundBeforeAltair (balanceAt index.toNat)) =
        (attesters.map UInt64.toNat).map fun j =>
          preset.baseRewardBoundBeforeAltair (balanceAt j) := by
      simp
    rw [mapped]
    refine le_trans (sum_map_baseRewardBoundBeforeAltair_le balanceAt _)
      (baseRewardBoundBeforeAltair_mono (le_trans (sum_effectiveBalance_le distinct ?_) summed))
    intro j member
    obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp member
    exact inside index indexMember
  obtain ⟨rewards, folded, bounded⟩ := foldlM_addInclusionReward_exists_le
    (fun index => preset.baseRewardBoundBeforeAltair (balanceAt index.toNat)) attesters
    (Array.replicate state.validators.data.size 0) ready
    fun j => by rw [replicate_getD_zero]; simp only [UInt64.toNat_zero]; omega
  refine ⟨rewards, Array.replicate state.validators.data.size 0, ?_, fun j => ?_⟩
  · simp only [getInclusionDelayDeltas, sourceOk, liftAccessor, signersOk, amongOk, totalOk,
      Except.mapError, bind, Except.bind]
    rw [folded]
    rfl
  · have := bounded j
    rw [replicate_getD_zero, UInt64.toNat_zero] at this
    omega

/-- Before Altair, one inactivity penalty succeeds at an index with a zero entry.

The base reward must succeed, at most a bound, and the effective balance at most the largest cap.

The delay of finality must be at most an epoch bound.

Four bounds on base rewards plus the largest cap times the epoch bound must fit.

It keeps the size of the penalties. -/
private theorem addInactivityPenalty_exists_ok {total delay : Gwei} {targetMatched : Array Bool}
    {penalties : Array Gwei} {index : ValidatorIndex} {validator : Validator} {base : Gwei}
    {ceiling epochBound : Nat} (found : state.validators.data[index.toNat]? = some validator)
    (capped : validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance)
    (based : getBaseReward state total index = .ok base) (baseLe : base.toNat ≤ ceiling)
    (delayLe : delay.toNat ≤ epochBound)
    (fits : 4 * ceiling + preset.largestEffectiveBalance * epochBound < 2 ^ 64)
    (inside : index.toNat < penalties.size) (zero : penalties.getD index.toNat 0 = 0) :
    ∃ next, addInactivityPenalty state total delay targetMatched penalties index = .ok next ∧
      next.size = penalties.size := by
  have perEpoch : BASE_REWARDS_PER_EPOCH.toNat = 4 := rfl
  have full : BASE_REWARDS_PER_EPOCH.toNat * base.toNat < 2 ^ 64 := by
    rw [perEpoch]
    omega
  have fullValue : (BASE_REWARDS_PER_EPOCH * base).toNat = 4 * base.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt full, perEpoch]
  have share := toNat_proposerReward_le (preset := preset) base
  have shareLe : proposerReward preset base ≤ BASE_REWARDS_PER_EPOCH * base := by
    rw [UInt64.le_iff_toNat_le, fullValue]
    omega
  have subOk : subChecked (BASE_REWARDS_PER_EPOCH * base) (proposerReward preset base) =
      .ok (BASE_REWARDS_PER_EPOCH * base - proposerReward preset base) := by
    simp only [subChecked, shareLe, ↓reduceIte]
  obtain ⟨paid, paidOk⟩ := addDelta_exists_ok_of_zero
    (BASE_REWARDS_PER_EPOCH * base - proposerReward preset base) inside zero
  have paidEntry : (paid.getD index.toNat 0).toNat ≤ 4 * ceiling := by
    rw [addDelta_getD paidOk, zero, UInt64.toNat_sub_of_le _ _ shareLe, fullValue]
    simp only [UInt64.toNat_zero, ↓reduceIte]
    omega
  have product := Nat.mul_le_mul capped delayLe
  have scaledFits : validator.effectiveBalance.toNat * delay.toNat < 2 ^ 64 := by omega
  obtain ⟨penalized, penalizedOk⟩ := addDelta_exists_ok (deltas := paid)
    (amount := validator.effectiveBalance * delay /
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT)
    (by rw [addDelta_size paidOk]; exact inside) (by
      rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt scaledFits]
      have := Nat.div_le_self (validator.effectiveBalance.toNat * delay.toNat)
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat
      omega)
  have validatorOk : getValidator state index = .ok validator := getValidator_eq_ok_iff.mpr found
  unfold addInactivityPenalty
  simp only [liftAccessor, based, liftArith, mulChecked_of_lt full, subOk, paidOk,
    Except.mapError, bind, Except.bind]
  split
  · exact ⟨_, rfl, addDelta_size paidOk⟩
  · simp only [validatorOk, mulChecked_of_lt scaledFits, penalizedOk]
    exact ⟨_, rfl, (addDelta_size penalizedOk).trans (addDelta_size paidOk)⟩

/-- Before Altair and after genesis, the inactivity deltas succeed under bounds.

The step must run at the last slot of an epoch, and the buffer of block roots must reach back.

Each base reward of the registry must succeed, at most a bound.

Each effective balance must be at most the largest cap, and the current epoch at most a bound.

Four bounds on base rewards plus the largest cap times the epoch bound must fit.

Each penalty is then at most that sum. -/
private theorem getInactivityPenaltyDeltas_exists_le {config : Config} {ceiling epochBound : Nat}
    (before : fork < .altair) (roots : preset.RootsReachPreviousEpoch)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (horizon : (getCurrentEpoch state).toNat ≤ epochBound) (within : state.RegistryWithinLimit)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance)
    (finalized : FinalizedSettled state) (resolved : PendingResolved state) {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (baseOk : ∀ index : ValidatorIndex, index.toNat < state.validators.data.size →
      ∃ base, getBaseReward state total index = .ok base ∧ base.toNat ≤ ceiling)
    (fits : 4 * ceiling + preset.largestEffectiveBalance * epochBound < 2 ^ 64) :
    ∃ rewards penalties, getInactivityPenaltyDeltas config state = .ok (rewards, penalties) ∧
      ∀ j < state.validators.data.size,
        (penalties.getD j 0).toNat ≤ 4 * ceiling + preset.largestEffectiveBalance * epochBound := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  have leakOk := isInInactivityLeak_eq_ok finalized
  have delayOk := getFinalityDelay_eq_ok finalized
  have delayLe : (getPreviousEpoch state - state.finalizedCheckpoint.epoch).toNat ≤
      epochBound := by
    rw [UInt64.toNat_sub_of_le _ _ finalized, getPreviousEpoch_toNat]
    omega
  obtain ⟨target, targetOk, targetIn⟩ := getMatchingTargetAttestations_exists_ok before
    (.inl rfl) (getBlockRoot_exists_ok roots last room (.inl rfl))
  obtain ⟨attesters, attestersOk, -⟩ := getUnslashedAttestingIndices_exists_ok within
    fun attestation member =>
      resolved before attestation (mem_recent_of_mem_source (targetIn attestation member))
  obtain ⟨⟨rewards, penalties⟩, computed⟩ :
      ∃ out, getInactivityPenaltyDeltas config state = .ok out := by
    unfold getInactivityPenaltyDeltas
    simp only [notAltair, ↓reduceDIte, leakOk, bind, Except.bind]
    split
    · obtain ⟨eligible, eligibleOk⟩ := getEligibleValidatorIndices_exists_ok within
      have distinct := (getEligibleValidatorIndices_ok eligibleOk).1
      have eligibleLt := getEligibleValidatorIndices_lt within eligibleOk
      simp only [targetOk, liftAccessor, attestersOk, totalOk, delayOk, eligibleOk,
        Except.mapError]
      obtain ⟨out, folded⟩ := foldlM_exists_ok_of_distinct UInt64.toNat
        (fun (last : Array Gwei) (index : ValidatorIndex) =>
          index.toNat < state.validators.data.size ∧ index.toNat < last.size ∧
            last.getD index.toNat 0 = 0)
        (step := addInactivityPenalty state total
          (getPreviousEpoch state - state.finalizedCheckpoint.epoch)
          (markIndices state.validators.data.size attesters))
        (fun last index ⟨lt, insideLast, zero⟩ => by
          obtain ⟨base, based, baseLe⟩ := baseOk index lt
          obtain ⟨next, stepped, size⟩ := addInactivityPenalty_exists_ok
            (targetMatched := markIndices state.validators.data.size attesters)
            (Array.getElem?_eq_getElem lt) (capped _ (Array.getElem_mem lt)) based baseLe
            delayLe fits insideLast zero
          refine ⟨next, stepped, fun other ne ⟨lt', inside', zero'⟩ => ⟨lt', ?_, ?_⟩⟩
          · rw [size]
            exact inside'
          · rw [addInactivityPenalty_getD_of_ne stepped ne]
            exact zero')
        eligible (Array.replicate state.validators.data.size 0) distinct
        (fun index member => by
          have lt := eligibleLt index member
          exact ⟨lt, by simpa using lt, replicate_getD_zero _ _⟩)
      rw [folded]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  refine ⟨rewards, penalties, computed, fun j inside => ?_⟩
  obtain ⟨-, leak, leakOk', outside, leaking⟩ :=
    getInactivityPenaltyDeltas_getD_of_lt_altair before within computed
  cases leak
  · rw [outside rfl j]
    simp
  · obtain ⟨_, attesters', total', delay, -, -, totalOk', delayOk', entries⟩ := leaking rfl
    obtain rfl : total = total' := Except.ok.inj (totalOk.symm.trans totalOk')
    obtain rfl : getPreviousEpoch state - state.finalizedCheckpoint.epoch = delay :=
      Except.ok.inj (delayOk.symm.trans delayOk')
    obtain ⟨eligible, -, notEligible, isEligible⟩ := entries j inside
    cases eligible
    · rw [notEligible rfl]
      simp
    · obtain ⟨base, based, value⟩ := isEligible rfl
      obtain ⟨base', based', baseLe⟩ := baseOk j.toUInt64
        (by rw [toNat_toUInt64_of_lt within inside]; exact inside)
      obtain rfl : base = base' := Except.ok.inj (based.symm.trans based')
      have perEpoch : BASE_REWARDS_PER_EPOCH.toNat = 4 := rfl
      have product := Nat.mul_le_mul (capped _ (Array.getElem_mem inside)) delayLe
      have scaled := Nat.div_le_self
        (state.validators.data[j].effectiveBalance.toNat *
          (getPreviousEpoch state - state.finalizedCheckpoint.epoch).toNat)
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat
      have shared := Nat.div_le_self base.toNat preset.PROPOSER_REWARD_QUOTIENT.toNat
      rw [value, perEpoch]
      generalize base.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat = share at shared ⊢
      generalize state.validators.data[j].effectiveBalance.toNat *
        (getPreviousEpoch state - state.finalizedCheckpoint.epoch).toNat /
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat = extra at scaled ⊢
      split <;> omega

/-- The sums of four lists of deltas succeed when each sum below the size of the first fits. -/
private theorem sumDeltas_exists_ok {first second third fourth : Array Gwei}
    (fits : ∀ j < first.size, (first.getD j 0).toNat + (second.getD j 0).toNat +
      (third.getD j 0).toNat + (fourth.getD j 0).toNat < 2 ^ 64) :
    ∃ result, sumDeltas first second third fourth = .ok result := by
  unfold sumDeltas
  refine array_mapM_exists_ok fun j member => ?_
  have sum := fits j (by simpa using member)
  have one : (first.getD j 0).toNat + (second.getD j 0).toNat < 2 ^ 64 := by omega
  have two : (first.getD j 0 + second.getD j 0).toNat + (third.getD j 0).toNat < 2 ^ 64 := by
    rw [toNat_add_of_lt one]
    omega
  have three : (first.getD j 0 + second.getD j 0 + third.getD j 0).toNat +
      (fourth.getD j 0).toNat < 2 ^ 64 := by
    rw [toNat_add_of_lt two, toNat_add_of_lt one]
    omega
  exact ⟨first.getD j 0 + second.getD j 0 + third.getD j 0 + fourth.getD j 0, by
    simp only [liftAccessor, liftArith, addChecked_of_lt one, addChecked_of_lt two,
      addChecked_of_lt three, Except.mapError, bind, Except.bind]⟩

/-- Before Altair, the rewards and penalties succeed under bounds.

The step must run at the last slot of an epoch.

The current epoch must be at most the epoch bound.

An epoch of the preset must have two slots at least.

Its buffer of block roots must reach the epoch before.

The slot plus the length of that buffer must be below 2^64.

The registry must stay within its limit, with one balance for each validator.

Each effective balance must be at most the largest cap, as the cap of its validator is.

The sum of the effective balances and each balance must be at most the budget.

The finalized epoch must be at most the previous epoch, so that the test for a leak succeeds.

The committee and the signers of each recent pending attestation must succeed.

Each recent pending attestation must be as inclusion in a block stored it.

The divisors of the preset must be positive.

The hypotheses are read on the state that justification and finalization return.

A run must show that they hold there. -/
theorem processRewardsAndPenalties_total_of_lt_altair {config : Config} {budget epochBound : Nat}
    (before : fork < .altair) (positive : preset.DivisorsPositive)
    (roots : preset.RootsReachPreviousEpoch) (fit : RewardsFitBeforeAltair preset budget epochBound)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (horizon : (getCurrentEpoch state).toNat ≤ epochBound)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance)
    (summed : effectiveBalanceSum state ≤ budget)
    (funded : ∀ balance ∈ state.balances.data, balance.toNat ≤ budget)
    (finalized : FinalizedSettled state) (resolved : PendingResolved state)
    (wellFormed : PendingWellFormed state) :
    ∃ after, processRewardsAndPenalties config state = .ok after := by
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · exact ⟨state, processRewardsAndPenalties_genesis config genesis⟩
  have budgetLt : budget < 2 ^ 64 := fit.budget_lt
  have rewardsFit := fit.rewards
  have penaltiesFit := fit.penalties
  rw [Nat.mul_assoc] at rewardsFit
  obtain ⟨total, totalOk, low, -⟩ :=
    getTotalActiveBalance_exists_ok within (Nat.lt_of_le_of_lt summed budgetLt)
  -- Each base reward succeeds, at most its bound, and so at most the bound at the largest cap.
  have baseAt : ∀ (index : ValidatorIndex) (validator : Validator),
      state.validators.data[index.toNat]? = some validator →
      ∃ base, getBaseReward state total index = .ok base ∧
        base.toNat ≤ preset.baseRewardBoundBeforeAltair validator.effectiveBalance.toNat :=
    fun index validator found => getBaseReward_le_of_lt_altair before positive.increment
      fit.product low found (capped _ (Array.mem_of_getElem? found))
  have baseOk : ∀ index : ValidatorIndex, index.toNat < state.validators.data.size →
      ∃ base, getBaseReward state total index = .ok base ∧
        base.toNat ≤ preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance :=
    fun index lt => by
      obtain ⟨base, based, baseLe⟩ := baseAt index _ (Array.getElem?_eq_getElem lt)
      exact ⟨base, based,
        le_trans baseLe (baseRewardBoundBeforeAltair_mono (capped _ (Array.getElem_mem lt)))⟩
  have one := one_le_budgetIncrements positive.increment budget
  have productFits : preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance *
      preset.budgetIncrements budget < 2 ^ 64 := by omega
  -- The source, target and head deltas read the matching votes of the previous epoch.
  have previousResolved : ∀ attestation ∈ (state.previousEpochAttestations before).data,
      ∃ signers, getPendingAttestingIndices state attestation = .ok signers :=
    fun attestation member => resolved before attestation (.inl member)
  have sourceOk := getMatchingSourceAttestations_eq_ok (state := state) before (.inl rfl)
  rw [previousSource_eq before genesis] at sourceOk
  obtain ⟨target, targetOk, targetIn⟩ := getMatchingTargetAttestations_exists_ok before
    (.inl rfl) (getBlockRoot_exists_ok roots last room (.inl rfl))
  simp only [previousSource_eq before genesis] at targetIn
  obtain ⟨head, headOk, headIn⟩ :=
    getMatchingHeadAttestations_previous before roots last room genesis wellFormed
  obtain ⟨sourceRewards, sourcePenalties, sourceDeltas, sourceLe⟩ :=
    getAttestationComponentDeltas_exists_le within summed budgetLt finalized totalOk baseOk one
      productFits previousResolved
  obtain ⟨targetRewards, targetPenalties, targetDeltas, targetLe⟩ :=
    getAttestationComponentDeltas_exists_le within summed budgetLt finalized totalOk baseOk one
      productFits fun attestation member => previousResolved attestation (targetIn _ member)
  obtain ⟨headRewards, headPenalties, headDeltas, headLe⟩ :=
    getAttestationComponentDeltas_exists_le within summed budgetLt finalized totalOk baseOk one
      productFits fun attestation member => previousResolved attestation (headIn _ member)
  obtain ⟨inclusionRewards, inclusionPenalties, inclusionOk, inclusionLe⟩ :=
    getInclusionDelayDeltas_exists_le before genesis within summed (by omega) totalOk baseAt
      resolved wellFormed
  obtain ⟨inactivityRewards, inactivityPenalties, inactivityOk, inactivityLe⟩ :=
    getInactivityPenaltyDeltas_exists_le (config := config) before roots last room horizon within
      capped finalized resolved totalOk baseOk (by omega)
  -- The sums of the rewards and of the penalties fit.
  have sizes := getAttestationComponentDeltas_size sourceDeltas
  obtain ⟨rewards, rewardsOk⟩ := sumDeltas_exists_ok (first := sourceRewards)
    (second := targetRewards) (third := headRewards) (fourth := inclusionRewards) fun j lt => by
      rw [sizes.1] at lt
      have := (sourceLe j lt).1
      have := (targetLe j lt).1
      have := (headLe j lt).1
      have := inclusionLe j
      omega
  obtain ⟨penalties, penaltiesOk⟩ := sumDeltas_exists_ok (first := sourcePenalties)
    (second := targetPenalties) (third := headPenalties) (fourth := inactivityPenalties)
    fun j lt => by
      rw [sizes.2] at lt
      have := (sourceLe j lt).2
      have := (targetLe j lt).2
      have := (headLe j lt).2
      have := inactivityLe j lt
      omega
  have deltasOk : getAttestationDeltas config state before = .ok (rewards, penalties) := by
    simp only [getAttestationDeltas, getSourceDeltas, getTargetDeltas, getHeadDeltas, sourceOk,
      targetOk, headOk, sourceDeltas, targetDeltas, headDeltas, inclusionOk, inactivityOk,
      rewardsOk, penaltiesOk, bind, Except.bind, pure, Except.pure]
  -- Each balance plus its reward fits, so the deltas apply.
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt within preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  obtain ⟨after, applied⟩ := applyAllDeltas_exists_ok (rewards := rewards)
    (penalties := penalties) matched small fun i inside => by
      have inRegistry : i < state.validators.data.size := by
        unfold BalancesMatch at matched
        omega
      have entry := sumDeltas_getD rewardsOk i
      simp only [show i < sourceRewards.size from sizes.1 ▸ inRegistry, ↓reduceIte] at entry
      have := funded _ (Array.getElem_mem inside)
      have := (sourceLe i inRegistry).1
      have := (targetLe i inRegistry).1
      have := (headLe i inRegistry).1
      have := inclusionLe i
      omega
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  refine ⟨after, ?_⟩
  simp only [processRewardsAndPenalties, genesis, notAltair, ↓reduceIte, ↓reduceDIte, deltasOk,
    bind, Except.bind]
  exact applied

end EthLib.Consensus
