module

public import EthLib.Consensus.Proofs.Transition.TargetFlags
public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
import EthLib.Consensus.Proofs.Transition.BlockRewards

/-!
# Proofs: an attestation that meets its checks is accepted, and flags its attesters

From Altair an attestation in a block passes checks, then sets flags and pays the proposer.

Its target must be the epoch of its slot, and the current or the previous epoch of the state.

It must come at least the least inclusion delay after its slot, and before Deneb within one epoch.

Its bits must fit its committees, and its source must be the justified checkpoint of its target.

Its indexed form must pass the signature check.

The rest of the step reads the state and adds rewards with checked arithmetic.

Under a budget on the balances with room for the rewards, none of it fails.

Each attester then holds the timely target flag, when the target root is the root of its epoch.

That is the root that the state holds for the first slot of the target epoch.

This is the step of plausible liveness that makes honest votes count.

Casper FFG states that property as its Theorem 2.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).

From Gloas the step also weighs a payment of the builder, which these theorems leave out.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state : BeaconState preset fork}

/-- One flag of one attester succeeds when its base reward is read and the sum fits.

The numerator then grows by at most the base reward times the weight of the flag. -/
private theorem addFlagReward_exists_ok {total base : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} (based : getBaseReward state total index = .ok base)
    (flags : ParticipationFlags) (numerator : Gwei) (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length)
    (fits : numerator.toNat + base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat < 2 ^ 64) :
    ∃ flags' numerator', addFlagReward state total earned index (flags, numerator) flag =
        .ok (flags', numerator') ∧
      numerator'.toNat ≤ numerator.toNat + base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat := by
  have weighted : base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat < 2 ^ 64 := by omega
  have product : (base * PARTICIPATION_FLAG_WEIGHTS[flag]).toNat =
      base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt weighted]
  unfold addFlagReward
  dsimp only
  split
  · -- A newly set flag adds the weighted base reward, which fits by assumption.
    refine ⟨addFlag flags flag.val.toUInt64, numerator + base * PARTICIPATION_FLAG_WEIGHTS[flag],
      ?_, ?_⟩
    · simp only [based, liftAccessor, liftArith, mulChecked_of_lt weighted,
        addChecked_of_lt (product ▸ fits), Except.mapError, bind, Except.bind, pure, Except.pure]
    · rw [toNat_add_of_lt (product ▸ fits), product]
  · exact ⟨flags, numerator, rfl, by omega⟩

/-- The flags of one attester, set in turn, succeed when its base reward is read and the sum fits.

The numerator then grows by at most the base reward times the weights of the flags. -/
private theorem foldlM_addFlagReward_exists_ok {total base : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} (based : getBaseReward state total index = .ok base) :
    ∀ (flagList : List (Fin PARTICIPATION_FLAG_WEIGHTS.length)) (flags : ParticipationFlags)
      (numerator : Gwei),
      numerator.toNat + base.toNat * (flagList.map (PARTICIPATION_FLAG_WEIGHTS[·].toNat)).sum <
        2 ^ 64 →
      ∃ flags' numerator', flagList.foldlM (addFlagReward state total earned index)
          (flags, numerator) = .ok (flags', numerator') ∧
        numerator'.toNat ≤ numerator.toNat +
          base.toNat * (flagList.map (PARTICIPATION_FLAG_WEIGHTS[·].toNat)).sum
  | [], flags, numerator, _ => ⟨flags, numerator, rfl, by simp⟩
  | flag :: rest, flags, numerator, fits => by
    rw [List.map_cons, List.sum_cons, Nat.mul_add] at fits ⊢
    obtain ⟨middleFlags, middle, stepped, grown⟩ :=
      addFlagReward_exists_ok (earned := earned) based flags numerator flag (by omega)
    obtain ⟨flags', numerator', folded, bound⟩ :=
      foldlM_addFlagReward_exists_ok based rest middleFlags middle (by omega)
    refine ⟨flags', numerator', ?_, by omega⟩
    rw [List.foldlM_cons, stepped]
    exact folded

/-- The weights of the three flags sum to 54, at most the weight denominator 64. -/
private theorem flagWeights_sum_le :
    ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map
      (PARTICIPATION_FLAG_WEIGHTS[·].toNat)).sum ≤ 64 := by
  decide

/-- The flags of one attester of the list succeed when its base reward is read and the sum fits.

The list keeps its size, and the numerator grows by at most 64 times the base reward. -/
private theorem addAttesterFlags_exists_ok {total base : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} (based : getBaseReward state total index = .ok base)
    (participation : EpochParticipation preset fork) (numerator : Gwei)
    (inside : index.toNat < participation.data.size)
    (fits : numerator.toNat + 64 * base.toNat < 2 ^ 64) :
    ∃ updated numerator', addAttesterFlags state total earned (participation, numerator) index =
        .ok (updated, numerator') ∧ updated.data.size = participation.data.size ∧
      numerator'.toNat ≤ numerator.toNat + 64 * base.toNat := by
  have scaled := Nat.mul_le_mul_left base.toNat flagWeights_sum_le
  obtain ⟨flags, numerator', folded, bound⟩ := foldlM_addFlagReward_exists_ok (earned := earned)
    based (List.finRange PARTICIPATION_FLAG_WEIGHTS.length) participation.data[index.toNat]
    numerator (by omega)
  refine ⟨⟨participation.data.set index.toNat flags inside,
    fun before => by simpa using participation.bound before⟩, numerator', ?_, by simp, by omega⟩
  simp only [addAttesterFlags, inside, ↓reduceDIte, bind, Except.bind, pure, Except.pure]
  rw [folded]

/-- The flags of attesters of the registry, set in turn, succeed when the numerator stays small.

Each attester must have a base reward of at most a ceiling, and the list of flags the registry size.

The numerator grows by at most 64 times the ceiling for each attester. -/
private theorem foldlM_addAttesterFlags_exists_ok {total : Gwei} {earned : List UInt64}
    {size ceiling : Nat}
    (baseOk : ∀ index : ValidatorIndex, index.toNat < size →
      ∃ base, getBaseReward state total index = .ok base ∧ base.toNat ≤ ceiling) :
    ∀ (attesters : List ValidatorIndex) (participation : EpochParticipation preset fork)
      (numerator : Gwei), participation.data.size = size →
      (∀ attester ∈ attesters, attester.toNat < size) →
      numerator.toNat + attesters.length * (64 * ceiling) < 2 ^ 64 →
      ∃ updated numerator', attesters.foldlM (addAttesterFlags state total earned)
          (participation, numerator) = .ok (updated, numerator') ∧
        numerator'.toNat ≤ numerator.toNat + attesters.length * (64 * ceiling)
  | [], participation, numerator, _, _, _ => ⟨participation, numerator, rfl, by simp⟩
  | attester :: rest, participation, numerator, sized, inside, fits => by
    rw [List.length_cons, Nat.add_mul] at fits ⊢
    obtain ⟨base, based, baseLe⟩ := baseOk attester (inside attester List.mem_cons_self)
    have scaled : 64 * base.toNat ≤ 64 * ceiling := Nat.mul_le_mul_left 64 baseLe
    obtain ⟨middle, middleNumerator, stepped, middleSize, grown⟩ :=
      addAttesterFlags_exists_ok (earned := earned) based participation numerator
        (sized ▸ inside attester List.mem_cons_self) (by omega)
    obtain ⟨updated, numerator', folded, bound⟩ :=
      foldlM_addAttesterFlags_exists_ok baseOk rest middle middleNumerator
        (middleSize.trans sized) (fun other member => inside other (List.mem_cons_of_mem _ member))
        (by omega)
    refine ⟨updated, numerator', ?_, by omega⟩
    rw [List.foldlM_cons, stepped]
    exact folded

/-- From Altair, under a budget each validator of the registry has a base reward up to a ceiling.

The total must be at least one positive increment, and the ceiling must fit in 64 bits. -/
private theorem getBaseReward_exists_le {budget scoreBound : Nat} (altair : .altair ≤ fork)
    (holds : WithinBudget budget scoreBound state)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (fits : preset.baseRewardCeiling < 2 ^ 64) {total : Gwei}
    (low : preset.EFFECTIVE_BALANCE_INCREMENT ≤ total) (index : ValidatorIndex)
    (inside : index.toNat < state.validators.data.size) :
    ∃ base, getBaseReward state total index = .ok base ∧ base.toNat ≤ preset.baseRewardCeiling := by
  obtain ⟨per, perOk, perLe⟩ := getBaseRewardPerIncrement_le increment scaled low
  have capped := holds.capped _ (Array.getElem_mem inside)
  exact getBaseReward_le altair perOk perLe fits (Array.getElem?_eq_getElem inside)
    ((UInt64.le_iff_toNat_le.mp capped).trans
      (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork _))

/-- A valid indexed attestation names only validators of the registry.

Its signature check reads the key of each of them. -/
private theorem isValidIndexedAttestation_lt_size {indexed : IndexedAttestation preset fork}
    (valid : isValidIndexedAttestation config checks state indexed = .ok true) :
    ∀ index ∈ indexed.attestingIndices.data.toList,
      index.toNat < state.validators.data.size := by
  intro index member
  obtain ⟨pubkeys, -, -, keysOk, -⟩ := isValidIndexedAttestation_signature valid
  rw [Array.mapM_eq_mapM_toList] at keysOk
  change (do
    let keys ← indexed.attestingIndices.data.toList.mapM
      (fun index => do return (← liftAccessor (getValidator state index)).pubkey)
    pure keys.toArray) = .ok _ at keysOk
  obtain ⟨keys, mapped, -⟩ := bind_ok_iff.mp keysOk
  -- The key of the index is read, so its validator is found.
  obtain ⟨key, computed⟩ := mapM_ok_of_mem mapped index member
  obtain ⟨validator, found, -⟩ := bind_ok_iff.mp computed
  exact (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp (liftAccessor_ok.mp found))).1

/-- Distinct indices below a size are at most that many. -/
private theorem length_le_of_nodup {indices : List ValidatorIndex} {size : Nat}
    (distinct : (indices.map UInt64.toNat).Nodup)
    (inside : ∀ index ∈ indices, index.toNat < size) : indices.length ≤ size := by
  have sub := List.subperm_of_subset (l₂ := List.range size) distinct fun n member => by
    obtain ⟨index, chosen, rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (inside index chosen)
  simpa using sub.length_le

/-- Before Gloas, the flags of a vote with the right source are earned when two roots are read.

They are the root of its target epoch and the root of its slot.

The target flag is among them when the target root matches.

Before Deneb its inclusion delay must also be at most one epoch. -/
private theorem getAttestationParticipationFlagIndices_target {data : AttestationData}
    {inclusionDelay : UInt64} {parentSlot : Slot} {root headRoot : Root}
    (beforeGloas : fork < .glamsterdam)
    (rootOk : getBlockRoot state data.target.epoch = .ok root)
    (headOk : getBlockRootAtSlot state data.slot = .ok headRoot)
    (source : data.source = if data.target.epoch = getCurrentEpoch state then
        state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint)
    (timely : fork < .dencun → inclusionDelay ≤ preset.SLOTS_PER_EPOCH) :
    ∃ earned, getAttestationParticipationFlagIndices state data inclusionDelay parentSlot =
        .ok earned ∧ (data.target.root = root → TIMELY_TARGET_FLAG_INDEX ∈ earned) := by
  have notGloas : ¬.glamsterdam ≤ fork := Nat.not_le.mpr beforeGloas
  simp only [getAttestationParticipationFlagIndices, rootOk, headOk, notGloas, ↓reduceDIte,
    ← source]
  refine ⟨_, rfl, fun same => ?_⟩
  -- From Deneb the delay does not count, and before it is at most one epoch.
  have onTime : (decide (Fork.dencun ≤ fork) ||
      decide (inclusionDelay ≤ preset.SLOTS_PER_EPOCH)) = true := by
    by_cases dencun : Fork.dencun ≤ fork
    · simp [dencun]
    · simp [timely (Nat.lt_of_not_le dencun)]
  simp [same, onTime]

/-- From Altair, the flags of an epoch just written are read back after a balance is set. -/
private theorem recentParticipation_putBalance_setEpochParticipation (altair : .altair ≤ fork)
    (current : Bool) (updated : EpochParticipation preset fork) (index : Nat)
    (inside : index < (setEpochParticipation state current updated).balances.data.size)
    (balance : Gwei) :
    recentParticipation ((setEpochParticipation state current updated).putBalance index inside
      balance) altair current = updated := by
  cases current <;> rfl

/-- From Altair until Gloas, an attestation that meets the checks of its step is accepted.

Its target is the epoch of its slot, and the current or the previous epoch of the state.

It comes after its slot, and at least the least inclusion delay after it.

Before Deneb it also comes within one epoch of its slot.

Its bits fit its committees, and its source is the justified checkpoint of its target epoch.

Its indexed form passes the signature check.

The committee check and the signature check are hypotheses here.

The state is within a budget, and the proposer of its slot is a validator of the registry.

Each list of participation flags has one entry for each validator.

The buffer of block roots must reach the previous epoch, and the slot plus its length must fit.

The increment of effective balance is positive, and its product with the reward factor fits.

The budget plus 64 times the base reward ceiling for each validator must fit in 64 bits.

Then each attester holds the timely target flag in the epoch of the target, when the root matches.

That root is the root of the block at the first slot of the target epoch. -/
theorem processAttestation_exists_ok {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    {attestation : Attestation preset fork} (parentSlot : Slot)
    (roots : preset.RootsReachPreviousEpoch)
    (slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    (room : budget + state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (recent : attestation.data.target.epoch = getPreviousEpoch state ∨
      attestation.data.target.epoch = getCurrentEpoch state)
    (slotEpoch : attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot)
    (past : attestation.data.slot.toNat < state.slot.toNat)
    (early : attestation.data.slot.toNat + preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤
      state.slot.toNat)
    (deadline : fork < .dencun →
      state.slot.toNat ≤ attestation.data.slot.toNat + preset.SLOTS_PER_EPOCH.toNat)
    (committees : checkAttestationCommittees state attestation = .ok ())
    (source : attestation.data.source =
      if attestation.data.target.epoch = getCurrentEpoch state then
        state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint)
    (valid : ∃ indexed, getIndexedAttestation state attestation = .ok indexed ∧
      isValidIndexedAttestation config checks state indexed = .ok true)
    (proposer : ∃ index, getBeaconProposerIndex state = .ok index ∧
      index.toNat < state.validators.data.size) :
    ∃ after, processAttestation config checks state parentSlot attestation = .ok after ∧
      ∀ attesters, getAttestingIndices state attestation = .ok attesters →
        getBlockRoot state attestation.data.target.epoch = .ok attestation.data.target.root →
        ∀ attester ∈ attesters, TargetFlagAt (recentParticipation after altair
          (attestation.data.target.epoch == getCurrentEpoch state)) attester.toNat := by
  rw [processAttestation_of_altair altair]
  set data := attestation.data with dataEq
  have twoSlots := roots.twoSlots
  have reach := roots.reach
  -- The slots of the state, of the attestation and of the start of its target, as numbers.
  have currentNat := getCurrentEpoch_toNat state
  have previousNat := getPreviousEpoch_toNat state
  have targetNat : data.target.epoch.toNat = data.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [slotEpoch]
    simp [computeEpochAtSlot, UInt64.toNat_div]
  have startLe : data.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ data.slot.toNat := by
    rw [targetNat]
    exact Nat.div_mul_le_self _ _
  have stateBelow : state.slot.toNat <
      (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_EPOCH.toNat := by
    rw [currentNat, Nat.mul_comm]
    have := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have := Nat.mod_lt state.slot.toNat (by omega : 0 < preset.SLOTS_PER_EPOCH.toNat)
    omega
  -- The target epoch is at least the previous epoch, so its start is at most an epoch back.
  have startHigh : (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      data.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    have recentNat : (getCurrentEpoch state).toNat ≤ data.target.epoch.toNat + 1 := by
      rcases recent with same | same <;> rw [same] <;> omega
    have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat recentNat
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  obtain ⟨root, rootOk⟩ := getBlockRoot_exists (state := state) (epoch := data.target.epoch)
    (by omega) (by omega) (by omega)
  obtain ⟨headRoot, headOk⟩ := getBlockRootAtSlot_exists (state := state) (slot := data.slot)
    past (by omega) (by omega) (by omega)
  -- The inclusion delay is the difference of the slots, without wrapping.
  have delayNat : (state.slot - data.slot).toNat = state.slot.toNat - data.slot.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
  obtain ⟨earned, earnedOk, targetEarned⟩ := getAttestationParticipationFlagIndices_target
    (inclusionDelay := state.slot - data.slot) (parentSlot := parentSlot) beforeGloas rootOk
    headOk source fun before => UInt64.le_iff_toNat_le.mpr (by
      have := deadline before
      omega)
  obtain ⟨indexed, indexedOk, validOk⟩ := valid
  obtain ⟨attesters, attestersOk, indices⟩ :=
    getAttestingIndices_of_getIndexedAttestation indexedOk
  -- The attesters are distinct validators of the registry, so there are at most that many.
  have inside : ∀ attester ∈ attesters, attester.toNat < state.validators.data.size :=
    fun attester member =>
      isValidIndexedAttestation_lt_size validOk attester (by rw [indices]; simpa using member)
  have distinct := getAttestingIndices_nodup attestersOk
  have counted := Nat.mul_le_mul_right (64 * preset.baseRewardCeiling)
    (length_le_of_nodup distinct inside)
  obtain ⟨proposerIndex, proposerOk, proposerInside⟩ := proposer
  -- The budget bounds the effective balances, so the total active balance is read.
  have budgetLt : budget < 2 ^ 64 := by omega
  obtain ⟨total, totalOk, low, -⟩ := getTotalActiveBalance_exists_ok holds.within
    (Nat.lt_of_le_of_lt holds.effectiveBalanceSum_le budgetLt)
  -- One validator makes the room bound the ceiling of a base reward.
  have ceilingLe : 64 * preset.baseRewardCeiling ≤
      state.validators.data.size * (64 * preset.baseRewardCeiling) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have baseOk := getBaseReward_exists_le altair holds increment scaled (by omega) low
  -- The flags of the epoch of the target have one entry for each validator.
  obtain ⟨previousSize, currentSize⟩ := participation altair
  have sized : (if (data.target.epoch == getCurrentEpoch state) then
      state.currentEpochParticipation altair
    else state.previousEpochParticipation altair).data.size = state.validators.data.size := by
    split <;> assumption
  obtain ⟨updated, numerator, folded, numeratorLe⟩ :=
    foldlM_addAttesterFlags_exists_ok (earned := earned) baseOk attesters _ 0 sized inside
      (by simp only [UInt64.toNat_zero]; omega)
  rw [UInt64.toNat_zero, Nat.zero_add] at numeratorLe
  -- Writing the flags keeps the balances, and the proposer's balance has room for the reward.
  have kept : (setEpochParticipation state (data.target.epoch == getCurrentEpoch state)
      updated).balances = state.balances := by
    unfold setEpochParticipation
    split <;> rfl
  have matched : state.balances.data.size = state.validators.data.size := holds.matched
  have balanceLe := holds.balance_le _ (Array.getElem_mem (xs := state.balances.data)
    (i := proposerIndex.toNat) (by omega))
  have rewardLe : (numerator / ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT)).toNat ≤ numerator.toNat := by
    rw [UInt64.toNat_div]
    exact Nat.div_le_self _ _
  obtain ⟨raised, raisedOk⟩ : ∃ raised, increaseBalance (setEpochParticipation state
      (data.target.epoch == getCurrentEpoch state) updated) proposerIndex
      (numerator / ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
        PROPOSER_WEIGHT)) = .ok raised := by
    generalize setEpochParticipation state (data.target.epoch == getCurrentEpoch state) updated =
      written at kept ⊢
    refine ⟨_, increaseBalance_eq_ok_iff.mpr ⟨by rw [kept]; omega, ?_, rfl⟩⟩
    simp only [kept]
    omega
  -- The earliest slot of inclusion fits, and the slot of the state is past it.
  have earliestOk : addChecked data.slot preset.MIN_ATTESTATION_INCLUSION_DELAY =
      .ok (data.slot + preset.MIN_ATTESTATION_INCLUSION_DELAY) := addChecked_of_lt (by omega)
  have earliestLe : data.slot + preset.MIN_ATTESTATION_INCLUSION_DELAY ≤ state.slot :=
    UInt64.le_iff_toNat_le.mpr (by rw [toNat_add_of_lt (by omega)]; omega)
  -- Before Deneb the slot of the state is within one epoch of the slot, which fits.
  have deadlineOk : checkInclusionDeadline state data.slot = .ok () := by
    by_cases before : fork < .dencun
    · exact (checkInclusionDeadline_ok_iff before).mpr ⟨by omega, deadline before⟩
    · exact checkInclusionDeadline_of_dencun (Nat.le_of_not_lt before)
  have notGloas : ¬.glamsterdam ≤ fork := Nat.not_le.mpr beforeGloas
  refine ⟨raised, ?_, ?_⟩
  · simp only [processAttestationAltair, ← dataEq, ensure, eq_true recent, eq_true slotEpoch,
      liftAccessor, liftArith, earliestOk, eq_true earliestLe, deadlineOk, committees, earnedOk,
      indexedOk, validOk, totalOk, attestersOk, folded,
      getBeaconProposerIndex_setEpochParticipation, proposerOk, raisedOk, notGloas,
      Except.mapError, bind, Except.bind, pure, Except.pure, ↓reduceIte, ↓reduceDIte]
  intro named namedOk matching attester member
  rw [attestersOk, Except.ok.injEq] at namedOk
  subst namedOk
  -- The target root is the root of the chain, so the attestation earns the target flag.
  have target := targetEarned (Except.ok.inj (rootOk.symm.trans matching)).symm
  obtain ⟨_, new, -, found, gained⟩ :=
    foldlM_addAttesterFlags_hasFlag distinct folded attester member
  -- Raising the balance of the proposer keeps the flags just written.
  obtain ⟨_, setOk⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok setOk
  refine ⟨new, ?_, ?_⟩
  · rw [recentParticipation_putBalance_setEpochParticipation]
    exact found
  · -- The attester holds every earned flag, and the target flag is the second one.
    have flagged := gained (⟨1, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length)
    have second : (⟨1, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length).val.toUInt64 =
        TIMELY_TARGET_FLAG_INDEX := rfl
    rw [second] at flagged
    simp [flagged, target]

end EthLib.Consensus
