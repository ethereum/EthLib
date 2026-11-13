module

public import EthLib.Consensus.Proofs.Transition.Totality.EffectiveBalances
public import EthLib.Consensus.Proofs.Transition.Totality.Registry
public import EthLib.Consensus.Proofs.Transition.Totality.RewardsBeforeAltair
public import EthLib.Consensus.Proofs.Transition.Totality.Slashings
public import EthLib.Consensus.Proofs.Transition.Totality.Slot

/-!
# Proofs: the epoch transition succeeds before Altair

Before Altair the epoch transition runs ten steps in a row.

Each step has its own theorem that it succeeds, under hypotheses on the state it reads.

This file reads all of them on the state before the epoch.

Justification and finalization change only the checkpoints and their bits.

The rewards and penalties then change only the balances, and leave each at most a ceiling.

The registry updates keep the balances and every effective balance.

The slashing penalties only lower balances.

So the bounds on the effective balances, the slashed balances and the history carry over.

The balances stay at most that ceiling.

The update of the effective balances needs that ceiling below 2^63.

The resets and the update of the history then need only that the slot plus one fits in 64 bits.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- A step that keeps the slot, the balances, the slashed balances and the historical lists.

It keeps the effective balance at each position of the registry, and so the size of the registry. -/
private def RegistryKept (state after : BeaconState preset fork) : Prop :=
  after.slot = state.slot ∧ after.balances = state.balances ∧ after.slashings = state.slashings ∧
    after.historicalRoots = state.historicalRoots ∧
    after.historicalSummaries = state.historicalSummaries ∧
    after.validators.data.map (·.effectiveBalance) = state.validators.data.map (·.effectiveBalance)

private theorem RegistryKept.refl (state : BeaconState preset fork) : RegistryKept state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem RegistryKept.trans {first second third : BeaconState preset fork}
    (one : RegistryKept first second) (two : RegistryKept second third) :
    RegistryKept first third :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.1.trans one.2.2.2.2.1,
    two.2.2.2.2.2.trans one.2.2.2.2.2⟩

/-- A write of a validator with the effective balance of the old one keeps the registry kept. -/
private theorem registryKept_setValidatorAt {after : BeaconState preset fork} {position : Nat}
    {validator old : Validator} (set : state.setValidatorAt position validator = .ok after)
    (found : getValidatorAt state position = .ok old)
    (same : validator.effectiveBalance = old.effectiveBalance) : RegistryKept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have read := getValidatorAt_eq_ok_iff.mp found
  rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at read
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Array.map_set,
    same, ← read]
  rw [← Array.getElem_map (f := fun x : Validator => x.effectiveBalance)]
  exact Array.set_getElem_self _

/-- The start of an exit changes only the epochs of one validator and the queue of exits. -/
private theorem registryKept_initiateValidatorExit {config : Config}
    {after : BeaconState preset fork} {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    RegistryKept state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact RegistryKept.refl _
  obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
  rw [setValidator_eq_setValidatorAt] at set
  rw [getValidator_eq_getValidatorAt] at found
  have last := registryKept_setValidatorAt (old := validator) set (by exact found) rfl
  exact RegistryKept.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ last

/-- Before Electra, the registry updates keep the slot and the balances.

They keep the slashed balances, the historical roots and the historical summaries.

They keep the effective balance at each position of the registry. -/
theorem processRegistryUpdates_registryKept {config : Config} {after : BeaconState preset fork}
    (before : fork < .pectra) (computed : processRegistryUpdates config state = .ok after) :
    after.slot = state.slot ∧ after.balances = state.balances ∧
      after.slashings = state.slashings ∧ after.historicalRoots = state.historicalRoots ∧
      after.historicalSummaries = state.historicalSummaries ∧
      after.validators.data.map (·.effectiveBalance) =
        state.validators.data.map (·.effectiveBalance) := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  unfold processRegistryUpdates at computed
  simp only [notElectra, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  -- Each entry joins the queue, which sets only its eligibility epoch, and may start an exit.
  have first := foldlM_ok_invariant (RegistryKept state) (fun middle index next before ok => by
    refine before.trans ?_
    simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, queued, queuedOk, marked, markedOk, ok⟩ := ok
    have same : queued.effectiveBalance = validator.effectiveBalance := by
      unfold queueForActivation at queuedOk
      split at queuedOk
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
        obtain ⟨_, _, rfl⟩ := queuedOk
        rfl
      · simp only [pure, Except.pure, Except.ok.injEq] at queuedOk
        rw [queuedOk]
    have set := registryKept_setValidatorAt markedOk found same
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact set.trans (registryKept_initiateValidatorExit exited)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ set) (RegistryKept.refl state) updatedOk
  -- Each activation sets only an activation epoch.
  exact foldlM_ok_invariant (RegistryKept state) (fun middle index next before ok => by
    refine before.trans ?_
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, _, _, set⟩ := ok
    rw [setValidator_eq_setValidatorAt] at set
    rw [getValidator_eq_getValidatorAt] at found
    exact registryKept_setValidatorAt set found rfl) first activated

/-- Two registries with the same effective balances at each position have the same sum of them. -/
theorem effectiveBalanceSum_eq_of_map {other : BeaconState preset fork}
    (same : other.validators.data.map (·.effectiveBalance) =
      state.validators.data.map (·.effectiveBalance)) :
    effectiveBalanceSum other = effectiveBalanceSum state := by
  unfold effectiveBalanceSum
  have := congrArg (fun balances : Array Gwei => (balances.toList.map UInt64.toNat).sum) same
  simpa [Array.toList_map, List.map_map, Function.comp_def] using this

/-- Two registries with the same effective balances hold the same effective balances. -/
theorem exists_effectiveBalance_of_map {other : BeaconState preset fork} {validator : Validator}
    (same : other.validators.data.map (·.effectiveBalance) =
      state.validators.data.map (·.effectiveBalance))
    (member : validator ∈ other.validators.data) :
    ∃ old ∈ state.validators.data, old.effectiveBalance = validator.effectiveBalance := by
  have mapped : validator.effectiveBalance ∈ other.validators.data.map (·.effectiveBalance) :=
    Array.mem_map_of_mem member
  rw [same] at mapped
  exact Array.mem_map.mp mapped

/-- Each effective balance is at most the sum of the effective balances. -/
theorem effectiveBalance_le_effectiveBalanceSum {validator : Validator}
    (member : validator ∈ state.validators.data) :
    validator.effectiveBalance.toNat ≤ effectiveBalanceSum state :=
  List.le_sum_of_mem (List.mem_map_of_mem (Array.mem_toList_iff.mpr member))

/-- Two states with the same registry and RANDAO mixes agree on the signers of a pending vote. -/
private theorem getPendingAttestingIndices_eq_of_eq {other : BeaconState preset fork}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes.elements = state.randaoMixes.elements)
    (attestation : PendingAttestation preset) :
    getPendingAttestingIndices other attestation =
      getPendingAttestingIndices state attestation := by
  unfold getPendingAttestingIndices getBeaconCommittee attesterShuffle getCommitteeCountPerSlot
    getActiveValidatorIndices getActiveValidatorIndicesChecked getSeed getRandaoMix
  simp only [validators, mixes]

/-- Before Altair, the epoch transition succeeds under bounds.

The transition must run at the last slot of an epoch.

The current epoch must be at most the epoch bound.

The rewards and penalties must fit in 64 bits under the budget and the epoch bound.

An epoch of the preset must have two slots at least.

The buffer of block roots of the preset must reach the epoch before.

The slot plus the length of that buffer must be below 2^64.

The registry must stay within its limit, with one balance for each validator.

Each effective balance must be at most the largest cap.

The sum of the effective balances and each balance must be at most the budget.

One increment plus the sum of the effective balances, times three, must be below 2^64.

The ceiling of the balances after the rewards must be below 2^63.

The finalized, previous justified and current justified epochs must be in order.

The current justified epoch must be at most the previous epoch.

The committee and the signers of each recent pending attestation must succeed.

Each recent pending attestation must be as inclusion in a block stored it.

An epoch must bound the first activation epoch and every finite exit epoch.

That epoch plus the registry size plus the withdrawability delay must be below 2^64.

The sum of the slashed balances must be below 2^64, and so must that sum times the multiplier.

The current epoch plus half the length of the slashings vector must be below 2^64.

Each effective balance in increments, times the sum of the effective balances, must be below 2^64.

The list of historical roots must have room for one more entry.

The divisors of the preset must be positive, and its hysteresis bands below 2^63.

Its circular buffers of slashed balances and of RANDAO mixes must have positive length. -/
theorem processEpoch_total_of_lt_altair {config : Config} {checks : SignatureChecks}
    {budget epochBound ceiling : Nat}
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    (before : fork < .altair) (positive : preset.DivisorsPositive)
    (roots : preset.RootsReachPreviousEpoch) (bands : preset.HysteresisBandsBelow)
    (fit : RewardsFitBeforeAltair preset budget epochBound)
    (half : preset.rewardsCeilingBeforeAltair budget < 2 ^ 63)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (horizon : (getCurrentEpoch state).toNat ≤ epochBound)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance)
    (summed : effectiveBalanceSum state ≤ budget)
    (tripled : 3 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state) < 2 ^ 64)
    (funded : ∀ balance ∈ state.balances.data, balance.toNat ≤ budget)
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    (resolved : PendingResolved state) (wellFormed : PendingWellFormed state)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (exitRoom : ceiling + state.validators.data.size +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64)
    (slashedFits : slashedBalanceSum state < 2 ^ 64)
    (slashedProduct : slashedBalanceSum state *
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat < 2 ^ 64)
    (halfway : (getCurrentEpoch state).toNat + (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat <
      2 ^ 64)
    (product : ∀ validator ∈ state.validators.data,
      (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
        effectiveBalanceSum state < 2 ^ 64)
    (history : state.historicalRoots.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat) :
    ∃ after, processEpoch config checks state = .ok after := by
  have notAltair : ¬ Fork.altair ≤ fork := Nat.not_le_of_lt before
  have electra : fork < .pectra := Nat.lt_trans before (by decide)
  have hegota : fork < .hegota := Nat.lt_trans before (by decide)
  have capella : fork < .shapella := Nat.lt_trans before (by decide)
  have next : state.slot.toNat + 1 < 2 ^ 64 := by
    have := roots.reach
    have := roots.twoSlots
    omega
  have budgetLe : budget ≤ preset.rewardsCeilingBeforeAltair budget := by
    unfold Preset.rewardsCeilingBeforeAltair
    omega
  -- Justification and finalization change only the checkpoints and their bits.
  obtain ⟨justified, justifiedOk⟩ := processJustificationAndFinalization_total roots last room
    within ordered settled tripled (fun altair => absurd altair notAltair) resolved
  have kept1 : justified.slot = state.slot ∧ justified.validators = state.validators ∧
      justified.balances = state.balances ∧ justified.randaoMixes = state.randaoMixes ∧
      justified.slashings = state.slashings ∧ justified.historicalRoots = state.historicalRoots ∧
      justified.previousEpochAttestations = state.previousEpochAttestations ∧
      justified.currentEpochAttestations = state.currentEpochAttestations := by
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      rw [← rest]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨slot1, validators1, balances1, mixes1, slashings1, roots1, previous1, current1⟩ := kept1
  have currentEpoch1 : getCurrentEpoch justified = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot1]
  have previousEpoch1 : getPreviousEpoch justified = getPreviousEpoch state := by
    simp only [getPreviousEpoch, currentEpoch1]
  have resolved1 : PendingResolved justified := by
    intro early attestation member
    rw [previous1, current1] at member
    rw [getPendingAttestingIndices_eq_of_eq (other := justified) (state := state)
      (by rw [validators1]) (by rw [mixes1])]
    exact resolved early attestation member
  have wellFormed1 : PendingWellFormed justified := by
    intro early
    simp only [previous1, current1, previousEpoch1, currentEpoch1, validators1]
    exact wellFormed early
  -- The rewards and penalties change only the balances, each to at most the ceiling.
  have matched1 : BalancesMatch justified := by
    unfold BalancesMatch at matched ⊢
    rw [balances1, validators1]
    exact matched
  obtain ⟨rewarded, rewardedOk, ceilinged⟩ := processRewardsAndPenalties_total_of_lt_altair
    (config := config) before positive roots fit (by rw [slot1]; exact last)
    (by rw [slot1]; exact room) (by rw [currentEpoch1]; exact horizon)
    (by unfold BeaconState.RegistryWithinLimit; rw [validators1]; exact within) matched1
    (by rw [validators1]; exact capped)
    (by unfold effectiveBalanceSum; rw [validators1]; exact summed)
    (by rw [balances1]; exact funded)
    (processJustificationAndFinalization_finalizedSettled ordered settled justifiedOk) resolved1
    wellFormed1
  have frame2 := processRewardsAndPenalties_frame rewardedOk
  have validators2 : rewarded.validators = state.validators :=
    (congrArg BeaconState.validators frame2).trans validators1
  have slot2 : rewarded.slot = state.slot := (congrArg BeaconState.slot frame2).trans slot1
  have slashings2 : rewarded.slashings = state.slashings :=
    (congrArg BeaconState.slashings frame2).trans slashings1
  have roots2 : rewarded.historicalRoots = state.historicalRoots :=
    (congrArg BeaconState.historicalRoots frame2).trans roots1
  have matched2 : BalancesMatch rewarded :=
    (frame_processRewardsAndPenalties rewardedOk).balancesMatch matched1
  have currentEpoch2 : getCurrentEpoch rewarded = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot2]
  -- The registry updates change only the epochs of the validators.
  obtain ⟨registered, registeredOk, -⟩ := processRegistryUpdates_total_of_lt_electra
    (config := config) rewarded electra ceiling (by rw [currentEpoch2]; exact first)
    (by rw [validators2]; exact exits) (by rw [validators2]; exact exitRoom)
  obtain ⟨slot3, balances3, slashings3, roots3, -, effective3⟩ :=
    processRegistryUpdates_registryKept electra registeredOk
  rw [validators2] at effective3
  have size3 : registered.validators.data.size = state.validators.data.size := by
    simpa using congrArg Array.size effective3
  have sum3 : effectiveBalanceSum registered = effectiveBalanceSum state :=
    effectiveBalanceSum_eq_of_map effective3
  have currentEpoch3 : getCurrentEpoch registered = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot3, slot2]
  have below3 : ∀ validator ∈ registered.validators.data,
      validator.effectiveBalance.toNat < 2 ^ 63 := by
    intro validator member
    obtain ⟨old, oldMember, same⟩ := exists_effectiveBalance_of_map effective3 member
    have := effectiveBalance_le_effectiveBalanceSum oldMember
    rw [same] at this
    omega
  have matched3 : BalancesMatch registered := by
    unfold BalancesMatch at matched2 ⊢
    rw [balances3, size3, matched2, validators2]
  -- The slashing penalties only lower balances.
  obtain ⟨slashed, slashedOk⟩ := processSlashings_total positive
    (by unfold BeaconState.RegistryWithinLimit; rw [size3]; exact within) matched3
    (by rw [sum3]; have := fit.budget_lt; omega) below3
    (by unfold slashedBalanceSum; rw [slashings3, slashings2]; exact slashedFits)
    (by unfold slashedBalanceSum; rw [slashings3, slashings2]; exact slashedProduct)
    (by rw [currentEpoch3]; exact halfway)
    (fun _ validator member => by
      obtain ⟨old, oldMember, same⟩ := exists_effectiveBalance_of_map effective3 member
      rw [sum3, ← same]
      exact product old oldMember)
  have frame4 := processSlashings_frame slashedOk
  have matched4 : BalancesMatch slashed :=
    (frame_processSlashings slashedOk).balancesMatch matched3
  have lowered4 : ∀ balance ∈ slashed.balances.data,
      balance.toNat ≤ preset.rewardsCeilingBeforeAltair budget := by
    obtain ⟨_, _, _, _, _, each⟩ := processSlashings_balances_toNat_of_lt_electra electra slashedOk
    intro balance member
    obtain ⟨i, inside, rfl⟩ := Array.getElem_of_mem member
    by_cases inRegistry : i < registered.validators.data.size
    · obtain ⟨_, _, mapped⟩ := (each i).1 inRegistry
      rw [Array.getElem?_eq_getElem inside] at mapped
      cases read : registered.balances.data[i]? with
      | none => simp [read] at mapped
      | some old =>
        simp only [read, Option.map_some, Option.some.injEq] at mapped
        have := ceilinged old (by rw [← balances3]; exact Array.mem_of_getElem? read)
        omega
    · have past := (each i).2 (Nat.le_of_not_lt inRegistry)
      rw [Array.getElem?_eq_getElem inside] at past
      exact ceilinged _ (by rw [← balances3]; exact Array.mem_of_getElem? past.symm)
  -- The reset of the deposit votes changes only those votes.
  obtain ⟨reset, resetOk⟩ := processEth1DataReset_total hegota
    (by rw [(frame_processSlashings slashedOk).slot, slot3, slot2]; exact next)
  have frame5 := processEth1DataReset_frame resetOk
  have balances5 : reset.balances = slashed.balances :=
    (congrArg BeaconState.balances frame5).trans rfl
  have validators5 : reset.validators = registered.validators :=
    (congrArg BeaconState.validators frame5).trans <|
      (congrArg BeaconState.validators frame4).trans rfl
  -- The effective balances move toward the balances, which stay below 2^63.
  obtain ⟨updated, updatedOk⟩ := processEffectiveBalanceUpdates_total bands
    (by unfold BalancesMatch at matched4 ⊢; rw [balances5, validators5, matched4,
      ← congrArg BeaconState.validators frame4])
    (fun balance member => by
      rw [balances5] at member
      have := lowered4 balance member
      omega)
    (by rw [validators5]; exact below3)
  have frame6 := processEffectiveBalanceUpdates_frame updatedOk
  have slot6 : updated.slot = state.slot :=
    (congrArg BeaconState.slot frame6).trans <| (congrArg BeaconState.slot frame5).trans <|
      (congrArg BeaconState.slot frame4).trans (slot3.trans slot2)
  have roots6 : updated.historicalRoots = state.historicalRoots :=
    (congrArg BeaconState.historicalRoots frame6).trans <|
      (congrArg BeaconState.historicalRoots frame5).trans <|
      (congrArg BeaconState.historicalRoots frame4).trans (roots3.trans roots2)
  -- The resets and the update of the history need only a next slot.
  obtain ⟨cleared, clearedOk⟩ := processSlashingsReset_total (state := updated)
    (by rw [slot6]; exact next)
  obtain ⟨_, _, _, _, frame7⟩ := processSlashingsReset_eq clearedOk
  obtain ⟨mixed, mixedOk⟩ := processRandaoMixesReset_total (state := cleared)
    (by rw [frame7]; exact slot6 ▸ next)
  obtain ⟨_, _, _, _, _, _, frame8⟩ := processRandaoMixesReset_eq mixedOk
  obtain ⟨recorded, recordedOk⟩ := processHistoricalRootsUpdate_total (state := mixed) capella
    (by rw [frame8, frame7]; exact slot6 ▸ next)
    (by rw [frame8, frame7]; exact roots6 ▸ history)
  obtain ⟨rotated, rotatedOk, -⟩ := processParticipationRecordUpdates_eq (state := recorded) before
  refine ⟨rotated, ?_⟩
  simp only [processEpoch, notAltair, ↓reduceDIte, justifiedOk, rewardedOk, registeredOk,
    slashedOk, resetOk, updatedOk, clearedOk, mixedOk, recordedOk, rotatedOk, bind, Except.bind]

end EthLib.Consensus
