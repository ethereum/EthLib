module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
public import EthLib.Consensus.Proofs.Transition.EpochDecomposition
public import EthLib.Consensus.Proofs.Transition.Totality.EpochBeforeAltair
public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
public import EthLib.Consensus.Proofs.Transition.Totality.SyncCommittee

/-!
# Proofs: the epoch transition succeeds from Altair to before Electra

From Altair the epoch transition adds the inactivity scores and the participation flags.

It also draws a new sync committee at the end of each period.

This file states the hypotheses of its steps on the state before the epoch.

Before Electra the steps keep the registry size and keys, and no effective balance passes the cap.

The draw needs one active validator at the cap in the state the steps compute.

So that is an assumption on the steps, not a bound on the state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- After the update of the effective balances, each validator keeps the key of its old self.

Its effective balance is unchanged, or at most the largest one its credentials allow. -/
private theorem processEffectiveBalanceUpdates_mem {after : BeaconState preset fork}
    (matched : BalancesMatch state)
    (computed : processEffectiveBalanceUpdates state = .ok after) {validator : Validator}
    (member : validator ∈ after.validators.data) :
    ∃ old ∈ state.validators.data, validator.pubkey = old.pubkey ∧
      (validator.effectiveBalance = old.effectiveBalance ∨
        validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork old) := by
  obtain ⟨i, inside, rfl⟩ := Array.getElem_of_mem member
  have insideOld : i < state.validators.data.size :=
    (sameSizes_processEffectiveBalanceUpdates computed).1 ▸ inside
  have insideBalance : i < state.balances.data.size := matched ▸ insideOld
  obtain ⟨effectiveBalance, read, bound⟩ := processEffectiveBalanceUpdates_effectiveBalance
    computed (Array.getElem?_eq_getElem insideOld) (Array.getElem?_eq_getElem insideBalance)
  rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at read
  rw [read]
  exact ⟨_, Array.getElem_mem insideOld, rfl, bound.imp id And.right⟩

/-- From Altair and before Electra, the epoch transition succeeds under bounds on the state.

The divisors of the preset and the configuration are positive, and the hysteresis bands fit.

The block roots reach the previous epoch, and the draw and the sync committee fit the preset.

The step runs at the last slot of an epoch.

The slot plus the slots of the history of roots fits in 64 bits.

The next epoch plus the length of the history of mixes fits in 64 bits.

The registry is within its limit, with one balance, one score and one flag set per validator.

Each effective balance is at most the cap of the draw.

The sum of the effective balances and each balance are at most the budget.

Three times that sum plus one increment fits in 64 bits, and so does each increment count times it.

Each inactivity score is at most a bound, and that bound plus the bias fits in 64 bits.

The rewards fit for the budget and that bound plus the bias.

The ceiling on the balances after the rewards is below `2^63`.

The checkpoints are in order, and the current justified epoch is at most the previous epoch.

An epoch bounds the first activation epoch and every finite exit epoch, with room above it.

The slashed balances fit, and so does their sum times the multiplier.

The epoch plus half the vector of slashed balances fits too.

The list of history entries of the fork has room for one more.

When the next epoch starts a sync committee period, a new committee is drawn.

The registry must then hold at most `2^40` validators with valid keys.

The committee size times the registry size must also fit in 64 bits.

The draw also needs one validator at the cap, active in the next epoch.

That validator is read in the state that the steps before the draw reach. -/
theorem processEpoch_total_of_altair_of_lt_electra {config : Config} {checks : SignatureChecks}
    {budget scoreBound ceiling : Nat}
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    (altair : .altair ≤ fork) (before : fork < .pectra)
    (positive : preset.DivisorsPositive) (configPositive : config.DivisorsPositive)
    (roots : preset.RootsReachPreviousEpoch) (bands : preset.HysteresisBandsBelow)
    (fit : RewardsFit preset config budget (scoreBound + config.INACTIVITY_SCORE_BIAS.toNat))
    (half : preset.rewardsCeiling budget < 2 ^ 63)
    (fits : DrawFits preset fork)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (members : preset.SYNC_COMMITTEE_SIZE ≠ 0)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (epochRoom : (getCurrentEpoch state).toNat + 1 + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat <
      2 ^ 64)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state)
    (sized : ParticipationMatches state) (scoresMatch : InactivityScoresMatch state)
    (drawCapped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ drawCap preset fork)
    (summed : effectiveBalanceSum state ≤ budget)
    (tripled : 3 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state) < 2 ^ 64)
    (funded : ∀ balance ∈ state.balances.data, balance.toNat ≤ budget)
    (scored : ∀ score ∈ (state.inactivityScores altair).data, score.toNat ≤ scoreBound)
    (scoreRoom : scoreBound + config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64)
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
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
    (rootsRoom : fork < .shapella →
      state.historicalRoots.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat)
    (summariesRoom : ∀ capella : .shapella ≤ fork,
      (state.historicalSummaries capella).data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat)
    (keys : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      ∀ validator ∈ state.validators.data,
        ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point)
    (few : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      state.validators.data.size ≤ 2 ^ 40)
    (syncRoom : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      preset.SYNC_COMMITTEE_SIZE.toNat * state.validators.data.size < 2 ^ 64)
    (full : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      ∀ ready, run (action config checks) (prefixStages ++ middleStages ++ [.participation])
          state = .ok ready →
        ∃ validator ∈ ready.validators.data,
          isActiveValidator validator (getCurrentEpoch state + 1) ∧
            validator.effectiveBalance.toNat = drawCap preset fork) :
    ∃ after, processEpoch config checks state = .ok after := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : ¬Fork.glamsterdam ≤ fork := fun gloas =>
    notElectra (Nat.le_trans (by decide) gloas)
  have notFulu : ¬Fork.fusaka ≤ fork := fun fulu => notElectra (Nat.le_trans (by decide) fulu)
  have hegota : fork < .hegota := Nat.lt_trans before (by decide)
  have next : state.slot.toNat + 1 < 2 ^ 64 := by
    have := roots.reach
    have := roots.twoSlots
    omega
  have cap : drawCap preset fork = preset.MAX_EFFECTIVE_BALANCE.toNat := by
    simp only [drawCap, notElectra, ↓reduceIte]
  have capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance := by
    intro validator member
    have := drawCapped validator member
    unfold Preset.largestEffectiveBalance
    omega
  -- Justification and finalization change only the checkpoints and their bits.
  obtain ⟨justified, justifiedOk⟩ := processJustificationAndFinalization_total roots last room
    within ordered settled tripled sized (fun early => absurd altair (Nat.not_le_of_lt early))
  obtain ⟨-, -, -, -, -, validators1, -, -, previous1, current1⟩ :=
    processJustificationAndFinalization_keeps justifiedOk
  have slot1 := processJustificationAndFinalization_slot justifiedOk
  have scores1 := processJustificationAndFinalization_inactivityScores justifiedOk
  have kept1 : justified.balances = state.balances ∧ justified.slashings = state.slashings ∧
      justified.historicalRoots = state.historicalRoots ∧
      justified.historicalSummaries = state.historicalSummaries := by
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      rw [← rest]
      exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨balances1, slashings1, roots1, summaries1⟩ := kept1
  have within1 : justified.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit
    rw [validators1]
    exact within
  have matched1 : BalancesMatch justified := by
    unfold BalancesMatch
    rw [balances1, validators1]
    exact matched
  have sized1 : ParticipationMatches justified := fun altair => by
    rw [previous1, current1, validators1]
    exact sized altair
  have scoresMatch1 : InactivityScoresMatch justified := fun altair => by
    rw [scores1, validators1]
    exact scoresMatch altair
  have finalized1 :=
    processJustificationAndFinalization_finalizedSettled ordered settled justifiedOk
  -- The update of the scores changes only the scores, each by at most the bias.
  obtain ⟨inactive, inactiveOk⟩ := processInactivityUpdates_total config altair within1
    finalized1 scoresMatch1 sized1 (fun score member => by
      rw [scores1] at member
      have := scored score member
      omega)
  have frame2 := processInactivityUpdates_frame inactiveOk
  have scored2 := processInactivityUpdates_scoreBound inactiveOk (by rw [scores1]; exact scored)
  have scoresSize2 := (processInactivityUpdates_sizes inactiveOk).2
  have validators2 : inactive.validators = state.validators := by rw [frame2]; exact validators1
  have slot2 : inactive.slot = state.slot := by rw [frame2]; exact slot1
  -- The rewards and penalties change only the balances, each to at most the ceiling.
  obtain ⟨rewarded, rewardedOk, ceilinged⟩ := processRewardsAndPenalties_total altair positive
    configPositive fit (by rw [frame2]; exact within1) (by rw [frame2]; exact matched1)
    (by rw [validators2]; exact capped)
    (by unfold effectiveBalanceSum; rw [validators2]; exact summed)
    (by rw [frame2, balances1]; exact funded) scored2 (by rw [frame2]; exact finalized1)
    (fun altair => by rw [scoresSize2, frame2]; exact scoresMatch1 altair)
    (by rw [frame2]; exact sized1)
  have frame3 := processRewardsAndPenalties_frame rewardedOk
  have validators3 : rewarded.validators = state.validators := by rw [frame3]; exact validators2
  have slot3 : rewarded.slot = state.slot := by rw [frame3]; exact slot2
  have currentEpoch3 : getCurrentEpoch rewarded = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot3]
  have matched3 : BalancesMatch rewarded :=
    (frame_processRewardsAndPenalties rewardedOk).balancesMatch (by rw [frame2]; exact matched1)
  -- The registry updates change only the epochs of the validators.
  obtain ⟨registered, registeredOk, -⟩ := processRegistryUpdates_total_of_lt_electra
    (config := config) rewarded before ceiling (by rw [currentEpoch3]; exact first)
    (by rw [validators3]; exact exits) (by rw [validators3]; exact exitRoom)
  obtain ⟨slot4, balances4, slashings4, roots4, summaries4, effective4⟩ :=
    processRegistryUpdates_registryKept before registeredOk
  rw [validators3] at effective4
  have size4 : registered.validators.data.size = state.validators.data.size := by
    simpa using congrArg Array.size effective4
  have sum4 : effectiveBalanceSum registered = effectiveBalanceSum state :=
    effectiveBalanceSum_eq_of_map effective4
  have old4 : ∀ validator ∈ registered.validators.data, ∃ old ∈ state.validators.data,
      old.effectiveBalance = validator.effectiveBalance := fun _ member =>
    exists_effectiveBalance_of_map effective4 member
  have currentEpoch4 : getCurrentEpoch registered = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot4, slot3]
  have below4 : ∀ validator ∈ registered.validators.data,
      validator.effectiveBalance.toNat < 2 ^ 63 := fun validator member => by
    obtain ⟨old, oldMember, same⟩ := old4 validator member
    have := effectiveBalance_le_effectiveBalanceSum oldMember
    rw [same] at this
    omega
  have matched4 := (frame_processRegistryUpdates registeredOk).balancesMatch matched3
  have slashings3 : rewarded.slashings = state.slashings := by
    rw [frame3, frame2]
    exact slashings1
  -- The slashing penalties only lower balances.
  obtain ⟨slashed, slashedOk⟩ := processSlashings_total positive
    (by unfold BeaconState.RegistryWithinLimit; rw [size4]; exact within) matched4
    (by rw [sum4]; have := fit.budget_lt; omega) below4
    (by unfold slashedBalanceSum; rw [slashings4, slashings3]; exact slashedFits)
    (by unfold slashedBalanceSum; rw [slashings4, slashings3]; exact slashedProduct)
    (by rw [currentEpoch4]; exact halfway)
    (fun _ validator member => by
      obtain ⟨old, oldMember, same⟩ := old4 validator member
      rw [sum4, ← same]
      exact product old oldMember)
  have frame5 := processSlashings_frame slashedOk
  have matched5 := (frame_processSlashings slashedOk).balancesMatch matched4
  have lowered5 : ∀ balance ∈ slashed.balances.data,
      balance.toNat ≤ preset.rewardsCeiling budget := by
    obtain ⟨_, _, _, _, _, each⟩ := processSlashings_balances_toNat_of_lt_electra before slashedOk
    intro balance member
    obtain ⟨i, inside, rfl⟩ := Array.getElem_of_mem member
    by_cases inRegistry : i < registered.validators.data.size
    · obtain ⟨_, _, mapped⟩ := (each i).1 inRegistry
      rw [Array.getElem?_eq_getElem inside] at mapped
      cases read : registered.balances.data[i]? with
      | none => simp [read] at mapped
      | some old =>
        simp only [read, Option.map_some, Option.some.injEq] at mapped
        have := ceilinged old (by rw [← balances4]; exact Array.mem_of_getElem? read)
        omega
    · have past := (each i).2 (Nat.le_of_not_lt inRegistry)
      rw [Array.getElem?_eq_getElem inside] at past
      exact ceilinged _ (by rw [← balances4]; exact Array.mem_of_getElem? past.symm)
  -- The reset of the deposit votes changes only those votes.
  obtain ⟨reset, resetOk⟩ := processEth1DataReset_total (state := slashed) hegota
    (by rw [frame5, slot4, slot3]; exact next)
  have frame6 := processEth1DataReset_frame resetOk
  have validators6 : reset.validators = registered.validators := by rw [frame6, frame5]
  have matched6 : BalancesMatch reset := by rw [frame6]; exact matched5
  -- The effective balances move toward the balances, which stay below 2^63.
  obtain ⟨updated, updatedOk⟩ := processEffectiveBalanceUpdates_total bands matched6
    (fun balance member => by
      rw [frame6] at member
      have := lowered5 balance member
      omega)
    (by rw [validators6]; exact below4)
  have frame7 := processEffectiveBalanceUpdates_frame updatedOk
  have slot7 : updated.slot = state.slot := by rw [frame7, frame6, frame5, slot4, slot3]
  have roots7 : updated.historicalRoots = state.historicalRoots := by
    rw [frame7, frame6, frame5, roots4, frame3, frame2]
    exact roots1
  have summaries7 : updated.historicalSummaries = state.historicalSummaries := by
    rw [frame7, frame6, frame5, summaries4, frame3, frame2]
    exact summaries1
  -- The resets and the update of the history need only a next slot.
  obtain ⟨cleared, clearedOk⟩ := processSlashingsReset_total (state := updated)
    (by rw [slot7]; exact next)
  obtain ⟨_, _, _, _, frame8⟩ := processSlashingsReset_eq clearedOk
  obtain ⟨mixed, mixedOk⟩ := processRandaoMixesReset_total (state := cleared)
    (by rw [frame8]; exact slot7 ▸ next)
  obtain ⟨_, _, _, _, _, _, frame9⟩ := processRandaoMixesReset_eq mixedOk
  obtain ⟨rooted, rootedOk, slot10, validators10⟩ : ∃ rooted,
      action config checks .history mixed = .ok rooted ∧ rooted.slot = mixed.slot ∧
        rooted.validators = mixed.validators := by
    by_cases capella : Fork.shapella ≤ fork
    · obtain ⟨rooted, ok⟩ := processHistoricalSummariesUpdate_total (state := mixed) capella
        (by rw [frame9, frame8]; exact slot7 ▸ next)
        (by rw [frame9, frame8, summaries7]; exact summariesRoom capella)
      refine ⟨rooted, action_cases.mpr (by simp only [Edge, capella, ↓reduceDIte]; exact ok),
        ?_⟩
      obtain ⟨-, kept⟩ := processHistoricalSummariesUpdate_eq ok
      split at kept
      · obtain ⟨_, _, _, _, _, rest⟩ := kept
        exact ⟨by rw [← rest], by rw [← rest]⟩
      · rw [kept]
        exact ⟨rfl, rfl⟩
    · have older : fork < .shapella := Nat.lt_of_not_le capella
      obtain ⟨rooted, ok⟩ := processHistoricalRootsUpdate_total (state := mixed) older
        (by rw [frame9, frame8]; exact slot7 ▸ next)
        (by rw [frame9, frame8, roots7]; exact rootsRoom older)
      refine ⟨rooted, action_cases.mpr (by simp only [Edge, capella, ↓reduceDIte]; exact ok),
        ?_⟩
      obtain ⟨-, kept⟩ := processHistoricalRootsUpdate_eq older ok
      split at kept
      · obtain ⟨_, _, _, rest⟩ := kept
        exact ⟨by rw [← rest], by rw [← rest]⟩
      · rw [kept]
        exact ⟨rfl, rfl⟩
  -- The rotation of the flags keeps the registry, which the draw then reads.
  let flagged := processParticipationFlagUpdates rooted altair
  have validatorsFlagged : flagged.validators = updated.validators := by
    rw [show flagged.validators = rooted.validators from rfl, validators10, frame9, frame8]
  have currentEpochFlagged : getCurrentEpoch flagged = getCurrentEpoch state := by
    simp only [getCurrentEpoch, show flagged.slot = rooted.slot from rfl, slot10, frame9,
      frame8, slot7]
  -- Before Electra the pending balances and the payments leave the state as it is.
  have deposits : action config checks .pendingDeposits reset = .ok reset :=
    action_cases.mpr (by simp only [Edge, notElectra, ↓reduceDIte])
  have consolidations : action config checks .pendingConsolidations reset = .ok reset :=
    action_cases.mpr (by simp only [Edge, notElectra, ↓reduceDIte])
  have payments : action config checks .payments reset = .ok reset :=
    action_cases.mpr (by simp only [Edge, notGloas, ↓reduceDIte])
  have rotated : action config checks .participation rooted = .ok flagged :=
    action_cases.mpr (by simp only [Edge, altair, ↓reduceDIte, flagged])
  have readyTrace : EpochTrace (action config checks)
      (prefixStages ++ middleStages ++ [.participation]) state flagged :=
    .cons (action_cases.mpr justifiedOk)
      (.cons (action_cases.mpr (by simp only [Edge, altair, ↓reduceDIte]; exact inactiveOk))
      (.cons (action_cases.mpr rewardedOk) (.cons (action_cases.mpr registeredOk)
      (.cons (action_cases.mpr slashedOk)
      (.cons (action_cases.mpr (by simp only [Edge, hegota, ↓reduceDIte]; exact resetOk))
      (.cons deposits (.cons consolidations (.cons payments
      (.cons (action_cases.mpr updatedOk) (.cons (action_cases.mpr clearedOk)
      (.cons (action_cases.mpr mixedOk) (.cons rootedOk (.cons rotated .nil)))))))))))))
  -- The draw reads the registry after the update of the effective balances.
  have drawable : (getCurrentEpoch flagged + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      SyncDrawable flagged := by
    intro boundary
    rw [currentEpochFlagged] at boundary
    have size : flagged.validators.data.size = state.validators.data.size := by
      rw [validatorsFlagged, (sameSizes_processEffectiveBalanceUpdates updatedOk).1, validators6,
        size4]
    refine ⟨fun validator member => ?_, fun validator member => ?_, ?_, ?_, ?_⟩
    · rw [validatorsFlagged] at member
      obtain ⟨old, oldMember, key, -⟩ :=
        processEffectiveBalanceUpdates_mem matched6 updatedOk member
      rw [validators6] at oldMember
      obtain ⟨first, firstMember, same, -⟩ :=
        (processRegistryUpdates_kept registeredOk).1.exists_of_mem
          (Nat.le_of_eq (size4.trans (by rw [validators3]))) oldMember
      rw [validators3] at firstMember
      rw [key, same]
      exact keys boundary first firstMember
    · rw [validatorsFlagged] at member
      obtain ⟨old, oldMember, -, bound⟩ :=
        processEffectiveBalanceUpdates_mem matched6 updatedOk member
      rw [validators6] at oldMember
      rcases bound with same | le
      · obtain ⟨first, firstMember, eq⟩ := old4 old oldMember
        rw [same, ← eq]
        exact drawCapped first firstMember
      · rw [cap]
        have := UInt64.le_iff_toNat_le.mp le
        simpa only [withdrawalMaxEffectiveBalance, notElectra, ↓reduceIte] using this
    · rw [currentEpochFlagged]
      exact full boundary flagged (run_ok_iff.mpr readyTrace)
    · rw [size]
      exact few boundary
    · rw [size]
      exact syncRoom boundary
  obtain ⟨synced, syncedOk⟩ := processSyncCommitteeUpdates_ok altair fits
    (by rw [currentEpochFlagged]; exact epochRoom) lookahead members drawable
  refine ⟨synced, ?_⟩
  have whole : epochStages = (prefixStages ++ middleStages ++ [.participation]) ++
      [.syncCommittees, .proposerLookahead, .ptcWindow] := rfl
  simp only [processEpoch, altair, ↓reduceDIte]
  rw [processEpochAltair_eq_run, whole]
  have lookaheadOk : action config checks .proposerLookahead synced = .ok synced :=
    action_cases.mpr (by simp only [Edge, notFulu, ↓reduceDIte])
  have windowOk : action config checks .ptcWindow synced = .ok synced :=
    action_cases.mpr (by simp only [Edge, notGloas, ↓reduceDIte])
  exact run_ok_iff.mpr (append_iff.mpr ⟨flagged, readyTrace,
    .cons (action_cases.mpr (by simp only [Edge, altair, ↓reduceDIte]; exact syncedOk))
      (.cons lookaheadOk (.cons windowOk .nil))⟩)

end EthLib.Consensus
