module

public import EthLib.Consensus.Proofs.Transition.Totality.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.Totality.EpochAltair
public import EthLib.Consensus.Proofs.Transition.Totality.ProposerLookahead
public import EthLib.Consensus.Proofs.Transition.Totality.PtcWindow
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryElectra
public import EthLib.Consensus.Proofs.Transition.Totality.Supply

/-!
# Proofs: the epoch transition succeeds from Electra

From Electra the epoch also drains the queues of deposits and consolidations.

From Fulu it moves the lookahead of proposers.

From Gloas it pays builders and moves the window of payload timeliness committees.

From Heze it skips the reset of the deposit votes.

The supply and the size of the registry stay bounded from the start, so the draws can succeed.

Each draw also needs a validator at its cap, which the steps take as an assumption.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- The stages of the epoch before the sync committee update. -/
abbrev readyStages : List EpochStage := prefixStages ++ middleStages ++ [.participation]

/-- Deposits applied in order keep each effective balance below a bound that exceeds each amount.

A new validator takes at most the amount of its deposit. -/
private theorem foldlM_applyPendingDeposit_effectiveBalance_lt {config : Config}
    {checks : SignatureChecks} {bound : Nat} :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset fork},
      deposits.foldlM (applyPendingDeposit config checks) state = .ok after →
      (∀ validator ∈ state.validators.data, validator.effectiveBalance.toNat < bound) →
      (∀ deposit ∈ deposits, deposit.amount.toNat < bound) →
      ∀ validator ∈ after.validators.data, validator.effectiveBalance.toNat < bound
  | [], _, _, computed, old, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact old
  | deposit :: rest, state, after, computed, old, amounts => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, applied, later⟩ := computed
    refine foldlM_applyPendingDeposit_effectiveBalance_lt later ?_
      (fun other member => amounts other (List.mem_cons_of_mem _ member))
    rcases applyPendingDeposit_cases applied with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact old
    · rw [increaseBalance_validators raised]
      exact old
    · rw [addValidatorToRegistry_validators_eq_push added]
      intro validator member
      rcases Array.mem_push.mp member with member | rfl
      · exact old validator member
      · exact Nat.lt_of_le_of_lt
          (UInt64.le_iff_toNat_le.mp (getValidatorFromDeposit_effectiveBalance_le _ _ _))
          (amounts deposit List.mem_cons_self)

/-- From Electra, the pending deposits keep each effective balance below a bound.

The bound must be above each effective balance and above the sum of the queue. -/
private theorem processPendingDeposits_effectiveBalance_lt {config : Config}
    {checks : SignatureChecks} {electra : .pectra ≤ fork} {after : BeaconState preset fork}
    {bound : Nat} (computed : processPendingDeposits config checks state electra = .ok after)
    (old : ∀ validator ∈ state.validators.data, validator.effectiveBalance.toNat < bound)
    (queued : pendingDepositSum state < bound) :
    ∀ validator ∈ after.validators.data, validator.effectiveBalance.toNat < bound := by
  obtain ⟨read, rest, applied, _, next, _, _, queue, _, _, sublist, _, _, later, rfl⟩ :=
    processPendingDeposits_applied computed
  refine (foldlM_applyPendingDeposit_effectiveBalance_lt (after := next) later old
    fun deposit member => ?_ :)
  have inQueue : deposit ∈ (state.pendingDeposits electra).data.toList := by
    rw [queue]
    exact List.mem_append_left _ (sublist.subset member)
  have le : deposit.amount.toNat ≤ pendingDepositSum state := by
    unfold pendingDepositSum
    simp only [electra, ↓reduceDIte, pendingAmount]
    exact List.le_sum_of_mem (List.mem_map_of_mem inQueue)
  omega

/-- From Electra, the largest effective balance of a validator is at most the cap of the draws.

The least balance to activate must be at most the cap of a compounding validator. -/
private theorem withdrawalMaxEffectiveBalance_le_drawCap (electra : .pectra ≤ fork)
    (activationCap : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (validator : Validator) :
    (withdrawalMaxEffectiveBalance preset fork validator).toNat ≤ drawCap preset fork := by
  simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, drawCap, electra, ↓reduceIte]
  split
  · exact Nat.le_refl _
  · exact UInt64.le_iff_toNat_le.mp activationCap

/-- From Electra, the epoch transition succeeds under bounds on the state.

The vectors of slashed balances and of mixes are not empty.

The divisors of the preset and the configuration are positive.

The block roots reach the previous epoch, and the hysteresis bands fit.

The rewards fit for the budget and an inactivity bound plus the bias.

The ceiling on the balances after the rewards is below `2^63`.

The seed lookahead is shorter than the history of mixes, and a sync committee is not empty.

The step runs at the last slot of an epoch.

The slot plus the slots of the history of roots fits in 64 bits.

The current epoch plus the seed lookahead, one and the length of the mixes fits in 64 bits.

The first slot of the epoch two past the seed lookahead is at most `2^64`.

The validators plus the pending deposits are within the limit of the registry.

There is one balance, one flag set and one score per validator.

Each effective balance is at most the largest one its credentials allow.

The sum of the effective balances is at most the budget.

That sum plus one increment, times three, fits in 64 bits.

Each balance is at most the budget.

Each inactivity score is at most that bound, and that bound plus the bias fits in 64 bits.

The total active balance and the balance behind each flag of the previous epoch are computed.

No flag of the previous epoch was set by more balance than is active now.

That is an assumption, not a consequence of validity, and the issuance bound needs it.

The balances plus the pending deposits plus the issuance bound are below `2^63`.

The checkpoints are in order, and the current justified epoch is at most the previous epoch.

An epoch bounds the first activation epoch, the end of the exit queue and every finite exit epoch.

That epoch plus the cost of the unstarted exits and the withdrawability delay is below `2^64 - 1`.

The least churn and the largest shared churn are each at least one increment.

The churn carried for exits plus three times its ceiling fits in 64 bits.

The churn carried for deposits plus its cap fits in 64 bits.

Both indices of every queued consolidation are in the registry.

The slashed balances fit, and so does their sum times the multiplier.

The current epoch plus half the length of the vector of slashed balances fits too.

The list of history summaries has room for one more.

From Gloas an epoch has at least six slots.

The least balance to activate is at most the cap of a compounding validator.

The validators plus the pending deposits number at most `2^40`.

That number times the size of a sync committee fits in 64 bits.

From Gloas, so does that number times the size of a payload committee.

From Gloas, so does it times one more than the committees per slot, times the slots of an epoch.

When the next epoch starts a sync committee period, take the state reached before that draw.

Every key of that state must pass validation.

The other two draws are for the epoch one past the seed lookahead, from Fulu and from Gloas.

Each draw must end on the state it reads, under the bounds of the draw.

No bound on the state makes a draw end, so that is assumed. -/
theorem processEpoch_total_of_electra {config : Config} {checks : SignatureChecks}
    {budget scoreBound ceiling : Nat}
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    (electra : .pectra ≤ fork)
    (positive : preset.DivisorsPositive) (configPositive : config.DivisorsPositive)
    (roots : preset.RootsReachPreviousEpoch) (bands : preset.HysteresisBandsBelow)
    (fit : RewardsFit preset config budget (scoreBound + config.INACTIVITY_SCORE_BIAS.toNat))
    (half : preset.rewardsCeiling budget < 2 ^ 63)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (members : preset.SYNC_COMMITTEE_SIZE ≠ 0)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (seedRoom : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (slotRoom : ((getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (loaded : registryLoad state ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (matched : BalancesMatch state)
    (sized : ParticipationMatches state) (scoresMatch : InactivityScoresMatch state)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator)
    (summed : effectiveBalanceSum state ≤ budget)
    (tripled : 3 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state) < 2 ^ 64)
    (funded : ∀ balance ∈ state.balances.data, balance.toNat ≤ budget)
    (scored : ∀ score ∈ (state.inactivityScores (Nat.le_trans (by decide) electra)).data,
      score.toNat ≤ scoreBound)
    (scoreRoom : scoreBound + config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64)
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {participatingBalance : Fin PARTICIPATION_FLAG_WEIGHTS.length → Gwei}
    (weighed : ∀ flagIndex, ∃ indices,
      getUnslashedParticipatingIndices state (Nat.le_trans (by decide) electra)
          flagIndex.val.toUInt64 (getPreviousEpoch state) = .ok indices ∧
        getTotalBalance state indices = .ok (participatingBalance flagIndex))
    (kept : ∀ flagIndex, participatingBalance flagIndex ≤ total)
    (supply : balanceSum state + pendingDepositSum state + preset.epochIssuance total.toNat <
      2 ^ 63)
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (queued : (state.earliestExitEpoch electra).toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (exitRoom : ceiling + exitCost preset state +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64 - 1)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (exitCarried : (state.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config state <
      2 ^ 64)
    (depositCarried :
      (state.depositBalanceToConsume electra).toNat + depositChurnCap config fork < 2 ^ 64)
    (inside : ∀ consolidation ∈ (state.pendingConsolidations electra).data,
      consolidation.sourceIndex.toNat < state.validators.data.size ∧
        consolidation.targetIndex.toNat < state.validators.data.size)
    (slashedFits : slashedBalanceSum state < 2 ^ 64)
    (slashedProduct : slashedBalanceSum state *
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat < 2 ^ 64)
    (halfway : (getCurrentEpoch state).toNat + (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat <
      2 ^ 64)
    (summariesRoom : (state.historicalSummaries (Nat.le_trans (by decide) electra)).data.size <
      preset.HISTORICAL_ROOTS_LIMIT.toNat)
    (slots : .glamsterdam ≤ fork → 6 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (activationCap : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (few : registryLoad state ≤ 2 ^ 40)
    (syncRoom : preset.SYNC_COMMITTEE_SIZE.toNat * registryLoad state < 2 ^ 64)
    (ptcRoom : .glamsterdam ≤ fork → preset.PTC_SIZE.toNat * registryLoad state < 2 ^ 64 ∧
      registryLoad state * (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (keys : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      ∀ ready, run (action config checks) readyStages state = .ok ready →
        ∀ validator ∈ ready.validators.data,
          ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point)
    (syncEnds : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      ∀ ready, run (action config checks) readyStages state = .ok ready →
        (∀ validator ∈ ready.validators.data,
          validator.effectiveBalance.toNat ≤ drawCap preset fork) →
        ready.validators.data.size ≤ 2 ^ 40 →
        preset.SYNC_COMMITTEE_SIZE.toNat * ready.validators.data.size < 2 ^ 64 →
        SyncDrawEnds ready (getCurrentEpoch state + 1))
    (proposersEnd : .fusaka ≤ fork → ∀ synced,
      run (action config checks) (readyStages ++ [.syncCommittees]) state = .ok synced →
        (∀ validator ∈ synced.validators.data,
          validator.effectiveBalance.toNat ≤ drawCap preset fork) →
        synced.validators.data.size ≤ 2 ^ 40 →
        ProposersDrawEnd synced (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1))
    (ptcEnd : .glamsterdam ≤ fork → ∀ moved,
      run (action config checks) (readyStages ++ [.syncCommittees, .proposerLookahead]) state =
          .ok moved →
        (∀ validator ∈ moved.validators.data,
          validator.effectiveBalance.toNat ≤ drawCap preset fork) →
        moved.validators.data.size ≤ 2 ^ 40 →
        preset.PTC_SIZE.toNat * moved.validators.data.size < 2 ^ 64 →
        PtcDrawsEnd moved (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1)) :
    ∃ after, processEpoch config checks state = .ok after := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have notBefore : ¬fork < .pectra := Nat.not_lt.mpr electra
  have next : state.slot.toNat + 1 < 2 ^ 64 := by
    have := roots.reach
    have := roots.twoSlots
    omega
  have epochNext : (getCurrentEpoch state).toNat + 1 < 2 ^ 64 := by
    have := getCurrentEpoch_toNat_le_slot state
    omega
  have within : state.RegistryWithinLimit := by
    unfold registryLoad at loaded
    exact Nat.le_trans (Nat.le_add_right _ _) loaded
  have budgetBelow : budget < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) half
  have effectiveSupply : effectiveBalanceSum state + pendingDepositSum state < 2 ^ 64 := by
    omega
  have largest : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance := fun validator member =>
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (capped validator member))
      (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork validator)
  -- Justification and finalization change only the checkpoints and their bits.
  obtain ⟨justified, justifiedOk⟩ := processJustificationAndFinalization_total roots last room
    within ordered settled tripled sized (fun early => absurd altair (Nat.not_le_of_lt early))
  have frame1 := processJustificationAndFinalization_eq justifiedOk
  have finalized1 :=
    processJustificationAndFinalization_finalizedSettled ordered settled justifiedOk
  -- The update of the scores changes only the scores, each by at most the bias.
  obtain ⟨inactive, inactiveOk⟩ := processInactivityUpdates_total config altair
    (by rw [frame1]; exact within) finalized1 (by rw [frame1]; exact scoresMatch)
    (by rw [frame1]; exact sized) (fun score member => by
      rw [frame1] at member
      have := scored score member
      omega)
  have frame2 := processInactivityUpdates_frame inactiveOk
  have scored2 := processInactivityUpdates_scoreBound inactiveOk (by rw [frame1]; exact scored)
  have scoresSize2 := (processInactivityUpdates_sizes inactiveOk).2
  -- The rewards and penalties change only the balances, each to at most the ceiling.
  obtain ⟨rewarded, rewardedOk, -⟩ := processRewardsAndPenalties_total altair positive
    configPositive fit (by rw [frame2, frame1]; exact within)
    (by rw [frame2, frame1]; exact matched) (by rw [frame2, frame1]; exact largest)
    (by unfold effectiveBalanceSum; rw [frame2, frame1]; exact summed)
    (by rw [frame2, frame1]; exact funded) scored2 (by rw [frame2]; exact finalized1)
    (fun altair => by rw [scoresSize2, frame2, frame1]; exact scoresMatch altair)
    (by rw [frame2, frame1]; exact sized)
  have frame3 := processRewardsAndPenalties_frame rewardedOk
  have matched3 : BalancesMatch rewarded :=
    (frame_processRewardsAndPenalties rewardedOk).balancesMatch
      (by rw [frame2, frame1]; exact matched)
  have head : EpochTrace (action config checks) [.justification, .inactivity, .rewards]
      state rewarded :=
    .cons (action_cases.mpr justifiedOk)
      (.cons (action_cases.mpr (by simp only [Edge, altair, ↓reduceDIte]; exact inactiveOk))
      (.cons (action_cases.mpr rewardedOk) .nil))
  have supply3 := supply_le_of_head altair within
    (Nat.pos_of_ne_zero fun zero => positive.increment (UInt64.toNat_inj.mp zero))
    fit.perIncrement active weighed kept head
  have validators3 : rewarded.validators = state.validators := by
    rw [frame3, frame2, frame1]
  have slot3 : rewarded.slot = state.slot := by rw [frame3, frame2, frame1]
  have currentEpoch3 : getCurrentEpoch rewarded = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot3]
  have effectiveSum3 : effectiveBalanceSum rewarded = effectiveBalanceSum state := by
    unfold effectiveBalanceSum
    rw [validators3]
  have summedBelow : effectiveBalanceSum state < 2 ^ 64 := by omega
  -- The registry updates keep the balances and the effective balances.
  obtain ⟨registered, registeredOk, -, -, -, slot4, balances4, effective4⟩ :=
    processRegistryUpdates_total_of_electra (config := config) rewarded electra
      (by unfold BeaconState.RegistryWithinLimit; rw [validators3]; exact within)
      (by rw [effectiveSum3]; exact summedBelow)
      (UInt64.pos_iff_ne_zero.mpr positive.increment) minimum maximum ceiling
      (by rw [currentEpoch3]; exact first) (by rw [frame3, frame2, frame1]; exact queued)
      (by rw [validators3]; exact exits)
      (by
        have same : exitCost preset rewarded = exitCost preset state := by
          unfold exitCost
          rw [validators3]
        rw [same]
        exact exitRoom)
      (by
        have same : exitChurnCeiling config rewarded = exitChurnCeiling config state := by
          unfold exitChurnCeiling
          rw [effectiveSum3]
        rw [same, frame3, frame2, frame1]
        exact exitCarried)
  have registeredAction : action config checks .registry rewarded = .ok registered :=
    action_cases.mpr registeredOk
  have fields4 := processRegistryUpdates_fields registeredOk
  have load4 : LoadKept rewarded registered := loadKeptLaws.epochEdge (by simp) registeredAction
  have frame4 := frame_processRegistryUpdates registeredOk
  obtain ⟨kept4, consolidations4⟩ := processRegistryUpdates_kept registeredOk
  have matched4 := frame4.balancesMatch matched3
  rw [validators3] at effective4
  have sum4 : effectiveBalanceSum registered = effectiveBalanceSum state :=
    effectiveBalanceSum_eq_of_map effective4
  have size4 : registered.validators.data.size = state.validators.data.size := by
    simpa using congrArg Array.size effective4
  have currentEpoch4 : getCurrentEpoch registered = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot4, slot3]
  have below4 : ∀ validator ∈ registered.validators.data,
      validator.effectiveBalance.toNat < 2 ^ 63 := fun validator member => by
    obtain ⟨old, oldMember, same⟩ := exists_effectiveBalance_of_map effective4 member
    have := effectiveBalance_le_effectiveBalanceSum oldMember
    rw [same] at this
    omega
  have slashings4 : registered.slashings = state.slashings := by
    rw [fields4.1, frame3, frame2, frame1]
  -- The slashing penalties only lower balances.
  obtain ⟨slashed, slashedOk⟩ := processSlashings_total positive
    (by unfold BeaconState.RegistryWithinLimit; rw [size4]; exact within) matched4
    (by rw [sum4]; exact summedBelow) below4
    (by unfold slashedBalanceSum; rw [slashings4]; exact slashedFits)
    (by unfold slashedBalanceSum; rw [slashings4]; exact slashedProduct)
    (by rw [currentEpoch4]; exact halfway)
    (fun before => absurd electra (Nat.not_le_of_lt before))
  have slashedAction : action config checks .slashings registered = .ok slashed :=
    action_cases.mpr slashedOk
  have frame5 := processSlashings_frame slashedOk
  have matched5 := (frame_processSlashings slashedOk).balancesMatch matched4
  -- The reset of the deposit votes changes only those votes, and Heze skips it.
  obtain ⟨reset, resetOk, frame6⟩ : ∃ reset,
      action config checks .eth1Reset slashed = .ok reset ∧
        reset = { slashed with eth1DataVotes := reset.eth1DataVotes } := by
    by_cases hegota : fork < .hegota
    · obtain ⟨reset, ok⟩ := processEth1DataReset_total (state := slashed) hegota
        (by rw [frame5, slot4, slot3]; exact next)
      exact ⟨reset, action_cases.mpr (by simp only [Edge, hegota, ↓reduceDIte]; exact ok),
        processEth1DataReset_frame ok⟩
    · exact ⟨slashed, action_cases.mpr (by simp only [Edge, hegota, ↓reduceDIte]), rfl⟩
  have supply6 : balanceSum reset + pendingDepositSum reset ≤
      balanceSum rewarded + pendingDepositSum rewarded := by
    have registry := supply_le_of_action (by simp) registeredAction
    have slashings := supply_le_of_action (by simp) slashedAction
    have votes := supply_le_of_action (by simp) resetOk
    omega
  -- Up to the queues, the registry keeps its size, its effective balances and its credentials.
  have validators6 : reset.validators = registered.validators := by rw [frame6, frame5]
  have size6 : reset.validators.data.size = state.validators.data.size := by
    rw [validators6, size4]
  have currentEpoch6 : getCurrentEpoch reset = getCurrentEpoch state := by
    rw [frame6, frame5]
    exact currentEpoch4
  have sum6 : effectiveBalanceSum reset = effectiveBalanceSum state := by
    unfold effectiveBalanceSum
    rw [validators6]
    exact sum4
  have pending6 : pendingDepositSum reset = pendingDepositSum state := by
    have pending : reset.pendingDeposits = state.pendingDeposits := by
      rw [frame6, frame5]
      exact load4.2.trans (by rw [frame3, frame2, frame1])
    unfold pendingDepositSum
    rw [pending]
  have finalizedRoom : justified.finalizedCheckpoint.epoch.toNat *
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    have settled1 := UInt64.le_iff_toNat_le.mp
      (UInt64.le_trans finalized1 (getPreviousEpoch_le justified))
    have currentEpoch1 : getCurrentEpoch justified = getCurrentEpoch state := by
      rw [frame1]
      rfl
    rw [currentEpoch1] at settled1
    have perEpoch : 0 < preset.SLOTS_PER_EPOCH.toNat :=
      Nat.pos_of_ne_zero fun zero => positive.slotsPerEpoch (UInt64.toNat_inj.mp zero)
    calc justified.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat
        < (justified.finalizedCheckpoint.epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
          rw [Nat.succ_mul]
          omega
      _ ≤ ((getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
          preset.SLOTS_PER_EPOCH.toNat := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ 64 := slotRoom
  -- The pending deposits move amounts from the queue to the balances or drop them.
  have load6 : registryLoad reset = registryLoad state := by
    rw [frame6, frame5]
    exact load4.registryLoad_eq.trans (by rw [frame3, frame2, frame1]; rfl)
  obtain ⟨deposited, depositedOk, loaded7, matched7, supply7, size7, consolidations7, epoch7,
    -, -, -, capped7⟩ := processPendingDeposits_total config checks reset electra
    (by rw [load6]; exact loaded)
    (by rw [frame6]; exact matched5)
    (fun altair => by
      rw [frame6, frame5]
      show (registered.previousEpochParticipation altair).data.size = _ ∧
        (registered.currentEpochParticipation altair).data.size = _
      rw [fields4.2.1, fields4.2.2.1, load4.1, frame3, frame2, frame1]
      exact sized altair)
    (fun altair => by
      rw [frame6, frame5]
      show (registered.inactivityScores altair).data.size = _
      rw [fields4.2.2.2.1, load4.1, frame3, scoresSize2, frame2, frame1]
      exact scoresMatch altair)
    (by
      rw [validators6]
      intro validator member
      obtain ⟨old, oldMember, -, same, credentials, -⟩ :=
        kept4.exists_of_mem (Nat.le_of_eq load4.1) member
      rw [validators3] at oldMember
      have := capped old oldMember
      unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
        hasCompoundingWithdrawalCredential at this ⊢
      rw [same, credentials]
      exact this)
    (by omega) (by rw [sum6]; exact summedBelow)
    (by
      rw [frame6, frame5]
      show (registered.depositBalanceToConsume electra).toNat + _ < _
      rw [fields4.2.2.2.2.2.2, frame3, frame2, frame1]
      exact depositCarried)
    (by rw [currentEpoch6]; exact epochNext)
    (by
      rw [frame6, frame5]
      show registered.finalizedCheckpoint.epoch.toNat * _ < _
      rw [frame4.finalized, frame3, frame2]
      exact finalizedRoom)
  have depositedAction : action config checks .pendingDeposits reset = .ok deposited :=
    action_cases.mpr (by simp only [Edge, electra, ↓reduceDIte]; exact depositedOk)
  have effective7 : ∀ validator ∈ deposited.validators.data,
      validator.effectiveBalance.toNat < 2 ^ 63 :=
    processPendingDeposits_effectiveBalance_lt depositedOk (by rw [validators6]; exact below4)
      (by omega)
  have effectiveSupply7 := processPendingDeposits_effectiveSupply_le depositedOk
  have size7Load : deposited.validators.data.size ≤ registryLoad state :=
    Nat.le_trans (Nat.le_add_right _ _)
      ((processPendingDeposits_registryLoad_le depositedOk).trans (Nat.le_of_eq load6))
  have frame7 := frame_processPendingDeposits depositedOk
  have summaries7 := (processPendingDeposits_history depositedOk).2.2
  -- The pending consolidations move balances between validators of the registry.
  obtain ⟨consolidated, consolidatedOk⟩ := processPendingConsolidations_total deposited electra
    matched7 (by omega)
    (by
      rw [consolidations7, frame6, frame5]
      intro consolidation member
      change consolidation ∈ (registered.pendingConsolidations electra).data at member
      rw [consolidations4, frame3, frame2, frame1] at member
      have := inside consolidation member
      omega)
    (by rw [epoch7, currentEpoch6]; exact epochNext)
  have consolidatedAction :
      action config checks .pendingConsolidations deposited = .ok consolidated :=
    action_cases.mpr (by simp only [Edge, electra, ↓reduceDIte]; exact consolidatedOk)
  have fields8 := processPendingConsolidations_fields consolidatedOk
  have kept8 := processPendingConsolidations_kept consolidatedOk
  have effectiveSupply8 := processPendingConsolidations_effectiveSupply_eq consolidatedOk
  have frame8 := frame_processPendingConsolidations consolidatedOk
  have summaries8 := fields8.2.2.2.2.2.2.1
  -- From Gloas the payments to builders change only their own queues.
  obtain ⟨paid, paidAction, validators9, balances9, slot9, summaries9⟩ : ∃ paid,
      action config checks .payments consolidated = .ok paid ∧
        paid.validators = consolidated.validators ∧ paid.balances = consolidated.balances ∧
        paid.slot = consolidated.slot ∧
        paid.historicalSummaries = consolidated.historicalSummaries := by
    by_cases gloas : Fork.glamsterdam ≤ fork
    · obtain ⟨paid, ok⟩ := processBuilderPendingPayments_total consolidated gloas
        (by
          unfold registryLoad at loaded7
          unfold BeaconState.RegistryWithinLimit
          rw [fields8.1]
          omega)
        (by omega) (slots gloas)
      have same := processBuilderPendingPayments_eq ok
      refine ⟨paid, action_cases.mpr (by simp only [Edge, gloas, ↓reduceDIte]; exact ok),
        ?_, ?_, ?_, ?_⟩ <;> rw [same]
    · exact ⟨consolidated, action_cases.mpr (by simp only [Edge, gloas, ↓reduceDIte]),
        rfl, rfl, rfl, rfl⟩
  -- The effective balances move toward the balances, which stay below the supply.
  have matched9 : BalancesMatch paid := by
    unfold BalancesMatch
    rw [balances9, validators9]
    exact frame8.balancesMatch matched7
  have validators9Deposited : paid.validators = deposited.validators :=
    validators9.trans fields8.1
  obtain ⟨updated, updatedOk⟩ := processEffectiveBalanceUpdates_total bands matched9
    (by
      rw [balances9]
      intro balance member
      obtain ⟨i, inside, rfl⟩ := Array.getElem_of_mem member
      have := balance_le_balanceSum consolidated inside
      omega)
    (by rw [validators9, fields8.1]; exact effective7)
  have frame10 := processEffectiveBalanceUpdates_frame updatedOk
  -- Each effective balance stays or moves to at most its largest one, so to the cap of the draws.
  have capped10 : ∀ validator ∈ updated.validators.data,
      validator.effectiveBalance.toNat ≤ drawCap preset fork := by
    intro validator member
    obtain ⟨i, inside, rfl⟩ := Array.getElem_of_mem member
    have insidePaid : i < paid.validators.data.size := by
      rw [← (sameSizes_processEffectiveBalanceUpdates updatedOk).1]
      exact inside
    obtain ⟨effectiveBalance, read, choice⟩ := processEffectiveBalanceUpdates_effectiveBalance
      updatedOk (Array.getElem?_eq_getElem insidePaid)
      (Array.getElem?_eq_getElem (by rw [matched9]; exact insidePaid))
    rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at read
    rw [read]
    have cap := withdrawalMaxEffectiveBalance_le_drawCap electra activationCap
      paid.validators.data[i]
    rcases choice with same | ⟨-, le⟩
    · have old := capped7 paid.validators.data[i] (by
        rw [← validators9Deposited]
        exact Array.getElem_mem insidePaid)
      rw [← same] at old
      exact Nat.le_trans (UInt64.le_iff_toNat_le.mp old) cap
    · exact Nat.le_trans (UInt64.le_iff_toNat_le.mp le) cap
  have size10 : updated.validators.data.size ≤ registryLoad state := by
    rw [(sameSizes_processEffectiveBalanceUpdates updatedOk).1, validators9Deposited]
    exact size7Load
  have slot10 : updated.slot = state.slot := by
    rw [frame10, slot9, frame8.slot, frame7.slot, frame6, frame5, slot4, slot3]
  have summaries10 : updated.historicalSummaries = state.historicalSummaries := by
    rw [frame10, summaries9, summaries8, summaries7, frame6, frame5]
    show registered.historicalSummaries = _
    rw [fields4.2.2.2.2.2.1, frame3, frame2, frame1]
  -- The resets and the update of the summaries need only a next slot.
  obtain ⟨cleared, clearedOk⟩ := processSlashingsReset_total (state := updated)
    (by rw [slot10]; exact next)
  obtain ⟨_, _, _, _, frame11⟩ := processSlashingsReset_eq clearedOk
  obtain ⟨mixed, mixedOk⟩ := processRandaoMixesReset_total (state := cleared)
    (by rw [frame11]; exact slot10 ▸ next)
  obtain ⟨_, _, _, _, _, _, frame12⟩ := processRandaoMixesReset_eq mixedOk
  obtain ⟨rooted, rootedOk⟩ := processHistoricalSummariesUpdate_total (state := mixed) capella
    (by rw [frame12, frame11]; exact slot10 ▸ next)
    (by rw [frame12, frame11, summaries10]; exact summariesRoom)
  obtain ⟨slot13, validators13⟩ : rooted.slot = state.slot ∧
      rooted.validators = updated.validators := by
    obtain ⟨-, kept⟩ := processHistoricalSummariesUpdate_eq rootedOk
    split at kept
    · obtain ⟨_, _, _, _, _, rest⟩ := kept
      have slot : rooted.slot = mixed.slot := by rw [← rest]
      have validators : rooted.validators = mixed.validators := by rw [← rest]
      rw [slot, validators, frame12, frame11, slot10]
      exact ⟨rfl, rfl⟩
    · rw [kept, frame12, frame11, slot10]
      exact ⟨rfl, rfl⟩
  -- The rotation of the flags keeps the slot, which the draws then read.
  let flagged := processParticipationFlagUpdates rooted altair
  have currentEpochFlagged : getCurrentEpoch flagged = getCurrentEpoch state := by
    simp only [getCurrentEpoch, show flagged.slot = rooted.slot from rfl, slot13]
  have readyTrace : EpochTrace (action config checks) readyStages state flagged :=
    .cons (action_cases.mpr justifiedOk)
      (.cons (action_cases.mpr (by simp only [Edge, altair, ↓reduceDIte]; exact inactiveOk))
      (.cons (action_cases.mpr rewardedOk) (.cons registeredAction (.cons slashedAction
      (.cons resetOk (.cons depositedAction (.cons consolidatedAction (.cons paidAction
      (.cons (action_cases.mpr updatedOk) (.cons (action_cases.mpr clearedOk)
      (.cons (action_cases.mpr mixedOk)
      (.cons (action_cases.mpr (by simp only [Edge, capella, ↓reduceDIte]; exact rootedOk))
      (.cons (action_cases.mpr (by simp only [Edge, altair, ↓reduceDIte, flagged]))
        .nil)))))))))))))
  -- The sync committee is drawn at the end of a period, from the state the steps reach.
  have validatorsFlagged : flagged.validators = updated.validators := validators13
  obtain ⟨synced, syncedOk⟩ := processSyncCommitteeUpdates_ok altair
    (by rw [currentEpochFlagged]; omega) lookahead members
    (fun boundary => by
      have boundary : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 :=
        by rw [← currentEpochFlagged]; exact boundary
      have ran := run_ok_iff.mpr readyTrace
      have fewFlagged : flagged.validators.data.size ≤ 2 ^ 40 := by
        rw [validatorsFlagged]
        omega
      refine ⟨keys boundary flagged ran, fewFlagged, ?_⟩
      rw [currentEpochFlagged]
      exact syncEnds boundary flagged ran (by rw [validatorsFlagged]; exact capped10) fewFlagged
        (by
          rw [validatorsFlagged]
          exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ size10) syncRoom))
  have validatorsSynced : synced.validators = updated.validators := by
    rw [← validatorsFlagged]
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals rfl
  have syncedTrace : EpochTrace (action config checks) (readyStages ++ [.syncCommittees])
      state synced :=
    append_iff.mpr ⟨flagged, readyTrace,
      .cons (action_cases.mpr (by simp only [Edge, altair, ↓reduceDIte]; exact syncedOk)) .nil⟩
  have currentEpochSynced : getCurrentEpoch synced = getCurrentEpoch state := by
    simp only [getCurrentEpoch, (frame_processSyncCommitteeUpdates syncedOk).slot]
    exact currentEpochFlagged
  -- From Fulu the lookahead of the proposers moves by one epoch.
  obtain ⟨moved, movedOk, slotMoved, validatorsMoved⟩ : ∃ moved,
      action config checks .proposerLookahead synced = .ok moved ∧ moved.slot = synced.slot ∧
        moved.validators = synced.validators := by
    by_cases fulu : Fork.fusaka ≤ fork
    · have fewSynced : synced.validators.data.size ≤ 2 ^ 40 := by
        rw [validatorsSynced]
        omega
      obtain ⟨moved, ok, same⟩ := processProposerLookahead_ok fulu
        (by rw [currentEpochSynced]; exact seedRoom) lookahead
        (by rw [currentEpochSynced]; exact slotRoom)
        (by
          rw [currentEpochSynced]
          exact ⟨fewSynced, proposersEnd fulu synced (run_ok_iff.mpr syncedTrace)
            (by rw [validatorsSynced]; exact capped10) fewSynced⟩)
      exact ⟨moved, action_cases.mpr (by simp only [Edge, fulu, ↓reduceDIte]; exact ok),
        by rw [same], by rw [same]⟩
    · exact ⟨synced, action_cases.mpr (by simp only [Edge, fulu, ↓reduceDIte]), rfl, rfl⟩
  have movedTrace : EpochTrace (action config checks)
      (readyStages ++ [.syncCommittees, .proposerLookahead]) state moved := by
    obtain ⟨middle, ready, last⟩ := append_iff.mp syncedTrace
    exact append_iff.mpr ⟨middle, ready, by
      obtain _ | ⟨first, rest⟩ := last
      cases rest
      exact .cons first (.cons movedOk .nil)⟩
  have currentEpochMoved : getCurrentEpoch moved = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slotMoved]
    exact currentEpochSynced
  -- From Gloas the window of the payload committees moves by one epoch.
  obtain ⟨windowed, windowedOk⟩ : ∃ windowed,
      action config checks .ptcWindow moved = .ok windowed := by
    by_cases gloas : Fork.glamsterdam ≤ fork
    · obtain ⟨windowed, ok, -⟩ := processPtcWindow_ok gloas
        (by rw [currentEpochMoved]; exact seedRoom) lookahead
        (by rw [currentEpochMoved]; exact slotRoom) positive.slotsPerEpoch
        (by
          rw [currentEpochMoved]
          have size : moved.validators.data.size ≤ registryLoad state := by
            rw [validatorsMoved, validatorsSynced]
            exact size10
          obtain ⟨ptcFits, committeeFits⟩ := ptcRoom gloas
          have fewMoved : moved.validators.data.size ≤ 2 ^ 40 := by omega
          refine ⟨ptcEnd gloas moved (run_ok_iff.mpr movedTrace) ?_ fewMoved
            (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ size) ptcFits), fewMoved,
            Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ size))
              committeeFits⟩
          rw [validatorsMoved, validatorsSynced]
          exact capped10)
      exact ⟨windowed, action_cases.mpr (by simp only [Edge, gloas, ↓reduceDIte]; exact ok)⟩
    · exact ⟨moved, action_cases.mpr (by simp only [Edge, gloas, ↓reduceDIte])⟩
  refine ⟨windowed, ?_⟩
  have whole : epochStages = readyStages ++ [.syncCommittees, .proposerLookahead, .ptcWindow] :=
    rfl
  rw [processEpoch_eq_run, whole]
  obtain ⟨middle, ready, last⟩ := append_iff.mp movedTrace
  obtain _ | ⟨first, rest⟩ := last
  obtain _ | ⟨second, rest⟩ := rest
  cases rest
  exact run_ok_iff.mpr (append_iff.mpr ⟨middle, ready,
    .cons first (.cons second (.cons windowedOk .nil))⟩)

end EthLib.Consensus
