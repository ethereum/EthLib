module

public import EthLib.Consensus.Proofs.Transition.Totality.ChainHolds

/-!
# Proofs: every slot advance within the horizon succeeds on a bounded state

A run of slots advances a state one slot at a time, with the upgrades due on the way.

Each state that it reaches keeps the invariant, the shape of the state and the bounds of the run.

So every slot advance within the horizon succeeds, under three hypotheses on the states reached.

From Electra, a run of empty slots leaks.

The hypothesis on the draws then fails within about `7.7 * 10^5` epochs.

On mainnet the bounds alone hold for `2.25 * 10^6` epochs, about 27 years.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The facts that each state of a bounded run of slots keeps.

The run starts at a given epoch, and the bounds count the epochs since then.

Before Altair, the pending attestations are as block processing stored and checked them. -/
structure RunHolds (config : Config) (start : RunStart) (budget startEpoch : Nat) {fork : Fork}
    (state : BeaconState preset fork) : Prop where
  /-- The state is at the first epoch of the run or later. -/
  started : startEpoch ≤ (getCurrentEpoch state).toNat
  /-- The state keeps the invariant of the state transition. -/
  invariant : Invariant state
  /-- The state keeps its shape. -/
  shaped : Shaped state
  /-- Each pending attestation has its slot in its epoch, a nonzero delay, and a known proposer. -/
  wellFormed : PendingWellFormed state
  /-- The committee and the signers of each pending attestation succeed. -/
  resolved : PendingResolved state
  /-- In the first two epochs after genesis, the two justified checkpoints are equal. -/
  early : JustifiedEarly state
  /-- Each pending attestation has the target and the source that its block checked. -/
  voted : PendingVoted Set.univ state
  /-- The bounds of the run hold, after as many epochs as the state is past the first one. -/
  bounded : RunBounded config start budget ((getCurrentEpoch state).toNat - startEpoch) state
  /-- From the second epoch of the run, no one has signed in the current epoch. -/
  quietCurrent : startEpoch < (getCurrentEpoch state).toNat → QuietCurrent state
  /-- From the third epoch of the run, no one has signed. -/
  quiet : startEpoch + 2 ≤ (getCurrentEpoch state).toNat → Quiet state

/-- A state that keeps the facts of a run keeps those of a chain whose blocks raise no bound. -/
theorem RunHolds.toChainHolds {start : RunStart} {budget startEpoch : Nat} {fork : Fork}
    {state : BeaconState preset fork} (holds : RunHolds config start budget startEpoch state) :
    ChainHolds config start BlockStep.zero budget startEpoch 0 state := by
  refine ⟨holds.started, holds.invariant, holds.shaped, holds.wellFormed, holds.resolved,
    holds.early, holds.voted, Nat.zero_le _, ?_⟩
  rw [RunStart.afterBlocks_zero]
  exact holds.bounded

/-! ## One slot -/

/-- A state of a chain whose blocks raise no bound, with the absence of signers, is in a run. -/
private theorem RunHolds.of_chainHolds {start : RunStart} {budget startEpoch blocks : Nat}
    {fork : Fork}
    {state : BeaconState preset fork}
    (holds : ChainHolds config start BlockStep.zero budget startEpoch blocks state)
    (quietCurrent : startEpoch < (getCurrentEpoch state).toNat → QuietCurrent state)
    (quiet : startEpoch + 2 ≤ (getCurrentEpoch state).toNat → Quiet state) :
    RunHolds config start budget startEpoch state := by
  have bounded := holds.bounded
  rw [RunStart.afterBlocks_zero] at bounded
  exact ⟨holds.started, holds.invariant, holds.shaped, holds.wellFormed, holds.resolved,
    holds.early, holds.voted, bounded, quietCurrent, quiet⟩

/-- At the end of each epoch of a run, the signers hold at most the active balance.

In the first two epochs of the run this is the hypothesis, and after them no one has signed. -/
private theorem RunHolds.signers {start : RunStart} {budget startEpoch : Nat} {fork : Fork}
    {state : BeaconState preset fork} (holds : RunHolds config start budget startEpoch state)
    (signers : (getCurrentEpoch state).toNat < startEpoch + 2 →
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot state = .ok cached → SignersWithinActive cached) :
    (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot state = .ok cached → SignersWithinActive cached := by
  intro boundary cached cachedOk
  by_cases early : (getCurrentEpoch state).toNat < startEpoch + 2
  · exact signers early boundary cached cachedOk
  · obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact (holds.quiet (by omega)).signers

/-- One slot keeps the absence of signers of a run, with the upgrades on the way. -/
private theorem RunHolds.quiet_of_advanceSlotAcross {start : RunStart} {budget startEpoch : Nat}
    {forked next : ForkedBeaconState preset}
    (holds : RunHolds config start budget startEpoch forked.state)
    (computed : advanceSlotAcross config checks forked = .ok next) :
    (startEpoch < (getCurrentEpoch next.state).toNat → QuietCurrent next.state) ∧
      (startEpoch + 2 ≤ (getCurrentEpoch next.state).toNat → Quiet next.state) := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  have epochEq : getCurrentEpoch next.state = getCurrentEpoch advanced := by
    unfold getCurrentEpoch
    rw [processUpgrades_slot upgraded]
  rw [epochEq]
  -- The epoch moves on by at most one.
  have moves : (getCurrentEpoch advanced).toNat = (getCurrentEpoch forked.state).toNat ∨
      (getCurrentEpoch advanced).toNat = (getCurrentEpoch forked.state).toNat + 1 := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, advanceSlot_slot advancedOk,
      Nat.succ_div]
    split <;> simp
  refine ⟨fun late => ?_, fun late => ?_⟩
  · refine QuietCurrent.of_processUpgrades (forked := ⟨forked.fork, advanced⟩) ?_ upgraded
    change QuietCurrent advanced
    rcases moves with same | crossed
    · exact (holds.quietCurrent (by omega)).of_advanceSlot advancedOk
    · exact advanceSlot_quietCurrent_of_lt advancedOk (by omega)
  · refine Quiet.of_processUpgrades (forked := ⟨forked.fork, advanced⟩) ?_ upgraded
    change Quiet advanced
    rcases moves with same | crossed
    · exact (holds.quiet (by omega)).of_advanceSlot advancedOk
    · exact (holds.quietCurrent (by omega)).quiet_of_advanceSlot_of_lt advancedOk (by omega)

/-- One slot of a bounded run succeeds, with the upgrades due at the slot it reaches.

The epoch of the next slot is at most the first epoch of the run plus the number of epochs.

The run then ends by the last epoch of the conditions.

At the end of an epoch, the draws meet a validator at the cap.

In the first two epochs of the run, the signers hold at most the active balance.

The draws of the upgrades due at the next slot meet a validator at the cap.

Before Altair, the epoch is within the limit before Altair. -/
theorem RunHolds.advanceSlotAcross_exists_ok
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch startEpoch : Nat}
    {forked : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget startEpoch forked.state)
    (within : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : (getCurrentEpoch forked.state).toNat < startEpoch + 2 →
      (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → SignersWithinActive cached)
    (draws : (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → EpochDraws config checks cached)
    (upgradeDraws : ∀ advanced, advanceSlot config checks forked.state = .ok advanced →
      ∀ upgrading, UpgradesPass config checks ⟨forked.fork, advanced⟩ upgrading →
        upgradeDue config upgrading = true → UpgradeDraws upgrading)
    (limit : forked.fork < .altair →
      (getCurrentEpoch forked.state).toNat ≤ preset.epochLimitBeforeAltair) :
    ∃ next, advanceSlotAcross config checks forked = .ok next := by
  exact ChainHolds.advanceSlotAcross_exists_ok conditions.toChain fits holds.toChainHolds within
    (holds.signers signers) draws upgradeDraws limit

/-- One slot of a bounded run keeps the facts of the run, with the upgrades on the way.

The epoch of the next slot is at most the first epoch of the run plus the number of epochs.

The run then ends by the last epoch of the conditions.

In the first two epochs of the run, the signers hold at most the active balance. -/
theorem RunHolds.of_advanceSlotAcross {start : RunStart}
    {budget epochs lastEpoch startEpoch : Nat} {forked next : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget startEpoch forked.state)
    (within : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : (getCurrentEpoch forked.state).toNat < startEpoch + 2 →
      (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → SignersWithinActive cached)
    (computed : advanceSlotAcross config checks forked = .ok next) :
    RunHolds config start budget startEpoch next.state := by
  obtain ⟨quietCurrent, quiet⟩ := holds.quiet_of_advanceSlotAcross computed
  exact RunHolds.of_chainHolds (ChainHolds.of_advanceSlotAcross conditions.toChain fits
    holds.toChainHolds within (holds.signers signers) computed) quietCurrent quiet

/-- A run of slots from a state of a run succeeds and keeps the facts of the run.

The hypotheses on the states it reaches read the first epoch of the run. -/
private theorem advanceSlotsAcross_run
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch startEpoch : Nat}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch) :
    ∀ (count : Nat) {forked : ForkedBeaconState preset},
      RunHolds config start budget startEpoch forked.state →
      (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs →
      (∀ steps < count, ∀ reached, advanceSlotsAcross config checks steps forked = .ok reached →
        (getCurrentEpoch reached.state).toNat < startEpoch + 2 →
        (reached.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
        ∀ cached, processSlot reached.state = .ok cached → SignersWithinActive cached) →
      DrawsAtCap config checks forked count → EpochLimitBeforeAltair forked count →
      ∃ after, advanceSlotsAcross config checks count forked = .ok after ∧
        RunHolds config start budget startEpoch after.state
  | 0, forked, holds, _, _, _, _ => ⟨forked, rfl, holds⟩
  | count + 1, forked, holds, within, signers, draws, limit => by
    have stepWithin : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤
        startEpoch + epochs :=
      (Nat.div_le_div_right (by omega)).trans within
    have stepSigners := signers 0 (Nat.succ_pos _) forked rfl
    obtain ⟨stepDraws, stepUpgradeDraws⟩ := draws 0 (Nat.succ_pos _) forked rfl
    have stepLimit : forked.fork < .altair →
        (getCurrentEpoch forked.state).toNat ≤ preset.epochLimitBeforeAltair := fun before => by
      rw [getCurrentEpoch_toNat]
      exact (Nat.div_le_div_right (by omega)).trans (limit before)
    obtain ⟨next, nextOk⟩ := RunHolds.advanceSlotAcross_exists_ok conditions fits holds
      stepWithin stepSigners stepDraws stepUpgradeDraws stepLimit
    have nextHolds := RunHolds.of_advanceSlotAcross conditions fits holds stepWithin
      stepSigners nextOk
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp nextOk
    have nextSlot : next.state.slot.toNat = forked.state.slot.toNat + 1 := by
      rw [processUpgrades_slot upgraded]
      exact advanceSlot_slot advancedOk
    have nextFork : forked.fork ≤ next.fork :=
      processUpgrades_fork_le (forked := ⟨forked.fork, advanced⟩) upgraded
    -- The rest of the run starts from the next state, one step later.
    have shifted : ∀ {steps reached}, advanceSlotsAcross config checks steps next = .ok reached →
        advanceSlotsAcross config checks (steps + 1) forked = .ok reached := fun reachedOk => by
      simp only [advanceSlotsAcross, nextOk, bind, Except.bind]
      exact reachedOk
    obtain ⟨after, afterOk, afterHolds⟩ := advanceSlotsAcross_run conditions fits count
      (forked := next) nextHolds (by rwa [nextSlot, Nat.add_right_comm, Nat.add_assoc])
      (fun steps below reached reachedOk =>
        signers (steps + 1) (by omega) reached (shifted reachedOk))
      (fun steps below reached reachedOk =>
        draws (steps + 1) (by omega) reached (shifted reachedOk))
      (fun before => by
        rw [nextSlot, Nat.add_right_comm, Nat.add_assoc]
        exact limit (Nat.lt_of_le_of_lt nextFork before))
    exact ⟨after, by simp only [advanceSlotsAcross, nextOk, bind, Except.bind]; exact afterOk,
      afterHolds⟩

/-! ## The run -/

/-- A run of slots from a bounded state succeeds and keeps the facts of the run.

The run starts at the epoch of the state, and its last slot is at most that many epochs later.

The run takes its three hypotheses on the states it reaches. -/
theorem advanceSlotsAcross_exists_ok_of_run
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch count : Nat}
    {forked : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : (getCurrentEpoch forked.state).toNat + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget (getCurrentEpoch forked.state).toNat forked.state)
    (within : (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤
      (getCurrentEpoch forked.state).toNat + epochs)
    (signers : SignersEarly config checks forked count)
    (draws : DrawsAtCap config checks forked count)
    (limit : EpochLimitBeforeAltair forked count) :
    ∃ after, advanceSlotsAcross config checks count forked = .ok after ∧
      RunHolds config start budget (getCurrentEpoch forked.state).toNat after.state :=
  advanceSlotsAcross_run conditions fits count holds within signers draws limit

/-- Every slot advance within the horizon succeeds from a bounded state.

The state keeps the facts of a run that starts at its own epoch.

The conditions hold for some number of epochs, which is within the horizon of the scores.

Their last epoch is at least that number of epochs past the epoch of the state.

The later slot is in an epoch at most that number of epochs past the epoch of the state.

The run takes three hypotheses on the states it reaches.

In its first two epochs, the signers hold at most the active balance.

The draws meet a validator at the cap, and before Altair the run ends within the epoch limit.

The state that the advance returns keeps the facts of the run. -/
theorem processSlotsAcross_exists_ok_of_run
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch : Nat}
    {forked : ForkedBeaconState preset} {slot : Slot}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : (getCurrentEpoch forked.state).toNat + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget (getCurrentEpoch forked.state).toNat forked.state)
    (later : forked.state.slot < slot)
    (within : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      (getCurrentEpoch forked.state).toNat + epochs)
    (signers : SignersEarly config checks forked (slot.toNat - forked.state.slot.toNat))
    (draws : DrawsAtCap config checks forked (slot.toNat - forked.state.slot.toNat))
    (limit : EpochLimitBeforeAltair forked (slot.toNat - forked.state.slot.toNat)) :
    ∃ after, processSlotsAcross config checks forked slot = .ok after ∧
      RunHolds config start budget (getCurrentEpoch forked.state).toNat after.state := by
  have ahead := UInt64.lt_iff_toNat_lt.mp later
  obtain ⟨after, afterOk, afterHolds⟩ := advanceSlotsAcross_exists_ok_of_run conditions fits
    holds (by rwa [Nat.add_sub_cancel' ahead.le]) signers draws limit
  refine ⟨after, ?_, afterHolds⟩
  have ensured : ensure (forked.state.slot < slot)
      (TransitionError.slotNotAfter slot forked.state.slot) = .ok () := ensure_ok_iff.mpr later
  simp only [processSlotsAcross, ensured, bind, Except.bind]
  exact afterOk

/-- On mainnet, every slot advance within `2.25 * 10^6` epochs succeeds from a bounded state.

The epoch of the state is at most `2^40`.

The state keeps the facts of a run from its epoch, with the mainnet bounds at the start.

The budget of effective balances is `2^57` Gwei.

The run takes the three hypotheses on the states it reaches.

From Electra, the leak takes every validator off the cap of 2048 ETH.

It does so within about `7.7 * 10^5` epochs.

From a balance at the cap, it takes 68 epochs. -/
theorem processSlotsAcross_exists_ok_mainnet {forked : ForkedBeaconState Preset.mainnet}
    {slot : Slot} (early : (getCurrentEpoch forked.state).toNat ≤ 2 ^ 40)
    (holds : RunHolds Config.mainnet (RunStart.mainnet (getCurrentEpoch forked.state).toNat)
      (2 ^ 57) (getCurrentEpoch forked.state).toNat forked.state)
    (later : forked.state.slot < slot)
    (within : slot.toNat / Preset.mainnet.SLOTS_PER_EPOCH.toNat ≤
      (getCurrentEpoch forked.state).toNat + 2250000)
    (signers : SignersEarly Config.mainnet checks forked (slot.toNat - forked.state.slot.toNat))
    (draws : DrawsAtCap Config.mainnet checks forked (slot.toNat - forked.state.slot.toNat))
    (limit : EpochLimitBeforeAltair forked (slot.toNat - forked.state.slot.toNat)) :
    ∃ after, processSlotsAcross Config.mainnet checks forked slot = .ok after ∧
      RunHolds Config.mainnet (RunStart.mainnet (getCurrentEpoch forked.state).toNat) (2 ^ 57)
        (getCurrentEpoch forked.state).toNat after.state :=
  processSlotsAcross_exists_ok_of_run (runConditions_mainnet early) (Nat.le_refl _) holds later
    within signers draws limit

/-! ## A start that meets the facts -/

/-- The empty state at genesis, before any deposit, keeps the facts of a run from its epoch.

It meets any bounds at the start and any budget, since it has no validator and no balance. -/
theorem runHolds_emptyGenesisState {fork : Fork} (before : fork < .altair) (start : RunStart)
    (budget : Nat) (genesisTime : UInt64) (eth1BlockHash : Hash32) (depositCount : UInt64)
    (bodyRoot : Root) :
    RunHolds config start budget 0 (emptyGenesisState (preset := preset) config before
      genesisTime eth1BlockHash depositCount bodyRoot) := by
  have never : ∀ {later : Fork}, .altair ≤ later → ¬ later ≤ fork := fun altair atLeast =>
    absurd (Nat.lt_of_lt_of_le before (Nat.le_trans altair atLeast)) (by simp)
  have quiet := emptyGenesisState_quiet (preset := preset) (config := config) before genesisTime
    eth1BlockHash depositCount bodyRoot
  have notAltair : ¬ .altair ≤ fork := fun altair => never altair (Nat.le_refl _)
  have notElectra : ¬ .pectra ≤ fork := never (by decide)
  refine
    { started := Nat.zero_le _
      invariant := emptyGenesisState_invariant before _ _ _ _
      shaped := ?_
      wellFormed := ?_
      resolved := ?_
      early := fun _ => rfl
      voted := ?_
      bounded := ?_
      quietCurrent := fun _ => quiet.1
      quiet := fun _ => quiet }
  · exact ⟨rfl, fun altair => (notAltair altair).elim, fun altair => (notAltair altair).elim,
      fun _ member => by simp [emptyGenesisState] at member,
      fun electra => (notElectra electra).elim⟩
  · exact fun _ => ⟨fun _ member => by simp [emptyGenesisState] at member,
      fun _ member => by simp [emptyGenesisState] at member⟩
  · intro _ _ member
    simp [emptyGenesisState] at member
  · intro _ current _ member
    cases current <;> simp [recentPending, emptyGenesisState] at member
  refine ⟨?_, Or.inl ?_, ?_, fun altair => (notAltair altair).elim,
    fun _ member => by simp [emptyGenesisState] at member,
    fun electra => (notElectra electra).elim, ?_, fun capella => (never (by decide) capella).elim,
    fun electra => (notElectra electra).elim, fun electra => (notElectra electra).elim, ?_⟩
  all_goals simp [balanceSum, pendingDepositSum, effectiveBalanceSum, registryLoad,
    slashedBalanceSum, emptyGenesisState, notElectra]

/-- On mainnet, from the empty state at genesis, every slot advance before Altair succeeds.

So the hypotheses of the mainnet theorem can hold together, with an empty registry before Altair.
-/
theorem processSlotsAcross_exists_ok_emptyGenesisState {slot : Slot} (later : 0 < slot.toNat)
    (beforeAltair : slot.toNat / 32 < 74240) (genesisTime : UInt64) (eth1BlockHash : Hash32)
    (depositCount : UInt64) (bodyRoot : Root) :
    ∃ after, processSlotsAcross Config.mainnet checks
      ⟨.phase0, emptyGenesisState (preset := Preset.mainnet) Config.mainnet (by decide)
        genesisTime eth1BlockHash depositCount bodyRoot⟩ slot = .ok after := by
  have before : Fork.phase0 < .altair := by decide
  have slot0 : (emptyGenesisState (preset := Preset.mainnet) Config.mainnet before genesisTime
      eth1BlockHash depositCount bodyRoot).slot.toNat = 0 := rfl
  have epoch : (getCurrentEpoch (emptyGenesisState (preset := Preset.mainnet) Config.mainnet
      before genesisTime eth1BlockHash depositCount bodyRoot)).toNat = 0 := by
    simp [getCurrentEpoch, computeEpochAtSlot, emptyGenesisState, GENESIS_SLOT]
  obtain ⟨signers, draws, limit⟩ := runHypotheses_mainnet (checks := checks)
    (count := slot.toNat) (emptyGenesisState_quiet before genesisTime eth1BlockHash depositCount
      bodyRoot) (by rw [slot0, Nat.zero_add]; exact beforeAltair)
  have holds := runHolds_emptyGenesisState (preset := Preset.mainnet) (config := Config.mainnet)
    before (RunStart.mainnet 0) (2 ^ 57) genesisTime eth1BlockHash depositCount bodyRoot
  obtain ⟨after, computed, -⟩ := processSlotsAcross_exists_ok_mainnet (checks := checks)
    (forked := ⟨.phase0, emptyGenesisState Config.mainnet before genesisTime eth1BlockHash
      depositCount bodyRoot⟩) (slot := slot)
    (by rw [epoch]; exact Nat.zero_le _) (by rw [epoch]; exact holds)
    (UInt64.lt_iff_toNat_lt.mpr (by rw [slot0]; exact later))
    (by rw [epoch]; change slot.toNat / 32 ≤ 0 + 2250000; omega)
    (by rw [slot0, Nat.sub_zero]; exact signers) (by rw [slot0, Nat.sub_zero]; exact draws)
    (by rw [slot0, Nat.sub_zero]; exact limit)
  exact ⟨after, computed⟩

end EthLib.Consensus
