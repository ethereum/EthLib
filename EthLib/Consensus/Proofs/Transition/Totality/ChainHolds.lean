module

public import EthLib.Consensus.Proofs.Transition.TargetUpgrades
public import EthLib.Consensus.Proofs.Transition.Totality.PendingBlock
public import EthLib.Consensus.Proofs.Transition.Totality.RunStep
public import EthLib.Consensus.Proofs.Transition.Totality.RunUpgrades
public import EthLib.Consensus.Proofs.Transition.Totality.Slot
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock
import EthLib.Consensus.Proofs.Transition.Totality.FlagWeight

/-!
# Proofs: the facts that a chain of slots and blocks keeps

A chain alternates runs of slots and blocks.

Its states keep the invariant, the shape of the state and the bounds of a run.

A block may raise some of those bounds, by at most a fixed amount for each block.

The rewards that blocks pay for attestations raise the supply once in each epoch instead.

At most one block lands in each slot, so the slots since the start bound the number of blocks.

Each empty slot keeps these facts, and succeeds, under hypotheses on the state it reaches.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The bounds that blocks raise -/

/-- The amounts by which blocks may raise the bounds of a run, in each block or in each epoch. -/
structure BlockStep where
  /-- The rise of the balances plus the pending deposits. -/
  supply : Nat
  /-- The rise of the sum of the effective balances. -/
  effective : Nat
  /-- The rise of the registry load, counted twice before Electra. -/
  load : Nat
  /-- The rise of the exit ceiling. -/
  ceiling : Nat
  /-- The rise of the sum of the slashed balances. -/
  slashed : Nat
  /-- The rise of the supply in each epoch, from what its blocks pay for attestations. -/
  rewards : Nat

/-- The block step that raises no bound. -/
def BlockStep.zero : BlockStep :=
  { supply := 0, effective := 0, load := 0, ceiling := 0, slashed := 0, rewards := 0 }

/-- The bounds at the start of a run, raised by some number of blocks. -/
def RunStart.afterBlocks (start : RunStart) (step : BlockStep) (blocks : Nat) : RunStart :=
  { start with
    supply := start.supply + blocks * step.supply
    effective := start.effective + blocks * step.effective
    load := start.load + blocks * step.load
    ceiling := start.ceiling + blocks * step.ceiling
    slashed := start.slashed + blocks * step.slashed }

/-- Blocks that raise no bound leave the start unchanged. -/
theorem RunStart.afterBlocks_zero (start : RunStart) (blocks : Nat) :
    start.afterBlocks BlockStep.zero blocks = start := by
  cases start
  simp [RunStart.afterBlocks, BlockStep.zero]

/-- One more block adds the step to the supply, effective, load, ceiling and slashed bounds.

The other fields of the start stay as they are. -/
theorem RunStart.afterBlocks_succ (start : RunStart) (step : BlockStep) (blocks : Nat) :
    start.afterBlocks step (blocks + 1) =
      { start.afterBlocks step blocks with
        supply := (start.afterBlocks step blocks).supply + step.supply
        effective := (start.afterBlocks step blocks).effective + step.effective
        load := (start.afterBlocks step blocks).load + step.load
        ceiling := (start.afterBlocks step blocks).ceiling + step.ceiling
        slashed := (start.afterBlocks step blocks).slashed + step.slashed } := by
  simp only [RunStart.afterBlocks, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- The bounds at the start of a run, raised by some blocks and by the rewards of some epochs.

The supply rises by the rewards of each epoch so far, and of the current one. -/
def RunStart.afterChain (start : RunStart) (step : BlockStep) (blocks elapsed : Nat) : RunStart :=
  { start.afterBlocks step blocks with
    supply := (start.afterBlocks step blocks).supply + (elapsed + 1) * step.rewards }

/-- Blocks that raise no bound leave the start unchanged, after any number of epochs. -/
theorem RunStart.afterChain_zero (start : RunStart) (blocks elapsed : Nat) :
    start.afterChain BlockStep.zero blocks elapsed = start := by
  cases start
  simp [RunStart.afterChain, RunStart.afterBlocks, BlockStep.zero]

/-- The bounds of a run hold for a start with a larger bound on the supply. -/
theorem RunBounded.raiseSupply {fork : Fork} {state : BeaconState preset fork}
    {start : RunStart} {budget elapsed : Nat}
    (holds : RunBounded config start budget elapsed state) {supply : Nat}
    (le : start.supply ≤ supply) :
    RunBounded config { start with supply := supply } budget elapsed state := by
  refine ⟨?_, ?_, holds.load, holds.scores, holds.exits, holds.queue, holds.consolidations,
    holds.roots, holds.summaries, holds.depositChurn, holds.exitChurn, holds.slashed⟩
  · have := holds.supply
    dsimp only
    omega
  · -- The ratio of the hysteresis reads the bound on the supply, which only grows.
    rcases holds.effective with low | ratio
    · exact Or.inl low
    · exact Or.inr (ratio.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right le _)))

/-- The bounds of a run raised by a chain hold with the rewards of more epochs. -/
theorem RunBounded.afterChain_mono {fork : Fork} {state : BeaconState preset fork}
    {start : RunStart} {step : BlockStep} {budget blocks elapsed later counted : Nat}
    (holds : RunBounded config (start.afterChain step blocks elapsed) budget counted state)
    (le : elapsed ≤ later) :
    RunBounded config (start.afterChain step blocks later) budget counted state :=
  holds.raiseSupply (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_succ le)) _)

/-- The most blocks in the first epoch of a run and the epochs after it, one in each slot. -/
def Preset.chainBlocks (preset : Preset) (epochs : Nat) : Nat :=
  (epochs + 1) * preset.SLOTS_PER_EPOCH.toNat

/-- The conditions on a chain of slots and blocks that make each of its epochs and upgrades succeed.

They are the conditions of a run, raised by the most blocks that the chain holds.

The exit ceiling at the start must still cover the first epoch, with no block. -/
structure ChainConditions (preset : Preset) (config : Config) (start : RunStart)
    (step : BlockStep) (budget epochs lastEpoch : Nat) : Prop where
  /-- The conditions of a run, at the start raised by the most blocks and the rewards of epochs.

  The rewards count two epochs more than the epochs after the first one.

  One is the first epoch, and one covers the cap that a block reads on its own rewards. -/
  run : RunConditions preset config
    (start.afterChain step (preset.chainBlocks epochs) (epochs + 1)) budget epochs lastEpoch
  /-- The exit ceiling at the start covers the first epoch, plus one and the longest lookahead. -/
  firstStart : lastEpoch - epochs + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ start.ceiling

/-- The conditions of a chain hold for its start raised by blocks and the rewards of epochs.

The blocks are at most the most blocks of the chain.

The epochs are at most one more than the epochs after the first one. -/
theorem ChainConditions.at {start : RunStart} {step : BlockStep}
    {budget epochs lastEpoch blocks elapsed : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (within : blocks ≤ preset.chainBlocks epochs) (early : elapsed ≤ epochs + 1) :
    RunConditions preset config (start.afterChain step blocks elapsed) budget epochs lastEpoch := by
  have run := conditions.run
  -- Each raised bound is monotone in the number of blocks, and the supply in the epochs.
  have raised : ∀ base rise, base + blocks * rise ≤ base + preset.chainBlocks epochs * rise :=
    fun base rise => Nat.add_le_add_left (Nat.mul_le_mul_right rise within) base
  have supply : (start.afterChain step blocks elapsed).supply ≤
      (start.afterChain step (preset.chainBlocks epochs) (epochs + 1)).supply :=
    Nat.add_le_add (raised start.supply step.supply)
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ early))
  have effective := raised start.effective step.effective
  have load := raised start.load step.load
  have ceiling := raised start.ceiling step.ceiling
  have slashed := raised start.slashed step.slashed
  have exitStep : (start.afterChain step blocks elapsed).exitStep preset budget ≤
      (start.afterChain step (preset.chainBlocks epochs) (epochs + 1)).exitStep preset budget := by
    unfold RunStart.exitStep
    exact Nat.add_le_add_right (Nat.add_le_add_left load _) _
  have exitRoom := run.exitRoom
  have loadRoom := run.loadRoom
  unfold RunStart.ceilingAt at exitRoom
  exact { run with
    effectiveStart := le_trans (max_le_max le_rfl effective) run.effectiveStart
    supplyRatio := le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right supply _))
      run.supplyRatio
    supplyRoom := lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_right supply _) _)
      run.supplyRoom
    firstStart := le_trans conditions.firstStart (Nat.le_add_right _ _)
    exitRoom := lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add ceiling (Nat.mul_le_mul_left epochs exitStep)) exitStep)
      _) _) exitRoom
    slashed := fun fork => lt_of_le_of_lt (Nat.mul_le_mul_right _ slashed) (run.slashed fork)
    load := ⟨le_trans load run.load.1, le_trans load run.load.2.1, le_trans load run.load.2.2⟩
    loadRoom := ⟨lt_of_le_of_lt (Nat.mul_le_mul_left _ load) loadRoom.1,
      lt_of_le_of_lt (Nat.mul_le_mul_left _ load) loadRoom.2.1,
      lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ load)) loadRoom.2.2⟩ }

/-- The conditions of a run are those of a chain whose blocks raise no bound. -/
theorem RunConditions.toChain {start : RunStart} {budget epochs lastEpoch : Nat}
    (conditions : RunConditions preset config start budget epochs lastEpoch) :
    ChainConditions preset config start BlockStep.zero budget epochs lastEpoch := by
  refine ⟨?_, conditions.firstStart⟩
  rw [RunStart.afterChain_zero]
  exact conditions

/-! ## The facts of a chain -/

/-- The facts that each state of a chain of slots and blocks keeps.

The chain starts at a given epoch, and the bounds count the epochs since then.

They start from the bounds of the run, raised by the blocks of the chain so far.

The supply is also raised by the rewards that blocks pay for attestations, once in each epoch. -/
structure ChainHolds (config : Config) (start : RunStart) (step : BlockStep)
    (budget startEpoch blocks : Nat) {fork : Fork} (state : BeaconState preset fork) : Prop where
  /-- The state is at the first epoch of the chain or later. -/
  started : startEpoch ≤ (getCurrentEpoch state).toNat
  /-- The state keeps the invariant of the state transition. -/
  invariant : Invariant state
  /-- The state keeps its shape. -/
  shaped : Shaped state
  -- Before Altair, the pending attestations are as block processing stored and checked them.
  /-- Each pending attestation has its slot in its epoch, a nonzero delay, and a known proposer. -/
  wellFormed : PendingWellFormed state
  /-- The committee and the signers of each pending attestation succeed. -/
  resolved : PendingResolved state
  /-- In the first two epochs after genesis, the two justified checkpoints are equal. -/
  early : JustifiedEarly state
  /-- Each pending attestation has the target and the source that its block checked. -/
  voted : PendingVoted Set.univ state
  -- At most one block lands in each slot, so the slots since the start bound the number of blocks.
  /-- The blocks so far are at most one for each slot since the start of the first epoch. -/
  counted : blocks ≤ state.slot.toNat + 1 - startEpoch * preset.SLOTS_PER_EPOCH.toNat
  /-- The bounds hold after the epochs since the first one.

  They are raised by the blocks so far, and by the rewards of those epochs and the current one. -/
  bounded : RunBounded config
    (start.afterChain step blocks ((getCurrentEpoch state).toNat - startEpoch)) budget
    ((getCurrentEpoch state).toNat - startEpoch) state
  -- In an epoch, the blocks pay at most the rise of the weight of the flags, over 448.
  --
  -- That weight starts at zero or more, so the rises add up to at most the weight now.
  --
  -- The bound on the supply then counts the rewards of the past epochs, and not the current one.
  /-- Times 448, the supply is within the bound so far times 448, plus the weight of the flags.

  The bound so far is that of the blocks, and the rewards and the issuance of the past epochs. -/
  rewarded : 448 * (balanceSum state + pendingDepositSum state) ≤
    448 * ((start.afterBlocks step blocks).supply + ((getCurrentEpoch state).toNat - startEpoch) *
      (step.rewards + preset.epochIssuanceBeforeAltair budget)) +
    flagRewardWeight preset (blockPerIncrement preset state) state

/-! ## One empty slot -/

/-- The caching of a slot keeps the pending attestations resolved. -/
private theorem PendingResolved.of_processSlot {fork : Fork}
    {state cached : BeaconState preset fork}
    (resolved : PendingResolved state) (computed : processSlot state = .ok cached) :
    PendingResolved cached := by
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok computed
  intro before attestation member
  rw [cachedEq] at member
  obtain ⟨signers, ok⟩ := resolved before attestation member
  refine ⟨signers, ?_⟩
  unfold getPendingAttestingIndices at ok ⊢
  rw [CommitteesKept.of_eq (state := state) (other := cached) (by rw [cachedEq])
    (by rw [cachedEq]) (computeEpochAtSlot preset attestation.data.slot) attestation.data.slot
    attestation.data.index rfl]
  exact ok

/-- The caching of a slot keeps the facts of a chain. -/
private theorem ChainHolds.of_processSlot {start : RunStart} {step : BlockStep}
    {budget startEpoch blocks : Nat} {fork : Fork} {state cached : BeaconState preset fork}
    (holds : ChainHolds config start step budget startEpoch blocks state)
    (computed : processSlot state = .ok cached) :
    ChainHolds config start step budget startEpoch blocks cached := by
  have frame := frame_processSlot computed
  have resolved := holds.resolved.of_processSlot computed
  have voted := holds.voted.of_processSlot computed
  have blocksLe := holds.counted
  have bounded := holds.bounded.of_processSlot computed
  have invariant := frame.invariant holds.invariant
  have early := holds.early.of_frame frame
  have rewarded := holds.rewarded
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  have shaped := holds.shaped
  exact ⟨holds.started, invariant, ⟨shaped.balancesMatch, shaped.participationMatches,
    shaped.inactivityScoresMatch, shaped.capped, shaped.inside⟩, holds.wellFormed, resolved,
    early, voted, blocksLe, bounded, rewarded⟩

/-- A state of a chain within its epochs meets the conditions of a run at its blocks. -/
theorem ChainHolds.run {start : RunStart} {step : BlockStep}
    {budget epochs lastEpoch startEpoch blocks : Nat} {fork : Fork}
    {state : BeaconState preset fork}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (holds : ChainHolds config start step budget startEpoch blocks state)
    (counted : (getCurrentEpoch state).toNat ≤ startEpoch + epochs) :
    RunConditions preset config
      (start.afterChain step blocks ((getCurrentEpoch state).toNat - startEpoch)) budget epochs
      lastEpoch := by
  have blocksLe := holds.counted
  refine conditions.at ?_ (by omega)
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := conditions.run.slots
    omega
  rw [getCurrentEpoch_toNat] at counted
  -- The slot is before the end of the last epoch of the chain.
  have below := (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_of_le counted)
  have split : (startEpoch + epochs + 1) * preset.SLOTS_PER_EPOCH.toNat =
      startEpoch * preset.SLOTS_PER_EPOCH.toNat + preset.chainBlocks epochs := by
    unfold Preset.chainBlocks
    rw [Nat.add_assoc, Nat.add_mul]
  rw [Nat.succ_eq_add_one, split] at below
  omega

/-- An epoch of the run, plus one and the longest lookahead, is at most the exit ceiling there. -/
theorem RunConditions.first_le_ceilingAt {start : RunStart}
    {budget epochs lastEpoch startEpoch epoch : Nat}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch) (started : startEpoch ≤ epoch) :
    epoch + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget (epoch - startEpoch) := by
  have firstStart := conditions.firstStart
  have step : epoch - startEpoch ≤ (epoch - startEpoch) * start.exitStep preset budget :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold RunStart.ceilingAt
  omega

/-- A chain of upgrades extends by one more due upgrade. -/
private theorem UpgradesPass.snoc {first reached : ForkedBeaconState preset}
    {next : {post : ForkedBeaconState preset // reached.fork < post.fork}}
    (pass : UpgradesPass config checks first reached) (due : upgradeDue config reached = true)
    (computed : upgradeNext config checks reached = .ok next) :
    UpgradesPass config checks first next.val := by
  induction pass with
  | refl forked => exact .step due computed (.refl _)
  | step stepDue stepOk rest ih => exact .step stepDue stepOk (ih due computed)

/-- One slot keeps the facts of a chain, before the upgrades of the slot it reaches.

When the slot it reaches starts an epoch, a stronger bound on the supply holds there.

That bound counts the rewards of the past epochs, and not of the current one. -/
private theorem ChainHolds.of_advanceSlot {start : RunStart} {step : BlockStep}
    {budget epochs lastEpoch startEpoch blocks : Nat} {fork : Fork}
    {state advanced : BeaconState preset fork}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : ChainHolds config start step budget startEpoch blocks state)
    (within : (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot state = .ok cached → SignersWithinActive cached)
    (computed : advanceSlot config checks state = .ok advanced) :
    ChainHolds config start step budget startEpoch blocks advanced ∧
      (advanced.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 →
        ∃ elapsed, (getCurrentEpoch advanced).toNat - startEpoch = elapsed + 1 ∧
          RunBounded config (start.afterChain step blocks elapsed) budget (elapsed + 1)
            advanced) := by
  have stateEpoch := getCurrentEpoch_toNat state
  have advancedEpoch := getCurrentEpoch_toNat advanced
  have slot := advanceSlot_slot computed
  have bounded := holds.bounded
  have run := holds.run conditions (by
    rw [stateEpoch]
    exact (Nat.div_le_div_right (Nat.le_succ _)).trans within)
  have invariant := (advanceSlot_invariant holds.invariant computed).1
  have shaped := advanceSlot_shaped computed holds.shaped
  have wellFormed := holds.wellFormed.of_advanceSlot computed
  have resolved := holds.resolved.of_advanceSlot run.apart holds.wellFormed computed
  have early := holds.early.of_advanceSlot computed
  have voted : PendingVoted Set.univ advanced := by
    by_cases before : fork < .altair
    · exact holds.voted.of_advanceSlot before run.apart holds.early computed
    · exact PendingVoted.of_altair (Nat.le_of_not_lt before) advanced
  -- The epoch moves on by at most one.
  have moves : (getCurrentEpoch advanced).toNat = (getCurrentEpoch state).toNat ∨
      (getCurrentEpoch advanced).toNat = (getCurrentEpoch state).toNat + 1 := by
    rw [advancedEpoch, stateEpoch, slot, Nat.succ_div]
    split <;> simp
  have started : startEpoch ≤ (getCurrentEpoch advanced).toNat := by
    have := holds.started
    omega
  -- An empty slot keeps the count of blocks, and the bound on it only grows.
  have counted : blocks ≤ advanced.slot.toNat + 1 - startEpoch * preset.SLOTS_PER_EPOCH.toNat := by
    have := holds.counted
    rw [slot]
    omega
  have rewarded := holds.rewarded
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedHolds := holds.of_processSlot cachedOk
  have cachedBounded := bounded.of_processSlot cachedOk
  have cachedEpoch : (getCurrentEpoch cached).toNat = (getCurrentEpoch state).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, processSlot_slot cachedOk]
  have nextEpoch : (getCurrentEpoch { epoched with slot := next }).toNat =
      next.toNat / preset.SLOTS_PER_EPOCH.toNat := getCurrentEpoch_toNat _
  obtain ⟨boundary, epochedOk⟩ | ⟨inside, kept⟩ := epochIfLast_cases epochedOk
  · have crossed := nextSlot_epoch_of_boundary sum boundary
    have nextIs : (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch state).toNat + 1 := by
      rw [← sum, crossed, stateEpoch]
    have startedState := holds.started
    have boundaryNat : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat boundary
      rwa [UInt64.toNat_mod, sum] at this
    -- The epoch keeps the bounds at the rewards of the epochs so far, one epoch further on.
    have epochBounded := RunBounded.of_processEpoch_of_run run cachedBounded
      cachedHolds.invariant cachedHolds.shaped cachedHolds.resolved (by omega)
      (by rw [cachedEpoch]; exact run.first_le_ceilingAt fits holds.started)
      (signers boundaryNat cached cachedOk) epochedOk
    have elapsed : (getCurrentEpoch { epoched with slot := next }).toNat - startEpoch =
        (getCurrentEpoch state).toNat - startEpoch + 1 := by
      omega
    have freshBounded := epochBounded.withSlot next
    have supplyLe := freshBounded.supply
    refine ⟨⟨started, invariant, shaped, wellFormed, resolved, early, voted, counted, ?_, ?_⟩,
      fun _ => ⟨_, elapsed, freshBounded⟩⟩
    · rw [elapsed]
      exact freshBounded.afterChain_mono (Nat.le_succ _)
    · -- The new epoch starts with the rewards of the past epochs, so the weight is not needed.
      rw [elapsed]
      simp only [RunStart.afterChain] at supplyLe
      have split := Nat.mul_add ((getCurrentEpoch state).toNat - startEpoch + 1) step.rewards
        (preset.epochIssuanceBeforeAltair budget)
      omega
  · subst epoched
    have same := nextSlot_epoch_of_inside sum inside
    have elapsed : (getCurrentEpoch { cached with slot := next }).toNat - startEpoch =
        (getCurrentEpoch state).toNat - startEpoch := by
      omega
    have insideNat : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 := by
      intro zero
      apply inside
      rw [← UInt64.toNat_inj, UInt64.toNat_mod, sum]
      simpa using zero
    obtain ⟨-, epochSame, -, -, -, perIncrement, weight⟩ := advanceSlot_flagsKept computed insideNat
    refine ⟨⟨started, invariant, shaped, wellFormed, resolved, early, voted, counted, ?_, ?_⟩,
      fun zero => absurd (by rw [← sum]; exact zero) insideNat⟩
    · rw [elapsed]
      exact cachedBounded.withSlot next
    · -- A slot inside an epoch keeps the supply and the weight of the flags.
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      rw [elapsed, perIncrement, weight]
      exact rewarded

/-- The upgrades due at a slot keep the facts of a chain, while the epoch is within the chain.

At the first slot of an epoch, the stronger bound on the supply must hold. -/
private theorem ChainHolds.of_processUpgrades {start : RunStart} {step : BlockStep}
    {budget epochs lastEpoch startEpoch blocks : Nat} {forked after : ForkedBeaconState preset}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (counted : (getCurrentEpoch forked.state).toNat ≤ startEpoch + epochs)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    (fresh : forked.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∃ elapsed, (getCurrentEpoch forked.state).toNat - startEpoch = elapsed + 1 ∧
        RunBounded config (start.afterChain step blocks elapsed) budget (elapsed + 1) forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    ChainHolds config start step budget startEpoch blocks after.state := by
  by_cases first : forked.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0
  swap
  · -- Off the first slot of an epoch, no upgrade is due.
    have notDue : upgradeDue config forked = false := by
      unfold upgradeDue
      have : (forked.state.slot % preset.SLOTS_PER_EPOCH == 0) = false := by
        rw [beq_eq_false_iff_ne]
        intro zero
        apply first
        rw [← UInt64.toNat_mod, zero]
        rfl
      rw [this, Bool.false_and]
    rw [processUpgrades] at computed
    simp only [notDue, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds
  obtain ⟨elapsed, elapsedEq, freshBounded⟩ := fresh first
  have slotEq := processUpgrades_slot computed
  have epochEq : getCurrentEpoch after.state = getCurrentEpoch forked.state := by
    unfold getCurrentEpoch
    rw [slotEq]
  have bounded := holds.bounded
  have run := holds.run conditions counted
  have budgeted := bounded.effective_le run (by omega)
  have firstLe := run.first_le_ceilingAt fits holds.started
  have bounded := bounded.of_processUpgrades budgeted firstLe computed
  -- The stronger bound holds at the same ceiling, which does not read the supply.
  rw [elapsedEq] at firstLe
  have freshAfter := freshBounded.of_processUpgrades budgeted firstLe computed
  have supplyLe := freshAfter.supply
  refine ⟨?_, (processUpgrades_invariant holds.invariant computed).1,
    processUpgrades_shaped run.activation run.compounding computed holds.shaped,
    holds.wellFormed.of_processUpgrades computed, holds.resolved.of_processUpgrades computed,
    holds.early.of_processUpgrades computed, holds.voted.of_processUpgrades computed,
    by rw [slotEq]; exact holds.counted, ?_, ?_⟩
  · rw [epochEq]
    exact holds.started
  · rw [epochEq]
    exact bounded
  · -- The upgrades may change the weight of the flags, so this reads the stronger bound.
    rw [epochEq, elapsedEq]
    simp only [RunStart.afterChain] at supplyLe
    have split := Nat.mul_add (elapsed + 1) step.rewards (preset.epochIssuanceBeforeAltair budget)
    omega

/-- One slot of a chain keeps its facts, with the upgrades on the way.

The epoch of the next slot is at most the first epoch of the chain plus the number of epochs.

The chain then ends by the last epoch of the conditions.

At the end of an epoch, the signers hold at most the active balance. -/
theorem ChainHolds.of_advanceSlotAcross {start : RunStart} {step : BlockStep}
    {budget epochs lastEpoch startEpoch blocks : Nat} {forked next : ForkedBeaconState preset}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    (within : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → SignersWithinActive cached)
    (computed : advanceSlotAcross config checks forked = .ok next) :
    ChainHolds config start step budget startEpoch blocks next.state := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  have advancedEpoch : (getCurrentEpoch advanced).toNat ≤ startEpoch + epochs := by
    rw [getCurrentEpoch_toNat, advanceSlot_slot advancedOk]
    exact within
  obtain ⟨advancedHolds, fresh⟩ :=
    ChainHolds.of_advanceSlot conditions fits holds within signers advancedOk
  exact ChainHolds.of_processUpgrades (forked := ⟨forked.fork, advanced⟩) conditions fits
    advancedEpoch advancedHolds fresh upgraded

/-- One slot of a chain succeeds, with the upgrades due at the slot it reaches. -/
theorem ChainHolds.advanceSlotAcross_exists_ok
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {step : BlockStep} {budget epochs lastEpoch startEpoch blocks : Nat}
    {forked : ForkedBeaconState preset}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    -- The chain ends by the last epoch of the conditions.
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    -- The epoch of the next slot is at most the first epoch of the chain plus the epochs.
    (within : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    -- At the end of an epoch, the signers hold at most the active balance.
    --
    -- Blocks carry attestations, so this is a hypothesis at every epoch, not only early on.
    (signers : (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → SignersWithinActive cached)
    -- At the end of an epoch, the draws of the epoch transition end.
    (draws : (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → EpochDrawsEnd config checks cached)
    -- The draws of the upgrades due at the next slot end.
    (upgradeDraws : ∀ advanced, advanceSlot config checks forked.state = .ok advanced →
      ∀ upgrading, UpgradesPass config checks ⟨forked.fork, advanced⟩ upgrading →
        upgradeDue config upgrading = true → UpgradeDrawsEnd upgrading)
    -- Before Altair, the epoch is within the limit before Altair.
    (limit : forked.fork < .altair →
      (getCurrentEpoch forked.state).toNat ≤ preset.epochLimitBeforeAltair) :
    ∃ next, advanceSlotAcross config checks forked = .ok next := by
  have started := holds.started
  have stateEpoch := getCurrentEpoch_toNat forked.state
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := conditions.run.slots
    omega
  have bounded := holds.bounded
  have run := holds.run conditions (by
    rw [stateEpoch]
    exact (Nat.div_le_div_right (Nat.le_succ _)).trans within)
  -- The next slot is before the end of the last epoch, so it fits in 64 bits.
  have slotFits : forked.state.slot.toNat + 1 < 2 ^ 64 := by
    have room := run.slotRoom
    have below := Nat.lt_div_mul_add (a := forked.state.slot.toNat + 1) positive
    have scaled : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat *
        preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat ≤
        (lastEpoch + preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨advanced, advancedOk⟩ := advanceSlot_exists_ok (config := config) (checks := checks)
    slotFits fun boundary cached cachedOk => by
      have cachedHolds := holds.of_processSlot cachedOk
      have cachedEpoch : (getCurrentEpoch cached).toNat = (getCurrentEpoch forked.state).toNat := by
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, processSlot_slot cachedOk]
      have cachedBounded := bounded.of_processSlot cachedOk
      have nextIs : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
          (getCurrentEpoch forked.state).toNat + 1 := by
        rw [stateEpoch]
        exact Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero boundary)
      exact processEpoch_exists_ok_of_run run cachedBounded cachedHolds.invariant
        cachedHolds.shaped cachedHolds.wellFormed cachedHolds.resolved
        (by omega) (by omega) (by rwa [processSlot_slot cachedOk])
        (by rw [cachedEpoch]; exact run.first_le_ceilingAt fits holds.started)
        (signers boundary cached cachedOk)
        (draws boundary cached cachedOk) (fun before => cachedEpoch ▸ limit before)
  have advancedHolds :=
    (ChainHolds.of_advanceSlot conditions fits holds within signers advancedOk).1
  have advancedEpoch : (getCurrentEpoch advanced).toNat ≤ startEpoch + epochs := by
    rw [getCurrentEpoch_toNat, advanceSlot_slot advancedOk]
    exact within
  have advancedSlot := advanceSlot_slot advancedOk
  -- The upgrades read the conditions of a run at the blocks of the state that the slot reaches.
  have advancedRun := advancedHolds.run conditions advancedEpoch
  have advancedBounded := advancedHolds.bounded
  -- Each due upgrade succeeds from a state that the upgrades pass through.
  obtain ⟨after, afterOk, -⟩ := processUpgrades_exists_ok (config := config) (checks := checks)
    (property := fun upgrading =>
      UpgradesPass config checks ⟨forked.fork, advanced⟩ upgrading ∧
        upgrading.state.slot = advanced.slot ∧
        RunBounded config
          (start.afterChain step blocks ((getCurrentEpoch advanced).toNat - startEpoch)) budget
          ((getCurrentEpoch advanced).toNat - startEpoch) upgrading.state ∧
        Shaped upgrading.state ∧ PendingResolved upgrading.state ∧
        PendingVoted Set.univ upgrading.state)
    ⟨.refl _, rfl, advancedBounded, advancedHolds.shaped, advancedHolds.resolved,
      advancedHolds.voted⟩
    (fun reached ⟨passes, slotEq, bounded, shaped, resolved, voted⟩ due => by
      have epochEq : getCurrentEpoch reached.state = getCurrentEpoch advanced := by
        unfold getCurrentEpoch
        rw [slotEq]
      have nonzero : reached.state.slot ≠ 0 := by
        intro zero
        have := congrArg UInt64.toNat (slotEq.symm.trans zero)
        simp only [UInt64.toNat_zero] at this
        omega
      have ready := UpgradeReady.of_run advancedRun bounded shaped resolved (by omega)
        (by rw [epochEq]; omega) (upgradeDraws advanced advancedOk reached passes due) due voted
        fun _ => nonzero
      obtain ⟨next, nextOk⟩ := upgradeNext_exists_ok (config := config) (checks := checks) ready
      have altair := (upgradeNext_altair nextOk).1
      refine ⟨next, nextOk, passes.snoc due nextOk,
        (upgradeFrame_upgradeNext nextOk).slot.trans slotEq,
        bounded.of_upgradeNext (bounded.effective_le advancedRun (by omega))
          (by rw [epochEq]; exact advancedRun.first_le_ceilingAt fits advancedHolds.started)
          nextOk,
        upgradeNext_shaped advancedRun.activation advancedRun.compounding nextOk shaped,
        PendingResolved.of_altair altair _, PendingVoted.of_altair altair _⟩)
  exact ⟨after, by simp only [advanceSlotAcross, advancedOk, bind, Except.bind]; exact afterOk⟩

end EthLib.Consensus
