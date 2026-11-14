module

public import EthLib.Consensus.Proofs.Transition.Totality.ChainHolds
public import EthLib.Consensus.Proofs.Transition.Totality.EffectiveBlock
public import EthLib.Consensus.Proofs.Transition.Totality.ExitsBlock
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoadBlock
public import EthLib.Consensus.Proofs.Transition.Totality.ShapeBlock
public import EthLib.Consensus.Proofs.Transition.Totality.SlashedBlock
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock

/-!
# Proofs: a bounded block keeps the facts of a chain

A chain keeps bounds that each block may raise by a fixed step.

The protocol does not cap every amount that a block brings in, such as the Gwei of its deposits.

So a block must stay within stated limits on its body.

A slashing limit fits only far below what the protocol allows from Electra.

The slashed balances must fit in 64 bits after the most blocks, at the largest cap per name.

The step must then cover those limits, at the budget of the effective balances.

A block that the transition accepts, within the limits, keeps the facts of the chain.

Its count of blocks rises by one, and the slots before it keep the facts too.

At the end of each epoch on the way, the signers must hold at most the active balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The limits on a block body -/

/-- The most that one block body may carry, in the amounts that the bounds of a chain read. -/
structure BlockLimits where
  /-- The Gwei of the deposits and the deposit requests. -/
  deposits : Nat
  /-- The deposits of the deposit contract, each of which may add a validator. -/
  joins : Nat
  /-- The bound on the rise of the validators plus the pending deposits. -/
  load : Nat
  /-- The validators that the slashings name. -/
  slashings : Nat
  /-- The withdrawal requests. -/
  withdrawals : Nat

/-- A block body within the limits. -/
structure BlockBounded {fork : Fork} (limits : BlockLimits)
    (body : BeaconBlockBody preset fork) : Prop where
  /-- Its deposits and deposit requests bring in at most the limit in Gwei. -/
  deposits : blockDepositAmount body ≤ limits.deposits
  /-- It applies at most the limit of deposits of the deposit contract. -/
  joins : blockDepositCount body ≤ limits.joins
  /-- It raises the validators plus the pending deposits by at most the limit. -/
  load : blockLoadBound body ≤ limits.load
  /-- Its slashings name at most the limit of validators. -/
  slashings : blockSlashingCount body ≤ limits.slashings
  /-- It carries at most the limit of withdrawal requests. -/
  withdrawals : (blockWithdrawalRequests body).length ≤ limits.withdrawals

/-- A block step covers the limits on a block body, for a chain within a budget.

The slashed step covers the largest cap for each validator that the slashings name.

The effective step covers the largest cap for each deposit, and the load step twice the load limit.

The supply step covers the deposits and the bound on the rewards of a block.

It also covers the whistleblower share of the slashed step, at every fork.

The effective step fits the supply step in the ratio of the hysteresis.

The ceiling step covers one more epoch, and the exit cost of the registry at the budget.

That cost reads the load after the most blocks of the chain.

It also covers the cost of each new validator, and of each withdrawal request at the budget. -/
structure BlockStep.Covers (preset : Preset) (step : BlockStep) (limits : BlockLimits)
    (start : RunStart) (budget epochs : Nat) : Prop where
  /-- The slashed step covers the slashings. -/
  slashed : limits.slashings * preset.largestEffectiveBalance ≤ step.slashed
  /-- The effective step covers the new validators. -/
  effective : limits.joins * preset.largestEffectiveBalance ≤ step.effective
  /-- The load step covers twice the load limit, the weight of the load before Electra. -/
  load : 2 * limits.load ≤ step.load
  /-- The supply step covers the deposits, the whistleblower rewards and the other rewards. -/
  supply : ∀ fork, limits.deposits +
      step.slashed / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      blockRewardBound preset budget ≤ step.supply
  /-- The effective step fits the supply step in the ratio of the hysteresis. -/
  ratio : step.effective *
      (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
    step.supply * preset.HYSTERESIS_QUOTIENT.toNat
  /-- The ceiling step covers the exits that a block can start. -/
  ceiling : 1 + budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      (start.afterBlocks step (preset.chainBlocks epochs)).load +
      limits.joins *
        (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) +
      limits.withdrawals * (budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ≤
    step.ceiling

/-! ## The signers along the slots -/

/-- The signers hold at most the active balance at the end of each epoch on a run of slots.

The condition reads the state at the end of each epoch, with the roots cached. -/
def SignersAtEnds (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset)
    (count : Nat) : Prop :=
  ∀ steps < count, ∀ reached, advanceSlotsAcross config checks steps forked = .ok reached →
    (reached.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
    ∀ cached, processSlot reached.state = .ok cached → SignersWithinActive cached

/-! ## The slots before a block -/

/-- A run of empty slots keeps the facts of a chain, with the same count of blocks.

The epoch of its last slot is at most the first epoch of the chain plus the number of epochs.

At the end of each epoch it crosses, the signers hold at most the active balance. -/
theorem ChainHolds.of_advanceSlotsAcross {start : RunStart} {step : BlockStep}
    {budget epochs lastEpoch startEpoch blocks : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch) :
    ∀ (count : Nat) {forked next : ForkedBeaconState preset},
      ChainHolds config start step budget startEpoch blocks forked.state →
      (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs →
      SignersAtEnds config checks forked count →
      advanceSlotsAcross config checks count forked = .ok next →
      ChainHolds config start step budget startEpoch blocks next.state
  | 0, forked, next, holds, _, _, computed => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds
  | count + 1, forked, next, holds, within, signers, computed => by
    obtain ⟨reached, reachedOk, rest⟩ := bind_ok_iff.mp computed
    have stepWithin : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤
        startEpoch + epochs :=
      (Nat.div_le_div_right (by omega)).trans within
    have reachedHolds := ChainHolds.of_advanceSlotAcross conditions fits holds stepWithin
      (signers 0 (Nat.succ_pos _) forked rfl) reachedOk
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp reachedOk
    have reachedSlot : reached.state.slot.toNat = forked.state.slot.toNat + 1 := by
      rw [processUpgrades_slot upgraded]
      exact advanceSlot_slot advancedOk
    -- The rest of the run starts from the state that the slot reaches, one step later.
    have shifted : ∀ {steps after}, advanceSlotsAcross config checks steps reached = .ok after →
        advanceSlotsAcross config checks (steps + 1) forked = .ok after := fun afterOk => by
      simp only [advanceSlotsAcross, reachedOk, bind, Except.bind]
      exact afterOk
    exact ChainHolds.of_advanceSlotsAcross conditions fits count reachedHolds
      (by rwa [reachedSlot, Nat.add_right_comm, Nat.add_assoc])
      (fun steps below after afterOk => signers (steps + 1) (by omega) after (shifted afterOk))
      rest

/-! ## The bounds across one block -/

/-- A run of slots ends that many slots after its first state. -/
theorem advanceSlotsAcross_slot :
    ∀ (count : Nat) {forked next : ForkedBeaconState preset},
      advanceSlotsAcross config checks count forked = .ok next →
      next.state.slot.toNat = forked.state.slot.toNat + count
  | 0, forked, next, computed => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | count + 1, forked, next, computed => by
    obtain ⟨reached, reachedOk, rest⟩ := bind_ok_iff.mp computed
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp reachedOk
    have reachedSlot : reached.state.slot.toNat = forked.state.slot.toNat + 1 := by
      rw [processUpgrades_slot upgraded]
      exact advanceSlot_slot advancedOk
    rw [advanceSlotsAcross_slot count rest, reachedSlot]
    omega

/-- A sum of terms, each at most a bound, is at most the number of terms times the bound. -/
private theorem sum_map_le_length_mul {α : Type} (items : List α) (term : α → Nat) (bound : Nat)
    (each : ∀ item ∈ items, term item ≤ bound) : (items.map term).sum ≤ items.length * bound := by
  simpa using List.sum_le_length_nsmul (items.map term) bound (by simpa using each)

/-- Each withdrawal request costs at most the cap in increments, plus one. -/
private theorem partialExitCost_le {fork : Fork} (cap : Nat) (body : BeaconBlockBody preset fork) :
    partialExitCost preset cap body ≤ (blockWithdrawalRequests body).length *
      (cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) := by
  unfold partialExitCost
  exact sum_map_le_length_mul _ _ _ fun request _ =>
    Nat.add_le_add_right (Nat.div_le_div_right (min_le_right _ _)) 1

/-- Within their caps, the validators from a position on cost at most the largest cap each.

The cost counts the largest cap in increments, plus one. -/
private theorem exitCostFrom_le {fork : Fork} {state : BeaconState preset fork}
    (capped : EffectiveBalancesCapped state) (count : Nat) :
    exitCostFrom preset state count ≤ (state.validators.data.size - count) *
      (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) := by
  unfold exitCostFrom
  have bound := sum_map_le_length_mul (state.validators.data.toList.drop count)
    (fun validator =>
      validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1)
    (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1)
    fun validator inside => by
      have registered := Array.mem_toList_iff.mp (List.mem_of_mem_drop inside)
      exact Nat.add_le_add_right (Nat.div_le_div_right
        ((UInt64.le_iff_toNat_le.mp (capped validator registered)).trans
          (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork validator))) 1
  simpa only [List.length_drop, Array.length_toList] using bound

/-- A block within the limits keeps the bounds of a chain, raised by one more block.

The step covers the limits, and one more block is within the most blocks of the chain.

The effective balances after the block are within their caps.

The current epoch plus one plus the longest lookahead is at most the exit ceiling.

The increment is at most the least balance to activate, and the withdrawal delay is positive. -/
private theorem RunBounded.of_processBlock {fork : Fork} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch blocks elapsed : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    (raised : blocks + 1 ≤ preset.chainBlocks epochs)
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (le : elapsed ≤ epochs)
    (holds : RunBounded config (start.afterBlocks step blocks) budget elapsed state)
    (shaped : Shaped state) (cappedAfter : EffectiveBalancesCapped after)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      (start.afterBlocks step blocks).ceilingAt preset budget elapsed)
    (bounded : BlockBounded limits block.body)
    (computed : processBlock config checks engine state block = .ok after) :
    RunBounded config (start.afterBlocks step (blocks + 1)) budget elapsed after := by
  have baseRun := conditions.at (Nat.le_of_succ_le raised)
  have raisedRun := conditions.at raised
  -- One more block raises each bound by its step.
  have supplyEq : (start.afterBlocks step (blocks + 1)).supply =
      (start.afterBlocks step blocks).supply + step.supply := by
    simp only [RunStart.afterBlocks, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have effectiveEq : (start.afterBlocks step (blocks + 1)).effective =
      (start.afterBlocks step blocks).effective + step.effective := by
    simp only [RunStart.afterBlocks, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have loadEq : (start.afterBlocks step (blocks + 1)).load =
      (start.afterBlocks step blocks).load + step.load := by
    simp only [RunStart.afterBlocks, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have ceilingEq : (start.afterBlocks step (blocks + 1)).ceiling =
      (start.afterBlocks step blocks).ceiling + step.ceiling := by
    simp only [RunStart.afterBlocks, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have slashedEq : (start.afterBlocks step (blocks + 1)).slashed =
      (start.afterBlocks step blocks).slashed + step.slashed := by
    simp only [RunStart.afterBlocks, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := UInt64.toNat_inj.not.mpr baseRun.positive.increment
    simp only [UInt64.toNat_zero] at this
    omega
  have increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT := UInt64.lt_iff_toNat_lt.mpr positive
  have capped := shaped.capped
  have effectiveLe := holds.effective_le baseRun le
  have budgeted : max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (effectiveBalanceSum state) ≤
      budget := max_le ((le_max_left _ _).trans baseRun.effectiveStart) effectiveLe
  -- The supply rises by the deposits, the whistleblower rewards and the other rewards.
  have rewardLe := blockRewardCap_le budgeted
  have slashedLe := processBlock_slashedBalanceSum_le_count capped computed
  have slashedStep : blockSlashingCount block.body * preset.largestEffectiveBalance ≤
      step.slashed := (Nat.mul_le_mul_right _ bounded.slashings).trans covers.slashed
  have whistle : (slashedBalanceSum after - slashedBalanceSum state) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      step.slashed / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Nat.div_le_div_right (by omega)
  have supplyLe := processBlock_supply_le_cap computed
  have coversSupply := covers.supply fork
  have depositsLe := bounded.deposits
  have supplyBefore := holds.supply
  have raisedBudget : (start.afterBlocks step (blocks + 1)).supply +
      epochs * preset.epochIssuanceBeforeAltair budget ≤ budget := raisedRun.supply_le_budget
  have issuanceLe : elapsed * preset.epochIssuanceBeforeAltair budget ≤
      epochs * preset.epochIssuanceBeforeAltair budget := Nat.mul_le_mul_right _ le
  have capLe : balanceSum state + pendingDepositSum state + blockDepositAmount block.body +
      (slashedBalanceSum after - slashedBalanceSum state) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      blockRewardCap preset state ≤ budget := by
    omega
  -- The effective balances rise by at most the largest cap for each new validator.
  have sizeLe := processBlock_validators_size_le computed
  have joinsLe := bounded.joins
  have effectiveAfter := processBlock_effectiveBalanceSum_le baseRun.compounding capped computed
  have risen : (after.validators.data.size - state.validators.data.size) *
      preset.largestEffectiveBalance ≤ step.effective :=
    (Nat.mul_le_mul_right _ (by omega)).trans covers.effective
  have effectiveField : effectiveBalanceSum after ≤
        (start.afterBlocks step (blocks + 1)).effective ∨
      effectiveBalanceSum after *
          (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
        ((start.afterBlocks step (blocks + 1)).supply +
          elapsed * preset.epochIssuanceBeforeAltair budget) *
          preset.HYSTERESIS_QUOTIENT.toNat := by
    rcases holds.effective with low | ratio
    · left
      omega
    · right
      rw [supplyEq]
      calc effectiveBalanceSum after *
            (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat)
          ≤ (effectiveBalanceSum state + step.effective) *
            (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ ((start.afterBlocks step blocks).supply +
              elapsed * preset.epochIssuanceBeforeAltair budget) *
            preset.HYSTERESIS_QUOTIENT.toNat + step.supply * preset.HYSTERESIS_QUOTIENT.toNat := by
            rw [Nat.add_mul]
            exact Nat.add_le_add ratio covers.ratio
        _ = _ := by
            rw [← Nat.add_mul]
            congr 1
            omega
  have effectiveAfterLe := raisedRun.effective_le_budget le effectiveField
  -- The registry load rises by at most the load limit, counted twice before Electra.
  have loadAfter := processBlock_registryLoad_le computed
  have factorLe : registryLoadFactor fork ≤ 2 := by
    unfold registryLoadFactor
    split <;> omega
  have loadField : registryLoadFactor fork * registryLoad after ≤
      (start.afterBlocks step (blocks + 1)).load := by
    have weighted := Nat.mul_le_mul_left (registryLoadFactor fork)
      (loadAfter.trans (Nat.add_le_add_left bounded.load _))
    rw [Nat.mul_add] at weighted
    have doubled := Nat.mul_le_mul_right limits.load factorLe
    have := holds.load
    have := covers.load
    omega
  -- The exits that the block starts fit in the ceiling, raised by its step.
  have sizeLoad : state.validators.data.size ≤ (start.afterBlocks step blocks).load :=
    (Nat.le_add_right _ _).trans
      ((Nat.le_mul_of_pos_left _ (one_le_registryLoadFactor fork)).trans holds.load)
  have most : (start.afterBlocks step blocks).load ≤
      (start.afterBlocks step (preset.chainBlocks epochs)).load := by
    simp only [RunStart.afterBlocks]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_succ_le raised)) _
  obtain ⟨reached, costLe, -, exitsLe, queuesLe⟩ := processBlock_exits computed increment
    baseRun.minimum baseRun.maximum activationIncrement withdrawable
    (ceiling := (start.afterBlocks step blocks).ceilingAt preset budget elapsed + 1) (by omega)
    (fun validator member set => (holds.exits validator member set).trans (Nat.le_succ _))
    (fun electra => ⟨holds.queue electra, (holds.consolidations electra).trans (Nat.le_succ _)⟩)
    (cap := budget) capLe
  have exitCostLe := exitCost_le state
  have divLe : effectiveBalanceSum state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat := Nat.div_le_div_right effectiveLe
  have fromLe := exitCostFrom_le cappedAfter state.validators.data.size
  have partialLe := partialExitCost_le budget block.body
  have joinsCost : (after.validators.data.size - state.validators.data.size) *
        (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ≤
      limits.joins *
        (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have withdrawalsCost : (blockWithdrawalRequests block.body).length *
        (budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ≤
      limits.withdrawals * (budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) :=
    Nat.mul_le_mul_right _ bounded.withdrawals
  have coversCeiling := covers.ceiling
  have exitStepLe : (start.afterBlocks step blocks).exitStep preset budget ≤
      (start.afterBlocks step (blocks + 1)).exitStep preset budget := by
    unfold RunStart.exitStep
    omega
  have ceilingLe : (start.afterBlocks step blocks).ceilingAt preset budget elapsed + step.ceiling ≤
      (start.afterBlocks step (blocks + 1)).ceilingAt preset budget elapsed := by
    have := Nat.mul_le_mul_left elapsed exitStepLe
    unfold RunStart.ceilingAt
    omega
  have reachedLe :
      reached ≤ (start.afterBlocks step (blocks + 1)).ceilingAt preset budget elapsed := by
    omega
  have kept := processBlock_blockKept computed
  refine ⟨?_, effectiveField, loadField, ?_, fun validator member set =>
    (exitsLe validator member set).trans reachedLe,
    fun electra => ((queuesLe electra).1.trans reachedLe).trans (Nat.le_succ _),
    fun electra => (queuesLe electra).2.trans reachedLe, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · -- A block keeps each inactivity score or sets it to zero.
    intro altair score member
    obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp member
    rcases kept.scores altair index with same | zero
    · rw [same] at found
      exact holds.scores altair score (Array.mem_of_getElem? found)
    · rw [zero, Option.some.injEq] at found
      subst found
      simp
  · rw [kept.roots]
    exact holds.roots
  · intro capella
    rw [kept.summaries]
    exact holds.summaries capella
  · intro electra
    rw [kept.depositCarry]
    exact holds.depositChurn electra
  · intro electra
    have churned := processBlock_exitBalanceToConsume_le computed increment baseRun.minimum
      baseRun.maximum activationIncrement withdrawable electra
    have ceilingChurn : exitChurnCeiling config after ≤ exitChurnBound preset config budget := by
      unfold exitChurnCeiling exitChurnBound
      omega
    exact churned.trans (max_le (holds.exitChurn electra)
      (ceilingChurn.trans (le_max_right _ _)))
  · have := holds.slashed
    omega

/-! ## One block -/

/-- A block that the transition accepts follows the slots that lead to its own slot.

The slots reach a state at the slot of the block, which the block then processes.

The slot of the block is after the slot of the state before it. -/
theorem stateTransitionAcross_advanced {fork : Fork} {engine : ExecutionEngine preset fork}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    ∃ advanced, forked.state.slot.toNat < signed.message.slot.toNat ∧
      advanceSlotsAcross config checks (signed.message.slot.toNat - forked.state.slot.toNat)
        forked = .ok ⟨fork, advanced⟩ ∧
      advanced.slot.toNat = signed.message.slot.toNat ∧
      processBlock config checks engine advanced signed.message = .ok after := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  have blockOk := (applySignedBlock_ok applied).2.1
  simp only [processSlotsAcross, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, later, advancedOk⟩ := slotsOk
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  refine ⟨advanced, laterNat, advancedOk, ?_, blockOk⟩
  have := advanceSlotsAcross_slot _ advancedOk
  dsimp only at this
  omega

/-- A block that the transition accepts lands after the state before it, at its own slot. -/
theorem stateTransitionAcross_slot {fork : Fork} {engine : ExecutionEngine preset fork}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    forked.state.slot.toNat < signed.message.slot.toNat ∧
      after.slot.toNat = signed.message.slot.toNat := by
  obtain ⟨advanced, later, _, advancedSlot, blockOk⟩ := stateTransitionAcross_advanced computed
  rw [(frame_processBlock blockOk).slot]
  exact ⟨later, advancedSlot⟩

/-- A block within the limits that the transition accepts keeps the facts of a chain.

The facts hold at the state before the slots that lead to the block, with some count of blocks.

They then hold after the block, with one more block.

The step covers the limits, and the slot of the block is within the epochs of the chain.

At the end of each epoch before the block, the signers hold at most the active balance.

The least inclusion delay and the withdrawal delay are positive.

The increment is at most the least balance to activate. -/
theorem ChainHolds.of_stateTransitionAcross {fork : Fork} {engine : ExecutionEngine preset fork}
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch startEpoch blocks : Nat}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    (inclusion : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat)
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    (bounded : BlockBounded limits signed.message.body)
    (within : signed.message.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : SignersAtEnds config checks forked
      (signed.message.slot.toNat - forked.state.slot.toNat))
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    ChainHolds config start step budget startEpoch (blocks + 1) after := by
  obtain ⟨advanced, later, advancedOk, advancedSlot, blockOk⟩ :=
    stateTransitionAcross_advanced computed
  have laterNat := later
  -- The slots before the block keep the facts, with the same count of blocks.
  have advancedHolds : ChainHolds config start step budget startEpoch blocks advanced :=
    ChainHolds.of_advanceSlotsAcross conditions fits _ holds
      (by rwa [Nat.add_sub_cancel' laterNat.le]) signers advancedOk
  -- The block keeps the slot, so the epoch too.
  have afterSlot : after.slot = advanced.slot := (frame_processBlock blockOk).slot
  have epochEq : getCurrentEpoch after = getCurrentEpoch advanced := by
    unfold getCurrentEpoch
    rw [afterSlot]
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := conditions.run.slots
    omega
  have started := advancedHolds.started
  have advancedEpoch : (getCurrentEpoch advanced).toNat ≤ startEpoch + epochs := by
    rw [getCurrentEpoch_toNat, advancedSlot]
    exact within
  have startSlot : startEpoch * preset.SLOTS_PER_EPOCH.toNat ≤ signed.message.slot.toNat := by
    have epochLe := started
    rw [getCurrentEpoch_toNat, advancedSlot] at epochLe
    exact (Nat.le_div_iff_mul_le positive).mp epochLe
  -- The block lands in a later slot than the state before the slots, so it fits the count.
  have counted : blocks + 1 ≤
      after.slot.toNat + 1 - startEpoch * preset.SLOTS_PER_EPOCH.toNat := by
    have := holds.counted
    rw [afterSlot, advancedSlot]
    omega
  have raised : blocks + 1 ≤ preset.chainBlocks epochs := by
    have below := (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_of_le within)
    have split : (startEpoch + epochs + 1) * preset.SLOTS_PER_EPOCH.toNat =
        startEpoch * preset.SLOTS_PER_EPOCH.toNat + preset.chainBlocks epochs := by
      unfold Preset.chainBlocks
      rw [Nat.add_assoc, Nat.add_mul]
    rw [Nat.succ_eq_add_one, split] at below
    have := counted
    rw [afterSlot, advancedSlot] at this
    omega
  have baseRun := conditions.at (Nat.le_of_succ_le raised)
  have shaped := stateTransitionAcross_shaped conditions.run.activation conditions.run.compounding
    computed holds.shaped
  have afterBounded := RunBounded.of_processBlock conditions covers raised activationIncrement
    withdrawable (by omega) advancedHolds.bounded advancedHolds.shaped shaped.capped
    (baseRun.first_le_ceilingAt fits started) bounded blockOk
  have pending := stateTransitionAcross_pending inclusion conditions.run.apart holds.wellFormed
    holds.resolved holds.voted holds.early computed
  refine ⟨by rw [epochEq]; exact started, (stateTransitionAcross_invariant holds.invariant
    computed).1, shaped, pending.1, pending.2.1, pending.2.2.2, pending.2.2.1, counted, ?_⟩
  rw [epochEq]
  exact afterBounded

end EthLib.Consensus
