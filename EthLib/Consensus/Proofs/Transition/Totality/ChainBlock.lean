module

public import EthLib.Consensus.Proofs.Transition.Totality.ChainHolds
public import EthLib.Consensus.Proofs.Transition.Totality.EffectiveBlock
public import EthLib.Consensus.Proofs.Transition.Totality.ExitsBlock
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoadBlock
public import EthLib.Consensus.Proofs.Transition.Totality.ShapeBlock
public import EthLib.Consensus.Proofs.Transition.Totality.SlashedBlock
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock
import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
import EthLib.Consensus.Proofs.Transition.Totality.SlashValidator

/-!
# Proofs: a bounded block keeps the facts of a chain

A chain keeps bounds that each block may raise by a fixed step.

The protocol does not cap every amount that a block brings in, such as the Gwei of its deposits.

So a block must stay within stated limits on its body.

A block that the transition accepts, within the limits, keeps the facts of the chain.

Within the same limits, slashing a validator succeeds at the turn of an attester slashing.

That attester slashing must name at least one validator.
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

The budget bounds the effective balances. -/
structure BlockStep.Covers (preset : Preset) (step : BlockStep) (limits : BlockLimits)
    (start : RunStart) (budget epochs : Nat) : Prop where
  -- A slashing limit fits only far below what the protocol allows from Electra.
  --
  -- The slashed balances must fit in 64 bits after the most blocks, at the largest cap per name.
  --
  -- The step must then cover those limits, at the budget of the effective balances.
  /-- The slashed step covers the slashings.

  It covers the largest cap for each validator that the slashings name. -/
  slashed : limits.slashings * preset.largestEffectiveBalance ≤ step.slashed
  /-- The effective step covers the new validators, at the largest cap for each deposit. -/
  effective : limits.joins * preset.largestEffectiveBalance ≤ step.effective
  /-- The load step covers twice the load limit, the weight of the load before Electra. -/
  load : 2 * limits.load ≤ step.load
  /-- The supply step covers the deposits, the whistleblower rewards and the other rewards.

  The other rewards are the bound on the rewards of a block.

  The whistleblower rewards are the share of the slashed step, at every fork. -/
  supply : ∀ fork, limits.deposits +
      step.slashed / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      blockRewardBound preset budget ≤ step.supply
  /-- The effective step fits the supply step in the ratio of the hysteresis. -/
  ratio : step.effective *
      (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
    step.supply * preset.HYSTERESIS_QUOTIENT.toNat
  /-- The ceiling step covers the exits that a block can start.

  It covers one more epoch, and the exit cost of the registry at the budget.

  That cost reads the load after the most blocks of the chain.

  It also covers the cost of each new validator, and of each withdrawal request at the budget. -/
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

/-- A bound that a block or a prefix of it reaches, plus a cost, is at most the next exit ceiling.

The bound plus the cost is at most the ceiling plus one, plus the cost owed before.

It adds a cost of the joined validators and a cost of the withdrawal requests, each within a limit.

The effective balances before are within the budget, and the registry within the load bound. -/
private theorem reached_le_ceilingAt {fork : Fork} {start : RunStart} {step : BlockStep}
    {limits : BlockLimits} {budget epochs blocks elapsed : Nat} {state : BeaconState preset fork}
    (coversCeiling : 1 + budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      (start.afterBlocks step (preset.chainBlocks epochs)).load +
      limits.joins *
        (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) +
      limits.withdrawals * (budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ≤
    step.ceiling)
    (raised : blocks + 1 ≤ preset.chainBlocks epochs)
    (effectiveLe : effectiveBalanceSum state ≤ budget)
    (sizeLoad : state.validators.data.size ≤ (start.afterBlocks step blocks).load)
    {reached cost joined withdrawn : Nat}
    (costLe : reached + cost ≤ (start.afterBlocks step blocks).ceilingAt preset budget elapsed + 1 +
      exitCost preset state + joined + withdrawn)
    (joinedLe : joined ≤ limits.joins *
      (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1))
    (partialLe : withdrawn ≤ limits.withdrawals *
      (budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1)) :
    reached + cost ≤ (start.afterBlocks step (blocks + 1)).ceilingAt preset budget elapsed := by
  have loadEq : (start.afterBlocks step (blocks + 1)).load =
      (start.afterBlocks step blocks).load + step.load := by
    rw [RunStart.afterBlocks_succ]
  have ceilingEq : (start.afterBlocks step (blocks + 1)).ceiling =
      (start.afterBlocks step blocks).ceiling + step.ceiling := by
    rw [RunStart.afterBlocks_succ]
  have most : (start.afterBlocks step blocks).load ≤
      (start.afterBlocks step (preset.chainBlocks epochs)).load := by
    simp only [RunStart.afterBlocks]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_succ_le raised)) _
  have exitCostLe := exitCost_le state
  have divLe : effectiveBalanceSum state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat := Nat.div_le_div_right effectiveLe
  have exitStepLe : (start.afterBlocks step blocks).exitStep preset budget ≤
      (start.afterBlocks step (blocks + 1)).exitStep preset budget := by
    unfold RunStart.exitStep
    omega
  have ceilingLe : (start.afterBlocks step blocks).ceilingAt preset budget elapsed + step.ceiling ≤
      (start.afterBlocks step (blocks + 1)).ceilingAt preset budget elapsed := by
    have := Nat.mul_le_mul_left elapsed exitStepLe
    unfold RunStart.ceilingAt
    omega
  omega

/-- A block within the limits keeps the bounds of a chain, raised by one more block.

The step covers the limits, and one more block is within the most blocks of the chain. -/
private theorem RunBounded.of_processBlock {fork : Fork} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch blocks elapsed : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    (raised : blocks + 1 ≤ preset.chainBlocks epochs)
    -- The increment is at most the least balance to activate.
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    -- The withdrawal delay is positive.
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (le : elapsed ≤ epochs)
    (holds : RunBounded config (start.afterBlocks step blocks) budget elapsed state)
    -- The effective balances after the block are within their caps.
    (shaped : Shaped state) (cappedAfter : EffectiveBalancesCapped after)
    -- The current epoch plus one plus the longest lookahead is at most the exit ceiling.
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
    rw [RunStart.afterBlocks_succ]
  have effectiveEq : (start.afterBlocks step (blocks + 1)).effective =
      (start.afterBlocks step blocks).effective + step.effective := by
    rw [RunStart.afterBlocks_succ]
  have loadEq : (start.afterBlocks step (blocks + 1)).load =
      (start.afterBlocks step blocks).load + step.load := by
    rw [RunStart.afterBlocks_succ]
  have ceilingEq : (start.afterBlocks step (blocks + 1)).ceiling =
      (start.afterBlocks step blocks).ceiling + step.ceiling := by
    rw [RunStart.afterBlocks_succ]
  have slashedEq : (start.afterBlocks step (blocks + 1)).slashed =
      (start.afterBlocks step blocks).slashed + step.slashed := by
    rw [RunStart.afterBlocks_succ]
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
  obtain ⟨reached, costLe, -, exitsLe, queuesLe⟩ := processBlock_exits computed increment
    baseRun.minimum baseRun.maximum activationIncrement withdrawable
    (ceiling := (start.afterBlocks step blocks).ceilingAt preset budget elapsed + 1) (by omega)
    (fun validator member set => (holds.exits validator member set).trans (Nat.le_succ _))
    (fun electra => ⟨holds.queue electra, (holds.consolidations electra).trans (Nat.le_succ _)⟩)
    (cap := budget) capLe
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
  have reachedLe :
      reached ≤ (start.afterBlocks step (blocks + 1)).ceilingAt preset budget elapsed :=
    Nat.le_of_add_right_le (reached_le_ceilingAt covers.ceiling raised effectiveLe sizeLoad costLe
      (fromLe.trans joinsCost) (partialLe.trans withdrawalsCost))
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

/-- One more block after the slots that lead to it fits the count of a chain.

It also fits within the most blocks of the chain's epochs. -/
private theorem raised_of_slots {fork : Fork} {epochs startEpoch blocks slot : Nat}
    {forked : ForkedBeaconState preset} {advanced : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (countedBefore :
      blocks ≤ forked.state.slot.toNat + 1 - startEpoch * preset.SLOTS_PER_EPOCH.toNat)
    (started : startEpoch ≤ (getCurrentEpoch advanced).toNat)
    (advancedSlot : advanced.slot.toNat = slot) (later : forked.state.slot.toNat < slot)
    (within : slot / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs) :
    blocks + 1 ≤ slot + 1 - startEpoch * preset.SLOTS_PER_EPOCH.toNat ∧
      blocks + 1 ≤ preset.chainBlocks epochs := by
  have startSlot : startEpoch * preset.SLOTS_PER_EPOCH.toNat ≤ slot := by
    have epochLe := started
    rw [getCurrentEpoch_toNat, advancedSlot] at epochLe
    exact (Nat.le_div_iff_mul_le positive).mp epochLe
  have counted : blocks + 1 ≤ slot + 1 - startEpoch * preset.SLOTS_PER_EPOCH.toNat := by
    omega
  refine ⟨counted, ?_⟩
  have below := (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_of_le within)
  have split : (startEpoch + epochs + 1) * preset.SLOTS_PER_EPOCH.toNat =
      startEpoch * preset.SLOTS_PER_EPOCH.toNat + preset.chainBlocks epochs := by
    unfold Preset.chainBlocks
    rw [Nat.add_assoc, Nat.add_mul]
  rw [Nat.succ_eq_add_one, split] at below
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

The step covers the limits, and the slot of the block is within the epochs of the chain. -/
theorem ChainHolds.of_stateTransitionAcross {fork : Fork} {engine : ExecutionEngine preset fork}
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch startEpoch blocks : Nat}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    -- The least inclusion delay and the withdrawal delay are positive.
    (inclusion : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat)
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    -- The increment is at most the least balance to activate.
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    (bounded : BlockBounded limits signed.message.body)
    (within : signed.message.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    -- At the end of each epoch before the block, the signers hold at most the active balance.
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
  -- The block lands in a later slot than the state before the slots, so it fits the count.
  obtain ⟨countedSlot, raised⟩ :=
    raised_of_slots positive holds.counted advancedHolds.started advancedSlot laterNat within
  have counted : blocks + 1 ≤
      after.slot.toNat + 1 - startEpoch * preset.SLOTS_PER_EPOCH.toNat := by
    rw [afterSlot, advancedSlot]
    exact countedSlot
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

/-! ## One slashing in a block -/

/-- Take the state a block reaches after its proposer slashings and first `j` attester slashings.

No attester slashing needs to exist at position `j`.

When the mixes span more than the seed lookahead plus two, the proposer read there is the block's.

When the balances there match the registry, that proposer's index is inside the balances. -/
private theorem slashingTurn_proposer
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {advanced turn : BeaconState preset fork} {j : Nat}
    (turned : SlashingTurn config checks engine advanced block j turn)
    (balancesMatch : BalancesMatch turn) :
    getBeaconProposerIndex turn = .ok block.proposerIndex ∧
      block.proposerIndex.toNat < turn.balances.data.size := by
  obtain ⟨input, started, frameKept, -, proposerKept⟩ := slashingTurn_kept turned
  obtain ⟨parented, headed, executed, revealed, -, headerOk, executionOk, randaoOk, eth1Ok⟩ :=
    id started
  obtain ⟨-, -, -, -, _, proposerFound, -⟩ := processBlockHeader_checks headerOk
  have growsExecuted : headed.validators.data.size ≤ executed.validators.data.size := by
    split at executionOk
    · exact (frame_processBlockExecution executionOk).registryGrows
    · cases executionOk
      exact Nat.le_refl _
  have growsInput : revealed.validators.data.size ≤ input.validators.data.size := by
    split at eth1Ok
    · exact (frame_processEth1Data eth1Ok).registryGrows
    · cases eth1Ok
      exact Nat.le_refl _
  have proposerRegistered : block.proposerIndex.toNat < turn.validators.data.size :=
    Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp proposerFound)).1
      ((frame_processBlockHeader headerOk).registryGrows.trans <| growsExecuted.trans <|
        (frame_processRandao randaoOk).registryGrows.trans <| growsInput.trans
          frameKept.registryGrows)
  refine ⟨?_, by rw [balancesMatch]; exact proposerRegistered⟩
  rw [proposerKept]
  exact (operationsInput_proposer apart started).1

/-- Take the state a block reaches after its proposer slashings and first `j` attester slashings.

The conditions of the chain hold, and one more block fits its count.

Then three bounds hold for a validator in the registry at the turn, and one for `advanced`:

- The slashed balance of the current epoch, if read, plus the effective balance is below `2^64`.
- From Altair, the whistleblower reward times the proposer weight is below `2^64`.
- Each balance at the turn plus the effective balance of the validator is below `2^64`.
- The sum of the balances at `advanced` is within the budget. -/
private theorem slashingTurn_balanceRoom {start : RunStart} {step : BlockStep}
    {limits : BlockLimits} {budget epochs lastEpoch startEpoch blocks : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (coversSlashed : limits.slashings * preset.largestEffectiveBalance ≤ step.slashed)
    {fork : Fork} {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {advanced turn : BeaconState preset fork} {j : Nat}
    (coversSupply : limits.deposits +
      step.slashed / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      blockRewardBound preset budget ≤ step.supply)
    -- The facts of the chain hold at `advanced`, after advancing the slots and before the block.
    (advancedHolds : ChainHolds config start step budget startEpoch blocks advanced)
    (raised : blocks + 1 ≤ preset.chainBlocks epochs)
    -- The epoch of `advanced` is within the epochs of the chain.
    (le : (getCurrentEpoch advanced).toNat - startEpoch ≤ epochs)
    (turned : SlashingTurn config checks engine advanced block j turn)
    -- The slashing count and the deposits of the block are within the limits.
    --
    -- The step covers those limits.
    (counted : blockSlashingCount block.body ≤ limits.slashings)
    (deposits : blockDepositAmount block.body ≤ limits.deposits)
    {slashing : AttesterSlashing preset fork}
    (atJ : block.body.attesterSlashings.data.toList[j]? = some slashing)
    -- The attester slashing at position `j` has at least one index in its first attestation.
    (named : 1 ≤ slashing.attestation1.attestingIndices.data.size)
    {index : ValidatorIndex} {validator : Validator}
    (found : turn.validators.data[index.toNat]? = some validator) :
    -- The slashed balance of the epoch has room for the effective balance of the validator.
    (∀ amount, readCircular turn.slashings.elements (getCurrentEpoch turn) = .ok amount →
      amount.toNat + validator.effectiveBalance.toNat < 2 ^ 64) ∧
    -- From Altair, the whistleblower reward fits with the proposer weight.
    (.altair ≤ fork → (validator.effectiveBalance /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat * PROPOSER_WEIGHT.toNat <
        2 ^ 64) ∧
    -- Each balance at the turn has room for it.
    (∀ (position : Nat) (balance : Gwei), turn.balances.data[position]? = some balance →
      balance.toNat + validator.effectiveBalance.toNat < 2 ^ 64) ∧
    -- The balances at `advanced` fit the budget.
    balanceSum advanced ≤ budget := by
  have baseRun := conditions.at (Nat.le_of_succ_le raised)
  have raisedRun := conditions.at raised
  have runBounded := advancedHolds.bounded
  -- The steps before the slashing keep the registry size and the effective balances.
  obtain ⟨sizeTurn, effectiveTurn, slashedTurn⟩ :=
    slashingTurn_slashed_le advancedHolds.shaped.capped turned
  have supplyTurn := slashingTurn_supply_le turned
  -- The validator keeps its effective balance, within the largest cap and the budget.
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have insideAdvanced : index.toNat < advanced.validators.data.size := sizeTurn ▸ inside
  have effectiveSame := effectiveTurn index.toNat insideAdvanced
  simp only [effectiveAt, found, Array.getElem?_eq_getElem insideAdvanced, Option.map_some,
    Option.getD_some] at effectiveSame
  have capLe : validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance :=
    effectiveSame.trans_le ((UInt64.le_iff_toNat_le.mp (advancedHolds.shaped.capped _
      (Array.getElem_mem insideAdvanced))).trans
        (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork _))
  have sumTurn : effectiveBalanceSum turn = effectiveBalanceSum advanced :=
    effectiveBalanceSum_eq_of_effectiveKept sizeTurn effectiveTurn
  have effectiveLe := runBounded.effective_le baseRun le
  have validatorLe : validator.effectiveBalance.toNat ≤ budget :=
    (effectiveBalance_le_effectiveBalanceSum (Array.mem_of_getElem? found)).trans
      (sumTurn ▸ effectiveLe)
  have tripled := baseRun.tripled
  -- The slashing at the turn supplies one name of the limit.
  have entry : ((block.body.attesterSlashings.data.toList.take j).map fun slashing =>
        slashing.attestation1.attestingIndices.data.size).sum +
      slashing.attestation1.attestingIndices.data.size ≤
        (block.body.attesterSlashings.data.toList.map fun slashing =>
          slashing.attestation1.attestingIndices.data.size).sum := by
    rw [List.map_take]
    generalize names : (block.body.attesterSlashings.data.toList.map fun slashing =>
      slashing.attestation1.attestingIndices.data.size) = sizes
    have atSizes : sizes[j]? = some slashing.attestation1.attestingIndices.data.size := by
      rw [← names, List.getElem?_map, atJ]
      rfl
    have split : sizes.take (j + 1) =
        sizes.take j ++ [slashing.attestation1.attestingIndices.data.size] := by
      rw [List.take_add_one, atSizes]
      rfl
    have whole : (sizes.take (j + 1)).sum ≤ sizes.sum := by
      conv_rhs => rw [← List.take_append_drop (j + 1) sizes]
      rw [List.sum_append]
      omega
    rw [split, List.sum_append, List.sum_singleton] at whole
    exact whole
  unfold blockSlashingCount at counted
  generalize names : block.body.proposerSlashings.data.size +
    ((block.body.attesterSlashings.data.toList.take j).map fun slashing =>
      slashing.attestation1.attestingIndices.data.size).sum = before at slashedTurn
  have oneName : before + 1 ≤ limits.slashings := by omega
  have namesCap : before * preset.largestEffectiveBalance + preset.largestEffectiveBalance ≤
      step.slashed := by
    rw [← Nat.succ_mul]
    exact (Nat.mul_le_mul_right _ oneName).trans coversSlashed
  have capSlashed : preset.largestEffectiveBalance ≤ step.slashed := by omega
  have slashedEq : (start.afterBlocks step (blocks + 1)).slashed =
      (start.afterBlocks step blocks).slashed + step.slashed := by
    rw [RunStart.afterBlocks_succ]
  have slashedRoom : (start.afterBlocks step (blocks + 1)).slashed < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (raisedRun.slashed fork)
  have slashedAdvanced := runBounded.slashed
  -- The balances at the turn are within the budget.
  have supplyEq : (start.afterBlocks step (blocks + 1)).supply =
      (start.afterBlocks step blocks).supply + step.supply := by
    rw [RunStart.afterBlocks_succ]
  have whistle : (slashedBalanceSum turn - slashedBalanceSum advanced) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      step.slashed / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Nat.div_le_div_right (by omega)
  have depositsLe := deposits
  have supplyBefore := runBounded.supply
  have budgetSupply := raisedRun.supply_le_budget
  have issuanceLe := Nat.mul_le_mul_right (preset.epochIssuanceBeforeAltair budget) le
  have balanceSumLe : balanceSum turn ≤ budget := by omega
  refine ⟨fun amount read => ?_, fun altair => ?_, fun position balance read => ?_, by omega⟩
  · -- The slashed balances plus one more largest cap are within the slashed bound.
    have entryLe : amount.toNat ≤ slashedBalanceSum turn := by
      unfold readCircular at read
      split at read
      · cases read
      · cases read
        unfold slashedBalanceSum
        exact List.le_sum_of_mem (List.mem_map_of_mem (Vector.mem_toList_iff.mpr
          (Vector.getElem_mem _)))
    omega
  · -- The whistleblower reward of one largest cap, times the proposer weight, fits.
    rw [UInt64.toNat_div]
    have weight : PROPOSER_WEIGHT.toNat = 8 := rfl
    rw [weight]
    have divLe : validator.effectiveBalance.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
        step.slashed / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Nat.div_le_div_right (capLe.trans capSlashed)
    have room := conditions.run.supplyRoom
    simp only [RunStart.afterBlocks] at room
    have six : 6 ≤ preset.chainBlocks epochs := by
      unfold Preset.chainBlocks
      have := conditions.run.slots
      exact this.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have sixSupply := Nat.mul_le_mul_right step.supply six
    omega
  · -- Each balance is at most their sum, within the budget.
    have below := (Array.getElem?_eq_some_iff.mp read).1
    have balanceLe := balance_le_balanceSum turn below
    rw [Array.getElem?_eq_getElem below, Option.some.injEq] at read
    rw [read] at balanceLe
    omega

/-- Take the state a block reaches after its proposer slashings and first `j` attester slashings.

When the block has at most `j` attester slashings, that is the state after all of them.

The conditions of the chain hold, and one more block fits its count.

Then starting the exit of a validator in the registry at the turn succeeds. -/
private theorem slashingTurn_exitRoom {start : RunStart} {step : BlockStep}
    {limits : BlockLimits} {budget epochs lastEpoch startEpoch blocks : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    -- The epochs of the chain end by its last epoch.
    (fits : startEpoch + epochs ≤ lastEpoch)
    -- The ceiling step covers the exits.
    (coversCeiling : 1 + budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      (start.afterBlocks step (preset.chainBlocks epochs)).load +
      limits.joins *
        (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) +
      limits.withdrawals * (budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ≤
    step.ceiling)
    -- The withdrawal delay is positive, and an increment is at most the least balance to activate.
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    {fork : Fork} {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {advanced turn : BeaconState preset fork} {j : Nat}
    -- The facts of the chain hold at `advanced`, after advancing the slots and before the block.
    (advancedHolds : ChainHolds config start step budget startEpoch blocks advanced)
    (raised : blocks + 1 ≤ preset.chainBlocks epochs)
    -- The epoch of `advanced` is within the epochs of the chain.
    (le : (getCurrentEpoch advanced).toNat - startEpoch ≤ epochs)
    (turned : SlashingTurn config checks engine advanced block j turn)
    -- The withdrawal requests of the block are within the limit.
    (withdrawals : (blockWithdrawalRequests block.body).length ≤ limits.withdrawals)
    -- The sum of the balances at `advanced` is within the budget.
    (capped : balanceSum advanced ≤ budget)
    {index : ValidatorIndex} (inside : index.toNat < turn.validators.data.size) :
    ∃ exited, initiateValidatorExit config turn index = .ok exited := by
  have baseRun := conditions.at (Nat.le_of_succ_le raised)
  have raisedRun := conditions.at raised
  have runBounded := advancedHolds.bounded
  have increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT :=
    UInt64.pos_iff_ne_zero.mpr baseRun.positive.increment
  obtain ⟨sizeTurn, effectiveTurn, -⟩ := slashingTurn_slashed_le advancedHolds.shaped.capped turned
  have sumTurn : effectiveBalanceSum turn = effectiveBalanceSum advanced :=
    effectiveBalanceSum_eq_of_effectiveKept sizeTurn effectiveTurn
  have effectiveLe := runBounded.effective_le baseRun le
  have tripled := baseRun.tripled
  obtain ⟨reached, costLe, firstReached, exitsReached, queuesReached⟩ :=
    slashingTurn_exits turned increment baseRun.minimum baseRun.maximum activationIncrement
      withdrawable
      (ceiling := (start.afterBlocks step blocks).ceilingAt preset budget
        ((getCurrentEpoch advanced).toNat - startEpoch) + 1)
      (by have := baseRun.first_le_ceilingAt fits advancedHolds.started; omega)
      (fun validator member set => (runBounded.exits validator member set).trans
        (Nat.le_succ _))
      (fun electra => ⟨runBounded.queue electra,
        (runBounded.consolidations electra).trans (Nat.le_succ _)⟩) capped
  have joined : exitCostFrom preset turn advanced.validators.data.size = 0 := by
    rw [← sizeTurn]
    unfold exitCostFrom
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl
  have withdrawn : (if .glamsterdam ≤ fork then partialExitCost preset budget block.body
      else 0) ≤ limits.withdrawals * (budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) := by
    split
    · exact (partialExitCost_le budget block.body).trans
        (Nat.mul_le_mul_right _ withdrawals)
    · exact Nat.zero_le _
  have reachedLe := reached_le_ceilingAt coversCeiling raised effectiveLe
    (RunBounded.size_le runBounded) costLe (by rw [joined]; exact Nat.zero_le _) withdrawn
  have ceilingLe : (start.afterBlocks step (blocks + 1)).ceilingAt preset budget
        ((getCurrentEpoch advanced).toNat - startEpoch) ≤
      (start.afterBlocks step (blocks + 1)).ceilingAt preset budget epochs := by
    unfold RunStart.ceilingAt
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ le) _
  have exitRoom := raisedRun.exitRoom
  by_cases electra : .pectra ≤ fork
  · have registryLe : turn.validators.data.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat := by
      rw [sizeTurn]
      exact (RunBounded.size_le runBounded).trans baseRun.load.1
    have carriedLe := (queuesReached electra).2
    have carriedBefore := runBounded.exitChurn electra
    have ceilingChurn : exitChurnCeiling config turn ≤ exitChurnBound preset config budget := by
      unfold exitChurnCeiling exitChurnBound
      omega
    have churnRoom := baseRun.churnRoom
    have carried : (turn.exitBalanceToConsume electra).toNat +
        3 * exitChurnCeiling config turn < 2 ^ 64 := by
      have maxLe : max (advanced.exitBalanceToConsume electra).toNat
          (exitChurnCeiling config turn) ≤
          max (start.afterBlocks step blocks).exitChurn (exitChurnBound preset config budget) :=
        max_le carriedBefore (ceilingChurn.trans (le_max_right _ _))
      omega
    exact initiateValidatorExit_total_of_electra electra registryLe (by omega) increment
      baseRun.minimum baseRun.maximum inside firstReached (queuesReached electra).1
      exitsReached carried (by omega)
  · obtain ⟨exited, ok, -⟩ := initiateValidatorExit_total_of_lt_electra (config := config)
      (Nat.lt_of_not_le electra) inside firstReached exitsReached (by omega)
    exact ⟨exited, ok⟩

/-- At the turn of an attester slashing of a block, slashing any validator in the registry succeeds.

The turn is the state that the steps before that attester slashing reach.

This says nothing about the rest of the block.

The slashings vector has a nonzero length. -/
theorem slashValidator_total_of_block [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch startEpoch blocks : Nat} {forked : ForkedBeaconState preset}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    -- The withdrawal delay is positive, and an increment is at most the least balance to activate.
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    -- The facts of a chain hold before the slots that lead to the block.
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    {fork : Fork} {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {advanced turn : BeaconState preset fork} {j : Nat}
    (advancedOk : advanceSlotsAcross config checks
      (block.slot.toNat - forked.state.slot.toNat) forked = .ok ⟨fork, advanced⟩)
    (later : forked.state.slot.toNat < block.slot.toNat)
    (turned : SlashingTurn config checks engine advanced block j turn)
    -- The block is within limits that a block step covers, inside the epochs of the chain.
    (bounded : BlockBounded limits block.body)
    (within : block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    -- The signers are within the active balance at each epoch end of the slots.
    (signers : SignersAtEnds config checks forked (block.slot.toNat - forked.state.slot.toNat))
    {slashing : AttesterSlashing preset fork}
    (atJ : block.body.attesterSlashings.data.toList[j]? = some slashing)
    -- That attester slashing counts at least one name, and supplies the budget of one name.
    (named : 1 ≤ slashing.attestation1.attestingIndices.data.size)
    {index : ValidatorIndex} (inside : index.toNat < turn.validators.data.size) :
    ∃ after, slashValidator config turn index = .ok after := by
  -- The slots keep the facts of the chain, and one more block fits its count.
  have advancedHolds : ChainHolds config start step budget startEpoch blocks advanced :=
    ChainHolds.of_advanceSlotsAcross conditions fits _ holds
      (by rwa [Nat.add_sub_cancel' later.le]) signers advancedOk
  have advancedSlot : advanced.slot.toNat = block.slot.toNat := by
    have := advanceSlotsAcross_slot _ advancedOk
    dsimp only at this
    omega
  have slotsPositive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := conditions.run.slots
    omega
  obtain ⟨-, raised⟩ := raised_of_slots slotsPositive holds.counted advancedHolds.started
    advancedSlot later within
  have advancedEpoch : (getCurrentEpoch advanced).toNat ≤ startEpoch + epochs := by
    rw [getCurrentEpoch_toNat, advancedSlot]
    exact within
  have le : (getCurrentEpoch advanced).toNat - startEpoch ≤ epochs := by omega
  -- The steps keep the slot, and the match of the registry and balance lengths.
  obtain ⟨input, started, frameKept, -, -⟩ := slashingTurn_kept turned
  have frameInput := frame_operationsInput started
  have turnSlot : turn.slot = advanced.slot := frameKept.slot.trans frameInput.slot
  have epochTurn : getCurrentEpoch turn = getCurrentEpoch advanced := by
    unfold getCurrentEpoch
    rw [turnSlot]
  have balancesMatch : BalancesMatch turn :=
    frameKept.balancesMatch (frameInput.balancesMatch advancedHolds.invariant.balancesMatch)
  have read : turn.validators.data[index.toNat]? = some turn.validators.data[index.toNat] :=
    Array.getElem?_eq_getElem inside
  have found := getValidator_eq_ok_iff.mpr read
  -- The proposer at the turn, room in the balances, and room for the exit.
  obtain ⟨turnProposer, proposerInside⟩ :=
    slashingTurn_proposer conditions.run.apart turned balancesMatch
  obtain ⟨slashedRoom, rewardRoom, balanceRoom, capped⟩ := slashingTurn_balanceRoom conditions
    covers.slashed (covers.supply fork) advancedHolds raised le turned bounded.slashings
    bounded.deposits atJ named read
  have exitTurn := slashingTurn_exitRoom conditions fits covers.ceiling withdrawable
    activationIncrement advancedHolds raised le turned bounded.withdrawals capped inside
  refine slashValidator_total_of_room found ⟨exitTurn, ?_, Uint64.ne_zero_of_neZero_toNat,
    slashedRoom, rewardRoom, ⟨block.proposerIndex, _, turnProposer,
      getBalance_eq_ok_iff.mpr (Array.getElem?_eq_getElem proposerInside),
      balanceRoom _ _ (Array.getElem?_eq_getElem proposerInside)⟩,
    ⟨_, getBalance_eq_ok_iff.mpr (Array.getElem?_eq_getElem (balancesMatch ▸ inside))⟩⟩
  -- The epoch of the turn is at most the last epoch of the chain.
  have baseRun := conditions.at (Nat.le_of_succ_le raised)
  have epochRoom := baseRun.epochRoom
  rw [epochTurn]
  omega

end EthLib.Consensus
