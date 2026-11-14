module

public import EthLib.Consensus.Proofs.Transition.Totality.AltairWitness
public import EthLib.Consensus.Proofs.Transition.Totality.ChainBlock
public import EthLib.Consensus.Proofs.Transition.Totality.RunHypotheses

/-!
# Proofs: every slot advance after a chain of bounded blocks succeeds

A chain starts from a state that keeps the facts of a chain.

Each of its blocks stays within the limits, and the transition accepts it.

Each block keeps the facts, with one more block in the count.

So the state at the end of the chain keeps them.

From that state, every slot advance within the epochs of the chain succeeds.

At the end of each epoch on the way, the signers must hold at most the active balance.

The draws must end, and a run before Altair must end within the epoch limit.

On mainnet, the step covers the limits for 16 epochs at a budget of `2^57` Gwei.

Before Gloas, the types of a mainnet body keep it within three of those limits.

The chain may start at any epoch up to `2^40`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The chain -/

/-- The states that a chain of blocks reaches from a state, with the number of its blocks.

Each block stays within the limits, and the transition accepts it from the state before it.

At the end of each epoch before each block, the signers hold at most the active balance. -/
inductive ChainReaches (config : Config) (checks : SignatureChecks) (limits : BlockLimits)
    (forked : ForkedBeaconState preset) : Nat → ForkedBeaconState preset → Prop where
  /-- A chain with no block reaches the state it starts from. -/
  | start : ChainReaches config checks limits forked 0 forked
  /-- A chain extends by one block that the transition accepts. -/
  | block {count : Nat} {reached : ForkedBeaconState preset} {fork : Fork}
      {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
      {validateResult : Bool} {after : BeaconState preset fork}
      (prior : ChainReaches config checks limits forked count reached)
      (bounded : BlockBounded limits signed.message.body)
      (signers : SignersAtEnds config checks reached
        (signed.message.slot.toNat - reached.state.slot.toNat))
      (computed :
        stateTransitionAcross config checks engine reached signed validateResult = .ok after) :
      ChainReaches config checks limits forked (count + 1) ⟨fork, after⟩

/-- A chain of blocks keeps the facts of a chain, with its blocks counted.

The step covers the limits, and the last slot of the chain is within its epochs.

The least inclusion delay and the withdrawal delay are positive.

The increment is at most the least balance to activate. -/
theorem ChainHolds.of_chainReaches {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch startEpoch blocks count : Nat}
    {forked reached : ForkedBeaconState preset}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    (inclusion : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat)
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    (reaches : ChainReaches config checks limits forked count reached)
    (within : reached.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs) :
    ChainHolds config start step budget startEpoch (blocks + count) reached.state := by
  induction reaches with
  | start => exact holds
  | @block count reached fork engine signed validateResult after prior bounded signers computed
      priorHolds =>
    obtain ⟨later, afterSlot⟩ := stateTransitionAcross_slot computed
    have blockWithin :
        signed.message.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs := by
      rw [← afterSlot]
      exact within
    rw [← Nat.add_assoc]
    exact ChainHolds.of_stateTransitionAcross conditions fits covers inclusion withdrawable
      activationIncrement (priorHolds ((Nat.div_le_div_right later.le).trans blockWithin))
      bounded blockWithin signers computed

/-! ## The slots after the chain -/

/-- A run of slots from a state of a chain succeeds and keeps the facts of the chain.

The epoch of its last slot is at most the first epoch of the chain plus the number of epochs.

It takes the hypotheses on the signers, the draws and the epoch limit. -/
private theorem advanceSlotsAcross_chain
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {step : BlockStep} {budget epochs lastEpoch startEpoch blocks : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch) :
    ∀ (count : Nat) {forked : ForkedBeaconState preset},
      ChainHolds config start step budget startEpoch blocks forked.state →
      (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs →
      SignersAtEnds config checks forked count →
      DrawsEnd config checks forked count → EpochLimitBeforeAltair forked count →
      ∃ after, advanceSlotsAcross config checks count forked = .ok after ∧
        ChainHolds config start step budget startEpoch blocks after.state :=
  fun count _ holds within signers draws limit =>
  advanceSlotsAcross_of_step
    (Holds := fun f => ChainHolds config start step budget startEpoch blocks f.state)
    (Ahead := fun f =>
      ((f.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
        ∀ cached, processSlot f.state = .ok cached → SignersWithinActive cached) ∧
      ((f.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
        ∀ cached, processSlot f.state = .ok cached → EpochDrawsEnd config checks cached) ∧
      ∀ advanced, advanceSlot config checks f.state = .ok advanced →
        ∀ upgrading, UpgradesPass config checks ⟨f.fork, advanced⟩ upgrading →
          upgradeDue config upgrading = true → UpgradeDrawsEnd upgrading)
    (fun {forked} holds stepWithin ahead stepLimit => by
      obtain ⟨stepSigners, stepDraws, stepUpgradeDraws⟩ := ahead
      obtain ⟨next, nextOk⟩ := ChainHolds.advanceSlotAcross_exists_ok conditions fits holds
        stepWithin stepSigners stepDraws stepUpgradeDraws stepLimit
      exact ⟨next, nextOk, ChainHolds.of_advanceSlotAcross conditions fits holds stepWithin
        stepSigners nextOk⟩)
    count holds within (fun steps below reached reachedOk =>
      ⟨signers steps below reached reachedOk, draws steps below reached reachedOk⟩) limit

/-- Every slot advance within the epochs of a chain succeeds, from a state of the chain.

It keeps the facts of the chain, with the same count of blocks.

At the end of each epoch on the way, the signers hold at most the active balance.

The draws end, and before Altair the advance ends within the epoch limit. -/
theorem ChainHolds.processSlotsAcross_exists_ok
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {step : BlockStep} {budget epochs lastEpoch startEpoch blocks : Nat}
    {forked : ForkedBeaconState preset} {slot : Slot}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    (later : forked.state.slot < slot)
    (within : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : SignersAtEnds config checks forked (slot.toNat - forked.state.slot.toNat))
    (draws : DrawsEnd config checks forked (slot.toNat - forked.state.slot.toNat))
    (limit : EpochLimitBeforeAltair forked (slot.toNat - forked.state.slot.toNat)) :
    ∃ after, processSlotsAcross config checks forked slot = .ok after ∧
      ChainHolds config start step budget startEpoch blocks after.state := by
  have ahead := UInt64.lt_iff_toNat_lt.mp later
  obtain ⟨after, afterOk, afterHolds⟩ := advanceSlotsAcross_chain conditions fits
    (slot.toNat - forked.state.slot.toNat) holds (by rwa [Nat.add_sub_cancel' ahead.le])
    signers draws limit
  refine ⟨after, ?_, afterHolds⟩
  have ensured : ensure (forked.state.slot < slot)
      (TransitionError.slotNotAfter slot forked.state.slot) = .ok () := ensure_ok_iff.mpr later
  simp only [processSlotsAcross, ensured, bind, Except.bind]
  exact afterOk

/-- After a chain of bounded blocks, every slot advance within its epochs succeeds.

The chain starts from a state that keeps the facts of a chain.

The step covers the limits, and the conditions of the chain hold.

The least inclusion delay and the withdrawal delay are positive.

The increment is at most the least balance to activate.

At the end of each epoch of the advance, the signers hold at most the active balance.

The draws end, and before Altair the advance ends within the epoch limit.

The state that the advance returns keeps the facts of the chain, with its blocks counted. -/
theorem processSlotsAcross_exists_ok_of_chain
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch startEpoch blocks count : Nat}
    {forked reached : ForkedBeaconState preset} {slot : Slot}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    (inclusion : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat)
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (holds : ChainHolds config start step budget startEpoch blocks forked.state)
    (reaches : ChainReaches config checks limits forked count reached)
    (later : reached.state.slot < slot)
    (within : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : SignersAtEnds config checks reached (slot.toNat - reached.state.slot.toNat))
    (draws : DrawsEnd config checks reached (slot.toNat - reached.state.slot.toNat))
    (limit : EpochLimitBeforeAltair reached (slot.toNat - reached.state.slot.toNat)) :
    ∃ after, processSlotsAcross config checks reached slot = .ok after ∧
      ChainHolds config start step budget startEpoch (blocks + count) after.state := by
  have reachedWithin :
      reached.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs :=
    (Nat.div_le_div_right (UInt64.lt_iff_toNat_lt.mp later).le).trans within
  exact ChainHolds.processSlotsAcross_exists_ok conditions fits
    (ChainHolds.of_chainReaches conditions fits covers inclusion withdrawable activationIncrement
      holds reaches reachedWithin) later within signers draws limit

/-! ## Mainnet -/

/-- Limits on a block body on mainnet.

Its deposits and deposit requests bring in at most 10,000 ETH, and it applies at most 16 deposits.

It raises the validators plus the pending deposits by at most `2^14`.

Its slashings name at most `2^10` validators, and it carries at most 16 withdrawal requests.

Before Gloas, the body types bound the count of deposits, the load and the withdrawal requests.

The protocol does not cap the Gwei of the deposits, and it allows far more slashed validators. -/
def BlockLimits.mainnet : BlockLimits :=
  { deposits := 10 ^ 13, joins := 16, load := 2 ^ 14, slashings := 2 ^ 10, withdrawals := 16 }

/-- Before Gloas, every mainnet block body is within three of the mainnet limits.

It applies at most 16 deposits of the deposit contract, the most that a body holds.

It raises the load by at most `2^14`, and carries at most 16 withdrawal requests. -/
theorem blockLimits_mainnet_of_body {fork : Fork} (before : fork < .glamsterdam)
    (body : BeaconBlockBody Preset.mainnet fork) :
    blockDepositCount body ≤ BlockLimits.mainnet.joins ∧
      blockLoadBound body ≤ BlockLimits.mainnet.load ∧
      (blockWithdrawalRequests body).length ≤ BlockLimits.mainnet.withdrawals := by
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr before
  have deposits : blockDepositCount body ≤ 16 := by
    have bound := (body.deposits (Nat.lt_trans before (by decide))).bound before
    have limit : Preset.mainnet.MAX_DEPOSITS.toNat = 16 := by decide
    simpa [blockDepositCount, before, limit] using bound
  have requests : blockRequestCount body ≤ 2 ^ 13 + 2 := by
    unfold blockRequestCount
    split
    · rename_i electra
      have d := (body.executionRequests electra).deposits.bound before
      have c := (body.executionRequests electra).consolidations.bound before
      have dl : Preset.mainnet.MAX_DEPOSIT_REQUESTS_PER_PAYLOAD.toNat = 2 ^ 13 := by decide
      have cl : Preset.mainnet.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat = 2 := by decide
      omega
    · simp
  refine ⟨deposits, ?_, ?_⟩
  · unfold blockLoadBound
    simp only [BlockLimits.mainnet]
    split <;> omega
  · unfold blockWithdrawalRequests
    simp only [BlockLimits.mainnet, gloas, dite_false]
    split
    · rename_i electra
      have w := (body.executionRequests ⟨electra, Nat.lt_of_not_le gloas⟩).withdrawals.bound before
      have wl : Preset.mainnet.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD.toNat = 16 := by decide
      simpa using w.trans wl.le
    · simp

/-- Before Gloas, a mainnet block body is within the mainnet limits under two conditions.

Its deposits and deposit requests bring in at most `10^13` Gwei.

Its slashings name at most `2^10` validators. -/
theorem BlockBounded.mainnet {fork : Fork} (before : fork < .glamsterdam)
    {body : BeaconBlockBody Preset.mainnet fork}
    (deposits : blockDepositAmount body ≤ 10 ^ 13) (slashings : blockSlashingCount body ≤ 2 ^ 10) :
    BlockBounded BlockLimits.mainnet body :=
  have limits := blockLimits_mainnet_of_body before body
  ⟨deposits, limits.1, limits.2.1, slashings, limits.2.2⟩

/-- The step of a block on mainnet, which covers the mainnet limits at a budget of `2^57` Gwei.

The supply rises by at most 100,000 ETH, and the effective balances by 16 times 2048 ETH.

The load rises by at most `2^15`, and the exit ceiling by at most `2^32` epochs.

The slashed balances rise by at most `2^10` times 2048 ETH. -/
def BlockStep.mainnet : BlockStep :=
  { supply := 10 ^ 14, effective := 16 * 2048 * 10 ^ 9, load := 2 ^ 15, ceiling := 2 ^ 32,
    slashed := 2 ^ 10 * 2048 * 10 ^ 9 }

/-- On mainnet the step covers the limits, at a budget of `2^57` Gwei and over 16 epochs. -/
theorem blockStep_covers_mainnet (startEpoch : Nat) :
    BlockStep.mainnet.Covers Preset.mainnet BlockLimits.mainnet (RunStart.mainnet startEpoch)
      (2 ^ 57) 16 := by
  have largest : Preset.mainnet.largestEffectiveBalance = 2048 * 10 ^ 9 := by decide
  have increment : Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat = 10 ^ 9 := by decide
  have root : Nat.sqrt (10 ^ 9) = 31622 := (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  have reward : blockRewardBound Preset.mainnet (2 ^ 57) = 70640217747754 := by
    unfold blockRewardBound
    rw [increment, root]
    decide
  have blocks : Preset.mainnet.chainBlocks 16 = 544 := by decide
  have hysteresis : Preset.mainnet.HYSTERESIS_QUOTIENT.toNat = 4 ∧
      Preset.mainnet.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat = 1 := by decide
  refine ⟨?_, ?_, ?_, fun fork => ?_, ?_, ?_⟩
  · simp only [BlockLimits.mainnet, BlockStep.mainnet, largest]
    omega
  · simp only [BlockLimits.mainnet, BlockStep.mainnet, largest]
    omega
  · simp only [BlockLimits.mainnet, BlockStep.mainnet]
    omega
  · have quotient : 512 ≤ (parameters Preset.mainnet fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
      cases fork <;> decide
    have share : 2 ^ 10 * 2048 * 10 ^ 9 /
        (parameters Preset.mainnet fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
        2 ^ 10 * 2048 * 10 ^ 9 / 512 := Nat.div_le_div_left quotient (by decide)
    simp only [BlockLimits.mainnet, BlockStep.mainnet, reward]
    omega
  · simp only [BlockStep.mainnet, hysteresis.1, hysteresis.2]
    omega
  · simp only [BlockLimits.mainnet, BlockStep.mainnet, RunStart.afterBlocks, RunStart.mainnet,
      blocks, increment, largest]
    omega

/-- On mainnet the conditions of a chain hold for 16 epochs, from any epoch up to `2^40`.

They read the mainnet start and step, and a budget of `2^57` Gwei. -/
theorem chainConditions_mainnet {startEpoch : Nat} (early : startEpoch ≤ 2 ^ 40) :
    ChainConditions Preset.mainnet Config.mainnet (RunStart.mainnet startEpoch) BlockStep.mainnet
      (2 ^ 57) 16 (startEpoch + 16) := by
  have run := runConditions_mainnet early
  have root : Nat.sqrt (2 ^ 57) = 379625062 := (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  have blocks : Preset.mainnet.chainBlocks 16 = 544 := by decide
  have seed : Preset.mainnet.MIN_SEED_LOOKAHEAD.toNat = 1 := by decide
  have longest : Preset.mainnet.MAX_SEED_LOOKAHEAD.toNat = 4 := by decide
  have slots : Preset.mainnet.SLOTS_PER_EPOCH.toNat = 32 := by decide
  have roots : Preset.mainnet.SLOTS_PER_HISTORICAL_ROOT.toNat = 8192 := by decide
  have mixes : Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR.toNat = 65536 := by decide
  have slashings : Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR.toNat = 8192 := by decide
  have increment : Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat = 10 ^ 9 := by decide
  have delay : Config.mainnet.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat = 256 := by decide
  have horizon := run.horizon
  have history := run.history
  have depositRoom := run.depositRoom
  refine ⟨{ run with
    effectiveStart := ?_
    supplyRatio := ?_
    supplyRoom := ?_
    horizon := ?_
    firstStart := ?_
    exitRoom := ?_
    depositRoom := ?_
    slashed := ?_
    history := ?_
    load := ?_
    loadRoom := ?_
    slotRoom := ?_
    epochRoom := ?_ }, ?_⟩
  · simp only [RunStart.afterBlocks, RunStart.mainnet, BlockStep.mainnet, blocks, increment]
    decide
  · simp only [Preset.epochIssuanceBeforeAltair, root, RunStart.afterBlocks, RunStart.mainnet,
      BlockStep.mainnet, blocks]
    decide
  · simp only [Preset.epochIssuanceBeforeAltair, Preset.epochIssuance, root, RunStart.afterBlocks,
      RunStart.mainnet, BlockStep.mainnet, blocks]
    decide
  · simp only [RunStart.afterBlocks, RunStart.mainnet] at horizon ⊢
    omega
  · simp only [RunStart.afterBlocks, RunStart.mainnet, BlockStep.mainnet, blocks, longest]
    omega
  · simp only [RunStart.ceilingAt, RunStart.exitStep, RunStart.afterBlocks, RunStart.mainnet,
      BlockStep.mainnet, blocks, increment, delay]
    omega
  · simp only [RunStart.afterBlocks, RunStart.mainnet] at depositRoom ⊢
    omega
  · intro fork
    simp only [RunStart.afterBlocks, RunStart.mainnet, BlockStep.mainnet, blocks]
    cases fork <;> decide
  · simp only [RunStart.afterBlocks, RunStart.mainnet] at history ⊢
    omega
  · simp only [RunStart.afterBlocks, RunStart.mainnet, BlockStep.mainnet, blocks]
    decide
  · simp only [RunStart.afterBlocks, RunStart.mainnet, BlockStep.mainnet, blocks]
    decide
  · rw [seed, slots, roots]
    omega
  · rw [seed, mixes, slashings]
    omega
  · simp only [RunStart.mainnet, longest]
    omega

/-- On mainnet, after a chain of blocks within the mainnet limits, the advance succeeds.

The chain starts from a state that keeps the facts of a chain, with the mainnet start and step.

The budget of effective balances is `2^57` Gwei.

The advance ends at most 16 epochs past the first epoch of the chain, which is at most `2^40`.

It takes the hypotheses on the signers, the draws and the epoch limit of the general theorem. -/
theorem processSlotsAcross_exists_ok_of_chain_mainnet {startEpoch blocks count : Nat}
    {forked reached : ForkedBeaconState Preset.mainnet} {slot : Slot}
    (early : startEpoch ≤ 2 ^ 40)
    (holds : ChainHolds Config.mainnet (RunStart.mainnet startEpoch) BlockStep.mainnet (2 ^ 57)
      startEpoch blocks forked.state)
    (reaches : ChainReaches Config.mainnet checks BlockLimits.mainnet forked count reached)
    (later : reached.state.slot < slot)
    (within : slot.toNat / Preset.mainnet.SLOTS_PER_EPOCH.toNat ≤ startEpoch + 16)
    (signers : SignersAtEnds Config.mainnet checks reached (slot.toNat - reached.state.slot.toNat))
    (draws : DrawsEnd Config.mainnet checks reached (slot.toNat - reached.state.slot.toNat))
    (limit : EpochLimitBeforeAltair reached (slot.toNat - reached.state.slot.toNat)) :
    ∃ after, processSlotsAcross Config.mainnet checks reached slot = .ok after ∧
      ChainHolds Config.mainnet (RunStart.mainnet startEpoch) BlockStep.mainnet (2 ^ 57)
        startEpoch (blocks + count) after.state :=
  processSlotsAcross_exists_ok_of_chain (chainConditions_mainnet early) (Nat.le_refl _)
    (blockStep_covers_mainnet startEpoch) (by decide) (by decide) (by decide) holds reaches later
    within signers draws limit

/-- A state that keeps the facts of a run keeps those of a chain with any step, before any block. -/
theorem RunHolds.toChainHolds_step {start : RunStart} {step : BlockStep} {budget startEpoch : Nat}
    {fork : Fork} {state : BeaconState preset fork}
    (holds : RunHolds config start budget startEpoch state) :
    ChainHolds config start step budget startEpoch 0 state := by
  have chain := holds.toChainHolds
  have zero : start.afterBlocks step 0 = start.afterBlocks BlockStep.zero 0 := by
    simp [RunStart.afterBlocks]
  exact ⟨chain.started, chain.invariant, chain.shaped, chain.wellFormed, chain.resolved,
    chain.early, chain.voted, chain.counted, zero ▸ chain.bounded⟩

/-- After a chain of blocks within the mainnet limits, the advance from the Altair witness succeeds.

The advance ends at most 16 epochs past the epoch of the witness.

It takes the hypotheses on the signers, the draws and the epoch limit of the general theorem. -/
theorem processSlotsAcross_exists_ok_of_chain_altairWitnessState {count : Nat}
    {reached : ForkedBeaconState Preset.mainnet} {slot : Slot}
    (reaches : ChainReaches Config.mainnet checks BlockLimits.mainnet ⟨.altair, altairWitnessState⟩
      count reached)
    (later : reached.state.slot < slot)
    (within : slot.toNat / Preset.mainnet.SLOTS_PER_EPOCH.toNat ≤ 74240 + 16)
    (signers : SignersAtEnds Config.mainnet checks reached (slot.toNat - reached.state.slot.toNat))
    (draws : DrawsEnd Config.mainnet checks reached (slot.toNat - reached.state.slot.toNat))
    (limit : EpochLimitBeforeAltair reached (slot.toNat - reached.state.slot.toNat)) :
    ∃ after, processSlotsAcross Config.mainnet checks reached slot = .ok after ∧
      ChainHolds Config.mainnet (RunStart.mainnet 74240) BlockStep.mainnet (2 ^ 57) 74240 count
        after.state := by
  have result := processSlotsAcross_exists_ok_of_chain_mainnet (by decide)
    (runHolds_altairWitnessState.toChainHolds_step (step := BlockStep.mainnet)) reaches later
    within signers draws limit
  rwa [Nat.zero_add] at result

end EthLib.Consensus
