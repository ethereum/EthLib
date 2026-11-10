module

public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints

/-!
# Proofs: unrealized checkpoints are those of the next epoch

The fork choice runs justification and finalization on the state after a block.

The checkpoints it gets are the unrealized checkpoints of the block.

If no other block comes before the next epoch, the slot advance runs the same step at its end.

It weighs the same participation, the same balances and the same block roots.

So its checkpoints are the unrealized ones, also when the block slashed validators.

The block roots of the history must cover two epochs, as both presets do.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state tip after : BeaconState preset fork} {next : Slot}

section Helpers

open Serialization.Ssz Cryptography.Bls

/-! ## The epoch steps after justification keep the justification bits -/

/-- A step that keeps the justification bits. -/
private abbrev Bits (state after : BeaconState preset fork) : Prop :=
  after.justificationBits = state.justificationBits

private theorem Bits.trans {first second third : BeaconState preset fork}
    (one : Bits first second) (two : Bits second third) : Bits first third :=
  Eq.trans two one

private theorem Bits.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x s', step s x = .ok s' → Bits s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Bits state after :=
  foldlM_ok_invariant (Bits state) (fun _ _ _ before ok => before.trans (keeps _ _ _ ok))
    (show Bits state state from rfl) computed

private theorem bits_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : Bits state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

private theorem bits_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : Bits state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem bits_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : Bits state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem bits_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    Bits state after := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    rfl

private theorem bits_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Bits state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, -, set⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  · exact (bits_exitQueue queue).trans (bits_setValidator set)

private theorem bits_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : Bits state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact (bits_increaseBalance raised).trans (bits_decreaseBalance lowered)

private theorem bits_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : Bits state after :=
  Bits.foldlM (fun _ _ _ ok => bits_applyDeltas ok) computed

private theorem bits_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : Bits state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact Bits.foldlM (fun _ _ _ ok => bits_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact bits_applyAllDeltas applied

private theorem bits_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : Bits state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, marked, markedOk, computed⟩ := computed
  have set : Bits state marked := bits_setValidator markedOk
  split at computed
  · rw [liftAccessor_ok] at computed
    exact set.trans (bits_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

private theorem bits_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : Bits state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact bits_setValidator set

private theorem bits_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    Bits state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact bits_setValidator set
  split at computed
  · rw [liftAccessor_ok] at computed
    exact bits_initiateValidatorExit computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact bits_setValidator computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl

private theorem bits_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : Bits state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact Bits.foldlM (fun _ _ _ ok => bits_updateRegistryEntryElectra ok) computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  exact (Bits.foldlM (fun _ _ _ ok => bits_updateRegistryEntry ok) updatedOk).trans
    (Bits.foldlM (fun _ _ _ ok => bits_activateValidator ok) activated)

private theorem bits_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    Bits state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact bits_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl

private theorem bits_applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement index = .ok after) :
    Bits state after := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, lowered⟩ := computed
      exact bits_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl

private theorem bits_processSlashings (computed : processSlashings state = .ok after) :
    Bits state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact Bits.foldlM (fun _ _ _ ok => bits_applySlashingPenaltyElectra ok) applied
  · exact Bits.foldlM (fun _ _ _ ok => bits_applySlashingPenalty ok) computed

private theorem bits_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : Bits state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
    subst computed <;> rfl

private theorem bits_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : Bits state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, set⟩ := computed
  exact bits_setValidator set

private theorem bits_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : Bits state after := by
  unfold processEffectiveBalanceUpdates at computed
  exact Bits.foldlM (fun _ _ _ ok => bits_updateEffectiveBalance ok) computed

private theorem bits_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    Bits state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  rfl

private theorem bits_processRandaoMixesReset
    (computed : processRandaoMixesReset state = .ok after) : Bits state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  rfl

private theorem bits_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : Bits state after := by
  unfold processHistoricalRootsUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals rfl

private theorem bits_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) : Bits state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  rfl

private theorem bits_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) : Bits state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    rfl

private theorem bits_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Bits state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rfl
  split at computed
  · cases computed
    rfl
  · cases computed

private theorem bits_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    Bits state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      rfl
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact bits_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ rfl
  · rw [liftAccessor_ok] at computed
    exact bits_increaseBalance computed

private theorem bits_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      Bits state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      rfl
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (bits_applyPendingDeposit credited).trans
        (bits_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact bits_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      rfl
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (bits_applyPendingDeposit credited).trans
      (bits_passPendingDeposits (deposits := rest) ‹_›)

private theorem bits_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    Bits state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact bits_passPendingDeposits ‹_›

private theorem bits_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      Bits state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact bits_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      rfl
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (bits_decreaseBalance loweredOk).trans <|
      (bits_increaseBalance raisedOk).trans
        (bits_passPendingConsolidations (result := (passed, read)) passedOk)

private theorem bits_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) : Bits state after := by
  unfold processPendingConsolidations at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact bits_passPendingConsolidations ‹_›

private theorem bits_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) : Bits state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    exact (bits_processPendingDeposits deposited).trans
      (bits_processPendingConsolidations consolidated)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl

private theorem bits_processBuilderPendingPayments {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) : Bits state after := by
  simp only [processBuilderPendingPayments, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  rfl

private theorem bits_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    Bits state after := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals rfl

private theorem bits_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) : Bits state after := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals rfl

private theorem bits_processProposerLookahead {fulu : .fusaka ≤ fork}
    (computed : processProposerLookahead state fulu = .ok after) : Bits state after := by
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

private theorem bits_processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) : Bits state after := by
  simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- The steps that close an epoch from Altair, after the history, keep the bits. -/
private theorem bits_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : Bits rooted after := by
  have lookedBits : Bits synced looked := by
    split at lookedOk
    · exact bits_processProposerLookahead (liftAccessor_ok.mp lookedOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ rfl
  have windowedBits : Bits looked after := by
    split at windowed
    · exact bits_processPtcWindow (liftAccessor_ok.mp windowed)
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ rfl
  exact (show Bits rooted (processParticipationFlagUpdates rooted altair) from rfl).trans <|
    (bits_processSyncCommitteeUpdates syncedOk).trans (lookedBits.trans windowedBits)

/-- The epoch transition is justification, then steps that keep the bits and the frame. -/
private theorem processEpoch_bits (computed : processEpoch config checks state = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      Frame justified after ∧ Bits justified after := by
  unfold processEpoch at computed
  split at computed
  · obtain ⟨justified, justifiedOk, frame⟩ := processEpochAltair_frame computed
    refine ⟨justified, justifiedOk, frame, ?_⟩
    unfold processEpochAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨justified', justifiedOk', scored, scoredOk, rewarded, rewardedOk, registered,
      registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk,
      balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
    rw [justifiedOk, Except.ok.injEq] at justifiedOk'
    subst justifiedOk'
    have resetBits : Bits slashed reset := by
      split at resetOk
      · exact bits_processEth1DataReset resetOk
      · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
        exact resetOk ▸ rfl
    have paidBits : Bits pending paid := by
      split at paidOk
      · exact bits_processBuilderPendingPayments (liftAccessor_ok.mp paidOk)
      · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
        exact paidOk ▸ rfl
    have head : Bits justified mixed :=
      (bits_processInactivityUpdates scoredOk).trans <|
      (bits_processRewardsAndPenalties rewardedOk).trans <|
      (bits_processRegistryUpdates registeredOk).trans <|
      (bits_processSlashings slashedOk).trans <|
      resetBits.trans <|
      (bits_processPendingBalances pendingOk).trans <|
      paidBits.trans <|
      (bits_processEffectiveBalanceUpdates balancedOk).trans <|
      (bits_processSlashingsReset clearedOk).trans <|
      (bits_processRandaoMixesReset mixedOk)
    split at computed <;> simp only [bind_ok_iff] at computed <;>
      obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
    · exact head.trans <| (bits_processHistoricalSummariesUpdate rootedOk).trans
        (bits_epochEnd syncedOk lookedOk windowed)
    · exact head.trans <| (bits_processHistoricalRootsUpdate rootedOk).trans
        (bits_epochEnd syncedOk lookedOk windowed)
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  refine ⟨justified, justifiedOk, ?_, ?_⟩
  · exact (frame_processRewardsAndPenalties rewardedOk).trans <|
      (frame_processRegistryUpdates registeredOk).trans <|
      (frame_processSlashings slashedOk).trans <|
      (frame_processEth1DataReset resetOk).trans <|
      (frame_processEffectiveBalanceUpdates balancedOk).trans <|
      (frame_processSlashingsReset clearedOk).trans <|
      (frame_processRandaoMixesReset mixedOk).trans <|
      (frame_processHistoricalRootsUpdate rootedOk).trans <|
      frame_processParticipationRecordUpdates rotated
  exact (bits_processRewardsAndPenalties rewardedOk).trans <|
    (bits_processRegistryUpdates registeredOk).trans <|
    (bits_processSlashings slashedOk).trans <|
    (bits_processEth1DataReset resetOk).trans <|
    (bits_processEffectiveBalanceUpdates balancedOk).trans <|
    (bits_processSlashingsReset clearedOk).trans <|
    (bits_processRandaoMixesReset mixedOk).trans <|
    (bits_processHistoricalRootsUpdate rootedOk).trans <|
    bits_processParticipationRecordUpdates rotated

/-! ## Justification reads the same values after the slots of an epoch -/

/-- A state that differs from another only in its slot, roots, header and payload availability. -/
private def Moved (state moved : BeaconState preset fork) : Prop :=
  ∃ (slot : Slot) (stateRoots blockRoots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (header : BeaconBlockHeader)
    (availability : Since .glamsterdam fork (ExecutionPayloadAvailability preset)),
    moved = { state with
      slot := slot
      stateRoots := stateRoots
      blockRoots := blockRoots
      latestBlockHeader := header
      executionPayloadAvailability := availability }

/-- The same epoch gives the same previous epoch. -/
private theorem previous_eq {moved : BeaconState preset fork}
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) :
    getPreviousEpoch moved = getPreviousEpoch state := by
  unfold getPreviousEpoch
  rw [epoch]

/-- From Altair, the participating validators are the same in both states. -/
private theorem participating_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) {altair : .altair ≤ fork}
    {flag : UInt64} {target : Epoch} :
    getUnslashedParticipatingIndices moved altair flag target =
      getUnslashedParticipatingIndices state altair flag target := by
  have previous := previous_eq epoch
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  unfold getUnslashedParticipatingIndices
  rw [epoch, previous]
  rfl

/-- The total active balance is the same in both states. -/
private theorem totalActive_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) :
    getTotalActiveBalance moved = getTotalActiveBalance state := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  unfold getTotalActiveBalance
  rw [epoch]
  rfl

/-- Both states give the same root for the first block of the previous or the current epoch.

This holds whenever both of them read that root. -/
private def SameRoots (state moved : BeaconState preset fork) : Prop :=
  ∀ {target : Epoch} {root root' : Root},
    (target = getPreviousEpoch state ∨ target = getCurrentEpoch state) →
    getBlockRoot state target = .ok root → getBlockRoot moved target = .ok root' → root' = root

/-- Two states with the same three checkpoints and the same justification bits. -/
private def SameOutcome (tip tip' : BeaconState preset fork) : Prop :=
  tip'.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint ∧
    tip'.previousJustifiedCheckpoint = tip.previousJustifiedCheckpoint ∧
    tip'.finalizedCheckpoint = tip.finalizedCheckpoint ∧
    tip'.justificationBits = tip.justificationBits

/-- A justified epoch gets the same checkpoint in both states. -/
private theorem justify_eq {moved : BeaconState preset fork} (roots : SameRoots state moved)
    {justified : Bool} {target : Epoch} {checkpoint first second : Checkpoint}
    (recent : target = getPreviousEpoch state ∨ target = getCurrentEpoch state)
    (one : justifyCheckpoint state justified target checkpoint = .ok first)
    (two : justifyCheckpoint moved justified target checkpoint = .ok second) : second = first := by
  unfold justifyCheckpoint at one two
  cases justified
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at one two
    rw [← one, ← two]
  · simp only [↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at one two
    obtain ⟨root, rootOk, rfl⟩ := one
    obtain ⟨root', rootOk', rfl⟩ := two
    rw [roots recent rootOk rootOk']

/-- Weighing the same balances gives the same checkpoints and bits in both states. -/
private theorem weigh_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    {total previousBalance currentBalance : Gwei}
    (one : weighJustificationAndFinalization state total previousBalance currentBalance = .ok tip)
    (two : weighJustificationAndFinalization moved total previousBalance currentBalance =
      .ok after) : SameOutcome tip after := by
  have previous := previous_eq epoch
  unfold weighJustificationAndFinalization at one two
  rw [epoch, previous] at two
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at one two
  obtain ⟨w1, hw1, th, hth, j1, hj1, w2, hw2, j2, hj2, f1, hf1, f2, hf2, f3, hf3, f4, hf4,
    rfl⟩ := one
  obtain ⟨w1', hw1', th', hth', j1', hj1', w2', hw2', j2', hj2', f1', hf1', f2', hf2', f3', hf3',
    f4', hf4', rfl⟩ := two
  cases hw1.symm.trans hw1'
  cases hth.symm.trans hth'
  cases hw2.symm.trans hw2'
  cases justify_eq roots (.inl rfl) hj1 hj1'
  cases justify_eq roots (.inr rfl) hj2 hj2'
  cases hf1.symm.trans hf1'
  cases hf2.symm.trans hf2'
  cases hf3.symm.trans hf3'
  cases hf4.symm.trans hf4'
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Before Altair, the balance of the signers is the same in both states. -/
private theorem attestingBalance_eq {moved : BeaconState preset fork} (same : Moved state moved)
    {attestations : Array (PendingAttestation preset)} :
    getAttestingBalance moved attestations = getAttestingBalance state attestations := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  rfl

/-- Before Altair, the votes for the first block of an epoch are the same in both states. -/
private theorem matchingTarget_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    {before : fork < .altair} {target : Epoch} {first second : Array (PendingAttestation preset)}
    (recent : target = getPreviousEpoch state ∨ target = getCurrentEpoch state)
    (one : getMatchingTargetAttestations state before target = .ok first)
    (two : getMatchingTargetAttestations moved before target = .ok second) : second = first := by
  have previous := previous_eq epoch
  have source : getMatchingSourceAttestations moved before target =
      getMatchingSourceAttestations state before target := by
    obtain ⟨_, _, _, _, _, rfl⟩ := same
    unfold getMatchingSourceAttestations
    rw [epoch, previous]
  unfold getMatchingTargetAttestations at one two
  rw [source] at two
  simp only [bind_ok_iff] at one two
  obtain ⟨found, foundOk, one⟩ := one
  obtain ⟨found', foundOk', two⟩ := two
  cases foundOk.symm.trans foundOk'
  by_cases empty : found.isEmpty
  · simp only [empty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at one two
    rw [← one, ← two]
  · simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at one two
    obtain ⟨root, rootOk, rfl⟩ := one
    obtain ⟨root', rootOk', rfl⟩ := two
    rw [roots recent rootOk rootOk']

/-- Justification on a moved state with the same epoch and roots ends the same way. -/
private theorem justification_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    (one : processJustificationAndFinalization state = .ok tip)
    (two : processJustificationAndFinalization moved = .ok after) : SameOutcome tip after := by
  have previous := previous_eq epoch
  unfold processJustificationAndFinalization at one two
  split at one
  · rename_i altair
    simp only [altair, ↓reduceDIte] at two
    unfold processJustificationAndFinalizationAltair at one two
    rw [epoch] at two
    split at one
    · rename_i early
      simp only [early, ↓reduceIte] at two
      simp only [pure, Except.pure, Except.ok.injEq] at one two
      subst one two
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact ⟨rfl, rfl, rfl, rfl⟩
    rename_i late
    simp only [late, ↓reduceIte, previous, participating_eq same epoch,
      totalActive_eq same epoch] at two
    simp only [bind_ok_iff, liftAccessor_ok] at one two
    obtain ⟨p, hp, c, hc, t, ht, pb, hpb, cb, hcb, one⟩ := one
    obtain ⟨p', hp', c', hc', t', ht', pb', hpb', cb', hcb', two⟩ := two
    cases hp.symm.trans hp'
    cases hc.symm.trans hc'
    cases ht.symm.trans ht'
    have hpb'' : getTotalBalance state p = .ok pb' := by
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact hpb'
    have hcb'' : getTotalBalance state c = .ok cb' := by
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact hcb'
    cases hpb.symm.trans hpb''
    cases hcb.symm.trans hcb''
    exact weigh_eq same epoch roots one two
  · rename_i altair
    simp only [altair, ↓reduceDIte, epoch] at two
    split at one
    · rename_i early
      simp only [early, ↓reduceIte] at two
      simp only [pure, Except.pure, Except.ok.injEq] at one two
      subst one two
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact ⟨rfl, rfl, rfl, rfl⟩
    rename_i late
    simp only [late, ↓reduceIte, previous, totalActive_eq same epoch,
      attestingBalance_eq same] at two
    simp only [bind_ok_iff, liftAccessor_ok] at one two
    obtain ⟨p, hp, c, hc, t, ht, pb, hpb, cb, hcb, one⟩ := one
    obtain ⟨p', hp', c', hc', t', ht', pb', hpb', cb', hcb', two⟩ := two
    cases matchingTarget_eq same epoch roots (.inl rfl) hp hp'
    cases matchingTarget_eq same epoch roots (.inr rfl) hc hc'
    cases ht.symm.trans ht'
    cases hpb.symm.trans hpb'
    cases hcb.symm.trans hcb'
    exact weigh_eq same epoch roots one two

/-! ## The slots up to the end of the epoch -/

/-- The moved state reads the same block roots at the slots before the original one.

Only slots from the start of the previous epoch count. -/
private def KeepsRoots (state moved : BeaconState preset fork) : Prop :=
  ∀ slot : Slot, slot.toNat < state.slot.toNat →
    ((getCurrentEpoch state).toNat - 1) * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat →
    readCircular moved.blockRoots.elements slot = readCircular state.blockRoots.elements slot

/-- A read of a block root is before the slot of the state, and reads the buffer of roots. -/
private theorem getBlockRootAtSlot_read {slot : Slot} {root : Root}
    (computed : getBlockRootAtSlot state slot = .ok root) :
    slot < state.slot ∧ readCircular state.blockRoots.elements slot = .ok root := by
  unfold getBlockRootAtSlot at computed
  by_cases lt : slot < state.slot
  · simp only [lt, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact ⟨lt, computed⟩
    · cases computed
  · simp only [lt, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨_, thrown, _⟩ := computed
    cases thrown

/-- Roots kept from the start of the previous epoch are the same roots for justification. -/
private theorem sameRoots_of (keeps : KeepsRoots state moved) : SameRoots state moved := by
  intro target root root' recent one two
  unfold getBlockRoot at one two
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at one two
  obtain ⟨slot, start, one⟩ := one
  obtain ⟨slot', start', two⟩ := two
  cases start.symm.trans start'
  obtain ⟨lt, read⟩ := getBlockRootAtSlot_read one
  obtain ⟨-, read'⟩ := getBlockRootAtSlot_read two
  have low : ((getCurrentEpoch state).toNat - 1) * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat := by
    rw [(mulChecked_ok_iff.mp start).2]
    apply Nat.mul_le_mul_right
    rcases recent with rfl | rfl
    · rw [getPreviousEpoch_toNat]
    · exact Nat.sub_le _ _
  rw [keeps slot (UInt64.lt_iff_toNat_lt.mp lt) low, read] at read'
  exact (Except.ok.inj read').symm

/-- The caching of a slot writes one block root, at the position of the slot. -/
private theorem processSlot_blockRoots {cached : BeaconState preset fork}
    (computed : processSlot moved = .ok cached) :
    ∃ root, writeCircular moved.blockRoots.elements moved.slot root =
      .ok cached.blockRoots.elements := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, root, _, blockRoots, written, computed⟩ := computed
  have elements := writeCircularRooted_elements moved.blockRoots moved.slot root
  rw [written] at elements
  refine ⟨root, ?_⟩
  split at computed
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    exact elements.symm
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact elements.symm

/-- The caching of a slot keeps a moved state moved. -/
private theorem Moved.processSlot {cached : BeaconState preset fork} (same : Moved state moved)
    (computed : processSlot moved = .ok cached) : Moved state cached := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  exact ⟨_, _, _, _, _, rfl⟩

/-- A new slot keeps a moved state moved. -/
private theorem Moved.slot (same : Moved state moved) (slot : Slot) :
    Moved state { moved with slot } := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  exact ⟨_, _, _, _, _, rfl⟩

/-- Two numbers that differ by less than a length lie at different positions modulo it. -/
private theorem mod_ne {low high length : Nat} (lt : low < high) (close : high - low < length) :
    high % length ≠ low % length := by
  intro same
  have zero := Nat.sub_mod_eq_zero_of_mod_eq same
  rw [Nat.mod_eq_of_lt close] at zero
  omega

/-- The first slot of the epoch of a state is at most its slot. -/
private theorem epoch_bounds (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat := by
  rw [getCurrentEpoch_toNat]
  exact Nat.div_mul_le_self _ _

/-- The caching of a slot keeps the roots that the original state reads.

The slot must be in the epoch of the original state, from its slot on. -/
private theorem KeepsRoots.processSlot {cached : BeaconState preset fork}
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (keeps : KeepsRoots state moved) (computed : processSlot moved = .ok cached)
    (low : state.slot.toNat ≤ moved.slot.toNat)
    (high : moved.slot.toNat < ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :
    KeepsRoots state cached := by
  intro slot lt lo
  obtain ⟨root, written⟩ := processSlot_blockRoots computed
  rw [readCircular_writeCircular_of_ne written, keeps slot lt lo]
  intro same
  have same' := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same'
  have start := epoch_bounds state
  rw [Nat.add_mul, Nat.one_mul] at high
  rw [Nat.sub_mul, Nat.one_mul] at lo
  exact mod_ne (by omega) (by omega) same'

/-- The slots up to the first slot of the next epoch end as justification on the original state.

The last of them runs the epoch transition, on a state that reads the same values. -/
private theorem advanceSlots_outcome
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip) :
    ∀ {count : Nat} {moved after : BeaconState preset fork}, Moved state moved →
      KeepsRoots state moved → state.slot.toNat ≤ moved.slot.toNat →
      moved.slot.toNat + count + 1 =
        ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      advanceSlots config checks (count + 1) moved = .ok after → SameOutcome tip after
  | count, moved, after, same, keeps, low, total, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨stepped, steppedOk, rest⟩ := computed
    simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at steppedOk
    obtain ⟨nextSlot, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := steppedOk
    simp only [UInt64.toNat_one] at sum
    have cachedSlot := processSlot_slot cachedOk
    have cachedSame := same.processSlot cachedOk
    have cachedKeeps := keeps.processSlot window cachedOk low (by omega)
    have start := epoch_bounds state
    have stateEpoch := getCurrentEpoch_toNat state
    rw [Nat.add_mul, Nat.one_mul] at total
    have epoch : getCurrentEpoch cached = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat cached, cachedSlot]
      exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    unfold epochIfLast at epochedOk
    cases count with
    | zero =>
      simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      have boundary : nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod, sum, UInt64.toNat_zero, show moved.slot.toNat + 1 =
          ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat by
            rw [Nat.add_mul, Nat.one_mul]; omega]
        exact Nat.mul_mod_left _ _
      simp only [boundary, ↓reduceIte] at epochedOk
      obtain ⟨justified, justifiedOk, frame, bits⟩ := processEpoch_bits epochedOk
      obtain ⟨current, previous, finalized, justificationBits⟩ :=
        justification_eq cachedSame epoch (sameRoots_of cachedKeeps) pulled justifiedOk
      exact ⟨frame.currentJustified.trans current, frame.previousJustified.trans previous,
        frame.finalized.trans finalized, Eq.trans bits justificationBits⟩
    | succ count =>
      have notBoundary : ¬ nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
        intro boundary
        have zero := congrArg UInt64.toNat boundary
        rw [UInt64.toNat_mod, sum, UInt64.toNat_zero] at zero
        have split := Nat.div_add_mod (moved.slot.toNat + 1) preset.SLOTS_PER_EPOCH.toNat
        rw [zero, Nat.add_zero, Nat.div_eq_of_lt_le (k := (getCurrentEpoch state).toNat)
          (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega), Nat.mul_comm] at split
        omega
      simp only [notBoundary, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact advanceSlots_outcome window pulled (cachedSame.slot nextSlot) cachedKeeps
        (by simp only; omega) (by simp only; rw [Nat.add_mul, Nat.one_mul]; omega) rest

end Helpers

/-- Advance a state to the first slot of the next epoch, with no block on the way.

Its justified and finalized checkpoints are then those of the state after justification.

Its justification bits are also those of that state.

That step reads the same participation, balances and block roots as the epoch transition.

The theorem assumes that the block roots of the history cover two epochs, as both presets do.

The bound is on natural numbers, since twice the slots of an epoch could overflow 64 bits. -/
theorem processSlots_checkpoints_eq_of_justification
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip)
    (start : computeStartSlotAtEpoch preset (getCurrentEpoch state + 1) = .ok next)
    (advanced : processSlots config checks state next = .ok after) :
    after.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint ∧
      after.previousJustifiedCheckpoint = tip.previousJustifiedCheckpoint ∧
      after.finalizedCheckpoint = tip.finalizedCheckpoint ∧
      after.justificationBits = tip.justificationBits := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advanced
  obtain ⟨_, lt, advanced⟩ := advanced
  have lt' := UInt64.lt_iff_toNat_lt.mp lt
  have nextValue : next.toNat =
      ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [(mulChecked_ok_iff.mp start).2, UInt64.toNat_add, UInt64.toNat_one]
    have bounded := (getCurrentEpoch state).toNat_lt
    by_cases full : (getCurrentEpoch state).toNat + 1 < 2 ^ 64
    · rw [Nat.mod_eq_of_lt full]
    · have wrapped : ((getCurrentEpoch state).toNat + 1) % 2 ^ 64 = 0 := by omega
      rw [(mulChecked_ok_iff.mp start).2, UInt64.toNat_add, UInt64.toNat_one, wrapped,
        Nat.zero_mul] at lt'
      omega
  obtain ⟨count, counted⟩ : ∃ count, next.toNat - state.slot.toNat = count + 1 :=
    ⟨next.toNat - state.slot.toNat - 1, by omega⟩
  rw [counted] at advanced
  exact advanceSlots_outcome (moved := state) window pulled
    ⟨state.slot, state.stateRoots, state.blockRoots, state.latestBlockHeader,
      state.executionPayloadAvailability, rfl⟩
    (fun _ _ _ => rfl) (Nat.le_refl _) (by omega) advanced

/-- The pulled-up tip of a block records the justified checkpoint of the next epoch.

The state of the block must advance to the first slot of the next epoch.

The store records no finalized checkpoint for each block; the previous theorem covers that one.

The theorem assumes that the block roots of the history cover two epochs, as both presets do. -/
theorem Store.computePulledUpTip_unrealizedJustification {store pulledStore : Store preset fork}
    {root : Root}
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : store.computePulledUpTip config root = .ok pulledStore)
    (stateOk : store.blockState root = .ok state)
    (start : computeStartSlotAtEpoch preset (getCurrentEpoch state + 1) = .ok next)
    (advanced : processSlots config checks state next = .ok after) :
    pulledStore.unrealizedJustifications[root]? = some after.currentJustifiedCheckpoint := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨found, foundOk, tip, weighed, block, -, epoch, -, pulled⟩ := pulled
  rw [stateOk, Except.ok.injEq] at foundOk
  subst foundOk
  rw [(processSlots_checkpoints_eq_of_justification window (Base.mapError_ok_iff.mp weighed)
    start advanced).1]
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled <;>
    simp only [updateCheckpoints, updateUnrealizedCheckpoints] <;> split_ifs <;> simp

end EthLib.Consensus
