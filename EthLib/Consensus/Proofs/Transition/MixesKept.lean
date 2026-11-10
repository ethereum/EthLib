module

public import EthLib.Consensus.Proofs.Transition.ActiveKept

/-!
# Proofs: a block and a slot write at most one RANDAO mix, at every fork

A block writes at most the mix of its epoch, in its RANDAO step.

The epoch step writes at most the mix of the next epoch, in its reset of the mixes.

So a slot writes at most the mix of the epoch that it reaches.

With the activity facts, a block and a slot then keep the committees of each recent epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Steps that keep the mixes and the slot -/

/-- Two states with the same RANDAO mixes and the same slot. -/
private def Kept (state after : BeaconState preset fork) : Prop :=
  after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot

/-- Every state keeps its own mixes and slot. -/
private theorem Kept.refl (state : BeaconState preset fork) : Kept state state :=
  ⟨rfl, rfl⟩

/-- Two steps in a row that keep the mixes and the slot keep them. -/
private theorem Kept.trans {first second third : BeaconState preset fork}
    (one : Kept first second) (two : Kept second third) : Kept first third :=
  ⟨two.1.trans one.1, two.2.trans one.2⟩

/-- A fold whose every step keeps the mixes and the slot keeps them. -/
private theorem Kept.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (kept : ∀ s x s', step s x = .ok s' → Kept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (Kept.refl state) computed

/-- A step that keeps the mixes and the slot, as a pair of equalities. -/
private theorem Kept.of_eq
    (kept : after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot) : Kept state after :=
  kept

/-- A step that keeps the inputs of a payload keeps the mixes and the slot. -/
private theorem Kept.of_payloadInputs (inputs : PayloadInputs state after) : Kept state after :=
  ⟨inputs.randaoMixes, inputs.slot⟩

/-- A validator write at a plain position keeps the mixes and the slot. -/
private theorem Kept.of_setValidatorAt {index : Nat} {validator : Validator}
    (set : state.setValidatorAt index validator = .ok after) : Kept state after := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact ⟨rfl, rfl⟩

/-- Adding a validator keeps the mixes and the slot. -/
private theorem kept_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Kept state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  split at computed
  · cases computed
    exact ⟨rfl, rfl⟩
  · cases computed

/-- A pending deposit keeps the mixes and the slot. -/
private theorem kept_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    Kept state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact Kept.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact kept_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Kept.refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact Kept.of_payloadInputs (payloadInputs_increaseBalance computed)

/-! ## The steps of an epoch from Altair -/

/-- The inactivity updates keep the mixes and the slot. -/
private theorem kept_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) : Kept state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩

/-- The registry updates keep the mixes and the slot. -/
private theorem kept_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : Kept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine Kept.foldlM (fun _ _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact Kept.of_setValidatorAt set
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact Kept.of_payloadInputs (payloadInputs_initiateValidatorExit exited)
    split at ok
    · exact Kept.of_setValidatorAt (liftAccessor_ok.mp ok)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Kept.refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  refine (Kept.foldlM (fun _ _ _ ok => ?_) updatedOk).trans
    (Kept.foldlM (fun _ _ _ ok => ?_) activated)
  · simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, markedOk, ok⟩ := ok
    have set := Kept.of_setValidatorAt markedOk
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact set.trans (Kept.of_payloadInputs (payloadInputs_initiateValidatorExit exited))
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ set
  · simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    exact Kept.of_payloadInputs (payloadInputs_setValidator set)

/-- A pass over the pending deposits keeps the mixes and the slot. -/
private theorem kept_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      Kept state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Kept.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact Kept.refl _
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (kept_applyPendingDeposit credited).trans
        (kept_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact kept_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact Kept.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (kept_applyPendingDeposit credited).trans
      (kept_passPendingDeposits (deposits := rest) ‹_›)

/-- A pass over the pending consolidations keeps the mixes and the slot. -/
private theorem kept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      Kept state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Kept.refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact kept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact Kept.refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact ((Kept.of_payloadInputs (payloadInputs_decreaseBalance loweredOk)).trans
      (Kept.of_payloadInputs (payloadInputs_increaseBalance raisedOk))).trans
      (kept_passPendingConsolidations (result := (passed, read)) passedOk)

/-- The pending deposits and consolidations keep the mixes and the slot. -/
private theorem kept_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) : Kept state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, deposited, consolidated⟩ := computed
    have deposits : Kept state middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals exact (kept_passPendingDeposits ‹_›).trans ⟨rfl, rfl⟩
    refine deposits.trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (kept_passPendingConsolidations ‹_›).trans ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

/-- The historical summaries update keeps the mixes and the slot. -/
private theorem kept_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    Kept state after := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact ⟨rfl, rfl⟩

/-- The last steps of an epoch, from the participation flags on, keep the mixes and the slot. -/
private theorem kept_epochTail {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : Kept rooted after := by
  have flags : Kept rooted (processParticipationFlagUpdates rooted altair) := ⟨rfl, rfl⟩
  have syncedKept : Kept (processParticipationFlagUpdates rooted altair) synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact ⟨rfl, rfl⟩
  have lookedKept : Kept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ Kept.refl _
  have windowedKept : Kept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ Kept.refl _
  exact flags.trans <| syncedKept.trans <| lookedKept.trans windowedKept

/-- An epoch one above another, as natural numbers, is its successor. -/
private theorem eq_add_one_of_toNat {next epoch : Epoch}
    (succ : next.toNat = epoch.toNat + 1) : next = epoch + 1 := by
  apply UInt64.toNat_inj.mp
  have bound := next.toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_one]
  omega

/-- From Altair, the epoch step writes at most the RANDAO mix of the next epoch. -/
private theorem processEpochAltair_mixesKeptBut {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    MixesKeptBut (getCurrentEpoch state + 1) state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : Kept slashed reset := by
    split at resetOk
    · exact Kept.of_eq (randaoMixes_slot_processEth1DataReset resetOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ Kept.refl _
  have paidKept : Kept pending paid := by
    split at paidOk
    · rw [processBuilderPendingPayments_eq (liftAccessor_ok.mp paidOk)]
      exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ Kept.refl _
  have clearedKept : Kept balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact ⟨rfl, rfl⟩
  have head : Kept state cleared :=
    (Kept.of_eq (randaoMixes_slot_processJustificationAndFinalization justifiedOk)).trans <|
    (kept_processInactivityUpdates scoredOk).trans <|
    (Kept.of_eq (randaoMixes_slot_processRewardsAndPenalties rewardedOk)).trans <|
    (kept_processRegistryUpdates registeredOk).trans <|
    (Kept.of_eq (randaoMixes_slot_processSlashings slashedOk)).trans <| resetKept.trans <|
    (kept_processPendingBalances pendingOk).trans <| paidKept.trans <|
    (Kept.of_eq (randaoMixes_slot_processEffectiveBalanceUpdates balancedOk)).trans clearedKept
  have tail : Kept mixed after := by
    split at computed <;> simp only [bind_ok_iff] at computed <;>
      obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
    · exact (kept_processHistoricalSummariesUpdate rootedOk).trans
        (kept_epochTail syncedOk lookedOk windowed)
    · exact (Kept.of_eq (randaoMixes_slot_processHistoricalRootsUpdate rootedOk)).trans
        (kept_epochTail syncedOk lookedOk windowed)
  have epoch : getCurrentEpoch cleared = getCurrentEpoch state := by
    simp only [getCurrentEpoch, head.2]
  obtain ⟨next, mix, randaoMixes, nextEq, -, written, rfl⟩ := processRandaoMixesReset_eq mixedOk
  rw [epoch] at nextEq
  rw [← eq_add_one_of_toNat nextEq]
  intro other apart
  have plain := writeCircularRooted_elements cleared.randaoMixes next mix
  rw [written] at plain
  rw [tail.1]
  exact (readCircular_writeCircular_of_ne plain.symm (Ne.symm apart)).trans (by rw [head.1])

/-- The epoch step writes at most the RANDAO mix of the next epoch, at every fork. -/
theorem mixesKeptBut_processEpoch (computed : processEpoch config checks state = .ok after) :
    MixesKeptBut (getCurrentEpoch state + 1) state after := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processEpoch, altair, ↓reduceDIte] at computed
    exact processEpochAltair_mixesKeptBut computed
  · obtain ⟨next, nextEq, mixes⟩ :=
      mixesKeptBut_processEpoch_of_lt_altair (Nat.lt_of_not_le altair) computed
    rwa [eq_add_one_of_toNat nextEq] at mixes

/-- One slot writes at most the RANDAO mix of the epoch that it reaches, at every fork. -/
theorem mixesKeptBut_advanceSlot (computed : advanceSlot config checks state = .ok after) :
    MixesKeptBut (getCurrentEpoch after) state after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  -- The slot step writes neither the mixes nor the slot.
  have cachedMixes : cached.randaoMixes = state.randaoMixes := by rw [cachedEq]
  have cachedSlot : cached.slot = state.slot := by rw [cachedEq]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have mixes := mixesKeptBut_processEpoch epochedOk
    -- At the end of an epoch, the epoch that the slot reaches is the next one.
    have written : getCurrentEpoch { epoched with slot := next } = getCurrentEpoch cached + 1 := by
      apply eq_add_one_of_toNat
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, cachedSlot]
      exact epochs
    rw [written]
    intro other apart
    exact (mixes other apart).trans (by rw [cachedMixes])
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    intro other _
    show readCircular cached.randaoMixes.elements other = _
    rw [cachedMixes]

/-! ## The steps of a block -/

/-- A deposit of a block keeps the mixes and the slot. -/
private theorem kept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    Kept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  have indexed : Kept state { state with eth1DepositIndex := fun _ => next } := ⟨rfl, rfl⟩
  refine indexed.trans ?_
  unfold applyDeposit at applied
  split at applied
  · unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨_, added, pushed⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (kept_addValidatorToRegistry added).trans ⟨rfl, rfl⟩
      · cases applied
        exact Kept.refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact ⟨rfl, rfl⟩
  · exact kept_applyPendingDeposit applied

/-- The operations of a block keep the mixes and the slot, at every fork. -/
private theorem kept_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    Kept state after := by
  by_cases gloas : Fork.glamsterdam ≤ fork
  · exact Kept.of_payloadInputs (payloadInputs_processOperations gloas computed)
  simp only [processOperations, gloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : Kept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact Kept.foldlM (fun _ _ _ ok =>
        Kept.of_payloadInputs (payloadInputs_processBlsToExecutionChange ok)) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ Kept.refl _
  have requests : Kept changed after := by
    split at requestsOk
    · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requestsOk
      obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := requestsOk
      exact (Kept.foldlM (fun _ _ _ ok =>
          Kept.of_payloadInputs (payloadInputs_processDepositRequest ok)) depositsOk).trans <|
        (Kept.foldlM (fun _ _ _ ok =>
          Kept.of_payloadInputs (payloadInputs_processWithdrawalRequest ok)) withdrawalsOk).trans <|
        Kept.foldlM (fun _ _ _ ok =>
          Kept.of_payloadInputs (payloadInputs_processConsolidationRequest ok)) consolidationsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ Kept.refl _
  exact (Kept.foldlM (fun _ _ _ ok =>
      Kept.of_payloadInputs (payloadInputs_processProposerSlashing ok)) proposersOk).trans <|
    (Kept.foldlM (fun _ _ _ ok =>
      Kept.of_payloadInputs (payloadInputs_processAttesterSlashing ok)) attestersOk).trans <|
    (Kept.foldlM (fun _ _ _ ok =>
      Kept.of_payloadInputs (payloadInputs_processAttestation ok)) attestedOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processDeposit ok) depositedOk).trans <|
    (Kept.foldlM (fun _ _ _ ok =>
      Kept.of_payloadInputs (payloadInputs_processVoluntaryExit ok)) exitsOk).trans <|
    changes.trans requests

/-- Two states with the same slot, whose RANDAO mixes agree except at the current epoch. -/
private def Writes (state after : BeaconState preset fork) : Prop :=
  MixesKeptBut (getCurrentEpoch state) state after ∧ after.slot = state.slot

/-- Every state writes nothing to itself. -/
private theorem Writes.refl (state : BeaconState preset fork) : Writes state state :=
  ⟨fun _ _ => rfl, rfl⟩

/-- The relation chains, since the slot and so the current epoch stay the same. -/
private theorem Writes.trans {first second third : BeaconState preset fork}
    (one : Writes first second) (two : Writes second third) : Writes first third := by
  have epoch : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, one.2]
  exact ⟨fun other apart => (two.1 other (epoch ▸ apart)).trans (one.1 other apart),
    two.2.trans one.2⟩

/-- A step that keeps the mixes and the slot writes no mix. -/
private theorem Writes.of_kept (kept : Kept state after) : Writes state after :=
  ⟨fun _ _ => by rw [kept.1], kept.2⟩

/-- A block writes at most the RANDAO mix of its epoch, at every fork. -/
theorem mixesKeptBut_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    MixesKeptBut (getCurrentEpoch state) state after := by
  suffices writes : Writes state after from writes.1
  have header : ∀ {state after : BeaconState preset fork},
      processBlockHeader state block = .ok after → Writes state after := fun ok =>
    Writes.of_kept ⟨(payloadInputs_processBlockHeader ok).randaoMixes,
      (payloadInputs_processBlockHeader ok).slot⟩
  have randao : ∀ {state after : BeaconState preset fork},
      processRandao config checks state block.body = .ok after → Writes state after := fun ok =>
    ⟨mixesKeptBut_processRandao ok, (frame_processRandao ok).slot⟩
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidStep : Writes state paid := by
      split at paidOk
      · exact Writes.of_kept ⟨(payloadInputs_processParentExecutionPayload paidOk).randaoMixes,
          (payloadInputs_processParentExecutionPayload paidOk).slot⟩
      · cases paidOk
        exact Writes.refl _
    have executedStep : Writes headed executed := by
      split at executedOk
      · exact Writes.of_kept ⟨randaoMixes_processBlockExecution executedOk,
          (frame_processBlockExecution executedOk).slot⟩
      · cases executedOk
        exact Writes.refl _
    have votedStep : Writes revealed voted := by
      split at votedOk
      · exact Writes.of_kept (Kept.of_payloadInputs (payloadInputs_processEth1Data votedOk))
      · cases votedOk
        exact Writes.refl _
    exact paidStep.trans <| (header headedOk).trans <| executedStep.trans <|
      (randao revealedOk).trans <| votedStep.trans <|
      (Writes.of_kept (kept_processOperations operatedOk)).trans
      (Writes.of_kept (Kept.of_payloadInputs (payloadInputs_processSyncAggregate synced)))
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (header headerOk).trans <| (randao randaoOk).trans <|
    (Writes.of_kept (Kept.of_payloadInputs (payloadInputs_processEth1Data eth1Ok))).trans
    (Writes.of_kept (kept_processOperations operationsOk))

/-! ## Committees -/

/-- A block keeps the committees of the previous and of the current epoch, at every fork.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem committeesKept_processBlock
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) {epoch : Epoch}
    (low : getPreviousEpoch state ≤ epoch) (high : epoch ≤ getCurrentEpoch state) :
    CommitteesKept epoch state after := by
  have previous := getPreviousEpoch_toNat state
  have lowNat := UInt64.le_iff_toNat_le.mp low
  -- The block writes at most the mix of the current epoch, which the seed never reads.
  exact CommitteesKept.of_activeKept apart
    ((activeKept_processBlock computed).mono
      (UInt64.le_trans high (getCurrentEpoch_le_activityFixedEpoch state)))
    (mixesKeptBut_processBlock computed) high (by omega)

/-- One slot keeps the committees of each epoch that both states see as recent, at every fork.

Such an epoch is at most the current epoch before the slot.

It is at least the previous epoch after it.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem committeesKept_advanceSlot
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : advanceSlot config checks state = .ok after) {epoch : Epoch}
    (low : getPreviousEpoch after ≤ epoch) (high : epoch ≤ getCurrentEpoch state) :
    CommitteesKept epoch state after := by
  have slots := advanceSlot_slot computed
  -- The slot never moves the current epoch back.
  have current : (getCurrentEpoch state).toNat ≤ (getCurrentEpoch after).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slots]
    exact Nat.div_le_div_right (Nat.le_succ _)
  have previous := getPreviousEpoch_toNat after
  have lowNat := UInt64.le_iff_toNat_le.mp low
  have highNat := UInt64.le_iff_toNat_le.mp high
  -- The slot writes at most the mix of the epoch it reaches, which the seed never reads.
  exact CommitteesKept.of_activeKept apart
    ((activeKept_advanceSlot computed).mono
      (UInt64.le_trans high (getCurrentEpoch_le_activityFixedEpoch state)))
    (mixesKeptBut_advanceSlot computed) (UInt64.le_iff_toNat_le.mpr (by omega)) (by omega)

end EthLib.Consensus
