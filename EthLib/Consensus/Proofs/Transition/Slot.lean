module

public import EthLib.Consensus.Proofs.Transition.Execution
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.SyncAggregate
public import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: a block keeps the slot of the state

No step of a block moves the slot of the state, at any fork.

A valid block runs on the state advanced to its slot, which is later than the slot before.

So the state after a valid block sits at the slot of the block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Withdrawals -/

theorem applyWithdrawal_slot {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : after.slot = state.slot := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · exact (frame_decreaseBalance computed).slot

theorem updateNextWithdrawalIndex_slot {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) :
    after.slot = state.slot := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · cases computed
    rfl

theorem updateNextWithdrawalValidatorIndex_slot {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    after.slot = state.slot := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    rfl

theorem updateNextWithdrawalBuilderIndex_slot {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    after.slot = state.slot := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl

theorem applyExpectedWithdrawals_slot {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    after.slot = state.slot := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, swept, sweptOk, last⟩ := computed
  have one : applied.slot = state.slot := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM_ok_invariant (fun s : BeaconState preset fork => s.slot = state.slot)
      (fun _ _ _ same step => (applyWithdrawal_slot step).trans same) rfl appliedOk
  have three : swept.slot = indexed.slot := by
    split at sweptOk
    · rw [updateNextWithdrawalBuilderIndex_slot sweptOk]
      split <;> rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at sweptOk
      rw [← sweptOk]
      split <;> rfl
  rw [updateNextWithdrawalValidatorIndex_slot last, three, updateNextWithdrawalIndex_slot indexedOk,
    one]

theorem processWithdrawals_slot {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    after.slot = state.slot := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact applyExpectedWithdrawals_slot applied
    · cases computed
      rfl
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact applyExpectedWithdrawals_slot applied

theorem processBlsToExecutionChange_slot {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, _, _, _, _, rfl⟩ := processBlsToExecutionChange_ok computed
  rfl

/-! ## The execution payload -/

theorem processExecutionPayload_slot {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  rfl

theorem processBlockExecution_slot {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processBlockExecution config engine state body bellatrix = .ok after) :
    after.slot = state.slot := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨withdrawn, withdrawnOk, paid⟩ := computed
    exact (processExecutionPayload_slot paid).trans (processWithdrawals_slot withdrawnOk)
  · split at computed
    · exact processExecutionPayload_slot computed
    · cases computed
      rfl

/-! ## Operations -/

theorem processAttestation_slot {attestation : Attestation preset fork}
    (computed : processAttestation config checks state attestation = .ok after) :
    after.slot = state.slot := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte] at computed
    unfold processAttestationAltair at computed
    split at computed
    · cases computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, raised⟩ := computed
    rw [(frame_increaseBalance raised).slot]
    unfold setEpochParticipation
    split <;> rfl
  · exact (frame_processAttestation (Nat.lt_of_not_le altair) computed).slot

theorem applyDeposit_slot {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    after.slot = state.slot := by
  by_cases altair : Fork.altair ≤ fork
  · unfold applyDeposit at computed
    split at computed
    · cases computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨valid, _, computed⟩ := computed
      split at computed
      · simp only [addValidatorToRegistry, altair, ↓reduceDIte] at computed
        unfold addValidatorToRegistryAltair at computed
        split at computed
        · cases computed
        simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
        obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
        rfl
      · cases computed
        rfl
    · exact (frame_increaseBalance (liftAccessor_ok.mp computed)).slot
  · exact (frame_applyDeposit (Nat.lt_of_not_le altair) computed).slot

theorem processDeposit_slot {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok computed
  exact (applyDeposit_slot applied :)

theorem processOperations_slot {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body = .ok after) :
    after.slot = state.slot := by
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have fold {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (keeps : ∀ s x s', step s x = .ok s' → s'.slot = s.slot) {items : List α}
      {start finish : BeaconState preset fork} (folded : items.foldlM step start = .ok finish) :
      finish.slot = start.slot :=
    foldlM_ok_invariant (fun s : BeaconState preset fork => s.slot = start.slot)
      (fun _ _ _ same ok => (keeps _ _ _ ok).trans same) rfl folded
  have last : after.slot = exited.slot := by
    split at changesOk
    · exact fold (fun _ _ _ ok => processBlsToExecutionChange_slot ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      rw [changesOk]
  rw [last, fold (fun _ _ _ ok => (frame_processVoluntaryExit ok).slot) exitsOk,
    fold (fun _ _ _ ok => processDeposit_slot ok) depositedOk,
    fold (fun _ _ _ ok => processAttestation_slot ok) attestedOk,
    fold (fun _ _ _ ok => (frame_processAttesterSlashing ok).slot) attestersOk,
    fold (fun _ _ _ ok => (frame_processProposerSlashing ok).slot) proposersOk]

/-! ## The sync aggregate -/

theorem processSyncAggregate_slot {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    after.slot = state.slot := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun s : BeaconState preset fork => s.slot = state.slot)
    (fun _ _ _ same step => ?_) rfl folded
  unfold applySyncReward at step
  split at step
  · simp only [bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨_, raised, _, _, paid⟩ := step
    rw [(frame_increaseBalance paid).slot, (frame_increaseBalance raised).slot, same]
  · rw [(frame_decreaseBalance (liftAccessor_ok.mp step)).slot, same]

/-! ## Blocks -/

/-- No block moves the slot of the state that it runs on. -/
theorem processBlock_slot {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    after.slot = state.slot := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processBlock, altair, ↓reduceDIte] at computed
    unfold processBlockAltair at computed
    by_cases electra : Fork.pectra ≤ fork
    · simp only [electra, ↓reduceDIte] at computed
      cases computed
    simp only [electra, ↓reduceDIte, bind_ok_iff] at computed
    obtain ⟨headed, headedOk, computed⟩ := computed
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    obtain ⟨executed, executedOk, revealed, revealedOk, voted, votedOk, operated, operatedOk,
        synced⟩ : ∃ executed, executed.slot = headed.slot ∧ ∃ revealed,
        processRandao config checks executed block.body = .ok revealed ∧ ∃ voted,
        processEth1Data _ revealed block.body = .ok voted ∧ ∃ operated,
        processOperations config checks voted block.body = .ok operated ∧
        processSyncAggregate config checks operated altair (block.body.syncAggregate altair) =
          .ok after := by
      by_cases bellatrix : Fork.bellatrix ≤ fork
      · simp only [bellatrix, ↓reduceDIte, bind_ok_iff] at computed
        obtain ⟨executed, executedOk, rest⟩ := computed
        exact ⟨executed, processBlockExecution_slot executedOk, rest⟩
      · simp only [bellatrix, ↓reduceDIte, bind_ok_iff, pure_bind] at computed
        exact ⟨headed, rfl, computed⟩
    rw [processSyncAggregate_slot synced, processOperations_slot operatedOk,
      (frame_processEth1Data votedOk).slot, (frame_processRandao revealedOk).slot, executedOk,
      (frame_processBlockHeader headedOk).slot]
  · simp only [processBlock, altair, ↓reduceDIte, bind_ok_iff] at computed
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operated⟩ := computed
    rw [processOperations_slot operated, (frame_processEth1Data votedOk).slot,
      (frame_processRandao revealedOk).slot, (frame_processBlockHeader headedOk).slot]

/-- A valid block runs on a state at an earlier slot, and leaves the state at its own slot. -/
theorem stateTransition_slot {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    state.slot < signed.message.slot ∧ after.slot = signed.message.slot := by
  obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok computed
  refine ⟨?_, (processBlock_slot blockOk).trans advancedSlot⟩
  unfold processSlots at slotsOk
  simp only [bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, later, _⟩ := slotsOk
  exact later

end EthLib.Consensus
