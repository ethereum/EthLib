module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Upgrade
public import EthLib.Consensus.Proofs.Transition.ForkBoundary

/-!
# Preservation of the deposit carry

Blocks before Gloas and the epoch operations other than pending deposits keep the carry.

The Electra upgrade initializes it to zero, and later upgrades before Gloas keep it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}
  {s t : BeaconState preset fork}

private abbrev Kept (s t : BeaconState preset fork) : Prop :=
  t.depositBalanceToConsume = s.depositBalanceToConsume

private theorem kept_fold {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x t, step s x = .ok t → Kept s t) {items : List α}
    (ok : items.foldlM step s = .ok t) : Kept s t :=
  foldlM_ok_invariant (Kept s) (fun _ _ _ before ok => (kept _ _ _ ok).trans before) rfl ok

private theorem kept_setValidatorAt {index : Nat} {v : Validator}
    (ok : s.setValidatorAt index v = .ok t) : Kept s t := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

private theorem kept_setValidator {index : ValidatorIndex} {v : Validator}
    (ok : s.setValidator index v = .ok t) : Kept s t :=
  kept_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem kept_setBalance {index : ValidatorIndex} {balance : Gwei}
    (ok : s.setBalance index balance = .ok t) : Kept s t := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  rfl

private theorem kept_increase {index : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s index amount = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  exact kept_setBalance set

private theorem kept_decrease {index : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s index amount = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  exact kept_setBalance set

private theorem kept_exitQueue {amount : Gwei} {epoch : Epoch}
    (ok : exitQueue config s amount = .ok (t, epoch)) : Kept s t := by
  unfold exitQueue at ok
  split at ok
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := ok
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, rfl, _⟩ := ok
    rfl

private theorem kept_exit {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) : Kept s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · rfl
  · exact (kept_setValidator set).trans (kept_exitQueue queue)

theorem depositCarry_processSlot (ok : processSlot s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok ok
  rfl

theorem depositCarry_processJustificationAndFinalization
    (ok : processJustificationAndFinalization s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]

theorem depositCarry_processInactivityUpdates {altair : .altair ≤ fork}
    (ok : processInactivityUpdates config s altair = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl

theorem depositCarry_processRewardsAndPenalties
    (ok : processRewardsAndPenalties config s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  rw [processRewardsAndPenalties_frame ok]

theorem depositCarry_processRegistryUpdates
    (ok : processRegistryUpdates config s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  unfold processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    refine kept_fold (fun _ _ _ ok => ?_) ok
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact kept_setValidatorAt set
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact kept_exit exited
    split at ok
    · exact kept_setValidatorAt (liftAccessor_ok.mp ok)
    · cases ok
      rfl
  simp only [bind_ok_iff] at ok
  obtain ⟨_, updated, activated⟩ := ok
  have one := kept_fold (fun _ _ _ ok => by
    simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, marked, ok⟩ := ok
    have same := kept_setValidatorAt marked
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact (kept_exit exited).trans same
    · cases ok
      exact same) updated
  exact (kept_fold (fun _ _ _ ok => by
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    exact kept_setValidator set) activated).trans one

theorem depositCarry_processSlashings (ok : processSlashings s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  unfold processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    refine kept_fold (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact kept_decrease lowered
      · cases ok; rfl
    · cases ok; rfl
  · refine kept_fold (fun _ _ _ ok => ?_) ok
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
        exact kept_decrease lowered
      · cases ok; rfl
    · cases ok; rfl

theorem depositCarry_processEth1DataReset {before : fork < .hegota}
    (ok : processEth1DataReset before s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> rfl

private theorem kept_passConsolidations {nextEpoch : Epoch} :
    ∀ {items : List PendingConsolidation} {s : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch s items = .ok result → Kept s result.1
  | [], _, _, ok => by cases ok; rfl
  | item :: rest, s, result, ok => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨⟨passed, read⟩, passedOk, ok⟩ := ok
      cases ok
      exact kept_passConsolidations (result := (passed, read)) passedOk
    split at ok
    · cases ok; rfl
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, lowered, _, raised, ⟨passed, read⟩, passedOk, ok⟩ := ok
    cases ok
    exact (kept_passConsolidations (result := (passed, read)) passedOk).trans
      ((kept_increase raised).trans (kept_decrease lowered))

theorem depositCarry_processPendingConsolidations {electra : .pectra ≤ fork}
    (ok : processPendingConsolidations s electra = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  unfold processPendingConsolidations at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact kept_passConsolidations ‹_›

theorem depositCarry_processEffectiveBalanceUpdates
    (ok : processEffectiveBalanceUpdates s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  refine kept_fold (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact kept_setValidatorAt set

theorem depositCarry_processSlashingsReset (ok : processSlashingsReset s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq ok
  rfl

theorem depositCarry_processRandaoMixesReset (ok : processRandaoMixesReset s = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq ok
  rfl

theorem depositCarry_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (ok : processHistoricalSummariesUpdate s capella = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  unfold processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals rfl

theorem depositCarry_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (ok : processSyncCommitteeUpdates s altair = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  unfold processSyncCommitteeUpdates at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals rfl

theorem depositCarry_processProposerLookahead {fulu : .fusaka ≤ fork}
    (ok : liftAccessor (processProposerLookahead s fulu) = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  rw [liftAccessor_ok] at ok
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, rfl⟩ := ok
  rfl

theorem depositCarry_processParticipationFlagUpdates (altair : .altair ≤ fork) :
    (processParticipationFlagUpdates s altair).depositBalanceToConsume =
      s.depositBalanceToConsume := rfl

private theorem kept_excess {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : Kept s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    have same := kept_setBalance set
    exact same
  · cases ok; rfl

private theorem depositCarry_upgradeToElectra {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    t.depositBalanceToConsume (by decide) = 0 := by
  simp only [upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := ok
  have one := kept_fold (fun _ _ _ ok => by
    simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
    exact (kept_setValidator validator).trans (kept_setBalance balance)) queued
  have two := kept_fold (fun _ _ _ ok => by
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · exact kept_excess (liftAccessor_ok.mp ok)
      · cases ok; rfl
    · cases ok; rfl) compounded
  exact congrFun (two.trans one) (by decide)

private theorem kept_upgradeNext {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) :
    (if h : .pectra ≤ t.val.fork then (t.val.state.depositBalanceToConsume h).toNat else 0) =
      (if h : .pectra ≤ s.fork then (s.state.depositBalanceToConsume h).toNat else 0) := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, _, rfl⟩ := ok
    rfl
  · subst ok; rfl
  · subst ok; rfl
  · subst ok; rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [show Fork.pectra ≤ .pectra from by decide, ↓reduceDIte]
    rw [depositCarry_upgradeToElectra upgraded]
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    rfl
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

theorem depositCarry_processUpgrades {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam) :
    (if h : .pectra ≤ t.fork then (t.state.depositBalanceToConsume h).toNat else 0) =
      (if h : .pectra ≤ s.fork then (s.state.depositBalanceToConsume h).toNat else 0) := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact (ih next rest early).trans (kept_upgradeNext nextOk
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early))
  | case2 s notDue => cases ok; rfl

private theorem kept_slash {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) : Kept s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, last, exited, -, -, marked, -, -, -, lowered, -, -,
    raised, paid, done⟩ := slashValidator_ok ok
  have cancelled : Kept last t := by
    subst done
    split <;> rfl
  exact cancelled.trans ((kept_increase paid).trans ((kept_increase raised).trans
    ((kept_decrease lowered).trans ((kept_setValidator marked).trans (kept_exit exited)))))

private theorem kept_proposer {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : Kept s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact kept_slash slashed

private theorem kept_attester {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : Kept s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => Kept s step.1) (fun _ _ _ previous ok => ?_)
    rfl folded
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact (kept_slash slashed).trans previous
  · cases ok
    exact previous

private theorem kept_attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : processAttestation config checks s parentSlot attestation = .ok t) : Kept s t := by
  unfold processAttestation at ok
  split at ok
  · unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have last : Kept raised t := by
      split at final
      · rw [recordPaymentWeight_eq final]
      · cases final; rfl
    have flags (current : Bool) (p : EpochParticipation preset fork) :
        Kept s (setEpochParticipation s current p) := by
      unfold setEpochParticipation
      split <;> rfl
    exact last.trans ((kept_increase raisedOk).trans (flags _ _))
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]

private theorem kept_addValidator {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s pubkey credentials amount = .ok t) : Kept s t := by
  unfold addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
    rfl
  split at ok <;> cases ok <;> rfl

private theorem kept_applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : applyDeposit config checks s pubkey credentials amount signature = .ok t) :
    Kept s t := by
  unfold applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, added, pushed⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        have same := kept_addValidator added
        exact same
      · cases ok; rfl
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      rfl
  · unfold applyPendingDeposit at ok
    split at ok
    · split at ok
      · cases ok; rfl
      simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · exact kept_addValidator ok
      · cases ok; rfl
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, ok⟩ := ok
      exact kept_increase ok

private theorem kept_withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : Kept s t := by
  have partialWithdrawal {s t : BeaconState preset fork} {index : ValidatorIndex} {v : Validator}
      {amount owed : Gwei}
      (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
      Kept s t := by
    simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
    obtain ⟨_, _, _, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
      obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
      simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churned
      obtain ⟨_, _, _, _, _, _, churned⟩ := churned
      cases churned
      rfl
    · cases ok; rfl
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; rfl)
    | exact kept_exit (liftAccessor_ok.mp ok)
    | exact partialWithdrawal ok

private theorem kept_consolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : Kept s t := by
  have switch {s t : BeaconState preset fork} {index : ValidatorIndex}
      (ok : switchToCompoundingValidator s electra index = .ok t) : Kept s t := by
    simp only [switchToCompoundingValidator, bind_ok_iff] at ok
    obtain ⟨_, _, _, set, queued⟩ := ok
    exact (kept_excess queued).trans (kept_setValidator set)
  have queue {s t : BeaconState preset fork} {sourceIndex targetIndex : ValidatorIndex}
      {source : Validator}
      (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
      Kept s t := by
    simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      pure, Except.pure] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, ok⟩ := ok
    cases ok
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    have same := kept_setValidator set
    exact same
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; rfl)
    | exact switch (liftAccessor_ok.mp ok)
    | exact queue ok

private theorem kept_operations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (early : fork < .glamsterdam)
    (ok : processOperations config checks s body parentSlot = .ok t) : Kept s t := by
  unfold processOperations at ok
  split at ok
  · exact False.elim (Nat.not_le_of_lt early (by assumption))
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have one := kept_fold (fun _ _ _ ok => kept_proposer ok) proposers
  have two := kept_fold (fun _ _ _ ok => kept_attester ok) attesters
  have three := kept_fold (fun _ _ _ ok => kept_attestation ok) attested
  have four := kept_fold (fun _ _ _ ok => by
    obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok ok
    have same := kept_applyDeposit applied
    exact same) deposits
  have five := kept_fold (fun _ _ _ ok => by
    unfold processVoluntaryExit at ok
    simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exit⟩ := ok
    exact kept_exit exit) exits
  have six : Kept exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact kept_fold (fun _ _ _ ok => by
        obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
        exact kept_setValidator set) changes
    · cases changes; rfl
  have seven : Kept changed t := by
    split at requests
    · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requests
      obtain ⟨_, deposited, _, withdrawn, consolidated⟩ := requests
      have first := kept_fold (fun a request _ ok => by
        obtain ⟨_, recorded⟩ := recordDepositRequestsStart_eq
          (state := a) (index := request.index)
        simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
          bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        rfl) deposited
      exact (kept_fold (fun _ _ _ ok => kept_consolidationRequest ok) consolidated).trans
        ((kept_fold (fun _ _ _ ok => kept_withdrawalRequest ok) withdrawn).trans first)
    · cases requests; rfl
  exact seven.trans (six.trans (five.trans (four.trans (three.trans (two.trans one)))))

private theorem kept_withdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (early : fork < .glamsterdam) (ok : processWithdrawals s capella payload = .ok t) :
    Kept s t := by
  have notGloas : ¬Fork.glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, _, _, _, applied⟩ := ok
  simp only [applyExpectedWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure] at applied
  obtain ⟨a, appliedOk, b, indexedOk, c, sweptOk, last⟩ := applied
  have one : Kept s a := kept_fold (step := applyWithdrawal)
    (fun _ _ _ ok => by rw [applyWithdrawal_eq ok])
    (by simpa only [applyWithdrawals, ← Array.foldlM_toList] using appliedOk)
  have two : Kept a b := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · obtain ⟨_, _, built⟩ := bind_ok_iff.mp indexedOk
      cases built
      rfl
    · cases indexedOk
      rfl
  have queued : Kept b c := by
    cases sweptOk
    split <;> rfl
  have three : Kept c t := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last <;> cases last
    rfl
  exact three.trans (queued.trans (two.trans one))

theorem depositCarry_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} (early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  have header {a b : BeaconState preset fork} (ok : processBlockHeader a block = .ok b) :
      Kept a b := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
    rfl
  have randao {a b : BeaconState preset fork}
      (ok : processRandao config checks a block.body = .ok b) : Kept a b := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
    rfl
  have vote {a b : BeaconState preset fork} {before : fork < .hegota}
      (ok : processEth1Data before a block.body = .ok b) : Kept a b := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
    rw [← rest]
  have execution {a b : BeaconState preset fork} {bellatrix : .bellatrix ≤ fork}
      (ok : processBlockExecution config checks engine a block.body bellatrix = .ok b) :
      Kept a b := by
    have payload {a b : BeaconState preset fork}
        {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
        (ok : processExecutionPayload config engine a block.body bellatrix = .ok b) :
        Kept a b := by
      obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    unfold processBlockExecution at ok
    split at ok
    · exact False.elim (Nat.not_le_of_lt early (by assumption))
    split at ok
    · obtain ⟨_, withdrawn, paid⟩ := bind_ok_iff.mp ok
      exact (payload paid).trans (kept_withdrawals early withdrawn)
    · dsimp only at ok
      split at ok
      · exact payload ok
      · cases ok; rfl
  unfold processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, a, headed, b, executed, c, revealed, d, voted,
      e, operated, synced⟩ := ok
    have paidSame : paid = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid
    have one : Kept a b := by
      split at executed
      · exact execution executed
      · cases executed; rfl
    have two : Kept c d := by
      split at voted
      · exact vote voted
      · cases voted; rfl
    have three : Kept e t := by
      unfold processSyncAggregate at synced
      simp only [bind_ok_iff, ← Array.foldlM_toList] at synced
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := synced
      refine kept_fold (fun _ _ _ ok => ?_) folded
      unfold applySyncReward at ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, raised, _, _, paid⟩ := ok
        exact (kept_increase paid).trans (kept_increase raised)
      · exact kept_decrease (liftAccessor_ok.mp ok)
    exact three.trans ((kept_operations early operated).trans
      (two.trans ((randao revealed).trans (one.trans (header headed)))))
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, headed, _, revealed, _, voted, operated⟩ := ok
    exact (kept_operations early operated).trans
      ((vote voted).trans ((randao revealed).trans (header headed)))

end EthLib.Consensus
