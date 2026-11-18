module

public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.EpochPending

/-!
# Pending consolidation sources and lifecycle

Every pending source remains in the validator registry along a run before Gloas.

Electra starts an empty queue, requests append existing indices, and processing drops a prefix.

With positive withdrawal delay, sources are distinct and keep their activation and exit ordering.

An assigned exit prevents a source from being queued twice, and slashing only delays withdrawal.

The queue is in the order of its sources' exits, so no pending source can withdraw yet.
-/

@[expose] public section
namespace EthLib.Consensus
open Base
variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def SamePendingQueue {f : Fork} (s t : BeaconState preset f) : Prop :=
  t.pendingConsolidations = s.pendingConsolidations

/-- A step keeps the pending consolidations and the earliest consolidation epoch.

Only a consolidation request, the pass of an epoch and the Electra upgrade write either. -/
private def QueueKept {f : Fork} (s t : BeaconState preset f) : Prop :=
  (t.pendingConsolidations, t.earliestConsolidationEpoch) =
    (s.pendingConsolidations, s.earliestConsolidationEpoch)

private theorem QueueKept.queue {f : Fork} {s t : BeaconState preset f} (kept : QueueKept s t) :
    SamePendingQueue s t :=
  congrArg Prod.fst kept

private theorem QueueKept.earliest {f : Fork} {s t : BeaconState preset f}
    (kept : QueueKept s t) : t.earliestConsolidationEpoch = s.earliestConsolidationEpoch :=
  congrArg Prod.snd kept

private theorem QueueKept.trans {f : Fork} {s t u : BeaconState preset f}
    (one : QueueKept s t) (two : QueueKept t u) : QueueKept s u :=
  Eq.trans two one

private theorem QueueKept.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → QueueKept a b)
    (ok : xs.foldlM step s = .ok t) : QueueKept s t :=
  foldlM_ok_invariant (QueueKept s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed)) rfl ok

private theorem QueueKept.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v : Validator} (ok : s.setValidatorAt i v = .ok t) : QueueKept s t := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

private theorem QueueKept.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v : Validator} (ok : s.setValidator i v = .ok t) :
    QueueKept s t :=
  setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem QueueKept.increase {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {amount : Gwei} (ok : increaseBalance s i amount = .ok t) :
    QueueKept s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem QueueKept.decrease {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {amount : Gwei} (ok : decreaseBalance s i amount = .ok t) :
    QueueKept s t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  rfl

private theorem QueueKept.addValidator {f : Fork} {s t : BeaconState preset f}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s pubkey credentials amount = .ok t) : QueueKept s t := by
  unfold addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
    rfl
  · split at ok <;> cases ok
    rfl

/-- Starting an exit writes one validator and the exit queue only. -/
private theorem initiateValidatorExit_kept {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} (ok : initiateValidatorExit config s index = .ok t) :
    t.balances = s.balances ∧ QueueKept s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact ⟨rfl, rfl⟩

/-- Starting an exit writes one validator and the exit queue only.

So it keeps the balances and the pending consolidations. -/
theorem initiateValidatorExit_balances_eq_and_pendingConsolidations_eq {f : Fork}
    {s t : BeaconState preset f} {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) :
    t.balances = s.balances ∧ t.pendingConsolidations = s.pendingConsolidations :=
  ⟨(initiateValidatorExit_kept ok).1, (initiateValidatorExit_kept ok).2.queue⟩

private theorem QueueKept.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) : QueueKept s t :=
  (initiateValidatorExit_kept ok).2

private theorem QueueKept.rewards {f : Fork} {s t : BeaconState preset f}
    (ok : processRewardsAndPenalties config s = .ok t) : QueueKept s t := by
  unfold QueueKept
  rw [processRewardsAndPenalties_frame ok]

private theorem QueueKept.slashings {f : Fork} {s t : BeaconState preset f}
    (ok : processSlashings s = .ok t) : QueueKept s t := by
  unfold QueueKept
  rw [processSlashings_frame ok]

private theorem QueueKept.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : QueueKept s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, middle, set, queued⟩ := ok
  apply (setValidator set).trans
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rfl
  · cases queued; rfl

theorem SamePendingQueue.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : SamePendingQueue s t :=
  (QueueKept.compounding ok).queue

/-- An epoch stage keeps the pending consolidations, unless it is the stage that processes them. -/
theorem EpochStage.Edge.samePendingQueue {f : Fork} {stage : EpochStage}
    {s t : BeaconState preset f} (edge : EpochStage.Edge config checks stage s t)
    (other : stage ≠ .pendingConsolidations) : SamePendingQueue s t := by
  cases stage
  case rewards => exact (QueueKept.rewards edge).queue
  case slashings => exact (QueueKept.slashings edge).queue
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits_pendingConsolidations edge
    · exact edge ▸ rfl
  case pendingConsolidations => exact absurd rfl other
  case registry => exact (processRegistryUpdates_kept edge).2
  case effectiveBalances =>
    show t.pendingConsolidations = s.pendingConsolidations
    rw [processEffectiveBalanceUpdates_frame edge]
  all_goals exact (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.1

variable {fork : Fork} {state after : BeaconState preset fork}
  {engine : ExecutionEngine preset fork}

namespace QueueKept

private theorem slash {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state i whistleblower = .ok after) :
    QueueKept state after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, read, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (exit exited).trans (setValidator set)
  have second : QueueKept marked last :=
    (show QueueKept marked { marked with slashings } from rfl).trans
      ((decrease lowered).trans ((increase raised).trans (increase paid)))
  apply (first.trans second).trans
  split <;> rfl

private theorem proposer {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    QueueKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slash slashed

private theorem slashIf {step next : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (ok : slashIfSlashable config step index = .ok next) : QueueKept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact slash slashed
  · cases ok; rfl

private theorem attester {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    QueueKept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step : BeaconState preset fork × Bool =>
    QueueKept state step.1)
    (fun _ _ _ prior ok => prior.trans (slashIf ok))
    (show QueueKept state (state, false).1 from rfl) folded

private theorem voluntary {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks state signed = .ok after) :
    QueueKept state after :=
  exit (processVoluntaryExit_initiates ok)

private theorem bls {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    QueueKept state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator set

private theorem deposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (ok : processDeposit config checks before state deposit = .ok after) :
    QueueKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨early, _⟩
  · rfl
  · rfl
  · exact (addValidator added :)
  · exact absurd electra (Nat.not_le_of_lt early)

private theorem depositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest state electra request = .ok after) :
    QueueKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  rfl

/-- A partial withdrawal writes the exit churn and the pending partial withdrawals only. -/
private theorem partialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config state electra index v amount owed = .ok after) :
    QueueKept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, final⟩ := churned
    cases final
    rfl
  · cases ok
    rfl

private theorem withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after) :
    QueueKept state after := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · rfl
  · exact exit exited
  · exact partialWithdrawal withdrawn

private theorem attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (electra : .pectra ≤ fork)
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    QueueKept state after := by
  unfold processAttestation at ok
  rw [dite_eq_left (show .altair ≤ fork from Nat.le_trans (by decide) electra)] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := ok
  have last : QueueKept raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]; rfl
    · cases final; rfl
  have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
      QueueKept state (setEpochParticipation state current participation) := by
    intro current participation
    unfold setEpochParticipation
    split <;> rfl
  exact (flagged _ _).trans ((increase raisedOk).trans last)

private theorem withdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (early : fork < .glamsterdam)
    (ok : processWithdrawals state capella payload = .ok after) :
    QueueKept state after := by
  unfold processWithdrawals at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, applied⟩ := ok
  apply applyExpectedWithdrawals_of_setters QueueKept (fun _ => rfl)
    (fun one two => one.trans two) (fun ok => by rw [applyWithdrawal_eq ok]; rfl)
    _ _ _ _ _ _ applied
  all_goals exact fun _ _ => rfl

private theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    QueueKept state after := by
  unfold processBlockExecution at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    apply (withdrawals early withdrawn).trans
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    rfl
  · dsimp only at ok
    split at ok
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    · cases ok; rfl

end QueueKept

namespace SamePendingQueue

theorem refl (s : BeaconState preset fork) : SamePendingQueue s s := rfl

theorem proposer {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.proposer ok).queue

theorem attester {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.attester ok).queue

theorem voluntary {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks state signed = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.voluntary ok).queue

theorem bls {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.bls ok).queue

theorem deposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (ok : processDeposit config checks before state deposit = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.deposit electra ok).queue

theorem depositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest state electra request = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.depositRequest ok).queue

theorem withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.withdrawalRequest ok).queue

theorem attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (electra : .pectra ≤ fork)
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.attestation electra ok).queue

theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    SamePendingQueue state after :=
  (QueueKept.blockExecution early ok).queue

end SamePendingQueue

/-- A property of the pending consolidation queue crosses an upgrade before Gloas.

It holds vacuously before Electra, and the Electra upgrade starts with an empty queue.

The Fulu upgrade must carry it. -/
private theorem upgradeNext_pending (P : ∀ {f : Fork}, BeaconState preset f → Prop)
    (vacuous : ∀ {f : Fork} (s : BeaconState preset f), f < .pectra → P s)
    (empty : ∀ t : BeaconState preset .pectra,
      (∀ electra, (t.pendingConsolidations electra).data.toList = []) → P t)
    (fulu : ∀ {s : BeaconState preset .pectra} {t : BeaconState preset .fusaka},
      upgradeToFulu config s = .ok t → P s → P t)
    {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : P pre.state) (ok : upgradeNext config checks pre = .ok post)
    (early : post.val.fork < .glamsterdam) : P post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, _, rfl⟩ := ok
    exact vacuous _ (show Fork.altair < .pectra by decide)
  · subst ok; exact vacuous _ (show Fork.bellatrix < .pectra by decide)
  · subst ok; exact vacuous _ (show Fork.shapella < .pectra by decide)
  · subst ok; exact vacuous _ (show Fork.dencun < .pectra by decide)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := upgraded
    have kept := QueueKept.fold (fun _ _ _ ok => by
      simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, b, balance, _, set, rfl⟩ := ok
      obtain ⟨_, rfl⟩ := setBalance_ok balance
      have same := QueueKept.setValidator set
      exact same) queued
    have kept' := QueueKept.fold (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · simp only [liftAccessor_ok, queueExcessActiveBalance, bind_ok_iff] at ok
          obtain ⟨_, _, ok⟩ := ok
          split at ok
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
            obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
            obtain ⟨_, rfl⟩ := setBalance_ok set
            rfl
          · cases ok; rfl
        · cases ok; rfl
      · cases ok; rfl) compounded
    have queue := (kept.trans kept').queue
    apply empty
    intro electra
    unfold SamePendingQueue at queue
    rw [queue]
    simp [carryFields, show ¬ Fork.pectra ≤ .dencun from by decide]
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact fulu upgraded holds
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.not_le_of_lt early (show Fork.glamsterdam ≤ .hegota from by decide))

/-- Every pending consolidation names a source inside the registry. -/
def PendingSources {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingConsolidations electra).data.toList,
    entry.sourceIndex.toNat < s.validators.data.size

/-- Each validator with an exit keeps its index, and its withdrawable epoch does not decrease.

A validator that is unslashed in the later state was unslashed before.

Its withdrawable epoch is then the same.

Only a slashing moves the withdrawable epoch of an exited validator, and it sets the flag. -/
private def WithdrawalKept {f g : Fork} (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.exitEpoch ≠ FAR_FUTURE_EPOCH →
    ∃ w : Validator, t.validators.data[i]? = some w ∧ v.withdrawableEpoch ≤ w.withdrawableEpoch ∧
      (w.slashed = false → v.slashed = false ∧ w.withdrawableEpoch = v.withdrawableEpoch)

/-- Each validator with an assigned exit keeps exactly its withdrawable epoch. -/
private def WithdrawalExact {f g : Fork} (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.exitEpoch ≠ FAR_FUTURE_EPOCH →
    ∃ w : Validator, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch

/-- Each validator without an assigned exit keeps its withdrawable epoch.

Otherwise it gets one after `bound`. -/
private def WithdrawalUnassigned {f g : Fork} (bound : Epoch) (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.exitEpoch = FAR_FUTURE_EPOCH →
    ∃ w : Validator, t.validators.data[i]? = some w ∧
      (w.withdrawableEpoch = v.withdrawableEpoch ∨ bound < w.withdrawableEpoch)

namespace WithdrawalKept

/-- A later state with the same validators keeps every withdrawable epoch. -/
private theorem of_data {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data := by rfl) : WithdrawalKept s t := by
  intro i v found _
  exact ⟨v, by rw [same]; exact found, UInt64.le_refl _, fun unslashed => ⟨unslashed, rfl⟩⟩

private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : WithdrawalKept s t) (two : WithdrawalKept t u)
    (life : RegistryLifecycle s t) : WithdrawalKept s u := by
  intro i v found assigned
  obtain ⟨w, middle, bound, exact⟩ := one i v found assigned
  obtain ⟨w', middle', kept⟩ := life.validators i v found
  have same : w' = w := Option.some.inj (middle'.symm.trans middle)
  subst w'
  obtain ⟨z, final, bound', exact'⟩ :=
    two i w middle (by rw [kept.exitEpoch assigned]; exact assigned)
  refine ⟨z, final, UInt64.le_trans bound bound', fun unslashed => ?_⟩
  obtain ⟨between, later⟩ := exact' unslashed
  obtain ⟨first, earlier⟩ := exact between
  exact ⟨first, later.trans earlier⟩

private theorem fold {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → WithdrawalKept a b)
    (life : ∀ a item b, step a item = .ok b → RegistryLifecycle a b)
    (ok : xs.foldlM step state = .ok after) : WithdrawalKept state after := by
  have both := foldlM_ok_invariant
    (fun s => WithdrawalKept state s ∧ RegistryLifecycle state s)
    (fun _ _ _ prior ok =>
      ⟨prior.1.trans (kept _ _ _ ok) prior.2, prior.2.trans (life _ _ _ ok)⟩)
    ⟨of_data, RegistryLifecycle.refl _⟩ ok
  exact both.1

/-- A write that keeps the withdrawable epoch and the slashed flag keeps the withdrawal. -/
private theorem kept_of_same {old v : Validator}
    (withdrawable : v.withdrawableEpoch = old.withdrawableEpoch) (flag : v.slashed = old.slashed)
    (_ : old.exitEpoch ≠ FAR_FUTURE_EPOCH) : old.withdrawableEpoch ≤ v.withdrawableEpoch ∧
      (v.slashed = false → old.slashed = false ∧ v.withdrawableEpoch = old.withdrawableEpoch) :=
  ⟨withdrawable ▸ UInt64.le_refl _, fun unslashed => ⟨flag ▸ unslashed, withdrawable⟩⟩

/-- A write at one position relates each old validator to the new one at its position.

The written validator is related to the old one by `kept`, and every other is kept. -/
private theorem setAt_transport (R : Validator → Validator → Prop) (refl : ∀ w, R w w)
    {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old) (set : state.setValidatorAt i v = .ok after)
    (kept : R old v) :
    ∀ (j : Nat) (w : Validator), state.validators.data[j]? = some w →
      ∃ w', after.validators.data[j]? = some w' ∧ R w w' := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro j w read
  by_cases same : j = i
  · subst j
    have eq : w = old := by simpa [Array.getElem?_eq_getElem inside, oldEq] using read.symm
    subst w
    refine ⟨v, ?_, kept⟩
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, inside]
  · refine ⟨w, ?_, refl w⟩
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same, Ne.symm same] using read

private theorem setAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old) (set : state.setValidatorAt i v = .ok after)
    (kept : old.exitEpoch ≠ FAR_FUTURE_EPOCH → old.withdrawableEpoch ≤ v.withdrawableEpoch ∧
      (v.slashed = false → old.slashed = false ∧ v.withdrawableEpoch = old.withdrawableEpoch)) :
    WithdrawalKept state after := fun j w read assigned => by
  obtain ⟨w', located, related⟩ := setAt_transport (fun a b => a.exitEpoch ≠ FAR_FUTURE_EPOCH →
      a.withdrawableEpoch ≤ b.withdrawableEpoch ∧
        (b.slashed = false → a.slashed = false ∧ b.withdrawableEpoch = a.withdrawableEpoch))
    (fun w => kept_of_same rfl rfl) found set kept j w read
  exact ⟨w', located, related assigned⟩

private theorem set {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old) (written : state.setValidator i v = .ok after)
    (kept : old.exitEpoch ≠ FAR_FUTURE_EPOCH → old.withdrawableEpoch ≤ v.withdrawableEpoch ∧
      (v.slashed = false → old.slashed = false ∧ v.withdrawableEpoch = old.withdrawableEpoch)) :
    WithdrawalKept state after :=
  setAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) kept

/-- A later state with the same validators keeps every withdrawable epoch exactly. -/
private theorem exact_of_data {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data := by rfl) : WithdrawalExact s t :=
  fun _ v found _ => ⟨v, by rw [same]; exact found, rfl⟩

private theorem exact_trans {f g h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} {u : BeaconState preset h} (one : WithdrawalExact s t)
    (two : WithdrawalExact t u) (life : RegistryLifecycle s t) : WithdrawalExact s u := by
  intro i v found assigned
  obtain ⟨w, middle, equal⟩ := one i v found assigned
  obtain ⟨w', middle', kept⟩ := life.validators i v found
  obtain rfl : w' = w := Option.some.inj (middle'.symm.trans middle)
  obtain ⟨z, final, equal'⟩ := two i w' middle (by rw [kept.exitEpoch assigned]; exact assigned)
  exact ⟨z, final, equal'.trans equal⟩

/-- A write that keeps the withdrawable epoch of an assigned exit keeps it exactly. -/
private theorem exact_setAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old) (set : state.setValidatorAt i v = .ok after)
    (kept : old.exitEpoch ≠ FAR_FUTURE_EPOCH → v.withdrawableEpoch = old.withdrawableEpoch) :
    WithdrawalExact state after := fun j w read assigned => by
  obtain ⟨w', located, related⟩ := setAt_transport (fun a b => a.exitEpoch ≠ FAR_FUTURE_EPOCH →
      b.withdrawableEpoch = a.withdrawableEpoch) (fun _ _ => rfl) found set kept j w read
  exact ⟨w', located, related assigned⟩

/-- Starting an exit writes an exit epoch only to a validator that has none.

So it keeps every assigned exit's withdrawable epoch, exactly. -/
private theorem exit_exact {i : ValidatorIndex}
    (ok : initiateValidatorExit config state i = .ok after) :
    WithdrawalKept state after ∧ WithdrawalExact state after := by
  obtain ⟨v, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, written⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact ⟨of_data, exact_of_data⟩
  · have same := (exitQueue_validators queue).1
    have read : getValidatorAt queued i.toNat = .ok v := by
      rw [← getValidator_eq_getValidatorAt]
      exact (getValidator_of_validators_eq same i).trans found
    rw [setValidator_eq_setValidatorAt] at written
    have life : RegistryLifecycle state queued := .of_data (congrArg (·.data) same)
    exact ⟨(of_data (congrArg (·.data) same)).trans
        (setAt read written (fun assigned => False.elim (assigned far))) life,
      exact_trans (exact_of_data (congrArg (·.data) same))
        (exact_setAt read written (fun assigned => False.elim (assigned far))) life⟩

private theorem exit {i : ValidatorIndex}
    (ok : initiateValidatorExit config state i = .ok after) : WithdrawalKept state after :=
  (exit_exact ok).1

private theorem increase {i : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance state i amount = .ok after) : WithdrawalKept state after :=
  of_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem slash {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state i whistleblower = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨exited, validator, withdrawal, marked, _, _, _, _, _, _, _, last, exitedOk,
    found, _, markedOk, _, _, _, lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  have same := (slashValidator_last (last := last) (after := after) (index := i)
    (by subst done; rfl)).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  exact (exit exitedOk).trans
    ((set found markedOk (fun _ => ⟨by
      rw [UInt64.max_def]
      split
      · assumption
      · exact UInt64.le_refl _, fun unslashed => nomatch unslashed⟩)).trans
      (of_data (congrArg (·.data) same))
      (.setValidator found markedOk ⟨fun _ => rfl, fun _ => rfl⟩))
    (registryLifecycle_initiateValidatorExit exitedOk)

/-- Effective-balance updates write only effective balances. -/
private theorem effectiveUpdates
    (ok : processEffectiveBalanceUpdates state = .ok after) : WithdrawalKept state after := by
  refine fold (fun _ _ _ ok => ?_) (fun _ _ _ ok => ?_) ok
  · simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, _, _, set⟩ := ok
    exact setAt found set (kept_of_same rfl rfl)
  · simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, _, _, set⟩ := ok
    exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩

/-- A switch to compounding credentials writes only the credentials and a balance. -/
private theorem compounding {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator state electra index = .ok after) :
    WithdrawalKept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, middle, written, queued⟩ := ok
  have rest : after.validators = middle.validators := by
    unfold queueExcessActiveBalance at queued
    simp only [bind_ok_iff] at queued
    obtain ⟨_, _, queued⟩ := queued
    split at queued
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
      obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
      obtain ⟨_, rfl⟩ := setBalance_ok set
      rfl
    · cases queued; rfl
  exact (set found written (kept_of_same rfl rfl)).trans
    (of_data (congrArg (·.data) rest))
    (.setValidator found written ⟨fun _ => rfl, fun _ => rfl⟩)

/-- A later state with the same validators keeps every unassigned withdrawable epoch. -/
private theorem unassigned_of_data {f g : Fork} {bound : Epoch} {s : BeaconState preset f}
    {t : BeaconState preset g} (same : t.validators.data = s.validators.data := by rfl) :
    WithdrawalUnassigned bound s t :=
  fun _ v found _ => ⟨v, by rw [same]; exact found, .inl rfl⟩

/-- An unassigned exit stays so or gets an exact one, so the two relations compose. -/
private theorem unassigned_trans {f g h : Fork} {bound : Epoch} {s : BeaconState preset f}
    {t : BeaconState preset g} {u : BeaconState preset h}
    (one : WithdrawalUnassigned bound s t) (exact : WithdrawalExact t u)
    (two : WithdrawalUnassigned bound t u) : WithdrawalUnassigned bound s u := by
  intro i v found far
  obtain ⟨w, middle, first⟩ := one i v found far
  by_cases still : w.exitEpoch = FAR_FUTURE_EPOCH
  · obtain ⟨z, final, second⟩ := two i w middle still
    refine ⟨z, final, ?_⟩
    rcases second with same | late
    · rw [same]
      exact first
    · exact .inr late
  · obtain ⟨z, final, same⟩ := exact i w middle still
    exact ⟨z, final, by rw [same]; exact first⟩

/-- Take a write that keeps an unassigned exit's withdrawable epoch, or sets it after `bound`.

It relates every validator so. -/
private theorem unassigned_setAt {bound : Epoch} {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old) (set : state.setValidatorAt i v = .ok after)
    (kept : old.exitEpoch = FAR_FUTURE_EPOCH →
      v.withdrawableEpoch = old.withdrawableEpoch ∨ bound < v.withdrawableEpoch) :
    WithdrawalUnassigned bound state after := fun j w read far => by
  obtain ⟨w', located, related⟩ := setAt_transport (fun a b => a.exitEpoch = FAR_FUTURE_EPOCH →
      b.withdrawableEpoch = a.withdrawableEpoch ∨ bound < b.withdrawableEpoch)
    (fun _ _ => .inl rfl) found set kept j w read
  exact ⟨w', located, related far⟩

/-- Starting an exit sets the withdrawable epoch after the current epoch.

The exit queue gives an exit after the current epoch, and the delay only adds to it. -/
private theorem unassigned_exit {i : ValidatorIndex}
    (ok : initiateValidatorExit config state i = .ok after) :
    WithdrawalUnassigned (getCurrentEpoch state) state after := by
  obtain ⟨v, found, ⟨_, rfl⟩ | ⟨_, queued, exitEpoch, withdrawable, queue, summed, written⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact unassigned_of_data
  · have same := (exitQueue_validators queue).1
    have read : getValidatorAt queued i.toNat = .ok v := by
      rw [← getValidator_eq_getValidatorAt]
      exact (getValidator_of_validators_eq same i).trans found
    rw [setValidator_eq_setValidatorAt] at written
    have late : getCurrentEpoch state < withdrawable := by
      have after := exitQueue_lt queue
      have sum := (Uint64.addChecked_ok_iff.mp summed).2
      rw [UInt64.lt_iff_toNat_lt]
      omega
    intro j w read' far
    have moved : queued.validators.data[j]? = some w := by rw [same]; exact read'
    obtain ⟨w', located, related⟩ := setAt_transport (fun a b =>
        a.exitEpoch = FAR_FUTURE_EPOCH →
          b.withdrawableEpoch = a.withdrawableEpoch ∨ getCurrentEpoch state < b.withdrawableEpoch)
      (fun _ _ => .inl rfl) read written (fun _ => .inr late) j w moved
    exact ⟨w', located, related far⟩

/-- From Electra, registry updates write eligibility, activation and new exits only.

So they keep every assigned exit's withdrawable epoch exactly.

They give each newly assigned exit a withdrawable epoch after the current epoch. -/
private theorem registry_unassigned (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config state = .ok after) :
    WithdrawalKept state after ∧ WithdrawalExact state after ∧
      WithdrawalUnassigned (getCurrentEpoch state) state after := by
  unfold processRegistryUpdates at ok
  rw [ite_eq_left electra] at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  have all := foldlM_ok_invariant
    (fun s => WithdrawalKept state s ∧ WithdrawalExact state s ∧ RegistryLifecycle state s ∧
      WithdrawalUnassigned (getCurrentEpoch state) state s ∧ s.slot = state.slot)
    (fun a _ b prior ok => by
      have life : RegistryLifecycle a b := by
        simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨v, found, ok⟩ := ok
        split at ok
        · simp only [bind_ok_iff, liftAccessor_ok] at ok
          obtain ⟨_, _, written⟩ := ok
          exact .setValidatorAt found written ⟨fun _ => rfl, fun _ => rfl⟩
        split at ok
        · simp only [bind_ok_iff, liftAccessor_ok] at ok
          obtain ⟨_, _, exited⟩ := ok
          exact registryLifecycle_initiateValidatorExit exited
        split at ok
        · rename_i eligible
          exact .setValidatorAt found (liftAccessor_ok.mp ok)
            ⟨fun h => False.elim (h (activationEpoch_of_isEligibleForActivation eligible)),
              fun _ => rfl⟩
        · cases ok; exact .refl _
      have step : WithdrawalKept a b ∧ WithdrawalExact a b ∧
          WithdrawalUnassigned (getCurrentEpoch a) a b := by
        simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨v, found, ok⟩ := ok
        split at ok
        · simp only [bind_ok_iff, liftAccessor_ok] at ok
          obtain ⟨_, _, written⟩ := ok
          exact ⟨setAt found written (kept_of_same rfl rfl), exact_setAt found written fun _ => rfl,
            unassigned_setAt found written fun _ => .inl rfl⟩
        split at ok
        · simp only [bind_ok_iff, liftAccessor_ok] at ok
          obtain ⟨_, _, exited⟩ := ok
          exact ⟨(exit_exact exited).1, (exit_exact exited).2, unassigned_exit exited⟩
        split at ok
        · exact ⟨setAt found (liftAccessor_ok.mp ok) (kept_of_same rfl rfl),
            exact_setAt found (liftAccessor_ok.mp ok) fun _ => rfl,
            unassigned_setAt found (liftAccessor_ok.mp ok) fun _ => .inl rfl⟩
        · cases ok; exact ⟨of_data, exact_of_data, unassigned_of_data⟩
      have slot : b.slot = a.slot := (frame_updateRegistryEntryElectra ok).slot
      have epoch : getCurrentEpoch a = getCurrentEpoch state := by
        simp only [getCurrentEpoch, prior.2.2.2.2]
      exact ⟨prior.1.trans step.1 prior.2.2.1, exact_trans prior.2.1 step.2.1 prior.2.2.1,
        prior.2.2.1.trans life, unassigned_trans prior.2.2.2.1 step.2.1 (epoch ▸ step.2.2),
        slot.trans prior.2.2.2.2⟩)
    ⟨of_data, exact_of_data, RegistryLifecycle.refl _, unassigned_of_data, rfl⟩ ok
  exact ⟨all.1, all.2.1, all.2.2.2.1⟩

/-- From Electra, registry updates write eligibility, activation and new exits only.

So they also keep every assigned exit's withdrawable epoch exactly. -/
private theorem registry_exact (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config state = .ok after) :
    WithdrawalKept state after ∧ WithdrawalExact state after :=
  ⟨(registry_unassigned electra ok).1, (registry_unassigned electra ok).2.1⟩

/-- From Electra, registry updates write eligibility, activation and new exits only. -/
private theorem registry (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config state = .ok after) : WithdrawalKept state after :=
  (registry_exact electra ok).1

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v) :
    WithdrawalKept state after := by
  intro i old found _
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  refine ⟨old, ?_, UInt64.le_refl _, fun unslashed => ⟨unslashed, rfl⟩⟩
  simpa [added, Array.getElem?_push, Nat.ne_of_lt inside] using found

private theorem deposit {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks state deposit = .ok after) :
    WithdrawalKept state after := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · exact of_data
  · exact increase ok
  · exact append (addValidatorToRegistry_validators_eq_push ok)

/-- Pending deposits raise balances or append validators. -/
private theorem pendingDeposits {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks state electra = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  exact (fold (fun _ _ _ => deposit) (fun _ _ _ => registryLifecycle_applyPendingDeposit)
    folded :)

/-- A proposer slashing moves the withdrawable epoch only of the validator it slashes. -/
private theorem proposer {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    WithdrawalKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slash slashed

/-- An attester slashing moves the withdrawable epochs only of the validators it slashes. -/
private theorem attester {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    WithdrawalKept state after := by
  have one {a b : BeaconState preset fork × Bool} {i : ValidatorIndex}
      (ok : slashIfSlashable config a i = .ok b) : WithdrawalKept a.1 b.1 := by
    obtain ⟨s, flag⟩ := a
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, slashed, rfl⟩ := ok
      exact slash slashed
    · cases ok; exact of_data
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  have both := foldlM_ok_invariant
    (fun s : BeaconState preset fork × Bool =>
      WithdrawalKept state s.1 ∧ RegistryLifecycle state s.1)
    (fun _ _ _ prior ok => ⟨prior.1.trans (one ok) prior.2,
      prior.2.trans (registryLifecycle_slashIfSlashable ok)⟩)
    (show WithdrawalKept state (state, false).1 ∧ RegistryLifecycle state (state, false).1 from
      ⟨of_data, .refl _⟩) folded
  exact both.1

/-- A change to execution credentials writes only the credentials. -/
private theorem bls {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨_, found, _, _, _, written⟩ := processBlsToExecutionChange_ok ok
  exact set found written (kept_of_same rfl rfl)

/-- An attestation keeps the validators. -/
private theorem attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    WithdrawalKept state after :=
  of_data (congrArg (·.data) (processAttestation_registry ok).1)

/-- From Electra, a block deposit keeps every validator or appends one. -/
private theorem blockDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (ok : processDeposit config checks before state deposit = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨early, _⟩
  · exact of_data
  · exact of_data
  · have data := addValidatorToRegistry_validators_eq_push added
    exact append data
  · exact absurd electra (Nat.not_le_of_lt early)

/-- A deposit request appends a pending deposit only. -/
private theorem depositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest state electra request = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact of_data

/-- A withdrawal request starts an exit or queues a partial withdrawal. -/
private theorem withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after) :
    WithdrawalKept state after := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · exact of_data
  · exact exit exited
  · exact of_data (congrArg (·.data) (requestPartialWithdrawal_kept withdrawn).1)

/-- The execution part of a block keeps the validators, so it keeps their withdrawal epochs. -/
private theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    WithdrawalKept state after :=
  of_data (congrArg (·.data) (processBlockExecution_validators ok))

end WithdrawalKept

/-- A queued consolidation assigns its source an exit epoch and pushes one entry on the queue.

That exit epoch is after the current epoch.

The exit epoch comes from the consolidation churn.

It is assigned when the withdrawal delay is positive.

The reason is that the withdrawal epoch is the exit epoch plus that delay, and fits in 64 bits.

The source is written over the state the churn returns, and the new state keeps its validators. -/
theorem queueConsolidation_queued {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    ∃ (churned written : BeaconState preset fork) (epoch withdrawal : Epoch),
      computeConsolidationEpochAndUpdateChurn config state electra source.effectiveBalance =
        .ok (churned, epoch) ∧
      epoch ≠ FAR_FUTURE_EPOCH ∧ getCurrentEpoch state < epoch ∧
      withdrawal.toNat = epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ∧
      churned.setValidator sourceIndex
        { source with exitEpoch := epoch, withdrawableEpoch := withdrawal } = .ok written ∧
      after.validators = written.validators ∧
      (after.pendingConsolidations electra).data.toList =
        (state.pendingConsolidations electra).data.toList ++ [⟨sourceIndex, targetIndex⟩] := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churnOk, withdrawal, added, written, set, pending, appended, final⟩ :=
    ok
  cases final
  have churnQueue : churned.pendingConsolidations = state.pendingConsolidations := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churnOk
    obtain ⟨_, _, _, _, _, _, final⟩ := churnOk
    cases final; rfl
  have queueEq := (QueueKept.setValidator set).queue
  change written.pendingConsolidations = churned.pendingConsolidations at queueEq
  have sum := (Uint64.addChecked_ok_iff.mp added).2
  -- The churn places the exit no earlier than the first epoch an exit may take.
  have later : getCurrentEpoch state < epoch := by
    apply UInt64.lt_iff_toNat_lt.mpr
    cases first : computeActivationExitEpoch preset (getCurrentEpoch state) with
    | error =>
      simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError, bind,
        Except.bind] at churnOk
    | ok firstEpoch =>
      have early := UInt64.le_iff_toNat_le.mp
        (computeConsolidationEpochAndUpdateChurn_first first churnOk).1
      have firstEq := (computeActivationExitEpoch_ok_iff.mp first).2
      omega
  refine ⟨churned, written, epoch, withdrawal, churnOk, fun eq => ?_, later, sum, set, rfl, ?_⟩
  · have bound := withdrawal.toNat_lt
    rw [eq] at sum
    have farNat : FAR_FUTURE_EPOCH.toNat = 18446744073709551615 := rfl
    rw [farNat] at sum
    omega
  · show pending.data.toList = _
    rw [appendWithinLimit_data appended, queueEq, churnQueue, Array.toList_push]

/-- The steps of an epoch keep the earliest consolidation epoch.

Only a consolidation request writes it, and no epoch stage makes one. -/
private theorem earliestLaws : EpochFrameLaws (preset := preset) (fork := fork)
    fun s t => t.earliestConsolidationEpoch = s.earliestConsolidationEpoch where
  refl _ := rfl
  trans one two := two.trans one
  setValidatorAt set _ _ _ _ _ := (QueueKept.setValidatorAt set).earliest
  increaseBalance ok := (QueueKept.increase ok).earliest
  decreaseBalance ok := (QueueKept.decrease ok).earliest
  initiateValidatorExit ok := (QueueKept.exit ok).earliest
  addValidatorToRegistry ok _ := (QueueKept.addValidator ok).earliest
  eth1DataVotes _ _ := rfl
  inactivityScores _ _ := rfl
  slashings _ _ := rfl
  randaoMixes _ _ := rfl
  historicalRoots _ _ := rfl
  historicalSummaries _ _ := rfl
  participationRecords _ := rfl
  pendingConsolidations _ _ := rfl
  syncCommittees _ _ _ := rfl
  proposerLookahead _ _ := rfl
  ptcWindow _ _ := rfl
  pendingDeposits _ _ _ := rfl

/-- Every epoch stage keeps the earliest consolidation epoch.

The laws above cover all stages but four, which keep it by their shape. -/
private theorem EpochStage.Edge.consolidationEarliest {stage : EpochStage}
    {s t : BeaconState preset fork} (edge : EpochStage.Edge config checks stage s t) :
    t.earliestConsolidationEpoch = s.earliestConsolidationEpoch := by
  cases stage
  case justification =>
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok edge
    · rfl
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      rw [← rest]
  case payments =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
    · exact edge ▸ rfl
  case participation =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · subst edge
      rfl
    · exact earliestLaws.processParticipationRecordUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact earliestLaws.processPendingDeposits edge
    · exact edge ▸ rfl
  all_goals
    exact earliestLaws.epochEdge (by exact ⟨nofun, nofun, nofun, nofun⟩)
      (EpochStage.action_cases.mpr edge)

/-- From Electra, an epoch stage other than the pending consolidations is a frame of the queue.

It keeps the queue and the earliest consolidation epoch, every withdrawal and the slot. -/
private theorem EpochStage.Edge.withdrawalFrame {stage : EpochStage}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    (edge : EpochStage.Edge config checks stage s t) (other : stage ≠ .pendingConsolidations) :
    QueueKept s t ∧ RegistryLifecycle s t ∧ WithdrawalKept s t ∧ t.slot = s.slot := by
  have queue : QueueKept s t := by
    have same : t.pendingConsolidations = s.pendingConsolidations := edge.samePendingQueue other
    unfold QueueKept
    rw [same, edge.consolidationEarliest]
  cases stage
  case registry =>
    exact ⟨queue, registryLifecycle_processRegistryUpdates edge,
      WithdrawalKept.registry electra edge, (frame_processRegistryUpdates edge).slot⟩
  case pendingDeposits =>
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact ⟨queue, registryLifecycle_processPendingDeposits edge,
      WithdrawalKept.pendingDeposits edge, (frame_processPendingDeposits edge).slot⟩
  case pendingConsolidations => exact absurd rfl other
  case effectiveBalances =>
    exact ⟨queue, registryLifecycle_processEffectiveBalanceUpdates edge,
      WithdrawalKept.effectiveUpdates edge, (frame_processEffectiveBalanceUpdates edge).slot⟩
  case rewards =>
    have same := congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)
    exact ⟨queue, .of_data same, .of_data same, (frame_processRewardsAndPenalties edge).slot⟩
  case slashings =>
    have same := congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)
    exact ⟨queue, .of_data same, .of_data same, (frame_processSlashings edge).slot⟩
  all_goals
    have kept := edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    have same := congrArg (·.data) kept.1
    exact ⟨queue, .of_data same, .of_data same, kept.2.2.2.2⟩

/-- Distinct pending sources have activated and keep their assigned exit and withdrawal delay. -/
def PendingConsolidationInvariant (config : Config) {fork : Fork}
    (s : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork,
    ((s.pendingConsolidations electra).data.toList.map (·.sourceIndex)).Nodup ∧
    ∀ c ∈ (s.pendingConsolidations electra).data.toList,
      ∃ v : Validator, s.validators.data[c.sourceIndex.toNat]? = some v ∧
        v.activationEpoch ≤ getCurrentEpoch s ∧
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat ∧ v.exitEpoch ≠ FAR_FUTURE_EPOCH

namespace PendingConsolidationInvariant

private theorem kept {s t : BeaconState preset fork}
    (holds : PendingConsolidationInvariant config s) (queue : SamePendingQueue s t)
    (life : RegistryLifecycle s t) (withdrawal : WithdrawalKept s t)
    (epoch : getCurrentEpoch s ≤ getCurrentEpoch t) :
    PendingConsolidationInvariant config t := by
  intro electra
  obtain ⟨unique, sources⟩ := holds electra
  unfold SamePendingQueue at queue
  rw [queue]
  refine ⟨unique, fun c mem => ?_⟩
  obtain ⟨v, found, active, ordered, assigned⟩ := sources c mem
  obtain ⟨w, read, later⟩ := life.validators c.sourceIndex.toNat v found
  obtain ⟨w', read', bound, -⟩ := withdrawal c.sourceIndex.toNat v found assigned
  have eq : w' = w := Option.some.inj (read'.symm.trans read)
  subst w'
  refine ⟨w, read, ?_, ?_, ?_⟩
  · by_cases activation : v.activationEpoch = FAR_FUTURE_EPOCH
    · have bound := w.activationEpoch.toNat_lt
      have active' := UInt64.le_trans active epoch
      simp only [UInt64.le_iff_toNat_le, activation, FAR_FUTURE_EPOCH] at active' ⊢
      have farNat : (UInt64.ofNat (2 ^ 64 - 1)).toNat = 18446744073709551615 := rfl
      rw [farNat] at active'
      omega
    · rw [later.activationEpoch activation]
      exact UInt64.le_trans active epoch
  · rw [later.exitEpoch assigned]
    exact Nat.le_trans ordered (UInt64.le_iff_toNat_le.mp bound)
  · rw [later.exitEpoch assigned]; exact assigned

theorem pendingDeposits (holds : PendingConsolidationInvariant config state)
    {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks state electra = .ok after) :
    PendingConsolidationInvariant config after := by
  apply holds.kept (processPendingDeposits_pendingConsolidations ok)
    (registryLifecycle_processPendingDeposits ok) (WithdrawalKept.pendingDeposits ok)
  rw [show getCurrentEpoch after = getCurrentEpoch state from
    congrArg (computeEpochAtSlot preset) (frame_processPendingDeposits ok).slot]
  exact UInt64.le_refl _

private theorem consolidations (holds : PendingConsolidationInvariant config state)
    {electra : .pectra ≤ fork}
    (ok : processPendingConsolidations state electra = .ok after) :
    PendingConsolidationInvariant config after := by
  intro witness
  obtain ⟨unique, sources⟩ := holds witness
  obtain ⟨result, _, _, queue⟩ := processPendingConsolidations_pass ok
  have registry := (processPendingConsolidations_kept ok).1
  have epoch : getCurrentEpoch after = getCurrentEpoch state :=
    congrArg (computeEpochAtSlot preset) (frame_processPendingConsolidations ok).slot
  rw [queue, registry, epoch]
  refine ⟨?_, fun c mem => sources c (List.mem_of_mem_drop mem)⟩
  exact unique.sublist ((List.drop_sublist _ _).map _)

private theorem framed (holds : PendingConsolidationInvariant config state)
    (queue : SamePendingQueue state after) (life : RegistryLifecycle state after)
    (withdrawal : WithdrawalKept state after) (slot : after.slot = state.slot) :
    PendingConsolidationInvariant config after := by
  apply holds.kept queue life withdrawal
  rw [show getCurrentEpoch after = getCurrentEpoch state from
    congrArg (computeEpochAtSlot preset) slot]
  exact UInt64.le_refl _

/-- Every epoch stage keeps the invariant.

Pending consolidations have their own lemma above.

Every other stage keeps the queue, the slot and each withdrawal of a validator with an exit. -/
theorem _root_.EthLib.Consensus.EpochStage.Edge.pendingConsolidationInvariant
    {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t)
    (holds : PendingConsolidationInvariant config s) : PendingConsolidationInvariant config t := by
  by_cases electra : .pectra ≤ fork
  case neg => exact fun witness => absurd witness electra
  by_cases pass : stage = .pendingConsolidations
  · subst pass
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact holds.consolidations edge
  · obtain ⟨queue, life, withdrawal, slot⟩ := edge.withdrawalFrame electra pass
    exact holds.framed queue.queue life withdrawal slot

end PendingConsolidationInvariant

/-- From Electra, the pending consolidations are in the order of their sources' exits.

It adds four facts about each source to `PendingConsolidationInvariant`.

- It exits no earlier than each source before it in the queue.
- It exits no later than the earliest consolidation epoch.
- If it is unslashed, it can withdraw exactly the withdrawal delay after its exit.
- It can withdraw only after the epoch `bound`. -/
def PendingConsolidationsOrdered (config : Config) (bound : Nat) {fork : Fork}
    (s : BeaconState preset fork) : Prop :=
  PendingConsolidationInvariant config s ∧ ∀ electra : .pectra ≤ fork,
    (s.pendingConsolidations electra).data.toList.Pairwise (fun a b => ∀ v w,
      s.validators.data[a.sourceIndex.toNat]? = some v →
        s.validators.data[b.sourceIndex.toNat]? = some w → v.exitEpoch ≤ w.exitEpoch) ∧
    ∀ c ∈ (s.pendingConsolidations electra).data.toList, ∀ v,
      s.validators.data[c.sourceIndex.toNat]? = some v →
        v.exitEpoch ≤ s.earliestConsolidationEpoch electra ∧
        (v.slashed = false → v.withdrawableEpoch.toNat ≤
          v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) ∧
        bound < v.withdrawableEpoch.toNat

/-- Each pending consolidation names two different validators. -/
private def PendingApart {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ c ∈ (s.pendingConsolidations electra).data.toList,
    c.sourceIndex ≠ c.targetIndex

/-- A step that keeps the queue keeps it apart. -/
private theorem PendingApart.kept {f : Fork} {s t : BeaconState preset f}
    (queue : QueueKept s t) (holds : PendingApart s) : PendingApart t := by
  intro electra c member
  have same : t.pendingConsolidations = s.pendingConsolidations := queue.queue
  rw [same] at member
  exact holds electra c member

/-- The pass of an epoch keeps a suffix of the queue, so it keeps it apart. -/
private theorem PendingApart.consolidations {electra : .pectra ≤ fork}
    (holds : PendingApart state) (ok : processPendingConsolidations state electra = .ok after) :
    PendingApart after := by
  intro witness c member
  obtain ⟨_, passed, -, queue⟩ := processPendingConsolidations_pass ok
  rw [queue, passPendingConsolidations_drop passed] at member
  exact holds witness c ((List.dropWhile_suffix _).subset member)

/-- Two different pubkeys found in the registry convert to two different indices. -/
private theorem consolidationRequest_indices_ne {state : BeaconState preset fork}
    {p q : Cryptography.Bls.BLSPubkey} {a b : Fin state.validators.data.size} {i j : UInt64}
    (differ : ¬(p == q) = true)
    (foundA : findValidatorByPubkey state p = some a)
    (foundB : findValidatorByPubkey state q = some b)
    (convertedA : liftAccessor (liftArith (Uint64.ofNatChecked (a : Nat))) =
      (Except.ok i : Except TransitionError UInt64))
    (convertedB : liftAccessor (liftArith (Uint64.ofNatChecked (b : Nat))) =
      (Except.ok j : Except TransitionError UInt64)) :
    i ≠ j := by
  intro same
  subst same
  have indexA :=
    (Uint64.ofNatChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp convertedA))).2
  have indexB :=
    (Uint64.ofNatChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp convertedB))).2
  obtain rfl : a = b := Fin.ext (indexA.symm.trans indexB)
  unfold findValidatorByPubkey at foundA foundB
  have keyA := (Array.findFinIdx?_eq_some_iff.mp foundA).1
  have keyB := (Array.findFinIdx?_eq_some_iff.mp foundB).1
  simp only [beq_iff_eq] at keyA keyB differ
  exact differ (keyA.symm.trans keyB)

namespace PendingConsolidationsOrdered

variable {bound : Nat}

private theorem mono {lower : Nat} (holds : PendingConsolidationsOrdered config bound state)
    (le : lower ≤ bound) : PendingConsolidationsOrdered config lower state :=
  ⟨holds.1, fun electra => ⟨(holds.2 electra).1, fun c mem v found =>
    have ⟨opened, exact, late⟩ := (holds.2 electra).2 c mem v found
    ⟨opened, exact, Nat.lt_of_le_of_lt le late⟩⟩⟩

/-- A step keeps the order when it keeps the queue, the earliest epoch and every withdrawal. -/
private theorem kept {s t : BeaconState preset fork}
    (holds : PendingConsolidationsOrdered config bound s) (queue : QueueKept s t)
    (life : RegistryLifecycle s t) (withdrawal : WithdrawalKept s t)
    (epoch : getCurrentEpoch s ≤ getCurrentEpoch t) :
    PendingConsolidationsOrdered config bound t := by
  refine ⟨holds.1.kept queue.queue life withdrawal epoch, fun electra => ?_⟩
  obtain ⟨sorted, sources⟩ := holds.2 electra
  -- A queued source keeps its exit, and its withdrawal moves only if it is slashed.
  have later : ∀ c ∈ (s.pendingConsolidations electra).data.toList, ∀ w,
      t.validators.data[c.sourceIndex.toNat]? = some w → ∃ v,
        s.validators.data[c.sourceIndex.toNat]? = some v ∧ w.exitEpoch = v.exitEpoch ∧
        v.withdrawableEpoch ≤ w.withdrawableEpoch ∧
        (w.slashed = false → v.slashed = false ∧ w.withdrawableEpoch = v.withdrawableEpoch) := by
    intro c mem w now
    obtain ⟨v, found, -, -, far⟩ := (holds.1 electra).2 c mem
    obtain ⟨_, read, life'⟩ := life.validators _ v found
    obtain ⟨_, read', grown, same⟩ := withdrawal _ v found far
    obtain rfl := Option.some.inj (read.symm.trans now)
    obtain rfl := Option.some.inj (read'.symm.trans now)
    exact ⟨v, found, life'.exitEpoch far, grown, same⟩
  have sameQueue : t.pendingConsolidations = s.pendingConsolidations := queue.queue
  rw [sameQueue]
  refine ⟨sorted.imp_of_mem fun memA memB order v' w' readA readB => ?_,
    fun c mem w now => ?_⟩
  · obtain ⟨v, foundA, exitA, -⟩ := later _ memA v' readA
    obtain ⟨w, foundB, exitB, -⟩ := later _ memB w' readB
    rw [exitA, exitB]
    exact order v w foundA foundB
  · obtain ⟨v, found, exit, grown, same⟩ := later c mem w now
    obtain ⟨opened, exact, late⟩ := sources c mem v found
    have grownNat := UInt64.le_iff_toNat_le.mp grown
    refine ⟨?_, fun unslashed => ?_, by omega⟩
    · rw [exit, queue.earliest]
      exact opened
    · obtain ⟨before, equal⟩ := same unslashed
      rw [equal, exit]
      exact exact before

/-- A step at one slot keeps the order at the current epoch, under the conditions of `kept`. -/
private theorem framed
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch state).toNat state)
    (queue : QueueKept state after) (life : RegistryLifecycle state after)
    (withdrawal : WithdrawalKept state after) (slot : after.slot = state.slot) :
    PendingConsolidationsOrdered config (getCurrentEpoch after).toNat after := by
  have epoch : getCurrentEpoch after = getCurrentEpoch state :=
    congrArg (computeEpochAtSlot preset) slot
  rw [epoch]
  exact holds.kept queue life withdrawal (by rw [epoch]; exact UInt64.le_refl _)

/-- The pass of an epoch leaves only sources that withdraw after the next epoch.

It stops at an unslashed source that cannot withdraw in the next epoch.

Each later source exits no earlier, so it withdraws no earlier. -/
private theorem consolidations {electra : .pectra ≤ fork}
    (holds : PendingConsolidationsOrdered config bound state)
    (ok : processPendingConsolidations state electra = .ok after) :
    PendingConsolidationsOrdered config (max bound (getCurrentEpoch state + 1).toNat) after := by
  refine ⟨holds.1.consolidations ok, fun witness => ?_⟩
  obtain ⟨sorted, sources⟩ := holds.2 witness
  have queued := (holds.1 witness).2
  obtain ⟨result, passed, -, queue⟩ := processPendingConsolidations_pass ok
  have earliest : after.earliestConsolidationEpoch = state.earliestConsolidationEpoch :=
    earliestLaws.processPendingConsolidations ok
  rw [queue, passPendingConsolidations_drop passed, (processPendingConsolidations_kept ok).1,
    earliest]
  let stops := fun consolidation : PendingConsolidation =>
    state.validators.data[consolidation.sourceIndex.toNat]?.any fun source =>
      source.slashed || source.withdrawableEpoch ≤ getCurrentEpoch state + 1
  have suffix := List.dropWhile_suffix (l := (state.pendingConsolidations witness).data.toList)
    stops
  refine ⟨sorted.sublist suffix.sublist, fun c mem v found => ?_⟩
  have inQueue := suffix.subset mem
  obtain ⟨opened, exact, late⟩ := sources c inQueue v found
  refine ⟨opened, exact, Nat.max_lt.mpr ⟨late, ?_⟩⟩
  -- The first source left is unslashed and withdraws after the next epoch.
  obtain ⟨head, tail, split⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem mem)
  have stopped := List.head?_dropWhile_not stops (state.pendingConsolidations witness).data.toList
  rw [split] at stopped
  simp only [List.head?_cons] at stopped
  have headQueued := suffix.subset (split ▸ List.mem_cons_self)
  obtain ⟨u, foundHead, -, -, -⟩ := queued head headQueued
  obtain ⟨-, exactHead, -⟩ := sources head headQueued u foundHead
  simp only [stops, foundHead, Option.any_some, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    UInt64.not_le] at stopped
  have waits := UInt64.lt_iff_toNat_lt.mp stopped.2
  -- A later source exits no earlier than the first one.
  have ordered := sorted.sublist suffix.sublist
  rw [split, List.pairwise_cons] at ordered
  rw [split] at mem
  rcases List.mem_cons.mp mem with rfl | inTail
  · obtain rfl := Option.some.inj (found.symm.trans foundHead)
    exact waits
  · have exitOrder := UInt64.le_iff_toNat_le.mp (ordered.1 c inTail u v foundHead found)
    obtain ⟨w, read, -, delayed, -⟩ := queued c inQueue
    obtain rfl := Option.some.inj (read.symm.trans found)
    have := exactHead stopped.1
    omega

/-- A consolidation request appends its source, which exits at the new earliest epoch.

That exit is no earlier than any queued exit, and the source withdraws after the current epoch. -/
private theorem queue {electra : .pectra ≤ fork} {sourceIndex targetIndex : ValidatorIndex}
    {source : Validator}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch state).toNat state)
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (active : source.activationEpoch ≤ getCurrentEpoch state)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    PendingConsolidationsOrdered config (getCurrentEpoch after).toNat after ∧
      (PendingApart state → sourceIndex ≠ targetIndex → PendingApart after) := by
  have frame := frame_queueConsolidation found ok
  have sameEpoch : getCurrentEpoch after = getCurrentEpoch state :=
    congrArg (computeEpochAtSlot preset) frame.slot
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churnOk, withdrawal, added, written, set, pending, appended, final⟩ :=
    ok
  cases final
  have data := appendWithinLimit_data appended
  obtain ⟨churnEarliest, churnRegistry, -⟩ :=
    computeConsolidationEpochAndUpdateChurn_earliest churnOk
  -- The churn call opens no earlier than the queue, and no earlier than the first exit epoch.
  obtain ⟨first, firstOk⟩ : ∃ first,
      computeActivationExitEpoch preset (getCurrentEpoch state) = .ok first := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith,
      mapError_ok_iff] at churnOk
    obtain ⟨first, firstOk, -⟩ := churnOk
    exact ⟨first, firstOk⟩
  obtain ⟨firstLe, earliestLe⟩ := computeConsolidationEpochAndUpdateChurn_first firstOk churnOk
  have firstNat := (computeActivationExitEpoch_ok_iff.mp firstOk).2
  have firstLeNat := UInt64.le_iff_toNat_le.mp firstLe
  have churnQueue : churned.pendingConsolidations = state.pendingConsolidations := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churnOk
    obtain ⟨_, _, _, _, _, _, final⟩ := churnOk
    cases final; rfl
  have writtenKept := QueueKept.setValidator set
  have queueEq := writtenKept.queue
  change written.pendingConsolidations = churned.pendingConsolidations at queueEq
  have sum := (Uint64.addChecked_ok_iff.mp added).2
  simp only at sum
  have assigned : epoch ≠ FAR_FUTURE_EPOCH := by
    intro eq
    have bound := withdrawal.toNat_lt
    rw [eq] at sum
    have farNat : FAR_FUTURE_EPOCH.toNat = 18446744073709551615 := rfl
    rw [farNat] at sum
    omega
  have newRead : written.validators.data[sourceIndex.toNat]? =
      some { source with exitEpoch := epoch, withdrawableEpoch := withdrawal } :=
    getValidator_eq_ok_iff.mp (getValidator_setValidator_self set)
  -- Each queued source has an exit, so it is not the new source and keeps its validator.
  have unchanged : ∀ witness : .pectra ≤ fork,
      ∀ c ∈ (state.pendingConsolidations witness).data.toList,
        written.validators.data[c.sourceIndex.toNat]? =
          state.validators.data[c.sourceIndex.toNat]? := by
    intro witness c mem
    have distinct : c.sourceIndex ≠ sourceIndex := by
      intro eq
      obtain ⟨v, read, -, -, assignedOld⟩ := (holds.1 witness).2 c mem
      rw [eq, found] at read
      cases read
      exact assignedOld far
    have same := (getValidator_setValidator_of_ne set distinct).trans
      (getValidator_of_validators_eq churnRegistry c.sourceIndex)
    exact Option.ext fun v => by rw [← getValidator_eq_ok_iff, ← getValidator_eq_ok_iff, same]
  refine ⟨⟨fun witness => ?_, fun witness => ?_⟩, fun apart distinct witness c member => ?_⟩
  · obtain ⟨unique, sources⟩ := holds.1 witness
    have absent : sourceIndex ∉ ((state.pendingConsolidations witness).data.toList.map
        (·.sourceIndex)) := by
      intro mem
      obtain ⟨c, mem, eq⟩ := List.mem_map.mp mem
      obtain ⟨v, read, _, _, assigned⟩ := sources c mem
      rw [eq, found] at read
      cases read
      exact assigned far
    change (pending.data.toList.map (·.sourceIndex)).Nodup ∧ _
    rw [data, queueEq, churnQueue, Array.toList_push]
    refine ⟨?_, ?_⟩
    · simpa [List.map_append, List.nodup_append, unique] using absent
    · intro c mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with mem | rfl
      · obtain ⟨v, read, activation, ordered, assigned⟩ := sources c mem
        refine ⟨v, by rw [unchanged witness c mem]; exact read, ?_, ordered, assigned⟩
        change v.activationEpoch ≤ getCurrentEpoch written
        rw [show getCurrentEpoch written = getCurrentEpoch state from sameEpoch]
        exact activation
      · refine ⟨_, newRead, ?_, Nat.le_of_eq sum.symm, assigned⟩
        change source.activationEpoch ≤ getCurrentEpoch written
        rw [show getCurrentEpoch written = getCurrentEpoch state from sameEpoch]
        exact active
  · obtain ⟨sorted, sources⟩ := holds.2 witness
    have newEarliest : written.earliestConsolidationEpoch witness = epoch :=
      (congrFun writtenKept.earliest witness).trans churnEarliest
    rw [sameEpoch]
    change (pending.data.toList.Pairwise fun a b => ∀ v w,
        written.validators.data[a.sourceIndex.toNat]? = some v →
          written.validators.data[b.sourceIndex.toNat]? = some w → v.exitEpoch ≤ w.exitEpoch) ∧
      ∀ c ∈ pending.data.toList, ∀ v, written.validators.data[c.sourceIndex.toNat]? = some v →
        v.exitEpoch ≤ written.earliestConsolidationEpoch witness ∧ _ ∧ _
    rw [data, queueEq, churnQueue, Array.toList_push, newEarliest, List.pairwise_append]
    refine ⟨⟨sorted.imp_of_mem fun memA memB order v w readA readB =>
        order v w (by rwa [unchanged witness _ memA] at readA)
          (by rwa [unchanged witness _ memB] at readB),
      List.pairwise_singleton _ _, fun a memA b memB v w readA readB => ?_⟩,
      fun c mem v read => ?_⟩
    · rw [List.mem_singleton.mp memB, newRead, Option.some.injEq] at readB
      subst readB
      rw [unchanged witness a memA] at readA
      exact UInt64.le_trans (sources a memA v readA).1 earliestLe
    · rcases List.mem_append.mp mem with mem | mem
      · rw [unchanged witness c mem] at read
        obtain ⟨opened, exact, late⟩ := sources c mem v read
        exact ⟨UInt64.le_trans opened earliestLe, exact, late⟩
      · rw [List.mem_singleton.mp mem, newRead, Option.some.injEq] at read
        subst read
        refine ⟨UInt64.le_refl _, fun _ => ?_, ?_⟩ <;> simp only <;> omega
  · -- The queue gains only the new pair.
    change c ∈ pending.data.toList at member
    rw [data, queueEq, churnQueue, Array.toList_push] at member
    rcases List.mem_append.mp member with member | member
    · exact apart witness c member
    · rw [List.mem_singleton.mp member]
      exact distinct

private theorem request {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch state).toNat state ∧
      PendingApart state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processConsolidationRequest config state electra request = .ok after) :
    PendingConsolidationsOrdered config (getCurrentEpoch after).toNat after ∧
      PendingApart after := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact holds)
    | exact ⟨holds.1.framed (QueueKept.compounding (liftAccessor_ok.mp ok))
        (registryLifecycle_switchToCompoundingValidator (liftAccessor_ok.mp ok))
        (WithdrawalKept.compounding (liftAccessor_ok.mp ok))
        (frame_switchToCompoundingValidator (liftAccessor_ok.mp ok)).slot,
        holds.2.kept (QueueKept.compounding (liftAccessor_ok.mp ok))⟩
    | (have queued := holds.1.queue (getElem?_toNat_of_ofNatChecked (by assumption))
          (by clear ok; simp_all [isActiveValidator]) (by clear ok; simp_all) delay ok
       -- The request names two different pubkeys, so two different indices.
       exact ⟨queued.1, queued.2 holds.2
         (consolidationRequest_indices_ne (by assumption) (by assumption) (by assumption)
           (by assumption) (by assumption))⟩)

/-- Every epoch stage keeps the order for a fixed bound. -/
private theorem stage {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t)
    (holds : PendingConsolidationsOrdered config bound s) :
    PendingConsolidationsOrdered config bound t := by
  by_cases electra : .pectra ≤ fork
  case neg =>
    exact ⟨fun witness => absurd witness electra, fun witness => absurd witness electra⟩
  by_cases pass : stage = .pendingConsolidations
  · subst pass
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact (holds.consolidations edge).mono (Nat.le_max_left _ _)
  · obtain ⟨queue, life, withdrawal, slot⟩ := edge.withdrawalFrame electra pass
    exact holds.kept queue life withdrawal (by
      rw [show getCurrentEpoch t = getCurrentEpoch s from
        congrArg (computeEpochAtSlot preset) slot]
      exact UInt64.le_refl _)

/-- An epoch moves the bound from the current epoch to the next one.

The bound holds up to the pass of the pending consolidations, which raises it. -/
private theorem epoch
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch state).toNat state ∧
      PendingApart state)
    (ok : processEpoch config checks state = .ok after) :
    PendingConsolidationsOrdered config (getCurrentEpoch state + 1).toNat after ∧
      PendingApart after := by
  by_cases electra : .pectra ≤ fork
  case neg =>
    exact ⟨⟨fun witness => absurd witness electra, fun witness => absurd witness electra⟩,
      fun witness => absurd witness electra⟩
  -- Before the pass the bound is the current epoch, and after it the next one.
  let Before (rest : List EpochStage) (a : BeaconState preset fork) : Prop :=
    a.slot = state.slot ∧
      (.pendingConsolidations ∈ rest →
        PendingConsolidationsOrdered config (getCurrentEpoch state).toNat a) ∧
      (.pendingConsolidations ∉ rest →
        PendingConsolidationsOrdered config (getCurrentEpoch state + 1).toNat a) ∧
      PendingApart a
  have done : Before [] after := by
    refine (processEpoch_trace ok).induction_on Before
      ⟨rfl, fun _ => holds.1, fun absent =>
        absurd (by simp [EpochStage.epochStages, EpochStage.prefixStages]) absent, holds.2⟩ ?_
    intro k rest a b computed ⟨slot, before, after, apart⟩
    have edge := EpochStage.action_cases.mp computed
    by_cases pass : k = .pendingConsolidations
    · subst pass
      simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
      refine ⟨(frame_processPendingConsolidations edge).slot.trans slot, ?_⟩
      have raised := (before List.mem_cons_self).consolidations edge
      rw [show getCurrentEpoch a = getCurrentEpoch state from
        congrArg (computeEpochAtSlot preset) slot] at raised
      exact ⟨fun _ => raised.mono (Nat.le_max_left _ _),
        fun _ => raised.mono (Nat.le_max_right _ _), apart.consolidations edge⟩
    · have same : (EpochStage.pendingConsolidations ∈ k :: rest) ↔
          .pendingConsolidations ∈ rest := by
        simp only [List.mem_cons, Ne.symm pass, false_or]
      exact ⟨(edge.withdrawalFrame electra pass).2.2.2.trans slot,
        fun present => (before (same.mpr present)).stage edge,
        fun absent => (after (mt same.mp absent)).stage edge,
        apart.kept (edge.withdrawalFrame electra pass).1⟩
  exact ⟨done.2.2.1 List.not_mem_nil, done.2.2.2⟩

private theorem executionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch state).toNat state ∧
      PendingApart state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processExecutionRequests config state body electra = .ok after) :
    PendingConsolidationsOrdered config (getCurrentEpoch after).toNat after ∧
      PendingApart after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  let Held (a : BeaconState preset fork) : Prop :=
    PendingConsolidationsOrdered config (getCurrentEpoch a).toNat a ∧ PendingApart a
  have first := foldlM_ok_invariant Held (fun _ _ _ h ok => ⟨h.1.framed
    (QueueKept.depositRequest ok) (registryLifecycle_processDepositRequest ok)
    (WithdrawalKept.depositRequest ok) (frame_processDepositRequest ok).slot,
    h.2.kept (QueueKept.depositRequest ok)⟩) holds deposits
  have second := foldlM_ok_invariant Held (fun _ _ _ h ok => ⟨h.1.framed
    (QueueKept.withdrawalRequest ok) (registryLifecycle_processWithdrawalRequest ok)
    (WithdrawalKept.withdrawalRequest ok) (frame_processWithdrawalRequest ok).slot,
    h.2.kept (QueueKept.withdrawalRequest ok)⟩) first withdrawals
  exact foldlM_ok_invariant Held (fun _ _ _ h ok => request h delay ok) second consolidations

/-- A block keeps the invariant and keeps the queue apart, step by step of the block.

A block frame does not carry the queue, so each step reads its own queue lemma. -/
private theorem block (early : fork < .glamsterdam)
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch state).toNat state ∧
      PendingApart state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) :
    PendingConsolidationsOrdered config (getCurrentEpoch after).toNat after ∧
      PendingApart after := by
  by_cases electra : .pectra ≤ fork
  case neg =>
    exact ⟨⟨fun witness => absurd witness electra, fun witness => absurd witness electra⟩,
      fun witness => absurd witness electra⟩
  have noGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt early
  let Held (a : BeaconState preset fork) : Prop :=
    PendingConsolidationsOrdered config (getCurrentEpoch a).toNat a ∧ PendingApart a
  let Kept (a b : BeaconState preset fork) : Prop := Held a → Held b
  have trans {a b c : BeaconState preset fork} (one : Kept a b) (two : Kept b c) : Kept a c :=
    two ∘ one
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : Kept state input :=
    OperationsInput.step_of Kept (fun _ => id) trans (fun gloas _ => absurd gloas noGloas)
      (fun headed => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed; exact id)
      (fun _ executed h => ⟨h.1.framed (QueueKept.blockExecution early executed)
        (.of_data (congrArg (·.data) (processBlockExecution_validators executed)))
        (WithdrawalKept.blockExecution executed)
        (frame_processBlockExecution executed).slot,
        h.2.kept (QueueKept.blockExecution early executed)⟩)
      (fun revealed => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        exact id)
      (fun _ voted h => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        rw [← rest] at h
        exact h)
      started
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of Kept (fun _ => id) trans
      (fun deposited h => ⟨h.1.framed (QueueKept.deposit electra deposited)
        (registryLifecycle_processDeposit deposited) (WithdrawalKept.blockDeposit electra deposited)
        (frame_processDeposit deposited).slot, h.2.kept (QueueKept.deposit electra deposited)⟩)
      (fun exited h => ⟨h.1.framed (QueueKept.voluntary exited)
        (registryLifecycle_processVoluntaryExit exited)
        (WithdrawalKept.exit (processVoluntaryExit_initiates exited))
        (frame_processVoluntaryExit exited).slot, h.2.kept (QueueKept.voluntary exited)⟩)
      (fun changed h => ⟨h.1.framed (QueueKept.bls changed)
        (registryLifecycle_processBlsToExecutionChange changed) (WithdrawalKept.bls changed)
        (frame_processBlsToExecutionChange changed).slot, h.2.kept (QueueKept.bls changed)⟩)
      (fun requested h => executionRequests h delay requested)
      (fun {_ _ gloas} _ => absurd gloas noGloas) operated
  have tail : Kept last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact fun h => ⟨h.1.framed rfl (.of_data rfl) .of_data rfl, h.2.kept rfl⟩
    · cases synced
      exact id
  have p := foldlM_ok_invariant Held (fun _ _ _ h ok => ⟨h.1.framed (QueueKept.proposer ok)
    (registryLifecycle_processProposerSlashing ok) (WithdrawalKept.proposer ok)
    (frame_processProposerSlashing ok).slot, h.2.kept (QueueKept.proposer ok)⟩)
    (head holds) proposersOk
  have a := foldlM_ok_invariant Held (fun _ _ _ h ok => ⟨h.1.framed (QueueKept.attester ok)
    (registryLifecycle_processAttesterSlashing ok) (WithdrawalKept.attester ok)
    (frame_processAttesterSlashing ok).slot, h.2.kept (QueueKept.attester ok)⟩) p slashingsOk
  have att := foldlM_ok_invariant Held (fun _ _ _ h ok => ⟨h.1.framed
    (QueueKept.attestation electra ok) (registryLifecycle_processAttestation ok)
    (WithdrawalKept.attestation ok) (frame_processAttestation ok).slot,
    h.2.kept (QueueKept.attestation electra ok)⟩) a attestedOk
  exact tail (rest att)

/-- A slot keeps the order at the current epoch, and an epoch boundary moves the bound.

The epoch boundary is the only case where the current epoch grows, by exactly one. -/
private theorem advance
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch state).toNat state ∧
      PendingApart state)
    (ok : advanceSlot config checks state = .ok after) :
    PendingConsolidationsOrdered config (getCurrentEpoch after).toNat after ∧
      PendingApart after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : PendingConsolidationsOrdered config (getCurrentEpoch cached).toNat cached ∧
      PendingApart cached := by
    rw [cachedEq]; exact holds
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by rw [cachedEq]; rfl
  have bounded := next.toNat_lt
  have slotEpoch := getCurrentEpoch_toNat state
  have nextEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  simp only at nextEpoch
  have below := Nat.div_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have second : ∃ bound, PendingConsolidationsOrdered config bound epoched ∧
      epoched.slot = state.slot ∧
      (getCurrentEpoch { epoched with slot := next }).toNat ≤ bound ∧ PendingApart epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · rename_i last
      refine ⟨_, (epoch first epochedOk).1, ?_, ?_, (epoch first epochedOk).2⟩
      · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
        have same : justified.slot = cached.slot := by
          obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
          · rfl
          · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
            rw [← rest]
        exact frame.slot.trans (same.trans (by rw [cachedEq]))
      · have divides : preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
          rw [← sum]
          exact Nat.dvd_of_mod_eq_zero (by simpa using congrArg UInt64.toNat last)
        rw [nextEpoch, sum, Nat.succ_div_of_dvd divides, cachedEpoch, UInt64.toNat_add,
          slotEpoch]
        simp only [UInt64.toNat_one]
        omega
    · rename_i last
      cases epochedOk
      refine ⟨_, first.1, by rw [cachedEq], ?_, first.2⟩
      have apart : ¬ preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := fun divides =>
        last (by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_mod, sum]
          simpa using Nat.mod_eq_zero_of_dvd divides)
      rw [nextEpoch, sum, Nat.succ_div_of_not_dvd apart, cachedEpoch, slotEpoch]
      exact Nat.le_refl _
  obtain ⟨bound, held, slot, le, apart⟩ := second
  refine ⟨(held.kept (t := { epoched with slot := next }) rfl (.of_data rfl)
    (WithdrawalKept.of_data rfl) ?_).mono le, apart.kept rfl⟩
  apply UInt64.le_iff_toNat_le.mpr
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  simp only [slot, sum]
  exact Nat.div_le_div_right (Nat.le_succ _)

private theorem upgrade {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : PendingConsolidationsOrdered config bound pre.state ∧ PendingApart pre.state)
    (ok : upgradeNext config checks pre = .ok post)
    (early : post.val.fork < .glamsterdam) :
    PendingConsolidationsOrdered config bound post.val.state ∧ PendingApart post.val.state :=
  upgradeNext_pending (P := fun s => PendingConsolidationsOrdered config bound s ∧ PendingApart s)
    (fun _ before => ⟨⟨fun electra => absurd electra (Nat.not_le_of_lt before),
      fun electra => absurd electra (Nat.not_le_of_lt before)⟩,
      fun electra => absurd electra (Nat.not_le_of_lt before)⟩)
    (fun _ empty => ⟨⟨fun electra => by simp [empty electra],
      fun electra => by simp [empty electra]⟩, fun electra => by simp [empty electra]⟩)
    (fun upgraded holds => by
      simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
      obtain ⟨_, _, rfl⟩ := upgraded
      refine ⟨⟨fun electra => ?_, fun electra => ?_⟩, fun electra => ?_⟩
      · simpa [carryFields, carryList, carryRooted, getCurrentEpoch] using
          holds.1.1 (show Fork.pectra ≤ .pectra from Nat.le_refl _)
      · simpa [carryFields, carryList, carryRooted] using
          holds.1.2 (show Fork.pectra ≤ .pectra from Nat.le_refl _)
      · simpa [carryFields, carryList, carryRooted] using
          holds.2 (show Fork.pectra ≤ .pectra from Nat.le_refl _))
    holds ok early

private theorem step {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam)
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state ∧
      PendingApart x.state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    PendingConsolidationsOrdered config (getCurrentEpoch y.state).toNat y.state ∧
      PendingApart y.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have initial := advance holds slotOk
    have rest := processUpgrades_induction
      (property := fun post => post.fork < .glamsterdam →
        PendingConsolidationsOrdered config (getCurrentEpoch advanced).toNat post.state ∧
          PendingApart post.state)
      (fun {pre post} h ok early => upgrade (h (Nat.lt_trans post.property early)) ok early)
      (fun _ => initial) upgrades
    rw [show getCurrentEpoch y.state = getCurrentEpoch advanced from
      congrArg (computeEpochAtSlot preset) (processUpgrades_slot upgrades)]
    exact rest early
  | block engine signed due ok => exact block early holds delay (applySignedBlock_ok ok).2.1

end PendingConsolidationsOrdered

/-- An epoch stage keeps the order of the pending consolidations at the current epoch.

So the state before each stage of an epoch has it, up to the pass that moves the bound. -/
theorem EpochStage.Edge.pendingConsolidationsOrdered {stage : EpochStage}
    {s t : BeaconState preset fork} (edge : EpochStage.Edge config checks stage s t)
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s) :
    PendingConsolidationsOrdered config (getCurrentEpoch t).toNat t := by
  by_cases electra : .pectra ≤ fork
  case neg =>
    exact ⟨fun witness => absurd witness electra, fun witness => absurd witness electra⟩
  have slot : t.slot = s.slot := by
    by_cases pass : stage = .pendingConsolidations
    · subst pass
      simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
      exact (frame_processPendingConsolidations edge).slot
    · exact (edge.withdrawalFrame electra pass).2.2.2
  rw [show getCurrentEpoch t = getCurrentEpoch s from congrArg (computeEpochAtSlot preset) slot]
  exact holds.stage edge

/-- From genesis and before Gloas, the pending consolidations of a run are ordered.

Each names two different validators. -/
private theorem Run.pendingConsolidationsOrdered_apart {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state ∧
      PendingApart x.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    have before := (initializeBeaconStateFromEth1_invariant ok).1
    have notElectra : ¬ Fork.pectra ≤ _ := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
    exact ⟨⟨fun electra => absurd electra notElectra, fun electra => absurd electra notElectra⟩,
      fun electra => absurd electra notElectra⟩
  | snoc pre step ih =>
    exact PendingConsolidationsOrdered.step step early
      (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)) delay

/-- From genesis and before Gloas, the pending consolidations of a run are ordered.

So no pending source can withdraw at the current epoch, whether it is slashed or not. -/
theorem Run.pendingConsolidationsOrdered {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state :=
  (run.pendingConsolidationsOrdered_apart genesis early delay).1

/-- From genesis and before Gloas, each pending consolidation of a run has two validators.

Its source is not its target.

A request with equal keys switches credentials instead.

Different keys name different indices. -/
theorem Run.pendingConsolidations_apart {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ electra : .pectra ≤ x.fork, ∀ c ∈ (x.state.pendingConsolidations electra).data.toList,
      c.sourceIndex ≠ c.targetIndex :=
  (run.pendingConsolidationsOrdered_apart genesis early delay).2

/-- Pending sources are distinct and retain their activation and withdrawal ordering. -/
theorem Run.pendingConsolidation_invariant {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (electra : .pectra ≤ x.fork)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ((x.state.pendingConsolidations electra).data.toList.map (·.sourceIndex)).Nodup ∧
    ∀ c ∈ (x.state.pendingConsolidations electra).data.toList,
      ∃ v, x.state.validators.data[c.sourceIndex.toNat]? = some v ∧
        v.activationEpoch ≤ getCurrentEpoch x.state ∧
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat ∧ v.exitEpoch ≠ FAR_FUTURE_EPOCH :=
  (run.pendingConsolidationsOrdered genesis early delay).1 electra

/-- Every pending consolidation of a state of a run names a source inside the registry. -/
theorem Run.pendingConsolidation_sources {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    PendingSources x.state := by
  intro electra c member
  obtain ⟨v, found, -⟩ :=
    (run.pendingConsolidation_invariant genesis early electra delay).2 c member
  exact (Array.getElem?_eq_some_iff.mp found).1

/-- From Electra, registry updates preserve the withdrawable epoch of an assigned exit. -/
theorem processRegistryUpdates_withdrawableEpoch_of_assigned
    {preset : Preset} {fork : Fork} {config : Config}
    {state after : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config state = .ok after)
    (i : Nat) (v : Validator) (found : state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ w : Validator, after.validators.data[i]? = some w ∧
      w.withdrawableEpoch = v.withdrawableEpoch :=
  (WithdrawalKept.registry_exact electra ok).2 i v found assigned

/-- From Electra, registry updates keep the withdrawable epoch of an unassigned exit.

Otherwise they give it one after the current epoch. -/
theorem processRegistryUpdates_withdrawableEpoch_of_unassigned
    {preset : Preset} {fork : Fork} {config : Config}
    {state after : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config state = .ok after)
    (i : Nat) (v : Validator) (found : state.validators.data[i]? = some v)
    (unassigned : v.exitEpoch = FAR_FUTURE_EPOCH) :
    ∃ w : Validator, after.validators.data[i]? = some w ∧
      (w.withdrawableEpoch = v.withdrawableEpoch ∨ getCurrentEpoch state < w.withdrawableEpoch) :=
  (WithdrawalKept.registry_unassigned electra ok).2.2 i v found unassigned

end EthLib.Consensus
