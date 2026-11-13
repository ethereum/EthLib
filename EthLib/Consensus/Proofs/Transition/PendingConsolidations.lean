module

public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Totality.EpochBeforeAltair

/-!
# Pending consolidation sources and lifecycle

Every pending source remains in the validator registry along a run before Gloas.

Electra starts an empty queue, requests append existing indices, and processing drops a prefix.

With positive withdrawal delay, sources are distinct and keep their activation and exit ordering.

An assigned exit prevents a source from being queued twice, and slashing only delays withdrawal.
-/

@[expose] public section
namespace EthLib.Consensus
open Base
variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A new validator leaves the pending consolidations as they were. -/
private theorem addValidatorToRegistry_pendingConsolidations {f : Fork}
    {s t : BeaconState preset f} {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    {amount : Gwei}
    (ok : addValidatorToRegistry s pubkey credentials amount = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := by
  unfold addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
    rfl
  · split at ok <;> cases ok
    rfl

/-- The pending deposits of an epoch leave the pending consolidations as they were. -/
theorem processPendingDeposits_pendingConsolidations {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f}
    (ok : processPendingDeposits config checks s electra = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := by
  have deposit {a b : BeaconState preset f} {d : PendingDeposit}
      (ok : applyPendingDeposit config checks a d = .ok b) :
      b.pendingConsolidations = a.pendingConsolidations := by
    rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · rfl
    · obtain ⟨_, set⟩ := increaseBalance_ok raised
      obtain ⟨_, rfl⟩ := setBalance_ok set
      rfl
    · exact addValidatorToRegistry_pendingConsolidations added
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  exact foldlM_ok_invariant (fun b => b.pendingConsolidations = s.pendingConsolidations)
    (fun _ _ _ prior step => (deposit step).trans prior) rfl folded

def SamePendingQueue {f : Fork} (s t : BeaconState preset f) : Prop :=
  t.pendingConsolidations = s.pendingConsolidations

private theorem SamePendingQueue.trans {f : Fork} {s t u : BeaconState preset f}
    (one : SamePendingQueue s t) (two : SamePendingQueue t u) : SamePendingQueue s u :=
  Eq.trans two one

private theorem SamePendingQueue.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → SamePendingQueue a b)
    (ok : xs.foldlM step s = .ok t) : SamePendingQueue s t :=
  foldlM_ok_invariant (SamePendingQueue s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed)) rfl ok

private theorem SamePendingQueue.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v : Validator} (ok : s.setValidatorAt i v = .ok t) : SamePendingQueue s t := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

private theorem SamePendingQueue.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v : Validator} (ok : s.setValidator i v = .ok t) :
    SamePendingQueue s t :=
  setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem SamePendingQueue.increase {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {amount : Gwei} (ok : increaseBalance s i amount = .ok t) :
    SamePendingQueue s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem SamePendingQueue.decrease {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {amount : Gwei} (ok : decreaseBalance s i amount = .ok t) :
    SamePendingQueue s t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  rfl

private theorem SamePendingQueue.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    SamePendingQueue s t :=
  (initiateValidatorExit_balances_eq_and_pendingConsolidations_eq ok).2

private theorem SamePendingQueue.rewards {f : Fork} {s t : BeaconState preset f}
    (ok : processRewardsAndPenalties config s = .ok t) : SamePendingQueue s t := by
  show t.pendingConsolidations = s.pendingConsolidations
  rw [processRewardsAndPenalties_frame ok]

private theorem SamePendingQueue.slashings {f : Fork} {s t : BeaconState preset f}
    (ok : processSlashings s = .ok t) : SamePendingQueue s t := by
  show t.pendingConsolidations = s.pendingConsolidations
  rw [processSlashings_frame ok]

private theorem SamePendingQueue.justification {f : Fork} {s t : BeaconState preset f}
    (ok : processJustificationAndFinalization s = .ok t) : SamePendingQueue s t := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    unfold SamePendingQueue
    rw [← rest]

theorem SamePendingQueue.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : SamePendingQueue s t := by
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

/-- An epoch stage keeps the pending consolidations, unless it is the stage that processes them. -/
theorem EpochStage.Edge.samePendingQueue {f : Fork} {stage : EpochStage}
    {s t : BeaconState preset f} (edge : EpochStage.Edge config checks stage s t)
    (other : stage ≠ .pendingConsolidations) : SamePendingQueue s t := by
  cases stage
  case rewards => exact SamePendingQueue.rewards edge
  case slashings => exact SamePendingQueue.slashings edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits_pendingConsolidations edge
    · exact edge ▸ rfl
  case pendingConsolidations => exact absurd rfl other
  all_goals exact (edge.balances_eq_and_pendingConsolidations_eq ⟨nofun, nofun, nofun, nofun⟩).2

variable {fork : Fork} {state after : BeaconState preset fork}
  {engine : ExecutionEngine preset fork}

namespace SamePendingQueue

theorem refl (s : BeaconState preset fork) : SamePendingQueue s s := rfl

private theorem slash {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state i whistleblower = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, read, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (exit exited).trans (setValidator set)
  have second : SamePendingQueue marked last :=
    (show SamePendingQueue marked { marked with slashings } from rfl).trans
      ((decrease lowered).trans ((increase raised).trans (increase paid)))
  apply (first.trans second).trans
  split <;> rfl

theorem proposer {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    SamePendingQueue state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slash slashed

private theorem slashIf {step next : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (ok : slashIfSlashable config step index = .ok next) : SamePendingQueue step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact slash slashed
  · cases ok; rfl

theorem attester {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    SamePendingQueue state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step : BeaconState preset fork × Bool =>
    SamePendingQueue state step.1)
    (fun _ _ _ prior ok => prior.trans (slashIf ok))
    (show SamePendingQueue state (state, false).1 from rfl) folded

theorem voluntary {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks state signed = .ok after) :
    SamePendingQueue state after :=
  exit (processVoluntaryExit_initiates ok)

theorem bls {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator set

theorem deposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (ok : processDeposit config checks before state deposit = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨early, _⟩
  · rfl
  · rfl
  · exact (addValidatorToRegistry_pendingConsolidations added :)
  · exact absurd electra (Nat.not_le_of_lt early)

theorem depositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest state electra request = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  rfl

private theorem partialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config state electra index validator amount owed = .ok after) :
    SamePendingQueue state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, final⟩ := churned
    cases final; rfl
  · cases ok; rfl

theorem withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after) :
    SamePendingQueue state after := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; rfl)
    | exact exit (liftAccessor_ok.mp ok)
    | exact partialWithdrawal ok

theorem attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (electra : .pectra ≤ fork)
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    SamePendingQueue state after := by
  unfold processAttestation at ok
  rw [dite_eq_left (show .altair ≤ fork from Nat.le_trans (by decide) electra)] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := ok
  have last : SamePendingQueue raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]; rfl
    · cases final; rfl
  have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
      SamePendingQueue state (setEpochParticipation state current participation) := by
    intro current participation
    unfold setEpochParticipation
    split <;> rfl
  exact (flagged _ _).trans ((increase raisedOk).trans last)

private theorem withdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (early : fork < .glamsterdam)
    (ok : processWithdrawals state capella payload = .ok after) :
    SamePendingQueue state after := by
  unfold processWithdrawals at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, applied⟩ := ok
  unfold applyExpectedWithdrawals at applied
  simp only [bind_ok_iff] at applied
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := applied
  have one : SamePendingQueue state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact fold (fun _ _ _ ok => by
      unfold applyWithdrawal at ok
      split at ok
      · simp only [bind_ok_iff] at ok
        obtain ⟨_, _, set⟩ := ok
        obtain ⟨_, rfl⟩ := setBuilder_ok set
        rfl
      · exact decrease ok) appliedOk
  have two : SamePendingQueue applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      rfl
    · cases indexedOk; rfl
  simp only [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early),
    pure, Except.pure, Except.ok.injEq] at sweptOk
  subst finished
  have lastKept : SamePendingQueue indexed after := by
    split at last <;>
    unfold updateNextWithdrawalValidatorIndex at last
    all_goals
      simp only [bind_ok_iff] at last
      obtain ⟨_, _, last⟩ := last
      split at last
      · cases last
      · cases last; rfl
  exact one.trans (two.trans lastKept)

theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    SamePendingQueue state after := by
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
    have kept := SamePendingQueue.fold (fun _ _ _ ok => by
      simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, b, balance, _, set, rfl⟩ := ok
      obtain ⟨_, rfl⟩ := setBalance_ok balance
      have same := SamePendingQueue.setValidator set
      exact same) queued
    have kept' := SamePendingQueue.fold (fun _ _ _ ok => by
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
    have queue := kept.trans kept'
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

private def WithdrawalKept {f g : Fork} (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.exitEpoch ≠ FAR_FUTURE_EPOCH →
    ∃ w : Validator, t.validators.data[i]? = some w ∧ v.withdrawableEpoch ≤ w.withdrawableEpoch

namespace WithdrawalKept

private theorem of_data {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data := by rfl) : WithdrawalKept s t := by
  intro i v found _
  exact ⟨v, by rw [same]; exact found, UInt64.le_refl _⟩

private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : WithdrawalKept s t) (two : WithdrawalKept t u)
    (life : RegistryLifecycle s t) : WithdrawalKept s u := by
  intro i v found assigned
  obtain ⟨w, middle, bound⟩ := one i v found assigned
  obtain ⟨w', middle', kept⟩ := life.validators i v found
  have same : w' = w := Option.some.inj (middle'.symm.trans middle)
  subst w'
  obtain ⟨z, final, bound'⟩ := two i w middle (by rw [kept.exitEpoch assigned]; exact assigned)
  exact ⟨z, final, UInt64.le_trans bound bound'⟩

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

private theorem setAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old) (set : state.setValidatorAt i v = .ok after)
    (kept : old.exitEpoch ≠ FAR_FUTURE_EPOCH → old.withdrawableEpoch ≤ v.withdrawableEpoch) :
    WithdrawalKept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro j w read assigned
  by_cases same : j = i
  · subst j
    have eq : w = old := by simpa [Array.getElem?_eq_getElem inside, oldEq] using read.symm
    subst w
    refine ⟨v, ?_, kept assigned⟩
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, inside]
  · refine ⟨w, ?_, UInt64.le_refl _⟩
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same, Ne.symm same] using read

private theorem set {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old) (written : state.setValidator i v = .ok after)
    (kept : old.exitEpoch ≠ FAR_FUTURE_EPOCH → old.withdrawableEpoch ≤ v.withdrawableEpoch) :
    WithdrawalKept state after :=
  setAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) kept

private theorem exit {i : ValidatorIndex}
    (ok : initiateValidatorExit config state i = .ok after) : WithdrawalKept state after := by
  obtain ⟨v, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, written⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact of_data
  · have same := (exitQueue_validators queue).1
    exact (of_data (congrArg (·.data) same)).trans
      (set ((getValidator_of_validators_eq same i).trans found) written
        (fun assigned => False.elim (assigned far))) (.of_data (congrArg (·.data) same))

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
    ((set found markedOk (fun _ => by
      rw [UInt64.max_def]
      split
      · assumption
      · exact UInt64.le_refl _)).trans
      (of_data (congrArg (·.data) same))
      (.setValidator found markedOk ⟨fun _ => rfl, fun _ => rfl⟩))
    (registryLifecycle_initiateValidatorExit exitedOk)

private theorem effectiveUpdates
    (ok : processEffectiveBalanceUpdates state = .ok after) : WithdrawalKept state after := by
  refine fold (fun _ _ _ ok => ?_) (fun _ _ _ ok => ?_) ok
  · simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, _, _, set⟩ := ok
    exact setAt found set (fun _ => UInt64.le_refl _)
  · simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, _, _, set⟩ := ok
    exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩

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
  exact (set found written (fun _ => UInt64.le_refl _)).trans
    (of_data (congrArg (·.data) rest))
    (.setValidator found written ⟨fun _ => rfl, fun _ => rfl⟩)

private theorem registry (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config state = .ok after) : WithdrawalKept state after := by
  unfold processRegistryUpdates at ok
  rw [ite_eq_left electra] at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  refine fold (fun _ _ _ ok => ?_)
    (fun _ _ _ ok => by
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
      · cases ok; exact .refl _) ok
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, written⟩ := ok
    exact setAt found written (fun _ => UInt64.le_refl _)
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact exit exited
  split at ok
  · exact setAt found (liftAccessor_ok.mp ok) (fun _ => UInt64.le_refl _)
  · cases ok; exact of_data

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v) :
    WithdrawalKept state after := by
  intro i old found _
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  refine ⟨old, ?_, UInt64.le_refl _⟩
  simpa [added, Array.getElem?_push, Nat.ne_of_lt inside] using found

private theorem deposit {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks state deposit = .ok after) :
    WithdrawalKept state after := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · exact of_data
  · exact increase ok
  · exact append (addValidatorToRegistry_validators_eq_push ok)

private theorem pendingDeposits {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks state electra = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  exact (fold (fun _ _ _ => deposit) (fun _ _ _ => registryLifecycle_applyPendingDeposit)
    folded :)

private theorem proposer {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    WithdrawalKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slash slashed

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

private theorem bls {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨_, found, _, _, _, written⟩ := processBlsToExecutionChange_ok ok
  exact set found written (fun _ => UInt64.le_refl _)

private theorem attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (electra : .pectra ≤ fork)
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    WithdrawalKept state after := by
  have same : after.validators = state.validators := by
    unfold processAttestation at ok
    rw [dite_eq_left (show .altair ≤ fork from Nat.le_trans (by decide) electra)] at ok
    unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have flagged : ∀ (current : Bool) (p : EpochParticipation preset fork),
        (setEpochParticipation state current p).validators = state.validators := by
      intro current p; unfold setEpochParticipation; split <;> rfl
    have before := (increaseBalance_validators raisedOk).trans (flagged _ _)
    split at final
    · rw [recordPaymentWeight_eq final]; exact before
    · cases final; exact before
  exact of_data (congrArg (·.data) same)

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

private theorem depositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest state electra request = .ok after) :
    WithdrawalKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact of_data

private theorem partialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config state electra index validator amount owed = .ok after) :
    WithdrawalKept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, final⟩ := churned
    cases final; exact of_data
  · cases ok; exact of_data

private theorem withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after) :
    WithdrawalKept state after := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact of_data)
    | exact exit (liftAccessor_ok.mp ok)
    | exact partialWithdrawal ok

/-- The execution part of a block keeps the validators, so it keeps their withdrawal epochs. -/
private theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    WithdrawalKept state after :=
  of_data (congrArg (·.data) (processBlockExecution_validators ok))

end WithdrawalKept

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
  obtain ⟨w', read', bound⟩ := withdrawal c.sourceIndex.toNat v found assigned
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

theorem justification (holds : PendingConsolidationInvariant config state)
    (ok : processJustificationAndFinalization state = .ok after) :
    PendingConsolidationInvariant config after := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · exact holds
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    apply holds.kept (SamePendingQueue.justification ok) (.of_data (by rw [← rest]))
    · exact WithdrawalKept.of_data (by rw [← rest])
    · rw [show getCurrentEpoch after = getCurrentEpoch state from by
        unfold getCurrentEpoch; rw [← rest]]
      exact UInt64.le_refl _

theorem inactivity (holds : PendingConsolidationInvariant config state) {altair : .altair ≤ fork}
    (ok : processInactivityUpdates config state altair = .ok after) :
    PendingConsolidationInvariant config after := by
  rw [processInactivityUpdates_frame ok]
  exact holds

theorem rewards (holds : PendingConsolidationInvariant config state)
    (ok : processRewardsAndPenalties config state = .ok after) :
    PendingConsolidationInvariant config after := by
  rw [processRewardsAndPenalties_frame ok]
  exact holds

theorem registry (holds : PendingConsolidationInvariant config state)
    (ok : processRegistryUpdates config state = .ok after) :
    PendingConsolidationInvariant config after := by
  by_cases electra : .pectra ≤ fork
  · -- The registry stage reads no signature checks, so any of them gives its edge.
    apply holds.kept (EpochStage.Edge.balances_eq_and_pendingConsolidations_eq
      (stage := .registry) (checks := .bls) ok ⟨nofun, nofun, nofun, nofun⟩).2
      (registryLifecycle_processRegistryUpdates ok) (WithdrawalKept.registry electra ok)
    rw [show getCurrentEpoch after = getCurrentEpoch state from
      congrArg (computeEpochAtSlot preset) (frame_processRegistryUpdates ok).slot]
    exact UInt64.le_refl _
  · intro h; exact False.elim (electra h)

theorem slashings (holds : PendingConsolidationInvariant config state)
    (ok : processSlashings state = .ok after) : PendingConsolidationInvariant config after := by
  rw [processSlashings_frame ok]
  exact holds

theorem eth1Reset (holds : PendingConsolidationInvariant config state) {before : fork < .hegota}
    (ok : processEth1DataReset before state = .ok after) :
    PendingConsolidationInvariant config after := by
  rw [processEth1DataReset_frame ok]
  exact holds

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

private theorem queue {electra : .pectra ≤ fork} {sourceIndex targetIndex : ValidatorIndex}
    {source : Validator} (holds : PendingConsolidationInvariant config state)
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (active : source.activationEpoch ≤ getCurrentEpoch state)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    PendingConsolidationInvariant config after := by
  have frame := frame_queueConsolidation found ok
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churnOk, withdrawal, added, written, set, pending, appended, final⟩ :=
    ok
  cases final
  have data := appendWithinLimit_data appended
  have churnRegistry := (computeConsolidationEpochAndUpdateChurn_earliest churnOk).2.1
  have churnQueue : churned.pendingConsolidations = state.pendingConsolidations := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churnOk
    obtain ⟨_, _, _, _, _, _, final⟩ := churnOk
    cases final; rfl
  have queueEq := SamePendingQueue.setValidator set
  change written.pendingConsolidations = churned.pendingConsolidations at queueEq
  have sum := (Uint64.addChecked_ok_iff.mp added).2
  have assigned : epoch ≠ FAR_FUTURE_EPOCH := by
    intro eq
    have bound := withdrawal.toNat_lt
    rw [eq] at sum
    have farNat : FAR_FUTURE_EPOCH.toNat = 18446744073709551615 := rfl
    rw [farNat] at sum
    omega
  intro witness
  obtain ⟨unique, sources⟩ := holds witness
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
    have sameEpoch : getCurrentEpoch written = getCurrentEpoch state :=
      congrArg (computeEpochAtSlot preset) frame.slot
    rcases mem with mem | rfl
    · obtain ⟨v, read, activation, ordered, assigned⟩ := sources c mem
      have distinct : c.sourceIndex ≠ sourceIndex := by
        intro eq
        rw [eq, found] at read
        cases read
        exact assigned far
      refine ⟨v, ?_, ?_, ordered, assigned⟩
      · have read' := getValidator_setValidator_of_ne set distinct
        rw [getValidator_of_validators_eq churnRegistry] at read'
        exact getValidator_eq_ok_iff.mp (read'.trans (getValidator_eq_ok_iff.mpr read))
      · change v.activationEpoch ≤ getCurrentEpoch written
        rw [sameEpoch]; exact activation
    · refine ⟨{source with exitEpoch := epoch, withdrawableEpoch := withdrawal}, ?_, ?_, ?_,
        assigned⟩
      · have read := getValidator_eq_ok_iff.mp (getValidator_setValidator_self set)
        exact read
      · change source.activationEpoch ≤ getCurrentEpoch written
        rw [sameEpoch]; exact active
      · exact Nat.le_of_eq sum.symm

private theorem request {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (holds : PendingConsolidationInvariant config state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processConsolidationRequest config state electra request = .ok after) :
    PendingConsolidationInvariant config after := by
  have epoch : getCurrentEpoch after = getCurrentEpoch state :=
    congrArg (computeEpochAtSlot preset) (frame_processConsolidationRequest ok).slot
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact holds)
    | exact holds.kept (SamePendingQueue.compounding (liftAccessor_ok.mp ok))
        (registryLifecycle_switchToCompoundingValidator (liftAccessor_ok.mp ok))
        (WithdrawalKept.compounding (liftAccessor_ok.mp ok))
        (by rw [epoch]; exact UInt64.le_refl _)
    | exact holds.queue (getElem?_toNat_of_ofNatChecked (by assumption))
        (by clear ok; simp_all [isActiveValidator]) (by clear ok; simp_all) delay ok

private theorem framed (holds : PendingConsolidationInvariant config state)
    (queue : SamePendingQueue state after) (life : RegistryLifecycle state after)
    (withdrawal : WithdrawalKept state after) (slot : after.slot = state.slot) :
    PendingConsolidationInvariant config after := by
  apply holds.kept queue life withdrawal
  rw [show getCurrentEpoch after = getCurrentEpoch state from
    congrArg (computeEpochAtSlot preset) slot]
  exact UInt64.le_refl _

/-- An epoch keeps the invariant, stage by stage of the epoch schedule.

The first eight stages have their own lemmas above.

Effective-balance updates keep the queue and the slot, and no withdrawal epoch decreases.

Each later stage keeps the queue, the validators and the slot. -/
private theorem epoch (holds : PendingConsolidationInvariant config state)
    (ok : processEpoch config checks state = .ok after) :
    PendingConsolidationInvariant config after := by
  refine (processEpoch_trace ok).transport
    (fun a b => PendingConsolidationInvariant config a → PendingConsolidationInvariant config b)
    (fun _ => id) (fun one two => two ∘ one) ?_ holds
  intro k _ a b computed held
  have edge := EpochStage.action_cases.mp computed
  cases k
  case justification => exact held.justification edge
  case rewards => exact held.rewards edge
  case registry => exact held.registry edge
  case slashings => exact held.slashings edge
  case inactivity | eth1Reset | pendingDeposits | pendingConsolidations =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · first
      | exact held.inactivity edge
      | exact held.eth1Reset edge
      | exact held.pendingDeposits edge
      | exact held.consolidations edge
    · exact edge ▸ held
  case effectiveBalances =>
    exact held.framed (edge.samePendingQueue nofun)
      (registryLifecycle_processEffectiveBalanceUpdates edge)
      (WithdrawalKept.effectiveUpdates edge) (frame_processEffectiveBalanceUpdates edge).slot
  all_goals
    have same := congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)
    refine held.framed (edge.samePendingQueue nofun) (.of_data same)
      (WithdrawalKept.of_data same) ?_
    simp only [EpochStage.Edge] at edge
    first
      | exact (frame_processSlashingsReset edge).slot
      | exact (frame_processRandaoMixesReset edge).slot
      | split at edge
        · first
          | exact (frame_processBuilderPendingPayments edge).slot
          | exact (frame_processHistoricalSummariesUpdate edge).slot
          | exact (frame_processSyncCommitteeUpdates edge).slot
          | exact (frame_processProposerLookahead edge).slot
          | exact (frame_processPtcWindow edge).slot
          | (subst edge; rfl)
        · first
          | exact (frame_processHistoricalRootsUpdate edge).slot
          | exact (frame_processParticipationRecordUpdates edge).slot
          | exact edge ▸ rfl

private theorem fold {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)} {xs : List α}
    (kept : ∀ a item b, PendingConsolidationInvariant config a → step a item = .ok b →
      PendingConsolidationInvariant config b)
    (holds : PendingConsolidationInvariant config state) (ok : xs.foldlM step state = .ok after) :
    PendingConsolidationInvariant config after :=
  foldlM_ok_invariant (PendingConsolidationInvariant config) kept holds ok

private theorem executionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (holds : PendingConsolidationInvariant config state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processExecutionRequests config state body electra = .ok after) :
    PendingConsolidationInvariant config after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  have first := fold (fun _ _ _ h ok => h.framed (SamePendingQueue.depositRequest ok)
    (registryLifecycle_processDepositRequest ok) (WithdrawalKept.depositRequest ok)
    (frame_processDepositRequest ok).slot) holds deposits
  have second := fold (fun _ _ _ h ok => h.framed (SamePendingQueue.withdrawalRequest ok)
    (registryLifecycle_processWithdrawalRequest ok) (WithdrawalKept.withdrawalRequest ok)
    (frame_processWithdrawalRequest ok).slot) first withdrawals
  exact fold (fun _ _ _ h ok => h.request delay ok) second consolidations

/-- A block keeps the invariant, read through master's decomposition of a block.

A block frame does not carry the queue, so each step reads its own queue lemma. -/
private theorem block (early : fork < .glamsterdam)
    (holds : PendingConsolidationInvariant config state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) :
    PendingConsolidationInvariant config after := by
  by_cases electra : .pectra ≤ fork
  case neg => exact fun witness => absurd witness electra
  have noGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt early
  let Kept (a b : BeaconState preset fork) : Prop :=
    PendingConsolidationInvariant config a → PendingConsolidationInvariant config b
  have trans {a b c : BeaconState preset fork} (one : Kept a b) (two : Kept b c) : Kept a c :=
    two ∘ one
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : Kept state input :=
    OperationsInput.step_of Kept (fun _ => id) trans (fun gloas _ => absurd gloas noGloas)
      (fun headed => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed; exact id)
      (fun _ executed h => h.framed (SamePendingQueue.blockExecution early executed)
        (.of_data (congrArg (·.data) (processBlockExecution_validators executed)))
        (WithdrawalKept.blockExecution executed)
        (frame_processBlockExecution executed).slot)
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
      (fun deposited h => h.framed (SamePendingQueue.deposit electra deposited)
        (registryLifecycle_processDeposit deposited) (WithdrawalKept.blockDeposit electra deposited)
        (frame_processDeposit deposited).slot)
      (fun exited h => h.framed (SamePendingQueue.voluntary exited)
        (registryLifecycle_processVoluntaryExit exited)
        (WithdrawalKept.exit (processVoluntaryExit_initiates exited))
        (frame_processVoluntaryExit exited).slot)
      (fun changed h => h.framed (SamePendingQueue.bls changed)
        (registryLifecycle_processBlsToExecutionChange changed) (WithdrawalKept.bls changed)
        (frame_processBlsToExecutionChange changed).slot)
      (fun requested h => h.executionRequests delay requested)
      (fun {_ _ gloas} _ => absurd gloas noGloas) operated
  have tail : Kept last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact fun h => h.framed rfl (.of_data rfl) .of_data rfl
    · cases synced
      exact id
  have p := fold (fun _ _ _ h ok => h.framed (SamePendingQueue.proposer ok)
    (registryLifecycle_processProposerSlashing ok) (WithdrawalKept.proposer ok)
    (frame_processProposerSlashing ok).slot) (head holds) proposersOk
  have a := fold (fun _ _ _ h ok => h.framed (SamePendingQueue.attester ok)
    (registryLifecycle_processAttesterSlashing ok) (WithdrawalKept.attester ok)
    (frame_processAttesterSlashing ok).slot) p slashingsOk
  have att := fold (fun _ _ _ h ok => h.framed (SamePendingQueue.attestation electra ok)
    (registryLifecycle_processAttestation ok) (WithdrawalKept.attestation electra ok)
    (frame_processAttestation ok).slot) a attestedOk
  exact tail (rest att)

private theorem advance (holds : PendingConsolidationInvariant config state)
    (ok : advanceSlot config checks state = .ok after) :
    PendingConsolidationInvariant config after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : PendingConsolidationInvariant config cached := by rw [cachedEq]; exact holds
  have second : PendingConsolidationInvariant config epoched ∧ epoched.slot = state.slot := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · refine ⟨epoch first epochedOk, ?_⟩
      obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
      have same : justified.slot = cached.slot := by
        obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
        · rfl
        · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
          rw [← rest]
      exact frame.slot.trans (same.trans (by rw [cachedEq]))
    · cases epochedOk; exact ⟨first, by rw [cachedEq]⟩
  apply second.1.kept (t := {epoched with slot := next}) rfl (.of_data rfl)
    (WithdrawalKept.of_data rfl)
  apply UInt64.le_iff_toNat_le.mpr
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  simp only [second.2, sum]
  exact Nat.div_le_div_right (Nat.le_succ _)

private theorem upgrade {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : PendingConsolidationInvariant config pre.state)
    (ok : upgradeNext config checks pre = .ok post)
    (early : post.val.fork < .glamsterdam) :
    PendingConsolidationInvariant config post.val.state :=
  upgradeNext_pending (P := PendingConsolidationInvariant config)
    (fun _ before electra => absurd electra (Nat.not_le_of_lt before))
    (fun _ empty electra => by simp [empty electra])
    (fun upgraded holds => by
      simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
      obtain ⟨_, _, rfl⟩ := upgraded
      intro electra
      simpa [carryFields, carryList, carryRooted, getCurrentEpoch] using
        holds (show Fork.pectra ≤ .pectra from Nat.le_refl _))
    holds ok early

private theorem step {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam)
    (holds : PendingConsolidationInvariant config x.state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    PendingConsolidationInvariant config y.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have initial := advance holds slotOk
    have rest := processUpgrades_induction
      (property := fun post => post.fork < .glamsterdam →
        PendingConsolidationInvariant config post.state)
      (fun {pre post} h ok early => upgrade (h (Nat.lt_trans post.property early)) ok early)
      (fun _ => initial) upgrades
    exact rest early
  | block engine signed due ok => exact block early holds delay (applySignedBlock_ok ok).2.1

end PendingConsolidationInvariant

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
          v.withdrawableEpoch.toNat ∧ v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  have holds : PendingConsolidationInvariant config x.state := by
    clear electra
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      have before := (initializeBeaconStateFromEth1_invariant ok).1
      intro electra
      exact False.elim (Nat.not_le_of_lt (Nat.lt_trans before (by decide)) electra)
    | snoc pre step ih =>
      exact PendingConsolidationInvariant.step step early
        (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)) delay
  exact holds electra

end EthLib.Consensus
