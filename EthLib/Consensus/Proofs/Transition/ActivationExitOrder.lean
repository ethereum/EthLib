module

public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Activation before exit

Every validator in a reachable state activates no later than it exits.

A new validator has no exit epoch.

An exit is only assigned to a validator whose activation epoch has passed.

An activation is only assigned to a validator whose exit is not yet assigned.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- Every validator activates no later than it exits. -/
def ActivationExitOrder (s : BeaconState preset fork) : Prop :=
  ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch

namespace ActivationExitOrder

private theorem far_max (e : Epoch) : e ≤ FAR_FUTURE_EPOCH := by
  have := e.toNat_lt
  change e.toNat ≤ (FAR_FUTURE_EPOCH).toNat
  change e.toNat ≤ 18446744073709551615
  omega

private theorem exit_pending {v : Validator} (ordered : v.activationEpoch ≤ v.exitEpoch)
    (pending : v.activationEpoch = FAR_FUTURE_EPOCH) : v.exitEpoch = FAR_FUTURE_EPOCH := by
  exact UInt64.le_antisymm (far_max _) (pending ▸ ordered)

private theorem active_le {v : Validator} {e : Epoch}
    (active : isActiveValidator v e = true) : v.activationEpoch ≤ e := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact active.1

private theorem slashable_le {v : Validator} {e : Epoch}
    (active : isSlashableValidator v e = true) : v.activationEpoch ≤ e := by
  simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact active.1.2

/-- A step after which the order holds whenever it held before. -/
private def Kept {f g : Fork} (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop := ActivationExitOrder s → ActivationExitOrder t

namespace Kept

private theorem refl (s : BeaconState preset fork) : Kept s s := id

private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : Kept s t) (two : Kept t u) :
    Kept s u := two ∘ one

private theorem of_data {g : Fork} {t : BeaconState preset g}
    (same : t.validators.data = state.validators.data := by rfl) :
    Kept state t := by
  intro h v member
  exact h v (same ▸ member)

private theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → Kept s t) {xs : List α}
    (ok : xs.foldlM step state = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (refl state) ok

private theorem setValidatorAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old)
    (set : state.setValidatorAt i v = .ok after)
    (keeps : old.activationEpoch ≤ old.exitEpoch → v.activationEpoch ≤ v.exitEpoch) :
    Kept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro h w member
  simp only [BeaconState.putValidator, RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set member with member | rfl
  · exact h w member
  · exact keeps (h old (oldEq ▸ Array.getElem_mem inside))

private theorem setValidator {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old)
    (set : state.setValidator i v = .ok after)
    (keeps : old.activationEpoch ≤ old.exitEpoch → v.activationEpoch ≤ v.exitEpoch) :
    Kept state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) keeps

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v)
    (pending : v.exitEpoch = FAR_FUTURE_EPOCH) : Kept state after := by
  intro h w member
  rw [added] at member
  rcases Array.mem_push.mp member with member | rfl
  · exact h w member
  · rw [pending]; exact far_max _

private theorem initiateValidatorExit {i : ValidatorIndex} {v : Validator}
    (found : getValidator state i = .ok v)
    (assigned : v.activationEpoch ≤ getCurrentEpoch state)
    (ok : Consensus.initiateValidatorExit config state i = .ok after) :
    Kept state after := by
  obtain ⟨old, read, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have equal := Except.ok.inj (read.symm.trans found)
    have same := (exitQueue_validators queue).1
    exact (of_data (congrArg (·.data) same)).trans <|
      setValidator ((getValidator_of_validators_eq same i).trans read) set
        (fun _ => by
          have later := exitQueue_lt queue
          have bound := UInt64.le_iff_toNat_le.mp assigned
          change old.activationEpoch.toNat ≤ UInt64.toNat _
          rw [equal]
          dsimp only at *
          omega)

private theorem increaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state i amount = .ok after) :
    Kept state after :=
  of_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem decreaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state i amount = .ok after) :
    Kept state after :=
  of_data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem slashValidator {i : ValidatorIndex} {v : Validator}
    {whistleblower : Option ValidatorIndex}
    (found : getValidator state i = .ok v)
    (assigned : v.activationEpoch ≤ getCurrentEpoch state)
    (ok : Consensus.slashValidator config state i whistleblower = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, read, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (initiateValidatorExit found assigned exited).trans
    (setValidator read set (fun h => h))
  have second := (of_data (state := marked) (t := { marked with slashings })).trans
    ((decreaseBalance lowered).trans ((increaseBalance raised).trans (increaseBalance paid)))
  apply (first.trans second).trans
  split <;> exact of_data

private theorem processProposerSlashing {slashing : ProposerSlashing}
    (ok : Consensus.processProposerSlashing config checks state slashing = .ok after) :
    Kept state after := by
  simp only [Consensus.processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, v, found, _, slashable, _, _, _, _, slashed⟩ := ok
  exact slashValidator found (slashable_le slashable) slashed

private theorem slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (ok : Consensus.slashIfSlashable config step index = .ok next) :
    Kept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [Consensus.slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · rename_i slashable
    simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    apply slashValidator found ?_ slashed
    simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at slashable
    exact slashable.1.2
  · cases ok; exact refl _

private theorem processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (ok : Consensus.processAttesterSlashing config checks state slashing = .ok after) :
    Kept state after := by
  simp only [Consensus.processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step => Kept state step.1)
    (fun _ _ _ before ok => before.trans (slashIfSlashable ok))
    (show Kept state (state, false).1 from refl state) folded

private theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    Kept state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨v, found, _, active, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit found (active_le active) exited

private theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    Kept state after := by
  unfold Consensus.applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact append (addValidatorToRegistry_validators_eq_push ok) rfl
    · cases ok; exact refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact increaseBalance ok

private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : Kept state after := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, added, pushed⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (append (addValidatorToRegistry_validators_eq_push added) rfl).trans of_data
      · cases ok; exact refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact of_data
  · exact applyPendingDeposit ok

private theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    Kept state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_data (state := state)
    (t := { state with eth1DepositIndex := fun _ => next })).trans (applyDeposit credited)

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    Kept state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator found set id

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    Kept state after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact of_data
  · cases ok; exact refl _

private theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    Kept state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (setValidator found set id).trans (queueExcessActiveBalance queued)

private theorem requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) : Kept state after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact (of_data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])).trans of_data
  · cases ok; exact refl _

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    Kept state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact requestPartialWithdrawal ok
    | (apply initiateValidatorExit (config := config)
         (by rw [getValidator, getElem?_toNat_of_ofNatChecked (by assumption)])
         ?_ (liftAccessor_ok.mp ok)
       rename_i position _ _ _ _ _ _ _ _ _ _ _ _ _ _
       have accepted : canRequest config state state.validators.data[position] = .ok true := by
         simp_all
       unfold canRequest at accepted
       dsimp only at accepted
       split at accepted
       · cases accepted
       · rename_i active
         apply active_le
         simp at active
         exact active.1)

private theorem queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (assigned : source.activationEpoch ≤ getCurrentEpoch state)
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : Kept state after := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, _⟩, churn, _, _, _, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have same := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, same, found]
  exact (of_data (by rw [same])).trans <|
    (setValidator read set (fun _ => by
      cases first : computeActivationExitEpoch preset (getCurrentEpoch state) with
      | error =>
        simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError,
          bind, Except.bind] at churn
      | ok firstEpoch =>
        have early := UInt64.le_iff_toNat_le.mp
          (computeConsolidationEpochAndUpdateChurn_first first churn).1
        have eq := (computeActivationExitEpoch_ok_iff.mp first).2
        have bound := UInt64.le_iff_toNat_le.mp assigned
        change source.activationEpoch.toNat ≤ UInt64.toNat _
        dsimp only at *
        omega)).trans of_data

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    Kept state after := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals try first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact switchToCompoundingValidator (liftAccessor_ok.mp ok)
  -- The source is active, so its activation epoch is at most the current one.
  rename_i bothActive _ _ _ _ _ _ _ _ _
  exact queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption))
    (active_le ((Bool.and_eq_true _ _).mp bothActive).1) ok

private theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    Kept state after :=
  of_data (congrArg (·.data) (processDepositRequest_ok ok).2.1)

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    Kept state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations)

private theorem genesisDeposit {before : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (ok : Consensus.genesisDeposit config checks before leaves state entry = .ok after) :
    Kept state after := by
  simp only [Consensus.genesisDeposit, bind_ok_iff] at ok
  obtain ⟨root, _, deposited⟩ := ok
  exact (of_data (state := state)
    (t := { state with
      eth1Data := fun _ => { state.eth1Data before with depositRoot := root } })).trans
    (processDeposit deposited)

private theorem activateAtGenesis {index : Nat}
    (ok : Consensus.activateAtGenesis state index = .ok after) :
    Kept state after := by
  simp only [Consensus.activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, _, _, set⟩ := ok
  apply setValidatorAt found set
  split
  · intro _; change (0 : UInt64) ≤ _; exact UInt64.zero_le
  · exact id

private theorem updateRegistryEntry {index : Nat}
    (ok : Consensus.updateRegistryEntry config state index = .ok after) :
    Kept state after := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queuedOk, marked, markedOk, ok⟩ := ok
  have epochs : queued.activationEpoch = v.activationEpoch ∧ queued.exitEpoch = v.exitEpoch := by
    unfold queueForActivation at queuedOk
    split at queuedOk
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
      obtain ⟨_, _, rfl⟩ := queuedOk
      exact ⟨rfl, rfl⟩
    · cases queuedOk; exact ⟨rfl, rfl⟩
  have first := setValidatorAt found markedOk (by simpa only [epochs.1, epochs.2] using id)
  split at ok
  · rename_i active
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨i, converted, exited⟩ := ok
    have indexEq : i.toNat = index := (ofNatChecked_ok_iff.mp (mapError_ok_iff.mp converted)).2
    have set : state.setValidator i queued = .ok marked := by
      simpa [setValidator_eq_setValidatorAt, indexEq] using markedOk
    apply first.trans (initiateValidatorExit (getValidator_setValidator_self set) ?_ exited)
    simp only [Bool.and_eq_true] at active
    exact active_le active.1
  · cases ok; exact first

private theorem updateRegistryEntryElectra {epoch : Epoch} {index : Nat}
    (ok : Consensus.updateRegistryEntryElectra config epoch state index = .ok after) :
    Kept state after := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact setValidatorAt found set id
  split at ok
  · rename_i active
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨i, converted, exited⟩ := ok
    have indexEq : i.toNat = index := (ofNatChecked_ok_iff.mp (mapError_ok_iff.mp converted)).2
    apply initiateValidatorExit
      (by simpa [getValidator_eq_getValidatorAt, indexEq] using found) ?_ exited
    simp only [Bool.and_eq_true] at active
    exact active_le active.1
  split at ok
  · rename_i eligible
    apply setValidatorAt found (liftAccessor_ok.mp ok)
    intro h
    change epoch ≤ v.exitEpoch
    rw [exit_pending h (activationEpoch_of_isEligibleForActivation eligible)]
    exact far_max _
  · cases ok; exact refl _

private theorem foldActivateValidator :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ v, getValidator state index = .ok v ∧
        v.activationEpoch = FAR_FUTURE_EPOCH) →
      indices.foldlM activateValidator state = .ok after → Kept state after
  | [], _, _, _, _, ok => by cases ok; exact refl _
  | index :: rest, state, after, unique, eligible, ok => by
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, tail⟩ := ok
    obtain ⟨v, found, far⟩ := eligible index List.mem_cons_self
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨old, read, _, _, set⟩ := first
    have equal := Except.ok.inj (read.symm.trans found)
    have kept := setValidator read set (fun h => by
      change _ ≤ old.exitEpoch
      rw [exit_pending h (equal ▸ far)]
      exact far_max _)
    refine kept.trans (foldActivateValidator restUnique (fun other member => ?_) tail)
    have distinct : other ≠ index := fun same => absent (same ▸ member)
    obtain ⟨w, read, pending⟩ := eligible other (List.mem_cons_of_mem _ member)
    exact ⟨w, (getValidator_setValidator_of_ne set distinct).trans read, pending⟩

private theorem processRegistryUpdates
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    Kept state after := by
  unfold Consensus.processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact foldlM (fun _ _ _ ok => updateRegistryEntryElectra ok) ok
  rename_i notElectra
  simp only [bind_ok_iff] at ok
  obtain ⟨updated, first, activated⟩ := ok
  have before : fork < .glamsterdam := Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound before) (UInt64.toNat_lt _)
  refine (foldlM (fun _ _ _ ok => updateRegistryEntry ok) first).trans
    (foldActivateValidator
      (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
      (fun index member => ?_) activated)
  obtain ⟨position, v, equal, found, eligible⟩ :=
    mem_activationQueue (List.mem_of_mem_take member)
  refine ⟨v, ?_, activationEpoch_of_isEligibleForActivation eligible⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : index.toNat = position := by
    have bound : position < UInt64.size := by change position < 2 ^ 64; omega
    rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' bound]
  simp [getValidator, exact, found]

private theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      Consensus.passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass → Kept state pass.1.state
  | [], _, _, _, _, _, ok => by cases ok; exact refl _
  | deposit :: rest, state, processed, count, postponed, pass, ok => by
    unfold Consensus.passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; exact refl _
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact passPendingDeposits (deposits := rest) ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; exact refl _
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)

private theorem processPendingDeposits {electra : .pectra ≤ fork}
    (ok : Consensus.processPendingDeposits config checks state electra = .ok after) :
    Kept state after := by
  unfold Consensus.processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact (passPendingDeposits ‹_›).trans of_data

private theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    Kept state after := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact (of_data (state := state)).trans <|
    (setValidator (old := v) (by exact found) set₂ id).trans of_data

private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    Kept pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToAltair_spec upgraded).1
  · subst ok; exact of_data
  · subst ok; exact of_data
  · subst ok; exact of_data
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := upgraded
    have tail := foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok; exact refl _
      · cases ok; exact refl _) compounded
    have head := foldlM (fun _ _ _ ok => queuePreActivation ok) queued
    exact (of_data (state := state)).trans (head.trans tail)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact of_data (upgradeHezeFields_lists _).1

private theorem processEffectiveBalanceUpdates
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    Kept state after := by
  apply foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact setValidatorAt found set id

private theorem slashings (ok : processSlashings state = .ok after) :
    Kept state after := by
  unfold processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    refine foldlM (fun _ _ _ ok => ?_) applied
    unfold applySlashingPenaltyElectra at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact refl _)
      | exact decreaseBalance (liftAccessor_ok.mp ok)
  · refine foldlM (fun _ _ _ ok => ?_) ok
    unfold applySlashingPenalty at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact refl _)
      | exact decreaseBalance (liftAccessor_ok.mp ok)

private theorem eth1Reset {before : fork < .hegota}
    (ok : processEth1DataReset before state = .ok after) : Kept state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact of_data

/-- An epoch keeps the order; only three of its stages change the validators. -/
private theorem processEpoch (ok : Consensus.processEpoch config checks state = .ok after) :
    Kept state after := by
  apply (processEpoch_trace ok).transport Kept refl (fun a b => a.trans b)
  intro k _ a b computed
  have edge := EpochStage.action_cases.mp computed
  cases k
  case registry => exact processRegistryUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits edge
    · exact edge ▸ refl _
  case effectiveBalances => exact processEffectiveBalanceUpdates edge
  all_goals exact of_data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

private theorem advanceSlot (ok : Consensus.advanceSlot config checks state = .ok after) :
    Kept state after := by
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : Kept state cached := of_data (by rw [cachedEq])
  have second : Kept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch epochedOk
    · cases epochedOk; exact refl _
  exact first.trans (second.trans of_data)

private theorem applyWithdrawal {withdrawal : Withdrawal}
    (ok : Consensus.applyWithdrawal state withdrawal = .ok after) :
    Kept state after := by
  unfold Consensus.applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_data
  · exact decreaseBalance ok

private theorem applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (ok : Consensus.applyExpectedWithdrawals state capella expected = .ok after) :
    Kept state after := by
  unfold Consensus.applyExpectedWithdrawals at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
  have one : Kept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM (fun _ _ _ ok => applyWithdrawal ok) appliedOk
  have two : Kept applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact of_data
    · cases indexedOk; exact refl _
  have queued : ∀ kept : BeaconState preset fork,
      Kept kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact of_data
  have partials : ∀ kept : BeaconState preset fork,
      Kept kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact of_data
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → Kept kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok; exact of_data
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact of_data
    · cases ok; exact refl _
  have lastKept : Kept finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last; exact of_data
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

private theorem processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : Consensus.processWithdrawals state capella payload = .ok after) :
    Kept state after := by
  unfold Consensus.processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact applyExpectedWithdrawals applied
    · cases ok; exact refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact applyExpectedWithdrawals applied

private theorem executionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionPayload config engine state body bellatrix = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact of_data

private theorem executionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (ok : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    Kept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok ok
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact of_data
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact of_data

private theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Kept state after := by
  unfold processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    exact (processWithdrawals withdrawn).trans (executionPayloadBid bid)
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (processWithdrawals withdrawn).trans (executionPayload paid)
  · dsimp only at ok
    split at ok
    · exact executionPayload ok
    · cases ok; exact refl _

private theorem builderDeposit {gloas : .glamsterdam ≤ fork} {request : BuilderDepositRequest}
    (ok : processBuilderDepositRequest config checks state gloas request = .ok after) :
    Kept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first | (cases ok; done) | (cases ok; exact of_data)

private theorem builderExit {gloas : .glamsterdam ≤ fork} {request : BuilderExitRequest}
    (ok : processBuilderExitRequest config state gloas request = .ok after) :
    Kept state after := by
  rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
  · exact refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_data

private theorem parentPayload {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks state gloas body = .ok after) :
    Kept state after := by
  rcases processParentExecutionPayload_ok ok with ⟨_, _, rfl⟩ |
    ⟨_, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, _, rfl⟩
  · exact refl _
  · have first : Kept state settled := by
      rw [settleParentPayment_eq settledOk]; exact of_data
    exact first.trans <|
      (foldlM (fun _ _ _ ok => processDepositRequest ok) depositsOk).trans <|
      (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawalsOk).trans <|
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidationsOk).trans <|
      (foldlM (fun _ _ _ ok => builderDeposit ok) buildersOk).trans <|
      (foldlM (fun _ _ _ ok => builderExit ok) exitsOk).trans of_data

private theorem attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    Kept state after := by
  unfold processAttestation at ok
  split at ok
  · unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have last : Kept raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]; exact of_data
      · cases final; exact refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        Kept state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact of_data
    exact (flagged _ _).trans ((increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact of_data (by rw [← rest])

private theorem operations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after) :
    Kept state after := by
  unfold processOperations at ok
  split at ok
  · unfold processOperationsGloas at ok
    simp only [bind_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposers, _, attesters, _,
      attested, _, exits, _, changes, paid⟩ := ok
    exact (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposers).trans <|
      (foldlM (fun _ _ _ ok => processAttesterSlashing ok) attesters).trans <|
      (foldlM (fun _ _ _ ok => attestation ok) attested).trans <|
      (foldlM (fun _ _ _ ok => processVoluntaryExit ok) exits).trans <|
      (foldlM (fun _ _ _ ok => processBlsToExecutionChange ok) changes).trans <|
      foldlM (fun _ _ _ ok => by rw [processPayloadAttestation_eq ok]; exact refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have changesKept : Kept exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact foldlM (fun _ _ _ ok => processBlsToExecutionChange ok) changes
    · cases changes; exact refl _
  have requestsKept : Kept changed after := by
    split at requests
    · exact processExecutionRequests requests
    · cases requests; exact refl _
  exact (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposers).trans <|
    (foldlM (fun _ _ _ ok => processAttesterSlashing ok) attesters).trans <|
    (foldlM (fun _ _ _ ok => attestation ok) attested).trans <|
    (foldlM (fun _ _ _ ok => processDeposit ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processVoluntaryExit ok) exits).trans <|
    changesKept.trans requestsKept

private theorem blockHeader {block : BeaconBlock preset fork}
    (ok : processBlockHeader state block = .ok after) : Kept state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact of_data

private theorem randao {body : BeaconBlockBody preset fork}
    (ok : processRandao config checks state body = .ok after) : Kept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact of_data

private theorem eth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : processEth1Data before state body = .ok after) : Kept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  exact of_data (by rw [← rest])

private theorem syncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks state altair aggregate = .ok after) :
    Kept state after := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  exact foldlM (fun _ _ _ ok => by
    unfold applySyncReward at ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, raised, _, _, paid⟩ := ok
      exact (increaseBalance raised).trans (increaseBalance paid)
    · exact decreaseBalance (liftAccessor_ok.mp ok)) folded

private theorem processBlock {block : BeaconBlock preset fork}
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    Kept state after := by
  unfold Consensus.processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := ok
    have paidKept : Kept state paid := by
      split at paidOk
      · exact parentPayload paidOk
      · cases paidOk; exact refl _
    have executedKept : Kept headed executed := by
      split at executedOk
      · exact blockExecution executedOk
      · cases executedOk; exact refl _
    have votedKept : Kept revealed voted := by
      split at votedOk
      · exact eth1Data votedOk
      · cases votedOk; exact refl _
    exact paidKept.trans <| (blockHeader headedOk).trans <|
      executedKept.trans <| (randao revealedOk).trans <|
      votedKept.trans <| (operations operatedOk).trans (syncAggregate synced)
  simp only [bind_ok_iff] at ok
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := ok
  exact (blockHeader headerOk).trans <| (randao randaoOk).trans <|
    (eth1Data eth1Ok).trans (operations operationsOk)

end Kept

private theorem genesis {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) : ActivationExitOrder g.state := by
  obtain ⟨hash, time, deposits, ok⟩ := genesis
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    equal⟩ := initializeBeaconStateFromEth1_ok ok
  have first := Kept.foldlM (fun _ _ _ ok => Kept.genesisDeposit ok) depositedOk
  have second := Kept.foldlM (fun _ _ _ ok => Kept.activateAtGenesis ok) activatedOk
  rw [equal]
  exact (first.trans second) (by
    intro v member
    simp [emptyGenesisState] at member)

private theorem chainStep {first last : ForkedBeaconState preset}
    (holds : ActivationExitOrder first.state) (step : ChainStep config checks first last) :
    ActivationExitOrder last.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact processUpgrades_induction (property := fun post => ActivationExitOrder post.state)
      (fun before ok => Kept.upgradeNext ok before)
      (show ActivationExitOrder (⟨first.fork, advanced⟩ : ForkedBeaconState preset).state from
        Kept.advanceSlot slotOk holds) upgrades
  | block engine signed validate ok =>
    exact Kept.processBlock (applySignedBlock_ok ok).2.1 holds

theorem processJustificationAndFinalization (holds : ActivationExitOrder state)
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    ActivationExitOrder after :=
  Kept.of_data (congrArg (·.data) (processJustificationAndFinalization_keeps ok).2.2.2.2.2.1)
    holds

theorem processInactivityUpdates {altair : .altair ≤ fork}
    (holds : ActivationExitOrder state)
    (ok : Consensus.processInactivityUpdates config state altair = .ok after) :
    ActivationExitOrder after :=
  Kept.of_data (by rw [processInactivityUpdates_frame ok]) holds

theorem processRewardsAndPenalties (holds : ActivationExitOrder state)
    (ok : Consensus.processRewardsAndPenalties config state = .ok after) :
    ActivationExitOrder after :=
  Kept.of_data (by rw [processRewardsAndPenalties_frame ok]) holds

theorem processRegistryUpdates (holds : ActivationExitOrder state)
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    ActivationExitOrder after :=
  Kept.processRegistryUpdates ok holds

theorem processSlashings (holds : ActivationExitOrder state)
    (ok : Consensus.processSlashings state = .ok after) : ActivationExitOrder after :=
  Kept.slashings ok holds

theorem processEth1DataReset {before : fork < .hegota} (holds : ActivationExitOrder state)
    (ok : Consensus.processEth1DataReset before state = .ok after) : ActivationExitOrder after :=
  Kept.eth1Reset ok holds

theorem applyPendingDeposit {deposit : PendingDeposit} (holds : ActivationExitOrder state)
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    ActivationExitOrder after :=
  Kept.applyPendingDeposit ok holds

end ActivationExitOrder

/-- Every validator in a run from genesis activates no later than it exits. -/
theorem Run.activationExitOrder {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (genesis : Genesis (config := config) (checks := checks) first) :
    ActivationExitOrder last.state := by
  induction run with
  | nil => exact ActivationExitOrder.genesis genesis
  | snoc pre step ih => exact ih.chainStep step.chainStep

end EthLib.Consensus
