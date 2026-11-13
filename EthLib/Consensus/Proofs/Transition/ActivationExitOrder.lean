module

public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Totality.EpochBeforeAltair

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
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · exact refl _
  · exact increaseBalance ok
  · exact append (addValidatorToRegistry_validators_eq_push ok) rfl

private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : Kept state after := by
  rcases applyDeposit_cases ok with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, ok⟩
  · exact refl _
  · exact of_data
  · exact (append (addValidatorToRegistry_validators_eq_push added) rfl).trans of_data
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

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    Kept state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact of_data (congrArg (·.data) (requestPartialWithdrawal_kept ok).1)
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

private theorem processPendingDeposits {electra : .pectra ≤ fork}
    (ok : Consensus.processPendingDeposits config checks state electra = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  exact (foldlM (fun _ _ _ => applyPendingDeposit) folded).trans of_data

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

/-- Only three epoch stages change the validators, and each of them keeps the order. -/
private theorem edge {stage : EpochStage}
    (edge : EpochStage.Edge config checks stage state after) : Kept state after := by
  cases stage
  case registry => exact processRegistryUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits edge
    · exact edge ▸ refl _
  case effectiveBalances => exact processEffectiveBalanceUpdates edge
  all_goals exact of_data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

private theorem processEpoch (ok : Consensus.processEpoch config checks state = .ok after) :
    Kept state after :=
  (processEpoch_trace ok).transport Kept refl (fun a b => a.trans b)
    (fun _ _ _ _ computed => edge (EpochStage.action_cases.mp computed))

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

/-- A block keeps the order, step by step of the block.

Each step that keeps the validators keeps the order, and so does each validator write. -/
private theorem processBlock {block : BeaconBlock preset fork}
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    Kept state after := by
  have keep {a b : BeaconState preset fork} (_ : BlockFrame a b)
      (same : b.validators = a.validators) : Kept a b := of_data (congrArg (·.data) same)
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : Kept state input :=
    OperationsInput.step_of Kept refl (fun one two => one.trans two)
      (fun _ paid => processParentExecutionPayload_step_of Kept refl (fun one two => one.trans two)
        keep processWithdrawalRequest processConsolidationRequest paid)
      blockHeader
      (fun _ executed => of_data (congrArg (·.data) (processBlockExecution_validators executed)))
      randao (fun _ voted => eth1Data voted) started
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of Kept refl (fun one two => one.trans two) processDeposit
      processVoluntaryExit processBlsToExecutionChange processExecutionRequests
      (fun paid => by rw [processPayloadAttestation_eq paid]; exact refl _) operated
  have tail : Kept last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact of_data
    · cases synced
      exact refl _
  exact head.trans <| (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposersOk).trans <|
    (foldlM (fun _ _ _ ok => processAttesterSlashing ok) slashingsOk).trans <|
    (foldlM (fun _ _ _ ok => of_data (congrArg (·.data) (processAttestation_registry ok).1))
      attestedOk).trans <| rest.trans tail

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

/-- Every epoch stage keeps the order. -/
theorem _root_.EthLib.Consensus.EpochStage.Edge.activationExitOrder {k : EpochStage}
    {s t : BeaconState preset fork} (edge : EpochStage.Edge config checks k s t)
    (holds : ActivationExitOrder s) : ActivationExitOrder t :=
  Kept.edge edge holds

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
