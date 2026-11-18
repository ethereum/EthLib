module

public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.ChainRoots
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.EpochPending

/-!
# Activation before exit

Every validator in a reachable state activates no later than it exits.

A new validator has no exit epoch.

An exit is only assigned to a validator whose activation epoch has passed.

An activation is only assigned to a validator whose exit is not yet assigned.

An activation is only assigned to a validator that is eligible by the finalized epoch.
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

/-- An assigned exit comes at least the seed lookahead and one epoch after the activation. -/
private def Gap (preset : Preset) (v : Validator) : Prop :=
  v.exitEpoch ≠ FAR_FUTURE_EPOCH →
    v.activationEpoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ v.exitEpoch.toNat

/-- Every validator with an assigned exit has the gap after its activation. -/
private def ExitGap (s : BeaconState preset fork) : Prop :=
  ∀ v ∈ s.validators.data, Gap preset v

private theorem gap_far {v : Validator} (gap : Gap preset v)
    (pending : v.activationEpoch = FAR_FUTURE_EPOCH) : v.exitEpoch = FAR_FUTURE_EPOCH := by
  refine Classical.byContradiction fun assigned => ?_
  have bound := gap assigned
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have := v.exitEpoch.toNat_lt
  rw [pending] at bound
  omega

private theorem active_le {v : Validator} {e : Epoch}
    (active : isActiveValidator v e = true) : v.activationEpoch ≤ e := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact active.1

private theorem slashable_le {v : Validator} {e : Epoch}
    (active : isSlashableValidator v e = true) : v.activationEpoch ≤ e := by
  simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact active.1.2

/-- An assigned exit waits the withdrawal delay before the validator can withdraw. -/
private def Delayed (config : Config) (v : Validator) : Prop :=
  v.exitEpoch ≠ FAR_FUTURE_EPOCH →
    v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
      v.withdrawableEpoch.toNat

/-- Every validator with an assigned exit waits the withdrawal delay. -/
private def ExitDelay (config : Config) (s : BeaconState preset fork) : Prop :=
  ∀ v ∈ s.validators.data, Delayed config v

/-- Every validator with an assigned activation was eligible by the finalized epoch. -/
private def Eligible (s : BeaconState preset fork) : Prop :=
  ∀ v ∈ s.validators.data, v.activationEpoch ≠ FAR_FUTURE_EPOCH →
    v.activationEligibilityEpoch ≤ s.finalizedCheckpoint.epoch

/-- A write of one validator keeps its eligibility below the bound, if it was below it. -/
private abbrev EligibleStep (bound : Epoch) (old v : Validator) : Prop :=
  (old.activationEpoch ≠ FAR_FUTURE_EPOCH → old.activationEligibilityEpoch ≤ bound) →
    v.activationEpoch ≠ FAR_FUTURE_EPOCH → v.activationEligibilityEpoch ≤ bound

/-- A step after which the order, the exit delay, the exit gap and the eligibility hold.

Each holds after it whenever it held before, and the step never lowers the finalized epoch. -/
private structure Kept (config : Config) {f g : Fork} (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop where
  order : ActivationExitOrder s → ActivationExitOrder t
  delay : ExitDelay config s → ExitDelay config t
  gap : ExitGap s → ExitGap t
  fin : s.finalizedCheckpoint.epoch ≤ t.finalizedCheckpoint.epoch
  eligible : Eligible s → Eligible t

private theorem eligibleStep_queue {bound : Epoch} {old : Validator} (epoch : Epoch)
    (queued : old.activationEligibilityEpoch = FAR_FUTURE_EPOCH) :
    EligibleStep bound old { old with activationEligibilityEpoch := epoch } := by
  intro held assigned
  have below := held assigned
  rw [queued] at below
  exact UInt64.le_trans (far_max epoch) below

private theorem addValidator_finalized {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei}
    (ok : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    after.finalizedCheckpoint = state.finalizedCheckpoint := by
  unfold addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
    rfl
  split at ok
  · cases ok
    rfl
  · cases ok

namespace Kept

private theorem refl (s : BeaconState preset fork) : Kept config s s :=
  ⟨id, id, id, UInt64.le_refl _, id⟩

private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : Kept config s t) (two : Kept config t u) :
    Kept config s u := ⟨two.1 ∘ one.1, two.2 ∘ one.2, two.3 ∘ one.3,
      UInt64.le_trans one.fin two.fin, two.eligible ∘ one.eligible⟩

private theorem of_data_le {g : Fork} {t : BeaconState preset g}
    (same : t.validators.data = state.validators.data)
    (finalized : state.finalizedCheckpoint.epoch ≤ t.finalizedCheckpoint.epoch) :
    Kept config state t :=
  ⟨fun h v member => h v (same ▸ member), fun h v member => h v (same ▸ member),
    fun h v member => h v (same ▸ member), finalized,
    fun h v member assigned => UInt64.le_trans (h v (same ▸ member) assigned) finalized⟩

private theorem of_data {g : Fork} {t : BeaconState preset g}
    (same : t.validators.data = state.validators.data := by rfl)
    (finalized : t.finalizedCheckpoint = state.finalizedCheckpoint := by rfl) :
    Kept config state t :=
  of_data_le same (by rw [finalized]; exact UInt64.le_refl _)

private theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → Kept config s t) {xs : List α}
    (ok : xs.foldlM step state = .ok after) : Kept config state after :=
  foldlM_ok_invariant (Kept config state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (refl state) ok

private theorem setValidatorAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old)
    (set : state.setValidatorAt i v = .ok after)
    (keeps : old.activationEpoch ≤ old.exitEpoch → v.activationEpoch ≤ v.exitEpoch)
    (delays : Delayed config old → Delayed config v)
    (gaps : Gap preset old → Gap preset v)
    (eligibles : EligibleStep state.finalizedCheckpoint.epoch old v) :
    Kept config state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  have mem := oldEq ▸ Array.getElem_mem inside
  refine ⟨fun h w member => ?_, fun h w member => ?_, fun h w member => ?_, UInt64.le_refl _,
    fun h w member => ?_⟩ <;>
    simp only [BeaconState.putValidator, RootedForkList.data_set] at member <;>
    rcases Array.mem_or_eq_of_mem_set member with member | rfl
  · exact h w member
  · exact keeps (h old mem)
  · exact h w member
  · exact delays (h old mem)
  · exact h w member
  · exact gaps (h old mem)
  · exact h w member
  · exact eligibles (h old mem)

private theorem setValidator {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old)
    (set : state.setValidator i v = .ok after)
    (keeps : old.activationEpoch ≤ old.exitEpoch → v.activationEpoch ≤ v.exitEpoch)
    (delays : Delayed config old → Delayed config v)
    (gaps : Gap preset old → Gap preset v)
    (eligibles : EligibleStep state.finalizedCheckpoint.epoch old v) :
    Kept config state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) keeps delays gaps eligibles

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v)
    (pending : v.exitEpoch = FAR_FUTURE_EPOCH) (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH)
    (finalized : after.finalizedCheckpoint = state.finalizedCheckpoint) :
    Kept config state after := by
  refine ⟨fun h w member => ?_, fun h w member => ?_, fun h w member => ?_,
    by rw [finalized]; exact UInt64.le_refl _, fun h w member => ?_⟩ <;>
    rw [added] at member <;> rcases Array.mem_push.mp member with member | rfl
  · exact h w member
  · rw [pending]; exact far_max _
  · exact h w member
  · exact fun assigned => absurd pending assigned
  · exact h w member
  · exact fun assigned => absurd pending assigned
  · rw [finalized]; exact h w member
  · exact fun assigned => absurd unassigned assigned

private theorem initiateValidatorExit {i : ValidatorIndex} {v : Validator}
    (found : getValidator state i = .ok v)
    (assigned : v.activationEpoch ≤ getCurrentEpoch state)
    (ok : Consensus.initiateValidatorExit config state i = .ok after) :
    Kept config state after := by
  obtain ⟨old, read, unchanged | ⟨_, queued, _, _, queue, delayed, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have equal := Except.ok.inj (read.symm.trans found)
    have same := (exitQueue_validators queue).1
    exact (of_data (congrArg (·.data) same) (frame_exitQueue queue).finalized).trans <|
      setValidator (config := config) ((getValidator_of_validators_eq same i).trans read) set
        (fun _ => by
          have later := exitQueue_lt queue
          have bound := UInt64.le_iff_toNat_le.mp assigned
          change old.activationEpoch.toNat ≤ UInt64.toNat _
          rw [equal]
          dsimp only at *
          omega)
        -- The new exit waits exactly the withdrawal delay.
        (fun _ _ => by
          have sum := (Uint64.addChecked_ok_iff.mp delayed).2
          dsimp only
          omega)
        -- The new exit is beyond the seed lookahead of the current epoch.
        (fun _ _ => by
          have later := exitQueue_lt queue
          have bound := UInt64.le_iff_toNat_le.mp assigned
          subst equal
          dsimp only at *
          omega)
        (fun held => held)

private theorem increaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state i amount = .ok after) :
    Kept config state after :=
  of_data (congrArg (·.data) (increaseBalance_validators ok)) (frame_increaseBalance ok).finalized

private theorem decreaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state i amount = .ok after) :
    Kept config state after :=
  of_data (congrArg (·.data) (decreaseBalance_validators ok)) (frame_decreaseBalance ok).finalized

private theorem slashValidator {i : ValidatorIndex} {v : Validator}
    {whistleblower : Option ValidatorIndex}
    (found : getValidator state i = .ok v)
    (assigned : v.activationEpoch ≤ getCurrentEpoch state)
    (ok : Consensus.slashValidator config state i whistleblower = .ok after) :
    Kept config state after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, read, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (initiateValidatorExit found assigned exited).trans
    (setValidator (config := config) read set (fun h => h) (fun h assigned => by
      -- Slashing only raises the withdrawable epoch.
      refine Nat.le_trans (h assigned) (UInt64.le_iff_toNat_le.mp ?_)
      rw [UInt64.max_def]
      split
      · assumption
      · exact UInt64.le_refl _) (fun g => g) (fun held => held))
  have second := (of_data (config := config) (state := marked)
    (t := { marked with slashings })).trans
    ((decreaseBalance lowered).trans ((increaseBalance raised).trans (increaseBalance paid)))
  apply (first.trans second).trans
  split <;> exact of_data

private theorem processProposerSlashing {slashing : ProposerSlashing}
    (ok : Consensus.processProposerSlashing config checks state slashing = .ok after) :
    Kept config state after := by
  simp only [Consensus.processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, v, found, _, slashable, _, _, _, _, slashed⟩ := ok
  exact slashValidator found (slashable_le slashable) slashed

private theorem slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (ok : Consensus.slashIfSlashable config step index = .ok next) :
    Kept config step.1 next.1 := by
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
    Kept config state after := by
  simp only [Consensus.processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step => Kept config state step.1)
    (fun _ _ _ before ok => before.trans (slashIfSlashable ok))
    (show Kept config state (state, false).1 from refl state) folded

private theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    Kept config state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨v, found, _, active, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit found (active_le active) exited

private theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    Kept config state after := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · exact refl _
  · exact increaseBalance ok
  · exact append (addValidatorToRegistry_validators_eq_push ok) rfl rfl
      (addValidator_finalized ok)

private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : Kept config state after := by
  rcases applyDeposit_cases ok with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, ok⟩
  · exact refl _
  · exact of_data
  · exact (append (addValidatorToRegistry_validators_eq_push added) rfl rfl
      (addValidator_finalized added)).trans of_data
  · exact applyPendingDeposit ok

private theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    Kept config state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_data (state := state)
    (t := { state with eth1DepositIndex := fun _ => next })).trans (applyDeposit credited)

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    Kept config state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator (config := config) found set id (by unfold Delayed; exact id)
    (by unfold Gap; exact id) (fun held => held)

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    Kept config state after := by
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
    Kept config state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (setValidator (config := config) found set id id id (fun held => held)).trans
    (queueExcessActiveBalance queued)

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    Kept config state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact of_data (congrArg (·.data) (requestPartialWithdrawal_kept ok).1)
        (frame_requestPartialWithdrawal ok).finalized
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
      .ok after) : Kept config state after := by
  obtain ⟨exitEpoch, withdrawable, rest, written, _, churn, delayed, set, _, rfl⟩ :=
    queueConsolidation_steps ok
  exact (of_data (config := config) (state := state)
    (t := { state with
      consolidationBalanceToConsume := fun _ => rest
      earliestConsolidationEpoch := fun _ => exitEpoch }) rfl).trans <|
    (setValidator (config := config) (old := source)
      (getValidator_eq_ok_iff.mpr (by simpa using found)) set (fun _ => by
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
        omega)
      -- The source's new exit waits exactly the withdrawal delay.
      (fun _ _ => by
        have sum := (Uint64.addChecked_ok_iff.mp delayed).2
        dsimp only at *
        omega)
      -- The source's new exit is beyond the seed lookahead of the current epoch.
      (fun _ _ => by
        cases first : computeActivationExitEpoch preset (getCurrentEpoch state) with
        | error =>
          simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError,
            bind, Except.bind] at churn
        | ok firstEpoch =>
          have early := UInt64.le_iff_toNat_le.mp
            (computeConsolidationEpochAndUpdateChurn_first first churn).1
          have eq := (computeActivationExitEpoch_ok_iff.mp first).2
          have bound := UInt64.le_iff_toNat_le.mp assigned
          change source.activationEpoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
            UInt64.toNat _
          dsimp only at *
          omega)
      (fun held => held)).trans of_data

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    Kept config state after := by
  rcases consolidationRequest_cases ok with rfl | ⟨_, _, _, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact refl _
  · exact switchToCompoundingValidator switched
  -- The source is active, so its activation epoch is at most the current one.
  · exact queueConsolidation accepted.sourceAt (active_le accepted.sourceActive) queued

private theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    Kept config state after :=
  of_data (congrArg (·.data) (processDepositRequest_ok ok).2.1)
    (frame_processDepositRequest ok).finalized

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    Kept config state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations)

private theorem genesisDeposit {before : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (ok : Consensus.genesisDeposit config checks before leaves state entry = .ok after) :
    Kept config state after := by
  simp only [Consensus.genesisDeposit, bind_ok_iff] at ok
  obtain ⟨root, _, deposited⟩ := ok
  exact (of_data (state := state)
    (t := { state with
      eth1Data := fun _ => { state.eth1Data before with depositRoot := root } })).trans
    (processDeposit deposited)

private theorem activateAtGenesis {index : Nat}
    (ok : Consensus.activateAtGenesis state index = .ok after) :
    Kept config state after := by
  simp only [Consensus.activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, _, _, set⟩ := ok
  apply setValidatorAt found set
  · split
    · intro _; change (0 : UInt64) ≤ _; exact UInt64.zero_le
    · exact id
  · split <;> exact id
  · split
    · intro gap assigned
      have bound := gap assigned
      dsimp only at *
      change 0 + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ _
      omega
    · exact id
  · split
    · intro _ _; change (0 : UInt64) ≤ _; exact UInt64.zero_le
    · exact id

private theorem updateRegistryEntry {index : Nat}
    (ok : Consensus.updateRegistryEntry config state index = .ok after) :
    Kept config state after := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queuedOk, marked, markedOk, ok⟩ := ok
  have epochs : queued.activationEpoch = v.activationEpoch ∧ queued.exitEpoch = v.exitEpoch ∧
      queued.withdrawableEpoch = v.withdrawableEpoch := by
    unfold queueForActivation at queuedOk
    split at queuedOk
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
      obtain ⟨_, _, rfl⟩ := queuedOk
      exact ⟨rfl, rfl, rfl⟩
    · cases queuedOk; exact ⟨rfl, rfl, rfl⟩
  have eligibles : EligibleStep state.finalizedCheckpoint.epoch v queued := by
    unfold queueForActivation at queuedOk
    split at queuedOk
    · rename_i queue
      simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
      obtain ⟨_, _, rfl⟩ := queuedOk
      simp only [isEligibleForActivationQueue, Bool.and_eq_true, beq_iff_eq] at queue
      exact eligibleStep_queue _ queue.1
    · cases queuedOk; exact fun held => held
  have first := setValidatorAt (config := config) found markedOk
    (by simpa only [epochs.1, epochs.2.1] using id)
    (by simpa only [Delayed, epochs.2.1, epochs.2.2] using id)
    (by simpa only [Gap, epochs.1, epochs.2.1] using id) eligibles
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
    Kept config state after := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · rename_i queue
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    simp only [isEligibleForActivationQueue, Bool.and_eq_true, beq_iff_eq] at queue
    exact setValidatorAt found set id id id (eligibleStep_queue _ queue.1)
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
    apply setValidatorAt found (liftAccessor_ok.mp ok) _ id _ _
    · intro h
      change epoch ≤ v.exitEpoch
      rw [exit_pending h (activationEpoch_of_isEligibleForActivation eligible)]
      exact far_max _
    · intro gap assigned
      exact absurd (gap_far gap (activationEpoch_of_isEligibleForActivation eligible)) assigned
    · intro _ _
      simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq] at eligible
      exact eligible.1
  · cases ok; exact refl _

private theorem foldActivateValidator :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ v, getValidator state index = .ok v ∧
        v.activationEpoch = FAR_FUTURE_EPOCH ∧
          v.activationEligibilityEpoch ≤ state.finalizedCheckpoint.epoch) →
      indices.foldlM activateValidator state = .ok after → Kept config state after
  | [], _, _, _, _, ok => by cases ok; exact refl _
  | index :: rest, state, after, unique, eligible, ok => by
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, tail⟩ := ok
    obtain ⟨v, found, far, low⟩ := eligible index List.mem_cons_self
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨old, read, _, _, set⟩ := first
    have equal := Except.ok.inj (read.symm.trans found)
    have farOld : old.activationEpoch = FAR_FUTURE_EPOCH := by rw [equal]; exact far
    have kept := setValidator (config := config) read set (fun h => by
      change _ ≤ old.exitEpoch
      rw [exit_pending h farOld]
      exact far_max _) id (fun gap assigned =>
        absurd (gap_far gap farOld) assigned) (fun _ _ => by subst equal; exact low)
    refine kept.trans (foldActivateValidator restUnique (fun other member => ?_) tail)
    have distinct : other ≠ index := fun same => absent (same ▸ member)
    obtain ⟨w, read, pending, lower⟩ := eligible other (List.mem_cons_of_mem _ member)
    exact ⟨w, (getValidator_setValidator_of_ne set distinct).trans read, pending,
      UInt64.le_trans lower kept.fin⟩

private theorem processRegistryUpdates
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    Kept config state after := by
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
  refine ⟨v, ?_, activationEpoch_of_isEligibleForActivation eligible, ?_⟩
  swap
  · simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq] at eligible
    exact eligible.1
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : index.toNat = position := by
    have bound : position < UInt64.size := by change position < 2 ^ 64; omega
    rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' bound]
  simp [getValidator, exact, found]

private theorem processPendingDeposits {electra : .pectra ≤ fork}
    (ok : Consensus.processPendingDeposits config checks state electra = .ok after) :
    Kept config state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  exact (foldlM (fun _ _ _ => applyPendingDeposit) folded).trans of_data

/-- A validator that is not yet activated, put back into the queue, stays not activated. -/
private theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (waiting : ∀ v, getValidator state index = .ok v → v.activationEpoch = FAR_FUTURE_EPOCH)
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    Kept config state after := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact (of_data (state := state)).trans <|
    (setValidator (config := config) (old := v) (by exact found) set₂ id id id
      (fun _ assigned => absurd (waiting v found) assigned)).trans of_data

/-- Putting a validator back into the queue leaves the activation epoch of each validator. -/
private theorem queuePreActivation_activation {electra : .pectra ≤ fork}
    {index other : ValidatorIndex} {w : Validator}
    (ok : Consensus.queuePreActivation state electra index = .ok after)
    (found : getValidator after other = .ok w) :
    ∃ v, getValidator state other = .ok v ∧ v.activationEpoch = w.activationEpoch := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, readV, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  by_cases same : other = index
  · subst same
    have written := (getValidator_setValidator_self set₂).symm.trans found
    exact ⟨v, readV, by rw [← Except.ok.inj written]⟩
  · exact ⟨w, (getValidator_setValidator_of_ne set₂ same).symm.trans found, rfl⟩

/-- The validators put back into the queue are those with no activation epoch yet. -/
private theorem preActivation_waiting {s : BeaconState preset .pectra} {index : ValidatorIndex}
    (member : index ∈ preActivationIndices s) {v : Validator}
    (found : getValidator s index = .ok v) : v.activationEpoch = FAR_FUTURE_EPOCH := by
  obtain ⟨⟨w, i⟩, sorted, rfl⟩ := List.mem_map.mp member
  rw [List.mem_mergeSort] at sorted
  obtain ⟨member, waiting⟩ := List.mem_filter.mp sorted
  have at_i : s.validators.data[i]? = some w := by
    simpa using List.mem_zipIdx_iff_getElem?.mp member
  have inside := (Array.getElem?_eq_some_iff.mp at_i).1
  have small : s.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (s.validators.bound (by decide)) (UInt64.toNat_lt _)
  have exact : i.toUInt64.toNat = i := by
    have bound : i < UInt64.size := by change i < 2 ^ 64; omega
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' bound]
  have read : getValidator s i.toUInt64 = .ok w := by simp [getValidator, exact, at_i]
  have same := Except.ok.inj (read.symm.trans found)
  subst same
  simpa using waiting

private theorem foldQueuePreActivation {electra : .pectra ≤ fork} :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      (∀ index ∈ indices, ∀ v, getValidator state index = .ok v →
        v.activationEpoch = FAR_FUTURE_EPOCH) →
      indices.foldlM (fun s i => Consensus.queuePreActivation s electra i) state = .ok after →
      Kept config state after
  | [], _, _, _, ok => by cases ok; exact refl _
  | index :: rest, state, after, waiting, ok => by
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, tail⟩ := ok
    refine (queuePreActivation (config := config) (waiting index List.mem_cons_self) first).trans
      (foldQueuePreActivation (fun other member w found => ?_) tail)
    obtain ⟨v, read, same⟩ := queuePreActivation_activation first found
    exact same ▸ waiting other (List.mem_cons_of_mem _ member) v read

private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    Kept config pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToAltair_spec upgraded).1
      (upgradeFrame_upgradeToAltair upgraded).finalized
  · subst ok; exact of_data
  · subst ok; exact of_data
  · subst ok; exact of_data
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := upgraded
    have tail := foldlM (config := config) (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok; exact refl _
      · cases ok; exact refl _) compounded
    have head := foldQueuePreActivation (config := config) (electra := by decide)
      (fun _ member _ found => preActivation_waiting member found) queued
    exact (of_data (state := state)).trans (head.trans tail)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToFulu_spec upgraded).1 (upgradeFrame_upgradeToFulu upgraded).finalized
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToGloas_spec upgraded).1 (upgradeFrame_upgradeToGloas upgraded).finalized
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact of_data (upgradeHezeFields_lists _).1

private theorem processEffectiveBalanceUpdates
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    Kept config state after := by
  apply foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact setValidatorAt found set id id id (fun held => held)

/-- Only three epoch stages change the validators, and each of them keeps the order.

Justification is the one stage that can move the finalized epoch, so it is left out. -/
private theorem edge {stage : EpochStage} (later : stage ≠ .justification)
    (edge : EpochStage.Edge config checks stage state after) : Kept config state after := by
  have finalized := (EpochStage.Edge.frame edge later).finalized
  cases stage
  case registry => exact processRegistryUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits edge
    · exact edge ▸ refl _
  case effectiveBalances => exact processEffectiveBalanceUpdates edge
  case justification => exact absurd rfl later
  all_goals exact of_data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)) finalized

/-- Justification keeps the validators.

From a valid state it does not lower the finalized epoch. -/
private theorem justification (valid : Invariant state)
    (ok : EpochStage.Edge config checks .justification state after) : Kept config state after := by
  obtain ⟨_, finalized, _, _, validators, _⟩ :=
    processJustificationAndFinalization_invariant valid.ordered valid.settled ok
  exact of_data_le (congrArg (·.data) validators) finalized

/-- An epoch keeps the order from a valid state: justification first, then the other stages. -/
private theorem processEpoch (valid : Invariant state)
    (ok : Consensus.processEpoch config checks state = .ok after) : Kept config state after := by
  have trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.justification :: EpochStage.epochStages.tail) state after :=
    EpochTrace.run_ok_iff.mp ((processEpoch_eq_run config checks state).symm.trans ok)
  cases trace with
  | cons first rest =>
    have later : ∀ k ∈ EpochStage.epochStages.tail, k ≠ .justification := by
      intro k member
      cases k
      case justification =>
        simp [EpochStage.epochStages, EpochStage.prefixStages, EpochStage.middleStages,
          EpochStage.tailStages] at member
      all_goals nofun
    refine (justification valid (EpochStage.action_cases.mp first)).trans ?_
    refine rest.transport (Kept config) refl (fun a b => a.trans b) fun k member _ _ computed => ?_
    exact edge (later k member) (EpochStage.action_cases.mp computed)

private theorem advanceSlot (valid : Invariant state)
    (ok : Consensus.advanceSlot config checks state = .ok after) :
    Kept config state after := by
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have frame := frame_processSlot cachedOk
  have first : Kept config state cached := of_data (by rw [cachedEq]) frame.finalized
  have second : Kept config cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch (frame.invariant valid) epochedOk
    · cases epochedOk; exact refl _
  exact first.trans (second.trans of_data)

private theorem blockHeader {block : BeaconBlock preset fork}
    (ok : processBlockHeader state block = .ok after) : Kept config state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact of_data

private theorem randao {body : BeaconBlockBody preset fork}
    (ok : processRandao config checks state body = .ok after) : Kept config state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact of_data

private theorem eth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : processEth1Data before state body = .ok after) : Kept config state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  exact of_data (by rw [← rest]) (by rw [← rest])

/-- A block keeps the order, step by step of the block.

Each step that keeps the validators keeps the order, and so does each validator write. -/
private theorem processBlock {block : BeaconBlock preset fork}
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    Kept config state after := by
  have keep {a b : BeaconState preset fork} (frame : BlockFrame a b)
      (same : b.validators = a.validators) : Kept config a b :=
    of_data (congrArg (·.data) same) frame.finalized
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : Kept config state input :=
    OperationsInput.step_of (Kept config) refl (fun one two => one.trans two)
      (fun _ paid => processParentExecutionPayload_step_of (Kept config) refl
        (fun one two => one.trans two)
        keep processWithdrawalRequest processConsolidationRequest paid)
      blockHeader
      (fun _ executed => of_data (congrArg (·.data) (processBlockExecution_validators executed))
        (frame_processBlockExecution executed).finalized)
      randao (fun _ voted => eth1Data voted) started
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of (Kept config) refl (fun one two => one.trans two) processDeposit
      processVoluntaryExit processBlsToExecutionChange processExecutionRequests
      (fun paid => by rw [processPayloadAttestation_eq paid]; exact refl _) operated
  have tail : Kept config last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact of_data
    · cases synced
      exact refl _
  exact head.trans <| (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposersOk).trans <|
    (foldlM (fun _ _ _ ok => processAttesterSlashing ok) slashingsOk).trans <|
    (foldlM (fun _ _ _ ok => of_data (congrArg (·.data) (processAttestation_registry ok).1)
      (frame_processAttestation ok).finalized) attestedOk).trans <| rest.trans tail

end Kept

/-- All four properties that the walk carries. -/
private def Holds (config : Config) (s : BeaconState preset fork) : Prop :=
  ExitGap s ∧ ActivationExitOrder s ∧ ExitDelay config s ∧ Eligible s

private theorem genesis {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    Holds config g.state := by
  obtain ⟨hash, time, deposits, ok⟩ := genesis
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    equal⟩ := initializeBeaconStateFromEth1_ok ok
  have first := Kept.foldlM (config := config) (fun _ _ _ ok => Kept.genesisDeposit ok) depositedOk
  have second := Kept.foldlM (config := config) (fun _ _ _ ok => Kept.activateAtGenesis ok)
    activatedOk
  rw [equal]
  -- The empty state before the deposits has no validator.
  exact ⟨(first.trans second).3 (by intro v member; simp [emptyGenesisState] at member),
    (first.trans second).1 (by intro v member; simp [emptyGenesisState] at member),
    (first.trans second).2 (by intro v member; simp [emptyGenesisState] at member),
    (first.trans second).eligible (by intro v member; simp [emptyGenesisState] at member)⟩

private theorem chainStep {first last : ForkedBeaconState preset}
    (valid : Invariant first.state) (holds : Holds config first.state)
    (step : ChainStep config checks first last) : Holds config last.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have slot := Kept.advanceSlot valid slotOk
    exact processUpgrades_induction
      (property := fun post => Holds config post.state)
      (fun before ok => ⟨(Kept.upgradeNext ok).3 before.1, (Kept.upgradeNext ok).1 before.2.1,
        (Kept.upgradeNext ok).2 before.2.2.1, (Kept.upgradeNext ok).eligible before.2.2.2⟩)
      (show Holds config (⟨first.fork, advanced⟩ : ForkedBeaconState preset).state from
        ⟨slot.3 holds.1, slot.1 holds.2.1, slot.2 holds.2.2.1, slot.eligible holds.2.2.2⟩)
      upgrades
  | block engine signed validate ok =>
    have block := Kept.processBlock (applySignedBlock_ok ok).2.1
    exact ⟨block.3 holds.1, block.1 holds.2.1, block.2 holds.2.2.1,
      block.eligible holds.2.2.2⟩

/-- Every epoch stage keeps the order. -/
theorem _root_.EthLib.Consensus.EpochStage.Edge.activationExitOrder {k : EpochStage}
    {s t : BeaconState preset fork} (edge : EpochStage.Edge config checks k s t)
    (holds : ActivationExitOrder s) : ActivationExitOrder t := by
  by_cases justification : k = .justification
  · subst justification
    intro v member
    exact holds v ((congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)) ▸ member)
  · exact (Kept.edge justification edge).1 holds

/-- An epoch stage preserves the withdrawal delay of every assigned exit. -/
theorem _root_.EthLib.Consensus.EpochStage.Edge.exit_withdrawable_delay {k : EpochStage}
    {s t : BeaconState preset fork} (edge : EpochStage.Edge config checks k s t)
    (holds : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat) :
    ∀ (i : Nat) (v : Validator), t.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat := by
  have before : ExitDelay config s := by
    intro v member
    obtain ⟨i, inside, equal⟩ := Array.mem_iff_getElem.mp member
    exact holds i v (by simp [← equal, inside])
  intro i v found
  by_cases justification : k = .justification
  · subst justification
    exact before v ((congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)) ▸
      Array.mem_of_getElem? found)
  · exact (Kept.edge justification edge).2 before v (Array.mem_of_getElem? found)

theorem applyPendingDeposit {deposit : PendingDeposit} (holds : ActivationExitOrder state)
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    ActivationExitOrder after :=
  (Kept.applyPendingDeposit ok).1 holds

end ActivationExitOrder

/-- Every validator in a run from genesis activates no later than it exits.

Each one with an assigned exit can withdraw only the withdrawal delay after that exit. -/
private theorem Run.activationExitDelay {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (genesis : Genesis (config := config) (checks := checks) first) :
    ActivationExitOrder.Holds config last.state := by
  have valid := Genesis.invariant genesis
  induction run with
  | nil => exact ActivationExitOrder.genesis genesis
  | snoc pre step ih => exact ActivationExitOrder.chainStep (pre.invariant valid) ih step.chainStep

/-- Every validator in a run from genesis activates no later than it exits. -/
theorem Run.activationExitOrder {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (genesis : Genesis (config := config) (checks := checks) first) :
    ActivationExitOrder last.state :=
  (run.activationExitDelay genesis).2.1

/-- From genesis, an assigned exit comes one epoch and the seed lookahead after the activation. -/
theorem Run.exit_activation_gap {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (genesis : Genesis (config := config) (checks := checks) first) :
    ∀ (i : Nat) (v : Validator), last.state.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.activationEpoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ v.exitEpoch.toNat := by
  intro i v found
  exact (run.activationExitDelay genesis).1 v (Array.mem_of_getElem? found)

/-- Each assigned exit reached from genesis waits the withdrawal delay. -/
theorem Run.exit_withdrawable_delay {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (genesis : Genesis (config := config) (checks := checks) first) :
    ∀ (i : Nat) (v : Validator), last.state.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat := by
  intro i v found
  exact (run.activationExitDelay genesis).2.2.1 v (Array.mem_of_getElem? found)

/-- From genesis, a validator with an assigned activation was eligible by the finalized epoch. -/
theorem Run.eligibility_le_finalized {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (genesis : Genesis (config := config) (checks := checks) first) :
    ∀ (i : Nat) (v : Validator), last.state.validators.data[i]? = some v →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH →
        v.activationEligibilityEpoch ≤ last.state.finalizedCheckpoint.epoch := by
  intro i v found
  exact (run.activationExitDelay genesis).2.2.2 v (Array.mem_of_getElem? found)

end EthLib.Consensus
