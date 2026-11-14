module

public import EthLib.Consensus.Proofs.Transition.Totality.Bound
public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
public import EthLib.Consensus.Transition.StateTransition
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.PayloadTimeliness
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.Transition.BuilderRequests
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Execution
import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.ParentPayload
import EthLib.Consensus.Proofs.Transition.Payload
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: a block raises the slashed balances by at most the balances not yet slashed

A slashing adds the effective balance of its validator to the slashed balances of its epoch.

Only a validator that is not yet slashed can be slashed, and it stays slashed.

A block keeps the effective balance of each validator that was there before it.

So the slashed balances plus the effective balances not yet slashed do not grow in a block.

The slashed balances then rise by at most the effective balances not yet slashed before it.

They also rise by at most the largest cap for each validator that the slashings of a block name.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}

/-- The sum of the effective balances of the validators not slashed, below a position. -/
def unslashedBalanceSum (state : BeaconState preset fork) (count : Nat) : Nat :=
  ((List.range count).map fun j =>
    ((state.validators.data[j]?).map fun validator =>
      if validator.slashed then 0 else validator.effectiveBalance.toNat).getD 0).sum

/-! ## Steps that keep the slashed balances -/

section Same

private theorem same_setValidatorAt {s t : BeaconState preset fork} {i : Nat} {v : Validator}
    (ok : s.setValidatorAt i v = .ok t) : t.slashings = s.slashings := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

private theorem same_setValidator {s t : BeaconState preset fork}
    {i : ValidatorIndex} {v : Validator}
    (ok : s.setValidator i v = .ok t) : t.slashings = s.slashings :=
  same_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem same_setBalance {s t : BeaconState preset fork} {i : ValidatorIndex} {b : Gwei}
    (ok : s.setBalance i b = .ok t) : t.slashings = s.slashings := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  rfl

private theorem same_increase {s t : BeaconState preset fork} {i : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s i amount = .ok t) : t.slashings = s.slashings :=
  same_setBalance (increaseBalance_ok ok).choose_spec

private theorem same_decrease {s t : BeaconState preset fork} {i : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s i amount = .ok t) : t.slashings = s.slashings :=
  same_setBalance (decreaseBalance_ok ok).choose_spec

private theorem same_exit {s t : BeaconState preset fork}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    t.slashings = s.slashings := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · rfl
  · obtain ⟨_, _, queued⟩ := exitQueue_eq queue
    rw [same_setValidator set, queued]

private theorem same_exitChurn {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {balance : Gwei} {epoch : Epoch}
    (ok : computeExitEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    t.slashings = s.slashings := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  cases ok
  rfl

private theorem same_consolidationChurn {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {balance : Gwei} {epoch : Epoch}
    (ok : computeConsolidationEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    t.slashings = s.slashings := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  cases ok
  rfl

private theorem same_partialWithdrawal {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index validator amount owed = .ok t) :
    t.slashings = s.slashings := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    have kept := same_exitChurn churned
    exact kept
  · cases ok
    rfl

private theorem same_withdrawalRequest {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    t.slashings = s.slashings := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · rfl
  · exact same_exit exited
  · exact same_partialWithdrawal withdrawn

private theorem same_depositRequest {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : t.slashings = s.slashings := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  rfl

private theorem same_excess {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : t.slashings = s.slashings := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    have kept := same_setBalance set
    exact kept
  · cases ok
    rfl

private theorem same_compounding {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : t.slashings = s.slashings := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, _, set, queued⟩ := ok
  exact (same_excess queued).trans (same_setValidator set)

private theorem same_queueConsolidation {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    t.slashings = s.slashings := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churn, _, _, marked, set, pending, appended, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  exact (same_setValidator set).trans (same_consolidationChurn churn)

private theorem same_consolidationRequest {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    t.slashings = s.slashings := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; rfl)
    | exact same_compounding (liftAccessor_ok.mp ok)
    | exact same_queueConsolidation ok

private theorem same_withdrawals {s t : BeaconState preset fork} {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) : t.slashings = s.slashings := by
  have expected {a b : BeaconState preset fork} {expected : ExpectedWithdrawals}
      (applied : applyExpectedWithdrawals a capella expected = .ok b) :
      b.slashings = a.slashings := by
    apply applyExpectedWithdrawals_of_setters (fun a b => b.slashings = a.slashings)
      (fun _ => rfl) (fun one two => two.trans one)
      (fun withdrawn => by rw [applyWithdrawal_eq withdrawn]) _ _ _ _ _ _ applied
    all_goals exact fun _ _ => rfl
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact expected applied
    · cases ok
      rfl
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact expected applied

private theorem same_blockExecution {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.slashings = s.slashings := by
  have payload {a b : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (paid : processExecutionPayload config engine a body execution = .ok b) :
      b.slashings = a.slashings := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    rfl
  unfold processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    have kept := same_withdrawals withdrawn
    exact kept
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (payload paid).trans (same_withdrawals withdrawn)
  · dsimp only at ok
    split at ok
    · exact payload ok
    · cases ok
      rfl

/-- A fold whose every step keeps the slashed balances keeps them. -/
private theorem same_foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → b.slashings = a.slashings) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) :
    b.slashings = a.slashings :=
  foldlM_ok_invariant (fun c => c.slashings = a.slashings)
    (fun _ _ _ before ok => (each _ _ _ ok).trans before) rfl computed

private theorem same_parentPayload {s t : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks s gloas body = .ok t) :
    t.slashings = s.slashings := by
  rcases processParentExecutionPayload_ok ok with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · rfl
  have settledSame : settled.slashings = s.slashings := by
    rw [settleParentPayment_eq settledOk]
  have builders := same_foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_eq ok
    rfl) buildersOk
  have exits := same_foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_eq ok
    rfl) exitsOk
  exact exits.trans <| builders.trans <|
    (same_foldlM (fun _ _ _ => same_consolidationRequest) consolidationsOk).trans <|
    (same_foldlM (fun _ _ _ => same_withdrawalRequest) withdrawalsOk).trans <|
    (same_foldlM (fun _ _ _ => same_depositRequest) depositsOk).trans settledSame

private theorem same_add {s t : BeaconState preset fork} {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    t.slashings = s.slashings := by
  unfold addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
    rfl
  · split at ok <;> cases ok
    rfl

private theorem same_deposit {s t : BeaconState preset fork} {before : fork < .hegota}
    {deposit : Deposit} (ok : processDeposit config checks before s deposit = .ok t) :
    t.slashings = s.slashings := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, pending⟩
  · rfl
  · rfl
  · have kept := same_add added
    exact kept
  · rcases applyPendingDeposit_cases pending with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · rfl
    · have kept := same_increase raised
      exact kept
    · have kept := same_add added
      exact kept

private theorem same_attestation {s t : BeaconState preset fork}
    {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    t.slashings = s.slashings := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte] at ok
    unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨updated, _⟩, folded, _, _, _, raisedOk, final⟩ := ok
    have flagged : (setEpochParticipation s
        (attestation.data.target.epoch == getCurrentEpoch s) updated).slashings =
          s.slashings := by
      unfold setEpochParticipation
      split <;> rfl
    have raised := (same_increase raisedOk).trans flagged
    split at final
    · rw [recordPaymentWeight_eq final]
      exact raised
    · cases final
      exact raised
  · obtain ⟨_, _, _, _, _, recorded, _⟩ := processAttestation_records (Nat.lt_of_not_le altair) ok
    have kept := recordPendingAttestation_ok recorded
    split at kept
    all_goals
      obtain ⟨_, rest⟩ := kept
      rw [← rest]

end Same

/-! ## The slashed balances plus the effective balances not slashed -/

section Potential

/-- The effective balance at a position if its validator is not slashed, and zero otherwise. -/
private def unslashedAt (state : BeaconState preset fork) (j : Nat) : Nat :=
  ((state.validators.data[j]?).map fun validator =>
    if validator.slashed then 0 else validator.effectiveBalance.toNat).getD 0

private theorem unslashedBalanceSum_eq (state : BeaconState preset fork) (count : Nat) :
    unslashedBalanceSum state count = ((List.range count).map (unslashedAt state)).sum := rfl

/-- The slashed balances plus the effective balances not slashed, below a position. -/
private def potential (count : Nat) (state : BeaconState preset fork) : Nat :=
  slashedBalanceSum state + unslashedBalanceSum state count

/-- A step keeps the slashed balances, each earlier effective balance and each slashed flag. -/
private def Kept (a b : BeaconState preset fork) : Prop :=
  b.slashings = a.slashings ∧ EffectiveKept a b ∧ Frame a b

private theorem Kept.refl (a : BeaconState preset fork) : Kept a a :=
  ⟨rfl, effectiveKept_refl a, Frame.refl a⟩

private theorem Kept.trans {a b c : BeaconState preset fork} (one : Kept a b) (two : Kept b c) :
    Kept a c :=
  ⟨two.1.trans one.1, effectiveKept_trans one.2.1 two.2.1 one.2.2.registryGrows,
    one.2.2.trans two.2.2⟩

/-- A position of the earlier registry holds no more unslashed balance after a kept step. -/
private theorem unslashedAt_le {a b : BeaconState preset fork} (kept : EffectiveKept a b)
    (frame : Frame a b) {j : Nat} (inside : j < a.validators.data.size) :
    unslashedAt b j ≤ unslashedAt a j := by
  have inside' := Nat.lt_of_lt_of_le inside frame.registryGrows
  have same := kept j inside
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem inside',
    Option.map_some, Option.getD_some] at same
  have flag := frame.slashed j _ _ (Array.getElem?_eq_getElem inside)
    (Array.getElem?_eq_getElem inside')
  simp only [unslashedAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem inside',
    Option.map_some, Option.getD_some, same]
  split <;> split <;> simp_all

/-- A kept step does not raise the slashed balances plus the effective balances not slashed.

The registry must cover the positions. -/
private theorem potential_le_of_kept {count : Nat} {a b : BeaconState preset fork}
    (covers : count ≤ a.validators.data.size) (kept : Kept a b) :
    potential count b ≤ potential count a := by
  unfold potential slashedBalanceSum
  rw [kept.1, unslashedBalanceSum_eq, unslashedBalanceSum_eq]
  refine Nat.add_le_add_left (sum_map_le_sum_map fun j member => ?_) _
  exact unslashedAt_le kept.2.1 kept.2.2 (Nat.lt_of_lt_of_le (List.mem_range.mp member) covers)

/-- A sum over the positions grows by a bonus at one position when each other term grows. -/
private theorem sum_range_add_le {f g : Nat → Nat} {i bonus : Nat} :
    ∀ {count : Nat}, i < count → f i + bonus ≤ g i → (∀ j < count, j ≠ i → f j ≤ g j) →
      ((List.range count).map f).sum + bonus ≤ ((List.range count).map g).sum
  | 0, inside, _, _ => absurd inside (Nat.not_lt_zero _)
  | count + 1, inside, here, others => by
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    by_cases last : i = count
    · subst last
      have below := sum_map_le_sum_map (xs := List.range i) (f := f) (g := g) fun j member =>
        others j (by have := List.mem_range.mp member; omega)
          (by have := List.mem_range.mp member; omega)
      omega
    · have below := sum_range_add_le (count := count) (by omega) here
        (fun j lt apart => others j (by omega) apart)
      have top := others count (by omega) (Ne.symm last)
      omega

/-- Slashing a validator not yet slashed moves its effective balance to the slashed balances.

The registry keeps its size.

Over the registry, the slashed balances plus the effective balances not slashed do not grow. -/
private theorem potential_slash {a b : BeaconState preset fork} {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex} {v : Validator} (found : getValidator a i = .ok v)
    (fresh : v.slashed = false) (ok : slashValidator config a i whistleblower = .ok b) :
    b.validators.data.size = a.validators.data.size ∧
      potential a.validators.data.size b ≤ potential a.validators.data.size a := by
  have sized := (sameSizes_slashValidator ok).1
  have kept := effectiveKept_slash ok
  have frame := (frame_slashValidator ok).toFrame
  obtain ⟨exited, validator, delay, marked, slashed, total, slashings, lowered, _, _, raised, last,
    exitedOk, _, _, markedOk, readOk, totalOk, writeOk, loweredOk, _, _, raisedOk, lastOk,
    done⟩ := slashValidator_ok ok
  -- The last steps change only the balances and the builder payments.
  have tail : b.validators = marked.validators ∧ b.slashings = slashings := by
    have lowerValidators := decreaseBalance_validators loweredOk
    have lowerSlashings := same_decrease loweredOk
    have validators : last.validators = marked.validators :=
      (increaseBalance_validators lastOk).trans
        ((increaseBalance_validators raisedOk).trans lowerValidators)
    have written : last.slashings = slashings :=
      (same_increase lastOk).trans ((same_increase raisedOk).trans lowerSlashings)
    subst done
    split <;> exact ⟨validators, written⟩
  refine ⟨sized, ?_⟩
  have earlier : marked.slashings = a.slashings :=
    (same_setValidator markedOk).trans (same_exit exitedOk)
  -- The slashed balances rise by the effective balance of the validator.
  have nonzero : preset.EPOCHS_PER_SLASHINGS_VECTOR ≠ 0 := by
    intro zero
    simp [readCircular, zero] at readOk
  simp only [readCircular, nonzero, ↓reduceDIte, Except.ok.injEq] at readOk
  simp only [writeCircularRooted, nonzero, ↓reduceDIte, Except.ok.injEq] at writeOk
  obtain ⟨_, totalNat⟩ := Base.Uint64.addChecked_ok_iff.mp totalOk
  have summed : slashedBalanceSum b + slashed.toNat =
      slashedBalanceSum a + total.toNat := by
    unfold slashedBalanceSum
    rw [tail.2, ← writeOk, ← readOk, ← earlier]
    simp only [Serialization.Ssz.RootedVector.elements_set, Vector.toList_set, List.map_set]
    have moved := sum_set_add (l := marked.slashings.elements.toList.map (·.toNat))
      (i := (getCurrentEpoch a % preset.EPOCHS_PER_SLASHINGS_VECTOR).toNat)
      (by simp only [List.length_map, Vector.length_toList]; exact toNat_mod_lt nonzero)
      total.toNat
    simpa using moved
  -- The validator is marked slashed, and keeps its effective balance.
  rw [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] at found
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  rw [setValidator_eq_setValidatorAt] at markedOk
  obtain ⟨insideExited, rfl⟩ := setValidatorAt_ok markedOk
  have marks : b.validators.data[i.toNat]? = some { validator with
      slashed := true, withdrawableEpoch := validator.withdrawableEpoch ⊔ delay } := by
    rw [tail.1]
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
  have same := kept i.toNat inside
  simp only [effectiveAt, marks, found, Option.map_some, Option.getD_some] at same
  have dropped : unslashedBalanceSum b a.validators.data.size + validator.effectiveBalance.toNat ≤
      unslashedBalanceSum a a.validators.data.size := by
    rw [unslashedBalanceSum_eq, unslashedBalanceSum_eq]
    refine sum_range_add_le inside ?_ fun j below _ => unslashedAt_le kept frame below
    simp [unslashedAt, marks, found, fresh, same]
  unfold potential
  omega

/-- A fold whose every step is kept is kept. -/
private theorem Kept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Kept a b) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) : Kept a b :=
  foldlM_ok_invariant (Kept a) (fun _ _ _ before ok => before.trans (each _ _ _ ok))
    (Kept.refl a) computed

/-- A step that keeps the registry and the slashed balances, in a frame, is kept. -/
private theorem Kept.of_validators {a b : BeaconState preset fork}
    (validators : b.validators = a.validators) (slashings : b.slashings = a.slashings)
    (frame : Frame a b) : Kept a b ∧ b.validators.data.size = a.validators.data.size :=
  ⟨⟨slashings, effectiveKept_data (congrArg (·.data) validators), frame⟩, by rw [validators]⟩

private theorem Kept.executionRequests {a b : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionRequests config a body electra = .ok b) : Kept a b := by
  have requests := ok
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requests
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := requests
  exact (Kept.foldlM (fun _ _ _ ok => ⟨same_depositRequest ok, effectiveKept_depositRequest ok,
      (frame_processDepositRequest ok).toFrame⟩) deposits).trans <|
    (Kept.foldlM (fun _ _ _ ok => ⟨same_withdrawalRequest ok,
      effectiveKept_withdrawalRequest ok, (frame_processWithdrawalRequest ok).toFrame⟩)
      withdrawals).trans
    (Kept.foldlM (fun _ _ _ ok => ⟨same_consolidationRequest ok,
      effectiveKept_consolidationRequest ok, (frame_processConsolidationRequest ok).toFrame⟩)
      consolidations)

/-- The steps of a block before its operations are kept, and keep the size of the registry. -/
private theorem Kept.operationsInput {engine : ExecutionEngine preset fork}
    {a input : BeaconState preset fork} {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine a block input) :
    Kept a input ∧ input.validators.data.size = a.validators.data.size := by
  refine started.step_of
    (fun a b => Kept a b ∧ b.validators.data.size = a.validators.data.size)
    (fun a => ⟨Kept.refl a, rfl⟩) (fun one two => ⟨one.1.trans two.1, two.2.trans one.2⟩)
    (fun _ paid => ?_) (fun headed => ?_) (fun _ executed => ?_) (fun revealed => ?_)
    (fun _ voted => ?_)
  · -- The payload of the parent exits and consolidates validators, but adds none.
    have registry := processParentExecutionPayload_step_of
      (fun a b => EffectiveKept a b ∧ b.validators.data.size = a.validators.data.size)
      (fun a => ⟨effectiveKept_refl a, rfl⟩)
      (fun one two => ⟨effectiveKept_trans one.1 two.1 (Nat.le_of_eq one.2.symm),
        two.2.trans one.2⟩)
      (fun _ validators => ⟨effectiveKept_data (congrArg (·.data) validators),
        by rw [validators]⟩)
      (fun requested => ⟨effectiveKept_withdrawalRequest requested,
        (sameSizes_processWithdrawalRequest requested).1⟩)
      (fun requested => ⟨effectiveKept_consolidationRequest requested,
        (sameSizes_processConsolidationRequest requested).1⟩) paid
    exact ⟨⟨same_parentPayload paid, registry.1,
      (frame_processParentExecutionPayload paid).toFrame⟩, registry.2⟩
  · have frame := (frame_processBlockHeader headed).toFrame
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
    exact Kept.of_validators rfl rfl frame
  · exact Kept.of_validators (processBlockExecution_validators executed)
      (same_blockExecution executed) (frame_processBlockExecution executed).toFrame
  · have frame := (frame_processRandao revealed).toFrame
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
    exact Kept.of_validators rfl rfl frame
  · have frame := (frame_processEth1Data voted).toFrame
    obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
    exact Kept.of_validators (by rw [← rest]) (by rw [← rest]) frame

/-- Within a registry of a fixed size, a step keeps that size.

It does not raise the slashed balances plus the effective balances not slashed. -/
private def Lowers (count : Nat) (a b : BeaconState preset fork) : Prop :=
  a.validators.data.size = count →
    b.validators.data.size = count ∧ potential count b ≤ potential count a

private theorem Lowers.refl (count : Nat) (a : BeaconState preset fork) : Lowers count a a :=
  fun sized => ⟨sized, Nat.le_refl _⟩

private theorem Lowers.trans {count : Nat} {a b c : BeaconState preset fork}
    (one : Lowers count a b) (two : Lowers count b c) : Lowers count a c := fun sized =>
  ⟨(two (one sized).1).1, Nat.le_trans (two (one sized).1).2 (one sized).2⟩

/-- Slashing a slashable validator does not raise the slashed plus the unslashed balances. -/
private theorem Lowers.slash {count : Nat} {a b : BeaconState preset fork} {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex} {v : Validator} (found : getValidator a i = .ok v)
    (slashable : isSlashableValidator v (getCurrentEpoch a) = true)
    (ok : slashValidator config a i whistleblower = .ok b) : Lowers count a b := by
  intro sized
  subst sized
  have fresh : v.slashed = false := by
    simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at slashable
    exact slashable.1.1
  exact potential_slash found fresh ok

private theorem Lowers.proposerSlashing {count : Nat} {a b : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks a slashing = .ok b) : Lowers count a b := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, found, _, slashable, _, _, _, _, slashed⟩ := ok
  exact Lowers.slash found slashable slashed

private theorem Lowers.attesterSlashing {count : Nat} {a b : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks a slashing = .ok b) : Lowers count a b := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step : BeaconState preset fork × Bool => Lowers count a step.1)
    (fun step _ _ before ok => ?_) (Lowers.refl count a) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact before.trans (Lowers.slash found ‹_› slashed)
  · cases ok
    exact before

end Potential

/-- A block runs its two folds of slashings between steps that keep the slashed balances.

Those steps also keep each earlier effective balance and slashed flag.

The steps before the folds keep the size of the registry. -/
private theorem processBlock_slashings {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ input proposersDone slashingsDone,
      Kept state input ∧ input.validators.data.size = state.validators.data.size ∧
      block.body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks)
        input = .ok proposersDone ∧
      block.body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks)
        proposersDone = .ok slashingsDone ∧
      Kept slashingsDone after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  have head := Kept.operationsInput started
  obtain ⟨_, slashingsDone, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of Kept Kept.refl Kept.trans
      (fun deposited => ⟨same_deposit deposited, effectiveKept_processDeposit deposited,
        (frame_processDeposit deposited).toFrame⟩)
      (fun exited => ⟨same_exit (processVoluntaryExit_initiates exited),
        effectiveKept_voluntaryExit exited, (frame_processVoluntaryExit exited).toFrame⟩)
      (fun changed => by
        obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok changed
        exact ⟨same_setValidator set, effectiveKept_blsChange changed,
          (frame_processBlsToExecutionChange changed).toFrame⟩)
      (fun requested => Kept.executionRequests requested)
      (fun attested => by rw [processPayloadAttestation_eq attested]; exact Kept.refl _) operated
  have tail : Kept last after := by
    split at synced
    · have frame := (frame_processSyncAggregate synced).toFrame
      obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact ⟨rfl, effectiveKept_data rfl, frame⟩
    · cases synced
      exact Kept.refl _
  have later := (Kept.foldlM (fun _ _ _ ok => ⟨same_attestation ok,
      effectiveKept_data (congrArg (·.data) (processAttestation_registry ok).1),
      frame_processAttestation ok⟩) attestedOk).trans (rest.trans tail)
  exact ⟨input, _, slashingsDone, head.1, head.2, proposersOk, slashingsOk, later⟩

/-- A block does not raise the slashed balances plus the effective balances not yet slashed.

The sums of the balances not slashed read the positions of the registry before the block. -/
theorem processBlock_slashedBalanceSum_add_le {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    slashedBalanceSum after + unslashedBalanceSum after state.validators.data.size ≤
      slashedBalanceSum state + unslashedBalanceSum state state.validators.data.size := by
  obtain ⟨_, _, _, head, sized, proposersOk, slashingsOk, later⟩ := processBlock_slashings computed
  -- The slashings run on the registry of the block, which they keep.
  have slashed := (Lowers.trans
    (foldlM_ok_steps (Lowers state.validators.data.size) (Lowers.refl _) Lowers.trans
      (fun _ _ _ ok => Lowers.proposerSlashing ok) proposersOk).1
    (foldlM_ok_steps (Lowers state.validators.data.size) (Lowers.refl _) Lowers.trans
      (fun _ _ _ ok => Lowers.attesterSlashing ok) slashingsOk).1) sized
  exact Nat.le_trans (potential_le_of_kept (Nat.le_of_eq slashed.1.symm) later) <|
    Nat.le_trans slashed.2 (potential_le_of_kept (Nat.le_refl _) head)

/-- The effective balances not slashed are at most all the effective balances. -/
theorem unslashedBalanceSum_le_effectiveBalanceSum (state : BeaconState preset fork) :
    unslashedBalanceSum state state.validators.data.size ≤ effectiveBalanceSum state := by
  rw [unslashedBalanceSum_eq, effectiveBalanceSum_eq_sum_range]
  refine sum_map_le_sum_map fun j _ => ?_
  unfold unslashedAt
  cases state.validators.data[j]? with
  | none => exact Nat.le_refl _
  | some validator =>
    simp only [Option.map_some, Option.getD_some]
    split <;> omega

/-- A block raises the slashed balances by at most the effective balances not slashed before it. -/
theorem processBlock_slashedBalanceSum_le {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    slashedBalanceSum after ≤
      slashedBalanceSum state + unslashedBalanceSum state state.validators.data.size :=
  (Nat.le_add_right _ _).trans (processBlock_slashedBalanceSum_add_le computed)

/-- The number of validators that the slashings of a block body name, once for each slashing.

Each proposer slashing names one validator.

Each attester slashing names the signers of its first attestation, which include all it slashes. -/
def blockSlashingCount (body : BeaconBlockBody preset fork) : Nat :=
  body.proposerSlashings.data.size +
    (body.attesterSlashings.data.toList.map fun slashing =>
      slashing.attestation1.attestingIndices.data.size).sum

/-! ## The slashed balances against a count of the validators named -/

section Counted

/-- Slashing a validator raises the slashed balances by at most its effective balance. -/
private theorem slashedBalanceSum_slash {a b : BeaconState preset fork} {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex} {v : Validator} (found : getValidator a i = .ok v)
    (ok : slashValidator config a i whistleblower = .ok b) :
    slashedBalanceSum b ≤ slashedBalanceSum a + effectiveAt ⟨fork, a⟩ i.toNat := by
  have kept := effectiveKept_slash ok
  obtain ⟨exited, validator, delay, marked, slashed, total, slashings, lowered, _, _, raised, last,
    exitedOk, _, _, markedOk, readOk, totalOk, writeOk, loweredOk, _, _, raisedOk, lastOk,
    done⟩ := slashValidator_ok ok
  -- The last steps change only the balances and the builder payments.
  have tail : b.validators = marked.validators ∧ b.slashings = slashings := by
    have lowerValidators := decreaseBalance_validators loweredOk
    have lowerSlashings := same_decrease loweredOk
    have validators : last.validators = marked.validators :=
      (increaseBalance_validators lastOk).trans
        ((increaseBalance_validators raisedOk).trans lowerValidators)
    have written : last.slashings = slashings :=
      (same_increase lastOk).trans ((same_increase raisedOk).trans lowerSlashings)
    subst done
    split <;> exact ⟨validators, written⟩
  have earlier : marked.slashings = a.slashings :=
    (same_setValidator markedOk).trans (same_exit exitedOk)
  -- The slashed balances rise by the effective balance of the validator.
  have nonzero : preset.EPOCHS_PER_SLASHINGS_VECTOR ≠ 0 := by
    intro zero
    simp [readCircular, zero] at readOk
  simp only [readCircular, nonzero, ↓reduceDIte, Except.ok.injEq] at readOk
  simp only [writeCircularRooted, nonzero, ↓reduceDIte, Except.ok.injEq] at writeOk
  obtain ⟨_, totalNat⟩ := Base.Uint64.addChecked_ok_iff.mp totalOk
  have summed : slashedBalanceSum b + slashed.toNat =
      slashedBalanceSum a + total.toNat := by
    unfold slashedBalanceSum
    rw [tail.2, ← writeOk, ← readOk, ← earlier]
    simp only [Serialization.Ssz.RootedVector.elements_set, Vector.toList_set, List.map_set]
    have moved := sum_set_add (l := marked.slashings.elements.toList.map (·.toNat))
      (i := (getCurrentEpoch a % preset.EPOCHS_PER_SLASHINGS_VECTOR).toNat)
      (by simp only [List.length_map, Vector.length_toList]; exact toNat_mod_lt nonzero)
      total.toNat
    simpa using moved
  -- The validator keeps its effective balance.
  rw [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] at found
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  rw [setValidator_eq_setValidatorAt] at markedOk
  obtain ⟨insideExited, rfl⟩ := setValidatorAt_ok markedOk
  have marks : b.validators.data[i.toNat]? = some { validator with
      slashed := true, withdrawableEpoch := validator.withdrawableEpoch ⊔ delay } := by
    rw [tail.1]
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
  have same := kept i.toNat inside
  simp only [effectiveAt, marks, Option.map_some, Option.getD_some] at same
  unfold effectiveAt
  rw [← same]
  omega

/-- Each effective balance is at most the largest cap. -/
private def Bounded (state : BeaconState preset fork) : Prop :=
  ∀ j, effectiveAt ⟨fork, state⟩ j ≤ preset.largestEffectiveBalance

private theorem Bounded.of_capped {state : BeaconState preset fork}
    (capped : EffectiveBalancesCapped state) : Bounded state := by
  intro j
  unfold effectiveAt
  cases read : state.validators.data[j]? with
  | none => simp
  | some validator =>
    simp only [Option.map_some, Option.getD_some]
    have within := capped validator (Array.mem_of_getElem? read)
    exact (UInt64.le_iff_toNat_le.mp within).trans
      (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork validator)

/-- A step that keeps the earlier effective balances and adds no validator keeps the bound. -/
private theorem Bounded.of_kept {a b : BeaconState preset fork} (bounded : Bounded a)
    (kept : EffectiveKept a b) (sized : b.validators.data.size ≤ a.validators.data.size) :
    Bounded b := by
  intro j
  by_cases inside : j < a.validators.data.size
  · rw [kept j inside]
    exact bounded j
  · simp [effectiveAt, Array.getElem?_eq_none (Nat.le_trans sized (Nat.le_of_not_lt inside))]

/-- A fold that keeps a predicate raises a measure by at most a count per item, times a unit. -/
private theorem foldlM_counted {α β ε : Type} {step : β → α → Except ε β} (P : β → Prop)
    (measure : β → Nat) (count : α → Nat) (unit : Nat)
    (each : ∀ a x b, step a x = .ok b → P a → P b ∧ measure b ≤ measure a + count x * unit) :
    ∀ {xs : List α} {a b : β}, xs.foldlM step a = .ok b → P a →
      P b ∧ measure b ≤ measure a + (xs.map count).sum * unit
  | [], a, b, computed, holds => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simpa using holds
  | x :: xs, a, b, computed, holds => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    obtain ⟨heldFirst, raisedFirst⟩ := each _ _ _ first holds
    obtain ⟨heldRest, raisedRest⟩ := foldlM_counted P measure count unit each rest heldFirst
    refine ⟨heldRest, ?_⟩
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    omega

/-- Slashing a validator keeps the bound, and raises the slashed balances by at most the cap. -/
private theorem Bounded.slash {a b : BeaconState preset fork} {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex} {v : Validator} (found : getValidator a i = .ok v)
    (ok : slashValidator config a i whistleblower = .ok b) (bounded : Bounded a) :
    Bounded b ∧ slashedBalanceSum b ≤ slashedBalanceSum a + 1 * preset.largestEffectiveBalance :=
  ⟨bounded.of_kept (effectiveKept_slash ok) (Nat.le_of_eq (sameSizes_slashValidator ok).1),
    (slashedBalanceSum_slash found ok).trans
      (Nat.add_le_add_left ((bounded _).trans (Nat.le_of_eq (Nat.one_mul _).symm)) _)⟩

private theorem Bounded.proposerSlashing {a b : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks a slashing = .ok b) (bounded : Bounded a) :
    Bounded b ∧ slashedBalanceSum b ≤ slashedBalanceSum a + 1 * preset.largestEffectiveBalance := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, found, _, _, _, _, _, _, slashed⟩ := ok
  exact Bounded.slash found slashed bounded

/-- An attester slashing raises the slashed balances by at most the largest cap per signer.

The signers are those of its first attestation.

It keeps the bound. -/
private theorem Bounded.attesterSlashing {a b : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks a slashing = .ok b) (bounded : Bounded a) :
    Bounded b ∧ slashedBalanceSum b ≤ slashedBalanceSum a +
      slashing.attestation1.attestingIndices.data.size * preset.largestEffectiveBalance := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  have counted := foldlM_counted (fun step : BeaconState preset fork × Bool => Bounded step.1)
    (fun step => slashedBalanceSum step.1) (fun _ => 1) preset.largestEffectiveBalance
    (fun step _ _ ok before => by
      obtain ⟨middle, slashedAny⟩ := step
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, found, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, slashed, rfl⟩ := ok
        exact Bounded.slash found slashed before
      · cases ok
        exact ⟨before, Nat.le_add_right _ _⟩) folded bounded
  refine ⟨counted.1, counted.2.trans (Nat.add_le_add_left ?_ _)⟩
  simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_one]
  refine Nat.mul_le_mul_right _ ((length_sortedSet_le _).trans ?_)
  exact (List.length_filter_le _ _).trans (by simp)

end Counted

/-- A block raises the slashed balances by at most the largest cap per validator its slashings name.

The effective balances before it must be within their caps. -/
theorem processBlock_slashedBalanceSum_le_count {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (capped : EffectiveBalancesCapped state)
    (computed : processBlock config checks engine state block = .ok after) :
    slashedBalanceSum after ≤
      slashedBalanceSum state + blockSlashingCount block.body * preset.largestEffectiveBalance := by
  obtain ⟨_, _, _, head, sized, proposersOk, slashingsOk, later⟩ := processBlock_slashings computed
  have bounded := (Bounded.of_capped capped).of_kept head.2.1 (Nat.le_of_eq sized)
  obtain ⟨boundedProposed, proposed⟩ := foldlM_counted Bounded slashedBalanceSum
    (fun _ => 1) preset.largestEffectiveBalance
    (fun _ _ _ ok => Bounded.proposerSlashing ok) proposersOk bounded
  have attested := (foldlM_counted Bounded slashedBalanceSum
    (fun slashing => slashing.attestation1.attestingIndices.data.size)
    preset.largestEffectiveBalance
    (fun _ _ _ ok => Bounded.attesterSlashing ok) slashingsOk boundedProposed).2
  have kept : slashedBalanceSum after = slashedBalanceSum _ := congrArg
    (fun slashings => (slashings.elements.toList.map (·.toNat)).sum) later.1
  have started : slashedBalanceSum _ = slashedBalanceSum state := congrArg
    (fun slashings => (slashings.elements.toList.map (·.toNat)).sum) head.1
  simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_one,
    Array.length_toList] at proposed
  unfold blockSlashingCount
  rw [Nat.add_mul]
  omega

end EthLib.Consensus
