module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.PayloadTimeliness
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.BuilderRequests
import EthLib.Consensus.Proofs.Transition.Execution
import EthLib.Consensus.Proofs.Transition.Payload
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: a block raises no balance of a validator it does not credit

A block credits a balance in a few ways.

Its proposer earns the rewards of the attestations, of the slashings and of the sync aggregate.

Each member of the sync committee that signs earns a reward.

Before Electra a deposit adds its amount to the validator with its key.

Every other step of a block lowers a balance or keeps it, at every fork.

So the balance of a validator that is not the proposer does not rise in the block.

From Altair this also needs the validator to sign no sync aggregate.

Before Electra it also needs no deposit to carry its key.

The bounds on an inactivity leak assume that a balance does not rise between two epochs.

The proposer is read at several steps of the block, and each read gives the same validator.

That holds when the mixes span more than the seed lookahead plus two epochs.

This holds on mainnet and on the minimal preset.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Balances that only fall -/

/-- The balance at a position stays, and does not rise, from one state to another. -/
private def Down (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ∀ earlier, state.balances.data[index]? = some earlier →
    ∃ later, after.balances.data[index]? = some later ∧ later ≤ earlier

/-- A state keeps each of its balances. -/
private theorem Down.refl (index : Nat) (state : BeaconState preset fork) :
    Down index state state :=
  fun earlier found => ⟨earlier, found, UInt64.le_refl _⟩

/-- Two steps that keep a balance from rising keep it from rising. -/
private theorem Down.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : Down index first second) (two : Down index second third) : Down index first third := by
  intro earlier found
  obtain ⟨middle, atMiddle, low⟩ := one earlier found
  obtain ⟨later, atLater, lower⟩ := two middle atMiddle
  exact ⟨later, atLater, UInt64.le_trans lower low⟩

/-- A step that keeps the balances keeps the balance at each position. -/
private theorem Down.of_balances {index : Nat} (same : after.balances = state.balances) :
    Down index state after := by
  intro earlier found
  exact ⟨earlier, by rw [same]; exact found, UInt64.le_refl _⟩

/-- A fold of steps that each keep a balance from rising keeps it. -/
private theorem Down.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ s x t, step s x = .ok t → Down index s t) {items : List α}
    (computed : items.foldlM step state = .ok after) : Down index state after :=
  (foldlM_ok_steps (Down index) (Down.refl index) Down.trans each computed).1

/-- Lowering a balance keeps every balance from rising. -/
private theorem down_decreaseBalance {position : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state position delta = .ok after) (index : Nat) :
    Down index state after := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
  intro earlier found
  simp only [BeaconState.putBalance, Array.getElem?_set]
  split
  · rename_i same
    subst same
    rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
    subst found
    refine ⟨_, rfl, ?_⟩
    rw [Uint64.saturatingSub]
    split
    · exact UInt64.sub_le (UInt64.le_of_lt ‹_›)
    · exact UInt64.zero_le
  · exact ⟨earlier, found, UInt64.le_refl _⟩

/-- Raising the balance at another position keeps the balance at this one. -/
private theorem down_increaseBalance {position : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state position delta = .ok after) {index : Nat}
    (other : position.toNat ≠ index) : Down index state after := by
  obtain ⟨inside, -, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  intro earlier found
  simp only [BeaconState.putBalance, Array.getElem?_set, other, ↓reduceIte]
  exact ⟨earlier, found, UInt64.le_refl _⟩


/-- Setting a balance to at most its old value keeps every balance from rising. -/
private theorem down_setBalance {position : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance position balance = .ok after)
    (low : ∀ old, state.balances.data[position.toNat]? = some old → balance ≤ old)
    (index : Nat) : Down index state after := by
  obtain ⟨inside, rfl⟩ := setBalance_ok set
  intro earlier found
  simp only [BeaconState.putBalance, Array.getElem?_set]
  split
  · rename_i same
    subst same
    exact ⟨balance, by simp, low earlier found⟩
  · exact ⟨earlier, found, UInt64.le_refl _⟩

/-- A write to a validator keeps the balances. -/
private theorem down_setValidator {position : ValidatorIndex} {validator : Validator}
    (set : state.setValidator position validator = .ok after) (index : Nat) :
    Down index state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact Down.of_balances rfl

/-- An exit keeps the balances. -/
private theorem down_initiateValidatorExit {position : ValidatorIndex}
    (computed : initiateValidatorExit config state position = .ok after) (index : Nat) :
    Down index state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact Down.refl _ _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    exact (Down.of_balances rfl).trans (down_setValidator set index)

/-- A partial withdrawal request keeps the balances. -/
private theorem down_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {position : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra position validator amount owed =
      .ok after) (index : Nat) :
    Down index state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact Down.of_balances (computeExitEpochAndUpdateChurn_earliest churned).2.2
  · cases computed
    exact Down.refl _ _

/-- A withdrawal request keeps every balance from rising. -/
private theorem down_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) (index : Nat) :
    Down index state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Down.refl _ _)
    | exact down_initiateValidatorExit (liftAccessor_ok.mp computed) index
    | exact down_requestPartialWithdrawal computed index

/-- A switch to compounding credentials keeps every balance from rising. -/
private theorem down_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {position : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra position = .ok after) (index : Nat) :
    Down index state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, mid, set, queued⟩ := computed
  refine (down_setValidator set index).trans ?_
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨balance, found, queued⟩ := queued
  split at queued
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, lowered, rfl⟩ := queued
    refine (down_setBalance lowered (fun old atOld => ?_) index).trans (Down.of_balances rfl)
    simp only [getBalance, atOld] at found
    cases found
    exact UInt64.le_of_lt above
  · cases queued
    exact Down.refl _ _

/-- A queued consolidation keeps the balances. -/
private theorem down_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after)
    (index : Nat) : Down index state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (Down.of_balances (computeConsolidationEpochAndUpdateChurn_earliest churned).2.2).trans
    ((down_setValidator set index).trans (Down.of_balances rfl))

/-- A consolidation request keeps every balance from rising. -/
private theorem down_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after)
    (index : Nat) : Down index state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Down.refl _ _)
    | exact down_switchToCompoundingValidator (liftAccessor_ok.mp computed) index
    | exact down_queueConsolidation computed index

/-- A deposit request keeps the balances. -/
private theorem down_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) (index : Nat) :
    Down index state after :=
  Down.of_balances (processDepositRequest_ok computed).2.2

/-- The withdrawals lower balances, and from Gloas those of builders. -/
private theorem down_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) (index : Nat) :
    Down index state after := by
  have applied {s t : BeaconState preset fork} {expected : ExpectedWithdrawals}
      (ok : applyExpectedWithdrawals s capella expected = .ok t) : Down index s t := by
    obtain ⟨mid, midOk, balances, -⟩ := applyExpectedWithdrawals_balances ok
    refine Down.trans ?_ (Down.of_balances balances)
    unfold applyWithdrawals at midOk
    rw [← Array.foldlM_toList] at midOk
    refine Down.foldlM (fun u withdrawal v step => ?_) midOk
    unfold applyWithdrawal at step
    split at step
    · simp only [bind_ok_iff] at step
      obtain ⟨_, _, set⟩ := step
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      exact Down.of_balances rfl
    · exact down_decreaseBalance step index
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp computed
      exact applied (liftAccessor_ok.mp ok)
    · cases computed
      exact Down.refl _ _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, ok⟩ := computed
    exact applied ok

/-! ## The proposer along a block -/

/-- The proposer search reads only the effective balances of the indices it draws from. -/
private theorem proposerSearch_validators {old new : Array Validator}
    {indices : Array ValidatorIndex} {order : Nat → Nat} {seed : Bytes32}
    (agree : ∀ candidate ∈ indices, (new[candidate.toNat]?).map (·.effectiveBalance) =
      (old[candidate.toNat]?).map (·.effectiveBalance))
    (nonempty : 0 < indices.size) (positions : ∀ place < indices.size, order place < indices.size) :
    ∀ {i : Nat}, proposerSearch preset fork new indices order seed i =
      proposerSearch preset fork old indices order seed i := by
  intro i
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
    have member : indices.getD (order (i % indices.size)) 0 ∈ indices := by
      have lt := positions _ (Nat.mod_lt i nonempty)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem lt, Option.getD_some]
      exact Array.getElem_mem lt
    have same := agree _ member
    unfold proposerSearch
    dsimp only
    generalize new[(indices.getD (order (i % indices.size)) 0).toNat]? = atNew at same
    generalize old[(indices.getD (order (i % indices.size)) 0).toNat]? = atOld at same
    cases atNew <;> cases atOld <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at same
    · rfl
    · simp only [bind, Except.bind, same]
      repeat' split
      all_goals first | rfl | exact ih _ (by omega) rfl


/-- The proposer draw reads only the effective balances of the indices it draws from. -/
private theorem computeProposerIndex_validators {other : BeaconState preset fork}
    {indices : Array ValidatorIndex} {seed : Bytes32}
    (agree : ∀ candidate ∈ indices,
      (other.validators.data[candidate.toNat]?).map (·.effectiveBalance) =
        (state.validators.data[candidate.toNat]?).map (·.effectiveBalance)) :
    computeProposerIndex other indices seed = computeProposerIndex state indices seed := by
  unfold computeProposerIndex
  by_cases empty : indices.size = 0
  · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  by_cases fits : indices.size < 2 ^ 64
  · by_cases large : 2 ^ 40 < indices.size
    · simp [empty, fits, large, bind, Except.bind, throw, throwThe, MonadExcept.throw,
        MonadExceptOf.throw]
    simp only [empty, fits, large, ↓reduceIte]
    exact proposerSearch_validators agree (Nat.pos_of_ne_zero empty)
      (fun _ lt => Shuffle.shuffledIndex_lt lt)
  · simp [empty, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

/-! ## Fields that a block keeps -/

/-- A step keeps the slot, the proposer lookahead, the current sync committee and the mixes. -/
private def Fixed (state after : BeaconState preset fork) : Prop :=
  after.slot = state.slot ∧ after.proposerLookahead = state.proposerLookahead ∧
    after.currentSyncCommittee = state.currentSyncCommittee ∧
    after.randaoMixes = state.randaoMixes

/-- A state keeps its own fields. -/
private theorem Fixed.refl (state : BeaconState preset fork) : Fixed state state :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Two steps that keep the fields keep them. -/
private theorem Fixed.trans {first second third : BeaconState preset fork}
    (one : Fixed first second) (two : Fixed second third) : Fixed first third :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.trans one.2.2.2⟩

/-- A fold of steps that keep the fields keeps them. -/
private theorem Fixed.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ s x t, step s x = .ok t → Fixed s t) {items : List α}
    (computed : items.foldlM step state = .ok after) : Fixed state after :=
  (foldlM_ok_steps Fixed Fixed.refl Fixed.trans each computed).1

/-- A write to a validator keeps the fields. -/
private theorem fixed_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : Fixed state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A write to a balance keeps the fields. -/
private theorem fixed_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : Fixed state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Raising a balance keeps the fields. -/
private theorem fixed_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : Fixed state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  exact fixed_setBalance set

/-- Lowering a balance keeps the fields. -/
private theorem fixed_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : Fixed state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  exact fixed_setBalance set

/-- An exit keeps the fields. -/
private theorem fixed_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Fixed state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact Fixed.refl _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    refine Fixed.trans ?_ (fixed_setValidator set)
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A slashing keeps the fields. -/
private theorem fixed_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    Fixed state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, last, exitedOk, -, -, markedOk, -, -, -, loweredOk, -, -,
    raisedOk, lastOk, done⟩ := slashValidator_ok computed
  have cancelled : Fixed last after := by
    subst done
    split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact Fixed.refl _
  refine (fixed_initiateValidatorExit exitedOk).trans <|
    ((fixed_setValidator markedOk).trans ?_).trans <|
    (fixed_decreaseBalance loweredOk).trans <|
    (fixed_increaseBalance raisedOk).trans <|
    (fixed_increaseBalance lastOk).trans cancelled
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A deposit request keeps the fields. -/
private theorem fixed_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) : Fixed state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A partial withdrawal request keeps the fields. -/
private theorem fixed_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    Fixed state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases computed
    exact Fixed.refl _

/-- A withdrawal request keeps the fields. -/
private theorem fixed_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    Fixed state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Fixed.refl _)
    | exact fixed_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact fixed_requestPartialWithdrawal computed

/-- A switch to compounding credentials keeps the fields. -/
private theorem fixed_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    Fixed state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  refine (fixed_setValidator set).trans ?_
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    exact (fixed_setBalance set).trans ⟨rfl, rfl, rfl, rfl⟩
  · cases queued
    exact Fixed.refl _

/-- A queued consolidation keeps the fields. -/
private theorem fixed_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    Fixed state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  refine (Fixed.trans ?_ (fixed_setValidator set)).trans ?_ <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A consolidation request keeps the fields. -/
private theorem fixed_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    Fixed state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Fixed.refl _)
    | exact fixed_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact fixed_queueConsolidation computed

/-- One step of an attester slashing keeps the fields. -/
private theorem fixed_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    Fixed step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact fixed_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Fixed.refl _

/-- An attestation keeps the fields. -/
private theorem fixed_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    Fixed state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : Fixed raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · cases final
        exact Fixed.refl _
    have flags : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        Fixed state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    exact (flags _ _).trans ((fixed_increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A new validator keeps the fields. -/
private theorem fixed_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Fixed state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl⟩
  · split at computed
    · cases computed
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases computed

/-- A deposit keeps the fields. -/
private theorem fixed_applyDeposit {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDeposit config checks state pubkey withdrawalCredentials amount signature =
      .ok after) :
    Fixed state after := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (fixed_addValidatorToRegistry added).trans ⟨rfl, rfl, rfl, rfl⟩
      · cases computed
        exact Fixed.refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact ⟨rfl, rfl, rfl, rfl⟩
  · rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact Fixed.refl _
    · exact fixed_increaseBalance raised
    · exact fixed_addValidatorToRegistry added

/-- A deposit of a block keeps the fields. -/
private theorem fixed_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    Fixed state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact Fixed.trans (second := { state with eth1DepositIndex := fun _ => next })
    ⟨rfl, rfl, rfl, rfl⟩
    (fixed_applyDeposit applied)

/-- A voluntary exit keeps the fields. -/
private theorem fixed_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    Fixed state after :=
  fixed_initiateValidatorExit (processVoluntaryExit_initiates computed)

/-- A change of credentials keeps the fields. -/
private theorem fixed_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    Fixed state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact fixed_setValidator set

/-- A step keeps what the proposer of the slot reads, and the current sync committee. -/
private def Steady (state after : BeaconState preset fork) : Prop :=
  (after.slot = state.slot ∧ after.proposerLookahead = state.proposerLookahead ∧
    after.currentSyncCommittee = state.currentSyncCommittee) ∧
    (fork < Fork.fusaka → ActiveKept (getCurrentEpoch state) state after ∧
      MixesKeptBut (getCurrentEpoch state) state after ∧ EffectiveKept state after ∧
      state.validators.data.size ≤ after.validators.data.size)

/-- A state keeps what its proposer reads. -/
private theorem Steady.refl (state : BeaconState preset fork) : Steady state state :=
  ⟨⟨rfl, rfl, rfl⟩, fun _ => ⟨ActiveKept.refl _ _, fun _ _ => rfl, effectiveKept_refl _,
    Nat.le_refl _⟩⟩

/-- Two steps that keep what the proposer reads keep it. -/
private theorem Steady.trans {first second third : BeaconState preset fork}
    (one : Steady first second) (two : Steady second third) : Steady first third := by
  have epoch : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, one.1.1]
  refine ⟨⟨two.1.1.trans one.1.1, two.1.2.1.trans one.1.2.1, two.1.2.2.trans one.1.2.2⟩,
    fun early => ?_⟩
  obtain ⟨active, mixes, effective, grows⟩ := one.2 early
  obtain ⟨active', mixes', effective', grows'⟩ := two.2 early
  rw [epoch] at active' mixes'
  exact ⟨active.trans active', fun other apart => (mixes' other apart).trans (mixes other apart),
    effectiveKept_trans effective effective' grows, Nat.le_trans grows grows'⟩

/-- A step that keeps the fields, activity and effective balances is steady. -/
private theorem Steady.of_parts (fixed : Fixed state after) (active : ActiveStep state after)
    (effective : EffectiveKept state after)
    (grows : state.validators.data.size ≤ after.validators.data.size) : Steady state after :=
  ⟨⟨fixed.1, fixed.2.1, fixed.2.2.1⟩, fun _ => ⟨active.2.mono
    (getCurrentEpoch_le_activityFixedEpoch _), fun _ _ => by rw [fixed.2.2.2], effective, grows⟩⟩

/-- A step that keeps the fields and the registry is steady. -/
private theorem Steady.of_validators (fixed : Fixed state after)
    (validators : after.validators.data = state.validators.data) : Steady state after :=
  Steady.of_parts fixed (ActiveStep.of_validators validators fixed.1)
    (effectiveKept_data validators) (Nat.le_of_eq (by rw [validators]))

/-- A steady step keeps the proposer, when the mixes span more than the seed lookahead plus two. -/
private theorem Steady.proposer
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (steady : Steady state after) :
    getBeaconProposerIndex after = getBeaconProposerIndex state := by
  obtain ⟨⟨slot, lookahead, -⟩, early⟩ := steady
  by_cases fulu : Fork.fusaka ≤ fork
  · simp only [getBeaconProposerIndex, fulu, ↓reduceDIte, slot, lookahead]
  obtain ⟨active, mixes, effective, grows⟩ := early (Nat.lt_of_not_le fulu)
  have epoch : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  -- The seed reads the mix one epoch beyond the seed lookahead, never that of the write.
  have seed : getSeed after (getCurrentEpoch state) DOMAIN_BEACON_PROPOSER =
      getSeed state (getCurrentEpoch state) DOMAIN_BEACON_PROPOSER := by
    refine getSeed_eq_of_mix _ fun shifted shiftedEq => mixes shifted fun same => ?_
    have same := congrArg UInt64.toNat same
    rw [UInt64.toNat_mod, UInt64.toNat_mod] at same
    exact Nat.mod_ne_of_sub_lt (low := (getCurrentEpoch state).toNat) (high := shifted.toNat)
      (length := preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) (by omega) (by omega) same
  have checked := active.getActiveValidatorIndicesChecked_eq (UInt64.le_refl _)
  simp only [getBeaconProposerIndex, fulu, ↓reduceDIte, epoch, slot, seed, checked]
  cases getSeed state (getCurrentEpoch state) DOMAIN_BEACON_PROPOSER with
  | error => simp only [bind, Except.bind]
  | ok epochSeed =>
    cases listed : getActiveValidatorIndicesChecked state (getCurrentEpoch state) with
    | error => simp only [bind, Except.bind]
    | ok indices =>
      refine computeProposerIndex_validators fun candidate member => ?_
      -- Each candidate names a validator of the state, whose effective balance stays.
      obtain ⟨old, found, -⟩ :=
        (mem_iff_of_getActiveValidatorIndicesChecked_ok listed).mp (by simpa using member)
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have same := effective _ inside
      simp only [effectiveAt, found, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside grows),
        Option.map_some, Option.getD_some] at same ⊢
      rw [UInt64.toNat_inj.mp same]

/-! ## The operations of a block -/

/-- A step keeps a balance from rising, keeps what the proposer reads, and keeps the keys. -/
private def Kept (index : Nat) (state after : BeaconState preset fork) : Prop :=
  Down index state after ∧ Steady state after ∧ validatorKeys state <+: validatorKeys after

/-- A state keeps its own balance, proposer and keys. -/
private theorem Kept.refl (index : Nat) (state : BeaconState preset fork) :
    Kept index state state :=
  ⟨Down.refl index state, Steady.refl state, List.prefix_refl _⟩

/-- Two steps that keep a balance, the proposer and the keys keep them. -/
private theorem Kept.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : Kept index first second) (two : Kept index second third) : Kept index first third :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, one.2.2.trans two.2.2⟩

/-- A fold keeps a relation from its start when each step does, given the relation so far. -/
private theorem Kept.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    {start : BeaconState preset fork} {items : List α}
    (each : ∀ u x v, x ∈ items → Kept index start u → step u x = .ok v → Kept index u v) :
    ∀ {first last : BeaconState preset fork}, Kept index start first →
      items.foldlM step first = .ok last → Kept index start last := by
  induction items with
  | nil =>
    intro first last held computed
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ held
  | cons item rest more =>
    intro first last held computed
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    exact more (fun u x v member => each u x v (List.mem_cons_of_mem _ member))
      (held.trans (each _ _ _ List.mem_cons_self held stepped)) folded

/-- A slashing keeps what the proposer of the slot reads. -/
private theorem steady_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    Steady state after :=
  Steady.of_parts (fixed_slashValidator computed) (activeStep_slashValidator computed)
    (effectiveKept_slash computed)
    (frame_slashValidator computed).registryGrows

/-- A slashing with no whistleblower raises only the balance of the proposer after it. -/
private theorem down_slashValidator {slashedIndex proposer : ValidatorIndex}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : slashValidator config state slashedIndex none = .ok after)
    (read : getBeaconProposerIndex after = .ok proposer) {index : Nat}
    (other : proposer.toNat ≠ index) : Down index state after := by
  obtain ⟨_, _, _, _, _, _, _, lowered, chosen, _, raised, last, exitedOk, -, -, markedOk, -, -,
    -, loweredOk, chosenOk, -, raisedOk, lastOk, done⟩ := slashValidator_ok computed
  -- The proposer read in the slashing is the one after it, since the rest keeps it.
  have cancelled : Steady last after := by
    subst done
    split
    · exact Steady.of_validators ⟨rfl, rfl, rfl, rfl⟩ rfl
    · exact Steady.refl _
  have same : chosen = proposer := by
    rw [Steady.proposer apart cancelled, getBeaconProposerIndex_increaseBalance lastOk,
      getBeaconProposerIndex_increaseBalance raisedOk, chosenOk] at read
    exact Except.ok.inj read
  subst same
  simp only [Option.getD_none] at lastOk
  refine (down_initiateValidatorExit exitedOk index).trans <|
    ((down_setValidator markedOk index).trans (Down.of_balances rfl)).trans <|
    (down_decreaseBalance loweredOk index).trans <|
    (down_increaseBalance raisedOk other).trans <| (down_increaseBalance lastOk other).trans ?_
  subst done
  split <;> exact Down.of_balances rfl

/-- A slashing with no whistleblower keeps a balance other than the proposer's from rising. -/
private theorem kept_slashValidator {slashedIndex proposer : ValidatorIndex}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : slashValidator config state slashedIndex none = .ok after)
    (read : getBeaconProposerIndex state = .ok proposer) {index : Nat}
    (other : proposer.toNat ≠ index) : Kept index state after :=
  have steady := steady_slashValidator computed
  ⟨down_slashValidator apart computed ((Steady.proposer apart steady).trans read) other, steady,
    (frame_slashValidator computed).pubkeysPrefix⟩

/-- A proposer slashing raises no balance other than the proposer's. -/
private theorem kept_processProposerSlashing {slashing : ProposerSlashing}
    {proposer : ValidatorIndex}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : processProposerSlashing config checks state slashing = .ok after)
    (read : getBeaconProposerIndex state = .ok proposer) {index : Nat}
    (other : proposer.toNat ≠ index) : Kept index state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact kept_slashValidator apart slashed read other

/-- An attester slashing raises no balance other than the proposer's. -/
private theorem kept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    {proposer : ValidatorIndex}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : processAttesterSlashing config checks state slashing = .ok after)
    (read : getBeaconProposerIndex state = .ok proposer) {index : Nat}
    (other : proposer.toNat ≠ index) : Kept index state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine foldlM_ok_invariant (fun step => Kept index state step.1) (fun step _ next held ok => ?_)
    (show Kept index state (state, false).1 from Kept.refl index state) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact held.trans (kept_slashValidator apart slashed
      ((Steady.proposer apart held.2.1).trans read) other)
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ held

/-- An attestation raises no balance other than the proposer's. -/
private theorem kept_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot} {proposer : ValidatorIndex}
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (read : getBeaconProposerIndex state = .ok proposer) {index : Nat}
    (other : proposer.toNat ≠ index) : Kept index state after := by
  have registry := processAttestation_registry computed
  refine ⟨?_, Steady.of_validators (fixed_processAttestation computed)
    (congrArg (·.data) registry.1), (frame_processAttestation computed).pubkeysPrefix⟩
  by_cases altair : Fork.altair ≤ fork
  · rw [processAttestation_of_altair altair] at computed
    obtain ⟨_, _, _, chosen, -, -, -, chosenOk, _, -, -, balances⟩ :=
      processAttestationAltair_balance computed
    rw [read, Except.ok.injEq] at chosenOk
    subst chosenOk
    intro earlier found
    obtain ⟨final, atFinal, value⟩ := balances index earlier found
    simp only [other, ↓reduceIte, Nat.add_zero] at value
    exact ⟨final, atFinal, UInt64.le_of_eq (UInt64.toNat_inj.mp value)⟩
  · unfold processAttestation at computed
    simp only [altair, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
    have kept := recordPendingAttestation_ok recorded
    split at kept <;>
    · obtain ⟨_, rest⟩ := kept
      exact Down.of_balances (congrArg (·.balances) rest)

/-- A new validator lands after the registry, so it keeps the balance at a position of it. -/
private theorem down_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {index : Nat}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    (inside : index < state.validators.data.size) : Down index state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, indexOk, _, _, _, balancesOk, _, _, _, _, _, _, rfl⟩ := computed
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    intro earlier found
    refine ⟨earlier, ?_, UInt64.le_refl _⟩
    show _ = _
    rw [setOrAppendList_getElem? balancesOk, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact found
  · split at computed
    · cases computed
      intro earlier found
      have below := (Array.getElem?_eq_some_iff.mp found).1
      refine ⟨earlier, ?_, UInt64.le_refl _⟩
      show (state.balances.data.push amount)[index]? = some earlier
      rw [Array.getElem?_push, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact found
    · cases computed

/-- A deposit to another key keeps the balance at the position of a validator from rising. -/
private theorem down_applyPendingDeposit {index : Nat} {validator : Validator}
    {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (found : state.validators.data[index]? = some validator)
    (other : deposit.pubkey ≠ validator.pubkey) : Down index state after := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact Down.refl index _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact down_addValidatorToRegistry computed inside
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Down.refl index _
  · rename_i position located
    simp only [liftAccessor_ok, bind_ok_iff, liftArith, mapError_ok_iff] at computed
    obtain ⟨target, converted, raised⟩ := computed
    obtain ⟨there, keyed⟩ := Array.findIdx?_eq_some_iff_getElem.mp located
    refine down_increaseBalance raised ?_
    rw [(Uint64.ofNatChecked_ok_iff.mp converted).2]
    rintro rfl
    rw [Array.getElem?_eq_getElem there, Option.some.injEq] at found
    subst found
    exact other (beq_iff_eq.mp keyed.1).symm

/-- A deposit of a block to another key keeps the balance at the position of a validator. -/
private theorem down_processDeposit {before : fork < .hegota} {deposit : Deposit} {index : Nat}
    {validator : Validator}
    (computed : processDeposit config checks before state deposit = .ok after)
    (found : state.validators.data[index]? = some validator)
    (other : deposit.data.pubkey ≠ validator.pubkey) : Down index state after := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine (Down.of_balances (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans ?_
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
        exact (down_addValidatorToRegistry added inside).trans (Down.of_balances rfl)
      · cases applied
        exact Down.refl _ _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact Down.of_balances rfl
  · exact down_applyPendingDeposit applied found other

/-- A deposit of a block to another key keeps a balance from rising. -/
private theorem kept_processDeposit {before : fork < .hegota} {deposit : Deposit} {index : Nat}
    {validator : Validator}
    (computed : processDeposit config checks before state deposit = .ok after)
    (found : state.validators.data[index]? = some validator)
    (other : deposit.data.pubkey ≠ validator.pubkey) : Kept index state after :=
  ⟨down_processDeposit computed found other,
    Steady.of_parts (fixed_processDeposit computed) (activeStep_processDeposit computed)
      (effectiveKept_processDeposit computed) (frame_processDeposit computed).registryGrows,
    (frame_processDeposit computed).pubkeysPrefix⟩

/-- A voluntary exit keeps a balance, the proposer and the keys. -/
private theorem kept_processVoluntaryExit {signed : SignedVoluntaryExit} {index : Nat}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    Kept index state after :=
  ⟨down_initiateValidatorExit (processVoluntaryExit_initiates computed) index,
    Steady.of_parts (fixed_processVoluntaryExit computed) (activeStep_processVoluntaryExit computed)
      (effectiveKept_voluntaryExit computed) (frame_processVoluntaryExit computed).registryGrows,
    (frame_processVoluntaryExit computed).pubkeysPrefix⟩

/-- A change of credentials keeps a balance, the proposer and the keys. -/
private theorem kept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    {index : Nat} (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    Kept index state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact ⟨down_setValidator set index,
    Steady.of_parts (fixed_processBlsToExecutionChange computed)
      (activeStep_processBlsToExecutionChange computed) (effectiveKept_blsChange computed)
      (frame_processBlsToExecutionChange computed).registryGrows,
    (frame_processBlsToExecutionChange computed).pubkeysPrefix⟩

/-- A deposit request keeps a balance, the proposer and the keys. -/
private theorem kept_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    {index : Nat} (computed : processDepositRequest state electra request = .ok after) :
    Kept index state after :=
  ⟨down_processDepositRequest computed index,
    Steady.of_parts (fixed_processDepositRequest computed)
      (activeStep_processDepositRequest computed)
      (effectiveKept_depositRequest computed) (frame_processDepositRequest computed).registryGrows,
    (frame_processDepositRequest computed).pubkeysPrefix⟩

/-- A withdrawal request keeps a balance from rising. -/
private theorem kept_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest} {index : Nat}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    Kept index state after :=
  ⟨down_processWithdrawalRequest computed index,
    Steady.of_parts (fixed_processWithdrawalRequest computed)
      (activeStep_processWithdrawalRequest computed) (effectiveKept_withdrawalRequest computed)
      (frame_processWithdrawalRequest computed).registryGrows,
    (frame_processWithdrawalRequest computed).pubkeysPrefix⟩

/-- A consolidation request keeps a balance from rising. -/
private theorem kept_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest} {index : Nat}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    Kept index state after :=
  ⟨down_processConsolidationRequest computed index,
    Steady.of_parts (fixed_processConsolidationRequest computed)
      (activeStep_processConsolidationRequest computed)
      (effectiveKept_consolidationRequest computed)
      (frame_processConsolidationRequest computed).registryGrows,
    (frame_processConsolidationRequest computed).pubkeysPrefix⟩

/-- The steps of a fold that each keep a balance keep it. -/
private theorem kept_foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ s x t, step s x = .ok t → Kept index s t) {items : List α}
    (computed : items.foldlM step state = .ok after) : Kept index state after :=
  (foldlM_ok_steps (Kept index) (Kept.refl index) Kept.trans each computed).1

/-- The requests of the execution layer keep a balance from rising. -/
private theorem kept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam} {index : Nat}
    (computed : processExecutionRequests config state body electra = .ok after) :
    Kept index state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (kept_foldlM (fun _ _ _ ok => kept_processDepositRequest ok) depositsOk).trans <|
    (kept_foldlM (fun _ _ _ ok => kept_processWithdrawalRequest ok) withdrawalsOk).trans
      (kept_foldlM (fun _ _ _ ok => kept_processConsolidationRequest ok) consolidationsOk)

/-- The operations keep a balance other than the proposer's, whose key no deposit carries. -/
private theorem kept_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    {proposer : ValidatorIndex} {index : Nat} {validator : Validator}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : processOperations config checks state body parentSlot = .ok after)
    (read : getBeaconProposerIndex state = .ok proposer) (other : proposer.toNat ≠ index)
    (found : state.validators.data[index]? = some validator)
    (undeposited : ∀ before : fork < .hegota, ∀ deposit ∈ (body.deposits before).data,
      deposit.data.pubkey ≠ validator.pubkey) :
    Kept index state after := by
  -- Each state the operations pass through has the proposer and the key of the state before.
  have reads {u : BeaconState preset fork} (held : Kept index state u) :
      getBeaconProposerIndex u = .ok proposer :=
    (Steady.proposer apart held.2.1).trans read
  have proposers {u v : BeaconState preset fork} {slashings : List ProposerSlashing}
      (held : Kept index state u)
      (ok : slashings.foldlM (processProposerSlashing config checks) u = .ok v) :
      Kept index state v :=
    Kept.foldlM (fun _ _ _ _ held ok => kept_processProposerSlashing apart ok (reads held) other)
      held ok
  have attesters {u v : BeaconState preset fork} {slashings : List (AttesterSlashing preset fork)}
      (held : Kept index state u)
      (ok : slashings.foldlM (processAttesterSlashing config checks) u = .ok v) :
      Kept index state v :=
    Kept.foldlM (fun _ _ _ _ held ok => kept_processAttesterSlashing apart ok (reads held) other)
      held ok
  have attestations {u v : BeaconState preset fork} {votes : List (Attestation preset fork)}
      (held : Kept index state u)
      (ok : votes.foldlM (processAttestation config checks · parentSlot ·) u = .ok v) :
      Kept index state v :=
    Kept.foldlM (fun _ _ _ _ held ok => kept_processAttestation ok (reads held) other) held ok
  have exits {u v : BeaconState preset fork} {signed : List SignedVoluntaryExit}
      (held : Kept index state u)
      (ok : signed.foldlM (processVoluntaryExit config checks) u = .ok v) :
      Kept index state v :=
    held.trans (kept_foldlM (fun _ _ _ ok => kept_processVoluntaryExit ok) ok)
  have changes {u v : BeaconState preset fork} {signed : List SignedBLSToExecutionChange}
      (held : Kept index state u)
      (ok : signed.foldlM (processBlsToExecutionChange config checks) u = .ok v) :
      Kept index state v :=
    held.trans (kept_foldlM (fun _ _ _ ok => kept_processBlsToExecutionChange ok) ok)
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    refine (changes (exits (attestations (attesters (proposers (Kept.refl index state)
      proposersOk) attestersOk) attestedOk) exitsOk) changesOk).trans ?_
    refine kept_foldlM (fun _ _ _ ok => ?_) paid
    rw [processPayloadAttestation_eq ok]
    exact Kept.refl _ _
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have attested := attestations (attesters (proposers (Kept.refl index state) proposersOk)
    attestersOk) attestedOk
  -- No deposit carries the key, which each state keeps at the position.
  have deposited := Kept.foldlM (fun u deposit v member held ok => by
    obtain ⟨now, atNow, same⟩ := validators_getElem?_of_validatorKeys_prefix held.2.2 found
    refine kept_processDeposit ok atNow ?_
    rw [same]
    exact undeposited _ deposit (Array.mem_toList_iff.mp member)) attested depositedOk
  have changed : Kept index state changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact changes (exits deposited exitsOk) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ exits deposited exitsOk
  split at requestsOk
  · exact changed.trans (kept_processExecutionRequests requestsOk)
  · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
    exact requestsOk ▸ changed

/-! ## The steps of a block before its operations -/

/-- A step that keeps the fields, the balances and the registry keeps a balance. -/
private theorem Kept.of_eq {index : Nat} (fixed : Fixed state after)
    (balances : after.balances = state.balances)
    (validators : after.validators = state.validators) :
    Kept index state after :=
  ⟨Down.of_balances balances, Steady.of_validators fixed (by rw [validators]), by
    simp only [validatorKeys, validators]
    exact List.prefix_refl _⟩

/-- Applying the expected withdrawals keeps the fields. -/
private theorem fixed_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    Fixed state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : Fixed state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    refine Fixed.foldlM (fun _ _ _ ok => ?_) appliedOk
    rw [applyWithdrawal_eq ok]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have two : Fixed applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · obtain ⟨_, _, built⟩ := bind_ok_iff.mp indexedOk
      cases built
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases indexedOk
      exact Fixed.refl _
  have three : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → Fixed kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact Fixed.refl _
      · obtain ⟨_, _, built⟩ := bind_ok_iff.mp ok
        cases built
        exact ⟨rfl, rfl, rfl, rfl⟩
    · cases ok
      exact Fixed.refl _
  have queued : Fixed indexed (if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) electra expected.processedPartialWithdrawalsCount
    else if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) := by
    split <;> split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have four : Fixed finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last
    · cases last
    · cases last
      exact ⟨rfl, rfl, rfl, rfl⟩
  exact one.trans (two.trans (queued.trans ((three _ sweptOk).trans four)))

/-- The withdrawal step keeps the fields. -/
private theorem fixed_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : Fixed state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp computed
      exact fixed_applyExpectedWithdrawals (liftAccessor_ok.mp applied)
    · cases computed
      exact Fixed.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact fixed_applyExpectedWithdrawals applied

/-- The execution part of a block keeps a balance from rising. -/
private theorem kept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} {index : Nat}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Kept index state after := by
  have validators := processBlockExecution_validators computed
  suffices both : Down index state after ∧ Fixed state after from
    ⟨both.1, Steady.of_validators both.2 (by rw [validators]), by
      simp only [validatorKeys, validators]
      exact List.prefix_refl _⟩
  have withdrawals {s t : BeaconState preset fork} {capella : .shapella ≤ fork}
      {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
      (ok : processWithdrawals s capella payload = .ok t) : Down index s t ∧ Fixed s t :=
    ⟨down_processWithdrawals ok index, fixed_processWithdrawals ok⟩
  have payload {s t : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine s body execution = .ok t) :
      Down index s t ∧ Fixed s t := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    exact ⟨Down.of_balances rfl, rfl, rfl, rfl, rfl⟩
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact ⟨(withdrawals withdrawnOk).1.trans (Down.of_balances rfl),
      (withdrawals withdrawnOk).2.trans ⟨rfl, rfl, rfl, rfl⟩⟩
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact ⟨(withdrawals withdrawnOk).1.trans (payload paid).1,
      (withdrawals withdrawnOk).2.trans (payload paid).2⟩
  · dsimp only at computed
    split at computed
    · exact payload computed
    · cases computed
      exact ⟨Down.refl _ _, Fixed.refl _⟩

/-- From Gloas, the payload of the parent keeps a balance from rising, and keeps the fields. -/
private theorem down_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} {index : Nat}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    Down index state after ∧ Fixed state after := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, _, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk, buildersOk,
      exitsOk, -, rfl⟩
  · exact ⟨Down.refl _ _, Fixed.refl _⟩
  have settled := settleParentPayment_eq settledOk
  have builders {s t : BeaconState preset fork} {request : BuilderDepositRequest}
      (ok : processBuilderDepositRequest config checks s gloas request = .ok t) :
      Down index s t := by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
    exact Down.of_balances rfl
  have exits {s t : BeaconState preset fork} {request : BuilderExitRequest}
      (ok : processBuilderExitRequest config s gloas request = .ok t) : Down index s t := by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
    exact Down.of_balances rfl
  refine ⟨(Down.of_balances (by rw [settled])).trans <|
      (Down.foldlM (fun _ _ _ ok => down_processDepositRequest ok index) depositsOk).trans <|
      (Down.foldlM (fun _ _ _ ok => down_processWithdrawalRequest ok index) withdrawalsOk).trans <|
      (Down.foldlM (fun _ _ _ ok => down_processConsolidationRequest ok index)
        consolidationsOk).trans <|
      (Down.foldlM (fun _ _ _ ok => builders ok) buildersOk).trans <|
      (Down.foldlM (fun _ _ _ ok => exits ok) exitsOk).trans (Down.of_balances rfl), ?_⟩
  refine (show Fixed state _ by rw [settled]; exact ⟨rfl, rfl, rfl, rfl⟩).trans <|
    (Fixed.foldlM (fun _ _ _ ok => fixed_processDepositRequest ok) depositsOk).trans <|
    (Fixed.foldlM (fun _ _ _ ok => fixed_processWithdrawalRequest ok) withdrawalsOk).trans <|
    (Fixed.foldlM (fun _ _ _ ok => fixed_processConsolidationRequest ok) consolidationsOk).trans <|
    (Fixed.foldlM (fun _ _ _ ok => ?_) buildersOk).trans <|
    (Fixed.foldlM (fun _ _ _ ok => ?_) exitsOk).trans ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The header step reads the proposer of the block. -/
private theorem processBlockHeader_proposer {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) :
    getBeaconProposerIndex state = .ok block.proposerIndex := by
  unfold processBlockHeader at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, proposer, proposerOk, _, same, -⟩ := computed
  rw [proposerOk, same]

/-- The header step keeps a balance, the proposer and the keys. -/
private theorem kept_processBlockHeader {block : BeaconBlock preset fork} {index : Nat}
    (computed : processBlockHeader state block = .ok after) : Kept index state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact Kept.of_eq ⟨rfl, rfl, rfl, rfl⟩ rfl rfl

/-- The RANDAO step keeps a balance, the keys and what the proposer reads. -/
private theorem kept_processRandao {body : BeaconBlockBody preset fork} {index : Nat}
    (computed : processRandao config checks state body = .ok after) : Kept index state after := by
  have mixes := mixesKeptBut_processRandao computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact ⟨Down.of_balances rfl, ⟨⟨rfl, rfl, rfl⟩, fun _ => ⟨ActiveKept.of_validators rfl _, mixes,
    effectiveKept_data rfl, Nat.le_refl _⟩⟩, List.prefix_refl _⟩

/-- The vote on the deposit contract keeps a balance, the proposer and the keys. -/
private theorem kept_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    {index : Nat} (computed : processEth1Data before state body = .ok after) :
    Kept index state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact Kept.of_eq ⟨rfl, rfl, rfl, rfl⟩ rfl rfl

/-! ## The sync aggregate -/

/-- The sync rewards do not raise a balance when no signer and no paid proposer sit at it. -/
private theorem syncRewards_le {reward proposerReward index : Nat} {chosen : ValidatorIndex} :
    ∀ (members : List (ValidatorIndex × Bool)) (balance : Nat),
      (∀ member ∈ members, member.2 = true → member.1.toNat ≠ index ∧ chosen.toNat ≠ index) →
      members.foldl (fun balance member =>
        if member.2 then balance + (if member.1.toNat = index then reward else 0) +
          (if chosen.toNat = index then proposerReward else 0)
        else if member.1.toNat = index then balance - reward else balance) balance ≤ balance
  | [], _, _ => Nat.le_refl _
  | member :: members, balance, apart => by
    rw [List.foldl_cons]
    refine Nat.le_trans (syncRewards_le members _
      fun other inside => apart other (List.mem_cons_of_mem _ inside)) ?_
    have head := apart member List.mem_cons_self
    split
    · rename_i signed
      simp [(head signed).1, (head signed).2]
    · split
      · exact Nat.sub_le _ _
      · exact Nat.le_refl _

/-- A member whose bit is set has another position, when the key at the position never signs. -/
private theorem signers_elsewhere {pubkeys : Array Cryptography.Bls.BLSPubkey}
    {bits : Array Bool} {members : Array ValidatorIndex} {index : Nat} {validator : Validator}
    (membersOk : pubkeys.mapM (validatorIndexOfPubkey state) = .ok members)
    (found : state.validators.data[index]? = some validator)
    (unsigned : ∀ member ∈ (pubkeys.zip bits).toList, member.2 = true →
      member.1 ≠ validator.pubkey) :
    ∀ member ∈ (members.zip bits).toList, member.2 = true → member.1.toNat ≠ index := by
  intro member inside signed same
  have onList : pubkeys.toList.mapM (validatorIndexOfPubkey state) = .ok members.toList := by
    rw [← Array.toList_mapM, membersOk]
    rfl
  have length := mapM_ok_length onList
  rw [Array.toList_zip] at inside
  obtain ⟨k, bound, rfl⟩ := List.getElem_of_mem inside
  have small : k < pubkeys.toList.length ∧ k < bits.toList.length := by
    have := bound
    simp only [List.length_zip, Array.length_toList] at this length ⊢
    omega
  rw [List.getElem_zip] at signed same
  have image := mapM_ok_getElem onList k small.1
  -- The position of the member holds its key.
  unfold validatorIndexOfPubkey at image
  split at image
  · rename_i position located
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at image
    obtain ⟨there, keyed⟩ := Array.findIdx?_eq_some_iff_getElem.mp located
    rw [(Uint64.ofNatChecked_ok_iff.mp image).2] at same
    subst same
    rw [Array.getElem?_eq_getElem there, Option.some.injEq] at found
    subst found
    refine unsigned (pubkeys.toList[k], bits.toList[k]) ?_ signed (beq_iff_eq.mp keyed.1).symm
    have mem := List.getElem_mem (l := pubkeys.toList.zip bits.toList) (n := k)
      (by simp only [List.length_zip]; omega)
    rw [List.getElem_zip] at mem
    rwa [Array.toList_zip]
  · cases image

/-- The sync aggregate raises no balance other than the proposer's, whose key never signs. -/
private theorem down_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset} {proposer : ValidatorIndex} {index : Nat}
    {validator : Validator}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after)
    (read : getBeaconProposerIndex state = .ok proposer) (other : proposer.toNat ≠ index)
    (found : state.validators.data[index]? = some validator)
    (unsigned : ∀ member ∈ ((state.currentSyncCommittee altair).value.pubkeys.toArray.zip
      aggregate.syncCommitteeBits.bits.toArray).toList,
      member.2 = true → member.1 ≠ validator.pubkey) :
    Down index state after := by
  obtain ⟨_, _, members, chosen, -, -, membersOk, chosenOk, balances⟩ :=
    processSyncAggregate_balance computed
  have elsewhere := signers_elsewhere membersOk found unsigned
  intro earlier atIndex
  obtain ⟨final, atFinal, value⟩ := balances index earlier atIndex
  refine ⟨final, atFinal, UInt64.le_iff_toNat_le.mpr ?_⟩
  rw [value]
  refine syncRewards_le _ _ fun member inside signed => ⟨elsewhere member inside signed, ?_⟩
  rw [read, Except.ok.injEq] at chosenOk
  rw [← chosenOk ⟨member, inside, signed⟩]
  exact other

/-- A balance that stays and does not rise is not raised. -/
private theorem Down.balanceNotRaised {index : Nat} (down : Down index state after)
    (held : index < state.balances.data.size) : BalanceNotRaised index state after := by
  intro later found
  obtain ⟨final, atFinal, low⟩ := down _ (Array.getElem?_eq_getElem held)
  rw [found, Option.some.injEq] at atFinal
  subst atFinal
  exact ⟨_, Array.getElem?_eq_getElem held, low⟩

/-- A block raises no balance of a validator that it does not credit.

This holds when the block succeeds, at every fork.

The validator has a balance, and it is not the proposer of the block.

From Altair, no member that signs the sync aggregate has its key.

No deposit of the block carries its key; there are none from Heze.

Only the deposits before Electra credit a balance at once.

The mixes must span more than the seed lookahead plus two epochs. -/
theorem balanceNotRaised_processBlock
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (held : index < state.balances.data.size)
    (notProposer : block.proposerIndex.toNat ≠ index)
    (unsigned : ∀ altair : .altair ≤ fork,
      ∀ member ∈ ((state.currentSyncCommittee altair).value.pubkeys.toArray.zip
        (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray).toList,
        member.2 = true → member.1 ≠ validator.pubkey)
    (undeposited : ∀ before : fork < .hegota, ∀ deposit ∈ (block.body.deposits before).data,
      deposit.data.pubkey ≠ validator.pubkey) :
    BalanceNotRaised index state after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  obtain ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk, randaoOk,
    eth1Ok⟩ := started
  -- From Gloas the payload of the parent runs first, and keeps the fields and the keys.
  have paid : Down index state parented ∧ Fixed state parented ∧
      validatorKeys state <+: validatorKeys parented := by
    split at paidOk
    · exact ⟨(down_processParentExecutionPayload paidOk).1,
        (down_processParentExecutionPayload (index := index) paidOk).2,
        (frame_processParentExecutionPayload paidOk).pubkeysPrefix⟩
    · cases paidOk
      exact ⟨Down.refl _ _, Fixed.refl _, List.prefix_refl _⟩
  -- The header reads the proposer of the block, and the later steps keep it.
  have read := processBlockHeader_proposer headerOk
  have before : Kept index parented input := by
    refine (kept_processBlockHeader headerOk).trans (Kept.trans ?_
      ((kept_processRandao randaoOk).trans ?_))
    · split at executionOk
      · exact kept_processBlockExecution executionOk
      · cases executionOk
        exact Kept.refl _ _
    · split at eth1Ok
      · exact kept_processEth1Data eth1Ok
      · cases eth1Ok
        exact Kept.refl _ _
  obtain ⟨now, atNow, sameKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix (paid.2.2.trans before.2.2) found
  have kept := before.trans (kept_processOperations apart operated
    ((Steady.proposer apart before.2.1).trans read) notProposer atNow
    (by rw [sameKey]; exact undeposited))
  refine (paid.1.trans (kept.1.trans ?_)).balanceNotRaised held
  -- From Altair the sync aggregate reads the committee and the proposer of the state before.
  split at synced
  · rename_i altair
    obtain ⟨final, atFinal, finalKey⟩ :=
      validators_getElem?_of_validatorKeys_prefix (paid.2.2.trans kept.2.2) found
    have committee : last.currentSyncCommittee = state.currentSyncCommittee :=
      kept.2.1.1.2.2.trans paid.2.1.2.2.1
    refine down_processSyncAggregate synced ((Steady.proposer apart kept.2.1).trans read)
      notProposer atFinal ?_
    rw [committee, finalKey]
    exact unsigned altair
  · cases synced
    exact Down.refl _ _

end EthLib.Consensus
