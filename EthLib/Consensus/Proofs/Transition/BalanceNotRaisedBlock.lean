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

A block also keeps the inactivity score at each position of the registry before it.

A new validator takes a position at the end of the registry, so no earlier score moves.

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

/-! ## Balances that fall, rise or stay -/

/-- The balance at a position stays, and does not rise, from one state to another.

Unlike the shared relation of a balance not raised, the position must keep a balance. -/
def BalanceDown (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ∀ earlier, state.balances.data[index]? = some earlier →
    ∃ later, after.balances.data[index]? = some later ∧ later ≤ earlier

/-- The balance at a position stays, and does not fall, from one state to another. -/
def BalanceRises (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ∀ earlier, state.balances.data[index]? = some earlier →
    ∃ later, after.balances.data[index]? = some later ∧ earlier ≤ later

/-- The balance at a position stays the same from one state to another. -/
def BalanceStays (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ∀ earlier, state.balances.data[index]? = some earlier →
    after.balances.data[index]? = some earlier

/-- A state keeps each of its balances. -/
private theorem BalanceDown.refl (index : Nat) (state : BeaconState preset fork) :
    BalanceDown index state state :=
  fun earlier found => ⟨earlier, found, UInt64.le_refl _⟩

/-- Two steps that keep a balance from rising keep it from rising. -/
private theorem BalanceDown.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : BalanceDown index first second) (two : BalanceDown index second third) :
    BalanceDown index first third := by
  intro earlier found
  obtain ⟨middle, atMiddle, low⟩ := one earlier found
  obtain ⟨later, atLater, lower⟩ := two middle atMiddle
  exact ⟨later, atLater, UInt64.le_trans lower low⟩

/-- A step that keeps the balances keeps the balance at each position. -/
private theorem BalanceDown.of_balances {index : Nat} (same : after.balances = state.balances) :
    BalanceDown index state after := by
  intro earlier found
  exact ⟨earlier, by rw [same]; exact found, UInt64.le_refl _⟩

/-- A fold of steps that each keep a balance from rising keeps it. -/
private theorem BalanceDown.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ s x t, step s x = .ok t → BalanceDown index s t) {items : List α}
    (computed : items.foldlM step state = .ok after) : BalanceDown index state after :=
  (foldlM_ok_steps (BalanceDown index) (BalanceDown.refl index) BalanceDown.trans each computed).1

/-- Lowering a balance keeps every balance from rising. -/
private theorem down_decreaseBalance {position : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state position delta = .ok after) (index : Nat) :
    BalanceDown index state after := by
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
    (other : position.toNat ≠ index) : BalanceDown index state after := by
  obtain ⟨inside, -, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  intro earlier found
  simp only [BeaconState.putBalance, Array.getElem?_set, other, ↓reduceIte]
  exact ⟨earlier, found, UInt64.le_refl _⟩


/-- Setting a balance to at most its old value keeps every balance from rising. -/
private theorem down_setBalance {position : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance position balance = .ok after)
    (low : ∀ old, state.balances.data[position.toNat]? = some old → balance ≤ old)
    (index : Nat) : BalanceDown index state after := by
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
    BalanceDown index state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact BalanceDown.of_balances rfl

/-- An exit keeps the balances. -/
private theorem down_initiateValidatorExit {position : ValidatorIndex}
    (computed : initiateValidatorExit config state position = .ok after) (index : Nat) :
    BalanceDown index state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact BalanceDown.refl _ _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    exact (BalanceDown.of_balances rfl).trans (down_setValidator set index)

/-- A partial withdrawal request keeps the balances. -/
private theorem down_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {position : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra position validator amount owed =
      .ok after) (index : Nat) :
    BalanceDown index state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact BalanceDown.of_balances (computeExitEpochAndUpdateChurn_earliest churned).2.2
  · cases computed
    exact BalanceDown.refl _ _

/-- A withdrawal request keeps every balance from rising. -/
private theorem down_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) (index : Nat) :
    BalanceDown index state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BalanceDown.refl _ _)
    | exact down_initiateValidatorExit (liftAccessor_ok.mp computed) index
    | exact down_requestPartialWithdrawal computed index

/-- A switch to compounding credentials keeps every balance from rising. -/
private theorem down_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {position : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra position = .ok after) (index : Nat) :
    BalanceDown index state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, mid, set, queued⟩ := computed
  refine (down_setValidator set index).trans ?_
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨balance, found, queued⟩ := queued
  split at queued
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, lowered, rfl⟩ := queued
    refine (down_setBalance lowered (fun old atOld => ?_) index).trans (BalanceDown.of_balances rfl)
    simp only [getBalance, atOld] at found
    cases found
    exact UInt64.le_of_lt above
  · cases queued
    exact BalanceDown.refl _ _

/-- A queued consolidation keeps the balances. -/
private theorem down_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after)
    (index : Nat) : BalanceDown index state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (BalanceDown.of_balances
    (computeConsolidationEpochAndUpdateChurn_earliest churned).2.2).trans
    ((down_setValidator set index).trans (BalanceDown.of_balances rfl))

/-- A consolidation request keeps every balance from rising. -/
private theorem down_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after)
    (index : Nat) : BalanceDown index state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BalanceDown.refl _ _)
    | exact down_switchToCompoundingValidator (liftAccessor_ok.mp computed) index
    | exact down_queueConsolidation computed index

/-- A deposit request keeps the balances. -/
private theorem down_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) (index : Nat) :
    BalanceDown index state after :=
  BalanceDown.of_balances (processDepositRequest_ok computed).2.2

/-- The withdrawals lower balances, and from Gloas those of builders. -/
private theorem down_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) (index : Nat) :
    BalanceDown index state after := by
  have applied {s t : BeaconState preset fork} {expected : ExpectedWithdrawals}
      (ok : applyExpectedWithdrawals s capella expected = .ok t) : BalanceDown index s t := by
    obtain ⟨mid, midOk, balances, -⟩ := applyExpectedWithdrawals_balances ok
    refine BalanceDown.trans ?_ (BalanceDown.of_balances balances)
    unfold applyWithdrawals at midOk
    rw [← Array.foldlM_toList] at midOk
    refine BalanceDown.foldlM (fun u withdrawal v step => ?_) midOk
    unfold applyWithdrawal at step
    split at step
    · simp only [bind_ok_iff] at step
      obtain ⟨_, _, set⟩ := step
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      exact BalanceDown.of_balances rfl
    · exact down_decreaseBalance step index
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp computed
      exact applied (liftAccessor_ok.mp ok)
    · cases computed
      exact BalanceDown.refl _ _
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

/-- The registry does not shrink, and each of its earlier positions keeps its inactivity score. -/
def BlockScored (state after : BeaconState preset fork) : Prop :=
  state.validators.data.size ≤ after.validators.data.size ∧
    ∀ i < state.validators.data.size, ScoreKept i state after

/-- A state keeps its own registry and scores. -/
private theorem BlockScored.refl (state : BeaconState preset fork) : BlockScored state state :=
  ⟨Nat.le_refl _, fun i _ => ScoreKept.refl i state⟩

/-- Two steps that keep the scores of the registry keep them. -/
private theorem BlockScored.trans {first second third : BeaconState preset fork}
    (one : BlockScored first second) (two : BlockScored second third) : BlockScored first third :=
  ⟨Nat.le_trans one.1 two.1,
    fun i below => (one.2 i below).trans (two.2 i (Nat.lt_of_lt_of_le below one.1))⟩

/-- A step that keeps the registry and the scores keeps the scores of the registry. -/
private theorem BlockScored.of_eq (validators : after.validators = state.validators)
    (scores : after.inactivityScores = state.inactivityScores) : BlockScored state after :=
  ⟨Nat.le_of_eq (by rw [validators]), fun i _ => ScoreKept.of_scores scores i⟩

/-- A step keeps the slot, the proposer lookahead, the current sync committee and the mixes.

The registry does not shrink, and each of its earlier positions keeps its inactivity score. -/
def BlockFixed (state after : BeaconState preset fork) : Prop :=
  after.slot = state.slot ∧ after.proposerLookahead = state.proposerLookahead ∧
    after.currentSyncCommittee = state.currentSyncCommittee ∧
    after.randaoMixes = state.randaoMixes ∧ BlockScored state after

/-- A step keeps the fields when it keeps each of them and the scores.

It also needs the registry not to shrink. -/
private theorem BlockFixed.of_eq (slot : after.slot = state.slot := by rfl)
    (proposerLookahead : after.proposerLookahead = state.proposerLookahead := by rfl)
    (currentSyncCommittee : after.currentSyncCommittee = state.currentSyncCommittee := by rfl)
    (randaoMixes : after.randaoMixes = state.randaoMixes := by rfl)
    (grows : state.validators.data.size ≤ after.validators.data.size := by
      exact Nat.le_refl _)
    (scores : after.inactivityScores = state.inactivityScores := by rfl) :
    BlockFixed state after :=
  ⟨slot, proposerLookahead, currentSyncCommittee, randaoMixes, grows,
    fun i _ => ScoreKept.of_scores scores i⟩

/-- A state keeps its own fields. -/
theorem BlockFixed.refl (state : BeaconState preset fork) : BlockFixed state state :=
  BlockFixed.of_eq

/-- Two steps that keep the fields keep them. -/
private theorem BlockFixed.trans {first second third : BeaconState preset fork}
    (one : BlockFixed first second) (two : BlockFixed second third) : BlockFixed first third :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, one.2.2.2.2.trans two.2.2.2.2⟩

/-- A fold of steps that keep the fields keeps them. -/
private theorem BlockFixed.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ s x t, step s x = .ok t → BlockFixed s t) {items : List α}
    (computed : items.foldlM step state = .ok after) : BlockFixed state after :=
  (foldlM_ok_steps BlockFixed BlockFixed.refl BlockFixed.trans each computed).1

/-- A write to a validator keeps the fields. -/
private theorem fixed_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : BlockFixed state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact BlockFixed.of_eq (grows := by simp [BeaconState.putValidator])

/-- A write to a balance keeps the fields. -/
private theorem fixed_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : BlockFixed state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact BlockFixed.of_eq

/-- Raising a balance keeps the fields. -/
private theorem fixed_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : BlockFixed state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  exact fixed_setBalance set

/-- Lowering a balance keeps the fields. -/
private theorem fixed_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : BlockFixed state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  exact fixed_setBalance set

/-- An exit keeps the fields. -/
private theorem fixed_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : BlockFixed state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact BlockFixed.refl _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    refine BlockFixed.trans ?_ (fixed_setValidator set)
    exact BlockFixed.of_eq

/-- A slashing keeps the fields. -/
private theorem fixed_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    BlockFixed state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, last, exitedOk, -, -, markedOk, -, -, -, loweredOk, -, -,
    raisedOk, lastOk, done⟩ := slashValidator_ok computed
  have cancelled : BlockFixed last after := by
    subst done
    split
    · exact BlockFixed.of_eq
    · exact BlockFixed.refl _
  refine (fixed_initiateValidatorExit exitedOk).trans <|
    ((fixed_setValidator markedOk).trans ?_).trans <|
    (fixed_decreaseBalance loweredOk).trans <|
    (fixed_increaseBalance raisedOk).trans <|
    (fixed_increaseBalance lastOk).trans cancelled
  exact BlockFixed.of_eq

/-- A deposit request keeps the fields. -/
private theorem fixed_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    BlockFixed state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact BlockFixed.of_eq

/-- A partial withdrawal request keeps the fields. -/
private theorem fixed_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    BlockFixed state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    exact BlockFixed.of_eq
  · cases computed
    exact BlockFixed.refl _

/-- A withdrawal request keeps the fields. -/
private theorem fixed_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    BlockFixed state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BlockFixed.refl _)
    | exact fixed_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact fixed_requestPartialWithdrawal computed

/-- A switch to compounding credentials keeps the fields. -/
private theorem fixed_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    BlockFixed state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  refine (fixed_setValidator set).trans ?_
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    exact (fixed_setBalance set).trans BlockFixed.of_eq
  · cases queued
    exact BlockFixed.refl _

/-- A queued consolidation keeps the fields. -/
private theorem fixed_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    BlockFixed state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  refine (BlockFixed.trans ?_ (fixed_setValidator set)).trans ?_ <;> exact BlockFixed.of_eq

/-- A consolidation request keeps the fields. -/
private theorem fixed_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    BlockFixed state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BlockFixed.refl _)
    | exact fixed_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact fixed_queueConsolidation computed

/-- One step of an attester slashing keeps the fields. -/
private theorem fixed_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    BlockFixed step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact fixed_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BlockFixed.refl _

/-- An attestation keeps the fields. -/
private theorem fixed_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    BlockFixed state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : BlockFixed raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact BlockFixed.of_eq
      · cases final
        exact BlockFixed.refl _
    have flags : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        BlockFixed state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact BlockFixed.of_eq
    exact (flags _ _).trans ((fixed_increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact BlockFixed.of_eq

/-- A new validator keeps the fields.

It lands at the end of the registry, so each validator before it keeps its score. -/
private theorem fixed_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    BlockFixed state after := by
  have grows : state.validators.data.size ≤ after.validators.data.size := by
    rw [addValidatorToRegistry_validators_eq_push computed, Array.size_push]
    exact Nat.le_succ _
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, indexOk, _, _, _, _, _, _, _, _, _, scoresOk, rfl⟩ := computed
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    refine ⟨rfl, rfl, rfl, rfl, grows, fun i below _ => ?_⟩
    show _ = _
    rw [setOrAppendList_getElem? scoresOk, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · split at computed
    · cases computed
      exact BlockFixed.of_eq (grows := grows)
    · cases computed

/-- A deposit keeps the fields. -/
private theorem fixed_applyDeposit {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDeposit config checks state pubkey withdrawalCredentials amount signature =
      .ok after) :
    BlockFixed state after := by
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
        exact (fixed_addValidatorToRegistry added).trans BlockFixed.of_eq
      · cases computed
        exact BlockFixed.refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact BlockFixed.of_eq
  · rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact BlockFixed.refl _
    · exact fixed_increaseBalance raised
    · exact fixed_addValidatorToRegistry added

/-- A deposit of a block keeps the fields. -/
private theorem fixed_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    BlockFixed state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact BlockFixed.trans (second := { state with eth1DepositIndex := fun _ => next })
    BlockFixed.of_eq
    (fixed_applyDeposit applied)

/-- A voluntary exit keeps the fields. -/
private theorem fixed_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    BlockFixed state after :=
  fixed_initiateValidatorExit (processVoluntaryExit_initiates computed)

/-- A change of credentials keeps the fields. -/
private theorem fixed_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    BlockFixed state after := by
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
private theorem Steady.of_parts (fixed : BlockFixed state after) (active : ActiveStep state after)
    (effective : EffectiveKept state after)
    (grows : state.validators.data.size ≤ after.validators.data.size) : Steady state after :=
  ⟨⟨fixed.1, fixed.2.1, fixed.2.2.1⟩, fun _ => ⟨active.2.mono
    (getCurrentEpoch_le_activityFixedEpoch _), fun _ _ => by rw [fixed.2.2.2.1], effective, grows⟩⟩

/-- A step that keeps the fields and the registry is steady. -/
private theorem Steady.of_validators (fixed : BlockFixed state after)
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
  BalanceDown index state after ∧ Steady state after ∧ validatorKeys state <+: validatorKeys after

/-- A state keeps its own balance, proposer and keys. -/
private theorem Kept.refl (index : Nat) (state : BeaconState preset fork) :
    Kept index state state :=
  ⟨BalanceDown.refl index state, Steady.refl state, List.prefix_refl _⟩

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
      items.foldlM step first = .ok last → Kept index start last :=
  foldlM_ok_invariant_of_mem (Kept index start)
    (fun _ _ _ member held computed => held.trans (each _ _ _ member held computed))

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
    (other : proposer.toNat ≠ index) : BalanceDown index state after := by
  obtain ⟨_, _, _, _, _, _, _, lowered, chosen, _, raised, last, exitedOk, -, -, markedOk, -, -,
    -, loweredOk, chosenOk, -, raisedOk, lastOk, done⟩ := slashValidator_ok computed
  -- The proposer read in the slashing is the one after it, since the rest keeps it.
  have cancelled : Steady last after := by
    subst done
    split
    · exact Steady.of_validators BlockFixed.of_eq rfl
    · exact Steady.refl _
  have same : chosen = proposer := by
    rw [Steady.proposer apart cancelled, getBeaconProposerIndex_increaseBalance lastOk,
      getBeaconProposerIndex_increaseBalance raisedOk, chosenOk] at read
    exact Except.ok.inj read
  subst same
  simp only [Option.getD_none] at lastOk
  refine (down_initiateValidatorExit exitedOk index).trans <|
    ((down_setValidator markedOk index).trans (BalanceDown.of_balances rfl)).trans <|
    (down_decreaseBalance loweredOk index).trans <|
    (down_increaseBalance raisedOk other).trans <| (down_increaseBalance lastOk other).trans ?_
  subst done
  split <;> exact BalanceDown.of_balances rfl

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
      exact BalanceDown.of_balances (congrArg (·.balances) rest)

/-- A new validator lands after the registry, so it keeps the balance at a position of it. -/
theorem addValidatorToRegistry_balance {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {index : Nat}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    (inside : index < state.validators.data.size) {earlier : Gwei}
    (found : state.balances.data[index]? = some earlier) :
    after.balances.data[index]? = some earlier := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, indexOk, _, _, _, balancesOk, _, _, _, _, _, _, rfl⟩ := computed
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    show _ = _
    rw [setOrAppendList_getElem? balancesOk, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact found
  · split at computed
    · cases computed
      have below := (Array.getElem?_eq_some_iff.mp found).1
      show (state.balances.data.push amount)[index]? = some earlier
      rw [Array.getElem?_push, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact found
    · cases computed

/-- A new validator keeps the balance at a position of the registry from rising. -/
private theorem down_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {index : Nat}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    (inside : index < state.validators.data.size) : BalanceDown index state after := by
  intro earlier found
  exact ⟨earlier, addValidatorToRegistry_balance computed inside found, UInt64.le_refl _⟩

/-- A deposit to another key keeps the balance at the position of a validator from rising. -/
private theorem down_applyPendingDeposit {index : Nat} {validator : Validator}
    {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (found : state.validators.data[index]? = some validator)
    (other : deposit.pubkey ≠ validator.pubkey) : BalanceDown index state after := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact BalanceDown.refl index _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact down_addValidatorToRegistry computed inside
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ BalanceDown.refl index _
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
theorem down_processDeposit {before : fork < .hegota} {deposit : Deposit} {index : Nat}
    {validator : Validator}
    (computed : processDeposit config checks before state deposit = .ok after)
    (found : state.validators.data[index]? = some validator)
    (other : deposit.data.pubkey ≠ validator.pubkey) : BalanceDown index state after := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine (BalanceDown.of_balances
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans ?_
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
        exact (down_addValidatorToRegistry added inside).trans (BalanceDown.of_balances rfl)
      · cases applied
        exact BalanceDown.refl _ _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact BalanceDown.of_balances rfl
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
private theorem Kept.of_eq {index : Nat} (fixed : BlockFixed state after)
    (balances : after.balances = state.balances)
    (validators : after.validators = state.validators) :
    Kept index state after :=
  ⟨BalanceDown.of_balances balances, Steady.of_validators fixed (by rw [validators]), by
    simp only [validatorKeys, validators]
    exact List.prefix_refl _⟩

/-- Applying the expected withdrawals keeps the fields. -/
private theorem fixed_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    BlockFixed state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : BlockFixed state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    refine BlockFixed.foldlM (fun _ _ _ ok => ?_) appliedOk
    rw [applyWithdrawal_eq ok]
    exact BlockFixed.of_eq
  have two : BlockFixed applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · obtain ⟨_, _, built⟩ := bind_ok_iff.mp indexedOk
      cases built
      exact BlockFixed.of_eq
    · cases indexedOk
      exact BlockFixed.refl _
  have three : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → BlockFixed kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact BlockFixed.refl _
      · obtain ⟨_, _, built⟩ := bind_ok_iff.mp ok
        cases built
        exact BlockFixed.of_eq
    · cases ok
      exact BlockFixed.refl _
  have queued : BlockFixed indexed (if electra : .pectra ≤ fork then
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
    split <;> split <;> exact BlockFixed.of_eq
  have four : BlockFixed finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last
    · cases last
    · cases last
      exact BlockFixed.of_eq
  exact one.trans (two.trans (queued.trans ((three _ sweptOk).trans four)))

/-- The withdrawal step keeps the fields. -/
private theorem fixed_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : BlockFixed state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp computed
      exact fixed_applyExpectedWithdrawals (liftAccessor_ok.mp applied)
    · cases computed
      exact BlockFixed.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact fixed_applyExpectedWithdrawals applied

/-- The execution part of a block keeps a balance from rising, and keeps the fields. -/
theorem down_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} {index : Nat}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    BalanceDown index state after ∧ BlockFixed state after := by
  have withdrawals {s t : BeaconState preset fork} {capella : .shapella ≤ fork}
      {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
      (ok : processWithdrawals s capella payload = .ok t) :
      BalanceDown index s t ∧ BlockFixed s t :=
    ⟨down_processWithdrawals ok index, fixed_processWithdrawals ok⟩
  have payload {s t : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine s body execution = .ok t) :
      BalanceDown index s t ∧ BlockFixed s t := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    exact ⟨BalanceDown.of_balances rfl, BlockFixed.of_eq⟩
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact ⟨(withdrawals withdrawnOk).1.trans (BalanceDown.of_balances rfl),
      (withdrawals withdrawnOk).2.trans BlockFixed.of_eq⟩
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact ⟨(withdrawals withdrawnOk).1.trans (payload paid).1,
      (withdrawals withdrawnOk).2.trans (payload paid).2⟩
  · dsimp only at computed
    split at computed
    · exact payload computed
    · cases computed
      exact ⟨BalanceDown.refl _ _, BlockFixed.refl _⟩

/-- The execution part of a block keeps a balance from rising. -/
private theorem kept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} {index : Nat}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Kept index state after := by
  have validators := processBlockExecution_validators computed
  have both := down_processBlockExecution (index := index) computed
  exact ⟨both.1, Steady.of_validators both.2 (by rw [validators]), by
    simp only [validatorKeys, validators]
    exact List.prefix_refl _⟩

/-- From Gloas, the payload of the parent keeps a balance from rising, and keeps the fields. -/
theorem down_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} {index : Nat}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    BalanceDown index state after ∧ BlockFixed state after := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, _, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk, buildersOk,
      exitsOk, -, rfl⟩
  · exact ⟨BalanceDown.refl _ _, BlockFixed.refl _⟩
  have settled := settleParentPayment_eq settledOk
  have builders {s t : BeaconState preset fork} {request : BuilderDepositRequest}
      (ok : processBuilderDepositRequest config checks s gloas request = .ok t) :
      BalanceDown index s t := by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
    exact BalanceDown.of_balances rfl
  have exits {s t : BeaconState preset fork} {request : BuilderExitRequest}
      (ok : processBuilderExitRequest config s gloas request = .ok t) : BalanceDown index s t := by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
    exact BalanceDown.of_balances rfl
  refine ⟨(BalanceDown.of_balances (by rw [settled])).trans <|
      (BalanceDown.foldlM (fun _ _ _ ok => down_processDepositRequest ok index) depositsOk).trans <|
      (BalanceDown.foldlM (fun _ _ _ ok => down_processWithdrawalRequest ok index)
        withdrawalsOk).trans <|
      (BalanceDown.foldlM (fun _ _ _ ok => down_processConsolidationRequest ok index)
        consolidationsOk).trans <|
      (BalanceDown.foldlM (fun _ _ _ ok => builders ok) buildersOk).trans <|
      (BalanceDown.foldlM (fun _ _ _ ok => exits ok) exitsOk).trans
        (BalanceDown.of_balances rfl), ?_⟩
  refine (show BlockFixed state _ by rw [settled]; exact BlockFixed.of_eq).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => fixed_processDepositRequest ok) depositsOk).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => fixed_processWithdrawalRequest ok) withdrawalsOk).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => fixed_processConsolidationRequest ok)
      consolidationsOk).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => ?_) buildersOk).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => ?_) exitsOk).trans BlockFixed.of_eq
  · obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
    exact BlockFixed.of_eq
  · obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
    exact BlockFixed.of_eq

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
  exact Kept.of_eq BlockFixed.of_eq rfl rfl

/-- The RANDAO step keeps a balance, the keys and what the proposer reads. -/
private theorem kept_processRandao {body : BeaconBlockBody preset fork} {index : Nat}
    (computed : processRandao config checks state body = .ok after) : Kept index state after := by
  have mixes := mixesKeptBut_processRandao computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact ⟨BalanceDown.of_balances rfl, ⟨⟨rfl, rfl, rfl⟩,
    fun _ => ⟨ActiveKept.of_validators rfl _, mixes, effectiveKept_data rfl, Nat.le_refl _⟩⟩,
    List.prefix_refl _⟩

/-- The vote on the deposit contract keeps a balance, the proposer and the keys. -/
private theorem kept_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    {index : Nat} (computed : processEth1Data before state body = .ok after) :
    Kept index state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact Kept.of_eq BlockFixed.of_eq rfl rfl

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

/-- A member with a bit has another position, when no key with that bit is the key there. -/
theorem signers_elsewhere {pubkeys : Array Cryptography.Bls.BLSPubkey}
    {bits : Array Bool} {members : Array ValidatorIndex} {index : Nat} {validator : Validator}
    {bit : Bool} (membersOk : pubkeys.mapM (validatorIndexOfPubkey state) = .ok members)
    (found : state.validators.data[index]? = some validator)
    (unsigned : ∀ member ∈ (pubkeys.zip bits).toList, member.2 = bit →
      member.1 ≠ validator.pubkey) :
    ∀ member ∈ (members.zip bits).toList, member.2 = bit → member.1.toNat ≠ index := by
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
    BalanceDown index state after := by
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
private theorem BalanceDown.balanceNotRaised {index : Nat} (down : BalanceDown index state after)
    (held : index < state.balances.data.size) : BalanceNotRaised index state after := by
  intro later found
  obtain ⟨final, atFinal, low⟩ := down _ (Array.getElem?_eq_getElem held)
  rw [found, Option.some.injEq] at atFinal
  subst atFinal
  exact ⟨_, Array.getElem?_eq_getElem held, low⟩

/-- A block keeps the balance of a validator that it does not credit, and does not raise it. -/
private theorem down_processBlock
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (notProposer : block.proposerIndex.toNat ≠ index)
    (unsigned : ∀ altair : .altair ≤ fork,
      ∀ member ∈ ((state.currentSyncCommittee altair).value.pubkeys.toArray.zip
        (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray).toList,
        member.2 = true → member.1 ≠ validator.pubkey)
    (undeposited : ∀ before : fork < .hegota, ∀ deposit ∈ (block.body.deposits before).data,
      deposit.data.pubkey ≠ validator.pubkey) :
    BalanceDown index state after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  obtain ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk, randaoOk,
    eth1Ok⟩ := started
  -- From Gloas the payload of the parent runs first, and keeps the fields and the keys.
  have paid : BalanceDown index state parented ∧ BlockFixed state parented ∧
      validatorKeys state <+: validatorKeys parented := by
    split at paidOk
    · exact ⟨(down_processParentExecutionPayload paidOk).1,
        (down_processParentExecutionPayload (index := index) paidOk).2,
        (frame_processParentExecutionPayload paidOk).pubkeysPrefix⟩
    · cases paidOk
      exact ⟨BalanceDown.refl _ _, BlockFixed.refl _, List.prefix_refl _⟩
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
  refine paid.1.trans (kept.1.trans ?_)
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
    exact BalanceDown.refl _ _

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
    BalanceNotRaised index state after :=
  (down_processBlock apart computed found notProposer unsigned undeposited).balanceNotRaised held

/-- A block keeps a balance at the position of a validator that it does not credit.

The hypotheses are the ones under which the block raises no balance of that validator. -/
theorem balance_lt_size_processBlock
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
    index < after.balances.data.size := by
  obtain ⟨later, atLater, -⟩ :=
    down_processBlock apart computed found notProposer unsigned undeposited _
      (Array.getElem?_eq_getElem held)
  exact (Array.getElem?_eq_some_iff.mp atLater).1

/-! ## The inactivity scores -/

/-- A proposer slashing keeps the fields. -/
private theorem fixed_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    BlockFixed state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact fixed_slashValidator slashed

/-- An attester slashing keeps the fields. -/
private theorem fixed_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    BlockFixed state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => BlockFixed state step.1)
    (fun _ _ _ held ok => held.trans (fixed_slashIfSlashable ok))
    (show BlockFixed state (state, false).1 from BlockFixed.refl state) folded

/-- The requests of the execution layer keep the fields. -/
private theorem fixed_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    BlockFixed state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (BlockFixed.foldlM (fun _ _ _ ok => fixed_processDepositRequest ok) depositsOk).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => fixed_processWithdrawalRequest ok) withdrawalsOk).trans
      (BlockFixed.foldlM (fun _ _ _ ok => fixed_processConsolidationRequest ok) consolidationsOk)

/-- The operations of a block keep the fields. -/
theorem fixed_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    BlockFixed state after := by
  obtain ⟨_, _, _, proposersOk, attestersOk, attestedOk, rest⟩ :=
    processOperations_folds_of BlockFixed BlockFixed.refl BlockFixed.trans fixed_processDeposit
      fixed_processVoluntaryExit fixed_processBlsToExecutionChange
      fixed_processExecutionRequests (fun ok => by
        rw [processPayloadAttestation_eq ok]
        exact BlockFixed.refl _) computed
  exact (BlockFixed.foldlM (fun _ _ _ ok => fixed_processProposerSlashing ok) proposersOk).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => fixed_processAttesterSlashing ok) attestersOk).trans <|
    (BlockFixed.foldlM (fun _ _ _ ok => fixed_processAttestation ok) attestedOk).trans rest

/-- A block keeps the inactivity score at each position of the registry before it.

This holds when the block succeeds; before Altair there are no scores.

A new validator takes the position at the end of the registry, so it moves no earlier score. -/
theorem scoreKept_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) {index : Nat}
    (inside : index < state.validators.data.size) : ScoreKept index state after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  -- The steps before the operations write no score, and keep the registry or grow it.
  have before : BlockScored state input :=
    started.step_of BlockScored BlockScored.refl BlockScored.trans
      (fun _ ok => (down_processParentExecutionPayload (index := 0) ok).2.2.2.2.2)
      (fun ok => by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
        exact BlockScored.of_eq rfl rfl)
      (fun _ ok => (down_processBlockExecution (index := 0) ok).2.2.2.2.2)
      (fun ok => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
        exact BlockScored.of_eq rfl rfl)
      (fun _ ok => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
        rw [← rest]
        exact BlockScored.of_eq rfl rfl)
  -- From Altair the sync aggregate changes only the balances.
  have synced : BlockScored last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact BlockScored.of_eq rfl rfl
    · cases synced
      exact BlockScored.refl _
  exact ((before.trans (fixed_processOperations operated).2.2.2.2).trans synced).2 index inside

/-! ## The proposer through the steps of a block -/

/-- A proposer slashing keeps what the proposer of the slot reads. -/
private theorem steady_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    Steady state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact steady_slashValidator slashed

/-- An attester slashing keeps what the proposer of the slot reads. -/
private theorem steady_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    Steady state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine foldlM_ok_invariant (fun step => Steady state step.1) (fun step _ next held ok => ?_)
    (show Steady state (state, false).1 from Steady.refl state) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact held.trans (steady_slashValidator slashed)
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ held

/-- An attestation keeps what the proposer of the slot reads. -/
private theorem steady_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    Steady state after :=
  Steady.of_validators (fixed_processAttestation computed)
    (congrArg (·.data) (processAttestation_registry computed).1)

/-- A deposit of a block keeps what the proposer of the slot reads. -/
private theorem steady_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    Steady state after :=
  Steady.of_parts (fixed_processDeposit computed) (activeStep_processDeposit computed)
    (effectiveKept_processDeposit computed) (frame_processDeposit computed).registryGrows

/-- The operations of a block keep the proposer of the slot and the current sync committee.

The mixes must span more than the seed lookahead plus two epochs. -/
theorem processOperations_proposer
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    getBeaconProposerIndex after = getBeaconProposerIndex state ∧
      after.currentSyncCommittee = state.currentSyncCommittee := by
  obtain ⟨_, _, _, proposersOk, attestersOk, attestedOk, rest⟩ :=
    processOperations_folds_of Steady Steady.refl Steady.trans steady_processDeposit
      (fun ok => (kept_processVoluntaryExit (index := 0) ok).2.1)
      (fun ok => (kept_processBlsToExecutionChange (index := 0) ok).2.1)
      (fun ok => (kept_processExecutionRequests (index := 0) ok).2.1)
      (fun ok => by
        rw [processPayloadAttestation_eq ok]
        exact Steady.refl _) computed
  have steady : Steady state after :=
    (foldlM_ok_steps Steady Steady.refl Steady.trans
      (fun _ _ _ ok => steady_processProposerSlashing ok) proposersOk).1.trans <|
    (foldlM_ok_steps Steady Steady.refl Steady.trans
      (fun _ _ _ ok => steady_processAttesterSlashing ok) attestersOk).1.trans <|
    (foldlM_ok_steps Steady Steady.refl Steady.trans
      (fun _ _ _ ok => steady_processAttestation ok) attestedOk).1.trans rest
  exact ⟨Steady.proposer apart steady, steady.1.2.2⟩

/-- The steps of a block before its operations end at a state whose proposer is that of the block.

They keep the current sync committee, and keep each balance from rising.

The mixes must span more than the seed lookahead plus two epochs. -/
theorem operationsInput_proposer
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork} {input : BeaconState preset fork}
    (started : OperationsInput config checks engine state block input) :
    getBeaconProposerIndex input = .ok block.proposerIndex ∧
      input.currentSyncCommittee = state.currentSyncCommittee ∧
      ∀ index, BalanceDown index state input := by
  obtain ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk, randaoOk,
    eth1Ok⟩ := started
  -- From Gloas the payload of the parent runs first, and keeps the fields.
  have paid : (∀ index, BalanceDown index state parented) ∧ BlockFixed state parented := by
    split at paidOk
    · exact ⟨fun index => (down_processParentExecutionPayload (index := index) paidOk).1,
        (down_processParentExecutionPayload (index := 0) paidOk).2⟩
    · cases paidOk
      exact ⟨fun index => BalanceDown.refl _ _, BlockFixed.refl _⟩
  -- The header reads the proposer of the block, and the later steps keep it.
  have read := processBlockHeader_proposer headerOk
  have before : ∀ index, Kept index parented input := by
    intro index
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
  exact ⟨(Steady.proposer apart (before 0).2.1).trans read,
    (before 0).2.1.1.2.2.trans paid.2.2.2.1, fun index => (paid.1 index).trans (before index).1⟩

end EthLib.Consensus
