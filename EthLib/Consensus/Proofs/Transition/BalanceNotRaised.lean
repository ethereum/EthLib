module

public import EthLib.Consensus.Proofs.Transition.EpochDecomposition
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Totality.EffectiveBalances

/-!
# Proofs: an epoch raises no uncredited balance after its rewards

From Altair, the rewards and penalties of an epoch come after justification.

They also come after the update of the inactivity scores.

The steps that follow them run up to the update of the effective balances.

Those steps credit a balance in two ways.

A pending deposit adds to the balance of the validator with its key, from Electra.

A pending consolidation adds to the balance of its target, from Electra.

The registry updates, the slashings, the eth1 vote reset and the builder payments raise none.

So the balance of a validator that no pending deposit or consolidation credits does not rise.

The update of the effective balances reads the balance reached at that point.

The later steps keep the balances and the registry.

The same steps keep the inactivity score of each validator already in the registry.

Only a pending deposit writes a score, and it writes it at the end of the registry.

The trace bounds of an inactivity leak assume these facts; this module proves them per epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The balance at a position of the registry does not rise from one state to another.

A position with no balance in the second state counts as not raised. -/
def BalanceNotRaised (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ∀ later, after.balances.data[index]? = some later →
    ∃ earlier, state.balances.data[index]? = some earlier ∧ later ≤ earlier

/-- A state raises no balance over itself. -/
theorem BalanceNotRaised.refl (index : Nat) (state : BeaconState preset fork) :
    BalanceNotRaised index state state :=
  fun later found => ⟨later, found, Nat.le_refl _⟩

/-- Two steps that raise no balance at a position raise none there. -/
theorem BalanceNotRaised.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : BalanceNotRaised index first second) (two : BalanceNotRaised index second third) :
    BalanceNotRaised index first third := by
  intro later found
  obtain ⟨middle, atMiddle, low⟩ := two later found
  obtain ⟨earlier, atFirst, lower⟩ := one middle atMiddle
  exact ⟨earlier, atFirst, UInt64.le_trans low lower⟩

/-- A step that keeps the balances raises none. -/
theorem BalanceNotRaised.of_balances (same : after.balances = state.balances) (index : Nat) :
    BalanceNotRaised index state after := by
  rw [BalanceNotRaised, same]
  exact BalanceNotRaised.refl index state

/-- From Altair, the inactivity score at a position is the same in both states.

Before Altair there are no scores, so the property says nothing. -/
def ScoreKept (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ∀ altair : .altair ≤ fork,
    (after.inactivityScores altair).data[index]? = (state.inactivityScores altair).data[index]?

/-- A state keeps its own scores. -/
theorem ScoreKept.refl (index : Nat) (state : BeaconState preset fork) :
    ScoreKept index state state :=
  fun _ => rfl

/-- Two steps that keep the score at a position keep it. -/
theorem ScoreKept.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : ScoreKept index first second) (two : ScoreKept index second third) :
    ScoreKept index first third :=
  fun altair => (two altair).trans (one altair)

/-- A step that keeps the scores keeps the score at each position. -/
theorem ScoreKept.of_scores (same : after.inactivityScores = state.inactivityScores)
    (index : Nat) : ScoreKept index state after := by
  intro altair
  rw [same]

/-- Lowering a balance raises none. -/
theorem balanceNotRaised_decreaseBalance {position : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state position delta = .ok after) (index : Nat) :
    BalanceNotRaised index state after := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
  intro later found
  simp only [BeaconState.putBalance, Array.getElem?_set] at found
  split at found
  · rename_i same
    subst same
    refine ⟨_, Array.getElem?_eq_getElem inside, ?_⟩
    rw [← Option.some.inj found, Uint64.saturatingSub]
    split
    · exact UInt64.sub_le (UInt64.le_of_lt ‹_›)
    · exact UInt64.zero_le
  · exact ⟨later, found, UInt64.le_refl _⟩

/-- Raising one balance raises no balance at another position. -/
theorem balanceNotRaised_increaseBalance {position : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state position delta = .ok after) {index : Nat}
    (other : position.toNat ≠ index) : BalanceNotRaised index state after := by
  obtain ⟨inside, -, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  intro later found
  simp only [BeaconState.putBalance, Array.getElem?_set, other, ↓reduceIte] at found
  exact ⟨later, found, UInt64.le_refl _⟩

/-- A validator keeps its key, its effective balance and its withdrawal credentials.

It also stays slashed or unslashed. -/
def ValidatorSame (old new : Validator) : Prop :=
  new.pubkey = old.pubkey ∧ new.effectiveBalance = old.effectiveBalance ∧
    new.withdrawalCredentials = old.withdrawalCredentials ∧ new.slashed = old.slashed

/-- Each validator keeps its position, its key, its effective balance and its credentials.

It also stays slashed or unslashed. -/
def ValidatorsKept (state after : BeaconState preset fork) : Prop :=
  ∀ (i : Nat) old, state.validators.data[i]? = some old →
    ∃ new, after.validators.data[i]? = some new ∧ ValidatorSame old new

/-- Each state keeps its own validators. -/
theorem ValidatorsKept.refl (state : BeaconState preset fork) :
    ValidatorsKept state state :=
  fun _ old found => ⟨old, found, rfl, rfl, rfl, rfl⟩

/-- Two steps that keep the validators keep them. -/
theorem ValidatorsKept.trans {first second third : BeaconState preset fork}
    (one : ValidatorsKept first second) (two : ValidatorsKept second third) :
    ValidatorsKept first third := by
  intro i old found
  obtain ⟨middle, atMiddle, a, b, c, d⟩ := one i old found
  obtain ⟨new, atThird, e, f, g, h⟩ := two i middle atMiddle
  exact ⟨new, atThird, e.trans a, f.trans b, g.trans c, h.trans d⟩

/-- A step with the same registry keeps each validator. -/
theorem ValidatorsKept.of_eq (same : after.validators = state.validators) :
    ValidatorsKept state after := by
  intro i old found
  exact ⟨old, by rw [same]; exact found, rfl, rfl, rfl, rfl⟩

/-- If a step keeps each validator and adds none, each validator after it matches one before it. -/
theorem ValidatorsKept.exists_of_mem (kept : ValidatorsKept state after)
    (size : after.validators.data.size ≤ state.validators.data.size) {validator : Validator}
    (member : validator ∈ after.validators.data) :
    ∃ old ∈ state.validators.data, ValidatorSame old validator := by
  obtain ⟨i, inside, rfl⟩ := Array.getElem_of_mem member
  have insideOld : i < state.validators.data.size := Nat.lt_of_lt_of_le inside size
  obtain ⟨new, read, same⟩ := kept i _ (Array.getElem?_eq_getElem insideOld)
  rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at read
  exact ⟨_, Array.getElem_mem insideOld, read ▸ same⟩

/-- A step that keeps each validator, the balances, both pending queues and the scores. -/
private def Kept (state after : BeaconState preset fork) : Prop :=
  ValidatorsKept state after ∧ after.balances = state.balances ∧
    after.pendingDeposits = state.pendingDeposits ∧
    after.pendingConsolidations = state.pendingConsolidations ∧
    after.inactivityScores = state.inactivityScores

/-- Each state keeps its own validators, balances, queues and scores. -/
private theorem Kept.refl (state : BeaconState preset fork) : Kept state state :=
  ⟨ValidatorsKept.refl state, rfl, rfl, rfl, rfl⟩

/-- Two steps that keep the validators, balances, queues and scores keep them. -/
private theorem Kept.trans {first second third : BeaconState preset fork}
    (one : Kept first second) (two : Kept second third) : Kept first third :=
  ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.trans one.2.2.2.2⟩

/-- A fold whose every step keeps the validators, balances, queues and scores keeps them. -/
private theorem Kept.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (kept : ∀ s x s', step s x = .ok s' → Kept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (Kept.refl state) computed

/-- A write of a validator with the same key, effective balance and credentials keeps them. -/
private theorem kept_putValidator {position : Nat} {old validator : Validator}
    (inside : position < state.validators.data.size)
    (found : state.validators.data[position]? = some old) (same : ValidatorSame old validator) :
    Kept state (state.putValidator position inside validator) := by
  refine ⟨fun i earlier atI => ?_, rfl, rfl, rfl, rfl⟩
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set]
  by_cases here : position = i
  · subst here
    rw [found, Option.some.injEq] at atI
    subst atI
    exact ⟨validator, by simp, same⟩
  · simp only [here, ↓reduceIte]
    exact ⟨earlier, atI, rfl, rfl, rfl, rfl⟩

/-- A write at a plain position with the same key, effective balance and credentials keeps them. -/
private theorem kept_setValidatorAt {position : Nat} {old validator : Validator}
    (set : state.setValidatorAt position validator = .ok after)
    (found : getValidatorAt state position = .ok old) (same : ValidatorSame old validator) :
    Kept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  exact kept_putValidator inside (getValidatorAt_eq_ok_iff.mp found) same

/-- The start of an exit keeps each validator's key, effective balance and credentials.

It also keeps the balances and both pending queues. -/
private theorem kept_initiateValidatorExit {config : Config} {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Kept state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Kept.refl _
  obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  rw [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] at found
  exact (Kept.refl state).trans (kept_putValidator (old := validator) inside
    (by exact found) ⟨rfl, rfl, rfl, rfl⟩)

/-- Joining the activation queue keeps the key, the effective balance and the credentials. -/
private theorem same_queueForActivation {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    ValidatorSame validator queued := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The registry updates keep each validator's key, effective balance and credentials.

They also keep the balances and both pending queues, at every fork. -/
private theorem kept_processRegistryUpdates {config : Config}
    (computed : processRegistryUpdates config state = .ok after) : Kept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine Kept.foldlM (fun _ _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact kept_setValidatorAt set found ⟨rfl, rfl, rfl, rfl⟩
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact kept_initiateValidatorExit exited
    split at ok
    · exact kept_setValidatorAt (liftAccessor_ok.mp ok) found ⟨rfl, rfl, rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Kept.refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  refine (Kept.foldlM (fun _ _ _ ok => ?_) updatedOk).trans
    (Kept.foldlM (fun _ _ _ ok => ?_) activated)
  · simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, queuedOk, _, markedOk, ok⟩ := ok
    have set := kept_setValidatorAt markedOk found (same_queueForActivation queuedOk)
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact set.trans (kept_initiateValidatorExit exited)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ set
  · simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, set⟩ := ok
    rw [setValidator_eq_setValidatorAt] at set
    rw [getValidator_eq_getValidatorAt] at found
    exact kept_setValidatorAt set found ⟨rfl, rfl, rfl, rfl⟩

/-- The registry updates keep the balances, at every fork. -/
theorem processRegistryUpdates_balances
    (computed : processRegistryUpdates config state = .ok after) :
    after.balances = state.balances :=
  (kept_processRegistryUpdates computed).2.1

/-- The registry updates keep each validator's key, effective balance and credentials.

They keep each validator slashed or unslashed.

They keep the pending consolidations, at every fork. -/
theorem processRegistryUpdates_kept (computed : processRegistryUpdates config state = .ok after) :
    ValidatorsKept state after ∧ after.pendingConsolidations = state.pendingConsolidations :=
  ⟨(kept_processRegistryUpdates computed).1, (kept_processRegistryUpdates computed).2.2.2.1⟩

/-- A step that keeps each validator, both queues and the scores.

It raises no balance at a position. -/
private def Lowered (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ValidatorsKept state after ∧ BalanceNotRaised index state after ∧
    after.pendingDeposits = state.pendingDeposits ∧
    after.pendingConsolidations = state.pendingConsolidations ∧
    after.inactivityScores = state.inactivityScores

/-- Two steps that raise no balance at a position raise none there. -/
private theorem Lowered.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : Lowered index first second) (two : Lowered index second third) :
    Lowered index first third :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.trans one.2.2.2.2⟩

/-- A step that keeps the balances raises none. -/
private theorem Lowered.of_kept {index : Nat} (kept : Kept state after) :
    Lowered index state after :=
  ⟨kept.1, BalanceNotRaised.of_balances kept.2.1 index, kept.2.2.1, kept.2.2.2.1, kept.2.2.2.2⟩

/-- A fold whose every step raises no balance at a position raises none there. -/
private theorem Lowered.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (lowered : ∀ s x s', step s x = .ok s' → Lowered index s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Lowered index state after :=
  foldlM_ok_invariant (Lowered index state) (fun _ _ _ before ok => before.trans (lowered _ _ _ ok))
    (Lowered.of_kept (Kept.refl state)) computed

/-- Lowering a balance keeps each validator and both queues. -/
private theorem lowered_decreaseBalance {index : Nat} {position : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state position delta = .ok after) : Lowered index state after := by
  refine ⟨ValidatorsKept.of_eq (decreaseBalance_validators computed),
    balanceNotRaised_decreaseBalance computed index, ?_⟩
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
  exact ⟨rfl, rfl, rfl⟩

/-- A slashing penalty is a lowered balance, or nothing. -/
private theorem lowered_applySlashingPenalty {index : Nat} {total adjusted : Gwei} {position : Nat}
    (computed : applySlashingPenalty state total adjusted position = .ok after) :
    Lowered index state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, _, _, lowered⟩ := computed
      exact lowered_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Lowered.of_kept (Kept.refl _)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Lowered.of_kept (Kept.refl _)

/-- From Electra, a slashing penalty is a lowered balance, or nothing. -/
private theorem lowered_applySlashingPenaltyElectra {index : Nat} {perIncrement : Gwei}
    {position : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement position = .ok after) :
    Lowered index state after := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact lowered_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Lowered.of_kept (Kept.refl _)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Lowered.of_kept (Kept.refl _)

/-- The slashings keep each validator and both queues, and raise no balance. -/
private theorem lowered_processSlashings {index : Nat}
    (computed : processSlashings state = .ok after) : Lowered index state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact Lowered.foldlM (fun _ _ _ ok => lowered_applySlashingPenaltyElectra ok) applied
  · exact Lowered.foldlM (fun _ _ _ ok => lowered_applySlashingPenalty ok) computed

/-- The slashings raise no balance, at every fork. -/
theorem balanceNotRaised_processSlashings (computed : processSlashings state = .ok after)
    (index : Nat) : BalanceNotRaised index state after :=
  (lowered_processSlashings computed).2.1

/-- A step that keeps each validator and the consolidations, and raises no balance at a position.

It also keeps the score at that position. -/
private def Credited (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ValidatorsKept state after ∧ BalanceNotRaised index state after ∧
    after.pendingConsolidations = state.pendingConsolidations ∧ ScoreKept index state after

/-- Each state raises no balance over itself. -/
private theorem Credited.refl (index : Nat) (state : BeaconState preset fork) :
    Credited index state state :=
  ⟨ValidatorsKept.refl state, BalanceNotRaised.refl index state, rfl, ScoreKept.refl index state⟩

/-- Two steps that raise no balance at a position raise none there. -/
private theorem Credited.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : Credited index first second) (two : Credited index second third) :
    Credited index first third :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, two.2.2.1.trans one.2.2.1, one.2.2.2.trans two.2.2.2⟩

/-- From Altair, a new validator at the end keeps each validator and the consolidations.

It keeps the balance and the score at a position that holds a validator. -/
theorem addValidatorToRegistry_kept {index : Nat} {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} (altair : .altair ≤ fork)
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    (inside : index < state.validators.data.size) :
    ValidatorsKept state after ∧ after.balances.data[index]? = state.balances.data[index]? ∧
      after.pendingConsolidations = state.pendingConsolidations ∧ ScoreKept index state after := by
  have pushed := addValidatorToRegistry_validators_eq_push computed
  have kept : ValidatorsKept state after := by
    intro i old found
    refine ⟨old, ?_, rfl, rfl, rfl, rfl⟩
    have below := (Array.getElem?_eq_some_iff.mp found).1
    rw [pushed, Array.getElem?_push, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact found
  unfold addValidatorToRegistry at computed
  simp only [altair, ↓reduceDIte, addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, indexOk, _, _, _, balancesOk, _, _, _, _, _, scoresOk, rfl⟩ := computed
  have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
  refine ⟨kept, ?_, rfl, fun _ => ?_⟩
  · rw [setOrAppendList_getElem? balancesOk, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · show _ = _
    rw [setOrAppendList_getElem? scoresOk, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- From Altair, a new validator at the end keeps each validator and the balance at a position.

The position holds a validator. -/
private theorem credited_addValidatorToRegistry {index : Nat} {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} (altair : .altair ≤ fork)
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    (inside : index < state.validators.data.size) : Credited index state after := by
  obtain ⟨kept, balance, consolidations, score⟩ :=
    addValidatorToRegistry_kept altair computed inside
  exact ⟨kept, fun later found => ⟨later, by rw [← balance]; exact found, UInt64.le_refl _⟩,
    consolidations, score⟩

/-- From Altair, a deposit to another key keeps each validator.

It raises no balance at the position of the validator. -/
private theorem credited_applyPendingDeposit {config : Config} {checks : SignatureChecks}
    {index : Nat} {validator : Validator} {deposit : PendingDeposit} (altair : .altair ≤ fork)
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (found : state.validators.data[index]? = some validator)
    (other : deposit.pubkey ≠ validator.pubkey) : Credited index state after := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact Credited.refl index _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact credited_addValidatorToRegistry altair computed inside
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Credited.refl index _
  · rename_i position located
    simp only [liftAccessor_ok, bind_ok_iff, liftArith, mapError_ok_iff] at computed
    obtain ⟨target, converted, raised⟩ := computed
    obtain ⟨there, keyed⟩ := Array.findIdx?_eq_some_iff_getElem.mp located
    have apart : target.toNat ≠ index := by
      rw [(Uint64.ofNatChecked_ok_iff.mp converted).2]
      rintro rfl
      rw [Array.getElem?_eq_getElem there, Option.some.injEq] at found
      subst found
      exact other (beq_iff_eq.mp keyed.1).symm
    refine ⟨ValidatorsKept.of_eq (increaseBalance_validators raised),
      balanceNotRaised_increaseBalance raised apart, ?_⟩
    obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    exact ⟨rfl, ScoreKept.refl index _⟩

/-- From Altair, a pass over deposits to other keys keeps each validator.

It raises no balance at the position of the validator. -/
private theorem credited_passPendingDeposits {config : Config} {checks : SignatureChecks}
    {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} {index : Nat}
    (altair : .altair ≤ fork) :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass} {validator : Validator},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      state.validators.data[index]? = some validator →
      (∀ deposit ∈ deposits, deposit.pubkey ≠ validator.pubkey) →
      Credited index state pass.1.state
  | [], _, _, _, _, _, _, computed, _, _ => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Credited.refl index _
  | deposit :: rest, state, processed, count, postponed, pass, validator, computed, found,
      unnamed => by
    have first : deposit.pubkey ≠ validator.pubkey := unnamed deposit List.mem_cons_self
    have others : ∀ deposit ∈ rest, deposit.pubkey ≠ validator.pubkey :=
      fun d member => unnamed d (List.mem_cons_of_mem _ member)
    -- A credited deposit keeps the validator at the position, for the rest of the pass.
    have next {middle : BeaconState preset fork}
        (credited : applyPendingDeposit config checks state deposit = .ok middle) :
        ∃ now, Credited index state middle ∧ middle.validators.data[index]? = some now ∧
          ∀ deposit ∈ rest, deposit.pubkey ≠ now.pubkey := by
      have step := credited_applyPendingDeposit altair credited found first
      obtain ⟨now, atNow, same, -, -, -⟩ := step.1 index validator found
      exact ⟨now, step, atNow, by rw [same]; exact others⟩
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact Credited.refl index _
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      obtain ⟨_, step, kept, apart⟩ := next credited
      exact step.trans (credited_passPendingDeposits altair (deposits := rest) ‹_› kept apart)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact credited_passPendingDeposits altair (deposits := rest) ‹_› found others
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact Credited.refl index _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    obtain ⟨_, step, kept, apart⟩ := next credited
    exact step.trans (credited_passPendingDeposits altair (deposits := rest) ‹_› kept apart)

/-- From Electra, deposits to other keys keep each validator and the consolidations.

They raise no balance at the position of the validator. -/
private theorem credited_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unnamed : ∀ deposit ∈ (state.pendingDeposits electra).data,
      deposit.pubkey ≠ validator.pubkey) :
    Credited index state after := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact credited_passPendingDeposits altair ‹_› found
      (fun deposit member => unnamed deposit (by simpa using member))

/-- From Electra, the pending deposits raise no balance of a validator whose key none carries.

The deposits are those of the queue before the step. -/
theorem balanceNotRaised_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unnamed : ∀ deposit ∈ (state.pendingDeposits electra).data,
      deposit.pubkey ≠ validator.pubkey) :
    BalanceNotRaised index state after :=
  (credited_processPendingDeposits computed found unnamed).2.1

/-- A pass over consolidations that target other positions keeps the registry and the scores.

It raises no balance at the given position. -/
private theorem kept_passPendingConsolidations {nextEpoch : Epoch} {index : Nat} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      (∀ consolidation ∈ consolidations, consolidation.targetIndex.toNat ≠ index) →
      result.1.validators = state.validators ∧ BalanceNotRaised index state result.1 ∧
        result.1.inactivityScores = state.inactivityScores
  | [], _, _, computed, _ => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, BalanceNotRaised.refl index _, rfl⟩
  | consolidation :: rest, state, result, computed, untargeted => by
    have others : ∀ c ∈ rest, c.targetIndex.toNat ≠ index :=
      fun c member => untargeted c (List.mem_cons_of_mem _ member)
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact kept_passPendingConsolidations (result := (passed, read)) passedOk others
    split at computed
    · cases computed
      exact ⟨rfl, BalanceNotRaised.refl index _, rfl⟩
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    obtain ⟨same, rest, scores⟩ :=
      kept_passPendingConsolidations (result := (passed, read)) passedOk others
    refine ⟨same.trans ((increaseBalance_validators raisedOk).trans
      (decreaseBalance_validators loweredOk)), ?_, ?_⟩
    · exact (balanceNotRaised_decreaseBalance loweredOk index).trans
        ((balanceNotRaised_increaseBalance raisedOk
          (untargeted consolidation List.mem_cons_self)).trans rest)
    · obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raisedOk
      obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp loweredOk
      exact scores

/-- From Electra, consolidations that target other positions keep the registry and the scores.

They raise no balance at the given position. -/
private theorem kept_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) {index : Nat}
    (untargeted : ∀ consolidation ∈ (state.pendingConsolidations electra).data,
      consolidation.targetIndex.toNat ≠ index) :
    after.validators = state.validators ∧ BalanceNotRaised index state after ∧
      after.inactivityScores = state.inactivityScores := by
  simp only [processPendingConsolidations, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  split at computed
  · cases computed
  rename_i passed
  cases computed
  exact kept_passPendingConsolidations passed
    (fun c member => untargeted c (by simpa using member))

/-- From Electra, the pending consolidations raise no balance of a validator none targets.

The consolidations are those of the queue before the step. -/
theorem balanceNotRaised_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) {index : Nat}
    (untargeted : ∀ consolidation ∈ (state.pendingConsolidations electra).data,
      consolidation.targetIndex.toNat ≠ index) :
    BalanceNotRaised index state after :=
  (kept_processPendingConsolidations computed untargeted).2.1

/-- Two states with the same balances, the same registry and the same scores. -/
def SameBalancesRegistryScores (state after : BeaconState preset fork) : Prop :=
  after.balances = state.balances ∧ after.validators = state.validators ∧
    after.inactivityScores = state.inactivityScores

/-- From Altair, the steps after the effective balances keep the balances and the registry.

They also keep the scores. -/
theorem sameBalancesRegistryScores_tail (altair : .altair ≤ fork)
    (trace : EpochTrace (EpochStage.action config checks)
      [.slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow] state after) :
    SameBalancesRegistryScores state after := by
  refine trace.transport SameBalancesRegistryScores (fun _ => ⟨rfl, rfl, rfl⟩)
    (fun one two => ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.trans one.2.2⟩)
    fun k member a b ok => ?_
  have edge := EpochStage.action_cases.mp ok
  cases k <;> simp only [EpochStage.Edge] at edge <;> try (simp at member; done)
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    exact ⟨rfl, rfl, rfl⟩
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    exact ⟨rfl, rfl, rfl⟩
  case history =>
    split at edge
    · unfold processHistoricalSummariesUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl, rfl⟩
    · unfold processHistoricalRootsUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl, rfl⟩
  case participation =>
    simp only [altair, ↓reduceDIte] at edge
    subst edge
    exact ⟨rfl, rfl, rfl⟩
  case syncCommittees =>
    simp only [altair, ↓reduceDIte] at edge
    unfold processSyncCommitteeUpdates at edge
    simp only [bind, Except.bind, pure, Except.pure] at edge
    repeat' (split at edge <;> try cases edge)
    all_goals exact ⟨rfl, rfl, rfl⟩
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case ptcWindow =>
    split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩

/-- The update of the effective balances keeps the scores. -/
private theorem processEffectiveBalanceUpdates_scores
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    after.inactivityScores = state.inactivityScores := by
  unfold processEffectiveBalanceUpdates at computed
  refine foldlM_ok_invariant
    (fun current : BeaconState preset fork => current.inactivityScores = state.inactivityScores)
    (fun current _ next kept step => ?_) rfl computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨_, _, _, _, _, _, set⟩ := step
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact kept

/-- From Altair, an epoch raises no balance of an uncredited validator after its rewards.

This holds when the epoch succeeds.

Uncredited means that no pending deposit carries its key, and no pending consolidation targets it.

The queues are those of the state before the epoch; there are none before Electra.

Justification comes first, then the update of the inactivity scores, then the rewards.

Justification keeps the balances and the registry.

From the rewards up to the update of the effective balances, the balance does not rise.

At that point the validator keeps its effective balance and its withdrawal credentials.

That update then runs, and the later steps keep the balances and the registry.

Every step after the rewards keeps the inactivity score of the validator. -/
theorem balanceNotRaised_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unnamed : ∀ electra : .pectra ≤ fork, ∀ deposit ∈ (state.pendingDeposits electra).data,
      deposit.pubkey ≠ validator.pubkey)
    (untargeted : ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ (state.pendingConsolidations electra).data,
        consolidation.targetIndex.toNat ≠ index) :
    ∃ justified scored rewarded settled updated kept,
      processJustificationAndFinalization state = .ok justified ∧
      justified.balances = state.balances ∧ justified.validators = state.validators ∧
      processInactivityUpdates config justified altair = .ok scored ∧
      processRewardsAndPenalties config scored = .ok rewarded ∧
      BalanceNotRaised index rewarded settled ∧
      settled.validators.data[index]? = some kept ∧
      kept.effectiveBalance = validator.effectiveBalance ∧
      kept.withdrawalCredentials = validator.withdrawalCredentials ∧
      processEffectiveBalanceUpdates settled = .ok updated ∧
      after.balances = updated.balances ∧ after.validators = updated.validators ∧
      ScoreKept index rewarded after := by
  rw [processEpochAltair_eq_run] at computed
  have trace := EpochTrace.run_ok_iff.mp computed
  change EpochTrace _ (.justification :: .inactivity :: .rewards :: .registry :: .slashings ::
    .eth1Reset :: .pendingDeposits :: .pendingConsolidations :: .payments ::
    .effectiveBalances :: [.slashingsReset, .randaoReset, .history, .participation,
      .syncCommittees, .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain _ | ⟨justifiedOk, trace⟩ := trace
  obtain _ | ⟨scoredOk, trace⟩ := trace
  obtain _ | ⟨rewardedOk, trace⟩ := trace
  obtain _ | ⟨registeredOk, trace⟩ := trace
  obtain _ | ⟨slashedOk, trace⟩ := trace
  obtain _ | ⟨resetOk, trace⟩ := trace
  obtain _ | ⟨depositedOk, trace⟩ := trace
  obtain _ | ⟨consolidatedOk, trace⟩ := trace
  obtain _ | ⟨settledOk, trace⟩ := trace
  obtain _ | ⟨updatedOk, trace⟩ := trace
  rename_i justified scored rewarded registered slashed reset deposited consolidated settled
    updated
  have justifiedEq : processJustificationAndFinalization state = .ok justified :=
    EpochStage.action_cases.mp justifiedOk
  have scoredEq := EpochStage.action_cases.mp scoredOk
  simp only [EpochStage.Edge, altair, ↓reduceDIte] at scoredEq
  have rewardedEq : processRewardsAndPenalties config scored = .ok rewarded :=
    EpochStage.action_cases.mp rewardedOk
  have updatedEq : processEffectiveBalanceUpdates settled = .ok updated :=
    EpochStage.action_cases.mp updatedOk
  -- Justification keeps the balances, the registry and both queues.
  have justifiedSame : justified.balances = state.balances ∧
      justified.validators = state.validators ∧
      justified.pendingDeposits = state.pendingDeposits ∧
      justified.pendingConsolidations = state.pendingConsolidations := by
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedEq
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest]⟩
  -- The scores and the rewards keep the registry and both queues.
  have scoredFrame : scored = { justified with inactivityScores := scored.inactivityScores } := by
    unfold processInactivityUpdates at scoredEq
    split at scoredEq
    · simp only [pure, Except.pure, Except.ok.injEq] at scoredEq
      subst scoredEq
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at scoredEq
      obtain ⟨_, _, _, _, rfl⟩ := scoredEq
      rfl
  have rewardedFrame := processRewardsAndPenalties_frame rewardedEq
  have rewardedValidators : rewarded.validators = state.validators :=
    (congrArg BeaconState.validators rewardedFrame).trans
      ((congrArg BeaconState.validators scoredFrame).trans justifiedSame.2.1)
  have rewardedDeposits : rewarded.pendingDeposits = state.pendingDeposits :=
    (congrArg BeaconState.pendingDeposits rewardedFrame).trans
      ((congrArg BeaconState.pendingDeposits scoredFrame).trans justifiedSame.2.2.1)
  have rewardedConsolidations : rewarded.pendingConsolidations = state.pendingConsolidations :=
    (congrArg BeaconState.pendingConsolidations rewardedFrame).trans
      ((congrArg BeaconState.pendingConsolidations scoredFrame).trans justifiedSame.2.2.2)
  have foundRewarded : rewarded.validators.data[index]? = some validator := by
    rw [rewardedValidators]
    exact found
  -- The registry updates, the slashings and the reset of the votes raise no balance.
  have resetKept : Kept slashed reset := by
    have edge := EpochStage.action_cases.mp resetOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at edge
      obtain ⟨_, _, edge⟩ := edge
      split at edge <;>
        (simp only [pure, Except.pure, Except.ok.injEq] at edge
         subst edge
         exact ⟨ValidatorsKept.refl _, rfl, rfl, rfl, rfl⟩)
    · subst edge
      exact Kept.refl _
  have toReset : Lowered index rewarded reset :=
    (Lowered.of_kept (kept_processRegistryUpdates (EpochStage.action_cases.mp registeredOk))).trans
      ((lowered_processSlashings (EpochStage.action_cases.mp slashedOk)).trans
        (Lowered.of_kept resetKept))
  obtain ⟨atReset, atResetEq, sameReset⟩ := toReset.1 index validator foundRewarded
  -- The deposits carry other keys, and the consolidations name other targets.
  have depositedStep : Credited index reset deposited := by
    have edge := EpochStage.action_cases.mp depositedOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · rename_i electra
      refine credited_processPendingDeposits edge atResetEq ?_
      rw [toReset.2.2.1, rewardedDeposits, sameReset.1]
      exact unnamed electra
    · subst edge
      exact Credited.refl index _
  have consolidatedStep : consolidated.validators = deposited.validators ∧
      BalanceNotRaised index deposited consolidated ∧
      consolidated.inactivityScores = deposited.inactivityScores := by
    have edge := EpochStage.action_cases.mp consolidatedOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · rename_i electra
      refine kept_processPendingConsolidations edge ?_
      rw [depositedStep.2.2.1, toReset.2.2.2.1, rewardedConsolidations]
      exact untargeted electra
    · subst edge
      exact ⟨rfl, BalanceNotRaised.refl index _, rfl⟩
  -- The builder payments keep the balances, the registry and the scores.
  have settledSame : settled.validators = consolidated.validators ∧
      settled.balances = consolidated.balances ∧
      settled.inactivityScores = consolidated.inactivityScores := by
    have edge := EpochStage.action_cases.mp settledOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · have frame := processBuilderPendingPayments_eq edge
      exact ⟨by rw [frame], by rw [frame], by rw [frame]⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  have raised : BalanceNotRaised index rewarded settled :=
    toReset.2.1.trans (depositedStep.2.1.trans
      (consolidatedStep.2.1.trans (BalanceNotRaised.of_balances settledSame.2.1 index)))
  have keptAll : ValidatorsKept rewarded settled :=
    toReset.1.trans (depositedStep.1.trans
      (ValidatorsKept.of_eq (settledSame.1.trans consolidatedStep.1)))
  obtain ⟨kept, atKept, sameKept⟩ := keptAll index validator foundRewarded
  have tail := sameBalancesRegistryScores_tail altair trace
  -- Only the deposits write a score, and only at the end of the registry.
  have scoreKept : ScoreKept index rewarded after :=
    (ScoreKept.of_scores toReset.2.2.2.2 index).trans <| depositedStep.2.2.2.trans <|
      (ScoreKept.of_scores (settledSame.2.2.trans consolidatedStep.2.2) index).trans <|
      (ScoreKept.of_scores (processEffectiveBalanceUpdates_scores updatedEq) index).trans
        (ScoreKept.of_scores tail.2.2 index)
  exact ⟨justified, scored, rewarded, settled, updated, kept, justifiedEq, justifiedSame.1,
    justifiedSame.2.1, scoredEq, rewardedEq, raised, atKept, sameKept.2.1, sameKept.2.2.1,
    updatedEq, tail.1, tail.2.1, scoreKept⟩

end EthLib.Consensus
