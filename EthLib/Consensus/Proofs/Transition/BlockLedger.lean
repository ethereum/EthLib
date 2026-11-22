module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Operations
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.EpochReads
public import EthLib.Consensus.Proofs.Transition.Totality.FlagsActive
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock
public import EthLib.Consensus.Proofs.Transition.ParticipationFlagsKept
public import EthLib.Consensus.Proofs.Transition.SlashedPersistence
public import EthLib.Consensus.Proofs.Transition.BlockRewards
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance
public import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts
public import EthLib.Consensus.Proofs.Transition.Withdrawals
public import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
public import EthLib.Consensus.Proofs.Participation

/-!
# The balance ledger of a block

A ledger reads how the balances move from one state to another, validator by validator.

Each step of a block moves the balances within a ledger.

From Gloas the payload of the parent runs first.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

namespace BlockLedger

/-! ## The balance ledger of a block -/

/-- How the balances move from one state to another, read at each validator.

A balance rises by at most its participant sync amount and its other credits.

Off the paid and converted validators, a balance falls by at most the sum of two amounts.

These are its participant sync amount and its slashing penalty.

A converted validator falls only to the activation balance, and then rises by its credits.

Off the converted validators, whether the credentials compound stays.

A converted validator did not compound before, and compounds after. -/
structure Ledger {fork : Fork} (s t : BeaconState preset fork)
    (paid conv : Finset ValidatorIndex) (sync other slash : ValidatorIndex → ℕ) : Prop where
  up : ∀ v, actualBalanceAt ⟨fork, t⟩ v.toNat ≤
    actualBalanceAt ⟨fork, s⟩ v.toNat + sync v + other v
  down : ∀ v, v ∉ paid → v ∉ conv →
    actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat + sync v + slash v
  converted : ∀ v ∈ conv, actualBalanceAt ⟨fork, t⟩ v.toNat ≤
    preset.MIN_ACTIVATION_BALANCE.toNat + sync v + other v
  lowered : ∀ v ∈ conv, v ∉ paid → min (actualBalanceAt ⟨fork, s⟩ v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat + sync v + slash v
  kept : ∀ (v : ValidatorIndex) validator, v ∉ conv → s.validators.data[v.toNat]? = some validator →
    ∃ later, t.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator
  fresh : ∀ v ∈ conv, ∀ validator, s.validators.data[v.toNat]? = some validator →
    hasCompoundingWithdrawalCredential validator = false
  switched : ∀ v ∈ conv, ∃ later, t.validators.data[v.toNat]? = some later ∧
    hasCompoundingWithdrawalCredential later = true

theorem Ledger.trans {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv paid' conv' : Finset ValidatorIndex} {sync other slash sync' other' slash' :
      ValidatorIndex → ℕ}
    (one : Ledger s u paid conv sync other slash)
    (two : Ledger u t paid' conv' sync' other' slash') :
    Ledger s t (paid ∪ paid') (conv ∪ conv') (sync + sync') (other + other') (slash + slash') where
  up v := by have := one.up v; have := two.up v; simp only [Pi.add_apply]; omega
  down v notPaid notConv := by
    simp only [Finset.mem_union, not_or] at notPaid notConv
    have := one.down v notPaid.1 notConv.1
    have := two.down v notPaid.2 notConv.2
    simp only [Pi.add_apply]; omega
  converted v member := by
    simp only [Pi.add_apply]
    rcases Finset.mem_union.mp member with first | second
    · have := one.converted v first; have := two.up v; omega
    · have := two.converted v second; omega
  lowered v member notPaid := by
    simp only [Pi.add_apply]
    simp only [Finset.mem_union, not_or] at notPaid
    -- No validator is converted twice: the first conversion makes it compound.
    have apart : v ∈ conv → v ∉ conv' := by
      intro first second
      obtain ⟨later, found, compounds⟩ := one.switched v first
      rw [two.fresh v second later found] at compounds
      cases compounds
    rcases Finset.mem_union.mp member with first | second
    · have := one.lowered v first notPaid.1
      have := two.down v notPaid.2 (apart first)
      omega
    · have first : v ∉ conv := fun first => apart first second
      have := one.down v notPaid.1 first
      have := two.lowered v second notPaid.2
      omega
  kept v validator notConv found := by
    simp only [Finset.mem_union, not_or] at notConv
    obtain ⟨middle, middleFound, same⟩ := one.kept v validator notConv.1 found
    obtain ⟨later, laterFound, same'⟩ := two.kept v middle notConv.2 middleFound
    exact ⟨later, laterFound, same'.trans same⟩
  fresh v member validator found := by
    rcases Finset.mem_union.mp member with first | second
    · exact one.fresh v first validator found
    · by_cases converted : v ∈ conv
      · exact one.fresh v converted validator found
      · obtain ⟨middle, middleFound, same⟩ := one.kept v validator converted found
        rw [← same]
        exact two.fresh v second middle middleFound
  switched v member := by
    rcases Finset.mem_union.mp member with first | second
    · obtain ⟨middle, middleFound, compounds⟩ := one.switched v first
      by_cases again : v ∈ conv'
      · exact two.switched v again
      · obtain ⟨later, laterFound, same⟩ := two.kept v middle again middleFound
        exact ⟨later, laterFound, same.trans compounds⟩
    · exact two.switched v second

/-- A step that keeps every balance and whether each existing validator compounds. -/
private theorem Ledger.of_kept {fork : Fork} {s t : BeaconState preset fork}
    (balances : t.balances.data = s.balances.data)
    (kept : ∀ (v : ValidatorIndex) validator, s.validators.data[v.toNat]? = some validator →
      ∃ later, t.validators.data[v.toNat]? = some later ∧
        hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator) :
    Ledger s t ∅ ∅ 0 0 0 where
  up v := by simp [actualBalanceAt, balances]
  down v _ _ := by simp [actualBalanceAt, balances]
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := kept v validator found
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- A step that keeps every balance and every validator. -/
private theorem Ledger.of_eq {fork : Fork} {s t : BeaconState preset fork}
    (balances : t.balances.data = s.balances.data)
    (validators : t.validators.data = s.validators.data) : Ledger s t ∅ ∅ 0 0 0 :=
  Ledger.of_kept balances fun v validator found =>
    ⟨validator, by rw [validators]; exact found, rfl⟩

theorem Ledger.refl {fork : Fork} (s : BeaconState preset fork) : Ledger s s ∅ ∅ 0 0 0 :=
  Ledger.of_eq rfl rfl

/-- A ledger with larger sets and amounts. -/
private theorem Ledger.mono {fork : Fork} {s t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash other' slash' : ValidatorIndex → ℕ}
    (ledger : Ledger s t paid conv sync other slash) (paid' : Finset ValidatorIndex)
    (morePaid : paid ⊆ paid') (moreOther : ∀ v, other v ≤ other' v)
    (moreSlash : ∀ v, slash v ≤ slash' v) : Ledger s t paid' conv sync other' slash' where
  up v := by have := ledger.up v; have := moreOther v; omega
  down v notPaid notConv := by
    have := ledger.down v (fun member => notPaid (morePaid member)) notConv
    have := moreSlash v; omega
  converted v member := by have := ledger.converted v member; have := moreOther v; omega
  lowered v member notPaid := by
    have := ledger.lowered v member (fun inside => notPaid (morePaid inside))
    have := moreSlash v; omega
  kept := ledger.kept
  fresh := ledger.fresh
  switched := ledger.switched

theorem Ledger.zero_left {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (one : Ledger s u ∅ ∅ 0 0 0) (two : Ledger u t paid conv sync other slash) :
    Ledger s t paid conv sync other slash := by
  simpa using one.trans two

theorem Ledger.zero_right {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (one : Ledger s u paid conv sync other slash) (two : Ledger u t ∅ ∅ 0 0 0) :
    Ledger s t paid conv sync other slash := by
  simpa using one.trans two

/-- Two states agree on the total when they agree on activity and the effective balances. -/
theorem activeBalanceTotal_eq {fork : Fork} {a s : BeaconState preset fork}
    (epoch : getCurrentEpoch s = getCurrentEpoch a)
    (active : ActiveKept (activityFixedEpoch a) a s) (kept : EffectiveKept a s)
    (size : a.validators.data.size ≤ s.validators.data.size) :
    activeBalanceTotal s = activeBalanceTotal a := by
  unfold activeBalanceTotal
  rw [epoch, activeSum_eq (fun i => active _ (getCurrentEpoch_le_activityFixedEpoch a) i) kept size]

/-- A successful read of the participant reward of the sync committee at a state. -/
def SyncRewardRead {fork : Fork} (a : BeaconState preset fork) : Prop :=
  ∃ reward : Gwei, syncParticipantReward a = .ok reward

/-- A successful read of the participant reward is its natural value, and a read. -/
theorem syncRewardRead_of_ok {fork : Fork} {a : BeaconState preset fork} {reward : Gwei}
    (computed : syncParticipantReward a = .ok reward) :
    reward.toNat = syncRewardAt a ∧ SyncRewardRead a :=
  ⟨syncParticipantReward_toNat computed, reward, computed⟩

/-- The participant reward reads only the total active balance. -/
theorem syncParticipantReward_congr {fork : Fork} {a s : BeaconState preset fork}
    (same : getTotalActiveBalance s = getTotalActiveBalance a) :
    syncParticipantReward s = syncParticipantReward a := by
  unfold syncParticipantReward
  rw [same]

/-- A successful participant reward has a successful proposer share.

The reward is at most the weighted base reward over the weight denominator.

So the product of the share fits in 64 bits. -/
theorem syncProposerReward_of_participant {fork : Fork} {a : BeaconState preset fork}
    {reward : Gwei} (computed : syncParticipantReward a = .ok reward) :
    ∃ share : Gwei, syncProposerReward reward = .ok share ∧
      share.toNat = reward.toNat * PROPOSER_WEIGHT.toNat /
        (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) := by
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  obtain ⟨_, _, _, _, weighted, weightedOk, perEpoch, perEpochOk, perSlot, perSlotOk, rewardOk⟩ :=
    computed
  rw [divChecked_ok_iff] at perEpochOk perSlotOk rewardOk
  have below := weighted.toNat_lt
  have proposer : PROPOSER_WEIGHT.toNat = 8 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := rfl
  have first := Nat.div_le_self perSlot.toNat preset.SYNC_COMMITTEE_SIZE.toNat
  have second := Nat.div_le_self perEpoch.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [← rewardOk.2] at first
  rw [← perSlotOk.2] at second
  rw [perEpochOk.2, denominator] at second
  have fits : reward.toNat * PROPOSER_WEIGHT.toNat < 2 ^ 64 := by
    rw [proposer]
    omega
  have scaled := mulChecked_of_lt fits
  refine ⟨reward * PROPOSER_WEIGHT / (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT), ?_, ?_⟩
  · simp only [syncProposerReward, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff]
    exact ⟨_, scaled, divChecked_ok_iff.mpr ⟨by decide, UInt64.toNat_div _ _⟩⟩
  · rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt fits]
    rfl

/-! ### Validators later in an epoch -/

section Lives

variable {fork : Fork} {s u t : BeaconState preset fork}

/-- One validator later inside an epoch keeps its activation epoch.

Once its exit is set, its withdrawable epoch only rises, and moves only when it is slashed.

Its slashed flag and its exit epoch are read from the frame and the registry lifecycle. -/
structure Later (old w : Validator) : Prop where
  activation : w.activationEpoch = old.activationEpoch
  withdrawable : old.exitEpoch ≠ FAR_FUTURE_EPOCH →
    old.withdrawableEpoch ≤ w.withdrawableEpoch ∧
      (w.slashed = true ∨ w.withdrawableEpoch = old.withdrawableEpoch)

/-- Every validator is later than itself. -/
private theorem Later.refl (v : Validator) : Later v v :=
  ⟨rfl, fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩

/-- The withdrawable epoch of one validator over two steps.

The first step keeps the exit, and the second keeps the slash. -/
private theorem withdrawable_trans {a b c : Validator}
    (one : a.exitEpoch ≠ FAR_FUTURE_EPOCH → a.withdrawableEpoch ≤ b.withdrawableEpoch ∧
      (b.slashed = true ∨ b.withdrawableEpoch = a.withdrawableEpoch))
    (two : b.exitEpoch ≠ FAR_FUTURE_EPOCH → b.withdrawableEpoch ≤ c.withdrawableEpoch ∧
      (c.slashed = true ∨ c.withdrawableEpoch = b.withdrawableEpoch))
    (exit : a.exitEpoch ≠ FAR_FUTURE_EPOCH → b.exitEpoch = a.exitEpoch)
    (slashed : b.slashed = true → c.slashed = true) (far : a.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    a.withdrawableEpoch ≤ c.withdrawableEpoch ∧
      (c.slashed = true ∨ c.withdrawableEpoch = a.withdrawableEpoch) := by
  obtain ⟨le, moved⟩ := one far
  obtain ⟨le', moved'⟩ := two (by rw [exit far]; exact far)
  refine ⟨UInt64.le_trans le le', ?_⟩
  rcases moved' with flag | same'
  · exact .inl flag
  · rcases moved with flag | same
    · exact .inl (slashed flag)
    · exact .inr (same'.trans same)

/-- Two later steps make one, given the exit kept by the first and the slash kept by the second. -/
private theorem Later.trans {a b c : Validator} (one : Later a b) (two : Later b c)
    (exit : a.exitEpoch ≠ FAR_FUTURE_EPOCH → b.exitEpoch = a.exitEpoch)
    (slashed : b.slashed = true → c.slashed = true) : Later a c where
  activation := two.activation.trans one.activation
  withdrawable := withdrawable_trans one.withdrawable two.withdrawable exit slashed

/-- A later registry inside an epoch keeps each old validator later.

Its new validators are not activated. -/
structure Lives (s t : BeaconState preset fork) : Prop where
  later : ∀ (index : ℕ) old w, s.validators.data[index]? = some old →
    t.validators.data[index]? = some w → Later old w
  fresh : ∀ (index : ℕ) w, s.validators.data[index]? = none →
    t.validators.data[index]? = some w → w.activationEpoch = FAR_FUTURE_EPOCH

/-- The withdrawable epochs of a later registry. -/
theorem Lives.withdrawableKept (lives : Lives s t) : WithdrawableKept s t :=
  fun i v w found read far => (lives.later i v w found read).withdrawable far

/-- Every state lives on in itself. -/
theorem Lives.refl (s : BeaconState preset fork) : Lives s s :=
  ⟨fun _ old w found read => by rw [found, Option.some.injEq] at read; exact read ▸ .refl old,
    fun _ _ none found => by rw [none] at found; cases found⟩

/-- Two later registries make one.

The exits of the first come from the registry lifecycle.

The slashes of the second come from its frame. -/
theorem Lives.trans (one : Lives s u) (two : Lives u t) (life : RegistryLifecycle s u)
    (slashed : SlashedPersistence u t) : Lives s t where
  later index old w found read := by
    obtain ⟨middle, middleFound, kept⟩ := life.validators index old found
    exact (one.later index old middle found middleFound).trans
      (two.later index middle w middleFound read) kept.exitEpoch fun flag => by
        obtain ⟨w', read', marked⟩ := slashed index middle middleFound flag
        rw [read, Option.some.injEq] at read'
        exact read' ▸ marked
  fresh index w none found := by
    cases middle : u.validators.data[index]? with
    | none => exact two.fresh index w middle found
    | some m =>
      rw [(two.later index m w middle found).activation]
      exact one.fresh index m none middle

/-- A registry that keeps every old position lives on, when its new validators are not active. -/
private theorem Lives.of_prefix
    (same : ∀ (index : ℕ) old, s.validators.data[index]? = some old →
      t.validators.data[index]? = some old)
    (fresh : ∀ (index : ℕ) w, s.validators.data[index]? = none →
      t.validators.data[index]? = some w → w.activationEpoch = FAR_FUTURE_EPOCH) : Lives s t :=
  ⟨fun index old w found read => by
    rw [same index old found, Option.some.injEq] at read; exact read ▸ .refl old, fresh⟩

/-- A state with the same validators lives on. -/
theorem Lives.of_data (same : t.validators.data = s.validators.data) : Lives s t :=
  Lives.of_prefix (fun _ _ found => by rw [same]; exact found)
    (fun _ _ none found => by rw [same, none] at found; cases found)

/-- A step before a state with the same validators. -/
theorem Lives.of_data_left (same : u.validators.data = s.validators.data)
    (two : Lives u t) : Lives s t :=
  ⟨fun index old w found => two.later index old w (by rw [same]; exact found),
    fun index w none => two.fresh index w (by rw [same]; exact none)⟩

/-- A step after a state with the same validators. -/
theorem Lives.of_data_right (one : Lives s u)
    (same : t.validators.data = u.validators.data) : Lives s t :=
  ⟨fun index old w found read => one.later index old w found (by rw [← same]; exact read),
    fun index w none read => one.fresh index w none (by rw [← same]; exact read)⟩

/-- A fold whose steps live on, keep the lifecycle and keep each slash, does all three. -/
private theorem Lives.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b →
      Lives a b ∧ RegistryLifecycle a b ∧ SlashedPersistence a b) {items : List α}
    (computed : items.foldlM step s = .ok t) : Lives s t :=
  (foldlM_ok_invariant (fun b => Lives s b ∧ RegistryLifecycle s b)
    (fun _ _ _ before ok => by
      obtain ⟨lives, life, slashed⟩ := each _ _ _ ok
      exact ⟨before.1.trans lives before.2 slashed, before.2.trans life⟩)
    ⟨Lives.refl s, .refl s⟩ computed).1

/-- Replacing a validator, read by its index, by one later than it. -/
theorem Lives.setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator s index = .ok old) (set : s.setValidator index validator = .ok t)
    (step : Later old validator) : Lives s t := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : s.validators.data[index.toNat]? = some old := getValidator_eq_ok_iff.mp found
  refine ⟨fun other v w found' read' => ?_, fun other w none read' => ?_⟩
  · simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at read'
    split at read'
    · rename_i same
      subst same
      rw [read, Option.some.injEq] at found'
      cases Option.some.inj read'
      exact found' ▸ step
    · rw [found', Option.some.injEq] at read'
      exact read' ▸ .refl v
  · simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at read'
    split at read'
    · rename_i same
      subst same
      rw [read] at none
      cases none
    · rw [none] at read'
      cases read'

private theorem lives_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config s index = .ok t) : Lives s t := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Lives.refl _
  · have same := (exitQueue_validators queue).1
    exact Lives.of_data_left (by rw [same]) <|
      Lives.setValidator ((getValidator_of_validators_eq same index).trans found) set
        ⟨rfl, fun set => absurd far set⟩

private theorem lives_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config s slashedIndex whistleblowerIndex = .ok t) : Lives s t := by
  obtain ⟨exited, validator, withdrawal, marked, _, _, _, _, _, _, _, last, exitedOk,
    found, _, markedOk, _, _, _, lowered, _, _, raised, final, done⟩ := slashValidator_ok computed
  have same := (slashValidator_last (last := last) (after := t) (index := slashedIndex)
    (by subst done; rfl)).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  have later : validator.withdrawableEpoch ≤ max validator.withdrawableEpoch withdrawal := by
    rw [UInt64.max_def]
    split
    · assumption
    · exact UInt64.le_refl _
  -- The write marks the validator, so every slash stays.
  have slashed : SlashedPersistence exited marked := by
    obtain ⟨inside, rfl⟩ := setValidator_ok markedOk
    intro j x read flag
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set]
    split
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨x, read, flag⟩
  exact ((lives_initiateValidatorExit exitedOk).trans
    (Lives.setValidator found markedOk ⟨rfl, fun _ => ⟨later, .inl rfl⟩⟩)
    (registryLifecycle_initiateValidatorExit exitedOk) slashed).of_data_right
      (congrArg (·.data) same)

theorem lives_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) : Lives s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact lives_slashValidator slashed

private theorem lives_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    Lives step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact lives_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Lives.refl _

theorem lives_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) : Lives s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact (foldlM_ok_invariant (fun step => Lives s step.1 ∧ RegistryLifecycle s step.1)
    (fun _ _ _ before ok => ⟨before.1.trans (lives_slashIfSlashable ok) before.2
        (.of_frame (frame_slashIfSlashable ok).toFrame),
      before.2.trans (registryLifecycle_slashIfSlashable ok)⟩)
    (show Lives s (s, false).1 ∧ RegistryLifecycle s (s, false).1 from
      ⟨Lives.refl s, .refl s⟩) folded).1

/-- From Electra a deposit keeps every old validator.

The new one keeps both of its epochs unassigned. -/
theorem lives_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (computed : processDeposit config checks before s deposit = .ok t) : Lives s t := by
  refine Lives.of_prefix ?_ fun index w none read =>
    (UnassignedKept.processDeposit computed s.validators.data.size (unassignedFrom_size s) index w
      (Nat.le_of_not_lt fun inside => by
        rw [Array.getElem?_eq_getElem inside] at none; cases none) read).1
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  intro index old found
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨early, _⟩
  · exact found
  · exact found
  · have inside := (Array.getElem?_eq_some_iff.mp found).1
    simpa [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push,
      Nat.ne_of_lt inside] using found
  · exact absurd electra (Nat.not_le_of_lt early)

theorem lives_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Lives s t := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact lives_initiateValidatorExit exited

private theorem lives_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config s electra request = .ok t) : Lives s t := by
  rcases withdrawalRequest_cases computed with rfl | ⟨_, _, _, exited⟩ | ⟨_, _, _, _, requested⟩
  · exact Lives.refl _
  · exact lives_initiateValidatorExit exited
  · exact Lives.of_data (congrArg (·.data) (requestPartialWithdrawal_kept requested).1)

private theorem lives_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator s electra index = .ok t) : Lives s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (Lives.setValidator found set ⟨rfl, fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩).of_data_right
    (congrArg (·.data) (queueExcessActiveBalance_validators queued))

private theorem lives_queueConsolidation {electra : .pectra ≤ fork} {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Lives s t := by
  obtain ⟨_, _, _, _, _, _, _, set, _, rfl⟩ := queueConsolidation_steps computed
  have step := Lives.setValidator (old := source) (by simp [getValidator, found]) set
    ⟨rfl, fun set => absurd far set⟩
  exact (Lives.of_data_left (s := s) (by rfl) step).of_data_right rfl

private theorem lives_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config s electra request = .ok t) : Lives s t := by
  rcases consolidationRequest_cases computed with rfl | ⟨_, _, -, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact Lives.refl _
  · exact lives_switchToCompoundingValidator switched
  · exact lives_queueConsolidation accepted.sourceAt accepted.sourceStays queued

/-- Deposit, withdrawal and consolidation requests, in turn, keep each old validator later.

They activate no new validator. -/
private theorem lives_requests {electra : .pectra ≤ fork} {deposits : List DepositRequest}
    {withdrawals : List WithdrawalRequest} {consolidations : List ConsolidationRequest}
    {deposited withdrawn : BeaconState preset fork}
    (depositsOk : deposits.foldlM (processDepositRequest · electra ·) s = .ok deposited)
    (withdrawalsOk :
      withdrawals.foldlM (processWithdrawalRequest config · electra ·) deposited = .ok withdrawn)
    (consolidationsOk : consolidations.foldlM (processConsolidationRequest config · electra ·)
      withdrawn = .ok t) : Lives s t := by
  -- The deposit requests only queue, so they keep the registry.
  have deposits := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators = s.validators)
    (fun _ _ _ before ok => (processDepositRequest_ok ok).2.1.trans before) rfl depositsOk
  have withdrawals := Lives.foldlM (fun _ _ _ ok => ⟨lives_processWithdrawalRequest ok,
    registryLifecycle_processWithdrawalRequest ok,
    .of_frame (frame_processWithdrawalRequest ok).toFrame⟩)
    withdrawalsOk
  have consolidations := Lives.foldlM (fun _ _ _ ok => ⟨lives_processConsolidationRequest ok,
    registryLifecycle_processConsolidationRequest ok,
    .of_frame (frame_processConsolidationRequest ok).toFrame⟩) consolidationsOk
  exact Lives.of_data_left (congrArg (·.data) deposits) <| withdrawals.trans consolidations
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok)
      withdrawalsOk)
    (.of_frame (Frame.foldlM (fun _ _ _ ok => (frame_processConsolidationRequest ok).toFrame)
      consolidationsOk))

theorem lives_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) : Lives s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact lives_requests depositsOk withdrawalsOk consolidationsOk

/-- From Gloas, after the payload of the parent, an old validator read at both ends is later.

A new validator is not activated. -/
theorem lives_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks s gloas body = .ok t) :
    Lives s t := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, consolidated, _, _, _, settledOk, depositsOk, withdrawalsOk,
      consolidationsOk, buildersOk, exitsOk, -, rfl⟩
  · exact Lives.refl _
  -- Settling the payment and the requests of builders keep the registry of validators.
  have builders := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators = consolidated.validators)
    (fun _ _ _ before ok => by
      obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
      exact before) rfl buildersOk
  have exits := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators = consolidated.validators)
    (fun _ _ _ before ok => by
      obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
      exact before) builders exitsOk
  exact Lives.of_data_left (u := settled) (by rw [settleParentPayment_eq settledOk])
    ((lives_requests depositsOk withdrawalsOk consolidationsOk).of_data_right
      (congrArg (·.data) exits))

/-- An unslashed validator, active by an epoch, whose exit is unset or not yet withdrawable. -/
def Eligible (E : Epoch) (w : Validator) : Prop :=
  w.slashed = false ∧ w.activationEpoch ≤ E ∧ E < FAR_FUTURE_EPOCH ∧
    (w.exitEpoch = FAR_FUTURE_EPOCH ∨ E < w.withdrawableEpoch)

/-- A slashable validator is eligible. -/
private theorem eligible_of_slashable {E : Epoch} {w : Validator}
    (slashable : isSlashableValidator w E = true) : Eligible E w := by
  simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    at slashable
  obtain ⟨⟨unslashed, active⟩, before⟩ := slashable
  refine ⟨unslashed, active, ?_, Or.inr before⟩
  have bound := w.withdrawableEpoch.toNat_lt
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  rw [UInt64.lt_iff_toNat_lt] at before ⊢
  omega

/-- An eligible validator of a later registry was eligible before.

Its slashed flag comes from the frame and its exit epoch from the registry lifecycle. -/
theorem Lives.back (lives : Lives s t) (life : RegistryLifecycle s t)
    (slashed : SlashedPersistence s t) {E : Epoch} {i : ℕ} {w : Validator}
    (found : t.validators.data[i]? = some w) (eligible : Eligible E w) :
    ∃ old, s.validators.data[i]? = some old ∧ Eligible E old := by
  obtain ⟨unslashed, active, below, window⟩ := eligible
  cases read : s.validators.data[i]? with
  | none =>
    have pending := lives.fresh i w read found
    rw [pending] at active
    exact absurd (UInt64.lt_of_le_of_lt active below) (UInt64.lt_irrefl _)
  | some old =>
    have step := lives.later i old w read found
    obtain ⟨later, laterFound, kept⟩ := life.validators i old read
    rw [found] at laterFound
    cases laterFound
    refine ⟨old, rfl, ?_, step.activation ▸ active, below, ?_⟩
    · cases flag : old.slashed
      · rfl
      · obtain ⟨w', read', marked⟩ := slashed i old read flag
        rw [found, Option.some.injEq] at read'
        rw [read', marked] at unslashed; cases unslashed
    · by_cases far : old.exitEpoch = FAR_FUTURE_EPOCH
      · exact Or.inl far
      · right
        rcases window with exitFar | early
        · exact absurd ((kept.exitEpoch far).symm.trans exitFar) far
        · obtain ⟨-, moved⟩ := step.withdrawable far
          rcases moved with flag | same
          · rw [flag] at unslashed; cases unslashed
          · rw [← same]; exact early

end Lives

/-! ### The steps of a block, one by one -/

section Steps

variable {fork : Fork} {s t : BeaconState preset fork}

theorem ledger_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact Ledger.of_eq rfl rfl

theorem ledger_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact Ledger.of_eq rfl rfl

theorem ledger_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact Ledger.of_eq (by rw [← rest]) (by rw [← rest])

/-- Applying the expected withdrawals keeps the registry of validators. -/
private theorem applyExpectedWithdrawals_validators {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals s capella expected = .ok t) :
    t.validators = s.validators := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : applied.validators = s.validators := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM_ok_invariant (fun x : BeaconState preset fork => x.validators = s.validators)
      (fun _ _ _ same ok => by rw [applyWithdrawal_eq ok]; exact same) rfl appliedOk
  have two : indexed.validators = applied.validators := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      rfl
    · cases indexedOk
      rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → finished.validators = kept.validators := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        rfl
    · cases ok
      rfl
  have three := swept _ sweptOk
  have queued : (if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) electra expected.processedPartialWithdrawalsCount
    else if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed).validators = indexed.validators := by
    split <;> split <;> rfl
  have four : t.validators = finished.validators := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      rfl
  rw [four, three, queued, two, one]

/-- Withdrawals keep the validators and lower balances only.

A balance that no withdrawal names stays.

From Gloas a withdrawal of a builder lowers no balance of a validator. -/
private theorem applyWithdrawals_moves : ∀ (withdrawals : List Withdrawal)
    (a b : BeaconState preset fork), withdrawals.foldlM applyWithdrawal a = .ok b →
    b.validators = a.validators ∧ ∀ v : ValidatorIndex,
      actualBalanceAt ⟨fork, b⟩ v.toNat ≤ actualBalanceAt ⟨fork, a⟩ v.toNat ∧
      ((∀ w ∈ withdrawals, w.validatorIndex ≠ v) →
        actualBalanceAt ⟨fork, b⟩ v.toNat = actualBalanceAt ⟨fork, a⟩ v.toNat)
  | [], a, b, ok => by
    cases ok
    exact ⟨rfl, fun _ => ⟨Nat.le_refl _, fun _ => rfl⟩⟩
  | w :: rest, a, b, ok => by
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨m, step, restOk⟩ := ok
    obtain ⟨same, moves⟩ := applyWithdrawals_moves rest m b restOk
    have first : m.validators = a.validators ∧ ∀ v : ValidatorIndex,
        actualBalanceAt ⟨fork, m⟩ v.toNat ≤ actualBalanceAt ⟨fork, a⟩ v.toNat ∧
        (w.validatorIndex ≠ v →
          actualBalanceAt ⟨fork, m⟩ v.toNat = actualBalanceAt ⟨fork, a⟩ v.toNat) := by
      unfold applyWithdrawal at step
      split at step
      · simp only [bind_ok_iff] at step
        obtain ⟨_, _, set⟩ := step
        obtain ⟨_, rfl⟩ := setBuilder_ok set
        exact ⟨rfl, fun _ => ⟨Nat.le_refl _, fun _ => rfl⟩⟩
      · have lowered := actualBalanceAt_decreaseBalance step
        obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp step
        refine ⟨rfl, fun v => ⟨?_, fun other => ?_⟩⟩
        · rw [lowered]
          exact Nat.sub_le _ _
        · rw [lowered]
          split_ifs with equal
          · exact absurd (UInt64.toNat_inj.mp equal) other
          · exact Nat.sub_zero _
    refine ⟨same.trans first.1, fun v => ⟨((moves v).1).trans (first.2 v).1, fun none => ?_⟩⟩
    exact ((moves v).2 fun x member => none x (List.mem_cons_of_mem w member)).trans
      ((first.2 v).2 (none w List.mem_cons_self))

/-- The expected withdrawals pay only the indices they name. -/
private theorem ledger_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals s capella expected = .ok t) :
    Ledger s t (expected.withdrawals.toList.map (·.validatorIndex)).toFinset ∅ 0 0 0 := by
  have validators := applyExpectedWithdrawals_validators computed
  obtain ⟨applied, appliedOk, balances, -⟩ := applyExpectedWithdrawals_balances computed
  unfold applyWithdrawals at appliedOk
  rw [← Array.foldlM_toList] at appliedOk
  obtain ⟨-, moves⟩ := applyWithdrawals_moves _ _ _ appliedOk
  have point (v : ValidatorIndex) :
      actualBalanceAt ⟨fork, t⟩ v.toNat = actualBalanceAt ⟨fork, applied⟩ v.toNat := by
    simp only [actualBalanceAt, balances]
  exact {
    up := fun v => by
      simp only [point v, Pi.zero_apply, Nat.add_zero]
      exact (moves v).1
    down := fun v notPaid _ => by
      rw [point v, (moves v).2 fun w member same =>
        notPaid (List.mem_toFinset.mpr (List.mem_map.mpr ⟨w, member, same⟩))]
      simp
    converted := fun v member => absurd member (Finset.notMem_empty v)
    lowered := fun v member => absurd member (Finset.notMem_empty v)
    kept := fun v validator _ found => ⟨validator, by rw [validators]; exact found, rfl⟩
    fresh := fun v member => absurd member (Finset.notMem_empty v)
    switched := fun v member => absurd member (Finset.notMem_empty v) }

/-- The withdrawal step pays at most as many indices as a payload has withdrawals.

From Gloas a block whose parent has no payload pays none. -/
private theorem ledger_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals s capella payload = .ok t) :
    ∃ paid : Finset ValidatorIndex, Ledger s t paid ∅ 0 0 0 ∧
      paid.card ≤ preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat := by
  have counted {expected : ExpectedWithdrawals}
      (found : getExpectedWithdrawals s capella = .ok expected) :
      (expected.withdrawals.toList.map (·.validatorIndex)).toFinset.card ≤
        preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat := by
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, Array.length_toList]
    exact getExpectedWithdrawals_size found
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨expected, found, applied⟩ := computed
      exact ⟨_, ledger_applyExpectedWithdrawals applied, counted found⟩
    · cases computed
      exact ⟨∅, Ledger.refl s, Nat.zero_le _⟩
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨expected, found, _, _, applied⟩ := computed
    exact ⟨_, ledger_applyExpectedWithdrawals applied, counted found⟩

/-- The withdrawals of a block pay at most as many indices as a payload has withdrawals.

From Gloas the bid that follows moves no balance. -/
theorem ledger_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ paid : Finset ValidatorIndex, Ledger s t paid ∅ 0 0 0 ∧
      paid.card ≤ if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0 := by
  unfold processBlockExecution at computed
  split at computed
  · rename_i gloas
    simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, bidOk⟩ := computed
    obtain ⟨paid, ledger, card⟩ := ledger_processWithdrawals withdrawnOk
    obtain ⟨payments, rfl⟩ := processExecutionPayloadBid_eq bidOk
    have whole := ledger.trans (Ledger.of_eq (s := middle) (t := { middle with
      builderPendingPayments := payments
      latestExecutionPayloadBid := fun _ => (body.signedExecutionPayloadBid gloas).message })
      rfl rfl)
    rw [Finset.union_empty, Finset.union_empty, add_zero] at whole
    refine ⟨_, whole, ?_⟩
    have capella : .shapella ≤ fork := Nat.le_trans (by decide) gloas
    simp only [capella, ↓reduceIte]
    exact card
  split at computed
  · rename_i capella
    simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨paid, ledger, card⟩ := ledger_processWithdrawals withdrawnOk
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    have whole := ledger.trans
      (Ledger.of_eq (t := { middle with latestExecutionPayloadHeader := fun _ => header })
        rfl rfl)
    rw [Finset.union_empty, Finset.union_empty, add_zero] at whole
    refine ⟨_, whole, ?_⟩
    simp only [capella, ↓reduceIte]
    exact card
  · rename_i capella
    simp only [capella, ↓reduceIte, nonpos_iff_eq_zero, Finset.card_eq_zero, exists_eq_right]
    dsimp only at computed
    split at computed
    · obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok computed
      exact Ledger.of_eq rfl rfl
    · cases computed
      exact Ledger.refl s

/-- Before Gloas, the execution part of a block keeps the registry. -/
theorem validators_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.validators = s.validators := by
  unfold processBlockExecution at computed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    obtain ⟨expected, -, -, appliedOk⟩ := processWithdrawals_expected early withdrawnOk
    have same := applyExpectedWithdrawals_validators appliedOk
    exact same
  · split at computed
    · obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok computed
      rfl
    · cases computed
      rfl

/-- Replace a validator by one with the same credentials.

This keeps the credentials of every validator. -/
private theorem credentials_setValidator {u w : BeaconState preset fork}
    {index : ValidatorIndex} {old new : Validator} (found : getValidator u index = .ok old)
    (set : u.setValidator index new = .ok w)
    (same : new.withdrawalCredentials = old.withdrawalCredentials) (j : ValidatorIndex)
    (before : Validator) (read : getValidator u j = .ok before) :
    ∃ later, getValidator w j = .ok later ∧
      later.withdrawalCredentials = before.withdrawalCredentials := by
  by_cases equal : j = index
  · subst equal
    have := Except.ok.inj (read.symm.trans found)
    subst this
    exact ⟨new, getValidator_setValidator_self set, same⟩
  · exact ⟨before, (getValidator_setValidator_of_ne set equal).trans read, rfl⟩

/-- Slashing a validator keeps the withdrawal credentials of every validator. -/
private theorem credentials_slashValidator {u w : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config u index whistleblower = .ok w) (j : ValidatorIndex)
    (before : Validator) (read : u.validators.data[j.toNat]? = some before) :
    ∃ later, w.validators.data[j.toNat]? = some later ∧
      later.withdrawalCredentials = before.withdrawalCredentials := by
  obtain ⟨exited, validator, _, marked, _, _, slashings, lowered, _, _, raised, last, exitOk,
    validatorOk, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok computed
  have exitedRead : ∃ middle, getValidator exited j = .ok middle ∧
      middle.withdrawalCredentials = before.withdrawalCredentials := by
    obtain ⟨old, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
      initiateValidatorExit_ok exitOk
    · exact ⟨before, getValidator_eq_ok_iff.mpr read, rfl⟩
    · have same := getValidator_of_validators_eq (exitQueue_validators queue).1
      exact credentials_setValidator ((same index).trans found) set rfl j before
        ((same j).trans (getValidator_eq_ok_iff.mpr read))
  obtain ⟨middle, middleRead, middleSame⟩ := exitedRead
  obtain ⟨later, laterRead, laterSame⟩ :=
    credentials_setValidator validatorOk markedOk rfl j middle middleRead
  have registry : w.validators = marked.validators := by
    have cancelled := slashValidator_last (last := last) (after := w) (index := index)
      (by subst done; rfl)
    rw [cancelled.1, increaseBalance_validators lastOk, increaseBalance_validators raisedOk,
      decreaseBalance_validators loweredOk]
  refine ⟨later, ?_, laterSame.trans middleSame⟩
  rw [registry]
  exact getValidator_eq_ok_iff.mp laterRead

/-- A slashing with the proposer as whistleblower debits the slashed validator its initial penalty.

It credits the whistleblower reward to the proposer that an earlier kept state reads. -/
private theorem ledger_slashValidator {r u w : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator}
    (keeps : StepKeeps r u) (inputs : PayloadInputs r u) (effective : EffectiveKept r u)
    (found : u.validators.data[index.toNat]? = some validator)
    (computed : slashValidator config u index none = .ok w) :
    ∃ proposer, getBeaconProposerIndex r = .ok proposer ∧
      Ledger u w ∅ ∅ 0
        (fun v => if v = proposer then validator.effectiveBalance.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v = index then validator.effectiveBalance.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) := by
  obtain ⟨exited, current, _, marked, _, _, slashings, lowered, proposer, reward, raised, last,
    exitOk, currentOk, _, markedOk, _, _, _, lowerOk, proposerOk, share, raiseOk, lastOk,
    final⟩ := slashValidator_ok computed
  have inside : index.toNat < u.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have sameEffective : current.effectiveBalance = validator.effectiveBalance := by
    have kept := effectiveKept_exit exitOk index.toNat inside
    simp only [effectiveAt, getValidator_eq_ok_iff.mp currentOk, found, Option.map_some,
      Option.getD_some] at kept
    exact UInt64.toNat_inj.mp kept
  -- The proposer is read after the exit, the slashed mark, the slashings write and the debit.
  have proposerRead : getBeaconProposerIndex r = .ok proposer := by
    rw [← getBeaconProposerIndex_slashDebit keeps inputs effective exitOk currentOk markedOk
      lowerOk]
    exact proposerOk
  refine ⟨proposer, proposerRead, ?_⟩
  -- The balances move only by the debit and the two credits.
  have exitBalances : exited.balances = u.balances := by
    obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok exitOk
    · rfl
    · obtain ⟨_, rfl⟩ := setValidator_ok set
      exact (exitQueue_validators queue).2
  have markedBalances : marked.balances = u.balances := by
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    exact exitBalances
  have shareLe : reward.toNat ≤
      (current.effectiveBalance /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat := by
    unfold proposerShare at share
    split at share
    · simp only [bind_ok_iff, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq] at share
      obtain ⟨product, productOk, rfl⟩ := share
      have productEq := (mulChecked_ok_iff.mp productOk).2
      rw [UInt64.toNat_div, productEq]
      change _ * 8 / 64 ≤ _
      omega
    · simp only [pure, Except.pure, Except.ok.injEq] at share
      subst reward
      exact Nat.div_le_self _ _
  have leftReward : (current.effectiveBalance /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT - reward).toNat =
        (current.effectiveBalance /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat - reward.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr shareLe)
  have cancelled := (slashValidator_last (last := last) (after := w) (index := index)
    (by subst final; rfl)).2
  have point (v : ValidatorIndex) :
      actualBalanceAt ⟨fork, w⟩ v.toNat =
        (actualBalanceAt ⟨fork, u⟩ v.toNat - if v = index then
          validator.effectiveBalance.toNat /
            (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) +
          (if v = proposer then reward.toNat else 0) +
          (if v = proposer then validator.effectiveBalance.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - reward.toNat
            else 0) := by
    rw [show actualBalanceAt ⟨fork, w⟩ v.toNat = actualBalanceAt ⟨fork, last⟩ v.toNat by
        simp only [actualBalanceAt, cancelled],
      actualBalanceAt_increaseBalance lastOk, actualBalanceAt_increaseBalance raiseOk,
      actualBalanceAt_decreaseBalance lowerOk, leftReward]
    have start : actualBalanceAt ⟨fork, { marked with slashings }⟩ v.toNat =
        actualBalanceAt ⟨fork, u⟩ v.toNat := by
      simp only [actualBalanceAt, markedBalances]
    simp only [start, Option.getD_none, UInt64.toNat_inj, eq_comm (a := index),
      eq_comm (a := proposer), UInt64.toNat_div, sameEffective]
  have shareLe' : reward.toNat ≤ validator.effectiveBalance.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    simpa only [UInt64.toNat_div, sameEffective] using shareLe
  exact {
    up := fun v => by
      rw [point v]
      simp only [Pi.zero_apply]
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = penalty at *
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = whistle at *
      split_ifs <;> omega
    down := fun v _ _ => by
      rw [point v]
      simp only [Pi.zero_apply]
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = penalty at *
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = whistle at *
      split_ifs <;> omega
    converted := fun v member => absurd member (Finset.notMem_empty v)
    lowered := fun v member => absurd member (Finset.notMem_empty v)
    kept := fun v before _ read => by
      obtain ⟨later, laterRead, same⟩ := credentials_slashValidator computed v before read
      exact ⟨later, laterRead, by simp only [hasCompoundingWithdrawalCredential, same]⟩
    fresh := fun v member => absurd member (Finset.notMem_empty v)
    switched := fun v member => absurd member (Finset.notMem_empty v) }

/-- A proposer slashing debits the slashed validator its initial penalty.

The penalty is read at the effective balance of that validator.

The slashing credits the whistleblower reward to the proposer of the slot. -/
theorem ledger_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) :
    ∃ (proposer slashed : ValidatorIndex) (validator : Validator),
      getBeaconProposerIndex s = .ok proposer ∧
      s.validators.data[slashed.toNat]? = some validator ∧ validator.slashed = false ∧
      (∃ later, t.validators.data[slashed.toNat]? = some later ∧ later.slashed = true) ∧
      Ledger s t ∅ ∅ 0
        (fun v => if v = proposer then validator.effectiveBalance.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v = slashed then validator.effectiveBalance.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) ∧
      Eligible (getCurrentEpoch s) validator := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, validator, found, _, slashable, _, _, _, _, slashed⟩ := computed
  have read := getValidator_eq_ok_iff.mp found
  obtain ⟨proposer, proposerRead, ledger⟩ := ledger_slashValidator (StepKeeps.refl s)
    (PayloadInputs.refl s) (effectiveKept_refl s) read slashed
  refine ⟨proposer, _, validator, proposerRead, read, ?_, ?_, ledger,
    eligible_of_slashable slashable⟩
  · simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at slashable
    exact slashable.1.1
  · have flag := (slashValidator_slashedFlag slashed).1
    cases later : t.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? with
    | none => simp [slashedFlag, getValidator, later, Except.map] at flag
    | some entry =>
      simp only [slashedFlag, getValidator, later, Except.map, Except.ok.injEq] at flag
      exact ⟨entry, rfl, flag⟩

/-- Take a state that keeps what the proposer of an earlier state reads.

From it, slashing each slashable index of a list in turn debits each slashed validator.

It also credits the proposer of the earlier state. -/
private theorem ledger_foldSlashIfSlashable {r : BeaconState preset fork}
    (chosen : ValidatorIndex)
    (choice : ∀ p, getBeaconProposerIndex r = .ok p → p = chosen) :
    ∀ (indices : List ValidatorIndex) {u w : BeaconState preset fork} {flag flag' : Bool},
      StepKeeps r u → PayloadInputs r u → EffectiveKept r u →
      u.validators.data.size = r.validators.data.size →
      indices.foldlM (slashIfSlashable config) (u, flag) = .ok (w, flag') →
      ∃ slashed : Finset ValidatorIndex,
        (slashed.Nonempty → getBeaconProposerIndex r = .ok chosen) ∧
        (∀ v ∈ slashed, ∃ validator later, u.validators.data[v.toNat]? = some validator ∧
          validator.slashed = false ∧ w.validators.data[v.toNat]? = some later ∧
          later.slashed = true) ∧
        (∀ v ∈ slashed, ∃ validator, u.validators.data[v.toNat]? = some validator ∧
          Eligible (getCurrentEpoch r) validator) ∧
        Ledger u w ∅ ∅ 0
          (fun v => if v = chosen then ∑ x ∈ slashed, effectiveAt ⟨fork, r⟩ x.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
          (fun v => if v ∈ slashed then effectiveAt ⟨fork, r⟩ v.toNat /
            (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0)
  | [], u, w, flag, flag', _, _, _, _, ok => by
    cases ok
    refine ⟨∅, fun empty => absurd empty Finset.not_nonempty_empty,
      fun v member => absurd member (Finset.notMem_empty v),
      fun v member => absurd member (Finset.notMem_empty v), ?_⟩
    exact (Ledger.refl u).mono ∅ (subset_refl _) (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
  | index :: rest, u, w, flag, flag', keeps, inputs, effective, size, ok => by
    obtain ⟨⟨middle, nextFlag⟩, first, tail⟩ := bind_ok_iff.mp ok
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨validator, found, first⟩ := first
    split at first
    · rename_i slashable
      simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at first
      obtain ⟨next, slashed, rfl, rfl⟩ := first
      have read := getValidator_eq_ok_iff.mp found
      obtain ⟨proposer, proposerRead, one⟩ :=
        ledger_slashValidator keeps inputs effective read slashed
      rw [choice proposer proposerRead] at one proposerRead
      obtain ⟨set, _, marks, eligibles, two⟩ := ledger_foldSlashIfSlashable chosen choice rest
        (keeps.trans (stepKeeps_slashValidator slashed))
        (inputs.trans (payloadInputs_slashValidator slashed))
        (effectiveKept_trans effective (effectiveKept_slash slashed) keeps.1)
        ((sameSizes_slashValidator slashed).1.trans size) tail
      have flagNext := slashValidator_slashedFlag slashed
      -- Each later member is unslashed when its fold starts, while this index is slashed by now.
      have fresh : index ∉ set := by
        intro member
        obtain ⟨entry, _, entryRead, entrySlashed, _⟩ := marks index member
        have marked := flagNext.1
        simp [slashedFlag, getValidator, entryRead, Except.map, entrySlashed] at marked
      have unslashed : validator.slashed = false := by
        simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at slashable
        exact slashable.1.1
      have effectiveIndex : effectiveAt ⟨fork, r⟩ index.toNat =
          validator.effectiveBalance.toNat := by
        rw [← effective index.toNat (size ▸ (Array.getElem?_eq_some_iff.mp read).1)]
        simp [effectiveAt, read]
      refine ⟨insert index set, fun _ => proposerRead, ?_, ?_, ?_⟩
      · intro v member
        rcases Finset.mem_insert.mp member with rfl | inside
        · have persist := (foldlM_slashIfSlashable rest tail).2.1 v flagNext.1
          cases later : w.validators.data[v.toNat]? with
          | none => simp [slashedFlag, getValidator, later, Except.map] at persist
          | some entry =>
            simp only [slashedFlag, getValidator, later, Except.map, Except.ok.injEq] at persist
            exact ⟨validator, entry, read, unslashed, rfl, persist⟩
        · obtain ⟨entry, later, entryRead, entrySlashed, laterRead, laterSlashed⟩ :=
            marks v inside
          have apart : v ≠ index := fun equal => fresh (equal ▸ inside)
          have before := flagNext.2 v.toNat (fun equal => apart (UInt64.toNat_inj.mp equal))
          cases old : u.validators.data[v.toNat]? with
          | none => simp [slashedFlagAt, old, entryRead] at before
          | some original =>
            simp [slashedFlagAt, old, entryRead, entrySlashed] at before
            exact ⟨original, later, rfl, before, laterRead, laterSlashed⟩
      · intro v member
        rcases Finset.mem_insert.mp member with rfl | inside
        · refine ⟨validator, read, ?_⟩
          have epoch : getCurrentEpoch u = getCurrentEpoch r := by
            simp only [getCurrentEpoch, keeps.2.1]
          rw [← epoch]
          exact eligible_of_slashable slashable
        · obtain ⟨entry, entryRead, entryEligible⟩ := eligibles v inside
          exact (lives_slashValidator slashed).back (registryLifecycle_slashValidator slashed)
            (.of_frame (frame_slashValidator slashed).toFrame) entryRead entryEligible
      · have both := one.trans two
        rw [add_zero] at both
        refine both.mono ∅ (subset_refl _) (fun v => ?_) (fun v => ?_)
        · simp only [Pi.add_apply, Finset.sum_insert fresh, effectiveIndex]
          split_ifs <;> omega
        · simp only [Pi.add_apply, Finset.mem_insert]
          by_cases equal : v = index
          · subst equal
            simp [fresh, effectiveIndex]
          · simp [equal]
    · cases first
      exact ledger_foldSlashIfSlashable chosen choice rest keeps inputs effective size tail

/-- An attester slashing slashes some validators, each not slashed before.

It debits each its initial penalty and credits the whistleblower rewards to the proposer. -/
theorem ledger_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ (proposer : ValidatorIndex) (slashed : Finset ValidatorIndex),
      (slashed.Nonempty → getBeaconProposerIndex s = .ok proposer) ∧
      (∀ v ∈ slashed, ∃ validator later, s.validators.data[v.toNat]? = some validator ∧
        validator.slashed = false ∧ t.validators.data[v.toNat]? = some later ∧
        later.slashed = true) ∧
      (∀ v ∈ slashed, ∃ validator, s.validators.data[v.toNat]? = some validator ∧
        Eligible (getCurrentEpoch s) validator) ∧
      Ledger s t ∅ ∅ 0
        (fun v => if v = proposer then ∑ x ∈ slashed, effectiveAt ⟨fork, s⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v ∈ slashed then effectiveAt ⟨fork, s⟩ v.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨u, flag⟩, folded, _, _, rfl⟩ := computed
  obtain ⟨chosen, choice⟩ : ∃ chosen : ValidatorIndex,
      ∀ p, getBeaconProposerIndex s = .ok p → p = chosen := by
    cases read : getBeaconProposerIndex s with
    | ok p => exact ⟨p, fun q found => (Except.ok.inj found).symm⟩
    | error _ => exact ⟨0, fun q found => by cases found⟩
  obtain ⟨slashed, nonempty, marks, eligibles, ledger⟩ :=
    ledger_foldSlashIfSlashable chosen choice _
      (StepKeeps.refl s) (PayloadInputs.refl s) (effectiveKept_refl s) rfl folded
  exact ⟨chosen, slashed, nonempty, marks, eligibles, ledger⟩

/-- A step that keeps every validator, lowers no balance and raises each by at most its credit. -/
theorem Ledger.of_rise {other : ValidatorIndex → ℕ}
    (validators : t.validators.data = s.validators.data)
    (rise : ∀ v : ValidatorIndex, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
      actualBalanceAt ⟨fork, t⟩ v.toNat ∧
      actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat + other v) :
    Ledger s t ∅ ∅ 0 other 0 where
  up v := by have := (rise v).2; simp only [Pi.zero_apply]; omega
  down v _ _ := by have := (rise v).1; simp only [Pi.zero_apply]; omega
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := ⟨validator, by rw [validators]; exact found, rfl⟩
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- Take a step that keeps the registry or appends one validator.

If it moves each balance by at most a credit, it gives a ledger with only that credit. -/
private theorem Ledger.of_append {credit : ValidatorIndex → ℕ}
    (validators : t.validators.data = s.validators.data ∨
      ∃ added, t.validators.data = s.validators.data.push added)
    (balances : ∀ v : ValidatorIndex,
      actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat + credit v ∧
      actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat) :
    Ledger s t ∅ ∅ 0 credit 0 where
  up v := by have := (balances v).1; simp only [Pi.zero_apply]; omega
  down v _ _ := by have := (balances v).2; simp only [Pi.zero_apply]; omega
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := by
    refine ⟨validator, ?_, rfl⟩
    rcases validators with same | ⟨added, pushed⟩
    · rw [same]; exact found
    · rw [pushed, Array.getElem?_push]
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.ne_of_lt inside))]
      exact found
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- From Electra a deposit moves no balance, since it only queues the amount.

A new validator gets a zero balance, which reads like no balance.

The balances must match the validators, so that a new validator gets a new balance. -/
theorem ledger_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (computed : processDeposit config checks before s deposit = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok computed
  generalize hs' : { s with eth1DepositIndex := fun _ => next } = s' at applied
  have balances' : s'.balances = s.balances := by rw [← hs']
  have validators' : s'.validators = s.validators := by rw [← hs']
  have matched' : BalancesMatch s' := by
    unfold BalancesMatch at matched ⊢; rw [balances', validators']; exact matched
  have actual' (i : ℕ) : actualBalanceAt ⟨fork, s'⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
    simp only [actualBalanceAt, balances']
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, queuedEq⟩ | ⟨early, _⟩
  · exact Ledger.of_append (.inl (by rw [validators'])) fun v => by
      have := actual' v.toNat; exact ⟨by simp; omega, by omega⟩
  · subst queuedEq
    exact Ledger.of_append (.inl (by rw [validators'])) fun v => by
      have := actual' v.toNat
      simp only [actualBalanceAt] at this ⊢
      exact ⟨by simp; omega, by omega⟩
  · obtain ⟨validatorsPushed, balancesPushed⟩ := addValidatorToRegistry_push added matched'
    have finalBalances : t.balances.data = s'.balances.data.push 0 := by
      rw [queuedEq]; exact balancesPushed
    refine Ledger.of_append (.inr ⟨_, by rw [queuedEq, ← validators']; exact validatorsPushed⟩)
      fun v => ?_
    -- An appended zero balance reads like no balance.
    have zero : actualBalanceAt ⟨fork, t⟩ v.toNat = actualBalanceAt ⟨fork, s⟩ v.toNat := by
      rw [actualBalanceAt_push finalBalances, ← actual' v.toNat]
      split
      · rename_i at_end
        simp [actualBalanceAt, at_end]
      · rfl
    exact ⟨by simp [zero], by omega⟩
  · exact absurd electra (Nat.not_le_of_lt early)

/-- Writing a validator that compounds exactly when the old one did moves no balance. -/
private theorem Ledger.setValidator {i : ValidatorIndex} {old new : Validator}
    (found : getValidator s i = .ok old)
    (same : hasCompoundingWithdrawalCredential new = hasCompoundingWithdrawalCredential old)
    (set : s.setValidator i new = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read := getValidator_eq_ok_iff.mp found
  refine Ledger.of_kept rfl fun v validator located => ?_
  by_cases eq : v.toNat = i.toNat
  · rw [eq, read, Option.some.injEq] at located
    subst located
    exact ⟨new, by simp [BeaconState.putValidator, eq], same⟩
  · exact ⟨validator, by simpa [BeaconState.putValidator, Ne.symm eq] using located, rfl⟩

/-- The start of an exit moves no balance, and keeps the credentials. -/
private theorem Ledger.exit {i : ValidatorIndex}
    (computed : initiateValidatorExit config s i = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Ledger.refl _
  · have same := exitQueue_validators queue
    have one : Ledger s queued ∅ ∅ 0 0 0 := Ledger.of_eq (by rw [same.2]) (by rw [same.1])
    have two := Ledger.setValidator (old := validator)
      (by rw [getValidator_of_validators_eq same.1]; exact found) (by rfl) set
    simpa only [Finset.empty_union, add_zero] using one.trans two

theorem ledger_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact Ledger.exit exited

/-- A fold whose every step moves no balance and keeps the credentials does the same. -/
private theorem Ledger.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)} {items : List α}
    (kept : ∀ u x u', step u x = .ok u' → Ledger u u' ∅ ∅ 0 0 0)
    (computed : items.foldlM step s = .ok t) : Ledger s t ∅ ∅ 0 0 0 :=
  foldlM_ok_invariant (fun u => Ledger s u ∅ ∅ 0 0 0)
    (fun _ _ _ before ok => by
      simpa only [Finset.empty_union, add_zero] using before.trans (kept _ _ _ ok))
    (Ledger.refl s) computed

theorem ledger_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    refine Ledger.foldlM (fun u signed u' ok => ?_) computed
    obtain ⟨validator, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
    -- Credentials of either prefix do not compound.
    refine Ledger.setValidator found ?_ set
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, bls,
      executionCredentials_prefix, BLS_WITHDRAWAL_PREFIX, ETH1_ADDRESS_WITHDRAWAL_PREFIX,
      COMPOUNDING_WITHDRAWAL_PREFIX]
  · cases computed
    exact Ledger.refl _

/-- Queueing the excess caps one balance at the activation balance, and keeps the registry. -/
private theorem queueExcessActiveBalance_capped {electra : .pectra ≤ fork} {i : ValidatorIndex}
    (computed : queueExcessActiveBalance s electra i = .ok t) :
    t.validators.data = s.validators.data ∧ ∀ j, actualBalanceAt ⟨fork, t⟩ j =
      if j = i.toNat then min (actualBalanceAt ⟨fork, s⟩ j) preset.MIN_ACTIVATION_BALANCE.toNat
      else actualBalanceAt ⟨fork, s⟩ j := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨balance, read, computed⟩ := computed
  rw [getBalance_eq_ok_iff] at read
  split at computed
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨inside, rfl⟩ := setBalance_ok set
    have := UInt64.lt_iff_toNat_lt.mp above
    refine ⟨rfl, fun j => ?_⟩
    by_cases eq : j = i.toNat
    · subst eq
      simp [actualBalanceAt, BeaconState.putBalance, read]
      omega
    · simp [actualBalanceAt, BeaconState.putBalance, eq, Ne.symm eq]
  · rename_i below
    cases computed
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp below)
    refine ⟨rfl, fun j => ?_⟩
    by_cases eq : j = i.toNat
    · subst eq
      simp [actualBalanceAt, read]
      omega
    · simp [eq]

/-- A switch to compounding converts one validator that did not compound before. -/
private theorem Ledger.switch {electra : .pectra ≤ fork} {i : ValidatorIndex}
    {validator : Validator}
    (found : s.validators.data[i.toNat]? = some validator)
    (fresh : hasCompoundingWithdrawalCredential validator = false)
    (computed : switchToCompoundingValidator s electra i = .ok t) : Ledger s t ∅ {i} 0 0 0 := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨old, read, _, set, queued⟩ := computed
  rw [getValidator_eq_ok_iff, found, Option.some.injEq] at read
  subst read
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  obtain ⟨same, capped⟩ := queueExcessActiveBalance_capped queued
  have balances : ∀ j, actualBalanceAt ⟨fork, t⟩ j = if j = i.toNat then
      min (actualBalanceAt ⟨fork, s⟩ j) preset.MIN_ACTIVATION_BALANCE.toNat
      else actualBalanceAt ⟨fork, s⟩ j := capped
  have apart {v : ValidatorIndex} (notConv : v ∉ ({i} : Finset ValidatorIndex)) :
      v.toNat ≠ i.toNat := fun eq =>
    notConv (Finset.mem_singleton.mpr (UInt64.toNat_inj.mp eq))
  constructor
  · intro v
    rw [balances]
    split <;> simp
  · intro v _ notConv
    simp [balances, apart notConv]
  · intro v member
    rw [Finset.mem_singleton.mp member, balances]
    simp
  · intro v member _
    rw [Finset.mem_singleton.mp member, balances]
    simp
  · intro v validator' notConv located
    exact ⟨validator', by
      simpa [same, BeaconState.putValidator, Ne.symm (apart notConv)] using located, rfl⟩
  · intro v member validator' located
    rw [Finset.mem_singleton.mp member, found, Option.some.injEq] at located
    exact located ▸ fresh
  · intro v member
    rw [Finset.mem_singleton.mp member, same]
    simp [BeaconState.putValidator, hasCompoundingWithdrawalCredential,
      isCompoundingWithdrawalCredential]

/-- Queueing a consolidation moves no balance, and keeps the credentials. -/
private theorem Ledger.consolidate {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (computed : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, _, marked, pending, _, _, set, _, rfl⟩ := queueConsolidation_steps computed
  have two := Ledger.setValidator (old := source) (by rw [getValidator_eq_ok_iff]; exact found)
    (by rfl) set
  have one := (Ledger.of_eq (s := s) (by rfl) (by rfl)).trans two
  simpa only [Finset.empty_union, add_zero] using one.trans
    (Ledger.of_eq (t := { marked with pendingConsolidations := fun _ => pending }) rfl rfl)

/-- A consolidation request converts at most one validator, and moves no other balance. -/
theorem ledger_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config s electra request = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧ conv.card ≤ 1 := by
  -- A validator valid for a switch has the execution address prefix, so it does not compound.
  have fresh : ∀ validator, isValidSwitchToCompoundingRequest s request validator = true →
      hasCompoundingWithdrawalCredential validator = false := by
    intro validator valid
    simp only [isValidSwitchToCompoundingRequest, hasEth1WithdrawalCredential, Bool.and_eq_true,
      beq_iff_eq] at valid
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, valid.1.1.2,
      ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals try first
    | (cases computed; done)
    | (cases computed; exact ⟨∅, Ledger.refl _, by simp⟩)
  · rename_i checked valid
    exact ⟨_, Ledger.switch (getElem?_toNat_of_ofNatChecked checked) (fresh _ valid)
      (liftAccessor_ok.mp computed), (Finset.card_singleton _).le⟩
  · rename_i checked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨∅, Ledger.consolidate (getElem?_toNat_of_ofNatChecked checked) computed, by simp⟩

/-- The deposit requests and then the withdrawal requests of a payload move no balance.

They keep the credentials. -/
theorem ledger_depositWithdrawalRequests {electra : .pectra ≤ fork}
    {deposits : List DepositRequest} {withdrawals : List WithdrawalRequest}
    {deposited withdrawn : BeaconState preset fork}
    (depositsOk : deposits.foldlM (processDepositRequest · electra ·) s = .ok deposited)
    (withdrawalsOk :
      withdrawals.foldlM (processWithdrawalRequest config · electra ·) deposited = .ok withdrawn) :
    Ledger s withdrawn ∅ ∅ 0 0 0 := by
  have one : Ledger s deposited ∅ ∅ 0 0 0 := Ledger.foldlM (fun _ _ _ ok =>
    Ledger.of_eq (by rw [(processDepositRequest_ok ok).2.2.1])
      (by rw [(processDepositRequest_ok ok).2.1])) depositsOk
  have two : Ledger deposited withdrawn ∅ ∅ 0 0 0 := by
    refine Ledger.foldlM (fun _ _ _ ok => ?_) withdrawalsOk
    rcases withdrawalRequest_cases ok with rfl | ⟨_, _, _, exited⟩ | ⟨_, _, _, _, requested⟩
    · exact Ledger.refl _
    · exact Ledger.exit exited
    -- A partial withdrawal keeps the registry and the balances.
    · have kept := requestPartialWithdrawal_kept requested
      exact Ledger.of_eq (congrArg (·.data) kept.2.1) (congrArg (·.data) kept.1)
  simpa only [Finset.empty_union, add_zero] using one.trans two

/-- Deposit, withdrawal and consolidation requests, run in turn, move no balance but conversions.

Each consolidation request converts at most one validator. -/
private theorem ledger_requests {electra : .pectra ≤ fork} {deposits : List DepositRequest}
    {withdrawals : List WithdrawalRequest} {consolidations : List ConsolidationRequest}
    {deposited withdrawn : BeaconState preset fork}
    (depositsOk : deposits.foldlM (processDepositRequest · electra ·) s = .ok deposited)
    (withdrawalsOk :
      withdrawals.foldlM (processWithdrawalRequest config · electra ·) deposited = .ok withdrawn)
    (consolidationsOk : consolidations.foldlM (processConsolidationRequest config · electra ·)
      withdrawn = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧
      conv.card ≤ consolidations.length := by
  have first := ledger_depositWithdrawalRequests depositsOk withdrawalsOk
  -- Each consolidation request converts at most one validator.
  have three : ∀ (requests : List ConsolidationRequest) (u : BeaconState preset fork),
      requests.foldlM (processConsolidationRequest config · electra ·) u = .ok t →
      ∃ conv : Finset ValidatorIndex, Ledger u t ∅ conv 0 0 0 ∧ conv.card ≤ requests.length := by
    intro requests
    induction requests with
    | nil =>
      intro u ok
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at ok
      exact ⟨∅, ok ▸ Ledger.refl u, by simp⟩
    | cons request rest ih =>
      intro u ok
      rw [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨middle, first, others⟩ := ok
      obtain ⟨conv, ledger, card⟩ := ledger_processConsolidationRequest first
      obtain ⟨conv', ledger', card'⟩ := ih middle others
      refine ⟨conv ∪ conv', ?_, ?_⟩
      · simpa only [Finset.empty_union, add_zero] using ledger.trans ledger'
      have := Finset.card_union_le conv conv'
      simp only [List.length_cons]
      omega
  obtain ⟨conv, ledger, card⟩ := three _ _ consolidationsOk
  exact ⟨conv, by simpa only [Finset.empty_union, add_zero] using first.trans ledger, card⟩

/-- The requests of the execution layer convert at most one validator per consolidation request.

They move no other balance. -/
theorem ledger_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := computed
  obtain ⟨conv, ledger, card⟩ := ledger_requests deposits withdrawals consolidations
  have bound := (body.executionRequests electra).consolidations.bound electra.2
  refine ⟨conv, ledger, ?_⟩
  simp only [Array.length_toList] at card
  omega

/-- From Gloas, the payload of the parent changes no balance outside a set of converted validators.

The set has at most the preset's most consolidation requests per payload.

No balance rises.

A converted balance falls to no less than the smaller of its old balance and the activation balance.
-/
theorem ledger_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks s gloas body = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  have bound := (processParentExecutionPayload_counts computed).2.1
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact ⟨∅, Ledger.refl _, Nat.zero_le _⟩
  -- Settling the payment and the requests of builders keep the balances and the validators.
  have settledEq := settleParentPayment_eq settledOk
  have settle := Ledger.of_eq (s := s) (t := settled) (by rw [settledEq]) (by rw [settledEq])
  have builders := Ledger.foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
    exact Ledger.of_eq rfl rfl) buildersOk
  have exits := Ledger.foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
    exact Ledger.of_eq rfl rfl) exitsOk
  obtain ⟨conv, requests, card⟩ := ledger_requests depositsOk withdrawalsOk consolidationsOk
  refine ⟨conv, ?_, ?_⟩
  · exact ((settle.zero_left requests).zero_right builders).zero_right exits |>.zero_right
      (Ledger.of_eq rfl rfl)
  · simp only [Array.length_toList] at card
    omega

/-- The sync aggregate step keeps the registry and the current sync committee. -/
theorem processSyncAggregate_kept {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) :
    t.validators = s.validators ∧ t.currentSyncCommittee = s.currentSyncCommittee := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun x : BeaconState preset fork =>
    x.validators = s.validators ∧ x.currentSyncCommittee = s.currentSyncCommittee)
    (fun _ _ _ held ok => ?_) ⟨rfl, rfl⟩ folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    obtain ⟨_, set⟩ := increaseBalance_ok raised
    obtain ⟨_, rfl⟩ := setBalance_ok set
    obtain ⟨_, set'⟩ := increaseBalance_ok paid
    obtain ⟨_, rfl⟩ := setBalance_ok set'
    exact held
  · obtain ⟨_, set⟩ := decreaseBalance_ok (liftAccessor_ok.mp ok)
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact held

/-- Each member index found for a list of keys stands for one of those keys.

Its validator holds that key. -/
private theorem countP_validatorIndexOfPubkey_le (v : ValidatorIndex) :
    ∀ {keys : List Cryptography.Bls.BLSPubkey} {members : List ValidatorIndex},
      keys.mapM (validatorIndexOfPubkey s) = .ok members →
      members.countP (fun m => m.toNat = v.toNat) ≤
        (keys.filter fun key => (s.validators.data[v.toNat]?).any (·.pubkey == key)).length
  | [], members, ok => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    simp
  | key :: keys, members, ok => by
    obtain ⟨m, rest, head, tail, rfl⟩ := mapM_cons_ok.mp ok
    have ih := countP_validatorIndexOfPubkey_le v tail
    by_cases same : m.toNat = v.toNat
    · have holds : (s.validators.data[v.toNat]?).any (·.pubkey == key) = true := by
        unfold validatorIndexOfPubkey at head
        split at head
        · rename_i position found
          simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at head
          have position_eq := (Base.Uint64.ofNatChecked_ok_iff.mp head).2
          obtain ⟨inside, matching, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
          rw [← same, position_eq, Array.getElem?_eq_getElem inside]
          simpa using matching
        · cases head
      simp only [List.countP_cons, same, decide_true, ↓reduceIte, List.filter_cons, holds,
        List.length_cons]
      omega
    · simp only [List.countP_cons, same, decide_false, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero, List.filter_cons]
      split <;> (try simp only [List.length_cons]) <;> omega

/-- In the fold of the sync rewards, a balance moves by at most the reward for each seat.

These seats are the seats of its validator.

When that validator is the proposer, the bound adds the proposer share for each signed seat. -/
private theorem foldl_syncReward_bounds (r p : ℕ) (chosen : ValidatorIndex) (j : ℕ) :
    ∀ (members : List (ValidatorIndex × Bool)) (b : ℕ),
      members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then r else 0) +
            (if chosen.toNat = j then p else 0)
          else if member.1.toNat = j then balance - r else balance) b ≤
        b + r * members.countP (fun m => m.1.toNat = j) +
          (if chosen.toNat = j then p * members.countP (·.2) else 0) ∧
      b ≤ members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then r else 0) +
            (if chosen.toNat = j then p else 0)
          else if member.1.toNat = j then balance - r else balance) b +
        r * members.countP (fun m => m.1.toNat = j)
  | [], b => by simp
  | ⟨index, signed⟩ :: members, b => by
    obtain ⟨up, down⟩ := foldl_syncReward_bounds r p chosen j members
      (if signed then b + (if index.toNat = j then r else 0) +
        (if chosen.toNat = j then p else 0)
      else if index.toNat = j then b - r else b)
    simp only [List.foldl_cons, List.countP_cons]
    cases signed <;> by_cases h1 : index.toNat = j <;> by_cases h2 : chosen.toNat = j <;>
      simp only [h1, h2, Bool.false_eq_true, decide_true, decide_false, ↓reduceIte,
        Nat.mul_add, Nat.mul_one, Nat.add_zero] at up down ⊢ <;>
      omega

/-- The sync aggregate pays each member the participant reward for each seat it signed.

It charges each member for each seat it did not sign.

The proposer of the slot earns its share for each signed seat, which no participant amount counts.
-/
theorem ledger_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∃ (proposer : ValidatorIndex) (reward : Gwei) (share : ℕ) (sync : ValidatorIndex → ℕ),
      syncParticipantReward s = .ok reward ∧
      (0 < share → getBeaconProposerIndex s = .ok proposer) ∧
      share ≤ preset.SYNC_COMMITTEE_SIZE.toNat *
        (reward.toNat * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) ∧
      (∀ v, sync v ≤ syncSeats t altair v.toNat * reward.toNat) ∧
      Ledger s t ∅ ∅ sync (fun v => if v = proposer then share else 0) 0 := by
  obtain ⟨reward, proposerReward, members, chosen, rewardOk, proposerValue, membersOk, signed,
    balances⟩ := processSyncAggregate_balance computed
  have kept := processSyncAggregate_kept computed
  have sizes := (sameSizes_processSyncAggregate computed).2
  obtain ⟨pairs, pairsDef⟩ :
      ∃ pairs, pairs = (members.zip aggregate.syncCommitteeBits.bits.toArray).toList := ⟨_, rfl⟩
  rw [← pairsDef] at signed balances
  have membersSize := (array_mapM_ok membersOk).1
  rw [Vector.size_toArray] at membersSize
  have pairsLength : pairs.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat := by
    rw [pairsDef, Array.length_toList, Array.size_zip]
    exact (Nat.min_le_left _ _).trans membersSize.le
  refine ⟨chosen, reward, proposerReward.toNat * pairs.countP (·.2),
    fun v => reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat), rewardOk, ?_, ?_, ?_, ?_⟩
  · intro positive
    apply signed
    have count : 0 < pairs.countP (·.2) :=
      Nat.pos_of_ne_zero fun zero => by simp [zero] at positive
    obtain ⟨member, member_in, holds⟩ := List.countP_pos_iff.mp count
    exact ⟨member, member_in, by simpa using holds⟩
  · rw [← proposerValue, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ ((List.countP_le_length).trans pairsLength)
  · intro v
    dsimp only
    rw [Nat.mul_comm (syncSeats t altair v.toNat)]
    apply Nat.mul_le_mul_left
    rw [Array.mapM_eq_mapM_toList] at membersOk
    cases listed : (s.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
        (validatorIndexOfPubkey s) with
    | error => rw [listed] at membersOk; cases membersOk
    | ok list =>
      rw [listed] at membersOk
      have same : list.toArray = members := Except.ok.inj membersOk
      subst same
      -- The first entries of the pairs are a prefix of the members.
      have zipped : ((list.zip aggregate.syncCommitteeBits.bits.toArray.toList).countP
          fun m => decide (m.1.toNat = v.toNat)) ≤
          list.countP fun m => decide (m.toNat = v.toNat) := by
        have firsts : List.Sublist
            ((list.zip aggregate.syncCommitteeBits.bits.toArray.toList).map Prod.fst) list := by
          rw [List.zip_eq_zip_take_min, List.map_fst_zip (by simp)]
          exact List.take_sublist _ _
        simpa [List.countP_map, Function.comp_def] using firsts.countP_le
          (p := fun m : ValidatorIndex => decide (m.toNat = v.toNat))
      have seats := countP_validatorIndexOfPubkey_le v listed
      rw [pairsDef, Array.toList_zip]
      simp only [syncSeats, kept.1, kept.2]
      exact zipped.trans seats
  · have bounds := fun v : ValidatorIndex =>
      foldl_syncReward_bounds reward.toNat proposerReward.toNat chosen v.toNat pairs
    have equal : ∀ v : ValidatorIndex, chosen.toNat = v.toNat ↔ v = chosen :=
      fun v => ⟨fun h => (UInt64.toNat_inj.mp h).symm, fun h => h ▸ rfl⟩
    have moved : ∀ v : ValidatorIndex,
        actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat +
          reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat) +
          (if v = chosen then proposerReward.toNat * pairs.countP (·.2) else 0) ∧
        actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat +
          reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat) := by
      intro v
      cases found : s.balances.data[v.toNat]? with
      | none =>
        have missing : t.balances.data[v.toNat]? = none := by
          rw [Array.getElem?_eq_none_iff] at found ⊢
          omega
        simp [actualBalanceAt, found, missing]
      | some balance =>
        obtain ⟨final, finalFound, finalValue⟩ := balances v.toNat balance found
        obtain ⟨up, down⟩ := bounds v balance.toNat
        rw [← finalValue] at up down
        simp only [actualBalanceAt, found, finalFound, Option.map_some, Option.getD_some]
        by_cases isChosen : v = chosen
        · subst isChosen
          simp only [↓reduceIte] at up ⊢
          exact ⟨up, down⟩
        · simp only [isChosen, ↓reduceIte, Nat.add_zero] at up ⊢
          simp only [mt (equal v).mp isChosen, ↓reduceIte, Nat.add_zero] at up
          exact ⟨up, down⟩
    exact {
      up := fun v => (moved v).1
      down := fun v _ _ => by have := (moved v).2; simp only [Pi.zero_apply]; omega
      converted := fun v member => absurd member (Finset.notMem_empty v)
      lowered := fun v member => absurd member (Finset.notMem_empty v)
      kept := fun v validator _ found => ⟨validator, by rw [kept.1]; exact found, rfl⟩
      fresh := fun v member => absurd member (Finset.notMem_empty v)
      switched := fun v member => absurd member (Finset.notMem_empty v) }

end Steps

end BlockLedger

end EthLib.Consensus
