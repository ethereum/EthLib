module

public import EthLib.Consensus.Proofs.Transition.BlockLedger
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
# The credits of a block

The operations of a block credit the proposers of attestations and the recipients of deposits.

Those credits read the participation flags, the proposer and the base rewards.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

open BlockLedger

namespace BlockCredits

/-! ### The participation flags behind the proposer rewards of attestations -/

/-- The registry does not shrink, and each flag at a position of it before is kept.

A position past the end of a list of flags reads as the empty flags. -/
def FlagKeeps {fork : Fork} (state after : BeaconState preset fork) : Prop :=
  state.validators.data.size ≤ after.validators.data.size ∧
    ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat)
      (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length), position < state.validators.data.size →
      hasFlag (((recentParticipation state altair current).data[position]?).getD 0)
          flag.val.toUInt64 = true →
        hasFlag (((recentParticipation after altair current).data[position]?).getD 0)
          flag.val.toUInt64 = true

private theorem FlagKeeps.refl {fork : Fork} (state : BeaconState preset fork) :
    FlagKeeps state state :=
  ⟨Nat.le_refl _, fun _ _ _ _ _ set => set⟩

private theorem FlagKeeps.trans {fork : Fork} {first second third : BeaconState preset fork}
    (one : FlagKeeps first second) (two : FlagKeeps second third) : FlagKeeps first third :=
  ⟨Nat.le_trans one.1 two.1, fun altair current position flag inside set =>
    two.2 altair current position flag (Nat.lt_of_lt_of_le inside one.1)
      (one.2 altair current position flag inside set)⟩

private theorem FlagKeeps.foldlM {fork : Fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → FlagKeeps a b) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) : FlagKeeps a b :=
  (foldlM_ok_steps FlagKeeps FlagKeeps.refl FlagKeeps.trans each computed).1

/-- A step that grows the registry and keeps both lists of flags keeps each flag. -/
private theorem FlagKeeps.of_flags {fork : Fork} {state after : BeaconState preset fork}
    (grows : state.validators.data.size ≤ after.validators.data.size)
    (flags : ParticipationKept state after) : FlagKeeps state after :=
  ⟨grows, fun altair current _ _ _ set => by
    cases current <;> simpa [recentParticipation, flags.1, flags.2] using set⟩

/-- A step that grows the registry and keeps the flags below its old size keeps each flag. -/
private theorem FlagKeeps.of_below {fork : Fork} {state after : BeaconState preset fork}
    (grows : state.validators.data.size ≤ after.validators.data.size)
    (below : ParticipationKeptBelow state after) : FlagKeeps state after :=
  ⟨grows, fun altair current position _ inside set => by
    have kept := below altair position inside
    cases current <;> simpa [recentParticipation, kept.1, kept.2] using set⟩

/-- An attestation keeps each flag of both epochs, and grows no smaller registry. -/
private theorem flagKeeps_processAttestation {fork : Fork} {state after : BeaconState preset fork}
    {attestation : Attestation preset fork} {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    FlagKeeps state after :=
  ⟨(frame_processAttestation computed).registryGrows,
    fun altair current position kept _ flagged =>
      processAttestation_keepsFlag computed altair current position kept flagged⟩

/-- A missing entry weighs as the empty flags, which weigh nothing. -/
private theorem flagTerm (flags : Option ParticipationFlags) (base : ℕ) :
    (flags.map (flagValue · base)).getD 0 = flagValue (flags.getD 0) base := by
  cases flags with
  | none =>
    have empty : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length,
        hasFlag 0 flag.val.toUInt64 = false := by decide
    simp [flagValue, empty]
  | some flags => rfl

/-- More flags weigh at least as much. -/
private theorem flagValue_mono {a b : ParticipationFlags} (base : ℕ)
    (more : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length,
      hasFlag a flag.val.toUInt64 = true → hasFlag b flag.val.toUInt64 = true) :
    flagValue a base ≤ flagValue b base := by
  unfold flagValue
  apply List.sum_le_sum
  intro flag _
  by_cases set : hasFlag a flag.val.toUInt64 = true
  · simp [set, more flag set]
  · simp only [Bool.not_eq_true] at set
    simp [set]

/-- Flags of existing validators that are kept raise a potential weighed on existing validators.
-/
private theorem recentFlagSum_mono_below {fork : Fork} {s t : BeaconState preset fork}
    (grow : FlagKeeps s t) (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ)
    (support : ∀ i, s.validators.data.size ≤ i → base i = 0) :
    recentFlagSum s altair base count ≤ recentFlagSum t altair base count := by
  unfold recentFlagSum flagSumOf
  refine Nat.add_le_add (List.sum_le_sum fun i _ => ?_) (List.sum_le_sum fun i _ => ?_)
  all_goals
    rw [flagTerm, flagTerm]
    by_cases inside : i < s.validators.data.size
    · first
        | exact flagValue_mono _ fun flag => by
            simpa [recentParticipation] using grow.2 altair false i flag inside
        | exact flagValue_mono _ fun flag => by
            simpa [recentParticipation] using grow.2 altair true i flag inside
    · rw [support i (Nat.le_of_not_lt inside)]
      simp [flagValue]

section Grow

variable {fork : Fork} {s t : BeaconState preset fork}

/-- The steps of an epoch that the epoch frame laws name keep each flag of an existing validator. -/
private theorem growsLaws : EpochFrameLaws (@FlagKeeps preset fork) where
  refl s := FlagKeeps.refl s
  trans one two := one.trans two
  setValidatorAt set _ _ _ _ _ := by
    have size := Nat.le_of_eq (sameSizes_setValidatorAt set).1.symm
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact FlagKeeps.of_flags size ⟨rfl, rfl⟩
  increaseBalance ok :=
    FlagKeeps.of_flags (frame_increaseBalance ok).registryGrows (flags_increase ok)
  decreaseBalance ok :=
    FlagKeeps.of_flags (frame_decreaseBalance ok).registryGrows (flags_decrease ok)
  initiateValidatorExit ok :=
    FlagKeeps.of_flags (frame_initiateValidatorExit ok).registryGrows (flags_exit ok)
  addValidatorToRegistry ok fresh :=
    FlagKeeps.of_below (frame_addValidatorToRegistry ok fresh).registryGrows (flagsBelow_add ok)
  eth1DataVotes _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  inactivityScores _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  slashings _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  randaoMixes _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  historicalRoots _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  historicalSummaries _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  participationRecords _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  pendingDeposits _ _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  pendingConsolidations _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  syncCommittees _ _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  proposerLookahead _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩
  ptcWindow _ _ := FlagKeeps.of_flags (Nat.le_refl _) ⟨rfl, rfl⟩

/-- From Altair an attestation credits the proposer of the slot its reward, and nothing else.

448 times that reward is at most what the newly set flags add to the potential.

Take each validator active in the previous or the current epoch.

Its weight must be the base reward that the attestation reads for it. -/
private theorem attestation_credit {attestation : Attestation preset fork}
    {parent : Slot} (altair : .altair ≤ fork)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    ∃ (proposer : ValidatorIndex) (credit : ℕ), getBeaconProposerIndex s = .ok proposer ∧
      Ledger s t ∅ ∅ 0 (fun v => if v = proposer then credit else 0) 0 ∧
      ∀ (base : ℕ → ℕ) {count : ℕ}, 2 ^ 64 ≤ count →
        (∀ (index : ValidatorIndex) (total reward : Gwei),
          (isActiveAt s (getPreviousEpoch s) index.toNat = true ∨
            isActiveAt s (getCurrentEpoch s) index.toNat = true) →
          total.toNat = activeBalanceTotal s → getBaseReward s total index = .ok reward →
          reward.toNat = base index.toNat) →
        credit * ((WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
            PROPOSER_WEIGHT.toNat) + recentFlagSum s altair base count ≤
          recentFlagSum t altair base count := by
  have registry := (processAttestation_registry computed).1
  simp only [processAttestation, altair, ↓reduceDIte, processAttestationAltair, bind_ok_iff,
    ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, recent, _, slotEpoch, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _,
    total, totalOk, attesters, attestersOk, ⟨updated, numerator⟩, folded, proposer, proposerOk,
    raised, raisedOk, final⟩ := computed
  -- From Gloas the last write records payment weights, which no balance or flag reads.
  obtain ⟨payments, rfl⟩ : ∃ payments, t = { raised with builderPendingPayments := payments } := by
    split at final
    · exact ⟨_, recordPaymentWeight_eq final⟩
    · cases final
      exact ⟨_, rfl⟩
  rw [getBeaconProposerIndex_setEpochParticipation] at proposerOk
  have denominator : ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT).toNat = 448 := by decide
  have denominatorNat : (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) *
      WEIGHT_DENOMINATOR.toNat / PROPOSER_WEIGHT.toNat = 448 := by decide
  refine ⟨proposer, (numerator /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat,
    proposerOk, ?_, fun base count big reads => ?_⟩
  · have kept : (setEpochParticipation s
        (attestation.data.target.epoch == getCurrentEpoch s) updated).balances = s.balances := by
      unfold setEpochParticipation
      split <;> rfl
    have sizes := (sameSizes_increaseBalance raisedOk).2
    rw [kept] at sizes
    refine Ledger.of_rise (by rw [registry]) fun v => ?_
    cases found : s.balances.data[v.toNat]? with
    | none =>
      have missing : raised.balances.data[v.toNat]? = none := by
        rw [Array.getElem?_eq_none_iff] at found ⊢
        omega
      simp [actualBalanceAt, found, missing]
    | some balance =>
      obtain ⟨final, finalFound, finalValue⟩ :=
        balance_increaseBalance raisedOk (j := v.toNat) (by rw [kept]; exact found)
      have same : proposer.toNat = v.toNat ↔ v = proposer :=
        ⟨fun h => (UInt64.toNat_inj.mp h).symm, fun h => h ▸ rfl⟩
      simp only [actualBalanceAt, found, finalFound, Option.map_some, Option.getD_some,
        finalValue]
      by_cases equal : v = proposer <;> simp [equal, same]
  rw [UInt64.toNat_div, denominator, denominatorNat]
  -- Each attester is inside the range and reads its weight as its base reward.
  have facts : ∀ attester ∈ attesters, attester.toNat < count ∧
      ∀ reward, getBaseReward s total attester = .ok reward →
        reward.toNat ≤ base attester.toNat := by
    intro attester member
    refine ⟨Nat.lt_of_lt_of_le attester.toNat_lt big, fun reward rewardOk => Nat.le_of_eq ?_⟩
    have active := isActiveAt_of_getAttestingIndices attestersOk member
    rw [← slotEpoch] at active
    refine reads attester total reward ?_ (getTotalActiveBalance_toNat totalOk) rewardOk
    rcases recent with previous | current
    · exact .inl (previous ▸ active)
    · exact .inr (current ▸ active)
  have more := flagSumOf_foldlM_addAttesterFlags facts folded
  -- The balance step keeps both lists of flags.
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  simp only [UInt64.toNat_zero, Nat.zero_add] at more
  unfold recentFlagSum setEpochParticipation
  split
  · rename_i current
    simp only [current, ↓reduceIte] at more
    dsimp only [BeaconState.putBalance]
    omega
  · rename_i current
    simp only [current, Bool.false_eq_true, ↓reduceIte] at more
    dsimp only [BeaconState.putBalance]
    omega

end Grow

/-! ### Steps that keep the proposer, the active validators and the base rewards -/

section Kept

variable {fork : Fork} {s u t : BeaconState preset fork}

/-- A step that keeps the inputs of the proposer draw, activity and effective balances. -/
structure Kept (s t : BeaconState preset fork) : Prop where
  frame : Frame s t
  inputs : PayloadInputs s t
  keeps : StepKeeps s t
  effective : EffectiveKept s t
  lifecycle : RegistryLifecycle s t
  lives : Lives s t

private theorem Kept.refl (s : BeaconState preset fork) : Kept s s :=
  ⟨Frame.refl s, PayloadInputs.refl s, StepKeeps.refl s, effectiveKept_refl s, .refl s,
    Lives.refl s⟩

private theorem Kept.trans (one : Kept s u) (two : Kept u t) : Kept s t :=
  ⟨one.frame.trans two.frame, one.inputs.trans two.inputs, one.keeps.trans two.keeps,
    effectiveKept_trans one.effective two.effective one.keeps.1,
    one.lifecycle.trans two.lifecycle,
    one.lives.trans two.lives one.lifecycle (.of_frame two.frame)⟩

/-- A step that keeps the slot, activity up to the fixed epoch and effective balances. -/
structure Steady (s t : BeaconState preset fork) : Prop where
  keeps : StepKeeps s t
  effective : EffectiveKept s t

private theorem Steady.trans (one : Steady s u) (two : Steady u t) : Steady s t :=
  ⟨one.keeps.trans two.keeps, effectiveKept_trans one.effective two.effective one.keeps.1⟩

private theorem Kept.steady (kept : Kept s t) : Steady s t := ⟨kept.keeps, kept.effective⟩

/-- The effective balances below the old registry size, read as options. -/
private theorem Steady.effective_map (kept : Steady s t) (j : ℕ)
    (inside : j < s.validators.data.size) :
    (s.validators.data[j]?).map (·.effectiveBalance) =
      (t.validators.data[j]?).map (·.effectiveBalance) := by
  have same := kept.effective j inside
  have later : j < t.validators.data.size := Nat.lt_of_lt_of_le inside kept.keeps.1
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem later,
    Option.map_some, Option.getD_some] at same ⊢
  exact congrArg some (UInt64.toNat_inj.mp same.symm)

/-- A steady step keeps the epochs. -/
theorem Steady.epoch (kept : Steady s t) : getCurrentEpoch t = getCurrentEpoch s := by
  simp only [getCurrentEpoch, kept.keeps.2.1]

/-- A steady step keeps the total active balance. -/
private theorem Steady.activeBalanceTotal (kept : Steady s t) :
    activeBalanceTotal t = activeBalanceTotal s :=
  activeBalanceTotal_eq kept.epoch kept.keeps.2.2 kept.effective kept.keeps.1

/-- A steady step keeps the read of the total active balance, with its errors. -/
private theorem Steady.total (kept : Steady s t) :
    getTotalActiveBalance t = getTotalActiveBalance s :=
  DirectSafety.total_active_congr
    (kept.keeps.2.2.mono (getCurrentEpoch_le_activityFixedEpoch s)) kept.epoch kept.effective

/-- The base rewards that a kept step reads at the active validators.

These validators are active in the previous or the current epoch. -/
def Reads (s : BeaconState preset fork) (base : ℕ → ℕ) : Prop :=
  ∀ (index : ValidatorIndex) (total reward : Gwei),
    (isActiveAt s (getPreviousEpoch s) index.toNat = true ∨
      isActiveAt s (getCurrentEpoch s) index.toNat = true) →
    total.toNat = activeBalanceTotal s → getBaseReward s total index = .ok reward →
    reward.toNat = base index.toNat

/-- A recent validator is in the registry. -/
theorem lt_size_of_isActiveAt_recent {a : BeaconState preset fork} {i : ℕ}
    (recent : isActiveAt a (getPreviousEpoch a) i = true ∨
      isActiveAt a (getCurrentEpoch a) i = true) : i < a.validators.data.size := by
  rcases recent with active | active <;>
  · unfold isActiveAt at active
    cases found : a.validators.data[i]? with
    | none => simp [found] at active
    | some _ => exact (Array.getElem?_eq_some_iff.mp found).1

private theorem Steady.reads (kept : Steady s t) {base : ℕ → ℕ} (reads : Reads s base) :
    Reads t base := by
  intro index total reward recent totalOk rewardOk
  have previous : getPreviousEpoch t = getPreviousEpoch s := by
    unfold getPreviousEpoch; rw [kept.epoch]
  have fixed := getCurrentEpoch_le_activityFixedEpoch s
  have previousLe : getPreviousEpoch s ≤ activityFixedEpoch s := by
    exact UInt64.le_trans (getPreviousEpoch_le s) fixed
  rw [previous, kept.epoch, kept.keeps.2.2 _ previousLe, kept.keeps.2.2 _ fixed] at recent
  have inside := lt_size_of_isActiveAt_recent recent
  rw [kept.activeBalanceTotal] at totalOk
  rw [← getBaseReward_congr inside (kept.effective_map _ inside)] at rewardOk
  exact reads index total reward recent totalOk rewardOk

private theorem Kept.reads (kept : Kept s t) {base : ℕ → ℕ} (reads : Reads s base) :
    Reads t base := kept.steady.reads reads

/-- A kept step keeps the proposer of the slot. -/
private theorem Kept.proposer (kept : Kept s t) :
    getBeaconProposerIndex t = getBeaconProposerIndex s :=
  getBeaconProposerIndex_of_kept kept.keeps kept.inputs kept.effective

end Kept

section KeptSteps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem Kept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Kept a b) {items : List α}
    (computed : items.foldlM step s = .ok t) : Kept s t :=
  foldlM_ok_invariant (Kept s) (fun _ _ _ before ok => before.trans (each _ _ _ ok))
    (Kept.refl s) computed

private theorem kept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) : Kept s t :=
  ⟨(frame_processProposerSlashing computed).toFrame, payloadInputs_processProposerSlashing computed,
    stepKeeps_processProposerSlashing computed, effectiveKept_proposerSlashing computed,
    registryLifecycle_processProposerSlashing computed, lives_processProposerSlashing computed⟩

private theorem kept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) : Kept s t :=
  ⟨(frame_processAttesterSlashing computed).toFrame,
    payloadInputs_processAttesterSlashing computed, stepKeeps_processAttesterSlashing computed,
    effectiveKept_attesterSlashing computed, registryLifecycle_processAttesterSlashing computed,
    lives_processAttesterSlashing computed⟩

private theorem kept_processAttestation {attestation : Attestation preset fork} {parent : Slot}
    (computed : processAttestation config checks s parent attestation = .ok t) : Kept s t :=
  ⟨frame_processAttestation computed, payloadInputs_processAttestation computed,
    stepKeeps_processAttestation computed,
    effectiveKept_data (by rw [(processAttestation_registry computed).1]),
    registryLifecycle_processAttestation computed,
    Lives.of_data (by rw [(processAttestation_registry computed).1])⟩

private theorem kept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork) (computed : processDeposit config checks before s deposit = .ok t) :
    Kept s t :=
  ⟨(frame_processDeposit computed).toFrame, payloadInputs_processDeposit computed,
    stepKeeps_processDeposit computed, effectiveKept_processDeposit computed,
    registryLifecycle_processDeposit computed, lives_processDeposit electra computed⟩

private theorem kept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Kept s t :=
  ⟨(frame_processVoluntaryExit computed).toFrame, payloadInputsLaws.processVoluntaryExit computed,
    stepKeeps_processVoluntaryExit computed, effectiveKept_voluntaryExit computed,
    registryLifecycle_processVoluntaryExit computed, lives_processVoluntaryExit computed⟩

private theorem kept_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) : Kept s t := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    exact Kept.foldlM (fun _ _ _ ok => ⟨(frame_processBlsToExecutionChange ok).toFrame,
      payloadInputsLaws.processBlsToExecutionChange ok, stepKeeps_processBlsToExecutionChange ok,
      effectiveKept_blsChange ok, registryLifecycle_processBlsToExecutionChange ok,
      (by obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
          exact Lives.setValidator found set ⟨rfl, fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩)⟩)
      computed
  · cases computed; exact Kept.refl _

private theorem kept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) : Kept s t :=
  ⟨(frame_processExecutionRequests computed).toFrame,
    payloadInputs_processExecutionRequests computed, stepKeeps_processExecutionRequests computed,
    effectiveKept_requests computed, registryLifecycle_processExecutionRequests computed,
    lives_processExecutionRequests computed⟩

end KeptSteps

/-! ### The operations of a block -/

/-- The divisor of the proposer reward of an attestation, `(64 - 8) * 64 / 8 = 448`. -/
abbrev proposerDenominator : ℕ :=
  (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
    PROPOSER_WEIGHT.toNat

/-- What some operations of a block do to the balances.

- The credits other than sync go to the proposer of the slot, from attestations and slashings.
- Before Electra, they also go to the recipients of deposits.
- The slashed validators were not slashed before, and pay their initial penalty.
- The proposer reward of the attestations is bounded by the flags they set. -/
structure Credited {fork : Fork} (o t : BeaconState preset fork)
    (proposer : ValidatorIndex) (credit : ℕ) (slashed conv : Finset ValidatorIndex)
    (other slash : ValidatorIndex → ℕ) : Prop where
  ledger : Ledger o t ∅ conv 0 other slash
  kept : Kept o t
  grow : FlagKeeps o t
  read : 0 < credit ∨ slashed.Nonempty → getBeaconProposerIndex o = .ok proposer
  -- The credits other than sync go to the proposer of the slot, from attestations and slashings.
  --
  -- Before Electra, they also go to the recipients of deposits.
  credited : ∀ v, other v ≤ if v = proposer then
    credit + ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0
  -- The slashed validators pay their initial penalty.
  penalized : ∀ v, slash v ≤ if v ∈ slashed then effectiveAt ⟨fork, t⟩ v.toNat /
    (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
  -- The slashed validators were not slashed before.
  newly : ∀ v ∈ slashed, (∀ validator, o.validators.data[v.toNat]? = some validator →
      validator.slashed = false) ∧
    ∃ later, t.validators.data[v.toNat]? = some later ∧ later.slashed = true
  -- The proposer reward of the attestations is bounded by the flags they set.
  potential : ∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count →
    Reads o base → (∀ i, o.validators.data.size ≤ i → base i = 0) →
    credit * proposerDenominator + recentFlagSum o altair base count ≤
      recentFlagSum t altair base count
  eligible : ∀ v ∈ slashed, ∃ old, o.validators.data[v.toNat]? = some old ∧
    Eligible (getCurrentEpoch o) old

section Credited

variable {fork : Fork} {o u t : BeaconState preset fork}

/-- A kept step that moves no balance credits nothing. -/
private theorem Credited.of_ledger (ledger : Ledger o t ∅ ∅ 0 0 0) (kept : Kept o t)
    (grow : FlagKeeps o t) : Credited o t 0 0 ∅ ∅ 0 0 where
  ledger := ledger
  kept := kept
  grow := grow
  read hyp := by simp at hyp
  credited v := by simp
  penalized v := by simp
  newly v member := absurd member (Finset.notMem_empty v)
  potential altair base count _ _ support := by
    simpa using recentFlagSum_mono_below grow altair base count support
  eligible v member := absurd member (Finset.notMem_empty v)

/-- An effective balance at a later kept state is the one before, for an existing validator. -/
private theorem effectiveAt_of_kept (kept : Kept u t) {v : ValidatorIndex} {validator : Validator}
    (found : u.validators.data[v.toNat]? = some validator) :
    effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, u⟩ v.toNat :=
  kept.effective v.toNat (Array.getElem?_eq_some_iff.mp found).1

private theorem Credited.trans {proposer proposer' : ValidatorIndex} {credit credit' : ℕ}
    {slashed slashed' conv conv' : Finset ValidatorIndex}
    {other other' slash slash' : ValidatorIndex → ℕ}
    (one : Credited o u proposer credit slashed conv other slash)
    (two : Credited u t proposer' credit' slashed' conv' other' slash') :
    Credited o t (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer)
      (credit + credit') (slashed ∪ slashed') (conv ∪ conv')
      (other + other') (slash + slash') := by
  -- No validator is slashed in both parts.
  have apart : ∀ v ∈ slashed, v ∉ slashed' := by
    intro v first second
    obtain ⟨later, found, marked⟩ := (one.newly v first).2
    rw [(two.newly v second).1 later found] at marked
    cases marked
  have disjoint : Disjoint slashed slashed' := Finset.disjoint_left.mpr apart
  -- The effective balance of a validator slashed in the first part stays to the end.
  have kept : ∀ v ∈ slashed, effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, u⟩ v.toNat := by
    intro v member
    obtain ⟨later, found, _⟩ := (one.newly v member).2
    exact effectiveAt_of_kept two.kept found
  have sumKept : ∑ x ∈ slashed, effectiveAt ⟨fork, u⟩ x.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
      ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Finset.sum_congr rfl fun x member => by rw [kept x member]
  have proposerSame : getBeaconProposerIndex u = getBeaconProposerIndex o := one.kept.proposer
  refine ⟨by simpa using one.ledger.trans two.ledger, one.kept.trans two.kept,
    one.grow.trans two.grow, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro positive
    split
    · rename_i later
      exact proposerSame ▸ two.read later
    · rename_i none
      have zero : credit' = 0 ∧ slashed' = ∅ := by
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at none
        exact none
      apply one.read
      rcases positive with positive | nonempty
      · left; omega
      · right; rw [zero.2, Finset.union_empty] at nonempty; exact nonempty
  · -- Each part credits the proposer of the whole, or nothing.
    have moved {x c : ℕ} {q : ValidatorIndex} (v : ValidatorIndex)
        (bound : x ≤ if v = q then c else 0)
        (same : c = 0 ∨ q = (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer)) :
        x ≤ if v = (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer) then c
          else 0 := by
      rcases same with zero | same
      · subst zero; split at bound <;> simp_all
      · rw [← same]; exact bound
    intro v
    have first := one.credited v
    have second := two.credited v
    rw [sumKept] at first
    have first' := moved v first (by
      by_cases earlier : 0 < credit ∨ slashed.Nonempty
      · right
        split
        · rename_i later
          have := one.read earlier
          rw [← proposerSame, two.read later] at this
          exact (Except.ok.inj this).symm
        · rfl
      · left
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at earlier
        simp [earlier.1, earlier.2])
    have second' := moved v second (by
      by_cases later : 0 < credit' ∨ slashed'.Nonempty
      · right; simp only [later, ↓reduceIte]
      · left
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at later
        simp [later.1, later.2])
    simp only [Pi.add_apply]
    rw [Finset.sum_union disjoint]
    have total := Nat.add_le_add first' second'
    generalize (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer) = chosen at total ⊢
    by_cases same : v = chosen
    · simp only [same, ↓reduceIte] at total ⊢; omega
    · simp only [same, ↓reduceIte] at total ⊢; omega
  · intro v
    simp only [Pi.add_apply]
    have first := one.penalized v
    have second := two.penalized v
    by_cases member : v ∈ slashed
    · have notSecond := apart v member
      simp only [member, notSecond, ↓reduceIte, Finset.mem_union, true_or] at first second ⊢
      rw [kept v member]
      omega
    · by_cases member' : v ∈ slashed'
      · simp only [member, member', ↓reduceIte, Finset.mem_union, or_true] at first second ⊢
        omega
      · simp only [member, member', ↓reduceIte, Finset.mem_union, or_self] at first second ⊢
        omega
  · intro v member
    rcases Finset.mem_union.mp member with first | second
    · obtain ⟨unslashed, later, found, marked⟩ := one.newly v first
      obtain ⟨final, finalFound, -⟩ :=
        (two.kept.frame.registryGrows) |> fun _ => (⟨later, found, marked⟩ :
          ∃ later, u.validators.data[v.toNat]? = some later ∧ later.slashed = true)
      have inside : v.toNat < t.validators.data.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 two.kept.frame.registryGrows
      refine ⟨unslashed, t.validators.data[v.toNat], Array.getElem?_eq_getElem inside, ?_⟩
      exact two.kept.frame.slashed v.toNat later _ found (Array.getElem?_eq_getElem inside) marked
    · refine ⟨fun validator found => ?_, (two.newly v second).2⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have middle : v.toNat < u.validators.data.size :=
        Nat.lt_of_lt_of_le inside one.kept.frame.registryGrows
      have unslashed := (two.newly v second).1 _ (Array.getElem?_eq_getElem middle)
      cases flag : validator.slashed
      · rfl
      · have := one.kept.frame.slashed v.toNat validator _ found
          (Array.getElem?_eq_getElem middle) flag
        rw [unslashed] at this
        cases this
  · intro altair base count big reads support
    have first := one.potential altair base count big reads support
    have second := two.potential altair base count big (one.kept.reads reads) fun i outside =>
      support i (Nat.le_trans one.kept.frame.registryGrows outside)
    rw [Nat.add_mul]
    omega
  · intro v member
    rcases Finset.mem_union.mp member with first | second
    · exact one.eligible v first
    · obtain ⟨w, found, eligible⟩ := two.eligible v second
      have epoch : getCurrentEpoch u = getCurrentEpoch o := by
        simp only [getCurrentEpoch, one.kept.inputs.slot]
      rw [epoch] at eligible
      exact one.kept.lives.back one.kept.lifecycle (.of_frame one.kept.frame) found eligible

/-- A fold of steps that each credit like operations, and convert nothing, does so too. -/
private theorem Credited.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, BalancesMatch a → step a x = .ok b →
      ∃ p c sl o sh, Credited a b p c sl ∅ o sh)
    {items : List α} (matched : BalancesMatch o) (computed : items.foldlM step o = .ok t) :
    ∃ p c sl o' sh, Credited o t p c sl ∅ o' sh := by
  refine foldlM_ok_invariant (fun b => ∃ p c sl o' sh, Credited o b p c sl ∅ o' sh)
    (fun a x b ⟨_, _, _, _, _, before⟩ ok => ?_)
    ⟨0, 0, ∅, 0, 0, Credited.of_ledger (Ledger.refl o) (Kept.refl o) (FlagKeeps.refl o)⟩
    computed
  obtain ⟨_, _, _, _, _, next⟩ := each a x b (before.kept.frame.balancesMatch matched) ok
  have joined := before.trans next
  rw [Finset.empty_union] at joined
  exact ⟨_, _, _, _, _, joined⟩

end Credited

section CreditedSteps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem effectiveAt_eq_of_found {validator : Validator}
    (found : s.validators.data[i]? = some validator) :
    effectiveAt ⟨fork, s⟩ i = validator.effectiveBalance.toNat := by
  simp [effectiveAt, found]

private theorem credited_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh := by
  obtain ⟨proposer, slashed, validator, read, found, unslashed, ⟨later, laterFound, marked⟩,
    ledger, eligible⟩ := ledger_processProposerSlashing computed
  have kept := kept_processProposerSlashing computed
  have grow := FlagKeeps.of_flags kept.frame.registryGrows (flags_proposerSlashing computed)
  have effective : effectiveAt ⟨fork, t⟩ slashed.toNat = validator.effectiveBalance.toNat :=
    (effectiveAt_of_kept kept found).trans (effectiveAt_eq_of_found found)
  refine ⟨proposer, 0, {slashed}, _, _, ledger, kept, grow, fun _ => read,
    fun v => ?_, fun v => ?_, fun v member => ?_, fun altair base count _ _ support => ?_,
    fun v member => ?_⟩
  · simp only [Finset.sum_singleton, effective, zero_add]; exact le_rfl
  · by_cases same : v = slashed
    · subst same; simp [effective]
    · simp [same]
  · rw [Finset.mem_singleton.mp member]
    exact ⟨fun other found' => by rw [found] at found'; cases found'; exact unslashed,
      later, laterFound, marked⟩
  · simpa using recentFlagSum_mono_below grow altair base count support
  · rw [Finset.mem_singleton.mp member]
    exact ⟨validator, found, eligible⟩

private theorem credited_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh := by
  obtain ⟨proposer, slashed, read, newly, eligibles, ledger⟩ :=
    ledger_processAttesterSlashing computed
  have kept := kept_processAttesterSlashing computed
  have grow := FlagKeeps.of_flags kept.frame.registryGrows (flags_attesterSlashing computed)
  have effective : ∀ v ∈ slashed, effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, s⟩ v.toNat :=
    fun v member => by
      obtain ⟨validator, _, found, _⟩ := newly v member
      exact effectiveAt_of_kept kept found
  refine ⟨proposer, 0, slashed, _, _, ledger, kept, grow,
    fun hyp => read (by simpa using hyp), fun v => ?_, fun v => ?_, fun v member => ?_,
    fun altair base count _ _ support => ?_, eligibles⟩
  · have same : ∑ x ∈ slashed, effectiveAt ⟨fork, s⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun x member => by rw [effective x member]
    simp only [same, zero_add]; exact le_rfl
  · split
    · rename_i member; rw [effective v member]
    · exact le_rfl
  · obtain ⟨validator, later, found, unslashed, laterFound, marked⟩ := newly v member
    exact ⟨fun other found' => by rw [found] at found'; cases found'; exact unslashed,
      later, laterFound, marked⟩
  · simpa using recentFlagSum_mono_below grow altair base count support

private theorem credited_processAttestation {attestation : Attestation preset fork}
    {parent : Slot} (altair : .altair ≤ fork)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh := by
  obtain ⟨proposer, credit, read, ledger, potential⟩ := attestation_credit altair computed
  exact ⟨proposer, credit, ∅, _, _, ledger, kept_processAttestation computed,
    flagKeeps_processAttestation computed, fun _ => read,
    fun v => by simp, fun v => by simp, fun v member => absurd member (Finset.notMem_empty v),
    fun _ base count big reads _ => potential base big reads,
    fun v member => absurd member (Finset.notMem_empty v)⟩

private theorem credited_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (computed : processDeposit config checks before s deposit = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh :=
  ⟨_, _, _, _, _, Credited.of_ledger (ledger_processDeposit electra matched computed)
    (kept_processDeposit electra computed)
    (FlagKeeps.of_below (frame_processDeposit computed).registryGrows
      (flagsBelow_deposit computed))⟩

private theorem credited_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh :=
  ⟨_, _, _, _, _, Credited.of_ledger (ledger_processVoluntaryExit computed)
    (kept_processVoluntaryExit computed) (growsLaws.processVoluntaryExit computed)⟩

private theorem credited_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh :=
  ⟨_, _, _, _, _, Credited.of_ledger (ledger_processBlsToExecutionChanges computed)
    (kept_processBlsToExecutionChanges computed)
    (by
      unfold processBlsToExecutionChanges at computed
      split at computed
      · rw [← Array.foldlM_toList] at computed
        exact (growsLaws.foldlM (fun _ _ _ ok => growsLaws.processBlsToExecutionChange ok)
          computed)
      · cases computed
        exact FlagKeeps.refl _)⟩

private theorem credited_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) :
    ∃ conv, Credited s t 0 0 ∅ conv 0 0 ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  obtain ⟨conv, ledger, count⟩ := ledger_processExecutionRequests computed
  have grow := FlagKeeps.of_flags (frame_processExecutionRequests computed).registryGrows
    (flags_processExecutionRequests computed)
  exact ⟨conv, ⟨ledger, kept_processExecutionRequests computed, grow, fun hyp => by simp at hyp,
    fun v => by simp, fun v => by simp, fun v member => absurd member (Finset.notMem_empty v),
    fun altair base count _ _ support => by
      simpa using recentFlagSum_mono_below grow altair base count support,
    fun v member => absurd member (Finset.notMem_empty v)⟩, count⟩

/-- Credits that join: the first part converts no validator. -/
private theorem credited_join {x y : BeaconState preset fork}
    {p c sl o sh p' c' sl' cv' o' sh'}
    (one : Credited s x p c sl ∅ o sh) (two : Credited x y p' c' sl' cv' o' sh') :
    ∃ p c sl o sh, Credited s y p c sl cv' o sh := by
  have joined := one.trans two
  rw [Finset.empty_union] at joined
  exact ⟨_, _, _, _, _, joined⟩

/-- From Fulu and before Heze, the operations before the requests credit like operations.

They convert no validator. -/
private theorem credited_operationsPrefix {body : BeaconBlockBody preset fork} {parent : Slot}
    {before : fork < .hegota}
    {proposed attested voted deposited exited changed : BeaconState preset fork}
    (fulu : .fusaka ≤ fork) (matched : BalancesMatch s)
    (proposersOk : body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) s = .ok proposed)
    (attestersOk : body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposed = .ok attested)
    (attestationsOk : body.attestations.data.toList.foldlM
      (processAttestation config checks · parent ·) attested = .ok voted)
    (depositsOk : (body.deposits before).data.toList.foldlM
      (processDeposit config checks before) voted = .ok deposited)
    (exitsOk : body.voluntaryExits.data.toList.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited)
    (changesOk : processBlsToExecutionChanges config checks exited body = .ok changed) :
    ∃ p c sl o sh, Credited s changed p c sl ∅ o sh := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
  have matchedAt {x : BeaconState preset fork} {p c sl o sh}
      (held : Credited s x p c sl ∅ o sh) : BalancesMatch x :=
    held.kept.frame.balancesMatch matched
  obtain ⟨_, _, _, _, _, one⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processProposerSlashing ok) matched proposersOk
  obtain ⟨_, _, _, _, _, two⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processAttesterSlashing ok) (matchedAt one) attestersOk
  obtain ⟨_, _, _, _, _, upTwo⟩ := credited_join one two
  obtain ⟨_, _, _, _, _, three⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processAttestation altair ok) (matchedAt upTwo)
    attestationsOk
  obtain ⟨_, _, _, _, _, upThree⟩ := credited_join upTwo three
  obtain ⟨_, _, _, _, _, four⟩ := Credited.foldlM
    (fun _ _ _ held ok => credited_processDeposit electra held ok) (matchedAt upThree) depositsOk
  obtain ⟨_, _, _, _, _, upFour⟩ := credited_join upThree four
  obtain ⟨_, _, _, _, _, five⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processVoluntaryExit ok) (matchedAt upFour) exitsOk
  obtain ⟨_, _, _, _, _, upFive⟩ := credited_join upFour five
  obtain ⟨_, _, _, _, _, six⟩ := credited_processBlsToExecutionChanges changesOk
  exact credited_join upFive six

/-- From Fulu, the operations of a block credit like operations.

Before Gloas they convert no more validators than a payload can carry consolidation requests.

From Gloas they carry no request, and convert no validator. -/
private theorem credited_processOperations {body : BeaconBlockBody preset fork} {parent : Slot}
    (fulu : .fusaka ≤ fork) (matched : BalancesMatch s)
    (computed : processOperations config checks s body parent = .ok t) :
    ∃ p c sl cv o sh, Credited s t p c sl cv o sh ∧
      cv.card ≤ if .glamsterdam ≤ fork then 0
        else preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) fulu
  have matchedAt {x : BeaconState preset fork} {p c sl o sh}
      (held : Credited s x p c sl ∅ o sh) : BalancesMatch x :=
    held.kept.frame.balancesMatch matched
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestationsOk, exited, exitsOk, changed, changesOk, paidOk⟩ := computed
    obtain ⟨_, _, _, _, _, one⟩ := Credited.foldlM
      (fun _ _ _ _ ok => credited_processProposerSlashing ok) matched proposersOk
    obtain ⟨_, _, _, _, _, two⟩ := Credited.foldlM
      (fun _ _ _ _ ok => credited_processAttesterSlashing ok) (matchedAt one) attestersOk
    obtain ⟨_, _, _, _, _, upTwo⟩ := credited_join one two
    obtain ⟨_, _, _, _, _, three⟩ := Credited.foldlM
      (fun _ _ _ _ ok => credited_processAttestation altair ok) (matchedAt upTwo) attestationsOk
    obtain ⟨_, _, _, _, _, upThree⟩ := credited_join upTwo three
    obtain ⟨_, _, _, _, _, four⟩ := Credited.foldlM
      (fun _ _ _ _ ok => credited_processVoluntaryExit ok) (matchedAt upThree) exitsOk
    obtain ⟨_, _, _, _, _, upFour⟩ := credited_join upThree four
    -- The changes of credentials run as in a block before Gloas.
    have changes : processBlsToExecutionChanges config checks exited body = .ok changed := by
      unfold processBlsToExecutionChanges
      simp only [capella, ↓reduceDIte, ← Array.foldlM_toList]
      exact changesOk
    obtain ⟨_, _, _, _, _, five⟩ := credited_processBlsToExecutionChanges changes
    obtain ⟨_, _, _, _, _, upFive⟩ := credited_join upFour five
    -- The payload attestations keep the state.
    have same := foldlM_ok_invariant (fun u : BeaconState preset fork => u = changed)
      (fun _ _ _ before ok => (processPayloadAttestation_eq ok).trans before) rfl paidOk
    subst same
    exact ⟨_, _, _, _, _, _, upFive, by simp [gloas]⟩
  rename_i notGloas
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, a, proposersOk, b, attestersOk, c, attestationsOk, d, depositsOk, e,
    exitsOk, f, changesOk, requestsOk⟩ := computed
  simp only [electra, ↓reduceDIte] at requestsOk
  obtain ⟨_, _, _, _, _, upSix⟩ := credited_operationsPrefix fulu matched proposersOk
    attestersOk attestationsOk depositsOk exitsOk changesOk
  obtain ⟨conv, seven, count⟩ := credited_processExecutionRequests requestsOk
  obtain ⟨_, _, _, _, _, upSeven⟩ := credited_join upSix seven
  exact ⟨_, _, _, _, _, _, upSeven, by simpa [notGloas] using count⟩

/-- A block's operations before its consolidation requests keep whether each validator compounds.

This holds from Fulu and before Gloas, from a state whose balances match its validators. -/
theorem compoundingKept_beforeConsolidations {body : BeaconBlockBody preset fork}
    {parent : Slot} {before : fork < .hegota}
    {proposed attested voted deposited exited changed requested withdrawn :
      BeaconState preset fork}
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork) (electra : .pectra ≤ fork)
    (matched : BalancesMatch s)
    (proposedOk : body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) s = .ok proposed)
    (attestedOk : body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposed = .ok attested)
    (votedOk : body.attestations.data.toList.foldlM
      (processAttestation config checks · parent ·) attested = .ok voted)
    (depositedOk : (body.deposits before).data.toList.foldlM
      (processDeposit config checks before) voted = .ok deposited)
    (exitedOk : body.voluntaryExits.data.toList.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited)
    (changedOk : processBlsToExecutionChanges config checks exited body = .ok changed)
    (requestedOk : (body.executionRequests ⟨electra, early⟩).deposits.data.toList.foldlM
      (processDepositRequest · electra ·) changed = .ok requested)
    (withdrawnOk : (body.executionRequests ⟨electra, early⟩).withdrawals.data.toList.foldlM
      (processWithdrawalRequest config · electra ·) requested = .ok withdrawn) :
    ∀ (v : ValidatorIndex) (validator : Validator),
      s.validators.data[v.toNat]? = some validator →
      ∃ later, withdrawn.validators.data[v.toNat]? = some later ∧
        hasCompoundingWithdrawalCredential later =
          hasCompoundingWithdrawalCredential validator := by
  obtain ⟨_, _, _, _, _, ops⟩ := credited_operationsPrefix fulu matched proposedOk
    attestedOk votedOk depositedOk exitedOk changedOk
  have both := ops.ledger.trans
    (ledger_depositWithdrawalRequests (electra := electra) requestedOk withdrawnOk)
  intro v validator located
  exact both.kept v validator (by simp) located

end CreditedSteps

/-- From Fulu, take a validator that stays unslashed through the operations of a block.

The operations keep its balance at least the smaller of two amounts.

They are its balance and its effective balance before the operations. -/
theorem _root_.EthLib.Consensus.processOperations_floor {fork : Fork}
    {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (fulu : .fusaka ≤ fork) (matched : BalancesMatch s)
    (computed : processOperations config checks s body parentSlot = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    -- Its effective balance is within its largest.
    (capped : val.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork val)
    (unslashed : ∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) :
    min (actualBalanceAt ⟨fork, s⟩ v.toNat) val.effectiveBalance.toNat ≤
      actualBalanceAt ⟨fork, t⟩ v.toNat := by
  obtain ⟨_, _, _, conv, _, slash, ops, -⟩ :=
    credited_processOperations fulu matched computed
  -- The validator stays unslashed, so the operations charge it no slashing penalty.
  have noSlash : slash v = 0 := by
    have bound := ops.penalized v
    split at bound
    · rename_i member
      obtain ⟨w, wFound, marked⟩ := (ops.newly v member).2
      rw [unslashed w wFound] at marked
      cases marked
    · omega
  by_cases converted : v ∈ conv
  · -- A conversion to compounding credentials only lowers a balance to the activation balance.
    --
    -- That is the largest effective balance before the conversion.
    --
    -- A converted validator did not compound.
    --
    -- So its effective balance is within the activation balance, where its balance is left.
    have lowered := ops.ledger.lowered v converted (Finset.notMem_empty v)
    have fresh := ops.ledger.fresh v converted val found
    have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
    have cap := UInt64.le_iff_toNat_le.mp capped
    simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance,
      fresh, Bool.false_eq_true] at cap
    simp only [Pi.zero_apply, noSlash] at lowered
    omega
  · have down := ops.ledger.down v (Finset.notMem_empty v) converted
    simp only [Pi.zero_apply, noSlash] at down
    omega

/-! ### One block -/

section Block

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem steady_of_validators (validators : t.validators.data = s.validators.data)
    (slot : t.slot = s.slot) : Steady s t :=
  ⟨StepKeeps.of_validators validators slot, effectiveKept_data validators⟩

private theorem steady_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : Steady s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact steady_of_validators rfl rfl

private theorem steady_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : Steady s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact steady_of_validators rfl rfl

private theorem steady_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : Steady s t :=
  ⟨stepKeeps_processEth1Data computed, effectiveKept_data (by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
    rw [← rest])⟩

private theorem steady_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    Steady s t := by
  refine ⟨stepKeeps_processBlockExecution computed, ?_⟩
  exact effectiveKept_data (congrArg (·.data) (processBlockExecution_validators computed))

private theorem kept_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) : Kept s t :=
  ⟨(frame_processSyncAggregate computed).toFrame, payloadInputsLaws.processSyncAggregate computed,
    stepKeeps_processSyncAggregate computed,
    effectiveKept_data (congrArg (·.data) (processSyncAggregate_kept computed).1),
    .of_data (by rw [(processSyncAggregate_kept computed).1]),
    Lives.of_data (by rw [(processSyncAggregate_kept computed).1])⟩

/-- The balances of a block from Fulu, read at each validator.

- Withdrawals pay at most the preset's `MAX_WITHDRAWALS_PER_PAYLOAD` validators.
- Consolidation requests convert at most `MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD` validators.
- The sync committee pays and charges each member at most its seats times the participant reward.
- The other credits go to the proposer of the slot.
- Deposits credit no balance in the block.
- The slashed validators were not slashed before, and pay their initial penalty.

The other credits are the proposer rewards of attestations and the whistleblower rewards.

They also include the proposer share of the sync aggregate, which no participant amount counts.

From Gloas the consolidation requests run in the payload of the parent, before the header. -/
theorem block_balances {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} (fulu : .fusaka ≤ fork)
    (matched : BalancesMatch s) (computed : processBlock config checks engine s block = .ok t) :
    ∃ (paid conv slashed : Finset ValidatorIndex) (sync other slash : ValidatorIndex → ℕ)
      (proposer : ValidatorIndex) (credit share : ℕ),
      Ledger s t paid conv sync other slash ∧
      -- Withdrawals pay at most the preset's `MAX_WITHDRAWALS_PER_PAYLOAD` validators.
      paid.card ≤ preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat ∧
      -- Consolidation requests convert at most `MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD` validators.
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat ∧
      -- The other credits go to the proposer of the slot.
      --
      -- They are the proposer rewards of attestations and the whistleblower rewards of slashings.
      --
      -- They also include the proposer share of the sync aggregate.
      --
      -- No participant amount counts that share.
      --
      -- From Electra, deposits credit no balance in the block.
      (∀ v, other v ≤ if v = proposer then credit + share +
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) ∧
      -- The slashed validators pay their initial penalty.
      (∀ v, slash v ≤ if v ∈ slashed then effectiveAt ⟨fork, t⟩ v.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) ∧
      -- The slashed validators were not slashed before.
      (∀ v ∈ slashed, (∀ validator, s.validators.data[v.toNat]? = some validator →
          validator.slashed = false) ∧
        ∃ later, t.validators.data[v.toNat]? = some later ∧ later.slashed = true) ∧
      -- The sync committee pays and charges each member a bounded amount.
      --
      -- That amount is at most its seats times the participant reward.
      (∀ altair : .altair ≤ fork, (∀ v, sync v ≤ syncSeats t altair v.toNat * syncRewardAt s) ∧
        share ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (syncRewardAt s * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))) ∧
      SyncRewardRead s ∧
      (∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count → Reads s base →
        (∀ i, s.validators.data.size ≤ i → base i = 0) →
        credit * proposerDenominator + recentFlagSum s altair base count ≤
          recentFlagSum t altair base count) ∧
      Lives s t ∧ RegistryLifecycle s t ∧
      (∀ v ∈ slashed, ∃ old, s.validators.data[v.toNat]? = some old ∧
        Eligible (getCurrentEpoch s) old) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) fulu
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) fulu
  obtain ⟨voted, operated, started, operatedOk, -, synced⟩ := processBlock_operationsInput computed
  simp only [altair, ↓reduceDIte] at synced
  -- The steps before the operations keep both flag lists and form a frame.
  have growVoted : ParticipationKept s voted := flags_operationsInput started
  have frameVoted : Frame s voted := (frame_operationsInput started).toFrame
  obtain ⟨parented, headed, executed, revealed, paidOk, headedOk, executedOk, revealedOk,
    votedOk⟩ := started
  simp only [bellatrix, ↓reduceDIte] at executedOk
  -- From Gloas the payload of the parent runs first, and its requests convert validators.
  obtain ⟨convPre, parentLedger, convPreCount, steadyParent, livesParent, lifeParent⟩ :
      ∃ conv : Finset ValidatorIndex, Ledger s parented ∅ conv 0 0 0 ∧
        conv.card ≤ (if .glamsterdam ≤ fork then
          preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0) ∧
        Steady s parented ∧ Lives s parented ∧ RegistryLifecycle s parented := by
    split at paidOk
    · rename_i gloas
      obtain ⟨conv, ledger, count⟩ := ledger_processParentExecutionPayload paidOk
      have effective := effectiveKept_parentPayload paidOk
      refine ⟨conv, ledger, by simpa [gloas] using count,
        ⟨⟨Nat.le_of_eq effective.2.symm, ?_⟩, effective.1⟩,
        lives_processParentExecutionPayload paidOk, ?_⟩
      · exact processParentExecutionPayload_step_of ActiveStep ActiveStep.refl ActiveStep.trans
          (fun frame validators =>
            ActiveStep.of_validators (congrArg (·.data) validators) frame.slot)
          activeStep_processWithdrawalRequest activeStep_processConsolidationRequest paidOk
      · exact registryLifecycle_processParentExecutionPayload paidOk
    · cases paidOk
      exact ⟨∅, Ledger.refl s, Nat.zero_le _, steady_of_validators rfl rfl, Lives.refl s,
        .refl s⟩
  -- Before Heze the vote on the deposit contract follows the reveal.
  have votedStep : Ledger revealed voted ∅ ∅ 0 0 0 ∧ Steady revealed voted ∧
      voted.validators.data = revealed.validators.data := by
    split at votedOk
    · refine ⟨ledger_processEth1Data votedOk, steady_processEth1Data votedOk, ?_⟩
      obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      rw [← rest]
    · cases votedOk
      exact ⟨Ledger.refl _, steady_of_validators rfl rfl, rfl⟩
  -- The header, the withdrawals and the bid or payload, the reveal and the vote.
  obtain ⟨paid, executedLedger, paidCount⟩ := ledger_processBlockExecution executedOk
  have toVoted : Ledger s voted paid convPre 0 0 0 := by
    simpa only [Finset.empty_union, Finset.union_empty, add_zero] using
      (((parentLedger.zero_right (ledger_processBlockHeader headedOk)).trans
        executedLedger).zero_right (ledger_processRandao revealedOk)).zero_right votedStep.1
  have steadyVoted : Steady s voted :=
    steadyParent.trans <| (steady_processBlockHeader headedOk).trans <|
      (steady_processBlockExecution executedOk).trans <|
        (steady_processRandao revealedOk).trans votedStep.2.1
  have afterParent : voted.validators.data = parented.validators.data := by
    have h1 : headed.validators = parented.validators := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      rfl
    have h2 : executed.validators = headed.validators :=
      processBlockExecution_validators executedOk
    have h3 : revealed.validators = executed.validators := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      rfl
    rw [votedStep.2.2, h3, h2, h1]
  have livesVoted : Lives s voted := livesParent.of_data_right afterParent
  have lifeVoted : RegistryLifecycle s voted :=
    lifeParent.trans (RegistryLifecycle.of_data afterParent)
  -- The operations and the sync aggregate.
  obtain ⟨proposer, credit, slashed, conv, other, slash, ops, convCount⟩ :=
    credited_processOperations fulu (frameVoted.balancesMatch matched) operatedOk
  obtain ⟨proposer', reward, share, sync, rewardOk, read', shareBound, seats, syncLedger⟩ :=
    ledger_processSyncAggregate synced
  have syncKept := kept_processSyncAggregate synced
  have syncGrow := growsLaws.processSyncAggregate synced
  have totalSame : activeBalanceTotal operated = activeBalanceTotal s :=
    (steadyVoted.trans ops.kept.steady).activeBalanceTotal
  obtain ⟨rewardValue, syncRead⟩ := syncRewardRead_of_ok rewardOk
  rw [syncRewardAt, totalSame, ← syncRewardAt] at rewardValue
  -- One proposer earns all the other credits.
  have same : 0 < credit ∨ slashed.Nonempty → 0 < share → proposer' = proposer := by
    intro first second
    have := read' second
    rw [ops.kept.proposer, ops.read first] at this
    exact (Except.ok.inj this).symm
  have effectiveSame : ∀ x ∈ slashed,
      effectiveAt ⟨fork, t⟩ x.toNat = effectiveAt ⟨fork, operated⟩ x.toNat := by
    intro x member
    obtain ⟨later, found, _⟩ := (ops.newly x member).2
    exact effectiveAt_of_kept syncKept found
  refine ⟨paid ∪ ∅ ∪ ∅, convPre ∪ conv ∪ ∅, slashed, 0 + 0 + sync,
    0 + other + fun v => if v = proposer' then share else 0, 0 + slash + 0,
    if 0 < share then proposer' else proposer, credit, share,
    (toVoted.trans ops.ledger).trans syncLedger, by simpa [capella] using paidCount,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Before Gloas the conversions come from the operations.
    -- From Gloas they come from the payload of the parent, which runs first.
    have union := Finset.card_union_le convPre conv
    rw [Finset.union_empty]
    split at convPreCount <;> split at convCount <;> omega
  · intro v
    have first := ops.credited v
    have sumSame : ∑ x ∈ slashed, effectiveAt ⟨fork, operated⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun x member => by rw [effectiveSame x member]
    rw [sumSame] at first
    simp only [Pi.add_apply, zero_add]
    by_cases positive : 0 < share
    · simp only [positive, ↓reduceIte]
      by_cases earlier : 0 < credit ∨ slashed.Nonempty
      · rw [same earlier positive] at *
        split at first <;> split <;> omega
      · simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at earlier
        simp only [earlier.1, earlier.2, Finset.sum_empty, add_zero] at first ⊢
        split at first <;> split <;> omega
    · have zero : share = 0 := by omega
      simp only [zero, ite_self, add_zero]
      split at first <;> split <;> omega
  · intro v
    have := ops.penalized v
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, add_zero]
    split at this
    · rename_i member; rw [ite_eq_left member, effectiveSame v member]; exact this
    · rw [ite_eq_right (by assumption)]; exact this
  · intro v member
    obtain ⟨unslashed, later, found, marked⟩ := ops.newly v member
    refine ⟨fun validator found' => ?_, ?_⟩
    · have inside := (Array.getElem?_eq_some_iff.mp found').1
      have middle : v.toNat < voted.validators.data.size :=
        Nat.lt_of_lt_of_le inside frameVoted.registryGrows
      have clear := unslashed _ (Array.getElem?_eq_getElem middle)
      cases flag : validator.slashed
      · rfl
      · have := frameVoted.slashed v.toNat validator _ found' (Array.getElem?_eq_getElem middle)
          flag
        rw [clear] at this
        cases this
    · have inside : v.toNat < t.validators.data.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 syncKept.frame.registryGrows
      exact ⟨_, Array.getElem?_eq_getElem inside,
        syncKept.frame.slashed v.toNat later _ found (Array.getElem?_eq_getElem inside) marked⟩
  · intro _
    rw [← rewardValue]
    exact ⟨fun v => by simpa using seats v, shareBound⟩
  · obtain ⟨reward', rewardOk'⟩ := syncRead
    exact ⟨reward', (syncParticipantReward_congr
      (steadyVoted.trans ops.kept.steady).total.symm).trans rewardOk'⟩
  · intro altair' base count big reads support
    have votedReads : Reads voted base := steadyVoted.reads reads
    -- The steps before the operations keep both lists of flags, so the potential stays.
    have first : recentFlagSum s altair' base count ≤ recentFlagSum voted altair' base count := by
      unfold recentFlagSum
      rw [growVoted.1, growVoted.2]
    have second := ops.potential altair' base count big votedReads fun i outside =>
      support i (Nat.le_trans frameVoted.registryGrows outside)
    have third := recentFlagSum_mono_below syncGrow altair' base count fun i outside =>
      support i (Nat.le_trans frameVoted.registryGrows
        (Nat.le_trans ops.kept.frame.registryGrows outside))
    omega
  · exact livesVoted.trans
      (ops.kept.lives.trans syncKept.lives ops.kept.lifecycle (.of_frame syncKept.frame))
      lifeVoted (.of_frame (ops.kept.frame.trans syncKept.frame))
  · exact lifeVoted.trans (ops.kept.lifecycle.trans syncKept.lifecycle)
  · intro v member
    obtain ⟨old, found, eligible⟩ := ops.eligible v member
    have epoch : getCurrentEpoch voted = getCurrentEpoch s := by
      simp only [getCurrentEpoch, frameVoted.slot]
    rw [epoch] at eligible
    exact livesVoted.back lifeVoted (.of_frame frameVoted) found eligible

end Block

end BlockCredits

end EthLib.Consensus
