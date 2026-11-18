module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.ChainRoots
public import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance
public import EthLib.Consensus.Proofs.Transition.PendingConsolidations
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.EpochPending

/-!
# Effective-balance changes from the actual balance path

A block operation keeps the effective balance of every validator that existed before it.

A whole block keeps them, at every fork.

Registry updates keep them as well.

Only rewards, slashings and the two pending stages can change the balances.

An effective-balance update never raises the larger of the effective and the actual balance.

Loss uses initial slack, balance debits and rounding; gain uses initial excess and credits.

An epoch's effective-balance update reads its intermediate balance, before later upgrades.

For this reason a slot's balance path includes that intermediate state, not just its endpoints.

A validator admitted along a run starts with an effective balance funded by its own balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The effective balance at a registry position, or zero past the end of the registry. -/
def effectiveAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
  ((s.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0

/-- The balance at a registry position, or zero past the end of the balances. -/
def actualBalanceAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
  ((s.state.balances.data[i]?).map (·.toNat)).getD 0

/-- A balance increase adds its amount at its own index and keeps every other balance. -/
theorem actualBalanceAt_increaseBalance {fork : Fork} {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : increaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j + if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, _, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨raised, located, value⟩ := balance_increaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]

/-- A balance decrease subtracts its amount at its own index and keeps every other balance. -/
theorem actualBalanceAt_decreaseBalance {fork : Fork} {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : decreaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j - if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨lowered, located, value⟩ := balance_decreaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]
    split <;> omega

/-- Appending a balance keeps every balance below and reads the new one at the end. -/
theorem actualBalanceAt_push {fork : Fork} {s t : BeaconState preset fork}
    {balance : Gwei}
    (pushed : t.balances.data = s.balances.data.push balance) (i : ℕ) :
    actualBalanceAt ⟨fork, t⟩ i = if i = s.balances.data.size then balance.toNat
      else actualBalanceAt ⟨fork, s⟩ i := by
  simp only [actualBalanceAt, pushed, Array.getElem?_push]
  split
  · simp
  · rfl

/-- Include the state before fork upgrades, where the effective balance was last updated. -/
def _root_.EthLib.Consensus.Step.balancePath {x y : ForkedBeaconState preset}
    (step : Step config checks x y) :
    List (ForkedBeaconState preset) :=
  match step with
  | .block _ _ _ _ => [x, y]
  | .slot _ => match (advanceSlot config checks x.state).toOption with
    | none => [x, y]
    | some s => [x, ⟨x.fork, s⟩, y]

/-- The balance path of a run joins the paths of its steps. -/
def _root_.EthLib.Consensus.Run.balancePath {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List (ForkedBeaconState preset)
  | _, .nil => [x]
  | _, .snoc pre step => pre.balancePath ++ step.balancePath

/-- A step's balance path starts at its start and ends at its end. -/
theorem Step.balancePath_ends {m n : ForkedBeaconState preset}
    (step : Step config checks m n) :
    step.balancePath.head? = some m ∧ step.balancePath.getLast? = some n := by
  cases step with
  | block => simp [Step.balancePath]
  | slot ok =>
    simp only [Step.balancePath]
    split <;> simp

/-- A run's balance path starts at its start and ends at its end. -/
theorem Run.balancePath_ends {x y : ForkedBeaconState preset}
    (run : Run config checks x y) :
    run.balancePath.head? = some x ∧ run.balancePath.getLast? = some y := by
  induction run with
  | nil => simp [Run.balancePath]
  | snoc pre step ih =>
    have ends := Step.balancePath_ends step
    simp only [Run.balancePath, List.head?_append, List.getLast?_append, ih.1, ends.2]
    simp

/-- The balance path of an appended run.

The second path loses its first state, which is the first path's last. -/
theorem Run.balancePath_append {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (rest : Run config checks m y) :
    (pre.append rest).balancePath = pre.balancePath ++ rest.balancePath.tail := by
  induction rest with
  | nil => simp [Run.append, Run.balancePath]
  | snoc rest step ih =>
    simp only [Run.append, Run.balancePath, ih, List.append_assoc]
    obtain ⟨head, _⟩ := Run.balancePath_ends rest
    cases h : rest.balancePath with
    | nil => simp [h] at head
    | cons a l => simp

/-- A run that extends to a run ending in a step is that whole run, or extends to its prefix. -/
theorem Run.prefix_snoc {x m k n : ForkedBeaconState preset}
    (p : Run config checks x m) (r : Run config checks m n)
    (q : Run config checks x k) (step : Step config checks k n)
    (split : p.append r = q.snoc step) :
    (m = n ∧ HEq p (q.snoc step)) ∨ ∃ r' : Run config checks m k, p.append r' = q := by
  cases r with
  | nil => exact .inl ⟨rfl, heq_of_eq split⟩
  | snoc r' last =>
    simp only [Run.append] at split
    injection split with middle _ prefixEq _
    subst middle
    exact .inr ⟨r', eq_of_heq prefixEq⟩

/-- Two runs with a common extension are ordered: one extends the other. -/
theorem Run.prefix_total_of {x m1 m2 : ForkedBeaconState preset}
    (p1 : Run config checks x m1) (p2 : Run config checks x m2) :
    ∀ {y : ForkedBeaconState preset} (r2 : Run config checks m2 y)
      (r1 : Run config checks m1 y), p1.append r1 = p2.append r2 →
    (∃ r : Run config checks m1 m2, p1.append r = p2) ∨
      ∃ r : Run config checks m2 m1, p2.append r = p1 := by
  intro y r2
  induction r2 with
  | nil => exact fun r1 same => .inl ⟨r1, same⟩
  | snoc r2 last ih =>
    intro r1 same
    simp only [Run.append] at same
    rcases Run.prefix_snoc p1 r1 (p2.append r2) last same with ⟨rfl, joined⟩ | ⟨r', earlier⟩
    · exact .inr ⟨r2.snoc last, (eq_of_heq joined).symm⟩
    · exact ih r' earlier

/-- Two splits of one run are ordered. -/
theorem Run.prefix_total {x m1 m2 y : ForkedBeaconState preset}
    {tail : Run config checks x y}
    (p1 : Run config checks x m1) (r1 : Run config checks m1 y)
    (p2 : Run config checks x m2) (r2 : Run config checks m2 y)
    (one : p1.append r1 = tail) (two : p2.append r2 = tail) :
    (∃ r : Run config checks m1 m2, p1.append r = p2) ∨
      ∃ r : Run config checks m2 m1, p2.append r = p1 :=
  Run.prefix_total_of p1 p2 r2 r1 (one.trans two.symm)

/-- A run's balance path is a list that ends at the end of the run. -/
theorem Run.balancePath_last {x y : ForkedBeaconState preset}
    (run : Run config checks x y) : ∃ pre, run.balancePath = pre ++ [y] :=
  List.getLast?_eq_some_iff.mp (Run.balancePath_ends run).2

/-- A run's balance path is a list that starts at the start of the run. -/
theorem Run.balancePath_head {x y : ForkedBeaconState preset}
    (run : Run config checks x y) : ∃ rest, run.balancePath = x :: rest :=
  List.head?_eq_some_iff.mp (Run.balancePath_ends run).1

/-- The balance increases at one position between consecutive states of a path. -/
def pathCredits (i : Nat) : List (ForkedBeaconState preset) → Nat
  | x :: y :: rest => (actualBalanceAt y i - actualBalanceAt x i) + pathCredits i (y :: rest)
  | _ => 0

/-- The balance decreases at one position between consecutive states of a path. -/
def pathDebits (i : Nat) : List (ForkedBeaconState preset) → Nat
  | x :: y :: rest => (actualBalanceAt x i - actualBalanceAt y i) + pathDebits i (y :: rest)
  | _ => 0

/-- The ordering of the effective-balance caps that the departure bound assumes. -/
structure CapOrder (preset : Preset) : Prop where
  activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE
  compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA

/-- The mainnet preset orders its effective-balance caps. -/
theorem CapOrder.mainnet : CapOrder Preset.mainnet := ⟨by decide, by decide⟩

/-- The minimal preset orders its effective-balance caps. -/
theorem CapOrder.minimal : CapOrder Preset.minimal := ⟨by decide, by decide⟩

/-- The activation balance is at most the largest effective balance before Electra.

With the cap order, the two are equal, as the upgrade to Electra needs. -/
def ActivationWithinMaxEffective (preset : Preset) : Prop :=
  preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE

/-- The mainnet preset activates within the largest effective balance before Electra. -/
theorem ActivationWithinMaxEffective.mainnet : ActivationWithinMaxEffective Preset.mainnet := by
  unfold ActivationWithinMaxEffective
  decide

/-- The minimal preset activates within the largest effective balance before Electra. -/
theorem ActivationWithinMaxEffective.minimal : ActivationWithinMaxEffective Preset.minimal := by
  unfold ActivationWithinMaxEffective
  decide

/-- The cap order and an activation within the largest balance make the two balances equal. -/
theorem CapOrder.maxEffective_eq (caps : CapOrder preset)
    (activation : ActivationWithinMaxEffective preset) :
    preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE :=
  UInt64.le_antisymm caps.activation activation

/-- Each validator of the first state keeps its effective balance in the second. -/
def EffectiveKept {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop :=
  ∀ i, i < s.validators.data.size → effectiveAt ⟨h, t⟩ i = effectiveAt ⟨f, s⟩ i

theorem effectiveKept_refl {f : Fork} (s : BeaconState preset f) : EffectiveKept s s :=
  fun _ _ => rfl

theorem effectiveKept_trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : EffectiveKept s t) (two : EffectiveKept t u)
    (grows : s.validators.data.size ≤ t.validators.data.size) : EffectiveKept s u :=
  fun i inside => (two i (Nat.lt_of_lt_of_le inside grows)).trans (one i inside)

namespace DirectSafety

/-- Two states with the same active validators and effective balances have the same total.

The second state is in the same epoch and keeps the activity of that epoch.

It also keeps the effective balance of every validator of the first state. -/
theorem total_active_congr {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (before : f < .glamsterdam) (after : h < .glamsterdam)
    (active : ActiveKept (getCurrentEpoch s) s t) (epoch : getCurrentEpoch t = getCurrentEpoch s)
    (effective : ∀ i, i < s.validators.data.size →
      effectiveAt ⟨h, t⟩ i = effectiveAt ⟨f, s⟩ i) :
    getTotalActiveBalance t = getTotalActiveBalance s := by
  classical
  let indices := getActiveValidatorIndices s (getCurrentEpoch s)
  have checked := active.getActiveValidatorIndicesChecked_eq (UInt64.le_refl _)
  have inside (i : ValidatorIndex) (member : i ∈ indices) : i.toNat < s.validators.data.size := by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (s.validators.bound before)).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have targetIndices := active.getActiveValidatorIndices_eq (UInt64.le_refl _)
  have targetInside (i : ValidatorIndex) (member : i ∈ indices) :
      i.toNat < t.validators.data.size := by
    change i ∈ getActiveValidatorIndices s (getCurrentEpoch s) at member
    rw [← targetIndices] at member
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (t.validators.bound after)).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have sum : Models.stake (fun i => balanceAt t i.toNat) indices.toFinset =
      Models.stake (fun i => balanceAt s i.toNat) indices.toFinset := by
    apply Finset.sum_congr rfl
    intro i member
    exact effective i.toNat (inside i (List.mem_toFinset.mp member))
  have sourceNone : indices.find? (s.validators.data.size ≤ ·.toNat) = none := by
    apply List.find?_eq_none.mpr
    intro i member
    have bound := inside i member
    simp only [decide_eq_true_eq]
    omega
  have targetNone : indices.find? (t.validators.data.size ≤ ·.toNat) = none := by
    apply List.find?_eq_none.mpr
    intro i member
    have bound := targetInside i member
    simp only [decide_eq_true_eq]
    omega
  unfold getTotalActiveBalance
  rw [epoch, checked, getActiveValidatorIndicesChecked_of_within
    (state := s) (s.validators.bound before)]
  simp only [bind, Except.bind]
  change getTotalBalance t indices = getTotalBalance s indices
  simp only [getTotalBalance, sourceNone, targetNone, sumMarked_markIndices_eq_stake, sum]

end DirectSafety

theorem effectiveKept_data {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data := by rfl) :
    EffectiveKept s t := by
  intro i _
  simp only [effectiveAt, same]

private theorem effectiveKept_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {index : Nat} {old v : Validator} (found : getValidatorAt s index = .ok old)
    (set : s.setValidatorAt index v = .ok t)
    (same : v.effectiveBalance = old.effectiveBalance) : EffectiveKept s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have read : s.validators.data[index]? = some old := by
    simpa [getValidatorAt, inside] using found
  intro i _
  by_cases eq : i = index
  · subst i
    simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      read, same]
  · simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Ne.symm eq]

theorem effectiveKept_setValidator {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} {old v : Validator} (found : getValidator s index = .ok old)
    (set : s.setValidator index v = .ok t)
    (same : v.effectiveBalance = old.effectiveBalance) : EffectiveKept s t :=
  effectiveKept_setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) same

private theorem effectiveKept_increase {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (ok : increaseBalance s index amount = .ok t) : EffectiveKept s t :=
  effectiveKept_data (congrArg (·.data) (increaseBalance_validators ok))

theorem effectiveKept_decrease {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (ok : decreaseBalance s index amount = .ok t) : EffectiveKept s t :=
  effectiveKept_data (congrArg (·.data) (decreaseBalance_validators ok))

theorem effectiveKept_exit {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} (ok : initiateValidatorExit config s index = .ok t) :
    EffectiveKept s t := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact effectiveKept_refl _
  · have same := (exitQueue_validators queue).1
    exact effectiveKept_trans (effectiveKept_data (congrArg (·.data) same))
      (effectiveKept_setValidator (old := v)
        (by rw [getValidator_of_validators_eq same]; exact found) set rfl)
      (Nat.le_of_eq (by rw [same]))

theorem effectiveKept_slash {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) : EffectiveKept s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := effectiveKept_trans (effectiveKept_exit exited)
    (effectiveKept_setValidator found set rfl) (frame_initiateValidatorExit exited).registryGrows
  have second := effectiveKept_trans (effectiveKept_decrease lowered)
    (effectiveKept_trans (effectiveKept_increase raised) (effectiveKept_increase paid)
      (frame_increaseBalance raised).registryGrows) (frame_decreaseBalance lowered).registryGrows
  have middle := effectiveKept_trans (effectiveKept_data (s := marked)
    (t := { marked with slashings })) second (Nat.le_refl _)
  have total := effectiveKept_trans first middle
    (Nat.le_trans (frame_initiateValidatorExit exited).registryGrows
      (Nat.le_of_eq (sameSizes_setValidator set).1.symm))
  split <;> exact total

theorem effectiveKept_fold {f : Fork} {s t : BeaconState preset f}
    {α ε : Type} {step : BeaconState preset f → α → Except ε _} {xs : List α}
    (kept : ∀ a b c, step a b = .ok c → EffectiveKept a c)
    (grows : ∀ a b c, step a b = .ok c → a.validators.data.size ≤ c.validators.data.size)
    (ok : xs.foldlM step s = .ok t) : EffectiveKept s t := by
  have result := foldlM_ok_invariant
    (fun t => EffectiveKept s t ∧ s.validators.data.size ≤ t.validators.data.size)
    (fun a b c previous computed =>
      ⟨effectiveKept_trans previous.1 (kept a b c computed) previous.2,
        Nat.le_trans previous.2 (grows a b c computed)⟩)
    ⟨effectiveKept_refl s, Nat.le_refl _⟩ ok
  exact result.1

private theorem effectiveKept_add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) : EffectiveKept s t := by
  intro i inside
  simp [effectiveAt, addValidatorToRegistry_validators_eq_push ok, Array.getElem?_push,
    Nat.ne_of_lt inside]

private theorem effectiveKept_deposit {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) : EffectiveKept s t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact effectiveKept_refl _
  · exact effectiveKept_increase raised
  · exact effectiveKept_add added

private theorem effectiveKept_applyDeposit {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (ok : applyDeposit config checks s key credentials amount signature = .ok t) :
    EffectiveKept s t := by
  rcases applyDeposit_cases ok with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, ok⟩
  · exact effectiveKept_refl _
  · exact effectiveKept_refl _
  · exact effectiveKept_trans (effectiveKept_add added) (effectiveKept_data rfl)
      (by rw [addValidatorToRegistry_validators_eq_push added]; simp)
  · exact effectiveKept_deposit ok

theorem effectiveKept_processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : EffectiveKept s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact effectiveKept_trans (effectiveKept_data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next }))
    (effectiveKept_applyDeposit credited) (Nat.le_refl _)

theorem effectiveKept_registryElectra {f : Fork} {s t : BeaconState preset f}
    {epoch : Epoch} {index : Nat}
    (ok : updateRegistryEntryElectra config epoch s index = .ok t) : EffectiveKept s t := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact effectiveKept_setValidatorAt found set rfl
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact effectiveKept_exit exited
  split at ok
  · exact effectiveKept_setValidatorAt found (liftAccessor_ok.mp ok) rfl
  · cases ok; exact effectiveKept_refl _

/-- Registry updates keep the effective balance of every validator. -/
theorem effectiveKept_registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : EffectiveKept s t := by
  intro i inside
  obtain ⟨_, found, _, same, _⟩ :=
    (processRegistryUpdates_kept ok).1 i _ (Array.getElem?_eq_getElem inside)
  simp [effectiveAt, found, same, Array.getElem?_eq_getElem inside]

private theorem effectiveKept_excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : EffectiveKept s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact effectiveKept_refl _
  · cases ok; exact effectiveKept_refl _

private theorem effectiveKept_compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : EffectiveKept s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact effectiveKept_trans (effectiveKept_setValidator found set rfl)
    (effectiveKept_excess queued) (Nat.le_of_eq (sameSizes_setValidator set).1.symm)

private theorem effectiveKept_consolidate {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    EffectiveKept s t := by
  obtain ⟨_, _, _, _, _, _, _, set, _, rfl⟩ := queueConsolidation_steps ok
  have kept := effectiveKept_trans (effectiveKept_setValidator (old := source)
    (by exact getValidator_eq_ok_iff.mpr found) set rfl) (effectiveKept_data rfl)
    (Nat.le_of_eq (sameSizes_setValidator set).1.symm)
  exact kept

theorem effectiveKept_consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : EffectiveKept s t := by
  rcases consolidationRequest_cases ok with rfl | ⟨_, _, _, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact effectiveKept_refl _
  · exact effectiveKept_compounding switched
  · exact effectiveKept_consolidate accepted.sourceAt queued

private theorem effectiveKept_partial {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    EffectiveKept s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact effectiveKept_data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact effectiveKept_refl _

theorem effectiveKept_withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : EffectiveKept s t := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · exact effectiveKept_refl _
  · exact effectiveKept_exit exited
  · exact effectiveKept_partial withdrawn

theorem effectiveKept_depositRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : EffectiveKept s t := by
  obtain ⟨-, -, -, _, _, rfl⟩ := processDepositRequest_ok ok
  exact effectiveKept_refl _

theorem effectiveKept_requests {f : Fork} {s t : BeaconState preset f}
    {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (ok : processExecutionRequests config s body electra = .ok t) : EffectiveKept s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  have first := effectiveKept_fold (fun _ _ _ => effectiveKept_depositRequest)
    (fun _ _ _ ok => (registryLifecycle_processDepositRequest ok).size_le) deposits
  have grows := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processDepositRequest ok) deposits
  have second := effectiveKept_fold (fun _ _ _ => effectiveKept_withdrawalRequest)
    (fun _ _ _ ok => (registryLifecycle_processWithdrawalRequest ok).size_le) withdrawals
  have grows' := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok) withdrawals
  exact effectiveKept_trans first (effectiveKept_trans second
    (effectiveKept_fold (fun _ _ _ => effectiveKept_consolidationRequest)
      (fun _ _ _ ok => (registryLifecycle_processConsolidationRequest ok).size_le) consolidations)
    grows'.size_le) grows.size_le

theorem effectiveKept_proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : EffectiveKept s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact effectiveKept_slash slashed

theorem effectiveKept_attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : EffectiveKept s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  have result := foldlM_ok_invariant
    (fun step => EffectiveKept s step.1 ∧ s.validators.data.size ≤ step.1.validators.data.size)
    (fun step _ next before ok => ?_)
    (show EffectiveKept s (s, false).1 ∧ s.validators.data.size ≤ (s, false).1.validators.data.size
      from ⟨effectiveKept_refl _, Nat.le_refl _⟩) folded
  · exact result.1
  · obtain ⟨middle, slashedAny⟩ := step
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, slashed, rfl⟩ := ok
      exact ⟨effectiveKept_trans before.1 (effectiveKept_slash slashed) before.2,
        Nat.le_trans before.2 (frame_slashValidator slashed).registryGrows⟩
    · cases ok; exact before

theorem effectiveKept_voluntaryExit {f : Fork} {s t : BeaconState preset f}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : EffectiveKept s t :=
  effectiveKept_exit (processVoluntaryExit_initiates ok)

theorem effectiveKept_blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : EffectiveKept s t := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact effectiveKept_setValidator found set rfl

/-- A block keeps the effective balance of every existing validator, at every fork.

From Gloas the payload of the parent runs first, and its requests keep these balances too. -/
theorem effectiveKept_processBlock {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (ok : processBlock config checks engine s block = .ok t) : EffectiveKept s t := by
  -- Composing two steps needs the registry growth of the first.
  let Kept (a b : BeaconState preset f) : Prop :=
    EffectiveKept a b ∧ a.validators.data.size ≤ b.validators.data.size
  have refl (a : BeaconState preset f) : Kept a a := ⟨effectiveKept_refl a, Nat.le_refl _⟩
  have trans {a b c : BeaconState preset f} (one : Kept a b) (two : Kept b c) : Kept a c :=
    ⟨effectiveKept_trans one.1 two.1 one.2, Nat.le_trans one.2 two.2⟩
  have same {a b : BeaconState preset f} (validators : b.validators = a.validators) : Kept a b :=
    ⟨effectiveKept_data (congrArg (·.data) validators),
      Nat.le_of_eq (congrArg (·.data.size) validators).symm⟩
  have folds {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      (each : ∀ a x b, step a x = .ok b → Kept a b) {items : List α}
      {a b : BeaconState preset f} (computed : items.foldlM step a = .ok b) : Kept a b :=
    foldlM_ok_invariant (Kept a) (fun _ _ _ before stepped => trans before (each _ _ _ stepped))
      (refl a) computed
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : Kept s input :=
    started.step_of Kept refl trans
      (fun _ paid => processParentExecutionPayload_step_of Kept refl trans
        (fun _ validators => same validators)
        (fun requested => ⟨effectiveKept_withdrawalRequest requested,
          (registryLifecycle_processWithdrawalRequest requested).size_le⟩)
        (fun requested => ⟨effectiveKept_consolidationRequest requested,
          (registryLifecycle_processConsolidationRequest requested).size_le⟩) paid)
      (fun headed => by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
        exact same rfl)
      (fun _ executed => same (processBlockExecution_validators executed))
      (fun revealed => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        exact same rfl)
      (fun _ voted => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        rw [← rest]
        exact same rfl)
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of Kept refl trans
      (fun deposited => ⟨effectiveKept_processDeposit deposited,
        (frame_processDeposit deposited).registryGrows⟩)
      (fun exited => ⟨effectiveKept_voluntaryExit exited,
        (frame_processVoluntaryExit exited).registryGrows⟩)
      (fun changed => ⟨effectiveKept_blsChange changed,
        (frame_processBlsToExecutionChange changed).registryGrows⟩)
      (fun requested => ⟨effectiveKept_requests requested,
        (registryLifecycle_processExecutionRequests requested).size_le⟩)
      (fun attested => same (by rw [processPayloadAttestation_eq attested])) operated
  have tail : Kept last t := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact same rfl
    · cases synced
      exact refl _
  exact (trans head <| trans (folds (fun _ _ _ slashed => ⟨effectiveKept_proposerSlashing slashed,
      (frame_processProposerSlashing slashed).registryGrows⟩) proposersOk) <|
    trans (folds (fun _ _ _ slashed => ⟨effectiveKept_attesterSlashing slashed,
      (frame_processAttesterSlashing slashed).registryGrows⟩) slashingsOk) <|
    trans (folds (fun _ _ _ attested => ⟨effectiveKept_data
        (by rw [(processAttestation_registry attested).1]),
      (frame_processAttestation attested).registryGrows⟩) attestedOk) <|
    trans rest tail).1

/-- The stages after the effective-balance update keep the validators and the balances. -/
theorem balanceDrift_late {f : Fork} {s t : BeaconState preset f}
    (trace : EpochTrace (EpochStage.action config checks)
      [.slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow] s t) :
    t.validators = s.validators ∧ t.balances = s.balances := by
  refine EpochTrace.transport
    (R := fun a b : BeaconState preset f => b.validators = a.validators ∧ b.balances = a.balances)
    (fun _ => ⟨rfl, rfl⟩) (fun one two => ⟨two.1.trans one.1, two.2.trans one.2⟩) ?_ trace
  intro k member a b computed
  have edge := EpochStage.action_cases.mp computed
  cases k
  case rewards | registry | slashings | pendingDeposits | pendingConsolidations
    | effectiveBalances => simp at member
  all_goals
    have kept := edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    exact ⟨kept.1, kept.2.1⟩

/-! ## The bands of hysteresis at the start of an epoch -/

section Epochs

variable {fork : Fork} {state after : BeaconState preset fork}

/-- Right after the epoch transition, each effective balance lies within the bands of its balance.

The update of the effective balances puts them there.

The later stages of the epoch keep the validators and the balances.

The increment must be positive and at most the upward band. -/
private theorem hysteresis_of_epochTransition (bands : preset.IncrementWithinUpwardBand)
    (computed : processEpoch config checks state = .ok after) : Hysteresis after := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ((EpochStage.prefixStages ++ [.payments]) ++
    [.effectiveBalances, .slashingsReset, .randaoReset, .history, .participation,
      .syncCommittees, .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨_, -, tail⟩ := EpochTrace.append_iff.mp trace
  cases tail
  rename_i updated tail
  have last := balanceDrift_late tail
  exact (processEffectiveBalanceUpdates_hysteresis bands
    (EpochStage.action_cases.mp updated)).of_data (congrArg (·.data) last.1)
    (congrArg (·.data) last.2) fun _ => rfl

/-- A slot step that reaches the first slot of an epoch ends within the bands of hysteresis. -/
theorem hysteresis_of_advanceSlot (bands : preset.IncrementWithinUpwardBand)
    (computed : advanceSlot config checks state = .ok after)
    (boundary : after.slot % preset.SLOTS_PER_EPOCH = 0) : Hysteresis after := by
  obtain ⟨next, cached, epoched, -, -, epochOk, rfl⟩ := advanceSlot_ok computed
  simp only [epochIfLast, show next % preset.SLOTS_PER_EPOCH = 0 from boundary, ↓reduceIte]
    at epochOk
  exact (hysteresis_of_epochTransition bands epochOk).of_data rfl rfl fun _ => rfl

/-- The state at the first slot of an epoch, reached by slot steps, is within the bands. -/
theorem hysteresis_of_processSlots (bands : preset.IncrementWithinUpwardBand)
    {slot : Slot} (computed : processSlots config checks state slot = .ok after)
    (boundary : slot % preset.SLOTS_PER_EPOCH = 0) : Hysteresis after := by
  obtain ⟨later, reached⟩ := processSlots_slot computed
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  have gap := UInt64.lt_iff_toNat_lt.mp later
  obtain ⟨count, counted⟩ : ∃ count, slot.toNat - state.slot.toNat = count + 1 :=
    ⟨slot.toNat - state.slot.toNat - 1, by omega⟩
  rw [counted] at advanced
  -- The last of the slot steps reaches the slot.
  clear counted gap later
  induction count generalizing state with
  | zero =>
    obtain ⟨_, first, rest⟩ := bind_ok_iff.mp advanced
    cases rest
    exact hysteresis_of_advanceSlot bands first (by rw [reached]; exact boundary)
  | succ count ih =>
    obtain ⟨_, first, rest⟩ := bind_ok_iff.mp advanced
    exact ih rest

end Epochs

/-- An effective-balance update cannot increase the funding held at any registry position. -/
private theorem updateEffectiveBalance_funding {fork : Fork} {s t : BeaconState preset fork}
    {index : Nat} (ok : updateEffectiveBalance s index = .ok t) (i : Nat) :
    max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, balance, read, effective, updated, set⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have old : s.validators.data[index]? = some validator := by
    simpa [getValidatorAt, inside] using found
  by_cases same : i = index
  · subst i
    have actual : actualBalanceAt ⟨fork, s⟩ index = balance.toNat := by
      simp [actualBalanceAt, getBalanceAt_eq_ok_iff.mp read]
    have bound := updatedEffectiveBalance_le_max updated
    simpa [effectiveAt, actualBalanceAt, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, old, ← actual] using
      (Nat.max_le.mpr ⟨bound, Nat.le_max_right validator.effectiveBalance.toNat balance.toNat⟩)
  · simp [effectiveAt, actualBalanceAt, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, Ne.symm same]

/-- The full effective-balance pass cannot mint funding, including at inactive positions. -/
theorem processEffectiveBalanceUpdates_max_le {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : Nat) :
    max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) := by
  unfold processEffectiveBalanceUpdates at ok
  exact foldlM_ok_invariant
    (fun t => max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i))
    (fun _ _ _ previous step => Nat.le_trans (updateEffectiveBalance_funding step i) previous)
    (Nat.le_refl _) ok

/-- A block keeps the effective balance of every existing validator.

The fork bound is not needed. -/
theorem effectiveKept_block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (_early : f < .glamsterdam) (ok : processBlock config checks engine s block = .ok t) :
    EffectiveKept s t :=
  effectiveKept_processBlock ok

private theorem effectiveKept_pendingDeposits {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f}
    (ok : processPendingDeposits config checks s electra = .ok t) : EffectiveKept s t := by
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → EffectiveKept state result.1.state := fun ok =>
    -- The registry only grows, which the transitivity of `EffectiveKept` needs.
    (passPendingDeposits_of
      (fun s t => EffectiveKept s t ∧ s.validators.data.size ≤ t.validators.data.size)
      (fun _ => ⟨effectiveKept_refl _, Nat.le_refl _⟩)
      (fun one two => ⟨effectiveKept_trans one.1 two.1 one.2, Nat.le_trans one.2 two.2⟩)
      (fun credited => ⟨effectiveKept_deposit credited,
        (registryLifecycle_applyPendingDeposit credited).size_le⟩) ok).1
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals
    intro i inside
    exact pass ‹_› i inside

/-- The epoch stages before payments keep every existing validator's effective balance. -/
theorem effectiveKept_epochBeforePayments
    {fork : Fork} {s t : BeaconState preset fork}
    (ok : epochBeforePayments config checks s = .ok t) : EffectiveKept s t := by
  rw [epochBeforePayments_eq_run] at ok
  have head := EpochTrace.run_ok_iff.mp ok
  have kept : EffectiveKept s t ∧ s.validators.data.size ≤ t.validators.data.size := by
    refine head.transport
      (fun a b => EffectiveKept a b ∧ a.validators.data.size ≤ b.validators.data.size)
      (fun a => ⟨effectiveKept_refl a, Nat.le_refl _⟩)
      (fun one two => ⟨effectiveKept_trans one.1 two.1 one.2, Nat.le_trans one.2 two.2⟩) ?_
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    cases k
    case registry =>
      exact ⟨effectiveKept_registry edge, (registryLifecycle_processRegistryUpdates edge).size_le⟩
    case pendingDeposits =>
      simp only [EpochStage.Edge] at edge
      split at edge
      · exact ⟨effectiveKept_pendingDeposits edge,
          (registryLifecycle_processPendingDeposits edge).size_le⟩
      · exact edge ▸ ⟨effectiveKept_refl _, Nat.le_refl _⟩
    case effectiveBalances => simp [EpochStage.prefixStages] at member
    all_goals
      have same := edge.validators_eq ⟨nofun, nofun, nofun⟩
      exact ⟨effectiveKept_data (congrArg (·.data) same),
        Nat.le_of_eq (congrArg (·.data.size) same).symm⟩
  exact kept.1

/-- An epoch stage keeps the balances, unless it is one of six stages.

Those are rewards, registry updates, slashings, the two pending stages and effective balances. -/
theorem EpochStage.Edge.balances_eq {f : Fork} {stage : EpochStage}
    {s t : BeaconState preset f} (edge : EpochStage.Edge config checks stage s t)
    (other : stage ≠ .rewards ∧ stage ≠ .registry ∧ stage ≠ .slashings ∧
      stage ≠ .pendingDeposits ∧ stage ≠ .pendingConsolidations ∧ stage ≠ .effectiveBalances) :
    t.balances = s.balances :=
  (edge.records other).2.1

/-- An epoch keeps every existing effective balance until its effective-balance update.

Before it, registry updates and pending deposits keep existing effective balances.

The other stages before it keep the validators.

The stages after it keep the validators and the balances. -/
theorem balanceDrift_epoch {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) :
    ∃ before after, EffectiveKept s before ∧
      processEffectiveBalanceUpdates before = .ok after ∧
      t.validators = after.validators ∧ t.balances = before.balances := by
  have trace := processEpoch_trace ok
  change EpochTrace _ ((EpochStage.prefixStages ++ [.payments]) ++
    [.effectiveBalances, .slashingsReset, .randaoReset, .history, .participation,
      .syncCommittees, .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨before, head, tail⟩ := EpochTrace.append_iff.mp trace
  have kept : EffectiveKept s before ∧
      s.validators.data.size ≤ before.validators.data.size := by
    refine head.transport
      (fun a b => EffectiveKept a b ∧ a.validators.data.size ≤ b.validators.data.size)
      (fun a => ⟨effectiveKept_refl a, Nat.le_refl _⟩)
      (fun one two => ⟨effectiveKept_trans one.1 two.1 one.2, Nat.le_trans one.2 two.2⟩) ?_
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    cases k
    case registry =>
      exact ⟨effectiveKept_registry edge, (registryLifecycle_processRegistryUpdates edge).size_le⟩
    case pendingDeposits =>
      simp only [EpochStage.Edge] at edge
      split at edge
      · exact ⟨effectiveKept_pendingDeposits edge,
          (registryLifecycle_processPendingDeposits edge).size_le⟩
      · exact edge ▸ ⟨effectiveKept_refl _, Nat.le_refl _⟩
    case effectiveBalances => simp [EpochStage.prefixStages] at member
    all_goals
      have same := edge.validators_eq ⟨nofun, nofun, nofun⟩
      exact ⟨effectiveKept_data (congrArg (·.data) same),
        Nat.le_of_eq (congrArg (·.data.size) same).symm⟩
  cases tail
  rename_i after updated tail
  have last := balanceDrift_late tail
  have updated := EpochStage.action_cases.mp updated
  exact ⟨before, after, kept.1, updated, last.1,
    last.2.trans (processEffectiveBalanceUpdates_balances updated)⟩

private theorem balanceDrift_update_upper {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : Nat) :
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i) (actualBalanceAt ⟨f, s⟩ i) := by
  have result := foldlM_ok_invariant
    (fun t => t.balances = s.balances ∧
      effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i) (actualBalanceAt ⟨f, s⟩ i))
    (fun a index b previous step => ?_)
    ⟨rfl, Nat.le_max_left _ _⟩ ok
  · exact result.2
  · simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨old, found, balance, read, next, updated, set⟩ := step
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
    refine ⟨previous.1, ?_⟩
    have found' := getValidatorAt_eq_ok_iff.mp found
    have read' := getBalanceAt_eq_ok_iff.mp read
    by_cases eq : i = index
    · subst i
      have bound := updatedEffectiveBalance_le_max updated
      have funded : balance.toNat = actualBalanceAt ⟨f, s⟩ index := by
        simp only [actualBalanceAt, ← previous.1, read', Option.map_some, Option.getD_some]
      have oldBound := previous.2
      simp only [effectiveAt, found', Option.map_some, Option.getD_some] at oldBound
      simp only [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set_self, Option.map_some, Option.getD_some]
      rw [funded] at bound
      omega
    · simpa [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq] using previous.2

theorem balanceDrift_slot_upper {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t)
    (i : Nat) (inside : i < s.validators.data.size) :
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i) (actualBalanceAt ⟨f, t⟩ i) := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch advance
    have bound := balanceDrift_update_upper updated i
    have same := kept i inside
    rw [same] at bound
    simpa only [effectiveAt, actualBalanceAt, validators, balances] using bound
  · cases advance
    exact Nat.le_max_left _ _

private theorem balanceDrift_upgrade_upper {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) (i : Nat) :
    effectiveAt t.val i ≤ effectiveAt s i := by
  have reset {f : Fork} {a b : BeaconState preset f} {electra : .pectra ≤ f}
      {index : ValidatorIndex} (ok : queuePreActivation a electra index = .ok b) :
      effectiveAt ⟨f, b⟩ i ≤ effectiveAt ⟨f, a⟩ i := by
    simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok balance
    obtain ⟨inside, rfl⟩ := setValidator_ok validator
    by_cases eq : i = index.toNat
    · subst i
      simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
    · simp [effectiveAt, BeaconState.putValidator, BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq]
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [effectiveAt, (upgradeToAltair_spec upgraded).1, Nat.le_refl]
  · subst ok; exact Nat.le_refl _
  · subst ok; exact Nat.le_refl _
  · subst ok; exact Nat.le_refl _
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    have one := foldlM_ok_invariant
      (fun t => effectiveAt ⟨.pectra, t⟩ i ≤ effectiveAt ⟨.dencun, state⟩ i)
      (fun _ _ _ previous ok => (reset ok).trans previous) (Nat.le_refl _) queued
    refine foldlM_ok_invariant
      (fun t => effectiveAt ⟨.pectra, t⟩ i ≤ effectiveAt ⟨.dencun, state⟩ i)
      (fun a index b previous ok => ?_) one compounded
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · have step := liftAccessor_ok.mp ok
        simp only [queueExcessActiveBalance, bind_ok_iff] at step
        obtain ⟨_, _, step⟩ := step
        split at step
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
          obtain ⟨_, _, _, _, _, set, rfl⟩ := step
          obtain ⟨_, rfl⟩ := setBalance_ok set
          exact previous
        · cases step; exact previous
      · cases ok; exact previous
    · cases ok; exact previous
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [effectiveAt, (upgradeToFulu_spec upgraded).1, Nat.le_refl]
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

theorem balanceDrift_upgrades_upper {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam) (i : Nat) :
    effectiveAt t i ≤ effectiveAt s i := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact (ih next rest early).trans (balanceDrift_upgrade_upper nextOk
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early) i)
  | case2 s notDue => cases ok; exact Nat.le_refl _

/-- A slot inside one epoch only caches the slot.

It runs no epoch transition and no upgrade, so it keeps the fork. -/
theorem advanceSlotAcross_of_same_epoch {middle last : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks middle = .ok last)
    (same : getCurrentEpoch last.state = getCurrentEpoch middle.state) :
    ∃ (cached : BeaconState preset middle.fork) (next : Slot),
      processSlot middle.state = .ok cached ∧
        last = ⟨middle.fork, { cached with slot := next }⟩ := by
  obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
  have epoch : getCurrentEpoch next = getCurrentEpoch middle.state := by
    have slot : last.state.slot = next.slot := processUpgrades_induction
      (property := fun t => t.state.slot = next.slot)
      (fun prior ok => (upgradeFrame_upgradeNext ok).slot.trans prior) rfl upgraded
    have eq : getCurrentEpoch last.state = getCurrentEpoch next := by
      simp only [getCurrentEpoch, slot]
    exact eq.symm.trans same
  obtain ⟨slot, cached, epoched, sum, cachedOk, epochOk, rfl⟩ := advanceSlot_ok advanced
  have notFirst : slot % preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro firstSlot
    have rem : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat firstSlot
    have eq := congrArg UInt64.toNat epoch
    simp only [getCurrentEpoch_toNat] at eq
    have divide := Nat.mod_add_div slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have before := Nat.mod_add_div middle.state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [eq] at divide
    omega
  rw [processUpgrades_of_not_due (upgradeDue_of_not_first notFirst)] at upgraded
  cases upgraded
  simp only [epochIfLast, ite_eq_right notFirst, pure, Except.pure, Except.ok.injEq] at epochOk
  subst epoched
  exact ⟨cached, slot, cachedOk, rfl⟩

/-- Induct over a run inside one epoch, with the run so far.

Inside one epoch no slot crosses an epoch boundary.

So a slot step only runs `processSlot` and sets the slot.

Before Gloas, a block step is one `applySignedBlock` call. -/
theorem Run.induction_of_same_epoch {x : ForkedBeaconState preset}
    (motive : (z : ForkedBeaconState preset) → Run config checks x z → Prop)
    (start : motive x .nil)
    (blockStep : ∀ {f : Fork} {s t : BeaconState preset f} (engine : ExecutionEngine preset f)
      (signed : SignedBeaconBlock preset f) (due : upgradeDue config ⟨f, s⟩ = false)
      (ok : applySignedBlock config checks engine s signed true = .ok t)
      (pre : Run config checks x ⟨f, s⟩), f < .glamsterdam → motive ⟨f, s⟩ pre →
        motive ⟨f, t⟩ (pre.snoc (.block engine signed due ok)))
    (slotStep : ∀ {middle last : ForkedBeaconState preset} {cached : BeaconState preset middle.fork}
      {next : Slot} (pre : Run config checks x middle)
      (ok : advanceSlotAcross config checks middle = .ok last),
      last = ⟨middle.fork, { cached with slot := next }⟩ →
      processSlot middle.state = .ok cached →
      getCurrentEpoch ({ cached with slot := next } : BeaconState preset middle.fork) =
        getCurrentEpoch middle.state → motive middle pre →
      motive last (pre.snoc (.slot ok)))
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    motive y tail := by
  induction tail with
  | nil => exact start
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have midEpoch : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
      UInt64.le_antisymm (same ▸ step.chainStep.currentEpoch_le)
        (currentEpoch_le_of_chainSteps pre.chainSteps)
    have prior := ih middleEarly midEpoch
    cases step with
    | block engine signed due ok => exact blockStep engine signed due ok pre early prior
    | slot ok =>
      have kept := same.trans midEpoch.symm
      obtain ⟨cached, next, cachedOk, lastEq⟩ := advanceSlotAcross_of_same_epoch ok kept
      rw [lastEq] at kept
      exact slotStep pre ok lastEq cachedOk kept prior

/-- Within one epoch before Gloas, each existing index keeps its effective balance. -/
theorem Run.effectiveKept_of_same_epoch {x y : ForkedBeaconState preset}
    (_tail : Run config checks x y) (_early : y.fork < .glamsterdam)
    (_same : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    EffectiveKept x.state y.state :=
  Run.induction_of_same_epoch (fun z _ => EffectiveKept x.state z.state) (effectiveKept_refl _)
    (fun _ _ _ ok pre early prior =>
      effectiveKept_trans prior (effectiveKept_block early (applySignedBlock_ok ok).2.1)
        pre.registryLifecycle.size_le)
    (fun _ _ lastEq cachedOk _ prior => by
      subst lastEq
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      exact prior)
    _tail _early _same

/-- Within one epoch before Electra, an existing index cannot gain effective balance. -/
theorem Run.effectiveAt_le_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .pectra)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    (i : Nat) (present : i < x.state.validators.data.size) :
    effectiveAt y i ≤ effectiveAt x i :=
  Nat.le_of_eq (tail.effectiveKept_of_same_epoch (Nat.lt_trans early (by decide)) same i present)

private theorem balanceDrift_credits_append (i : Nat) (a b : List (ForkedBeaconState preset))
    (x : ForkedBeaconState preset) :
    pathCredits i (a ++ x :: b) = pathCredits i (a ++ [x]) + pathCredits i (x :: b) := by
  induction a with
  | nil => simp [pathCredits]
  | cons first rest ih =>
    cases rest with
    | nil => simp [pathCredits]
    | cons second rest => simpa [pathCredits, Nat.add_assoc] using ih

private theorem balanceDrift_gain {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    max (effectiveAt y i) (actualBalanceAt y i) ≤
      max (effectiveAt x i) (actualBalanceAt x i) + pathCredits i tail.balancePath := by
  induction tail with
  | nil => simp [Run.balancePath, pathCredits]
  | @snoc middle last pre step ih =>
    have forkLe := step.chainStep.fork_le
    have middleEarly := Nat.lt_of_le_of_lt forkLe early
    have bound := ih middleEarly
    have inside := Nat.lt_of_lt_of_le present pre.registryLifecycle.size_le
    obtain ⟨initial, path⟩ := Run.balancePath_last pre
    cases step with
    | @block fork before after engine signed due ok =>
      have kept := effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i inside
      have credits : pathCredits i (pre.snoc (.block engine signed due ok)).balancePath =
          pathCredits i pre.balancePath +
            (actualBalanceAt ⟨fork, after⟩ i - actualBalanceAt ⟨fork, before⟩ i) := by
        simp only [Run.balancePath, Step.balancePath, path, List.append_assoc]
        simp only [List.cons_append, List.nil_append]
        rw [balanceDrift_credits_append]
        simp [pathCredits]
      rw [credits, kept]
      dsimp only at *
      omega
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have update := balanceDrift_slot_upper advanced i inside
      change effectiveAt ⟨middle.fork, next⟩ i ≤
        max (effectiveAt middle i) (actualBalanceAt ⟨middle.fork, next⟩ i) at update
      have upgrade := balanceDrift_upgrades_upper upgraded early i
      have credits : pathCredits i (pre.snoc (.slot ok)).balancePath =
          pathCredits i pre.balancePath +
            ((actualBalanceAt ⟨middle.fork, next⟩ i - actualBalanceAt middle i) +
              (actualBalanceAt last i - actualBalanceAt ⟨middle.fork, next⟩ i)) := by
        simp only [Run.balancePath, Step.balancePath, advanced, Except.toOption,
          path, List.append_assoc]
        simp only [List.cons_append, List.nil_append]
        rw [balanceDrift_credits_append]
        simp [pathCredits]
      rw [credits]
      omega

private theorem balanceDrift_reference_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : Nat) (reference : Gwei)
    (aligned : reference.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (funded : reference.toNat ≤ actualBalanceAt ⟨f, s⟩ i)
    (previous : reference.toNat ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      reference ≤ withdrawalMaxEffectiveBalance preset f v) :
    reference.toNat ≤ effectiveAt ⟨f, t⟩ i := by
  have one {a b : BeaconState preset f} {j : Nat}
      (step : updateEffectiveBalance a j = .ok b) :
      b.balances = a.balances ∧
      (∀ v, b.validators.data[i]? = some v →
        reference ≤ withdrawalMaxEffectiveBalance preset f v) →
      (∀ v, a.validators.data[i]? = some v →
        reference ≤ withdrawalMaxEffectiveBalance preset f v) ∧
      (reference.toNat ≤ actualBalanceAt ⟨f, a⟩ i →
        reference.toNat ≤ effectiveAt ⟨f, a⟩ i →
        reference.toNat ≤ effectiveAt ⟨f, b⟩ i) := by
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨v, found, balance, read, next, changed, set⟩ := step
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
    intro premise
    have located := getValidatorAt_eq_ok_iff.mp found
    by_cases eq : i = j
    · subst i
      have nextRead :
          (a.putValidator j inside { v with effectiveBalance := next }).validators.data[j]? =
          some { v with effectiveBalance := next } := by
        simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
      have capped := premise.2 _ nextRead
      change reference ≤ withdrawalMaxEffectiveBalance preset f v at capped
      constructor
      · intro w wRead
        rw [located, Option.some.injEq] at wRead
        subst w
        exact capped
      · intro funded previous
        simp only [actualBalanceAt, getBalanceAt_eq_ok_iff.mp read, effectiveAt, located,
          Option.map_some, Option.getD_some] at funded previous
        simp only [effectiveAt, nextRead, Option.map_some, Option.getD_some]
        rcases updatedEffectiveBalance_cases changed with rfl | rfl
        · exact previous
        · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
            UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
          have quotient := Nat.div_le_div_right funded
            (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          have product := Nat.mul_le_mul_left preset.EFFECTIVE_BALANCE_INCREMENT.toNat quotient
          have refDivision := Nat.mod_add_div reference.toNat
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          have balDivision := Nat.mod_add_div balance.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          rw [aligned] at refDivision
          rw [Base.Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
          have capped := UInt64.le_iff_toNat_le.mp capped
          omega
    · have same :
          (a.putValidator j inside { v with effectiveBalance := next }).validators.data[i]? =
          a.validators.data[i]? := by
        simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm eq]
      constructor
      · simpa only [same] using premise.2
      · intro _ previous
        simpa only [effectiveAt, same] using previous
  have fold : ∀ (xs : List Nat) {a b : BeaconState preset f},
      xs.foldlM updateEffectiveBalance a = .ok b →
      (∀ v, b.validators.data[i]? = some v →
        reference ≤ withdrawalMaxEffectiveBalance preset f v) →
      (∀ v, a.validators.data[i]? = some v →
        reference ≤ withdrawalMaxEffectiveBalance preset f v) ∧
      (reference.toNat ≤ actualBalanceAt ⟨f, a⟩ i →
        reference.toNat ≤ effectiveAt ⟨f, a⟩ i →
        reference.toNat ≤ effectiveAt ⟨f, b⟩ i) := by
    intro xs
    induction xs with
    | nil => intro a b ok cap; cases ok; exact ⟨cap, fun _ previous => previous⟩
    | cons j xs ih =>
      intro a b ok cap
      obtain ⟨middle, updated, rest⟩ := bind_ok_iff.mp ok
      have tail := ih rest cap
      have balances : middle.balances = a.balances := by
        simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at updated
        obtain ⟨_, _, _, _, _, _, set⟩ := updated
        obtain ⟨_, rfl⟩ := setValidatorAt_ok set
        rfl
      have head := one updated ⟨balances, tail.1⟩
      exact ⟨head.1, fun funded previous => tail.2
        (by simpa only [actualBalanceAt, balances] using funded) (head.2 funded previous)⟩
  exact (fold _ ok cap).2 funded previous

private theorem balanceDrift_reference_epoch {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) (reference : Gwei)
    (aligned : reference.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (funded : reference.toNat ≤ actualBalanceAt ⟨f, t⟩ i)
    (previous : reference.toNat ≤ effectiveAt ⟨f, s⟩ i)
    (cap : reference ≤ withdrawalMaxEffectiveBalance preset f v) :
    reference.toNat ≤ effectiveAt ⟨f, t⟩ i := by
  obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch ok
  obtain ⟨w, located, monotone⟩ := processEpoch_validatorCap_mono ok i v found
  have capAfter : ∀ z, after.validators.data[i]? = some z →
      reference ≤ withdrawalMaxEffectiveBalance preset f z := by
    intro z read
    rw [validators] at located
    rw [located, Option.some.injEq] at read
    subst z
    exact UInt64.le_trans cap monotone
  have prior : reference.toNat ≤ effectiveAt ⟨f, before⟩ i := by
    rw [kept i (Array.getElem?_eq_some_iff.mp found).1]
    exact previous
  have bound := balanceDrift_reference_update updated i reference aligned
    (by simpa only [actualBalanceAt, balances] using funded) prior capAfter
  simpa only [effectiveAt, validators] using bound

private theorem balanceDrift_reference_slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) (reference : Gwei)
    (aligned : reference.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (funded : reference.toNat ≤ actualBalanceAt ⟨f, t⟩ i)
    (previous : reference.toNat ≤ effectiveAt ⟨f, s⟩ i)
    (cap : reference ≤ withdrawalMaxEffectiveBalance preset f v) :
    reference.toNat ≤ effectiveAt ⟨f, t⟩ i := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · exact balanceDrift_reference_epoch advance i v found reference aligned funded previous cap
  · cases advance
    exact previous

private theorem balanceDrift_preActivation_excludes {f : Fork} {s : BeaconState preset f}
    (early : f < .glamsterdam) (i : Nat) (v : Validator)
    (found : s.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∀ index ∈ preActivationIndices s, index.toNat ≠ i := by
  intro index member
  simp only [preActivationIndices, List.mem_map, List.mem_mergeSort, List.mem_filter] at member
  obtain ⟨⟨w, j⟩, ⟨located, waiting⟩, rfl⟩ := member
  have read : s.validators.data[j]? = some w := by
    simpa using List.mem_zipIdx_iff_getElem?.mp located
  have inside := (Array.getElem?_eq_some_iff.mp read).1
  have small : j < 2 ^ 64 := Nat.lt_of_lt_of_le inside
    ((s.validators.bound early).trans (Nat.le_of_lt preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt))
  have converted : j.toUInt64.toNat = j := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  rw [converted]
  intro eq
  subst j
  rw [found, Option.some.injEq] at read
  subst w
  exact activated (by simpa using waiting)

private theorem balanceDrift_upgrade_active {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : s.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt t.val i = effectiveAt s i := by
  have reset {f : Fork} {a b : BeaconState preset f} {electra : .pectra ≤ f}
      {index : ValidatorIndex} (different : index.toNat ≠ i)
      (ok : queuePreActivation a electra index = .ok b) :
      effectiveAt ⟨f, b⟩ i = effectiveAt ⟨f, a⟩ i := by
    simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok balance
    obtain ⟨inside, rfl⟩ := setValidator_ok validator
    simp [effectiveAt, BeaconState.putValidator, BeaconState.putBalance,
      Serialization.Ssz.RootedForkList.data_set, different]
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [effectiveAt, (upgradeToAltair_spec upgraded).1]
  · subst ok; rfl
  · subst ok; rfl
  · subst ok; rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    have pass : ∀ (xs : List ValidatorIndex) {a b : BeaconState preset .pectra},
        (∀ j ∈ xs, j.toNat ≠ i) →
        xs.foldlM (fun s j => queuePreActivation s (by decide) j) a = .ok b →
        effectiveAt ⟨.pectra, b⟩ i = effectiveAt ⟨.pectra, a⟩ i := by
      intro xs
      induction xs with
      | nil => intro a b _ ok; cases ok; rfl
      | cons j xs ih =>
        intro a b different ok
        obtain ⟨middle, first, rest⟩ := bind_ok_iff.mp ok
        exact (ih (fun k member => different k (List.mem_cons_of_mem j member)) rest).trans
          (reset (different j List.mem_cons_self) first)
    have excluded := balanceDrift_preActivation_excludes
      (s := state) (by decide) i v found activated
    have one := pass _ (by exact excluded) queued
    have second := foldlM_ok_invariant
        (fun t => effectiveAt ⟨.pectra, t⟩ i = effectiveAt ⟨.dencun, state⟩ i)
        (fun a index b previous ok => ?_) one compounded
    · exact second
    · unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · have step := liftAccessor_ok.mp ok
          simp only [queueExcessActiveBalance, bind_ok_iff] at step
          obtain ⟨_, _, step⟩ := step
          split at step
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
            obtain ⟨_, _, _, _, _, set, rfl⟩ := step
            obtain ⟨_, rfl⟩ := setBalance_ok set
            exact previous
          · cases step; exact previous
        · cases ok; exact previous
      · cases ok; exact previous
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [effectiveAt, (upgradeToFulu_spec upgraded).1]
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

theorem balanceDrift_upgrades_active {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : s.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt t i = effectiveAt s i := by
  fun_induction processUpgrades config checks s generalizing t v with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    obtain ⟨w, located, lifecycle⟩ := (registryLifecycle_upgradeNext nextOk).validators i v found
    exact (ih next rest early w located (by rwa [lifecycle.activationEpoch activated])).trans
      (balanceDrift_upgrade_active nextOk
        (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early) i v found activated)
  | case2 s notDue => cases ok; rfl

/-- The balance at the start of a path is at most the balance at any of its states plus its debits.
-/
private theorem balanceDrift_le_add_pathDebits (i : Nat) :
    ∀ (x : ForkedBeaconState preset) (rest : List (ForkedBeaconState preset))
      (p : ForkedBeaconState preset), p ∈ x :: rest →
      actualBalanceAt x i ≤ actualBalanceAt p i + pathDebits i (x :: rest)
  | x, [], p, member => by
    obtain rfl := List.mem_singleton.mp member
    simp [pathDebits]
  | x, y :: rest, p, member => by
    simp only [pathDebits]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have later := balanceDrift_le_add_pathDebits i y rest p member
      omega

/-- An effective balance stays at or above a reference while the balance does, before Gloas.

The reference is a whole number of increments, and at most the effective balance at `x`.

It is also at most the cap of the validator at `x`, which has an activation epoch.

The balance must be at least the reference at every state of the balance path of the run.

That path holds every state where an update of the effective balances reads the balance. -/
theorem _root_.EthLib.Consensus.Run.effectiveAt_ge_of_balanceFloor
    {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (caps : CapOrder preset) (early : y.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) (reference : Gwei)
    (aligned : reference.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (floor : ∀ p ∈ tail.balancePath, reference.toNat ≤ actualBalanceAt p i)
    (previous : reference.toNat ≤ effectiveAt x i)
    (cap : reference ≤ withdrawalMaxEffectiveBalance preset x.fork v) :
    reference.toNat ≤ effectiveAt y i := by
  induction tail with
  | nil => exact previous
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨w, located, lifecycle⟩ := pre.registryLifecycle.validators i v found
    have assigned : w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      rwa [lifecycle.activationEpoch activated]
    obtain ⟨z, locatedZ, capMono⟩ := pre.validatorCap_mono caps.activation caps.compounding
      middleEarly i v found
    have eq : z = w := by rw [located, Option.some.injEq] at locatedZ; exact locatedZ.symm
    subst z
    have capMiddle := UInt64.le_trans cap capMono
    have prior := ih middleEarly fun p member => floor p (List.mem_append_left _ member)
    have later (p : ForkedBeaconState preset) (member : p ∈ step.balancePath) :=
      floor p (List.mem_append_right _ member)
    cases step with
    | @block fork before after engine signed due ok =>
      rw [effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i
        (Array.getElem?_eq_some_iff.mp located).1]
      exact prior
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have funded := later ⟨middle.fork, next⟩
        (by simp [Step.balancePath, advanced, Except.toOption])
      have updated := balanceDrift_reference_slot advanced i w located reference
        aligned funded prior capMiddle
      obtain ⟨a, read, life⟩ := (registryLifecycle_advanceSlot advanced).validators i w located
      have kept := balanceDrift_upgrades_active upgraded early i a read
        (by rwa [life.activationEpoch assigned])
      rwa [kept]

/-- An effective-balance loss is at most the debits less the initial headroom, and one increment.

The headroom is the actual balance above the effective balance. -/
theorem effective_loss_from_balance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (early : y.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt x i - effectiveAt y i ≤
      (effectiveAt x i + pathDebits i tail.balancePath - actualBalanceAt x i) +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  let amount := min (effectiveAt x i) (actualBalanceAt x i - pathDebits i tail.balancePath)
  let rounded := amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  have effective : effectiveAt x i = v.effectiveBalance.toNat := by simp [effectiveAt, found]
  have amount_le : amount ≤ v.effectiveBalance.toNat := by dsimp [amount]; omega
  have rounded_le : rounded ≤ amount := Nat.sub_le _ _
  have small : rounded < 2 ^ 64 := lt_of_le_of_lt (rounded_le.trans amount_le)
    v.effectiveBalance.toNat_lt
  let reference : Gwei := rounded.toUInt64
  have value : reference.toNat = rounded := by
    dsimp [reference]; rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  by_cases affordable : pathDebits i tail.balancePath ≤ actualBalanceAt x i
  · have capped := shared.effectiveBalance_capped genesis caps.activation caps.compounding
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early) v
      (Array.mem_of_getElem? found)
    obtain ⟨rest, path⟩ := Run.balancePath_head tail
    have bound := tail.effectiveAt_ge_of_balanceFloor caps early i v found activated reference
      (by rw [value]; dsimp [rounded]
          have division := Nat.mod_add_div amount preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          have eq : amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT.toNat =
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
                (amount / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by omega
          rw [eq, Nat.mul_mod_right])
      (fun p member => by
        rw [path] at member
        have below := balanceDrift_le_add_pathDebits i x rest p member
        rw [← path] at below
        rw [value]; dsimp [rounded, amount]; omega)
      (by rw [value]; omega)
      (UInt64.le_iff_toNat_le.mpr (by
        have cap := UInt64.le_iff_toNat_le.mp capped
        rw [value]; omega))
    have remainder := Nat.mod_lt amount increment
    rw [value] at bound
    dsimp [rounded, amount] at *
    omega
  · omega

/-- An effective-balance gain is at most the initial excess balance and the credits. -/
theorem effective_gain_from_balance {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    effectiveAt y i - effectiveAt x i ≤
      (actualBalanceAt x i - effectiveAt x i) + pathCredits i tail.balancePath := by
  have bound := balanceDrift_gain tail early i present
  omega

private def AdmissionFunded {f : Fork} (n : Nat) (s : BeaconState preset f) : Prop :=
  ∀ i, n ≤ i → effectiveAt ⟨f, s⟩ i ≤ actualBalanceAt ⟨f, s⟩ i

private theorem admissionFunded_empty {f : Fork} (s : BeaconState preset f) :
    AdmissionFunded s.validators.data.size s := by
  intro i large
  simp [effectiveAt, Array.getElem?_eq_none large]

private theorem admissionFunded_increase {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {index amount : UInt64} (holds : AdmissionFunded n s)
    (ok : increaseBalance s index amount = .ok t) : AdmissionFunded n t := by
  intro i large
  have prior := holds i large
  have validators := increaseBalance_validators ok
  simp only [effectiveAt, validators] at *
  cases found : s.balances.data[i]? with
  | none =>
    have zero : actualBalanceAt ⟨f, s⟩ i = 0 := by simp [actualBalanceAt, found]
    rw [zero] at prior
    exact prior.trans (Nat.zero_le _)
  | some balance =>
    obtain ⟨now, located, value⟩ := balance_increaseBalance ok found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some] at *
    omega

private theorem admissionFunded_decrease {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {index amount : UInt64} (holds : AdmissionFunded n s)
    (old : index.toNat < n) (ok : decreaseBalance s index amount = .ok t) :
    AdmissionFunded n t := by
  intro i large
  have prior := holds i large
  have validators := decreaseBalance_validators ok
  simp only [effectiveAt, validators] at *
  cases found : s.balances.data[i]? with
  | none =>
    have zero : actualBalanceAt ⟨f, s⟩ i = 0 := by simp [actualBalanceAt, found]
    rw [zero] at prior
    exact prior.trans (Nat.zero_le _)
  | some balance =>
    obtain ⟨now, located, value⟩ := balance_decreaseBalance ok found
    have different : index.toNat ≠ i := by omega
    simpa only [actualBalanceAt, found, located, Option.map_some, Option.getD_some,
      value, ite_eq_right different] using prior

private theorem admissionFunded_syncRewards {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {reward proposerReward : Gwei} {proposer : Except AccessorError ValidatorIndex}
    {members : List (ValidatorIndex × Bool)} (holds : AdmissionFunded n s)
    (old : ∀ member ∈ members, member.1.toNat < n)
    (ok : members.foldlM (applySyncReward reward proposerReward proposer) s = .ok t) :
    AdmissionFunded n t := by
  induction members generalizing s with
  | nil => cases ok; exact holds
  | cons member rest ih =>
    obtain ⟨middle, stepped, folded⟩ := bind_ok_iff.mp ok
    apply ih (s := middle) ?_ (fun item mem => old item (List.mem_cons_of_mem _ mem)) folded
    unfold applySyncReward at stepped
    split at stepped
    · simp only [bind_ok_iff, liftAccessor_ok] at stepped
      obtain ⟨_, raised, _, _, paid⟩ := stepped
      exact admissionFunded_increase (admissionFunded_increase holds raised) paid
    · exact admissionFunded_decrease holds (old member (List.mem_cons_self))
        (liftAccessor_ok.mp stepped)

private theorem balanceDrift_indexOfPubkey_lt {f : Fork} {s : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {index : ValidatorIndex} {n : Nat}
    (existsOld : ∃ j, j < n ∧ ∃ v, s.validators.data[j]? = some v ∧ v.pubkey = key)
    (ok : validatorIndexOfPubkey s key = .ok index) : index.toNat < n := by
  unfold validatorIndexOfPubkey at ok
  split at ok
  · rename_i position found
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at ok
    rw [(Base.Uint64.ofNatChecked_ok_iff.mp ok).2]
    obtain ⟨inside, _, first⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    obtain ⟨j, old, v, located, keyEq⟩ := existsOld
    by_contra large
    have earlier : j < position := by omega
    have different := first j earlier
    have value : s.validators.data[j]'(by omega) = v := by
      exact (Array.getElem?_eq_some_iff.mp located).2
    simp [value, keyEq] at different
  · cases ok

private theorem balanceDrift_old_key {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {key : Cryptography.Bls.BLSPubkey}
    (kept : validatorKeys s <+: validatorKeys t) (member : key ∈ validatorKeys s) :
    ∃ j, j < s.validators.data.size ∧ ∃ v,
      t.validators.data[j]? = some v ∧ v.pubkey = key := by
  obtain ⟨j, inside, value⟩ := List.mem_iff_getElem.mp member
  have later := (List.prefix_iff_getElem?.mp kept) j inside
  rw [value] at later
  simp only [validatorKeys, List.getElem?_map, Array.getElem?_toList] at later
  cases found : t.validators.data[j]? with
  | none => simp [found] at later
  | some v =>
    exact ⟨j, by simpa [validatorKeys] using inside, v, found, by simpa [found] using later⟩

private theorem admissionFunded_sync {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (holds : AdmissionFunded n s)
    (old : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toArray,
      ∀ index, validatorIndexOfPubkey s key = .ok index → index.toNat < n)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    AdmissionFunded n t := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, members, mapped, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  apply admissionFunded_syncRewards holds ?_ folded
  intro member mem
  have memberIn := Array.mem_toList_iff.mp mem
  obtain ⟨key, keyIn, indexed⟩ := array_mapM_ok_mem mapped member.1
    (Array.of_mem_zip memberIn).1
  exact old key keyIn member.1 indexed

private theorem admissionFunded_add {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (holds : AdmissionFunded n s) (matched : BalancesMatch s)
    (ok : addValidatorToRegistry s key credentials amount = .ok t) : AdmissionFunded n t := by
  obtain ⟨validators, balances⟩ := addValidatorToRegistry_push ok matched
  change s.balances.data.size = s.validators.data.size at matched
  intro i large
  by_cases same : s.validators.data.size = i
  · subst i
    have rounded : amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ amount :=
      UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
    simp only [effectiveAt, actualBalanceAt, validators, balances,
      Array.getElem?_push, matched,
      ↓reduceIte, Option.map_some, Option.getD_some,
      getValidatorFromDeposit, Base.Uint64.toNat_min,
      UInt64.toNat_sub_of_le _ _ rounded]
    omega
  · simpa only [effectiveAt, actualBalanceAt, validators, balances,
      Array.getElem?_push, matched, Ne.symm same, ↓reduceIte] using holds i large

private theorem admissionFunded_deposit {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {deposit : PendingDeposit} (holds : AdmissionFunded n s)
    (matched : BalancesMatch s)
    (ok : applyPendingDeposit config checks s deposit = .ok t) : AdmissionFunded n t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · exact holds
  · exact admissionFunded_increase holds ok
  · exact admissionFunded_add holds matched ok

private theorem admissionFunded_applyDeposit {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature} (holds : AdmissionFunded n s)
    (matched : BalancesMatch s)
    (ok : applyDeposit config checks s key credentials amount signature = .ok t) :
    AdmissionFunded n t := by
  rcases applyDeposit_cases ok with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, ok⟩
  · exact holds
  · exact holds
  · simpa only [AdmissionFunded, effectiveAt, actualBalanceAt] using
      admissionFunded_add holds matched added
  · exact admissionFunded_deposit holds matched ok

private theorem admissionFunded_processDeposit {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {before : f < .hegota} {deposit : Deposit}
    (holds : AdmissionFunded n s) (matched : BalancesMatch s)
    (ok : processDeposit config checks before s deposit = .ok t) : AdmissionFunded n t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact admissionFunded_applyDeposit
    (s := { s with eth1DepositIndex := fun _ => next }) holds matched credited

private theorem admissionFunded_kept {f : Fork} {s t : BeaconState preset f}
    {n : Nat} (holds : AdmissionFunded n s) (kept : EffectiveKept s t)
    (size : t.validators.data.size = s.validators.data.size)
    (balances : t.balances = s.balances) : AdmissionFunded n t := by
  intro i large
  by_cases inside : i < s.validators.data.size
  · rw [kept i inside]
    simpa only [actualBalanceAt, balances] using holds i large
  · have absent : t.validators.data[i]? = none := by
      apply Array.getElem?_eq_none; omega
    simp [effectiveAt, absent]

private theorem admissionFunded_exit {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {index : ValidatorIndex} (holds : AdmissionFunded n s)
    (ok : initiateValidatorExit config s index = .ok t) : AdmissionFunded n t := by
  have balances : t.balances = s.balances := by
    obtain ⟨_, _, unchanged | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
    · rw [unchanged.2]
    · obtain ⟨_, rfl⟩ := setValidator_ok set
      exact (exitQueue_validators queue).2
  exact admissionFunded_kept holds (effectiveKept_exit ok) (sameSizes_initiateValidatorExit ok).1
    balances

private theorem admissionFunded_blsChange {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {signed : SignedBLSToExecutionChange} (holds : AdmissionFunded n s)
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : AdmissionFunded n t := by
  have balances : t.balances = s.balances := by
    obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
    obtain ⟨_, rfl⟩ := setValidator_ok set
    rfl
  apply admissionFunded_kept holds ?_ (sameSizes_processBlsToExecutionChange ok).1 balances
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact effectiveKept_setValidator found set rfl

private theorem admissionFunded_partial {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {electra : .pectra ≤ f} {index : ValidatorIndex} {v : Validator}
    {amount owed : Gwei} (holds : AdmissionFunded n s)
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    AdmissionFunded n t := by
  have same : t.validators = s.validators ∧ t.balances = s.balances := by
    simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
    obtain ⟨_, _, _, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
      obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
      exact (computeExitEpochAndUpdateChurn_earliest churned).2
    · cases ok; exact ⟨rfl, rfl⟩
  simpa only [AdmissionFunded, effectiveAt, actualBalanceAt, same.1, same.2] using holds

private theorem admissionFunded_withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (holds : AdmissionFunded n s)
    (ok : processWithdrawalRequest config s electra request = .ok t) : AdmissionFunded n t := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · exact holds
  · exact admissionFunded_exit holds exited
  · exact admissionFunded_partial holds withdrawn

private theorem admissionFunded_compounding {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {electra : .pectra ≤ f} {index : ValidatorIndex}
    (holds : AdmissionFunded n s) (old : index.toNat < n)
    (ok : switchToCompoundingValidator s electra index = .ok t) : AdmissionFunded n t := by
  have size := (switchToCompoundingValidator_compounding ok).1.1
  have kept := effectiveKept_compounding ok
  have balances : ∀ i, n ≤ i → t.balances.data[i]? = s.balances.data[i]? := by
    simp only [switchToCompoundingValidator, bind_ok_iff] at ok
    obtain ⟨_, _, _, set, queued⟩ := ok
    obtain ⟨_, rfl⟩ := setValidator_ok set
    simp only [queueExcessActiveBalance, bind_ok_iff] at queued
    obtain ⟨_, _, queued⟩ := queued
    split at queued
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
      obtain ⟨_, _, _, _, _, setBalance, rfl⟩ := queued
      obtain ⟨_, rfl⟩ := setBalance_ok setBalance
      intro i large
      have different : index.toNat ≠ i := by omega
      simp [BeaconState.putBalance, BeaconState.putValidator, different]
    · cases queued; intro i _; rfl
  intro i large
  by_cases inside : i < s.validators.data.size
  · rw [kept i inside]
    simpa only [actualBalanceAt, balances i large] using holds i large
  · have absent : t.validators.data[i]? = none := by
      apply Array.getElem?_eq_none; omega
    simp [effectiveAt, absent]

private theorem admissionFunded_consolidate {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex}
    {source : Validator} (holds : AdmissionFunded n s)
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    AdmissionFunded n t :=
  admissionFunded_kept holds (effectiveKept_consolidate found ok)
    (sameSizes_queueConsolidation ok).1 (queueConsolidation_balances ok)

private theorem admissionFunded_consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (holds : AdmissionFunded n s)
    (pending : ∀ i v, n ≤ i → s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH)
    (ok : processConsolidationRequest config s electra request = .ok t) : AdmissionFunded n t := by
  rcases consolidationRequest_cases ok with rfl | ⟨index, validator, switch, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact holds
  · -- A validator from the index `n` on is not active, so it cannot pass the switch check.
    refine admissionFunded_compounding holds (Nat.lt_of_not_le fun large => ?_) switched
    have epochs := pending index.toNat validator large switch.found
    have inactive : isActiveValidator validator (getCurrentEpoch s) = false := by
      simp only [isActiveValidator, epochs.1, epochs.2, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_cases h : FAR_FUTURE_EPOCH ≤ getCurrentEpoch s
      · exact Or.inr (UInt64.not_lt.mpr h)
      · exact Or.inl h
    have valid := switch.valid
    simp only [isValidSwitchToCompoundingRequest, inactive, Bool.and_false, Bool.false_and,
      Bool.false_eq_true] at valid
  · exact admissionFunded_consolidate holds accepted.sourceAt queued

private theorem admissionFunded_requests {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (holds : AdmissionFunded n s)
    (pending : ∀ i v, n ≤ i → s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH)
    (ok : processExecutionRequests config s body electra = .ok t) : AdmissionFunded n t := by
  let property := fun a : BeaconState preset f => AdmissionFunded n a ∧
    ∀ i v, n ≤ i → a.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  have one : property deposited := foldlM_ok_invariant property (fun a request b prior ok => by
    obtain ⟨_, validators, balances, -⟩ := processDepositRequest_ok ok
    constructor
    · simpa only [AdmissionFunded, effectiveAt, actualBalanceAt, validators, balances] using prior.1
    · simpa only [validators] using prior.2) ⟨holds, pending⟩ deposits
  have two : property withdrawn := foldlM_ok_invariant property (fun a request b prior ok =>
    ⟨admissionFunded_withdrawalRequest prior.1 ok,
      processWithdrawalRequest_epochs_unassigned ok prior.2⟩) one withdrawals
  exact (foldlM_ok_invariant property (fun a request b prior ok =>
    ⟨admissionFunded_consolidationRequest prior.1 prior.2 ok,
      processConsolidationRequest_epochs_unassigned ok prior.2⟩) two consolidations).1

private theorem balanceDrift_unassigned_before {f h : Fork}
    {s : BeaconState preset f} {t : BeaconState preset h} {n : Nat}
    (lifecycle : RegistryLifecycle s t)
    (pending : ∀ i v, n ≤ i → t.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH) :
    ∀ i v, n ≤ i → s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH := by
  intro i v large found
  obtain ⟨w, located, life⟩ := lifecycle.validators i v found
  have epochs := pending i w large located
  constructor
  · by_contra assigned
    exact assigned ((life.activationEpoch assigned).symm.trans epochs.1)
  · by_contra assigned
    exact assigned ((life.exitEpoch assigned).symm.trans epochs.2)

/-- Block operations fund every validator that they admit, from its deposit.

The three folds before the deposits keep the registry size, so no entry needs funding there.

After them each step funds new entries if the entries of its end state are still unassigned.

The end state of the operations has all new entries unassigned. -/
private theorem admissionFunded_operations {f : Fork} {s t : BeaconState preset f}
    (early : f < .glamsterdam) {body : BeaconBlockBody preset f} {parentSlot : Slot}
    (matched : BalancesMatch s)
    (ok : processOperations config checks s body parentSlot = .ok t) :
    AdmissionFunded s.validators.data.size t := by
  let n := s.validators.data.size
  let Pending (a : BeaconState preset f) : Prop := ∀ i v, n ≤ i → a.validators.data[i]? = some v →
    v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH
  let Funds (a b : BeaconState preset f) : Prop := RegistryLifecycle a b ∧
    (Pending b → AdmissionFunded n a → BalancesMatch a → AdmissionFunded n b ∧ BalancesMatch b)
  have refl (a : BeaconState preset f) : Funds a a := ⟨.refl a, fun _ funded m => ⟨funded, m⟩⟩
  have trans {a b c : BeaconState preset f} (one : Funds a b) (two : Funds b c) : Funds a c :=
    ⟨one.1.trans two.1, fun pending funded m =>
      have middle := one.2 (balanceDrift_unassigned_before two.1 pending) funded m
      two.2 pending middle.1 middle.2⟩
  obtain ⟨_, _, attested, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of Funds refl trans
      (fun deposited => ⟨registryLifecycle_processDeposit deposited, fun _ funded m =>
        ⟨admissionFunded_processDeposit funded m deposited,
          balancesMatch_processDeposit deposited m⟩⟩)
      (fun exited => ⟨registryLifecycle_processVoluntaryExit exited, fun _ funded m =>
        ⟨admissionFunded_exit funded (processVoluntaryExit_initiates exited),
          balancesMatch_of_sameSizes (sameSizes_processVoluntaryExit exited) m⟩⟩)
      (fun changed => ⟨registryLifecycle_processBlsToExecutionChange changed, fun _ funded m =>
        ⟨admissionFunded_blsChange funded changed,
          balancesMatch_of_sameSizes (sameSizes_processBlsToExecutionChange changed) m⟩⟩)
      (fun requested => ⟨registryLifecycle_processExecutionRequests requested,
        fun pending funded m => ⟨admissionFunded_requests funded (balanceDrift_unassigned_before
          (registryLifecycle_processExecutionRequests requested) pending) requested,
          (frame_processExecutionRequests requested).toFrame.balancesMatch m⟩⟩)
      (fun {_ _ gloas} _ => absurd gloas (Nat.not_le_of_lt early)) ok
  have sizes {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      (keeps : ∀ a b c, step a b = .ok c → SameSizes a c) {xs : List α}
      {a b : BeaconState preset f} (ok : xs.foldlM step a = .ok b) : SameSizes a b :=
    foldlM_ok_invariant (SameSizes a)
      (fun _ _ _ prior ok => prior.trans (keeps _ _ _ ok)) (SameSizes.refl _) ok
  have before := (sizes (fun _ _ _ => sameSizes_processProposerSlashing) proposersOk).trans
    ((sizes (fun _ _ _ => sameSizes_processAttesterSlashing) slashingsOk).trans
      (sizes (fun _ _ _ => sameSizes_processAttestation) attestedOk))
  have initial : AdmissionFunded n attested := by
    change AdmissionFunded s.validators.data.size attested
    rw [← before.1]
    exact admissionFunded_empty _
  exact (rest.2 (processOperations_new_validator_epochs_unassigned ok) initial
    (balancesMatch_of_sameSizes before matched)).1

/-- A block funds every validator that it admits.

The steps before the operations keep the validators, the current sync committee and the keys.

The sync aggregate then pays only validators whose keys were in the registry before the block. -/
private theorem admissionFunded_block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (early : f < .glamsterdam) (matched : BalancesMatch s)
    (keys : ∀ altair : .altair ≤ f,
      ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList, key ∈ validatorKeys s)
    (ok : processBlock config checks engine s block = .ok t) :
    AdmissionFunded s.validators.data.size t := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head (altair : .altair ≤ f) :
      input.currentSyncCommittee altair = s.currentSyncCommittee altair :=
    OperationsInput.step_of (fun a b : BeaconState preset f =>
        b.currentSyncCommittee altair = a.currentSyncCommittee altair) (fun _ => rfl)
      (fun one two => two.trans one)
      (fun gloas _ => absurd gloas (Nat.not_le_of_lt early))
      (fun headed => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed; rfl)
      (fun _ executed => processBlockExecution_currentSyncCommittee altair executed)
      (fun revealed => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        rfl)
      (fun _ voted => by obtain ⟨_, _, rest⟩ := processEth1Data_eq voted; rw [← rest])
      started
  have frame := frame_operationsInput started
  have funded := admissionFunded_operations early (frame.balancesMatch matched) operated
  rw [OperationsInput.validators_eq early started] at funded
  split at synced
  · rename_i altair
    apply admissionFunded_sync funded ?_ synced
    intro key member index indexed
    apply balanceDrift_indexOfPubkey_lt ?_ indexed
    apply balanceDrift_old_key
      (frame.pubkeysPrefix.trans (frame_processOperations operated).pubkeysPrefix)
    apply keys altair key
    have same : last.currentSyncCommittee altair = s.currentSyncCommittee altair := by
      rw [processOperations_currentSyncCommittee altair operated, head altair]
    simpa only [same, Vector.toList_toArray] using (Array.mem_toList_iff.mpr member)
  · cases synced
    exact funded

private theorem admissionFunded_pendingDeposits {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {electra : .pectra ≤ f} (holds : AdmissionFunded n s)
    (matched : BalancesMatch s)
    (ok : processPendingDeposits config checks s electra = .ok t) : AdmissionFunded n t := by
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → AdmissionFunded n state → BalancesMatch state →
          AdmissionFunded n result.1.state := fun ok =>
    -- Each deposit keeps the balances matched, which the next deposit needs.
    (passPendingDeposits_of
      (fun s t => (AdmissionFunded n s → BalancesMatch s → AdmissionFunded n t) ∧
        (BalancesMatch s → BalancesMatch t))
      (fun _ => ⟨fun holds _ => holds, id⟩)
      (fun one two => ⟨fun holds matched => two.1 (one.1 holds matched) (one.2 matched),
        two.2 ∘ one.2⟩)
      (fun credited => ⟨fun holds matched => admissionFunded_deposit holds matched credited,
        (frame_applyPendingDeposit credited).balancesMatch⟩) ok).1
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact pass ‹_› holds matched

private theorem admissionFunded_passConsolidations {f : Fork} {n : Nat} {nextEpoch : Epoch}
    {entries : List PendingConsolidation} {s : BeaconState preset f} {result}
    (holds : AdmissionFunded n s)
    (old : ∀ entry ∈ entries, entry.sourceIndex.toNat < n)
    (ok : passPendingConsolidations nextEpoch s entries = .ok result) :
    AdmissionFunded n result.1 := by
  induction entries generalizing s result with
  | nil => cases ok; exact holds
  | cons entry rest ih =>
    unfold passPendingConsolidations at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i output passed
      cases ok
      exact ih (result := output) holds
        (fun entry mem => old entry (List.mem_cons_of_mem _ mem)) passed
    split at ok
    · cases ok; exact holds
    split at ok
    · cases ok
    split at ok
    · cases ok
    rename_i lowered loweredOk
    split at ok
    · cases ok
    rename_i raised raisedOk
    split at ok
    · cases ok
    rename_i output passed
    cases ok
    exact ih (result := output) (admissionFunded_increase
      (admissionFunded_decrease holds (old entry (List.mem_cons_self))
        (liftAccessor_ok.mp loweredOk)) (liftAccessor_ok.mp raisedOk))
      (fun entry mem => old entry (List.mem_cons_of_mem _ mem)) passed

private theorem admissionFunded_consolidations {f : Fork} {s t : BeaconState preset f}
    {n : Nat} {electra : .pectra ≤ f} (holds : AdmissionFunded n s)
    (old : ∀ entry ∈ (s.pendingConsolidations electra).data.toList,
      entry.sourceIndex.toNat < n)
    (ok : processPendingConsolidations s electra = .ok t) : AdmissionFunded n t := by
  obtain ⟨result, passed, balances, _⟩ := processPendingConsolidations_pass ok
  have funded := admissionFunded_passConsolidations holds old passed
  intro i large
  simpa only [effectiveAt, actualBalanceAt, (processPendingConsolidations_kept ok).1,
    (passPendingConsolidations_kept passed).1, balances] using funded i large

/-- Validators admitted by an epoch start with an effective balance funded by their balance.

Before pending deposits the registry, the balances and the consolidation queue keep their sizes.

Pending deposits and consolidations then fund new entries, and later stages keep the funding. -/
private theorem admissionFunded_epoch {f : Fork} {s t : BeaconState preset f}
    (matched : BalancesMatch s) (sources : PendingSources s)
    (ok : processEpoch config checks s = .ok t) :
    AdmissionFunded s.validators.data.size t := by
  have transport {a b : BeaconState preset f} {n : Nat} (funded : AdmissionFunded n a)
      (same : b.validators = a.validators ∧ b.balances = a.balances) : AdmissionFunded n b := by
    intro i large
    simpa only [effectiveAt, actualBalanceAt, same.1, same.2] using funded i large
  have trace := processEpoch_trace ok
  change EpochTrace _ ([.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ [.pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances,
      .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
      .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨reset, head, tail⟩ := EpochTrace.append_iff.mp trace
  have start : SameSizes s reset ∧ reset.pendingConsolidations = s.pendingConsolidations := by
    refine head.transport
      (fun a b => SameSizes a b ∧ b.pendingConsolidations = a.pendingConsolidations)
      (fun a => ⟨SameSizes.refl a, rfl⟩) (fun one two => ⟨one.1.trans two.1, two.2.trans one.2⟩)
      ?_
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    cases k
    case rewards => exact ⟨processRewardsAndPenalties_sameSizes edge, edge.samePendingQueue nofun⟩
    case registry => exact ⟨sameSizes_processRegistryUpdates edge, edge.samePendingQueue nofun⟩
    case slashings => exact ⟨sameSizes_processSlashings edge, edge.samePendingQueue nofun⟩
    case justification | inactivity | eth1Reset =>
      have kept := edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
      exact ⟨⟨congrArg (·.data.size) kept.1, congrArg (·.data.size) kept.2.1⟩, kept.2.2.1⟩
    all_goals simp at member
  have size := start.1.1
  cases tail
  rename_i deposited depositedOk tail
  cases tail
  rename_i consolidated consolidatedOk tail
  cases tail
  rename_i paid paidOk tail
  cases tail
  rename_i balanced balancedOk tail
  -- Before pending deposits the registry has its old size, so no entry needs funding yet.
  have pending : AdmissionFunded s.validators.data.size consolidated := by
    have depositEdge := EpochStage.action_cases.mp depositedOk
    have consolidationEdge := EpochStage.action_cases.mp consolidatedOk
    simp only [EpochStage.Edge] at depositEdge consolidationEdge
    rw [← size]
    by_cases electra : Fork.pectra ≤ f
    · simp only [electra, ↓reduceDIte] at depositEdge consolidationEdge
      apply admissionFunded_consolidations (admissionFunded_pendingDeposits
        (admissionFunded_empty reset) (balancesMatch_of_sameSizes start.1 matched) depositEdge)
        ?_ consolidationEdge
      simpa only [processPendingDeposits_pendingConsolidations depositEdge, start.2, size] using
        sources electra
    · simp only [electra, ↓reduceDIte] at depositEdge consolidationEdge
      subst depositEdge consolidationEdge
      exact admissionFunded_empty reset
  have paidEdge := EpochStage.action_cases.mp paidOk
  have atPaid := transport pending ⟨paidEdge.validators_eq ⟨nofun, nofun, nofun⟩,
    paidEdge.balances_eq ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩⟩
  have updated := EpochStage.action_cases.mp balancedOk
  change processEffectiveBalanceUpdates paid = .ok balanced at updated
  have atBalanced : AdmissionFunded s.validators.data.size balanced := by
    intro i large
    have bound := balanceDrift_update_upper updated i
    simpa only [actualBalanceAt, processEffectiveBalanceUpdates_balances updated] using
      bound.trans (max_le (atPaid i large) (Nat.le_refl _))
  exact transport atBalanced (balanceDrift_late tail)

private theorem admissionFunded_slot {f : Fork} {s t : BeaconState preset f}
    (matched : BalancesMatch s) (sources : PendingSources s)
    (ok : advanceSlot config checks s = .ok t) : AdmissionFunded s.validators.data.size t := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · have funded := admissionFunded_epoch (s := _) (t := advanced) (by exact matched)
      (by exact sources) advance
    exact funded
  · cases advance
    exact admissionFunded_empty s

private theorem balanceDrift_join_of_admission {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (i : Nat)
    (newKey : x.state.validators.data.size ≤ i)
    (matched : BalancesMatch x.state)
    (admitted : ∀ {a b : ForkedBeaconState preset}, Run config checks g a →
      (step : Step config checks a b) → b.fork < .glamsterdam →
      a.state.validators.data.size ≤ i →
      max (effectiveAt b i) (actualBalanceAt b i) ≤ pathCredits i step.balancePath) :
    max (effectiveAt y i) (actualBalanceAt y i) ≤ pathCredits i tail.balancePath := by
  induction tail with
  | nil =>
    have absent : x.state.balances.data[i]? = none := by
      apply Array.getElem?_eq_none; rw [matched]; exact newKey
    simp [Run.balancePath, pathCredits, effectiveAt, actualBalanceAt, absent,
      Array.getElem?_eq_none newKey]
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have prior := ih middleEarly
    have credits : pathCredits i (pre.snoc step).balancePath =
        pathCredits i pre.balancePath + pathCredits i step.balancePath := by
      obtain ⟨initial, path⟩ := Run.balancePath_last pre
      cases step with
      | block engine signed due ok =>
        simp only [Run.balancePath, Step.balancePath, path, List.append_assoc,
          List.cons_append, List.nil_append]
        rw [balanceDrift_credits_append]
        simp [pathCredits]
      | slot ok =>
        obtain ⟨next, advanced, _⟩ := bind_ok_iff.mp ok
        simp only [Run.balancePath, Step.balancePath, advanced, Except.toOption,
          path, List.append_assoc, List.cons_append, List.nil_append]
        rw [balanceDrift_credits_append]
        simp [pathCredits]
    rw [credits]
    by_cases present : i < middle.state.validators.data.size
    · have gained := balanceDrift_gain (.snoc .nil step) early i present
      have single : pathCredits i (Run.snoc Run.nil step).balancePath =
          pathCredits i step.balancePath := by
        cases step with
        | block engine signed due ok => simp [Run.balancePath, Step.balancePath, pathCredits]
        | slot ok =>
          obtain ⟨next, advanced, _⟩ := bind_ok_iff.mp ok
          simp [Run.balancePath, Step.balancePath, advanced, Except.toOption, pathCredits]
      rw [single] at gained
      omega
    · exact (admitted (shared.append pre) step early (by omega)).trans (Nat.le_add_left _ _)

private theorem balanceDrift_admission_step {g x y : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (sources : PendingSources x.state) (step : Step config checks x y)
    (early : y.fork < .glamsterdam) (i : Nat) (absent : x.state.validators.data.size ≤ i) :
    max (effectiveAt y i) (actualBalanceAt y i) ≤ pathCredits i step.balancePath := by
  have matched := reachable_balancesMatch run genesis
  change x.state.balances.data.size = x.state.validators.data.size at matched
  have zero : actualBalanceAt x i = 0 := by
    have missing : x.state.balances.data[i]? = none :=
      Array.getElem?_eq_none (by simpa only [matched] using absent)
    simp only [actualBalanceAt, missing, Option.map_none, Option.getD_none]
  cases step with
  | block engine signed due ok =>
    have funded := admissionFunded_block early matched
      (fun altair => (run.syncCommittee_keys genesis altair).1)
      (applySignedBlock_ok ok).2.1 i absent
    simp only [Step.balancePath, pathCredits, zero, Nat.sub_zero, Nat.add_zero]
    exact max_le funded (Nat.le_refl _)
  | slot ok =>
    obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
    have funded := admissionFunded_slot matched sources advanced i absent
    change effectiveAt ⟨x.fork, next⟩ i ≤ actualBalanceAt ⟨x.fork, next⟩ i at funded
    have upper := balanceDrift_upgrades_upper upgraded early i
    simp only [Step.balancePath, advanced, Except.toOption, pathCredits, zero,
      Nat.sub_zero, Nat.add_zero]
    omega

private theorem balanceDrift_join_of_sources {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (early : y.fork < .glamsterdam)
    (sources : ∀ {a : ForkedBeaconState preset}, Run config checks g a →
      a.fork < .glamsterdam → PendingSources a.state)
    (i : Nat) (newKey : x.state.validators.data.size ≤ i) :
    effectiveAt y i ≤ pathCredits i tail.balancePath := by
  apply (Nat.le_max_left _ _).trans
  apply balanceDrift_join_of_admission shared tail early i newKey
    (reachable_balancesMatch shared genesis)
  intro a b run step early absent
  exact balanceDrift_admission_step run genesis
    (sources run (Nat.lt_of_le_of_lt step.chainStep.fork_le early)) step early i absent

/-- New keys are bounded from their actual admission balance, not a fictitious zero receipt.

The withdrawal delay is positive. -/
theorem joining_growth_from_admission {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (i : Nat) (newKey : x.state.validators.data.size ≤ i) :
    effectiveAt y i ≤ pathCredits i tail.balancePath :=
  balanceDrift_join_of_sources shared tail genesis early
    (fun run early => run.pendingConsolidation_sources genesis early delay) i newKey

end EthLib.Consensus
