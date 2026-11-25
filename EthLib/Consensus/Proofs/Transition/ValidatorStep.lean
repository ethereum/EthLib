module

public import EthLib.Consensus.Proofs.Transition.Totality.Genesis
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.RunKept
public import EthLib.Consensus.Proofs.Proposers
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card
import EthLib.Base.Proofs.Nat
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance
import EthLib.Consensus.Proofs.Transition.PendingConsolidations
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
public import EthLib.Consensus.Proofs.Transition.AssignedProposers
import EthLib.Consensus.Proofs.Transition.InactivityLeakVoter
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.DepositCarryCore
import EthLib.Consensus.Proofs.Transition.ActiveKept
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The facts that one step keeps for every validator

One induction over the steps of a run carries the facts about each validator that later proofs read.

They cover the cap of the effective balance, the assigned exits and the withdrawable epochs.

They also cover the balance that a validator holds before its activation.

The topic modules state them for a run, a block and an epoch.

The declarations here serve those modules only, in a namespace that is not a stable interface.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- At genesis, each validator's effective balance is at most the cap of its credentials. -/
theorem Genesis.effectiveBalance_capped {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ∀ validator ∈ g.state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset g.fork validator := by
  obtain ⟨hash, time, deposits, _, initialized⟩ := genesis
  exact (initializeBeaconStateFromEth1_withinBudget 0 (Nat.le_refl _) initialized).capped

namespace Internal

/-- Unassigned validators retain their effective-balance funding and eligibility threshold. -/
def UnassignedEligibleBalance {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.activationEpoch = FAR_FUTURE_EPOCH →
    (∃ balance, s.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      (v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance) ∧ v.slashed = false

/-- From Electra, an eligible key that is not yet active keeps its activation reserve. -/
def ScheduledEligibleBalanceElectra {f : Fork} (s : BeaconState preset f) : Prop :=
  .pectra ≤ f → ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    (v.activationEpoch ≠ FAR_FUTURE_EPOCH ∨ v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH) →
    getCurrentEpoch s < v.activationEpoch →
    ((getCurrentEpoch s).toNat + 1 < v.activationEpoch.toNat →
      ∃ balance, s.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance ∧ v.slashed = false

/-- Before Electra, a scheduled key keeps its activation reserve until it becomes active. -/
def ScheduledEligibleBalance {f : Fork} (s : BeaconState preset f)
    (cutoff : Nat := (getCurrentEpoch s).toNat) : Prop :=
  f < .pectra → ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    cutoff < v.activationEpoch.toNat → v.activationEpoch ≠ FAR_FUTURE_EPOCH →
    preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance ∧
      ((getCurrentEpoch s).toNat + 1 < v.activationEpoch.toNat →
        ∃ balance, s.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      v.slashed = false

/-- A scheduled key keeps its activation reserve until it becomes active. -/
private def ScheduledFree {f : Fork} (s : BeaconState preset f)
    (cutoff : Nat := (getCurrentEpoch s).toNat) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    cutoff < v.activationEpoch.toNat → v.activationEpoch ≠ FAR_FUTURE_EPOCH →
    preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance ∧
      ((getCurrentEpoch s).toNat + 1 < v.activationEpoch.toNat →
        ∃ balance, s.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      v.slashed = false

private theorem ScheduledFree.restrict {f : Fork} {s : BeaconState preset f}
    {before after : Nat} (held : ScheduledFree s before) (later : before ≤ after) :
    ScheduledFree s after := by
  intro i v found future assigned
  exact held i v found (Nat.lt_of_le_of_lt later future) assigned

private theorem ScheduledFree.reframe {f h : Fork}
    {s : BeaconState preset f} {t : BeaconState preset h} {before after : Nat}
    (held : ScheduledFree s before) (later : before ≤ after)
    (forward : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat)
    (validators : t.validators.data = s.validators.data)
    (balances : t.balances.data = s.balances.data) :
    ScheduledFree t after := by
  intro i v found future assigned
  obtain ⟨minimum, funding, unslashed⟩ := held
    i v (validators ▸ found) (Nat.lt_of_le_of_lt later future) assigned
  refine ⟨minimum, ?_, unslashed⟩
  intro distant
  obtain ⟨b, located, low⟩ := funding (by omega)
  exact ⟨b, by rw [balances]; exact located, low⟩

/-- A live candidate owns capped funding; assignment replaces it by a permanent MEB charge. -/
def preKeyCharge {f : Fork} (candidate : Nat → Bool)
    (s : BeaconState preset f) (i : Nat) : Nat :=
  if candidate i then
    ((s.validators.data[i]?).map fun v =>
      if v.activationEpoch = FAR_FUTURE_EPOCH then
        max v.effectiveBalance.toNat
          (min ((s.balances.data[i]?.map UInt64.toNat).getD 0)
            (withdrawalMaxEffectiveBalance preset f v).toNat)
      else preset.MAX_EFFECTIVE_BALANCE.toNat).getD 0
  else 0

private theorem preKeyCharge_balance {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (credit : Nat → Nat)
    (growth : ∀ i, ((t.balances.data[i]?.map UInt64.toNat).getD 0) ≤
      ((s.balances.data[i]?.map UInt64.toNat).getD 0) + credit i) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i + credit i := by
  intro i
  have paid := growth i
  unfold preKeyCharge
  rw [same]
  split
  · cases found : s.validators.data[i]? with
    | none => simp
    | some v =>
      simp only [Option.map_some, Option.getD_some]
      split <;> omega
  · omega

private theorem preKeyCharge_same {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (balances : t.balances = s.balances) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  intro i
  simp only [preKeyCharge, same, balances]

private theorem preKeyCharge_sum_range {f : Fork} (candidate : Nat → Bool)
    (s : BeaconState preset f) {size : Nat} (contains : s.validators.data.size ≤ size) :
    (∑ i ∈ Finset.range size, preKeyCharge candidate s i) =
      ∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i := by
  symm
  apply Finset.sum_subset (Finset.range_mono contains)
  intro i _ outside
  have absent : s.validators.data[i]? = none := Array.getElem?_eq_none (by
    simpa only [Finset.mem_range, not_lt] using outside)
  simp only [preKeyCharge, absent, Option.map_none, Option.getD_none, ite_self]

private theorem preKeyCharge_notRaised {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (lowered : ∀ i, BalanceNotRaised i s t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i := by
  have growth := preKeyCharge_balance candidate same (fun _ => 0) (by
    intro i
    cases after : t.balances.data[i]? with
    | none => simp only [Option.map_none, Option.getD_none, Nat.zero_le]
    | some b =>
      obtain ⟨a, before, low⟩ := lowered i b after
      simpa only [after, before, Option.map_some, Option.getD_some, Nat.add_zero] using
        UInt64.le_iff_toNat_le.mp low)
  simpa only [Nat.add_zero] using growth

private theorem preKeyCharge_of_live_balances {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (same : t.validators.data = s.validators.data)
    (matched : BalancesMatch s)
    (balances : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → ∀ balance,
      s.balances.data[i]? = some balance → t.balances.data[i]? = some balance) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  intro i
  cases found : s.validators.data[i]? with
  | none => simp only [preKeyCharge, same, found, Option.map_none, Option.getD_none]
  | some v =>
    by_cases pending : v.activationEpoch = FAR_FUTURE_EPOCH
    · have inside : i < s.balances.data.size := by
        rw [matched]
        exact (Array.getElem?_eq_some_iff.mp found).1
      have read := Array.getElem?_eq_getElem inside
      simp only [preKeyCharge, same, found, pending, ↓reduceIte, Option.map_some,
        Option.getD_some, read, balances i v found pending _ read]
    · simp only [preKeyCharge, same, found, pending, ↓reduceIte, Option.map_some,
        Option.getD_some]

/-- At genesis, unassigned validators are funded and none is eligible yet. -/
private theorem genesis_unassigned_eligible_balance {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    UnassignedEligibleBalance g.state := by
  intro i v found pending
  obtain ⟨_, _, _, _, initialized⟩ := genesis
  obtain ⟨funded, unassigned, unslashed⟩ := initializeBeaconStateFromEth1_unassigned_eligibility
    initialized i v found pending
  refine ⟨funded, ?_, unslashed⟩
  exact fun assigned => False.elim (assigned unassigned)

private theorem UnassignedEligibleBalance.transfer {f h : Fork}
    {s : BeaconState preset f} {t : BeaconState preset h}
    (held : UnassignedEligibleBalance s) (same : t.validators.data = s.validators.data)
    (balances : ∀ (i : Nat) (v : Validator) (b : Gwei),
      s.validators.data[i]? = some v → v.activationEpoch = FAR_FUTURE_EPOCH →
      s.balances.data[i]? = some b → v.effectiveBalance ≤ b →
      ∃ c, t.balances.data[i]? = some c ∧ v.effectiveBalance ≤ c) :
    UnassignedEligibleBalance t := by
  intro i v found pending
  have before := same ▸ found
  obtain ⟨⟨b, read, low⟩, eligible, unslashed⟩ := held i v before pending
  exact ⟨balances i v b before pending read low, eligible, unslashed⟩

private theorem UnassignedEligibleBalance.setBalance {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : UnassignedEligibleBalance s)
    (floor : ∀ v, s.validators.data[index.toNat]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → v.effectiveBalance ≤ amount)
    (ok : s.setBalance index amount = .ok t) : UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := setBalance_ok ok
  apply held.transfer (t := s.putBalance index.toNat inside amount) rfl
  intro i v b found pending read low
  by_cases same : index.toNat = i
  · subst i
    exact ⟨amount, by simp [BeaconState.putBalance], floor v found pending⟩
  · refine ⟨b, ?_, low⟩
    simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same] using read

private theorem UnassignedEligibleBalance.increase {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : UnassignedEligibleBalance s)
    (ok : increaseBalance s index amount = .ok t) : UnassignedEligibleBalance t := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  apply held.transfer (t := s.putBalance index.toNat inside
    (s.balances.data[index.toNat] + amount)) rfl
  intro i v b _ _ read low
  by_cases same : index.toNat = i
  · subst i
    have equal := Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans read)
    subst b
    refine ⟨s.balances.data[index.toNat] + amount, by simp [BeaconState.putBalance], ?_⟩
    apply UInt64.le_trans low
    apply UInt64.le_iff_toNat_le.mpr
    rw [Uint64.toNat_add_of_lt fits]
    omega
  · refine ⟨b, ?_, low⟩
    simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same] using read

private theorem UnassignedEligibleBalance.decrease {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : UnassignedEligibleBalance s)
    (assigned : ∀ v, s.validators.data[index.toNat]? = some v →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : decreaseBalance s index amount = .ok t) : UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  apply held.transfer (t := s.putBalance index.toNat inside
    (Uint64.saturatingSub s.balances.data[index.toNat] amount)) rfl
  intro i v b found pending read low
  have different : index.toNat ≠ i := by
    rintro rfl
    exact assigned v found pending
  refine ⟨b, ?_, low⟩
  simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set, different] using read

private theorem UnassignedEligibleBalance.add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (held : UnassignedEligibleBalance s) (matched : BalancesMatch s)
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    UnassignedEligibleBalance t := by
  obtain ⟨validators, balances⟩ := addValidatorToRegistry_push ok matched
  have sizes : s.validators.data.size = s.balances.data.size := matched.symm
  intro i v found pending
  rw [validators, Array.getElem?_push] at found
  split at found
  · rename_i equal
    cases found
    refine ⟨⟨amount, ?_, ?_⟩, fun impossible => (impossible rfl).elim, rfl⟩
    · simp [balances, equal, sizes]
    · apply UInt64.le_iff_toNat_le.mpr
      change (min (amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT) _).toNat ≤ amount.toNat
      rw [Uint64.toNat_min]
      apply Nat.le_trans (Nat.min_le_left _ _)
      exact UInt64.le_iff_toNat_le.mp (UInt64.sub_le (by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
        exact Nat.mod_le _ _))
  · rename_i different
    obtain ⟨⟨b, read, low⟩, eligible, unslashed⟩ := held i v found pending
    exact ⟨⟨b, by simpa [balances, Array.getElem?_push, ← sizes, different] using read, low⟩,
      eligible, unslashed⟩

private theorem UnassignedEligibleBalance.setValidatorAt {f : Fork}
    {s t : BeaconState preset f} {i : Nat} {v w : Validator}
    (held : UnassignedEligibleBalance s) (found : getValidatorAt s i = .ok v)
    (set : s.setValidatorAt i w = .ok t)
    (kept : w.activationEpoch = FAR_FUTURE_EPOCH →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧
      w.effectiveBalance ≤ v.effectiveBalance ∧
      (w.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ w.effectiveBalance) ∧ w.slashed = false) :
    UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j old read pending
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at read
  split at read
  · rename_i equal
    subst j
    cases read
    obtain ⟨before, lower, eligible, unslashed⟩ := kept pending
    obtain ⟨⟨b, located, funded⟩, _, _⟩ :=
      held i v (getValidatorAt_eq_ok_iff.mp found) before
    exact ⟨⟨b, located, UInt64.le_trans lower funded⟩, eligible, unslashed⟩
  · exact held j old read pending

private theorem queueForActivation_eligibility {f : Fork} {s : BeaconState preset f}
    {v w : Validator}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (eligible : v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
      preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance)
    (ok : queueForActivation s v = .ok w) :
    w.effectiveBalance = v.effectiveBalance ∧ w.activationEpoch = v.activationEpoch ∧
      w.slashed = v.slashed ∧
      (w.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ w.effectiveBalance) := by
  unfold queueForActivation at ok
  split at ok
  · rename_i queued
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    refine ⟨rfl, rfl, rfl, fun _ => ?_⟩
    unfold isEligibleForActivationQueue at queued
    split at queued
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at queued
      exact UInt64.le_trans activation queued.2
    · simp only [Bool.and_eq_true, beq_iff_eq] at queued
      exact UInt64.le_of_eq queued.2.symm
  · cases ok
    exact ⟨rfl, rfl, rfl, eligible⟩

/-- A whole minimum effective balance survives an update backed by that much balance. -/
private theorem updatedEffectiveBalance_minimum {cap balance effective result : Gwei}
    (aligned : preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (old : preset.MAX_EFFECTIVE_BALANCE ≤ effective)
    (funded : preset.MAX_EFFECTIVE_BALANCE ≤ balance)
    (capped : preset.MAX_EFFECTIVE_BALANCE ≤ cap)
    (updated : updatedEffectiveBalance preset cap balance effective = .ok result) :
    preset.MAX_EFFECTIVE_BALANCE ≤ result := by
  rcases updatedEffectiveBalance_cases updated with rfl | rfl
  · exact old
  · apply UInt64.le_iff_toNat_le.mpr
    rw [Uint64.toNat_min, toNat_rounded]
    apply Nat.le_min.mpr
    constructor
    · have whole := congrArg UInt64.toNat aligned
      simp only [UInt64.toNat_mod, UInt64.toNat_zero] at whole
      simpa only [whole, Nat.sub_zero] using
        Base.rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (UInt64.le_iff_toNat_le.mp funded)
    · exact UInt64.le_iff_toNat_le.mp capped

private theorem ScheduledFree.transfer {f h : Fork}
    {s : BeaconState preset f} {t : BeaconState preset h}
    (held : ScheduledFree s)
    (forward : getCurrentEpoch s ≤ getCurrentEpoch t)
    (same : t.validators.data = s.validators.data)
    (balances : ∀ (i : Nat) (v : Validator) (b : Gwei),
      s.validators.data[i]? = some v →
      (getCurrentEpoch s).toNat + 1 < v.activationEpoch.toNat →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH → s.balances.data[i]? = some b →
      v.effectiveBalance ≤ b →
      ∃ c, t.balances.data[i]? = some c ∧ v.effectiveBalance ≤ c) :
    ScheduledFree t := by
  intro i v found future assigned
  have before := same ▸ found
  have pending : (getCurrentEpoch s).toNat < v.activationEpoch.toNat :=
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp forward) future
  obtain ⟨minimum, funding, unslashed⟩ :=
    held i v before pending assigned
  refine ⟨minimum, ?_, unslashed⟩
  intro distant
  have pendingFar : (getCurrentEpoch s).toNat + 1 < v.activationEpoch.toNat := by
    have mono := UInt64.le_iff_toNat_le.mp forward
    omega
  obtain ⟨b, read, low⟩ := funding pendingFar
  exact balances i v b before pendingFar assigned read low

private theorem ScheduledFree.increase {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : ScheduledFree s)
    (ok : increaseBalance s index amount = .ok t) : ScheduledFree t := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  apply held.transfer (t := s.putBalance index.toNat inside
    (s.balances.data[index.toNat] + amount)) (UInt64.le_refl _) rfl
  intro i v b _ _ _ read low
  by_cases same : index.toNat = i
  · subst i
    have equal := Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans read)
    subst b
    refine ⟨s.balances.data[index.toNat] + amount, by simp [BeaconState.putBalance], ?_⟩
    apply UInt64.le_trans low
    apply UInt64.le_iff_toNat_le.mpr
    rw [Uint64.toNat_add_of_lt fits]
    omega
  · refine ⟨b, ?_, low⟩
    simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same] using read

private theorem ScheduledFree.decrease {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : ScheduledFree s)
    (active : ∀ v, s.validators.data[index.toNat]? = some v →
      v.activationEpoch ≤ getCurrentEpoch s)
    (ok : decreaseBalance s index amount = .ok t) : ScheduledFree t := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  apply held.transfer (t := s.putBalance index.toNat inside
    (Uint64.saturatingSub s.balances.data[index.toNat] amount))
    (UInt64.le_refl _) rfl
  intro i v b found future _ read low
  have different : index.toNat ≠ i := by
    rintro rfl
    have le := UInt64.le_iff_toNat_le.mp (active v found)
    omega
  refine ⟨b, ?_, low⟩
  simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set, different] using read

private theorem ScheduledFree.setBalance {f : Fork}
    {s t : BeaconState preset f} {index amount : UInt64}
    (held : ScheduledFree s)
    (floor : ∀ v, s.validators.data[index.toNat]? = some v →
      getCurrentEpoch s < v.activationEpoch → v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      v.effectiveBalance ≤ amount)
    (ok : s.setBalance index amount = .ok t) : ScheduledFree t := by
  obtain ⟨inside, rfl⟩ := setBalance_ok ok
  apply held.transfer (t := s.putBalance index.toNat inside amount) (UInt64.le_refl _) rfl
  intro i v b found distant assigned read low
  by_cases same : index.toNat = i
  · subst i
    exact ⟨amount, by simp [BeaconState.putBalance],
      floor v found (UInt64.lt_iff_toNat_lt.mpr (by omega)) assigned⟩
  · refine ⟨b, ?_, low⟩
    simpa [BeaconState.putBalance, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same] using read

private theorem ScheduledFree.effective {f : Fork}
    {s t : BeaconState preset f} {i : Nat} {v : Validator} {balance result : Gwei}
    (held : ScheduledFree s ((getCurrentEpoch s).toNat + 1))
    (aligned : preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (caps : ∀ v ∈ s.validators.data,
      preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset f v)
    (found : getValidatorAt s i = .ok v) (read : getBalanceAt s i = .ok balance)
    (scalar : updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v)
      balance v.effectiveBalance = .ok result)
    (set : s.setValidatorAt i { v with effectiveBalance := result } = .ok t) :
    ScheduledFree t ((getCurrentEpoch s).toNat + 1) := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j w located future assigned
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at located
  split at located
  · rename_i equal
    subst j
    cases located
    obtain ⟨minimum, funding, unslashed⟩ :=
      held i v (getValidatorAt_eq_ok_iff.mp found) future assigned
    obtain ⟨b, owned, funded⟩ := funding future
    have equal := Option.some.inj (owned.symm.trans (getBalanceAt_eq_ok_iff.mp read))
    subst b
    refine ⟨updatedEffectiveBalance_minimum aligned minimum (UInt64.le_trans minimum funded)
      (caps v (mem_of_getValidatorAt found)) scalar, fun _ => ⟨balance, owned, ?_⟩, unslashed⟩
    rcases updatedEffectiveBalance_eq_or_le scalar with rfl | ⟨lower, _⟩
    · exact funded
    · exact lower
  · exact held j w located future assigned

private theorem ScheduledFree.setValidatorAt {f : Fork}
    {s t : BeaconState preset f} {i : Nat} {w : Validator}
    (held : ScheduledFree s) (set : s.setValidatorAt i w = .ok t)
    (kept : getCurrentEpoch s < w.activationEpoch →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH →
      preset.MAX_EFFECTIVE_BALANCE ≤ w.effectiveBalance ∧
        ((getCurrentEpoch s).toNat + 1 < w.activationEpoch.toNat →
          ∃ b, s.balances.data[i]? = some b ∧ w.effectiveBalance ≤ b) ∧ w.slashed = false) :
    ScheduledFree t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j old read future assigned
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at read
  split at read
  · rename_i equal
    subst j
    cases read
    exact kept (UInt64.lt_iff_toNat_lt.mpr future) assigned
  · exact held j old read future assigned

private theorem ScheduledFree.setValidatorAt_kept {f : Fork}
    {s t : BeaconState preset f} {i : Nat} {v w : Validator}
    (held : ScheduledFree s) (found : getValidatorAt s i = .ok v)
    (set : s.setValidatorAt i w = .ok t)
    (epoch : w.activationEpoch = v.activationEpoch)
    (effective : w.effectiveBalance = v.effectiveBalance)
    (flag : w.slashed = v.slashed) : ScheduledFree t := by
  apply held.setValidatorAt set
  intro future assigned
  obtain ⟨minimum, funding, unslashed⟩ := held i v
    (getValidatorAt_eq_ok_iff.mp found)
    (by simpa only [epoch] using UInt64.lt_iff_toNat_lt.mp future) (epoch ▸ assigned)
  simpa only [epoch, effective, flag] using And.intro minimum (And.intro funding unslashed)

private theorem ScheduledFree.add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (held : ScheduledFree s) (matched : BalancesMatch s)
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    ScheduledFree t := by
  obtain ⟨validators, balances⟩ := addValidatorToRegistry_push ok matched
  have slot : t.slot = s.slot := addValidatorToRegistry_slot ok
  intro i v found future assigned
  rw [validators, Array.getElem?_push] at found
  split at found
  · cases found
    exact (assigned rfl).elim
  · rename_i different
    have input := held i v found (by simpa only [getCurrentEpoch, slot] using future) assigned
    refine ⟨input.1, ?_, input.2.2⟩
    intro distant
    obtain ⟨b, located, low⟩ := input.2.1 (by simpa only [getCurrentEpoch, slot] using distant)
    refine ⟨b, ?_, low⟩
    rw [balances, Array.getElem?_push]
    split
    · rename_i equal
      have sizes : s.balances.data.size = s.validators.data.size := matched
      exact (different (equal.trans sizes)).elim
    · exact located

private theorem UnassignedEligibleBalance.effective {f : Fork}
    {s t : BeaconState preset f} {i : Nat} {v : Validator} {balance result : Gwei}
    (held : UnassignedEligibleBalance s)
    (aligned : preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (caps : ∀ v ∈ s.validators.data,
      preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset f v)
    (found : getValidatorAt s i = .ok v) (read : getBalanceAt s i = .ok balance)
    (scalar : updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v)
      balance v.effectiveBalance = .ok result)
    (set : s.setValidatorAt i { v with effectiveBalance := result } = .ok t) :
    UnassignedEligibleBalance t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j w located pending
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at located
  split at located
  · rename_i equal
    subst j
    cases located
    obtain ⟨⟨b, owned, funded⟩, eligible, unslashed⟩ :=
      held i v (getValidatorAt_eq_ok_iff.mp found) pending
    have equal := Option.some.inj (owned.symm.trans (getBalanceAt_eq_ok_iff.mp read))
    subst b
    refine ⟨⟨balance, owned, ?_⟩, ?_, unslashed⟩
    · rcases updatedEffectiveBalance_eq_or_le scalar with rfl | ⟨lower, _⟩
      · exact funded
      · exact lower
    · intro queued
      have old := eligible queued
      exact updatedEffectiveBalance_minimum aligned old (UInt64.le_trans old funded)
        (caps v (mem_of_getValidatorAt found)) scalar
  · exact held j w located pending

private theorem UnassignedEligibleBalance.withdrawals {f : Fork}
    {s t : BeaconState preset f} {capella : .shapella ≤ f}
    {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (held : UnassignedEligibleBalance s)
    (same : t.validators.data = s.validators.data)
    (capped : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (unwithdrawable : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → getCurrentEpoch s < v.withdrawableEpoch)
    (unqueued : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH → ∀ electra : .pectra ≤ f,
        ∀ pending ∈ (s.pendingPartialWithdrawals electra).data,
          pending.validatorIndex.toNat ≠ i)
    (ok : processWithdrawals s capella payload = .ok t) : UnassignedEligibleBalance t := by
  apply held.transfer same
  intro i v b found pending read low
  obtain ⟨later, located, retained⟩ := processWithdrawals_capped ok found
    (unwithdrawable i v found pending) (unqueued i v found pending) b read
  refine ⟨later, located, ?_⟩
  have bound := capped v (Array.mem_of_getElem? found)
  exact UInt64.le_trans (by
      apply UInt64.le_iff_toNat_le.mpr
      rw [Uint64.toNat_min]
      exact Nat.le_min.mpr ⟨UInt64.le_iff_toNat_le.mp low, UInt64.le_iff_toNat_le.mp bound⟩)
    (UInt64.le_trans retained (by
      apply UInt64.le_iff_toNat_le.mpr
      rw [Uint64.toNat_min]
      exact Nat.min_le_left _ _))

private theorem UnassignedEligibleBalance.ineligible {f : Fork} {s : BeaconState preset f}
    {i : Nat} {v : Validator} (held : UnassignedEligibleBalance s)
    (found : s.validators.data[i]? = some v) (pending : v.activationEpoch = FAR_FUTURE_EPOCH) :
    isEligibleValidator (getPreviousEpoch s) v = .ok false := by
  have unslashed := (held i v found pending).2.2
  have inactive : isActiveValidator v (getPreviousEpoch s) = false := by
    simp only [isActiveValidator, pending, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases later : FAR_FUTURE_EPOCH ≤ getPreviousEpoch s
    · apply Or.inr
      have bound := v.exitEpoch.toNat_lt
      have high := UInt64.le_iff_toNat_le.mp later
      intro less
      have low := UInt64.lt_iff_toNat_lt.mp less
      change 18446744073709551615 ≤ (getPreviousEpoch s).toNat at high
      omega
    · exact Or.inl later
  simp [isEligibleValidator, inactive, unslashed, pure, Except.pure]

private theorem rewardsAltair_ineligible_balance {f : Fork}
    {s t : BeaconState preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (ok : processRewardsAndPenalties config s = .ok t) {i : Nat} {v : Validator} {b : Gwei}
    (found : s.validators.data[i]? = some v)
    (ineligible : isEligibleValidator (getPreviousEpoch s) v = .ok false)
    (read : s.balances.data[i]? = some b) : t.balances.data[i]? = some b := by
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · obtain rfl := Except.ok.inj ((processRewardsAndPenalties_genesis config genesis).symm.trans ok)
    exact read
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have equal : s.validators.data[i] = v := (Array.getElem?_eq_some_iff.mp found).2
  obtain ⟨flags, inactivity, flagged, penalized, balances⟩ :=
    processRewardsAndPenalties_balances_of_altair altair genesis ok
  have zero (delta) (member : delta ∈ flags ++ [inactivity]) :
      delta.1.getD i 0 = 0 ∧ delta.2.getD i 0 = 0 := by
    rcases List.mem_append.mp member with flag | last
    · obtain ⟨j, _, computed⟩ := mapM_ok_mem flagged _ flag
      obtain ⟨_, _, _, _, _, _, entries⟩ :=
        getFlagIndexDeltas_getD (s.validators.bound early) computed
      obtain ⟨eligible, tested, empty, _⟩ := entries i inside
      rw [equal, ineligible, Except.ok.injEq] at tested
      exact empty tested.symm
    · obtain rfl := List.mem_singleton.mp last
      obtain ⟨_, _, entries⟩ := getInactivityPenaltyDeltas_getD_of_altair altair
        (s.validators.bound early) penalized
      obtain ⟨eligible, tested, reward, penalty, _⟩ := entries i inside
      rw [equal, ineligible, Except.ok.injEq] at tested
      exact ⟨reward, penalty (.inl tested.symm)⟩
  have folded : (flags ++ [inactivity]).foldl (fun balance delta =>
      Uint64.saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) b = b := by
    have unchanged : ∀ (ds : List (Array Gwei × Array Gwei)),
        (∀ d ∈ ds, d.1.getD i 0 = 0 ∧ d.2.getD i 0 = 0) →
        ds.foldl (fun balance delta =>
          Uint64.saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) b = b := by
      intro ds
      induction ds with
      | nil => exact fun _ => rfl
      | cons d ds ih =>
        intro empty
        obtain ⟨reward, penalty⟩ := empty d List.mem_cons_self
        simp only [List.foldl_cons, reward, penalty, UInt64.add_zero]
        have unchanged : Uint64.saturatingSub b 0 = b := by
          simp [Uint64.saturatingSub]
          exact fun zero => zero.symm
        rw [unchanged]
        exact ih (fun d member => empty d (List.mem_cons_of_mem _ member))
    exact unchanged _ zero
  have value := (balances i).1 inside
  rw [read] at value
  change t.balances.data[i]? = some _ at value
  dsimp only at value
  rw [folded] at value
  exact value

private theorem UnassignedEligibleBalance.rewardsAltair_balance {f : Fork}
    {s t : BeaconState preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) {i : Nat} {v : Validator} {b : Gwei}
    (found : s.validators.data[i]? = some v) (pending : v.activationEpoch = FAR_FUTURE_EPOCH)
    (read : s.balances.data[i]? = some b) : t.balances.data[i]? = some b :=
  rewardsAltair_ineligible_balance altair early ok found (held.ineligible found pending) read

private theorem ScheduledFree.ineligible {f : Fork} {s : BeaconState preset f}
    (held : ScheduledFree s)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (future : getCurrentEpoch s < v.activationEpoch)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    isEligibleValidator (getPreviousEpoch s) v = .ok false := by
  have unslashed := (held i v found (UInt64.lt_iff_toNat_lt.mp future) assigned).2.2
  have inactive : isActiveValidator v (getPreviousEpoch s) = false := by
    simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    left
    exact UInt64.not_le.mpr
      (UInt64.lt_of_le_of_lt (getPreviousEpoch_le s) future)
  simp [isEligibleValidator, inactive, unslashed, pure, Except.pure]

private theorem ScheduledFree.rewardsAltair {f : Fork}
    {s t : BeaconState preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (held : ScheduledFree s)
    (ok : processRewardsAndPenalties config s = .ok t) : ScheduledFree t := by
  have same : t.validators.data = s.validators.data := by
    rw [processRewardsAndPenalties_frame ok]
  have slot : t.slot = s.slot := by rw [processRewardsAndPenalties_frame ok]
  apply held.transfer (t := t)
    (by simp only [getCurrentEpoch, slot, UInt64.le_refl])
    same _
  intro i v b found future assigned read low
  exact ⟨b, rewardsAltair_ineligible_balance altair early ok found
    (held.ineligible found (UInt64.lt_iff_toNat_lt.mpr (by omega)) assigned) read, low⟩

private theorem UnassignedEligibleBalance.rewardsAltair {f : Fork}
    {s t : BeaconState preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) : UnassignedEligibleBalance t := by
  apply held.transfer (by rw [processRewardsAndPenalties_frame ok])
  intro i v b found pending read low
  exact ⟨b, held.rewardsAltair_balance altair early ok found pending read, low⟩

private theorem preKeyCharge_rewardsAltair {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (altair : .altair ≤ f) (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  have registry : t.validators.data = s.validators.data := by
    rw [processRewardsAndPenalties_frame ok]
  intro i
  cases found : s.validators.data[i]? with
  | none => simp only [preKeyCharge, registry, found, Option.map_none, Option.getD_none]
  | some v =>
    by_cases pending : v.activationEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨⟨b, read, _⟩, _⟩ := held i v found pending
      have same := held.rewardsAltair_balance altair early ok found pending read
      simp only [preKeyCharge, registry, found, read, same]
    · simp only [preKeyCharge, registry, found, Option.map_some, pending, ↓reduceIte]

private theorem preKeyCharge_slashings {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) (ok : processSlashings s = .ok t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i :=
  preKeyCharge_notRaised candidate (by rw [processSlashings_frame ok])
    (balanceNotRaised_processSlashings ok)

private theorem rewardsPhase0_ineligible_balance {f : Fork}
    {s t : BeaconState preset f} (before : f < .altair)
    (ok : processRewardsAndPenalties config s = .ok t) {i : Nat} {v : Validator} {b : Gwei}
    (found : s.validators.data[i]? = some v)
    (ineligible : isEligibleValidator (getPreviousEpoch s) v = .ok false)
    (read : s.balances.data[i]? = some b) :
    ∃ c, t.balances.data[i]? = some c ∧ b ≤ c := by
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · obtain rfl := Except.ok.inj ((processRewardsAndPenalties_genesis config genesis).symm.trans ok)
    exact ⟨b, read, UInt64.le_refl _⟩
  have early : f < .glamsterdam := Nat.lt_trans before (by decide)
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have equal : s.validators.data[i] = v := (Array.getElem?_eq_some_iff.mp found).2
  obtain ⟨rewards, penalties, deltas, balances⟩ :=
    processRewardsAndPenalties_balances_of_lt_altair before genesis ok
  obtain ⟨source, target, head, inclusion, inactivity, sourced, targeted, headed,
    included, penalized, entries⟩ := getAttestationDeltas_getD before deltas
  have component {attestations : Array (PendingAttestation preset)}
      {deltas : Array Gwei × Array Gwei}
      (computed : getAttestationComponentDeltas s attestations = .ok deltas) :
      deltas.2.getD i 0 = 0 := by
    obtain ⟨_, _, _, _, _, _, entries⟩ :=
      getAttestationComponentDeltas_getD (s.validators.bound early) computed
    obtain ⟨eligible, tested, empty, _⟩ := entries i inside
    rw [equal, ineligible, Except.ok.injEq] at tested
    exact (empty tested.symm).2
  have sourceZero : source.2.getD i 0 = 0 := by
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp sourced
    exact component computed
  have targetZero : target.2.getD i 0 = 0 := by
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp targeted
    exact component computed
  have headZero : head.2.getD i 0 = 0 := by
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp headed
    exact component computed
  have inactivityZero : inactivity.2.getD i 0 = 0 := by
    obtain ⟨_, leak, _, quiet, leaking⟩ := getInactivityPenaltyDeltas_getD_of_lt_altair
      before (s.validators.bound early) penalized
    cases leak with
    | false => exact quiet rfl i
    | true =>
      obtain ⟨_, _, _, _, _, _, _, _, entries⟩ := leaking rfl
      obtain ⟨eligible, tested, empty, _⟩ := entries i inside
      rw [equal, ineligible, Except.ok.injEq] at tested
      exact empty tested.symm
  have penaltyZero : penalties.getD i 0 = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [sourceZero, targetZero, headZero, inactivityZero] using (entries i inside).2
  obtain ⟨old, located, fits, value⟩ := (balances i).1 inside
  obtain rfl := Option.some.inj (read.symm.trans located)
  refine ⟨b + rewards.getD i 0, ?_, ?_⟩
  · have zero (amount : Gwei) : Uint64.saturatingSub amount 0 = amount := by
      simp [Uint64.saturatingSub]
      exact fun equal => equal.symm
    simpa only [penaltyZero, zero] using value
  · apply UInt64.le_iff_toNat_le.mpr
    rw [Uint64.toNat_add_of_lt fits]
    omega

private theorem UnassignedEligibleBalance.rewards {f : Fork}
    {s t : BeaconState preset f} (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s)
    (ok : processRewardsAndPenalties config s = .ok t) : UnassignedEligibleBalance t := by
  by_cases altair : .altair ≤ f
  · exact held.rewardsAltair altair early ok
  apply held.transfer (by rw [processRewardsAndPenalties_frame ok])
  intro i v b found pending read low
  obtain ⟨c, located, raised⟩ := rewardsPhase0_ineligible_balance (Nat.lt_of_not_le altair)
    ok found (held.ineligible found pending) read
  exact ⟨c, located, UInt64.le_trans low raised⟩

private theorem ScheduledFree.rewards {f : Fork}
    {s t : BeaconState preset f} (early : f < .glamsterdam)
    (held : ScheduledFree s)
    (ok : processRewardsAndPenalties config s = .ok t) : ScheduledFree t := by
  by_cases altair : .altair ≤ f
  · exact held.rewardsAltair altair early ok
  have same : t.validators.data = s.validators.data := by
    rw [processRewardsAndPenalties_frame ok]
  have slot : t.slot = s.slot := by rw [processRewardsAndPenalties_frame ok]
  apply held.transfer (t := t)
    (by simp only [getCurrentEpoch, slot, UInt64.le_refl])
    same _
  intro i v b found future assigned read low
  obtain ⟨c, located, raised⟩ := rewardsPhase0_ineligible_balance (Nat.lt_of_not_le altair)
    ok found (held.ineligible found (UInt64.lt_iff_toNat_lt.mpr (by omega)) assigned) read
  exact ⟨c, located, UInt64.le_trans low raised⟩

private theorem slashings_unslashed_balance {f : Fork}
    {s t : BeaconState preset f} (early : f < .glamsterdam)
    (ok : processSlashings s = .ok t) {i : Nat} {v : Validator} {b : Gwei}
    (found : s.validators.data[i]? = some v) (unslashed : v.slashed = false)
    (read : s.balances.data[i]? = some b) : t.balances.data[i]? = some b := by
  have notDue : ¬ SlashingPenaltyDue preset (getCurrentEpoch s) v := by
    intro due
    simp [SlashingPenaltyDue, unslashed] at due
  by_cases electra : .pectra ≤ f
  · obtain ⟨_, _, _, _, balances⟩ := processSlashings_balances_of_electra electra
      (s.validators.bound early) ok
    obtain ⟨w, located, value⟩ := (balances i).1 (Array.getElem?_eq_some_iff.mp found).1
    obtain rfl := Option.some.inj (found.symm.trans located)
    simpa [read, notDue] using value
  · obtain ⟨_, _, _, _, balances⟩ := processSlashings_balances_of_lt_electra
      (Nat.lt_of_not_le electra) ok
    obtain ⟨w, located, value⟩ := (balances i).1 (Array.getElem?_eq_some_iff.mp found).1
    obtain rfl := Option.some.inj (found.symm.trans located)
    simpa [read, notDue] using value

private theorem UnassignedEligibleBalance.slashings {f : Fork}
    {s t : BeaconState preset f} (early : f < .glamsterdam)
    (held : UnassignedEligibleBalance s) (ok : processSlashings s = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.transfer (by rw [processSlashings_frame ok])
  intro i v b found pending read low
  exact ⟨b, slashings_unslashed_balance early ok found (held i v found pending).2.2 read, low⟩

private theorem ScheduledFree.slashings {f : Fork}
    {s t : BeaconState preset f} (early : f < .glamsterdam)
    (held : ScheduledFree s) (ok : processSlashings s = .ok t) :
    ScheduledFree t := by
  have same : t.validators.data = s.validators.data := by rw [processSlashings_frame ok]
  have slot : t.slot = s.slot := by rw [processSlashings_frame ok]
  apply held.transfer (t := t)
    (by simp only [getCurrentEpoch, slot, UInt64.le_refl]) same _
  intro i v b found future assigned read low
  exact ⟨b, slashings_unslashed_balance early ok found
    (held i v found (by omega) assigned).2.2 read, low⟩

private theorem attestation_balance_not_lowered {f : Fork}
    {s t : BeaconState preset f} {parentSlot : Slot} {attestation : Attestation preset f}
    (ok : processAttestation config checks s parentSlot attestation = .ok t)
    (i : Nat) (b : Gwei) (read : s.balances.data[i]? = some b) :
    ∃ c, t.balances.data[i]? = some c ∧ b ≤ c := by
  by_cases altair : .altair ≤ f
  · rw [processAttestation_of_altair altair] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, balances⟩ :=
      processAttestationAltair_balance ok
    obtain ⟨now, located, value⟩ := balances i b read
    refine ⟨now, located, UInt64.le_iff_toNat_le.mpr ?_⟩
    rw [value]
    exact Nat.le_add_right _ _
  · unfold processAttestation at ok
    simp only [altair, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
    have kept := recordPendingAttestation_ok recorded
    split at kept <;>
    · obtain ⟨_, rest⟩ := kept
      exact ⟨b, by rw [show _ = s.balances from congrArg (·.balances) rest]; exact read,
        UInt64.le_refl _⟩

private theorem UnassignedEligibleBalance.attestation {f : Fork}
    {s t : BeaconState preset f} {parentSlot : Slot} {attestation : Attestation preset f}
    (held : UnassignedEligibleBalance s)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.transfer (congrArg (·.data) (processAttestation_registry ok).1)
  intro i v b _ _ read low
  obtain ⟨c, located, raised⟩ := attestation_balance_not_lowered ok i b read
  exact ⟨c, located, UInt64.le_trans low raised⟩

private theorem ScheduledFree.attestation {f : Fork}
    {s t : BeaconState preset f} {parentSlot : Slot} {attestation : Attestation preset f}
    (held : ScheduledFree s)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    ScheduledFree t := by
  have slot := (frame_processAttestation ok).slot
  apply held.transfer (t := t)
    (by simp only [getCurrentEpoch, slot, UInt64.le_refl])
    (congrArg (·.data) (processAttestation_registry ok).1)
  intro i v b _ _ _ read low
  obtain ⟨c, located, raised⟩ := attestation_balance_not_lowered ok i b read
  exact ⟨c, located, UInt64.le_trans low raised⟩

private theorem sync_member_not_unassigned {f : Fork} {s : BeaconState preset f}
    {altair : .altair ≤ f} {members : Array ValidatorIndex}
    (mapped : (s.currentSyncCommittee altair).value.pubkeys.toArray.mapM
      (validatorIndexOfPubkey s) = .ok members)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (excluded : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      key ≠ v.pubkey) {member : ValidatorIndex} (named : member ∈ members.toList) :
    member.toNat ≠ i := by
  intro same
  have onList : (s.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
      (validatorIndexOfPubkey s) = .ok members.toList := by
    rw [← Array.toList_mapM, mapped]
    rfl
  obtain ⟨key, keyed, image⟩ := mapM_ok_mem onList member named
  unfold validatorIndexOfPubkey at image
  split at image
  · rename_i position located
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at image
    obtain ⟨there, equal⟩ := Array.findIdx?_eq_some_iff_getElem.mp located
    rw [(Uint64.ofNatChecked_ok_iff.mp image).2] at same
    subst i
    rw [Array.getElem?_eq_getElem there, Option.some.injEq] at found
    subst v
    exact excluded key (by simpa using keyed) (beq_iff_eq.mp equal.1).symm
  · cases image

private theorem sync_excluded_balance_not_lowered {f : Fork}
    {s t : BeaconState preset f} {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t)
    {i : Nat} {v : Validator} {b : Gwei}
    (found : s.validators.data[i]? = some v)
    (excluded : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList, key ≠ v.pubkey)
    (read : s.balances.data[i]? = some b) :
    ∃ c, t.balances.data[i]? = some c ∧ b ≤ c := by
  obtain ⟨reward, proposerReward, members, chosen, _, _, mapped, _, balances⟩ :=
    processSyncAggregate_balance ok
  obtain ⟨final, located, value⟩ := balances i b read
  have apart : ∀ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.1.toNat ≠ i := by
    intro member inside
    exact sync_member_not_unassigned mapped found excluded
      (List.of_mem_zip (by simpa only [Array.toList_zip] using inside)).1
  refine ⟨final, located, UInt64.le_iff_toNat_le.mpr ?_⟩
  rw [value]
  apply List.foldlRecOn (motive := fun n : Nat => b.toNat ≤ n)
    (members.zip aggregate.syncCommitteeBits.bits.toArray).toList _ (Nat.le_refl _)
  intro balance previous member inside
  by_cases signed : member.2 = true
  · simp only [signed, ↓reduceIte]
    omega
  · simpa [signed, apart member inside] using previous

private theorem UnassignedEligibleBalance.sync {f : Fork}
    {s t : BeaconState preset f} {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (held : UnassignedEligibleBalance s)
    (excluded : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH →
      ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList, key ≠ v.pubkey)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    UnassignedEligibleBalance t := by
  obtain ⟨_, shape⟩ := processSyncAggregate_eq ok
  apply held.transfer (by rw [shape])
  intro i v b found pending read low
  obtain ⟨c, located, raised⟩ :=
    sync_excluded_balance_not_lowered ok found (excluded i v found pending) read
  exact ⟨c, located, UInt64.le_trans low raised⟩

/-- Ordered preset caps and retained compounding credentials make a validator's cap monotone. -/
private theorem withdrawalMaxEffectiveBalance_mono {f h : Fork} {v w : Validator}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h)
    (credentials : hasCompoundingWithdrawalCredential v = true →
      hasCompoundingWithdrawalCredential w = true) :
    withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  split <;> rename_i before
  · have later : Fork.pectra ≤ h := Nat.le_trans before forks
    rw [ite_eq_left later]
    split <;> rename_i compound
    · rw [ite_eq_left (credentials compound)]
      exact UInt64.le_refl _
    · split
      · exact compounding
      · exact UInt64.le_refl _
  · split
    · split
      · exact UInt64.le_trans activation compounding
      · exact activation
    · exact UInt64.le_refl _

private theorem capped_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v : Validator}
    (capped : ∀ w ∈ s.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (ok : s.setValidatorAt i v = .ok t) :
    ∀ w ∈ t.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  intro w member
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact capped w old
  · exact bound

/-- Each end of a queued consolidation has assigned activation at its stable index. -/
def AssignedTargets {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingConsolidations electra).data.toList,
    ∀ index ∈ [entry.sourceIndex, entry.targetIndex],
      ∃ v, s.validators.data[index.toNat]? = some v ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH

/-- The ends of the queued consolidations are assigned, and reached when `reached` holds. -/
private def TargetsAt {f : Fork} (reached : Prop) (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingConsolidations electra).data.toList,
    ∀ index ∈ [entry.sourceIndex, entry.targetIndex],
      ∃ v, s.validators.data[index.toNat]? = some v ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
          (reached → v.activationEpoch ≤ getCurrentEpoch s)

private theorem TargetsAt.old {f : Fork} {s : BeaconState preset f} {reached : Prop}
    (held : TargetsAt reached s) : AssignedTargets s := by
  intro electra entry member index named
  obtain ⟨v, found, assigned, _⟩ := held electra entry member index named
  exact ⟨v, found, assigned⟩

private theorem AssignedTargets.at {f : Fork} {s : BeaconState preset f}
    (held : AssignedTargets s) : TargetsAt False s := by
  intro electra entry member index named
  obtain ⟨v, found, assigned⟩ := held electra entry member index named
  exact ⟨v, found, assigned, fun impossible => impossible.elim⟩

private theorem TargetsAt.transfer {f : Fork} {s t : BeaconState preset f} {reached : Prop}
    (held : TargetsAt reached s) (life : RegistryLifecycle s t)
    (forward : getCurrentEpoch s ≤ getCurrentEpoch t)
    (subset : ∀ electra : .pectra ≤ f,
      ∀ entry ∈ (t.pendingConsolidations electra).data.toList,
        entry ∈ (s.pendingConsolidations electra).data.toList) : TargetsAt reached t := by
  intro electra entry member index named
  obtain ⟨v, found, assigned, active⟩ := held electra entry (subset electra entry member) index
    named
  obtain ⟨w, read, kept⟩ := life.validators index.toNat v found
  refine ⟨w, read, (kept.activationEpoch assigned) ▸ assigned, fun reach => ?_⟩
  have reached := active reach
  rw [← kept.activationEpoch assigned] at reached
  exact UInt64.le_trans reached forward

private theorem UnassignedEligibleBalance.consolidations {f : Fork}
    {s t : BeaconState preset f} {electra : .pectra ≤ f}
    (held : UnassignedEligibleBalance s) (sources : AssignedTargets s)
    (ok : processPendingConsolidations s electra = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.transfer (congrArg (·.data) (processPendingConsolidations_kept ok).1)
  intro i v b found pending read low
  have excluded (entry : PendingConsolidation)
      (member : entry ∈ (s.pendingConsolidations electra).data) :
      entry.sourceIndex.toNat ≠ i := by
    intro same
    obtain ⟨w, located, assigned⟩ := sources electra entry (by simpa using member)
      entry.sourceIndex (by simp)
    rw [same, found, Option.some.injEq] at located
    subst w
    exact assigned pending
  obtain ⟨now, located, rose⟩ := processPendingConsolidations_balanceNotLowered ok excluded b read
  exact ⟨now, located, UInt64.le_trans low rose⟩

private theorem ScheduledFree.consolidations {f : Fork}
    {s t : BeaconState preset f} {electra : .pectra ≤ f}
    (held : ScheduledFree s) (sources : TargetsAt True s)
    (ok : processPendingConsolidations s electra = .ok t) :
    ScheduledFree t := by
  apply held.transfer (t := t)
    (by simp only [getCurrentEpoch, (frame_processPendingConsolidations ok).slot, UInt64.le_refl])
    (congrArg (·.data) (processPendingConsolidations_kept ok).1)
  intro i v b found distant _ read low
  have excluded (entry : PendingConsolidation)
      (member : entry ∈ (s.pendingConsolidations electra).data) :
      entry.sourceIndex.toNat ≠ i := by
    intro same
    obtain ⟨w, located, _, active⟩ := sources electra entry (by simpa using member)
      entry.sourceIndex (by simp)
    rw [same, found, Option.some.injEq] at located
    subst w
    exact UInt64.not_le.mpr (UInt64.lt_iff_toNat_lt.mpr (by omega)) (active trivial)
  obtain ⟨now, located, rose⟩ := processPendingConsolidations_balanceNotLowered ok excluded b read
  exact ⟨now, located, UInt64.le_trans low rose⟩

private theorem property_of_key_provenance {f : Fork} {s : BeaconState preset f}
    (P : Validator → Prop)
    {keys : List Cryptography.Bls.BLSPubkey} (unique : PubkeysDistinct s)
    (assigned : ∀ key ∈ keys,
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
        P v) :
    ∀ key ∈ keys, ∀ (i : Nat) (v : Validator),
      s.validators.data[i]? = some v → v.pubkey = key →
      P v := by
  intro key member i v found equal
  obtain ⟨j, w, read, keyed, active⟩ := assigned key member
  obtain rfl := unique.index_eq found read (equal.trans keyed.symm)
  obtain rfl := Option.some.inj (found.symm.trans read)
  exact active

private theorem UnassignedEligibleBalance.sync_of_provenance {f : Fork}
    {s t : BeaconState preset f} {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (held : UnassignedEligibleBalance s) (unique : PubkeysDistinct s)
    (assigned : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    UnassignedEligibleBalance t := by
  apply held.sync (ok := ok)
  intro i v found pending key member equal
  exact property_of_key_provenance (fun v => v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    unique assigned key member i v found equal.symm pending

private theorem ScheduledFree.sync {f : Fork}
    {s t : BeaconState preset f} {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (held : ScheduledFree s) (unique : PubkeysDistinct s)
    (bounded : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.activationEpoch.toNat ≤ (getCurrentEpoch s).toNat + 1)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    ScheduledFree t := by
  obtain ⟨_, shape⟩ := processSyncAggregate_eq ok
  have slot : t.slot = s.slot := by rw [shape]
  apply held.transfer (t := t)
    (by simp only [getCurrentEpoch, slot, UInt64.le_refl]) (by rw [shape])
  intro i v b found distant _ read low
  have excluded : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      key ≠ v.pubkey := by
    intro key member equal
    have bound := property_of_key_provenance
      (fun v => v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.activationEpoch.toNat ≤ (getCurrentEpoch s).toNat + 1)
      unique bounded key member i v found equal.symm
    omega
  obtain ⟨c, located, raised⟩ := sync_excluded_balance_not_lowered ok found excluded read
  exact ⟨c, located, UInt64.le_trans low raised⟩

def AssignedPartials {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingPartialWithdrawals electra).data.toList,
    ∃ v, s.validators.data[entry.validatorIndex.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH

/-- The queued partial withdrawals are assigned, and reached when `reached` holds. -/
private def PartialsAt {f : Fork} (reached : Prop) (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingPartialWithdrawals electra).data.toList,
    ∃ v, s.validators.data[entry.validatorIndex.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ (reached → v.activationEpoch ≤ getCurrentEpoch s)

private theorem PartialsAt.old {f : Fork} {s : BeaconState preset f} {reached : Prop}
    (held : PartialsAt reached s) : AssignedPartials s := by
  intro electra entry member
  obtain ⟨v, found, assigned, _⟩ := held electra entry member
  exact ⟨v, found, assigned⟩

private theorem AssignedPartials.at {f : Fork} {s : BeaconState preset f}
    (held : AssignedPartials s) : PartialsAt False s := by
  intro electra entry member
  obtain ⟨v, found, assigned⟩ := held electra entry member
  exact ⟨v, found, assigned, fun impossible => impossible.elim⟩

private theorem PartialsAt.transfer {f : Fork} {s t : BeaconState preset f} {reached : Prop}
    (held : PartialsAt reached s) (life : RegistryLifecycle s t)
    (forward : getCurrentEpoch s ≤ getCurrentEpoch t)
    (subset : ∀ electra : .pectra ≤ f,
      ∀ entry ∈ (t.pendingPartialWithdrawals electra).data.toList,
        entry ∈ (s.pendingPartialWithdrawals electra).data.toList) : PartialsAt reached t := by
  intro electra entry member
  obtain ⟨v, found, assigned, active⟩ := held electra entry (subset electra entry member)
  obtain ⟨w, read, kept⟩ := life.validators entry.validatorIndex.toNat v found
  refine ⟨w, read, (kept.activationEpoch assigned) ▸ assigned, fun reach => ?_⟩
  have reached := active reach
  rw [← kept.activationEpoch assigned] at reached
  exact UInt64.le_trans reached forward

private theorem PartialsAt.drop {f : Fork} {s : BeaconState preset f} {reached : Prop}
    (held : PartialsAt reached s) (electra : .pectra ≤ f) (count : UInt64) :
    PartialsAt reached (updatePendingPartialWithdrawals s electra count) := by
  intro witness entry member
  apply held witness entry
  simp only [updatePendingPartialWithdrawals, Array.toList_extract,
    List.extract_eq_take_drop] at member
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

private theorem PartialsAt.increase {f : Fork} {s t : BeaconState preset f} {reached : Prop}
    {index amount : UInt64} (held : PartialsAt reached s)
    (ok : increaseBalance s index amount = .ok t) : PartialsAt reached t := by
  obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  exact held

private theorem PartialsAt.decrease {f : Fork} {s t : BeaconState preset f} {reached : Prop}
    {index amount : UInt64} (held : PartialsAt reached s)
    (ok : decreaseBalance s index amount = .ok t) : PartialsAt reached t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  exact held

private theorem PartialsAt.attestation {f : Fork} {reached : Prop}
    {s t : BeaconState preset f} {parentSlot : Slot} {attestation : Attestation preset f}
    (held : PartialsAt reached s)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    PartialsAt reached t := by
  by_cases altair : .altair ≤ f
  · rw [processAttestation_of_altair altair] at ok
    unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have flags (participation : EpochParticipation preset f) :
        PartialsAt reached (setEpochParticipation s
          (attestation.data.target.epoch == getCurrentEpoch s) participation) := by
      unfold setEpochParticipation
      split <;> exact held
    have paid := (flags _).increase raisedOk
    split at final
    · rw [recordPaymentWeight_eq final]
      exact paid
    · cases final
      exact paid
  · intro electra
    exact (altair (Nat.le_trans (by decide : Fork.altair ≤ .pectra) electra)).elim

private theorem AssignedPartials.excludes {f : Fork} {s : BeaconState preset f}
    (held : AssignedPartials s) {i : Nat} {v : Validator}
    (found : s.validators.data[i]? = some v)
    (pending : v.activationEpoch = FAR_FUTURE_EPOCH) (electra : .pectra ≤ f)
    (entry : PendingPartialWithdrawal)
    (member : entry ∈ (s.pendingPartialWithdrawals electra).data) :
    entry.validatorIndex.toNat ≠ i := by
  intro same
  obtain ⟨w, read, assigned⟩ := held electra entry
    (List.mem_toArray.mp (by simpa using member))
  rw [same, found, Option.some.injEq] at read
  subst w
  exact assigned pending

private theorem PartialsAt.excludes_scheduled {f : Fork} {s : BeaconState preset f}
    (held : PartialsAt True s) {i : Nat} {v : Validator}
    (found : s.validators.data[i]? = some v)
    (future : getCurrentEpoch s < v.activationEpoch) (electra : .pectra ≤ f)
    (entry : PendingPartialWithdrawal)
    (member : entry ∈ (s.pendingPartialWithdrawals electra).data) :
    entry.validatorIndex.toNat ≠ i := by
  intro same
  obtain ⟨w, read, _, active⟩ := held electra entry
    (List.mem_toArray.mp (by simpa using member))
  rw [same, found, Option.some.injEq] at read
  subst w
  exact UInt64.not_le.mpr future (active trivial)

private theorem PartialsAt.setValidator {f : Fork} {s t : BeaconState preset f}
    {reached : Prop} {i : ValidatorIndex} {v w : Validator} (held : PartialsAt reached s)
    (found : getValidator s i = .ok v) (set : s.setValidator i w = .ok t)
    (kept : v.activationEpoch ≠ FAR_FUTURE_EPOCH → w.activationEpoch = v.activationEpoch) :
    PartialsAt reached t := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  intro electra entry member
  obtain ⟨old, read, assigned, active⟩ := held electra entry member
  by_cases equal : entry.validatorIndex.toNat = i.toNat
  · have same := Option.some.inj ((getValidator_eq_ok_iff.mp found).symm.trans (equal ▸ read))
    subst old
    refine ⟨w, by simp [BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, equal], ?_, ?_⟩
    · rw [kept assigned]; exact assigned
    · intro reach; rw [kept assigned]; exact active reach
  · exact ⟨old, by simpa [BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, Ne.symm equal] using read,
      assigned, active⟩

private theorem unassigned_withdrawable_far {f : Fork} {s : BeaconState preset f}
    (activation : ActivationExitOrder s) (exits : ExitsOrdered s)
    {i : Nat} {v : Validator} (found : s.validators.data[i]? = some v)
    (pending : v.activationEpoch = FAR_FUTURE_EPOCH) :
    v.withdrawableEpoch = FAR_FUTURE_EPOCH := by
  have member := Array.mem_of_getElem? found
  have low := UInt64.le_iff_toNat_le.mp
    (UInt64.le_trans (activation v member) (exits v member))
  rw [pending] at low
  apply UInt64.toNat_inj.mp
  have bound := v.withdrawableEpoch.toNat_lt
  change 18446744073709551615 ≤ v.withdrawableEpoch.toNat at low
  change v.withdrawableEpoch.toNat = 18446744073709551615
  omega

private theorem UnassignedEligibleBalance.withdrawals_of_provenance {f : Fork}
    {s t : BeaconState preset f} {capella : .shapella ≤ f}
    {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (held : UnassignedEligibleBalance s) (activation : ActivationExitOrder s)
    (exits : ExitsOrdered s) (partials : AssignedPartials s)
    (same : t.validators.data = s.validators.data)
    (before : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (capped : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (ok : processWithdrawals s capella payload = .ok t) : UnassignedEligibleBalance t := by
  apply held.withdrawals same capped
    (fun i v found pending => by
      rw [unassigned_withdrawable_far activation exits found pending]
      exact before)
    (fun _ _ found pending electra entry member =>
      partials.excludes found pending electra entry member) ok

private theorem ScheduledFree.withdrawals {f : Fork}
    {s t : BeaconState preset f} {capella : .shapella ≤ f}
    {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (held : ScheduledFree s) (activation : ActivationExitOrder s)
    (exits : ExitsOrdered s) (partials : PartialsAt True s)
    (same : t.validators.data = s.validators.data)
    (capped : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (ok : processWithdrawals s capella payload = .ok t) : ScheduledFree t := by
  apply held.transfer (t := t)
    (by simp only [getCurrentEpoch, (frame_processWithdrawals ok).slot, UInt64.le_refl])
    same
  intro i v b found distant _ read low
  have member := Array.mem_of_getElem? found
  have unwithdrawable : getCurrentEpoch s < v.withdrawableEpoch := by
    exact UInt64.lt_of_lt_of_le
      (show getCurrentEpoch s < v.activationEpoch from UInt64.lt_iff_toNat_lt.mpr (by omega))
      (UInt64.le_trans (activation v member) (exits v member))
  obtain ⟨later, located, retained⟩ := processWithdrawals_capped ok found unwithdrawable
    (fun electra entry member => partials.excludes_scheduled found
      (UInt64.lt_iff_toNat_lt.mpr (by omega)) electra entry member) b read
  refine ⟨later, located, ?_⟩
  exact UInt64.le_trans (by
      apply UInt64.le_iff_toNat_le.mpr
      rw [Uint64.toNat_min]
      exact Nat.le_min.mpr ⟨UInt64.le_iff_toNat_le.mp low,
        UInt64.le_iff_toNat_le.mp (capped v member)⟩)
    (UInt64.le_trans retained (by
      apply UInt64.le_iff_toNat_le.mpr
      rw [Uint64.toNat_min]
      exact Nat.min_le_left _ _))

private theorem assigned_and_reached_of_active {v : Validator} {epoch : Epoch} {reached : Prop}
    (active : isActiveValidator v epoch = true) :
    v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ (reached → v.activationEpoch ≤ epoch) :=
  ⟨assigned_of_active active, fun _ => activationLe_of_active active⟩

private theorem assigned_and_le_of_active {v : Validator} {epoch : Epoch}
    (active : isActiveValidator v epoch = true) :
    v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ v.activationEpoch ≤ epoch :=
  ⟨assigned_of_active active, activationLe_of_active active⟩

private theorem assigned_of_slashable {v : Validator} {epoch : Epoch}
    (slashable : isSlashableValidator v epoch = true) : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at slashable
  intro far
  have less := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt slashable.1.2 slashable.2)
  rw [far] at less
  have bound := v.withdrawableEpoch.toNat_lt
  change (2 ^ 64 - 1 : Nat) < v.withdrawableEpoch.toNat at less
  omega

structure CapStep (config : Config) {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop where
  capped : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) →
    ∀ v ∈ t.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset h v
  monotone : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w
  forward : getCurrentEpoch s ≤ getCurrentEpoch t
  forks : f ≤ h
  proposers : h < .glamsterdam → AssignedProposers s → AssignedProposers t
  targets : h < .glamsterdam → AssignedTargets s → AssignedTargets t
  retired : ∀ (i : Nat) (v w : Validator), s.validators.data[i]? = some v →
    t.validators.data[i]? = some w → v.exitEpoch ≤ getCurrentEpoch s →
    v.slashed = false → v.withdrawableEpoch ≤ getCurrentEpoch s →
    w.slashed = false ∧ w.exitEpoch = v.exitEpoch ∧ w.withdrawableEpoch = v.withdrawableEpoch
  withdrawal : ∀ (i : Nat) (v w : Validator), s.validators.data[i]? = some v →
    t.validators.data[i]? = some w →
    (v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        w.withdrawableEpoch = v.withdrawableEpoch) ∧
    (0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat)
  appended : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
    ∀ j w, s.validators.data.size ≤ j → t.validators.data[j]? = some w →
      w.slashed = true → w.exitEpoch ≠ FAR_FUTURE_EPOCH
  frozen : ∀ (i : Nat) (v w : Validator), s.validators.data[i]? = some v →
    t.validators.data[i]? = some w → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
    w.exitEpoch = v.exitEpoch ∧
      (hasCompoundingWithdrawalCredential w = true →
        hasCompoundingWithdrawalCredential v = true)

theorem CapStep.refl {f : Fork} (s : BeaconState preset f) : CapStep config s s := by
  refine ⟨id, fun _ v found => ⟨v, found, UInt64.le_refl _⟩, UInt64.le_refl _,
    Nat.le_refl _, fun _ => id, fun _ => id, ?_, ?_, ?_, ?_⟩
  · intro i v w before after _ flag _
    obtain rfl := Option.some.inj (before.symm.trans after)
    exact ⟨flag, rfl, rfl⟩
  · intro i v w before after
    have eq := Option.some.inj (before.symm.trans after)
    subst w
    exact ⟨fun slashed assigned => ⟨slashed, assigned, rfl⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩
  · intro _ j w outside found _
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    omega
  · intro i v w before after _
    obtain rfl := Option.some.inj (before.symm.trans after)
    exact ⟨rfl, id⟩

theorem CapStep.trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : CapStep config s t) (two : CapStep config t u) : CapStep config s u where
  capped := two.capped ∘ one.capped
  monotone i v found := by
    obtain ⟨w, read, first⟩ := one.monotone i v found
    obtain ⟨z, read', second⟩ := two.monotone i w read
    exact ⟨z, read', UInt64.le_trans first second⟩
  forward := UInt64.le_trans one.forward two.forward
  forks := Nat.le_trans one.forks two.forks
  proposers early := two.proposers early ∘ one.proposers (Nat.lt_of_le_of_lt two.forks early)
  targets early := two.targets early ∘ one.targets (Nat.lt_of_le_of_lt two.forks early)
  retired i v z before after assigned flag withdrawn := by
    obtain ⟨w, middle, _⟩ := one.monotone i v before
    obtain ⟨flag', exit, withdrawal⟩ := one.retired i v w before middle assigned flag withdrawn
    obtain ⟨flag'', exit', withdrawal'⟩ := two.retired i w z middle after
      (exit ▸ UInt64.le_trans assigned one.forward) flag'
      (withdrawal ▸ UInt64.le_trans withdrawn one.forward)
    exact ⟨flag'', exit'.trans exit, withdrawal'.trans withdrawal⟩
  withdrawal i v z before after := by
    obtain ⟨w, middle, _⟩ := one.monotone i v before
    obtain ⟨kept, newly⟩ := one.withdrawal i v w before middle
    obtain ⟨kept', newly'⟩ := two.withdrawal i w z middle after
    constructor
    · intro slashed assigned
      obtain ⟨flag, assigned', bound⟩ := kept slashed assigned
      obtain ⟨flag', assigned'', bound'⟩ := kept' flag assigned'
      exact ⟨flag', assigned'', bound'.trans bound⟩
    · intro delay unslashed slashed
      cases flag : w.slashed with
      | false =>
        obtain ⟨assigned, bound⟩ := newly' delay flag slashed
        have forward := UInt64.le_iff_toNat_le.mp one.forward
        exact ⟨assigned, by omega⟩
      | true =>
        obtain ⟨assigned, bound⟩ := newly delay unslashed flag
        obtain ⟨_, assigned', bound'⟩ := kept' flag assigned
        exact ⟨assigned', by rw [bound']; exact bound⟩
  appended delay j z outside after slashed := by
    by_cases inside : j < t.validators.data.size
    · have middle : t.validators.data[j]? = some t.validators.data[j] :=
        Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
      generalize t.validators.data[j] = w at middle
      cases flag : w.slashed with
      | false => exact ((two.withdrawal j w z middle after).2 delay flag slashed).1
      | true =>
        exact ((two.withdrawal j w z middle after).1 flag
          (one.appended delay j w outside middle flag)).2.1
    · exact two.appended delay j z (by omega) after slashed
  frozen i v z before after assigned := by
    obtain ⟨w, middle, _⟩ := one.monotone i v before
    obtain ⟨exit, credentials⟩ := one.frozen i v w before middle assigned
    obtain ⟨exit', credentials'⟩ := two.frozen i w z middle after (exit ▸ assigned)
    exact ⟨exit'.trans exit, credentials ∘ credentials'⟩

theorem CapStep.data {f : Fork} {s t : BeaconState preset f}
    (same : t.validators.data = s.validators.data := by rfl)
    (slot : t.slot = s.slot := by rfl)
    (cache : t.proposerLookahead = s.proposerLookahead := by rfl)
    (targets : AssignedTargets s → AssignedTargets t := by
      intro held electra entry member index named
      exact ⟨_, (held electra entry member index named).choose_spec.1,
        (held electra entry member index named).choose_spec.2⟩) :
    CapStep config s t := by
  constructor
  · simpa only [same] using (id : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) → _)
  · intro i v found
    exact ⟨v, same ▸ found, UInt64.le_refl _⟩
  · rw [getCurrentEpoch, getCurrentEpoch, slot]
    exact UInt64.le_refl _
  · exact Nat.le_refl _
  · exact fun _ held => held.transfer (.of_data same) fun late => ⟨late, congrFun cache late⟩
  · exact fun _ => targets
  · intro i v w before after _ flag _
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨flag, rfl, rfl⟩
  · intro i v w before after
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨fun slashed assigned => ⟨slashed, assigned, rfl⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩
  · intro _ j w outside found _
    rw [same] at found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    omega
  · intro i v w before after _
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨rfl, id⟩

private structure CapStepR (config : Config) {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop extends CapStep config s t where
  targetsAt : h < .glamsterdam → ∀ c, TargetsAt c s → TargetsAt c t
  targets := fun early held => (targetsAt early False held.at).old

private theorem CapStepR.refl {f : Fork} (s : BeaconState preset f) : CapStepR config s s :=
  { CapStep.refl s with targetsAt := fun _ _ => id }

private theorem CapStepR.trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : CapStepR config s t) (two : CapStepR config t u) : CapStepR config s u :=
  { one.toCapStep.trans two.toCapStep with
    targetsAt := fun early c =>
      two.targetsAt early c ∘ one.targetsAt (Nat.lt_of_le_of_lt two.forks early) c }

private theorem CapStepR.data {f : Fork} {s t : BeaconState preset f}
    (same : t.validators.data = s.validators.data := by rfl)
    (slot : t.slot = s.slot := by rfl)
    (cache : t.proposerLookahead = s.proposerLookahead := by rfl)
    (targets : getCurrentEpoch s ≤ getCurrentEpoch t →
      ∀ c, TargetsAt c s → TargetsAt c t := by
      intro forward c held electra entry member index named
      obtain ⟨v, found, assigned, active⟩ := held electra entry member index named
      exact ⟨v, found, assigned, fun reach => UInt64.le_trans (active reach) forward⟩) :
    CapStepR config s t :=
  have forward : getCurrentEpoch s ≤ getCurrentEpoch t := by
    rw [getCurrentEpoch, getCurrentEpoch, slot]
    exact UInt64.le_refl _
  { CapStep.data same slot cache (fun held => (targets forward False held.at).old) with
    targetsAt := fun _ => targets forward }

private theorem CapStep.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v w : Validator} (found : getValidatorAt s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidatorAt i w = .ok t)
    (kept : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        w.withdrawableEpoch = v.withdrawableEpoch := by
      intros; exact ⟨by assumption, by assumption, rfl⟩)
    (newly : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      intro _ unslashed slashed
      exact Bool.noConfusion (unslashed.symm.trans slashed))
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      w.activationEpoch = v.activationEpoch := by intro _; rfl)
    (retired : v.exitEpoch ≤ getCurrentEpoch s → v.slashed = false →
      v.withdrawableEpoch ≤ getCurrentEpoch s →
      w.slashed = false ∧ w.exitEpoch = v.exitEpoch ∧
        w.withdrawableEpoch = v.withdrawableEpoch := by
      intros; exact ⟨by assumption, rfl, rfl⟩)
    (frozen : v.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch = v.exitEpoch ∧
      (hasCompoundingWithdrawalCredential w = true →
        hasCompoundingWithdrawalCredential v = true) := by
      intro _; exact ⟨rfl, id⟩) : CapStepR config s t := by
  refine {
    capped := ?_
    monotone := ?_
    forward := ?_
    forks := ?_
    proposers := ?_
    targetsAt := ?targetsAt
    retired := ?_
    withdrawal := ?_
    appended := ?_
    frozen := ?_ }
  · intro capped
    exact capped_setValidatorAt capped (bound (capped v (mem_of_getValidatorAt found))) ok
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    have read := getValidatorAt_eq_ok_iff.mp found
    intro j old located
    by_cases eq : j = i
    · subst j
      rw [read, Option.some.injEq] at located
      subst old
      exact ⟨w, by simp [BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set], monotone⟩
    · refine ⟨old, ?_, UInt64.le_refl _⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq] using located
  · obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
    exact UInt64.le_refl _
  · exact Nat.le_refl _
  · intro _ held fulu j member
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    obtain ⟨old, read, active⟩ := held fulu j member
    by_cases eq : j.toNat = i
    · have same := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans
        (eq ▸ read))
      subst old
      refine ⟨w, ?_, (assigned active) ▸ active⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨old, ?_, active⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq] using read
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    intro j old final before after assigned flag withdrawn
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at after
    split at after
    · rename_i eq
      subst j
      obtain rfl := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans before)
      cases after
      exact retired assigned flag withdrawn
    · obtain rfl := Option.some.inj (before.symm.trans after)
      exact ⟨flag, rfl, rfl⟩
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    intro j old final before after
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at after
    split at after
    · rename_i eq
      subst j
      have eq := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans before)
      subst old
      cases after
      exact ⟨kept, newly⟩
    · have eq := Option.some.inj (before.symm.trans after)
      subst final
      exact ⟨fun flag assigned => ⟨flag, assigned, rfl⟩,
        fun _ unslashed slashed => by simp [unslashed] at slashed⟩

  · intro _ j final outside after _
    obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
    have inside := (Array.getElem?_eq_some_iff.mp after).1
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.size_set] at inside
    omega
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    intro j old final before after assigned
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at after
    split at after
    · rename_i eq
      subst j
      obtain rfl := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans before)
      cases after
      exact frozen assigned
    · obtain rfl := Option.some.inj (before.symm.trans after)
      exact ⟨rfl, id⟩
  case targetsAt =>
    intro _ c held electra entry member index named
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    obtain ⟨old, read, active, reached⟩ := held electra entry member index named
    by_cases eq : index.toNat = i
    · have same := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans
        (eq ▸ read))
      subst old
      refine ⟨w, ?_, (assigned active) ▸ active, fun reach => (assigned active) ▸ reached reach⟩
      simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
    · refine ⟨old, ?_, active, reached⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set, Ne.symm eq] using read

private theorem CapStep.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v w : Validator} (found : getValidator s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidator i w = .ok t)
    (kept : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        w.withdrawableEpoch = v.withdrawableEpoch := by
      intros; exact ⟨by assumption, by assumption, rfl⟩)
    (newly : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      v.slashed = false → w.slashed = true →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch s).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      intro _ unslashed slashed
      exact Bool.noConfusion (unslashed.symm.trans slashed))
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH →
      w.activationEpoch = v.activationEpoch := by intro _; rfl)
    (retired : v.exitEpoch ≤ getCurrentEpoch s → v.slashed = false →
      v.withdrawableEpoch ≤ getCurrentEpoch s →
      w.slashed = false ∧ w.exitEpoch = v.exitEpoch ∧
        w.withdrawableEpoch = v.withdrawableEpoch := by
      intros; exact ⟨by assumption, rfl, rfl⟩)
    (frozen : v.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch = v.exitEpoch ∧
      (hasCompoundingWithdrawalCredential w = true →
        hasCompoundingWithdrawalCredential v = true) := by
      intro _; exact ⟨rfl, id⟩) : CapStepR config s t :=
  CapStep.setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) monotone bound
    (by rwa [← setValidator_eq_setValidatorAt]) kept newly assigned retired frozen

private theorem CapStep.increase {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : increaseBalance s i amount = .ok t) : CapStepR config s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact CapStepR.data rfl

private theorem CapStep.decrease {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : decreaseBalance s i amount = .ok t) : CapStepR config s t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  exact CapStepR.data rfl

private theorem preKeyCharge_decrease {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {index amount : UInt64}
    (ok : decreaseBalance s index amount = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  have growth := preKeyCharge_balance candidate (s := s)
    (t := s.putBalance index.toNat inside
      (Uint64.saturatingSub s.balances.data[index.toNat] amount)) rfl (fun _ => 0) ?_
  · simpa only [Nat.add_zero] using growth
  · intro j
    by_cases equal : index.toNat = j
    · subst j
      simp only [BeaconState.putBalance,
        Array.getElem?_set, ↓reduceIte, Option.map_some, Option.getD_some,
        Array.getElem?_eq_getElem inside, Uint64.toNat_saturatingSub, Nat.add_zero]
      omega
    · simp only [BeaconState.putBalance,
        Array.getElem?_set, equal, ↓reduceIte, Nat.add_zero, Nat.le_refl]

private theorem preKeyCharge_increase {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {index amount : UInt64}
    (ok : increaseBalance s index amount = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
      if j = index.toNat then amount.toNat else 0 := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  apply preKeyCharge_balance candidate (s := s)
    (t := s.putBalance index.toNat inside (s.balances.data[index.toNat] + amount)) rfl
    (fun j => if j = index.toNat then amount.toNat else 0)
  intro j
  by_cases equal : j = index.toNat
  · subst j
    simp only [BeaconState.putBalance, Array.getElem?_set, ↓reduceIte,
      Option.map_some, Option.getD_some, Array.getElem?_eq_getElem inside,
      UInt64.toNat_add, Nat.mod_eq_of_lt fits, Nat.le_refl]
  · simp only [BeaconState.putBalance, Array.getElem?_set, Ne.symm equal, equal,
      ↓reduceIte, Nat.add_zero, Nat.le_refl]

private theorem preKeyCharge_increase_assigned {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {index amount : UInt64}
    (assigned : ∀ v, s.validators.data[index.toNat]? = some v →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : increaseBalance s index amount = .ok t) :
    ∀ j, preKeyCharge candidate t j = preKeyCharge candidate s j := by
  obtain ⟨inside, _, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  intro j
  by_cases equal : index.toNat = j
  · subst j
    unfold preKeyCharge
    simp only [BeaconState.putBalance]
    split
    · cases found : s.validators.data[index.toNat]? with
      | none => rfl
      | some v => simp only [Option.map_some, assigned v found, ↓reduceIte, Option.getD_some]
    · rfl
  · simp only [preKeyCharge, BeaconState.putBalance, Array.getElem?_set, equal, ↓reduceIte]

private theorem preKeyCharge_consolidations {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (candidate : Nat → Bool) (sources : AssignedTargets s)
    (ok : processPendingConsolidations s electra = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨result, passed, balances, _⟩ := processPendingConsolidations_pass ok
  let R := fun (a b : BeaconState preset f) =>
    a.validators.data = s.validators.data →
      b.validators.data = s.validators.data ∧
        ∀ j, preKeyCharge candidate b j ≤ preKeyCharge candidate a j
  have composed := passPendingConsolidations_of R
    (fun _ same => ⟨same, fun _ => Nat.le_refl _⟩)
    (fun one two same => by
      obtain ⟨middle, first⟩ := one same
      obtain ⟨last, second⟩ := two middle
      exact ⟨last, fun j => (second j).trans (first j)⟩)
    (fun entry => entry ∈ (s.pendingConsolidations electra).data.toList)
    (fun {a lowered raised entry source balance} member _ _ debit credit same => by
      have downRegistry := decreaseBalance_validators debit
      have upRegistry := increaseBalance_validators credit
      refine ⟨(congrArg (·.data) (upRegistry.trans downRegistry)).trans same, ?_⟩
      have assigned : ∀ v, lowered.validators.data[entry.targetIndex.toNat]? = some v →
          v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
        intro v read
        obtain ⟨w, located, active⟩ := sources electra entry member entry.targetIndex
          (by simp)
        rw [downRegistry, same, located, Option.some.injEq] at read
        subst v
        exact active
      intro j
      rw [preKeyCharge_increase_assigned candidate assigned credit j]
      exact preKeyCharge_decrease candidate debit j)
    (fun _ member => member) passed
  have output := (composed.2 rfl).2
  intro j
  simpa only [preKeyCharge, balances, (composed.2 rfl).1,
    (processPendingConsolidations_kept ok).1] using output j

/-- Record writes compare only the live reserve or its permanent assignment charge. -/
private theorem preKeyCharge_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {i : Nat} {v w : Validator}
    (found : getValidatorAt s i = .ok v) (set : s.setValidatorAt i w = .ok t)
    (effective : w.effectiveBalance = v.effectiveBalance)
    (cap : withdrawalMaxEffectiveBalance preset f w = withdrawalMaxEffectiveBalance preset f v)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH → w.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (reserve : v.activationEpoch = FAR_FUTURE_EPOCH →
      w.activationEpoch ≠ FAR_FUTURE_EPOCH →
      preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j
  by_cases equal : j = i
  · subst j
    have read := getValidatorAt_eq_ok_iff.mp found
    simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, ↓reduceIte, Option.map_some, Option.getD_some, read]
    by_cases chosen : candidate i = true
    · simp only [chosen, ↓reduceIte]
      by_cases before : v.activationEpoch = FAR_FUTURE_EPOCH
      · by_cases after : w.activationEpoch = FAR_FUTURE_EPOCH
        · simp only [before, after, ↓reduceIte, effective, cap, Nat.le_refl]
        · simp only [before, after, ↓reduceIte]
          exact (UInt64.le_iff_toNat_le.mp (reserve before after)).trans (Nat.le_max_left _ _)
      · simp only [before, assigned before, ↓reduceIte, Nat.le_refl]
    · simp only [chosen, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  · simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, Ne.symm equal, ↓reduceIte, Nat.le_refl]

private theorem preKeyCharge_setAssigned {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {i : ValidatorIndex} {v w : Validator}
    (found : getValidator s i = .ok v) (set : s.setValidator i w = .ok t)
    (before : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (after : w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∀ j, preKeyCharge candidate t j = preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read := getValidator_eq_ok_iff.mp found
  intro j
  by_cases equal : i.toNat = j
  · subst j
    simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set_self, read, Option.map_some, before, after, ↓reduceIte,
      Option.getD_some]
  · simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, equal, ↓reduceIte]

private theorem CapStepR.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
      (ScheduledFree s → ScheduledFree t) := by
  obtain ⟨v, found, unchanged | ⟨unassigned, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact ⟨CapStepR.refl _, id, fun _ => id, (fun _ _ => Nat.le_refl _), id⟩
  · have same := (exitQueue_validators queue).1
    have cache : queued.proposerLookahead = s.proposerLookahead := by
      obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (CapStepR.data (congrArg (·.data) same) (frame_exitQueue queue).slot cache
        (by obtain ⟨_, _, rfl⟩ := exitQueue_eq queue; exact fun _ _ => id)).trans
        (CapStep.setValidator (v := v)
          (by rw [getValidator_of_validators_eq same]; exact found)
          (by exact UInt64.le_refl _) (by exact id) set
          (fun _ assigned => False.elim (assigned unassigned))
          (retired := by
            intro assigned _ _
            have later := exitQueue_lt queue
            have epochSame := (frame_exitQueue queue).slot
            have bound := UInt64.le_iff_toNat_le.mp assigned
            rw [getCurrentEpoch, epochSame, ← getCurrentEpoch, unassigned] at bound
            have limit := epoch.toNat_lt
            change 18446744073709551615 ≤ _ at bound
            omega)
          (frozen := fun assigned => False.elim (assigned unassigned)))
    · intro held
      have balances : queued.balances = s.balances := by
        obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
        rfl
      have middle := held.transfer (congrArg (·.data) same)
        (fun _ _ b _ _ read low => ⟨b, by rw [balances]; exact read, low⟩)
      have foundAt : getValidatorAt queued i.toNat = .ok v := by
        rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]
        exact found
      rw [setValidator_eq_setValidatorAt] at set
      apply middle.setValidatorAt foundAt set
      intro pending
      obtain ⟨_, eligible, unslashed⟩ := held i.toNat v (getValidator_eq_ok_iff.mp found) pending
      exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩
    · intro c held witness entry member
      obtain ⟨inside, rfl⟩ := setValidator_ok set
      have queueSame : queued.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
        obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
        rfl
      obtain ⟨old, read, assigned, active⟩ := held witness entry
        (by simpa [BeaconState.putValidator, queueSame] using member)
      have epochSame : getCurrentEpoch queued = getCurrentEpoch s := by
        rw [getCurrentEpoch, getCurrentEpoch, (frame_exitQueue queue).slot]
      have later := fun reach => UInt64.le_trans (active reach) (UInt64.le_of_eq epochSame.symm)
      by_cases equal : entry.validatorIndex.toNat = i.toNat
      · have eq := Option.some.inj ((getValidator_eq_ok_iff.mp found).symm.trans (equal ▸ read))
        subst old
        exact ⟨{ v with exitEpoch := epoch, withdrawableEpoch := withdrawal },
          by simp [BeaconState.putValidator,
          Serialization.Ssz.RootedForkList.data_set, equal], assigned, later⟩
      · exact ⟨old, by simpa [BeaconState.putValidator,
          Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set,
          (Ne.symm equal), same] using read, assigned, later⟩
    · intro candidate j
      have balances : queued.balances = s.balances := by
        obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
        rfl
      have step := preKeyCharge_setValidatorAt candidate
        (s := queued) (t := t) (i := i.toNat) (v := v)
        (w := { v with exitEpoch := epoch, withdrawableEpoch := withdrawal })
        (by rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]; exact found)
        (by rwa [← setValidator_eq_setValidatorAt]) rfl rfl id
        (fun pending assigned => (assigned pending).elim) j
      simpa only [preKeyCharge, same, balances] using step
    · intro held
      have balances : queued.balances = s.balances := by
        obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
        rfl
      have middle := held.transfer (t := queued)
        (by simp only [getCurrentEpoch, (frame_exitQueue queue).slot, UInt64.le_refl])
        (congrArg (·.data) same)
        (fun _ _ b _ _ _ read low => ⟨b, by rw [balances]; exact read, low⟩)
      exact middle.setValidatorAt_kept
        (i := i.toNat) (v := v)
        (w := { v with exitEpoch := epoch, withdrawableEpoch := withdrawal })
        (by rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]; exact found)
        (by rwa [← setValidator_eq_setValidatorAt]) rfl rfl rfl

private theorem CapStep.slash {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (slashable : ∀ v, getValidator s i = .ok v →
      isSlashableValidator v (getCurrentEpoch s) = true)
    (ok : slashValidator config s i whistleblower = .ok t) :
    CapStepR config s t ∧
      (UnassignedEligibleBalance s →
        (∃ w, s.validators.data[i.toNat]? = some w ∧
          w.activationEpoch ≠ FAR_FUTURE_EPOCH) → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (ScheduledFree s → ScheduledFree t) := by
  obtain ⟨exitedState, v, withdrawal, marked, _, _, slashings, _, _, _, _, last,
    exited, found, summed, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have assigned (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
      v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    obtain ⟨old, read, unchanged | ⟨_, queued, epoch, withdrawable, _, add, written⟩⟩ :=
      initiateValidatorExit_ok exited
    · rw [unchanged.2] at found
      have eq := Except.ok.inj (read.symm.trans found)
      exact eq ▸ unchanged.1
    · obtain ⟨inside, rfl⟩ := setValidator_ok written
      simp only [getValidator, BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set_self,
        Except.ok.injEq] at found
      subst v
      intro far
      have sum := Base.Uint64.addChecked_ok_iff.mp add
      change epoch = FAR_FUTURE_EPOCH at far
      rw [far] at sum
      have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      rw [farNat] at sum
      omega
  -- The slashed key is unslashed before the slashing, so only an unslashed key reaches the write.
  have unslashed : v.slashed = false := by
    obtain ⟨old, read, unchanged | ⟨_, queued, epoch, withdrawable, _, add, written⟩⟩ :=
      initiateValidatorExit_ok exited
    · rw [unchanged.2] at found
      obtain rfl := Except.ok.inj (read.symm.trans found)
      have live := slashable old read
      simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at live
      simpa using live.1.1
    · obtain ⟨inside, rfl⟩ := setValidator_ok written
      simp only [getValidator, BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set_self,
        Except.ok.injEq] at found
      subst v
      have live := slashable old read
      simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at live
      simpa using live.1.1
  have first := (CapStepR.exit exited).1.trans
    (CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set
      (fun slashed _ => Bool.noConfusion (slashed.symm.trans unslashed))
      (fun delay _ _ => ⟨assigned delay, by
        have sum := Base.Uint64.addChecked_ok_iff.mp summed
        have epoch : getCurrentEpoch exitedState = getCurrentEpoch s := by
          rw [getCurrentEpoch, getCurrentEpoch, (frame_initiateValidatorExit exited).slot]
        change (getCurrentEpoch exitedState).toNat + _ ≤
          (max v.withdrawableEpoch withdrawal).toNat
        rw [epoch, Base.Uint64.toNat_max]
        omega⟩)
      (retired := by
        intro assigned flag withdrawn
        have epochSame : getCurrentEpoch exitedState = getCurrentEpoch s := by
          rw [getCurrentEpoch, getCurrentEpoch, (frame_initiateValidatorExit exited).slot]
        rw [epochSame] at withdrawn
        obtain ⟨old, read, unchanged | ⟨far, queued, epoch, withdrawal', queue, add, written⟩⟩ :=
          initiateValidatorExit_ok exited
        · rw [unchanged.2] at found
          obtain rfl := Except.ok.inj (read.symm.trans found)
          have live := slashable old read
          simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at live
          exact (UInt64.not_le.mpr live.2 withdrawn).elim
        · obtain ⟨inside, rfl⟩ := setValidator_ok written
          simp only [getValidator, BeaconState.putValidator,
            Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set_self,
            Except.ok.injEq] at found
          subst v
          exact False.elim (by
            have later := exitQueue_lt queue
            have sum := Base.Uint64.addChecked_ok_iff.mp add
            have withdrawn := UInt64.le_iff_toNat_le.mp withdrawn
            change withdrawal'.toNat ≤ _ at withdrawn
            omega)))
  have second := (CapStep.decrease (config := config) lowered).trans
    ((CapStep.increase raised).trans (CapStep.increase paid))
  have total := first.trans ((CapStepR.data (s := marked)
    (t := { marked with slashings })).trans second)
  have funding (held : UnassignedEligibleBalance s)
      (active : ∃ w, s.validators.data[i.toNat]? = some w ∧
        w.activationEpoch ≠ FAR_FUTURE_EPOCH) : UnassignedEligibleBalance last := by
    obtain ⟨old, located, assigned⟩ := active
    obtain ⟨afterExit, read, life⟩ :=
      (registryLifecycle_initiateValidatorExit exited).validators i.toNat old located
    have equal := Option.some.inj (read.symm.trans (getValidator_eq_ok_iff.mp found))
    subst afterExit
    have notFar : v.activationEpoch ≠ FAR_FUTURE_EPOCH :=
      (life.activationEpoch assigned) ▸ assigned
    have foundAt := found
    rw [getValidator_eq_getValidatorAt] at foundAt
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    have funded := ((CapStepR.exit exited).2.1 held).setValidatorAt foundAt setAt
      (fun far => (notFar far).elim)
    have markedAssigned : ∀ w, marked.validators.data[i.toNat]? = some w →
        w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      intro w located
      obtain ⟨inside, rfl⟩ := setValidator_ok set
      simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set_self, Option.some.injEq] at located
      subst w
      exact notFar
    have slashingFunded := funded.transfer (t := { marked with slashings }) rfl
      (fun _ _ b _ _ read low => ⟨b, read, low⟩)
    exact ((slashingFunded.decrease markedAssigned lowered).increase raised).increase paid
  have partials (c : Prop) (held : PartialsAt c s) : PartialsAt c last := by
    have exitedHeld := (CapStepR.exit exited).2.2.1 c held
    have markedHeld := exitedHeld.setValidator found set (fun _ => rfl)
    have slashingHeld : PartialsAt c { marked with slashings } := markedHeld
    exact ((slashingHeld.decrease lowered).increase raised).increase paid
  have scheduled (held : ScheduledFree s) : ScheduledFree last := by
    have active : v.activationEpoch ≤ getCurrentEpoch exitedState := by
      obtain ⟨old, read, life⟩ :=
        (registryLifecycle_initiateValidatorExit exited).validators i.toNat
          _ (getValidator_eq_ok_iff.mp ((initiateValidatorExit_ok exited).choose_spec.1))
      have live := slashable _ ((initiateValidatorExit_ok exited).choose_spec.1)
      have assigned := assigned_of_slashable live
      simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at live
      have eq := Option.some.inj (read.symm.trans (getValidator_eq_ok_iff.mp found))
      subst old
      rw [life.activationEpoch assigned, getCurrentEpoch,
        (frame_initiateValidatorExit exited).slot]
      exact live.1.2
    have markedHeld := ((CapStepR.exit exited).2.2.2.2 held).setValidatorAt
      (w := { v with slashed := true, withdrawableEpoch := max v.withdrawableEpoch withdrawal })
      (by simpa only [setValidator_eq_setValidatorAt] using set)
      (fun future _ => (UInt64.not_le.mpr future active).elim)
    have slashingHeld : ScheduledFree { marked with slashings } := markedHeld
    have markedActive : ∀ w,
        ({ marked with slashings } : BeaconState preset f).validators.data[i.toNat]? = some w →
        w.activationEpoch ≤ getCurrentEpoch { marked with slashings } := by
      obtain ⟨inside, rfl⟩ := setValidator_ok set
      intro w located
      simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set_self, Option.some.injEq] at located
      subst w
      exact active
    exact ((slashingHeld.decrease markedActive lowered).increase raised).increase paid
  by_cases gloas : Fork.glamsterdam ≤ f
  · rw [dite_eq_left_of_eq_true (eq_true gloas)]
    exact ⟨total.trans (CapStepR.data rfl), (fun held active =>
      (funding held active).transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)), partials,
      fun held => (scheduled held).transfer (UInt64.le_refl _) rfl
        (fun _ _ b _ _ _ read low => ⟨b, read, low⟩)⟩
  · rw [dite_eq_right_of_eq_false (eq_false gloas)]
    exact ⟨total, funding, partials, scheduled⟩

private theorem preKeyCharge_add {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei} (matched : BalancesMatch s)
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
      if j = s.validators.data.size then amount.toNat else 0 := by
  obtain ⟨validators, balances⟩ := addValidatorToRegistry_push ok matched
  have sizes : s.balances.data.size = s.validators.data.size := matched
  intro j
  by_cases equal : j = s.validators.data.size
  · subst j
    have funded : (getValidatorFromDeposit preset f key credentials amount).effectiveBalance.toNat ≤
        amount.toNat := by
      change (min (amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT) _).toNat ≤ amount.toNat
      rw [Uint64.toNat_min]
      apply (Nat.min_le_left _ _).trans
      exact UInt64.le_iff_toNat_le.mp (UInt64.sub_le (by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
        exact Nat.mod_le _ _))
    simp only [preKeyCharge, validators, balances, Array.getElem?_push,
      sizes, ↓reduceIte, Option.map_some, Option.getD_some]
    split
    · change max (getValidatorFromDeposit preset f key credentials amount).effectiveBalance.toNat
        (min amount.toNat _) ≤ _
      omega
    · omega
  · simp only [preKeyCharge, validators, balances, Array.getElem?_push,
      sizes, equal, ↓reduceIte, Nat.add_zero, Nat.le_refl]

private theorem CapStep.add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    CapStepR config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) := by
  have data := addValidatorToRegistry_validators_eq_push ok
  have partials : t.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
    unfold addValidatorToRegistry at ok
    split at ok
    · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
        pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
      rfl
    · split at ok <;> cases ok
      rfl
  have forward : getCurrentEpoch s ≤ getCurrentEpoch t := by
    rw [getCurrentEpoch, getCurrentEpoch, addValidatorToRegistry_slot ok]
    exact UInt64.le_refl _
  refine ⟨?_, (fun matched held => held.add matched ok), fun _ held =>
    held.transfer (.append data) forward (fun _ _ member => partials ▸ member)⟩
  refine {
    capped := ?_
    monotone := ?_
    forward := ?_
    forks := ?_
    proposers := ?_
    targetsAt := ?targetsAt
    retired := ?_
    withdrawal := ?_
    appended := ?_
    frozen := ?_ }
  · intro capped v member
    rw [data, Array.mem_push] at member
    rcases member with old | rfl
    · exact capped v old
    · unfold getValidatorFromDeposit
      exact UInt64.le_iff_toNat_le.mpr (by rw [Base.Uint64.toNat_min]; exact Nat.min_le_right _ _)
  · intro i v found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    refine ⟨v, ?_, UInt64.le_refl _⟩
    simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using found
  · rw [getCurrentEpoch, getCurrentEpoch, addValidatorToRegistry_slot ok]
    exact UInt64.le_refl _
  · exact Nat.le_refl _
  · have cache : t.proposerLookahead = s.proposerLookahead := by
      unfold addValidatorToRegistry at ok
      split at ok
      · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
          pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
        rfl
      · split at ok
        · cases ok; rfl
        · cases ok
    intro _ held fulu i member
    rw [cache] at member
    obtain ⟨v, found, assigned⟩ := held fulu i member
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨v, by simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using found,
      assigned⟩
  · intro i v w before after _ flag _
    have inside := (Array.getElem?_eq_some_iff.mp before).1
    have read : t.validators.data[i]? = some v := by
      simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using before
    obtain rfl := Option.some.inj (read.symm.trans after)
    exact ⟨flag, rfl, rfl⟩
  · intro i v w before after
    have inside := (Array.getElem?_eq_some_iff.mp before).1
    have read : t.validators.data[i]? = some v := by
      simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using before
    have eq := Option.some.inj (read.symm.trans after)
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, rfl⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩

  · intro _ j w outside after slashed
    rw [data] at after
    simp only [Array.getElem?_push] at after
    split at after
    · cases after
      simp [getValidatorFromDeposit] at slashed
    · have inside := (Array.getElem?_eq_some_iff.mp after).1
      omega
  · intro i v w before after _
    have inside := (Array.getElem?_eq_some_iff.mp before).1
    have read : t.validators.data[i]? = some v := by
      simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using before
    obtain rfl := Option.some.inj (read.symm.trans after)
    exact ⟨rfl, id⟩
  case targetsAt =>
    have queue : t.pendingConsolidations = s.pendingConsolidations := by
      unfold addValidatorToRegistry at ok
      split at ok
      · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
          pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
        rfl
      · split at ok <;> cases ok
        rfl
    intro _ _ held
    exact held.transfer (.append data) forward (fun _ _ member => queue ▸ member)

private theorem preKeyCharge_deposit_growth {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {deposit : PendingDeposit} (matched : BalancesMatch s)
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    ∀ j, ((s.balances.data[j]?.map UInt64.toNat).getD 0) ≤
        ((t.balances.data[j]?.map UInt64.toNat).getD 0) ∧
      preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
        (((t.balances.data[j]?.map UInt64.toNat).getD 0) -
          ((s.balances.data[j]?.map UInt64.toNat).getD 0)) := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨index, raised⟩ | ⟨_, added⟩
  · exact fun _ => ⟨Nat.le_refl _, by simp⟩
  · have growth := preKeyCharge_increase candidate raised
    obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    intro j
    have bound := growth j
    by_cases equal : j = index.toNat
    · subst j
      simp only [BeaconState.putBalance, Array.getElem?_set, ↓reduceIte,
        Option.map_some, Option.getD_some, Array.getElem?_eq_getElem inside,
        UInt64.toNat_add, Nat.mod_eq_of_lt fits] at bound ⊢
      exact ⟨Nat.le_add_right _ _, by omega⟩
    · simp only [BeaconState.putBalance, Array.getElem?_set, Ne.symm equal,
        equal, ↓reduceIte, Nat.add_zero] at bound ⊢
      exact ⟨Nat.le_refl _, by simpa using bound⟩
  · have growth := preKeyCharge_add candidate matched added
    obtain ⟨_, balances⟩ := addValidatorToRegistry_push added matched
    have sizes : s.balances.data.size = s.validators.data.size := matched
    intro j
    have bound := growth j
    by_cases equal : j = s.validators.data.size
    · subst j
      simp only [balances, Array.getElem?_push, sizes, ↓reduceIte,
        Array.getElem?_eq_none (by omega : s.balances.data.size ≤ s.validators.data.size),
        Option.map_none, Option.getD_none, Option.map_some, Option.getD_some] at bound ⊢
      exact ⟨Nat.zero_le _, by simpa using bound⟩
    · simp only [balances, Array.getElem?_push, sizes, equal, ↓reduceIte,
        Nat.add_zero] at bound ⊢
      exact ⟨Nat.le_refl _, by simpa using bound⟩

private theorem CapStep.deposit {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    CapStepR config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (BalancesMatch s → ScheduledFree s → ScheduledFree t) := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact ⟨CapStepR.refl _, fun _ => id, fun _ => id, fun _ => id⟩
  · exact ⟨CapStep.increase raised, (fun _ held => held.increase raised),
      (fun _ held => held.increase raised), fun _ held => held.increase raised⟩
  · exact ⟨(CapStep.add added).1, (CapStep.add (config := config) added).2.1,
      (CapStep.add (config := config) added).2.2,
      fun matched held => held.add matched added⟩

private theorem CapStep.applyDeposit {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (ok : Consensus.applyDeposit config checks s key credentials amount signature = .ok t) :
    CapStepR config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (.pectra ≤ f → BalancesMatch s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (BalancesMatch s → ScheduledFree s → ScheduledFree t) := by
  rcases applyDeposit_cases ok with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨early, ok⟩
  · exact ⟨CapStepR.refl _, fun _ => id, fun _ => id, (fun _ _ _ _ => Nat.le_refl _),
      fun _ => id⟩
  · exact ⟨CapStepR.data rfl, (fun _ held => held.transfer rfl
      (fun _ _ b _ _ read low => ⟨b, read, low⟩)), fun _ => id, (fun _ _ _ _ => Nat.le_refl _),
      fun _ held => held.reframe (Nat.le_refl _) (Nat.le_refl _) rfl rfl⟩
  · exact ⟨(CapStep.add added).1.trans (CapStepR.data rfl), (fun matched held =>
      ((CapStep.add (config := config) added).2.1 matched held).transfer rfl
        (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
      (CapStep.add (config := config) added).2.2, (fun _ matched candidate i => by
        have growth := preKeyCharge_add candidate matched added i
        simpa only [preKeyCharge, UInt64.toNat_zero, ite_self, Nat.add_zero] using growth),
      fun matched held => (held.add matched added).reframe (Nat.le_refl _)
        (Nat.le_refl _) rfl rfl⟩
  · obtain ⟨step, funded, partials, scheduled⟩ := CapStep.deposit ok
    exact ⟨step, funded, partials, (fun electra => absurd electra (Nat.not_le_of_lt early)),
      scheduled⟩

private theorem CapStepR.processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    CapStepR config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (.pectra ≤ f → BalancesMatch s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (BalancesMatch s → ScheduledFree s → ScheduledFree t) := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact ⟨(CapStepR.data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next })).trans
      (CapStep.applyDeposit credited).1, (fun matched held =>
        (CapStep.applyDeposit (config := config) credited).2.1 matched
          (held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩))),
      (CapStep.applyDeposit (config := config) credited).2.2.1,
      (fun electra matched candidate i =>
        (CapStep.applyDeposit (config := config) credited).2.2.2.1 electra matched candidate i),
      fun matched held => (CapStep.applyDeposit (config := config) credited).2.2.2.2 matched
        (held.reframe (Nat.le_refl _) (Nat.le_refl _) rfl rfl)⟩

private theorem CapStep.registryEntry {f : Fork} {s t : BeaconState preset f}
    {i : Nat} (ok : updateRegistryEntry config s i = .ok t) :
    CapStepR config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (ScheduledFree s → ScheduledFree t) := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have preserved : queued.activationEpoch = v.activationEpoch ∧
      (queued.effectiveBalance = v.effectiveBalance ∧
      queued.withdrawalCredentials = v.withdrawalCredentials) ∧
      (queued.slashed = v.slashed ∧ queued.exitEpoch = v.exitEpoch ∧
        queued.withdrawableEpoch = v.withdrawableEpoch) := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      exact ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    · cases queue; exact ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  obtain ⟨epoch, same, records⟩ := preserved
  have cap : withdrawalMaxEffectiveBalance preset f queued =
      withdrawalMaxEffectiveBalance preset f v := by
    simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
      hasCompoundingWithdrawalCredential, same.2]
    rfl
  have first := CapStep.setValidatorAt (config := config) found
    (by rw [cap]; exact UInt64.le_refl _) (by simp only [same.1, cap]; exact id) set
    (by simp only [records.1, records.2.1, records.2.2];
        exact fun flag assigned => ⟨flag, assigned, trivial⟩)
    (by intro _ unslashed slashed
        exact Bool.noConfusion (unslashed.symm.trans (records.1.symm.trans slashed)))
    (by intro _; exact epoch)
    (by simp only [records.1, records.2.1, records.2.2];
        exact fun _ flag _ => ⟨flag, trivial, trivial⟩)
    (frozen := fun _ => ⟨records.2.1, fun compound => by
      unfold hasCompoundingWithdrawalCredential at compound ⊢
      rwa [same.2] at compound⟩)
  have funded (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
      (held : UnassignedEligibleBalance s) : UnassignedEligibleBalance marked := by
    apply held.setValidatorAt found set
    intro pending
    have before : v.activationEpoch = FAR_FUTURE_EPOCH := epoch ▸ pending
    obtain ⟨_, eligible, unslashed⟩ := held i v (getValidatorAt_eq_ok_iff.mp found) before
    obtain ⟨effective, _, flags, floor⟩ := queueForActivation_eligibility activation eligible queue
    exact ⟨before, UInt64.le_of_eq effective, floor, flags.trans unslashed⟩
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    obtain ⟨last, retained, _, _, scheduled⟩ := CapStepR.exit exited
    exact ⟨first.trans last, (fun activation held => retained (funded activation held)),
      fun held => scheduled (held.setValidatorAt_kept found set epoch same.1 records.1)⟩
  · cases ok
    exact ⟨first, funded, fun held => held.setValidatorAt_kept found set epoch same.1 records.1⟩

private theorem CapStep.activate {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v : Validator} (found : getValidator s i = .ok v)
    (far : v.activationEpoch = FAR_FUTURE_EPOCH)
    (ok : activateValidator s i = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH → UnassignedEligibleBalance s →
        ScheduledFree s → ScheduledFree t) := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨old, read, _, _, set⟩ := ok
  obtain rfl : old = v := Except.ok.inj (read.symm.trans found)
  refine ⟨CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set
    (assigned := fun assigned => (assigned far).elim), ?_, ?_⟩
  · intro held
    rw [setValidator_eq_setValidatorAt] at set
    apply held.setValidatorAt (by simpa only [getValidator_eq_getValidatorAt] using found) set
    intro _
    obtain ⟨_, eligible, unslashed⟩ := held i.toNat old
      (by simpa only [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] using found) far
    exact ⟨far, UInt64.le_refl _, eligible, unslashed⟩
  · intro eligible funded held
    rw [setValidator_eq_setValidatorAt] at set
    apply held.setValidatorAt set
    intro _ _
    obtain ⟨balance, minimum, unslashed⟩ := funded i.toNat old
      (getValidator_eq_ok_iff.mp found) far
    exact ⟨minimum eligible, fun _ => balance, unslashed⟩

private theorem CapStep.registryElectra {f : Fork} {s t : BeaconState preset f}
    {epoch : Epoch} {i : Nat}
    (ok : updateRegistryEntryElectra config epoch s i = .ok t) :
    CapStepR config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (UnassignedEligibleBalance s → s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
        ∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
      (s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH → UnassignedEligibleBalance s →
        ScheduledFree s → ScheduledFree t) := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    refine ⟨CapStep.setValidatorAt found (by exact UInt64.le_refl _)
      (by exact id) set, ?_, (fun _ held =>
        held.transfer (.setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩)
          (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact UInt64.le_refl _)
          (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact fun _ _ => id)), ?_,
      fun _ _ held => held.setValidatorAt_kept found set rfl rfl rfl⟩
    · intro activation held
      apply held.setValidatorAt found set
      intro pending
      obtain ⟨_, _, unslashed⟩ := held i v (getValidatorAt_eq_ok_iff.mp found) pending
      refine ⟨pending, UInt64.le_refl _, fun _ => ?_, unslashed⟩
      have queued : isEligibleForActivationQueue preset f v = true := by assumption
      simp only [isEligibleForActivationQueue, Bool.and_eq_true, beq_iff_eq] at queued
      split at queued
      · exact UInt64.le_trans activation (of_decide_eq_true queued.2)
      · exact UInt64.le_of_eq (beq_iff_eq.mp queued.2).symm
    · intro _ _ candidate
      exact preKeyCharge_setValidatorAt candidate found set rfl rfl id
        (fun pending assigned => (assigned pending).elim)
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact ⟨(CapStepR.exit exited).1, (fun _ => (CapStepR.exit exited).2.1),
      (CapStepR.exit (config := config) exited).2.2.1,
      fun _ _ => (CapStepR.exit (config := config) exited).2.2.2.1,
      fun _ _ => (CapStepR.exit (config := config) exited).2.2.2.2⟩
  split at ok
  · have set := liftAccessor_ok.mp ok
    refine ⟨CapStep.setValidatorAt found (by exact UInt64.le_refl _) (by exact id) set
      (assigned := fun assigned => (assigned (activationEpoch_of_isEligibleForActivation
        (by assumption))).elim), ?_, (fun _ held =>
          held.transfer (.setValidatorAt found set
            ⟨fun assigned => (assigned (activationEpoch_of_isEligibleForActivation
              (by assumption))).elim, fun _ => rfl⟩)
            (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact UInt64.le_refl _)
            (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact fun _ _ => id)), ?_, ?_⟩
    · intro _ held
      apply held.setValidatorAt found set
      intro _
      have pending := activationEpoch_of_isEligibleForActivation (by assumption)
      obtain ⟨_, eligible, unslashed⟩ := held i v (getValidatorAt_eq_ok_iff.mp found) pending
      exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩
    · intro held finite candidate
      have eligible : isEligibleForActivation s v = true := by assumption
      have pending := activationEpoch_of_isEligibleForActivation eligible
      apply preKeyCharge_setValidatorAt candidate found set rfl rfl
        (fun assigned => (assigned pending).elim)
      intro _ _
      apply (held i v (getValidatorAt_eq_ok_iff.mp found) pending).2.1
      have low : v.activationEligibilityEpoch ≤ s.finalizedCheckpoint.epoch := by
        simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq] at eligible
        exact eligible.1
      intro equal
      have strict := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt low finite)
      rw [equal] at strict
      omega
    · intro finite funded held
      have eligible : isEligibleForActivation s v = true := by assumption
      have pending := activationEpoch_of_isEligibleForActivation eligible
      apply held.setValidatorAt set
      intro _ _
      obtain ⟨⟨b, read, low⟩, minimum, unslashed⟩ :=
        funded i v (getValidatorAt_eq_ok_iff.mp found) pending
      have low' : v.activationEligibilityEpoch ≤ s.finalizedCheckpoint.epoch := by
        simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq] at eligible
        exact eligible.1
      have notFar : v.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH := by
        intro equal
        have strict := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt low' finite)
        rw [equal] at strict
        omega
      exact ⟨minimum notFar, fun _ => ⟨b, read, low⟩, unslashed⟩
  · cases ok; exact ⟨CapStepR.refl _, fun _ => id, fun _ => id, fun _ _ _ _ => Nat.le_refl _,
      fun _ _ => id⟩

private theorem CapStepR.registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) :
    CapStepR config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (.pectra ≤ f → preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
        ∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
        UnassignedEligibleBalance s → ScheduledFree s → ScheduledFree t) := by
  let R := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (∀ c, PartialsAt c a → PartialsAt c b) ∧
    (.pectra ≤ f → preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      UnassignedEligibleBalance a → a.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
      ∀ (candidate : Nat → Bool) j, preKeyCharge candidate b j ≤ preKeyCharge candidate a j) ∧
    b.finalizedCheckpoint = a.finalizedCheckpoint ∧
    (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
      UnassignedEligibleBalance a → ScheduledFree a → ScheduledFree b)
  have refl (a) : R a a :=
    ⟨CapStepR.refl a, fun _ => id, fun _ => id, (fun _ _ _ _ _ _ => Nat.le_refl _), rfl,
      fun _ _ _ => id⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c :=
    ⟨one.1.trans two.1, (fun activation => two.2.1 activation ∘ one.2.1 activation),
      fun c => two.2.2.1 c ∘ one.2.2.1 c,
      (fun electra activation held finite candidate j =>
        (two.2.2.2.1 electra activation (one.2.1 activation held)
          (by rw [one.2.2.2.2.1]; exact finite) candidate j).trans
          (one.2.2.2.1 electra activation held finite candidate j)),
      two.2.2.2.2.1.trans one.2.2.2.2.1,
      fun activation finite funded held => two.2.2.2.2.2 activation
        finite (one.2.1 activation funded)
        (one.2.2.2.2.2 activation finite funded held)⟩
  suffices held : R s t from
    ⟨held.1, held.2.1, held.2.2.1, held.2.2.2.1, held.2.2.2.2.2⟩
  unfold processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact foldlM_ok_invariant (R s)
      (fun _ _ _ previous edge => trans previous
        ⟨(CapStep.registryElectra edge).1, (CapStep.registryElectra edge).2.1,
          (CapStep.registryElectra edge).2.2.1,
          (fun _ _ => (CapStep.registryElectra edge).2.2.2.1),
          (frame_updateRegistryEntryElectra edge).finalized,
          fun _ finite funded held => (CapStep.registryElectra edge).2.2.2.2
            (by rw [previous.2.2.2.2.1]; exact finite) funded held⟩)
      (refl s) ok
  · rename_i notElectra
    simp only [bind_ok_iff] at ok
    obtain ⟨middle, updated, activated⟩ := ok
    have before : f < .glamsterdam :=
      Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
    have small : middle.validators.data.size < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (middle.validators.bound before) (UInt64.toNat_lt _)
    have first : R s middle := foldlM_ok_invariant (R s)
      (fun _ _ _ previous edge => trans previous
        ⟨(CapStep.registryEntry edge).1, (CapStep.registryEntry edge).2.1,
          (fun _ _ electra => (notElectra electra).elim),
          (fun electra => (notElectra electra).elim),
          (frame_updateRegistryEntry edge).finalized,
          fun _ _ _ => (CapStep.registryEntry edge).2.2⟩) (refl s) updated
    refine trans first
      (foldActivateValidator_of_queue R refl
        (fun one two => trans one two) ?_
        (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
        (fun i member => ?_) activated)
    · intro a b i v original member located epoch found far ok
      refine ⟨(CapStep.activate found far ok).1,
        (fun _ => (CapStep.activate (config := config) found far ok).2.1),
        (fun _ _ electra => (notElectra electra).elim),
        (fun electra => (notElectra electra).elim),
        (frame_activateValidator ok).finalized, ?_⟩
      intro _ finite funded held
      apply (CapStep.activate (config := config) found far ok).2.2 ?_ funded held
      obtain ⟨position, queued, equal, read, eligible⟩ :=
        mem_activationQueue (List.mem_of_mem_take member)
      have inside := (Array.getElem?_eq_some_iff.mp read).1
      have exactIndex : i.toNat = position := by
        have fits : position < UInt64.size := by change position < 2 ^ 64; omega
        rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' fits]
      have same : original = queued := Except.ok.inj
        (located.symm.trans (by simp [getValidator, exactIndex, read]))
      have low : original.activationEligibilityEpoch ≤ middle.finalizedCheckpoint.epoch := by
        subst queued
        simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq] at eligible
        exact eligible.1
      have finiteMiddle : middle.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH := by
        rw [first.2.2.2.2.1]
        exact finite
      intro farEpoch
      rw [epoch] at farEpoch
      have lt := UInt64.lt_of_le_of_lt low finiteMiddle
      rw [farEpoch] at lt
      exact UInt64.lt_irrefl _ lt
    · obtain ⟨position, v, equal, found, eligible⟩ :=
        mem_activationQueue (List.mem_of_mem_take member)
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have exactIndex : i.toNat = position := by
        have fits : position < UInt64.size := by
          change position < 2 ^ 64
          omega
        rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' fits]
      exact ⟨v, by simp [getValidator, exactIndex, found],
        activationEpoch_of_isEligibleForActivation eligible⟩

private theorem CapStep.excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra i = .ok t) :
    CapStepR config s t ∧
      (UnassignedEligibleBalance s →
        (∀ v, s.validators.data[i.toNat]? = some v →
          v.activationEpoch = FAR_FUTURE_EPOCH →
          v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) →
        UnassignedEligibleBalance t) ∧
      t.pendingPartialWithdrawals = s.pendingPartialWithdrawals ∧
      (ScheduledFree s →
        (∀ v, s.validators.data[i.toNat]? = some v →
          getCurrentEpoch s < v.activationEpoch → v.activationEpoch ≠ FAR_FUTURE_EPOCH →
          v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) →
        ScheduledFree t) := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, middle, set, rfl⟩ := ok
    refine ⟨?_, ?_, by obtain ⟨_, rfl⟩ := setBalance_ok set; rfl, ?_⟩
    · obtain ⟨_, rfl⟩ := setBalance_ok set
      exact CapStepR.data rfl
    · intro held retained
      exact (held.setBalance retained set).transfer rfl
        (fun _ _ b _ _ read low => ⟨b, read, low⟩)
    · intro held retained
      exact (held.setBalance (fun v found future assigned => retained v found future assigned)
        set).transfer (UInt64.le_refl _) rfl
        (fun _ _ b _ _ _ read low => ⟨b, read, low⟩)
  · cases ok
    exact ⟨CapStepR.refl _, fun held _ => held, rfl, fun held _ => held⟩

private theorem preKeyCharge_excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex} (candidate : Nat → Bool)
    (ok : queueExcessActiveBalance s electra index = .ok t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i := by
  apply preKeyCharge_notRaised candidate
    (congrArg (·.data) (queueExcessActiveBalance_validators ok))
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨balance, read, ok⟩ := ok
  split at ok
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, middle, set, rfl⟩ := ok
    obtain ⟨inside, rfl⟩ := setBalance_ok set
    intro i amount located
    by_cases equal : index.toNat = i
    · subst i
      simp only [BeaconState.putBalance, Array.getElem?_set_self, Option.some.injEq] at located
      subst amount
      exact ⟨balance, getBalance_eq_ok_iff.mp read, UInt64.le_of_lt above⟩
    · exact ⟨amount, by simpa [BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, equal] using located,
        UInt64.le_refl _⟩
  · cases ok
    exact fun _ amount read => ⟨amount, read, UInt64.le_refl _⟩

private theorem CapStep.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : switchToCompoundingValidator s electra i = .ok t)
    (unassigned : ∀ v, s.validators.data[i.toNat]? = some v →
      v.exitEpoch = FAR_FUTURE_EPOCH) :
    CapStepR config s t ∧
      (UnassignedEligibleBalance s →
        (∀ v, s.validators.data[i.toNat]? = some v →
          v.activationEpoch ≠ FAR_FUTURE_EPOCH) → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      ((∀ v, s.validators.data[i.toNat]? = some v →
        v.activationEpoch ≠ FAR_FUTURE_EPOCH) → ∀ candidate j,
        preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
      (ScheduledFree s → (∀ v, s.validators.data[i.toNat]? = some v →
        v.activationEpoch ≤ getCurrentEpoch s) → ScheduledFree t) := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨v, found, middle, set, queued⟩ := ok
  obtain ⟨cap, funding, partials, scheduled⟩ := CapStep.excess (config := config) queued
  have step : CapStepR config s t := by
    apply CapStepR.trans (CapStep.setValidator found ?_ ?_ set
      (frozen := fun assigned => False.elim (assigned (unassigned v
        (getValidator_eq_ok_iff.mp found))))) cap
    · simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
        getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
        isCompoundingWithdrawalCredential]
      simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
      by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
      · simp only [h]; exact UInt64.le_refl _
      · simp only [h]; exact order
    · intro bound
      apply UInt64.le_trans bound
      simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
        getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
        isCompoundingWithdrawalCredential]
      simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
      by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
      · simp only [h]; exact UInt64.le_refl _
      · simp only [h]; exact order
  refine ⟨step, ?_, ?_, ?_, ?_⟩
  · intro held assigned
    have notFar := assigned v (getValidator_eq_ok_iff.mp found)
    have foundAt := found
    rw [getValidator_eq_getValidatorAt] at foundAt
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    apply funding (held.setValidatorAt foundAt setAt (fun far => (notFar far).elim))
    intro w located pending
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set_self, Option.some.injEq] at located
    subst w
    exact (notFar pending).elim
  · intro _ held
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    exact (held.setValidator found set (fun _ => rfl)).transfer
      (.of_data (congrArg (·.data) (queueExcessActiveBalance_validators queued)))
      step.forward (fun _ _ member => by simpa [partials] using member)
  · intro assigned candidate j
    have active := assigned v (getValidator_eq_ok_iff.mp found)
    have charge := preKeyCharge_setAssigned candidate found set active active j
    exact (preKeyCharge_excess candidate queued j).trans (Nat.le_of_eq charge)
  · intro held active
    have foundAt := found
    rw [getValidator_eq_getValidatorAt] at foundAt
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    refine scheduled (held.setValidatorAt_kept foundAt setAt rfl rfl rfl) ?_
    intro w located future _
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set_self, Option.some.injEq] at located
    subst w
    exact (UInt64.not_le.mpr future (active v (getValidator_eq_ok_iff.mp found))).elim

private theorem CapStepR.blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  obtain ⟨v, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
  have before : hasCompoundingWithdrawalCredential v = false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, bls,
      BLS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  have after : hasCompoundingWithdrawalCredential
      { v with withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } =
      false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential,
      executionCredentials_prefix, ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  have cap : withdrawalMaxEffectiveBalance preset f
      { v with withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } =
      withdrawalMaxEffectiveBalance preset f v := by
    simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, before, after]
  refine ⟨?_, ?_, (fun _ held => held.setValidator found set (fun _ => rfl)), ?_,
    fun held => held.setValidatorAt_kept
      (v := v) (w := { v with
        withdrawalCredentials := executionCredentials signed.message.toExecutionAddress })
      (by simpa only [getValidator_eq_getValidatorAt] using found)
      (by simpa only [setValidator_eq_setValidatorAt] using set) rfl rfl rfl⟩
  rotate_left
  · intro held
    have foundAt := found
    rw [getValidator_eq_getValidatorAt] at foundAt
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    apply held.setValidatorAt foundAt setAt
    intro pending
    obtain ⟨_, eligible, unslashed⟩ := held _ v
      (getValidator_eq_ok_iff.mp found) pending
    exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩
  · intro candidate i
    exact preKeyCharge_setValidatorAt candidate
      (v := v) (w := { v with
        withdrawalCredentials := executionCredentials signed.message.toExecutionAddress })
      (by simpa only [getValidator_eq_getValidatorAt] using found)
      (by simpa only [setValidator_eq_setValidatorAt] using set) rfl cap id
      (fun far assigned => (assigned far).elim) i
  · apply CapStep.setValidator found (UInt64.le_of_eq cap.symm) ?_ set
      (frozen := fun _ => ⟨rfl, fun compound => Bool.noConfusion (after.symm.trans compound)⟩)
    simpa only [cap] using (id : v.effectiveBalance ≤
      withdrawalMaxEffectiveBalance preset f v → _)

private theorem CapStep.consolidate {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (sourceAssigned : source.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (sourceActive : source.activationEpoch ≤ getCurrentEpoch s)
    (target : ∃ v, s.validators.data[targetIndex.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ v.activationEpoch ≤ getCurrentEpoch s)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churn, withdrawal, _, marked, set, pending, appended, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  have partials : churned.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churn
    obtain ⟨_, _, _, _, _, _, rest⟩ := churn
    cases rest; rfl
  have charge : ∀ candidate i, preKeyCharge candidate
      { marked with pendingConsolidations := fun _ => pending } i ≤ preKeyCharge candidate s i := by
    intro candidate i
    have step := preKeyCharge_setAssigned candidate read set sourceAssigned sourceAssigned i
    have balances : churned.balances = s.balances := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churn
      obtain ⟨_, _, _, _, _, _, rest⟩ := churn
      cases rest; rfl
    simpa only [preKeyCharge, validators, balances] using Nat.le_of_eq step
  have forward : getCurrentEpoch s ≤ getCurrentEpoch churned := by
    rw [getCurrentEpoch, getCurrentEpoch,
      (frame_computeConsolidationEpochAndUpdateChurn churn).slot]
    exact UInt64.le_refl _
  refine ⟨?cap, ?funded, ?partials, charge, ?scheduled⟩
  case partials =>
    intro _ held
    have middle := held.transfer (.of_data (congrArg (·.data) validators)) forward
      (fun _ _ member => by simpa [partials] using member)
    exact (middle.setValidator read set (fun _ => rfl)).transfer (.of_data rfl)
      (UInt64.le_refl _) (fun _ _ member => member)
  case scheduled =>
    intro held
    have balances : churned.balances = s.balances := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churn
      obtain ⟨_, _, _, _, _, _, rest⟩ := churn
      cases rest; rfl
    have middle := held.transfer forward (congrArg (·.data) validators)
      (fun _ _ b _ _ _ located low => ⟨b, by rw [balances]; exact located, low⟩)
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    exact (middle.setValidatorAt_kept (v := source)
      (w := { source with exitEpoch := epoch, withdrawableEpoch := withdrawal })
      (by simpa only [getValidator_eq_getValidatorAt] using read) setAt rfl rfl rfl).transfer
      (UInt64.le_refl _) rfl (fun _ _ b _ _ _ located low => ⟨b, located, low⟩)
  case funded =>
    intro held
    have balances : churned.balances = s.balances := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churn
      obtain ⟨_, _, _, _, _, _, rest⟩ := churn
      cases rest; rfl
    have middle := held.transfer (congrArg (·.data) validators)
      (fun _ _ b _ _ located low => ⟨b, by rw [balances]; exact located, low⟩)
    have setAt := set
    rw [setValidator_eq_setValidatorAt] at setAt
    have retained := middle.setValidatorAt
      (by simpa only [getValidator_eq_getValidatorAt] using read) setAt (fun pending => by
        obtain ⟨_, eligible, unslashed⟩ := held sourceIndex.toNat source found pending
        exact ⟨pending, UInt64.le_refl _, eligible, unslashed⟩)
    exact retained.transfer rfl (fun _ _ b _ _ located low => ⟨b, located, low⟩)
  case cap =>
    have cache : churned.proposerLookahead = s.proposerLookahead := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churn
      obtain ⟨_, _, _, _, _, _, rest⟩ := churn
      cases rest; rfl
    have queue : churned.pendingConsolidations = s.pendingConsolidations := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churn
      obtain ⟨_, _, _, _, _, _, rest⟩ := churn
      cases rest; rfl
    have first := (CapStepR.data (config := config) (by rw [validators])
      (frame_computeConsolidationEpochAndUpdateChurn churn).slot cache
      (fun fwd _ held => held.transfer (.of_data (congrArg (·.data) validators)) fwd
        (fun _ _ member => queue ▸ member))).trans
      (CapStep.setValidator read (by exact UInt64.le_refl _) (by exact id) set
        (fun _ assigned => False.elim (assigned far))
        (retired := by
          intro assigned _ _
          have sourceEpoch : getCurrentEpoch churned = getCurrentEpoch s := by
            rw [getCurrentEpoch, getCurrentEpoch,
              (frame_computeConsolidationEpochAndUpdateChurn churn).slot]
          have bound := UInt64.le_iff_toNat_le.mp assigned
          rw [sourceEpoch, far] at bound
          have first := churn
          simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff] at first
          obtain ⟨firstEpoch, first, _⟩ := first
          have checked := computeActivationExitEpoch_ok_iff.mp (by
            simpa only [liftArith, mapError_ok_iff] using first)
          have limit := firstEpoch.toNat_lt
          change 18446744073709551615 ≤ _ at bound
          omega)
        (frozen := fun assigned => False.elim (assigned far)))
    refine first.trans (CapStepR.data rfl rfl rfl ?_)
    intro _ c held witness entry member
    have data := appendWithinLimit_data appended
    change entry ∈ pending.data.toList at member
    rw [data, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact held witness entry old
    · intro index named
      have located : ∃ v, s.validators.data[index.toNat]? = some v ∧
          v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ v.activationEpoch ≤ getCurrentEpoch s := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at named
        rcases named with rfl | rfl
        · exact ⟨source, found, sourceAssigned, sourceActive⟩
        · exact target
      obtain ⟨v, foundTarget, assigned, reached⟩ := located
      obtain ⟨inside, rfl⟩ := setValidator_ok set
      by_cases eq : index.toNat = sourceIndex.toNat
      · have same := Option.some.inj (found.symm.trans (eq ▸ foundTarget))
        subst v
        refine ⟨{ source with exitEpoch := epoch, withdrawableEpoch := withdrawal }, ?_, assigned,
          fun _ => UInt64.le_trans reached forward⟩
        simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, eq]
      · refine ⟨v, ?_, assigned, fun _ => UInt64.le_trans reached forward⟩
        simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
          Array.getElem?_set, Ne.symm eq, validators] using foundTarget

private theorem CapStepR.consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  rcases consolidationRequest_cases ok with rfl | ⟨index, validator, switch, switched⟩ |
    ⟨_, _, _, target, accepted, queued⟩
  · exact ⟨CapStepR.refl _, id, fun _ => id, fun _ _ => Nat.le_refl _, id⟩
  · have valid := switch.valid
    simp only [isValidSwitchToCompoundingRequest, Bool.and_eq_true, beq_iff_eq] at valid
    have read {v} (found : s.validators.data[index.toNat]? = some v) : v = validator :=
      Option.some.inj (found.symm.trans switch.found)
    obtain ⟨step, retained, partials, charge, scheduled⟩ := CapStep.compounding order switched
      fun v found => read found ▸ valid.2
    have assigned : ∀ v, s.validators.data[index.toNat]? = some v →
        v.activationEpoch ≠ FAR_FUTURE_EPOCH := fun v found =>
      assigned_of_active (epoch := getCurrentEpoch s) (read found ▸ valid.1.2)
    have active : ∀ v, s.validators.data[index.toNat]? = some v →
        v.activationEpoch ≤ getCurrentEpoch s := fun v found =>
      activationLe_of_active (e := getCurrentEpoch s) (read found ▸ valid.1.2)
    exact ⟨step, (fun held => retained held assigned), partials, charge assigned,
      fun held => scheduled held active⟩
  · exact CapStep.consolidate accepted.sourceAt accepted.sourceStays
      (assigned_of_active (epoch := getCurrentEpoch s) accepted.sourceActive)
      (activationLe_of_active (e := getCurrentEpoch s) accepted.sourceActive)
      ⟨target, accepted.targetAt,
        assigned_and_le_of_active (epoch := getCurrentEpoch s) accepted.targetActive⟩ queued

private theorem CapStep.partialWithdrawal {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra i v amount owed = .ok t) :
    CapStepR config s t ∧
      (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s →
        (∃ w, s.validators.data[i.toNat]? = some w ∧
          w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ (c → w.activationEpoch ≤ getCurrentEpoch s)) →
        PartialsAt c t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨middle, _⟩, churned, _, _, pending, appended, rfl⟩ := ok
    have validators := (computeExitEpochAndUpdateChurn_earliest churned).2.1
    have queue : middle.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
      simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churned
      obtain ⟨_, _, _, _, _, _, rest⟩ := churned
      cases rest; rfl
    have balances : middle.balances = s.balances := by
      simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churned
      obtain ⟨_, _, _, _, _, _, rest⟩ := churned
      cases rest; rfl
    have forward : getCurrentEpoch s ≤ getCurrentEpoch middle := by
      rw [getCurrentEpoch, getCurrentEpoch, (frame_computeExitEpochAndUpdateChurn churned).slot]
      exact UInt64.le_refl _
    refine ⟨?_, ?_, ?_, fun candidate i => Nat.le_of_eq
      (preKeyCharge_same candidate (congrArg (·.data) validators) balances i), ?_⟩
    · exact CapStepR.data (by rw [validators])
        (frame_computeExitEpochAndUpdateChurn churned).slot
        (by
          simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
            Except.ok.injEq] at churned
          obtain ⟨_, _, _, _, _, _, rest⟩ := churned
          cases rest; rfl)
        (by
          simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
            Except.ok.injEq] at churned
          obtain ⟨_, _, _, _, _, _, rest⟩ := churned
          cases rest; exact fun _ _ => id)
    · intro held
      apply held.transfer (congrArg (·.data) validators)
      intro j w b found far read low
      have balances : middle.balances = s.balances := by
        simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at churned
        obtain ⟨_, _, _, _, _, _, rest⟩ := churned
        cases rest; rfl
      exact ⟨b, by simpa [balances] using read, low⟩
    · intro c held assigned witness entry member
      change entry ∈ pending.data.toList at member
      rw [appendWithinLimit_data appended, Array.toList_push,
        List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · obtain ⟨w, read, far, active⟩ := held witness entry (by simpa [queue] using old)
        exact ⟨w, by simpa [validators] using read, far,
          fun reach => UInt64.le_trans (active reach) forward⟩
      · obtain ⟨w, read, far, active⟩ := assigned
        exact ⟨w, by simpa [validators] using read, far,
          fun reach => UInt64.le_trans (active reach) forward⟩
    · intro held
      apply held.transfer forward (congrArg (·.data) validators)
      intro j w b found far assigned read low
      exact ⟨b, by simpa [balances] using read, low⟩
  · cases ok; exact ⟨CapStepR.refl _, id, fun _ held _ => held, fun _ _ => Nat.le_refl _, id⟩

private theorem CapStepR.withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact ⟨CapStepR.refl _, id, fun _ => id, fun _ _ => Nat.le_refl _, id⟩)
    | (have step := CapStepR.exit (liftAccessor_ok.mp ok)
       exact ⟨step.1, step.2.1, step.2.2.1, step.2.2.2.1, step.2.2.2.2⟩)
    | (obtain ⟨step, funded, retained, charge, scheduled⟩ := CapStep.partialWithdrawal ok
       rename_i noRoom candidate position located checkedResult index checked credentials
         acceptedResult allowed accepted yes owedResult owed owedOk isPartial
       refine ⟨step, funded, (fun c held => retained c held ?_), charge, scheduled⟩
       have read := getElem?_toNat_of_ofNatChecked (by assumption)
       refine ⟨_, read, ?_⟩
       apply assigned_and_reached_of_active (epoch := getCurrentEpoch s)
       have acceptedTrue : canRequest config s s.validators.data[position] = .ok true :=
         yes ▸ accepted
       unfold canRequest at acceptedTrue
       dsimp only at acceptedTrue
       split at acceptedTrue
       · cases acceptedTrue
       · rename_i active
         have both := (not_or.mp (by simpa only [Bool.or_eq_true] using active)).1
         simpa using both)

private theorem CapStep.depositRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  obtain ⟨-, -, -, _, _, rfl⟩ := processDepositRequest_ok ok
  exact ⟨CapStepR.data rfl, fun held => held.transfer rfl
    (fun _ _ b _ _ read low => ⟨b, read, low⟩), fun _ => id, fun _ _ => Nat.le_refl _,
    fun held => held.transfer (UInt64.le_refl _) rfl
      (fun _ _ b _ _ _ read low => ⟨b, read, low⟩)⟩

private theorem CapStep.requests {f : Fork} {s t : BeaconState preset f}
    {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processExecutionRequests config s body electra = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  let R := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (∀ c, PartialsAt c a → PartialsAt c b) ∧
    (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i) ∧
    (ScheduledFree a → ScheduledFree b)
  have refl (a) : R a a := ⟨CapStepR.refl a, id, fun _ => id, fun _ _ => Nat.le_refl _, id⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c :=
    ⟨one.1.trans two.1, two.2.1 ∘ one.2.1, fun c => two.2.2.1 c ∘ one.2.2.1 c,
      fun candidate i => (two.2.2.2.1 candidate i).trans (one.2.2.2.1 candidate i),
      two.2.2.2.2 ∘ one.2.2.2.2⟩
  have fold {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      (kept : ∀ a x b, step a x = .ok b → R a b)
      {a b : BeaconState preset f} {xs : List α} (ok : xs.foldlM step a = .ok b) : R a b :=
    foldlM_ok_invariant (R a)
      (fun _ _ _ previous computed => trans previous (kept _ _ _ computed)) (refl a) ok
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  exact trans (fold (fun _ _ _ => CapStep.depositRequest) deposits)
    (trans (fold (fun _ _ _ => CapStepR.withdrawalRequest) withdrawals)
      (fold (fun _ _ _ => CapStepR.consolidationRequest order) consolidations))

private theorem preKeyCharge_slash {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} (candidate : Nat → Bool) (proposers : AssignedProposers s)
    (early : f < .glamsterdam)
    (ok : slashValidator config s index none = .ok t) :
    ∀ i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i := by
  obtain ⟨exited, validator, withdrawal, marked, _, _, slashings, lowered, proposer,
    reward, raised, last, exitOk, found, _, set, _, _, _, debit, chosen, _, credit,
    paid, result⟩ := slashValidator_ok ok
  have markCharge := preKeyCharge_setValidatorAt candidate
    (v := validator) (w := { validator with
      slashed := true
      withdrawableEpoch := max validator.withdrawableEpoch withdrawal })
    (by simpa only [getValidator_eq_getValidatorAt] using found)
    (by simpa only [setValidator_eq_setValidatorAt] using set) rfl rfl id
    (fun far assigned => (assigned far).elim)
  have exitedProposers := (CapStepR.exit exitOk).1.proposers early proposers
  have markedProposers : AssignedProposers marked := exitedProposers.transfer
    (.setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩) (fun late => ⟨late, by
      obtain ⟨_, rfl⟩ := setValidator_ok set
      rfl⟩)
  have loweredProposers : AssignedProposers lowered :=
    (CapStep.decrease (config := config) debit).proposers early markedProposers
  have assigned : ∀ v, lowered.validators.data[proposer.toNat]? = some v →
      v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro v read
    obtain ⟨w, named, active⟩ := loweredProposers.selected chosen
    obtain rfl := Option.some.inj (named.symm.trans read)
    exact active
  have first := preKeyCharge_increase_assigned candidate assigned credit
  have second := preKeyCharge_increase_assigned candidate (by
    intro v read
    apply assigned v
    simpa only [increaseBalance_validators credit, Option.getD_none] using read) paid
  rw [result]
  simp only [show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early, ↓reduceDIte]
  intro i
  have down := preKeyCharge_decrease candidate debit i
  have markedCharge := markCharge i
  have exitedCharge := (CapStepR.exit exitOk).2.2.2.1 candidate i
  rw [second i, first i]
  exact down.trans (markedCharge.trans exitedCharge)

private theorem CapStepR.proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (f < .glamsterdam → AssignedProposers s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, v, found, _, slashable, _, _, _, _, slashed⟩ := ok
  obtain ⟨step, retained, partials, scheduled⟩ := CapStep.slash (fun w read => by
    obtain rfl := Except.ok.inj (found.symm.trans read)
    exact slashable) slashed
  exact ⟨step, (fun held => retained held
    ⟨v, getValidator_eq_ok_iff.mp found, assigned_of_slashable slashable⟩), partials,
    (fun early proposers candidate => preKeyCharge_slash candidate proposers early slashed),
    scheduled⟩

private theorem CapStep.attesterSlashing_of {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (R : BeaconState preset f → BeaconState preset f → Prop)
    (refl : ∀ a, R a a)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (each : ∀ {a b : BeaconState preset f} {index : ValidatorIndex},
      (∀ v, getValidator a index = .ok v →
        isSlashableValidator v (getCurrentEpoch a) = true) →
      slashValidator config a index none = .ok b → R a b)
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧ R s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun (step : BeaconState preset f × Bool) =>
    CapStepR config s step.1 ∧
    (UnassignedEligibleBalance s → UnassignedEligibleBalance step.1) ∧
    (∀ c, PartialsAt c s → PartialsAt c step.1) ∧ R s step.1) ?_
    ⟨CapStepR.refl s, id, fun _ => id, refl s⟩ folded
  intro step i next previous ok
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    have slashable : ∀ w, getValidator middle i = .ok w →
        isSlashableValidator w (getCurrentEpoch middle) = true := by
      intro w read
      obtain rfl := Except.ok.inj (found.symm.trans read)
      assumption
    obtain ⟨step, retained, partials, _⟩ := CapStep.slash slashable slashed
    exact ⟨previous.1.trans step, (fun held => retained (previous.2.1 held)
      ⟨v, getValidator_eq_ok_iff.mp found, assigned_of_slashable (by assumption)⟩),
      fun c => partials c ∘ previous.2.2.1 c, trans previous.2.2.2 (each slashable slashed)⟩
  · cases ok; exact previous

private theorem CapStepR.attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (f < .glamsterdam → AssignedProposers s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledFree s → ScheduledFree t) := by
  have whole := CapStep.attesterSlashing_of
    (fun a b => CapStepR config a b ∧
      (f < .glamsterdam → AssignedProposers a → ∀ candidate i,
        preKeyCharge candidate b i ≤ preKeyCharge candidate a i) ∧
      (ScheduledFree a → ScheduledFree b))
    (fun a => ⟨CapStepR.refl a, (fun _ _ _ _ => Nat.le_refl _), id⟩)
    (fun one two => ⟨one.1.trans two.1,
      fun early proposers candidate i =>
        (two.2.1 early (one.1.proposers early proposers) candidate i).trans
          (one.2.1 early proposers candidate i), two.2.2 ∘ one.2.2⟩)
    (fun slashable slashed => ⟨(CapStep.slash slashable slashed).1,
      (fun early proposers candidate => preKeyCharge_slash candidate proposers early slashed),
      (CapStep.slash (config := config) slashable slashed).2.2.2⟩) ok
  exact ⟨whole.1, whole.2.1, whole.2.2.1, whole.2.2.2.2⟩

private theorem preKeyCharge_attestation {f : Fork} {s t : BeaconState preset f}
    {parentSlot : Slot} {attestation : Attestation preset f}
    (altair : .altair ≤ f) (candidate : Nat → Bool) (matched : BalancesMatch s)
    (proposers : AssignedProposers s)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  have registry := congrArg (·.data) (processAttestation_registry ok).1
  rw [processAttestation_of_altair altair] at ok
  obtain ⟨_, _, _, proposer, _, _, _, chosen, _, _, _, balances⟩ :=
    processAttestationAltair_balance ok
  apply preKeyCharge_of_live_balances candidate registry matched
  intro i v found pending balance read
  obtain ⟨final, located, value⟩ := balances i balance read
  have different : proposer.toNat ≠ i := by
    intro equal
    obtain ⟨w, named, assigned⟩ := proposers.selected chosen
    rw [equal, found, Option.some.injEq] at named
    subst w
    exact assigned pending
  have same : final = balance := by
    apply UInt64.toNat_inj.mp
    simpa only [different, ↓reduceIte, Nat.add_zero] using value
  exact same ▸ located

private theorem preKeyCharge_sync {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (candidate : Nat → Bool) (matched : BalancesMatch s)
    (assigned : ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
      ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v → v.pubkey = key →
        v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (proposers : AssignedProposers s)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∀ i, preKeyCharge candidate t i = preKeyCharge candidate s i := by
  obtain ⟨_, _, members, proposer, _, _, mapped, chosen, balances⟩ :=
    processSyncAggregate_balance ok
  obtain ⟨_, shape⟩ := processSyncAggregate_eq ok
  apply preKeyCharge_of_live_balances candidate (by rw [shape]) matched
  intro i v found pending balance read
  obtain ⟨final, located, value⟩ := balances i balance read
  have apart : ∀ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.1.toNat ≠ i := by
    intro member inside
    apply sync_member_not_unassigned mapped found
      (fun key keyed equal => assigned key keyed i v found equal.symm pending)
    exact (List.of_mem_zip (by simpa only [Array.toList_zip] using inside)).1
  have same : final = balance := by
    apply UInt64.toNat_inj.mp
    rw [value]
    apply List.foldlRecOn (motive := fun n : Nat => n = balance.toNat)
      (members.zip aggregate.syncCommitteeBits.bits.toArray).toList _ rfl
    intro amount previous member inside
    by_cases signed : member.2 = true
    · have different : proposer.toNat ≠ i := by
        intro equal
        obtain ⟨w, named, active⟩ := proposers.selected (chosen ⟨member, inside, signed⟩)
        rw [equal, found, Option.some.injEq] at named
        subst w
        exact active pending
      simpa only [signed, ↓reduceIte, apart member inside, different, Nat.add_zero] using previous
    · simpa only [signed, Bool.false_eq_true, ↓reduceIte, apart member inside] using previous
  exact same ▸ located

private theorem CapStep.withdrawals {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (early : f < .glamsterdam)
    (ok : processWithdrawals s capella payload = .ok t) :
    CapStepR config s t ∧ (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      t.validators.data = s.validators.data ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ActivationExitOrder s → ExitsOrdered s → PartialsAt True s →
        EffectiveBalancesCapped s → ScheduledFree s → ScheduledFree t) := by
  obtain ⟨expected, _, _, applied⟩ := processWithdrawals_expected early ok
  let R := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (∀ c, PartialsAt c a → PartialsAt c b) ∧ b.validators.data = a.validators.data ∧
    (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i)
  have kept : R s t := by
    apply applyExpectedWithdrawals_of_updates R
      (fun a => ⟨CapStepR.refl a, fun _ => id, rfl, fun _ _ => Nat.le_refl _⟩)
      (fun one two => ⟨one.1.trans two.1, fun c => two.2.1 c ∘ one.2.1 c,
        two.2.2.1.trans one.2.2.1,
        fun candidate i => (two.2.2.2 candidate i).trans (one.2.2.2 candidate i)⟩)
      (fun withdrawn => by
        have lowered := withdrawn
        simp only [applyWithdrawal, show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early,
          false_and, ↓reduceDIte] at lowered
        rw [applyWithdrawal_eq withdrawn]
        exact ⟨CapStepR.data rfl, fun _ => id, rfl, fun candidate i => by
          simpa only [preKeyCharge, decreaseBalance_validators lowered] using
            preKeyCharge_decrease candidate lowered i⟩) _ _ _ _ _
      (fun _ electra count => ⟨CapStepR.data rfl, fun _ held => held.drop electra count, rfl,
        fun _ _ => Nat.le_refl _⟩)
      applied
    all_goals exact fun _ _ => ⟨CapStepR.data rfl, fun _ => id, rfl, fun _ _ => Nat.le_refl _⟩
  exact ⟨kept.1, kept.2.1, fun activation exits partials before capped held =>
    held.withdrawals_of_provenance activation exits partials kept.2.2.1 before capped ok,
    kept.2.2.1, kept.2.2.2, fun activation exits partials capped held =>
      held.withdrawals activation exits partials kept.2.2.1 capped ok⟩

private theorem CapStep.execution {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {body : BeaconBlockBody preset f}
    {bellatrix : .bellatrix ≤ f}
    (early : f < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    CapStepR config s t ∧ (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      t.validators.data = s.validators.data ∧ t.slot = s.slot ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ActivationExitOrder s → ExitsOrdered s → PartialsAt True s →
        EffectiveBalancesCapped s → ScheduledFree s → ScheduledFree t) := by
  let R := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (∀ c, PartialsAt c a → PartialsAt c b) ∧ b.validators.data = a.validators.data ∧
    b.slot = a.slot ∧
    (ActivationExitOrder a → ExitsOrdered a → AssignedPartials a →
      getCurrentEpoch a < FAR_FUTURE_EPOCH → EffectiveBalancesCapped a →
      UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i) ∧
    (ActivationExitOrder a → ExitsOrdered a → PartialsAt True a →
      EffectiveBalancesCapped a → ScheduledFree a → ScheduledFree b)
  have refl (a) : R a a :=
    ⟨CapStepR.refl a, fun _ => id, rfl, rfl, (fun _ _ _ _ _ => id),
      (fun _ _ => Nat.le_refl _), fun _ _ _ _ => id⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c := by
    refine ⟨one.1.trans two.1, fun c => two.2.1 c ∘ one.2.1 c, two.2.2.1.trans one.2.2.1,
      two.2.2.2.1.trans one.2.2.2.1, ?_,
      (fun candidate i => (two.2.2.2.2.2.1 candidate i).trans
        (one.2.2.2.2.2.1 candidate i)), ?_⟩
    · intro activation exits partials before capped held
      apply two.2.2.2.2.1
      · simpa only [ActivationExitOrder, one.2.2.1] using activation
      · simpa only [ExitsOrdered, one.2.2.1] using exits
      · exact (one.2.1 False partials.at).old
      · simpa only [getCurrentEpoch, one.2.2.2.1] using before
      · exact one.1.capped capped
      · exact one.2.2.2.2.1 activation exits partials before capped held
    · intro activation exits partials capped held
      apply two.2.2.2.2.2.2
      · simpa only [ActivationExitOrder, one.2.2.1] using activation
      · simpa only [ExitsOrdered, one.2.2.1] using exits
      · exact one.2.1 True partials
      · exact one.1.capped capped
      · exact one.2.2.2.2.2.2 activation exits partials capped held
  have whole : R s t := by
    apply processBlockExecution_of R refl (fun one two => trans one two)
      (fun paid => by
        obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
        exact ⟨CapStepR.data rfl, fun _ => id, rfl, rfl, (fun _ _ _ _ _ held =>
          held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
          (fun _ _ => Nat.le_refl _),
          fun _ _ _ _ held => held.reframe (Nat.le_refl _)
            (Nat.le_refl _) rfl rfl⟩)
      (fun _ => (Nat.not_le_of_lt early ‹.glamsterdam ≤ f›).elim)
      (fun withdrawn => by
        obtain ⟨step, partials, funded, same, charge, scheduled⟩ :=
          CapStep.withdrawals early withdrawn
        exact ⟨step, partials, same, (frame_processWithdrawals withdrawn).slot, funded,
          charge, scheduled⟩) ok
  exact ⟨whole.1, whole.2.1, whole.2.2.2.2.1, whole.2.2.1, whole.2.2.2.1,
    whole.2.2.2.2.2⟩

private theorem CapStepR.block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) :
    CapStepR config s t ∧
      (f < .glamsterdam → ∀ c, PartialsAt c s → PartialsAt c t) ∧
      (f < .glamsterdam → ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH) →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (.pectra ≤ f → f < .glamsterdam → AssignedProposers s →
        BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH) →
        ∀ candidate i,
          preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (f < .glamsterdam → ActivationExitOrder s → ExitsOrdered s → PartialsAt True s →
        EffectiveBalancesCapped s → BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
              v.activationEpoch.toNat ≤ (getCurrentEpoch s).toNat + 1) →
        ScheduledFree s → ScheduledFree t) := by
  have same {a b : BeaconState preset f} (validators : b.validators = a.validators)
      (slot : b.slot = a.slot) (cache : b.proposerLookahead = a.proposerLookahead)
      (queue : b.pendingConsolidations = a.pendingConsolidations) :
      CapStepR config a b := CapStepR.data (congrArg (·.data) validators) slot cache
        (fun fwd _ held => held.transfer (.of_data (congrArg (·.data) validators)) fwd
          (fun _ _ member => queue ▸ member))
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have framed {a b : BeaconState preset f} (frame : BlockFrame a b)
      (validators : b.validators = a.validators)
      (cache : f < .glamsterdam → b.proposerLookahead = a.proposerLookahead)
      (queue : f < .glamsterdam → b.pendingConsolidations = a.pendingConsolidations) :
      CapStepR config a b := by
    have data := congrArg (·.data) validators
    refine {
      capped := fun held v member => held v (data ▸ member)
      monotone := fun _ v found => ⟨v, data ▸ found, UInt64.le_refl _⟩
      forward := by rw [getCurrentEpoch, getCurrentEpoch, frame.slot]; exact UInt64.le_refl _
      forks := Nat.le_refl _
      proposers := fun early held =>
        held.transfer (.of_data (congrArg (·.data) validators))
          fun late => ⟨late, congrFun (cache early) late⟩
      targetsAt := fun early _ held => held.transfer (.of_data (congrArg (·.data) validators))
        (by rw [getCurrentEpoch, getCurrentEpoch, frame.slot]; exact UInt64.le_refl _)
        (fun _ _ member => queue early ▸ member)
      retired := by
        intro i v w before after _ flag _
        rw [data, before, Option.some.injEq] at after
        subst w
        exact ⟨flag, rfl, rfl⟩
      withdrawal := ?_
      appended := by
        intro _ j w outside found _
        rw [data] at found
        have inside := (Array.getElem?_eq_some_iff.mp found).1
        omega
      frozen := by
        intro i v w before after _
        rw [data, before, Option.some.injEq] at after
        subst w
        exact ⟨rfl, id⟩ }
    intro i v w before after
    rw [data, before, Option.some.injEq] at after
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, rfl⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩
  let R := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (f < .glamsterdam → b.validators.data = a.validators.data ∧ b.slot = a.slot ∧
      (∀ c, PartialsAt c a → PartialsAt c b) ∧
      b.currentSyncCommittee = a.currentSyncCommittee ∧
      (ActivationExitOrder a → ExitsOrdered a → AssignedPartials a →
        getCurrentEpoch a < FAR_FUTURE_EPOCH → EffectiveBalancesCapped a →
        UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
      (∀ candidate i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i) ∧
      (ActivationExitOrder a → ExitsOrdered a → PartialsAt True a →
        EffectiveBalancesCapped a → ScheduledFree a → ScheduledFree b))
  have refl (a) : R a a :=
    ⟨CapStepR.refl a, fun _ => ⟨rfl, rfl, fun _ => id, rfl, (fun _ _ _ _ _ => id),
      (fun _ _ => Nat.le_refl _), fun _ _ _ _ => id⟩⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c := by
    refine ⟨one.1.trans two.1, fun early => ?_⟩
    obtain ⟨registry, slot, partials, committee, funded, charge, scheduled⟩ := one.2 early
    obtain ⟨registry', slot', partials', committee', funded', charge', scheduled'⟩ := two.2 early
    refine ⟨registry'.trans registry, slot'.trans slot, fun c => partials' c ∘ partials c,
      committee'.trans committee, ?_, (fun candidate i => (charge' candidate i).trans
        (charge candidate i)), ?_⟩
    · intro activation exits queue before capped held
      apply funded'
      · simpa only [ActivationExitOrder, registry] using activation
      · simpa only [ExitsOrdered, registry] using exits
      · exact (partials False queue.at).old
      · simpa only [getCurrentEpoch, slot] using before
      · exact one.1.capped capped
      · exact funded activation exits queue before capped held
    · intro activation exits queue capped held
      apply scheduled'
      · simpa only [ActivationExitOrder, registry] using activation
      · simpa only [ExitsOrdered, registry] using exits
      · exact partials True queue
      · exact one.1.capped capped
      · exact scheduled activation exits queue capped held
  have plain {a b : BeaconState preset f} (step : CapStepR config a b)
      (registry : b.validators.data = a.validators.data) (slot : b.slot = a.slot)
      (balances : b.balances = a.balances)
      (partials : b.pendingPartialWithdrawals = a.pendingPartialWithdrawals)
      (committee : b.currentSyncCommittee = a.currentSyncCommittee := by rfl) : R a b :=
    ⟨step, fun _ => ⟨registry, slot,
      fun _ held => held.transfer (.of_data registry) step.forward
        (fun _ _ member => partials ▸ member),
      committee,
      fun _ _ _ _ _ held => held.transfer registry
        (fun _ _ amount _ _ read low => ⟨amount, by rw [balances]; exact read, low⟩),
      (fun candidate i => Nat.le_of_eq (by simp only [preKeyCharge, registry, balances])),
      fun _ _ _ _ held => held.reframe (by simp only [getCurrentEpoch, slot, Nat.le_refl])
        (by simp only [getCurrentEpoch, slot, Nat.le_refl]) registry
        (congrArg (·.data) balances)⟩⟩
  -- From Gloas, a block first applies the payload of the parent, which runs the validator requests.
  have head : R s input :=
    started.step_of R refl (fun one two => trans one two)
      (fun gloas paid => ⟨processParentExecutionPayload_step_of (CapStepR config) CapStepR.refl
        (fun one two => one.trans two) (fun frame validators => framed frame validators
          (fun early => (Nat.not_le_of_lt early gloas).elim)
          (fun early => (Nat.not_le_of_lt early gloas).elim))
        (fun ok => (CapStepR.withdrawalRequest ok).1)
        (fun ok => (CapStepR.consolidationRequest order ok).1) paid,
        fun early => (Nat.not_le_of_lt early gloas).elim⟩)
      (fun headed => by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
        exact plain (same rfl rfl rfl rfl) rfl rfl rfl rfl)
      (fun _ executed => by
        by_cases early : f < .glamsterdam
        · obtain ⟨step, partials, funded, registry, slot, charge, scheduled⟩ :=
            CapStep.execution early executed
          exact ⟨step, fun _ => ⟨registry, slot, partials,
            funext fun altair => processBlockExecution_currentSyncCommittee altair executed,
            funded, charge, scheduled⟩⟩
        · exact ⟨framed (frame_processBlockExecution executed)
            (processBlockExecution_validators executed)
            (fun _ => processBlockExecution_proposerLookahead executed)
            (fun _ => SamePendingQueue.blockExecution executed),
            fun before => (early before).elim⟩)
      (fun revealed => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        exact plain (same rfl rfl rfl rfl) rfl rfl rfl rfl)
      (fun _ voted => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        rw [← rest]
        exact plain (same rfl rfl rfl rfl) rfl rfl rfl rfl)
  let P := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (f < .glamsterdam → ∀ c, PartialsAt c a → PartialsAt c b) ∧
    (BalancesMatch a → BalancesMatch b) ∧
    (BalancesMatch a → UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (.pectra ≤ f → f < .glamsterdam → AssignedProposers a → BalancesMatch a →
      ∀ candidate i,
        preKeyCharge candidate b i ≤ preKeyCharge candidate a i) ∧
    (BalancesMatch a → ScheduledFree a → ScheduledFree b) ∧
    RegistryLifecycle a b
  have reflP (a) : P a a :=
    ⟨CapStepR.refl a, fun _ _ => id, id, fun _ => id,
      (fun _ _ _ _ _ _ => Nat.le_refl _), (fun _ => id), .refl _⟩
  have transP {a b c} (one : P a b) (two : P b c) : P a c :=
    ⟨one.1.trans two.1, fun early c => two.2.1 early c ∘ one.2.1 early c,
      two.2.2.1 ∘ one.2.2.1,
      (fun matched => two.2.2.2.1 (one.2.2.1 matched) ∘ one.2.2.2.1 matched),
      (fun electra early proposers matched candidate i =>
        (two.2.2.2.2.1 electra early (one.1.proposers early proposers)
          (one.2.2.1 matched) candidate i).trans
          (one.2.2.2.2.1 electra early proposers matched candidate i)),
      (fun matched => two.2.2.2.2.2.1 (one.2.2.1 matched) ∘ one.2.2.2.2.2.1 matched),
      one.2.2.2.2.2.2.trans two.2.2.2.2.2.2⟩
  have foldP {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      (each : ∀ a x b, step a x = .ok b → P a b)
      {a b : BeaconState preset f} {items : List α} (ok : items.foldlM step a = .ok b) :
      P a b := (foldlM_ok_steps P reflP (fun one two => transP one two) each ok).1
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of P reflP (fun one two => transP one two)
      (fun ok => ⟨(CapStepR.processDeposit ok).1,
        fun _ => (CapStepR.processDeposit (config := config) ok).2.2.1,
        (frame_processDeposit ok).balancesMatch, (CapStepR.processDeposit ok).2.1,
        (fun electra _ _ matched =>
          (CapStepR.processDeposit (config := config) ok).2.2.2.1 electra matched),
        (CapStepR.processDeposit (config := config) ok).2.2.2.2,
        registryLifecycle_processDeposit ok⟩)
      (fun exited => ⟨(CapStepR.exit (processVoluntaryExit_initiates exited)).1,
        fun _ => (CapStepR.exit (config := config)
          (processVoluntaryExit_initiates exited)).2.2.1,
        (frame_processVoluntaryExit exited).balancesMatch,
        fun _ => (CapStepR.exit (config := config)
          (processVoluntaryExit_initiates exited)).2.1,
        (fun _ _ _ _ => (CapStepR.exit (config := config)
          (processVoluntaryExit_initiates exited)).2.2.2.1),
        (fun _ => (CapStepR.exit (config := config)
          (processVoluntaryExit_initiates exited)).2.2.2.2),
        registryLifecycle_processVoluntaryExit exited⟩)
      (fun ok => ⟨(CapStepR.blsChange ok).1,
        fun _ => (CapStepR.blsChange (config := config) ok).2.2.1,
        (frame_processBlsToExecutionChange ok).balancesMatch,
        fun _ => (CapStepR.blsChange (config := config) ok).2.1,
        (fun _ _ _ _ => (CapStepR.blsChange (config := config) ok).2.2.2.1),
        (fun _ => (CapStepR.blsChange (config := config) ok).2.2.2.2),
        registryLifecycle_processBlsToExecutionChange ok⟩)
      (fun ok => ⟨(CapStep.requests order ok).1,
        fun _ => (CapStep.requests (config := config) order ok).2.2.1,
        (frame_processExecutionRequests ok).balancesMatch,
        fun _ => (CapStep.requests (config := config) order ok).2.1,
        (fun _ _ _ _ => (CapStep.requests (config := config) order ok).2.2.2.1),
        (fun _ => (CapStep.requests (config := config) order ok).2.2.2.2),
        registryLifecycle_processExecutionRequests ok⟩)
      (fun attested => by
        rw [processPayloadAttestation_eq attested]
        exact reflP _) operated
  have tail : CapStepR config last t ∧
      (f < .glamsterdam → ∀ c, PartialsAt c last → PartialsAt c t) := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact ⟨same rfl rfl rfl rfl, fun _ _ => id⟩
    · cases synced
      exact ⟨CapStepR.refl _, fun _ _ => id⟩
  have operations : P input last :=
    transP (foldP (fun _ _ _ ok => ⟨(CapStepR.proposerSlashing ok).1,
      fun _ => (CapStepR.proposerSlashing (config := config) ok).2.2.1,
      (frame_processProposerSlashing ok).balancesMatch,
      fun _ => (CapStepR.proposerSlashing (config := config) ok).2.1,
      (fun _ early proposers _ =>
        (CapStepR.proposerSlashing (config := config) ok).2.2.2.1 early proposers),
      (fun _ => (CapStepR.proposerSlashing (config := config) ok).2.2.2.2),
      registryLifecycle_processProposerSlashing ok⟩) proposersOk) <|
    transP (foldP (fun _ _ _ ok => ⟨(CapStepR.attesterSlashing ok).1,
      fun _ => (CapStepR.attesterSlashing (config := config) ok).2.2.1,
      (frame_processAttesterSlashing ok).balancesMatch,
      fun _ => (CapStepR.attesterSlashing (config := config) ok).2.1,
      (fun _ early proposers _ =>
        (CapStepR.attesterSlashing (config := config) ok).2.2.2.1 early proposers),
      (fun _ => (CapStepR.attesterSlashing (config := config) ok).2.2.2.2),
      registryLifecycle_processAttesterSlashing ok⟩) slashingsOk) <|
    transP (foldP (fun _ _ _ attested => ⟨same (processAttestation_registry attested).1
      (frame_processAttestation attested).slot (processAttestation_proposerLookahead attested)
      (by
        by_cases electra : .pectra ≤ f
        · exact SamePendingQueue.attestation electra attested
        · funext witness; exact (electra witness).elim),
      fun _ _ held => held.attestation attested,
      (frame_processAttestation attested).balancesMatch,
      (fun _ held => held.attestation attested),
      (fun electra _ proposers matched candidate i => Nat.le_of_eq
        (preKeyCharge_attestation (Nat.le_trans (by decide) electra)
          candidate matched proposers attested i)),
      (fun _ held => held.attestation attested),
      registryLifecycle_processAttestation attested⟩) attestedOk) rest
  refine ⟨head.1.trans (operations.1.trans tail.1), fun early c =>
    tail.2 early c ∘ operations.2.1 early c ∘ (head.2 early).2.2.1 c, ?_, ?_, ?_⟩
  rotate_left
  · intro electra early proposers matched unique assigned
    obtain ⟨registry, slot, _, committee, _, charge, _⟩ := head.2 early
    have inputMatched := (frame_operationsInput started).balancesMatch matched
    have operatedCharge := operations.2.2.2.2.1 electra early
      (head.1.proposers early proposers) inputMatched
    have inputAssigned (altair : .altair ≤ f) :
        ∀ key ∈ (input.currentSyncCommittee altair).value.pubkeys.toList,
          ∃ (i : Nat) (v : Validator), input.validators.data[i]? = some v ∧ v.pubkey = key ∧
            v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      simpa only [committee, registry] using assigned altair
    intro candidate i
    apply Nat.le_trans ?_ ((operatedCharge candidate i).trans (charge candidate i))
    split at synced
    · apply Nat.le_of_eq (preKeyCharge_sync candidate
        (operations.2.2.1 inputMatched) ?_
        (operations.1.proposers early (head.1.proposers early proposers)) synced i)
      exact property_of_key_provenance (fun v => v.activationEpoch ≠ FAR_FUTURE_EPOCH)
        ((frame_processOperations operated).pubkeysDistinct
          ((frame_operationsInput started).pubkeysDistinct unique))
        (processOperations_syncCommittee_activation_assigned _ (inputAssigned _) operated)
    · cases synced; exact Nat.le_refl _
  · intro early activation exits partials capped matched unique bounded held
    obtain ⟨registry, slot, _, committee, _, _, scheduled⟩ := head.2 early
    have inputHeld := scheduled activation exits partials capped held
    have lastHeld := operations.2.2.2.2.2.1
      ((frame_operationsInput started).balancesMatch matched) inputHeld
    have lastSlot : last.slot = s.slot := (frame_processOperations operated).slot.trans slot
    have lastBounded (altair : .altair ≤ f) :
        ∀ key ∈ (last.currentSyncCommittee altair).value.pubkeys.toList,
          ∃ (i : Nat) (v : Validator), last.validators.data[i]? = some v ∧ v.pubkey = key ∧
            v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
            v.activationEpoch.toNat ≤ (getCurrentEpoch last).toNat + 1 := by
      intro key member
      rw [processOperations_currentSyncCommittee altair operated, committee] at member
      obtain ⟨i, v, found, keyed, assigned, bound⟩ := bounded altair key member
      have inputFound : input.validators.data[i]? = some v := registry ▸ found
      obtain ⟨w, read, life⟩ := operations.2.2.2.2.2.2.validators i v inputFound
      have keys := (frame_processOperations operated).pubkeysPrefix
      have pubkey : w.pubkey = v.pubkey := by
        obtain ⟨suffix, eq⟩ := keys
        have entry : (validatorKeys last)[i]? = (validatorKeys input)[i]? := by
          rw [← eq, List.getElem?_append_left]
          simpa [validatorKeys] using (Array.getElem?_eq_some_iff.mp inputFound).1
        simpa [validatorKeys, List.getElem?_map, inputFound, read] using entry
      refine ⟨i, w, read, pubkey.trans keyed, (life.activationEpoch assigned) ▸ assigned, ?_⟩
      simpa only [life.activationEpoch assigned, getCurrentEpoch, lastSlot] using bound
    split at synced
    · exact lastHeld.sync
        ((frame_processOperations operated).pubkeysDistinct
          ((frame_operationsInput started).pubkeysDistinct unique)) (lastBounded _) synced
    · cases synced; exact lastHeld
  intro early activation exits partials finite capped matched unique assigned held
  obtain ⟨registry, slot, _, committee, funded, _, _⟩ := head.2 early
  have inputFunded := funded activation exits partials finite capped held
  have lastFunded := operations.2.2.2.1 (frame_operationsInput started |>.balancesMatch matched)
    inputFunded
  have inputAssigned (altair : .altair ≤ f) :
      ∀ key ∈ (input.currentSyncCommittee altair).value.pubkeys.toList,
        ∃ (i : Nat) (v : Validator), input.validators.data[i]? = some v ∧ v.pubkey = key ∧
          v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    simpa only [committee, registry] using assigned altair
  split at synced
  · exact lastFunded.sync_of_provenance
      ((frame_processOperations operated).pubkeysDistinct
        ((frame_operationsInput started).pubkeysDistinct unique))
      (processOperations_syncCommittee_activation_assigned _ (inputAssigned _) operated) synced
  · cases synced
    exact lastFunded

private theorem CapStep.pending {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t) :
    CapStepR config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (BalancesMatch s → ∀ (candidate : Nat → Bool) j,
        preKeyCharge candidate t j ≤ preKeyCharge candidate s j +
          (((t.balances.data[j]?.map UInt64.toNat).getD 0) -
            ((s.balances.data[j]?.map UInt64.toNat).getD 0))) ∧
      (BalancesMatch s → ScheduledFree s → ScheduledFree t) := by
  let R := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (BalancesMatch a → BalancesMatch b) ∧
    (BalancesMatch a → UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
    (∀ c, PartialsAt c a → PartialsAt c b) ∧
    (BalancesMatch a → ∀ (candidate : Nat → Bool) j,
      ((a.balances.data[j]?.map UInt64.toNat).getD 0) ≤
          ((b.balances.data[j]?.map UInt64.toNat).getD 0) ∧
        preKeyCharge candidate b j ≤ preKeyCharge candidate a j +
          (((b.balances.data[j]?.map UInt64.toNat).getD 0) -
            ((a.balances.data[j]?.map UInt64.toNat).getD 0))) ∧
    (BalancesMatch a → ScheduledFree a → ScheduledFree b)
  have refl (a) : R a a :=
    ⟨CapStepR.refl a, id, fun _ => id, fun _ => id, fun _ _ _ => ⟨Nat.le_refl _, by simp⟩,
      fun _ => id⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c := by
    refine ⟨one.1.trans two.1, two.2.1 ∘ one.2.1,
      (fun matched held => two.2.2.1 (one.2.1 matched) (one.2.2.1 matched held)),
      fun c => two.2.2.2.1 c ∘ one.2.2.2.1 c, ?_,
      fun matched held => two.2.2.2.2.2 (one.2.1 matched) (one.2.2.2.2.2 matched held)⟩
    intro matched candidate j
    obtain ⟨first, paid⟩ := one.2.2.2.2.1 matched candidate j
    obtain ⟨second, paid'⟩ := two.2.2.2.2.1 (one.2.1 matched) candidate j
    exact ⟨first.trans second, by omega⟩
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → R state result.1.state :=
    fun ok => passPendingDeposits_of R refl (fun one two => trans one two)
      (fun credited => ⟨(CapStep.deposit credited).1,
        (applyPendingDeposit_kept credited).1, (CapStep.deposit credited).2.1,
        (CapStep.deposit (config := config) credited).2.2.1,
        fun matched candidate => preKeyCharge_deposit_growth candidate matched credited,
        (CapStep.deposit (config := config) credited).2.2.2⟩) ok
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals
    have passed := pass ‹_›
    exact ⟨passed.1.trans (CapStepR.data rfl), (fun matched held =>
      (passed.2.2.1 matched held).transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
      passed.2.2.2.1, fun matched candidate j => (passed.2.2.2.2.1 matched candidate j).2,
      fun matched held => (passed.2.2.2.2.2 matched held).transfer (UInt64.le_refl _) rfl
        (fun _ _ b _ _ _ read low => ⟨b, read, low⟩)⟩

/-- Rounding an effective balance cannot raise the capped Pre potential. -/
private theorem pre_effective_le {largest balance effective result : Gwei}
    (ok : updatedEffectiveBalance preset largest balance effective = .ok result) :
    max result.toNat (min balance.toNat largest.toNat) ≤
      max effective.toNat (min balance.toNat largest.toNat) := by
  rcases updatedEffectiveBalance_cases ok with rfl | rfl
  · exact Nat.le_refl _
  · have remainder : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    have rounded := UInt64.le_iff_toNat_le.mp (UInt64.sub_le remainder)
    simp only [Uint64.toNat_min]
    omega

private theorem preKeyCharge_effective {f : Fork} {s t : BeaconState preset f}
    (candidate : Nat → Bool) {i : Nat} {v : Validator} {balance result : Gwei}
    (found : getValidatorAt s i = .ok v) (read : getBalanceAt s i = .ok balance)
    (updated : updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v)
      balance v.effectiveBalance = .ok result)
    (set : s.setValidatorAt i { v with effectiveBalance := result } = .ok t) :
    ∀ j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j
  by_cases equal : j = i
  · subst j
    have atIndex := getValidatorAt_eq_ok_iff.mp found
    have atBalance := getBalanceAt_eq_ok_iff.mp read
    simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, ↓reduceIte, Option.map_some, Option.getD_some, atIndex, atBalance]
    by_cases chosen : candidate i = true
    · simp only [chosen, ↓reduceIte]
      split
      · exact pre_effective_le updated
      · exact Nat.le_refl _
    · simp only [chosen, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  · simp only [preKeyCharge, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, Ne.symm equal, ↓reduceIte, Nat.le_refl]

private theorem CapStep.effective {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) :
    CapStepR config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
      (preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        ScheduledFree s ((getCurrentEpoch s).toNat + 1) →
          ScheduledFree t ((getCurrentEpoch s).toNat + 1)) := by
  unfold processEffectiveBalanceUpdates at ok
  have result := foldlM_ok_invariant (fun t => CapStepR config s t ∧
    (preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
      (∀ {h : Fork} (v : Validator),
        preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
      UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
    (∀ c, PartialsAt c s → PartialsAt c t) ∧
    (∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
    t.slot = s.slot ∧
    (preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
      (∀ {h : Fork} (v : Validator),
        preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
      ScheduledFree s ((getCurrentEpoch s).toNat + 1) →
        ScheduledFree t ((getCurrentEpoch s).toNat + 1))) ?_
    ⟨CapStepR.refl s, fun _ _ => id, fun _ => id, fun _ _ => Nat.le_refl _, rfl, fun _ _ => id⟩ ok
  exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1, result.2.2.2.2.2⟩
  next =>
  intro middle i final previous ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, balance, read, next, changed, set⟩ := ok
  refine ⟨?_, ?_, (fun c held => (previous.2.2.1 c held).transfer
    (.setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩)
    (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact UInt64.le_refl _)
    (by obtain ⟨_, rfl⟩ := setValidatorAt_ok set; exact fun _ _ => id)),
    fun candidate j => (preKeyCharge_effective candidate found read changed set j).trans
      (previous.2.2.2.1 candidate j), ?_, ?_⟩
  · refine previous.1.trans (CapStep.setValidatorAt found ?_ ?_ set)
    · exact UInt64.le_refl _
    · intro bound
      have potential := pre_effective_le changed
      have capped := UInt64.le_iff_toNat_le.mp bound
      apply UInt64.le_iff_toNat_le.mpr
      change next.toNat ≤ (withdrawalMaxEffectiveBalance preset f v).toNat
      omega
  · intro aligned caps held
    exact (previous.2.1 aligned caps held).effective aligned (fun v _ => caps v)
      found read changed set
  · obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact previous.2.2.2.2.1
  · intro aligned caps held
    have input : ScheduledFree middle ((getCurrentEpoch middle).toNat + 1) := by
      simpa only [getCurrentEpoch, previous.2.2.2.2.1] using
        previous.2.2.2.2.2 aligned caps held
    have output := input.effective aligned (fun v _ => caps v) found read changed set
    simpa only [getCurrentEpoch, previous.2.2.2.2.1] using output

private theorem epoch_schedule_step {f : Fork} {s a b : BeaconState preset f}
    {k : EpochStage} {rest : List EpochStage}
    (edge : EpochStage.Edge config checks k a b)
    (first : EpochStage.justification ∈ k :: rest →
      k :: rest = EpochStage.epochStages ∧ a = s) :
    (EpochStage.justification ∈ rest → rest = EpochStage.epochStages ∧ b = s) ∧
      (Invariant s → a.finalizedCheckpoint.epoch ≤ getCurrentEpoch s →
        b.finalizedCheckpoint.epoch ≤ getCurrentEpoch s) := by
  constructor
  · intro remains
    have schedule := (first (List.mem_cons_of_mem k remains)).1
    simp only [EpochStage.epochStages, EpochStage.prefixStages, EpochStage.middleStages,
      EpochStage.tailStages, List.cons_append, List.nil_append, List.cons.injEq] at schedule
    obtain ⟨rfl, rfl⟩ := schedule
    simp at remains
  · intro valid checkpoint
    by_cases justification : k = .justification
    · subst k
      have same := (first List.mem_cons_self).2
      subst a
      have result :=
        processJustificationAndFinalization_invariant valid.ordered valid.settled edge
      exact UInt64.le_trans result.1.1 (UInt64.le_trans result.1.2 result.2.2.1)
    · simpa only [(EpochStage.Edge.frame edge justification).finalized] using checkpoint

private theorem preKeyCharge_epochEdge {f : Fork} {a b : BeaconState preset f} {k : EpochStage}
    (edge : EpochStage.Edge config checks k a b) (other : k ≠ .pendingDeposits)
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (held : UnassignedEligibleBalance a) (targets : AssignedTargets a)
    (finite : a.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH)
    (candidate : Nat → Bool) :
    ∀ i, preKeyCharge candidate b i ≤ preKeyCharge candidate a i := by
  cases k
  case registry => exact (CapStepR.registry edge).2.2.2.1 electra activation held finite candidate
  case effectiveBalances => exact (CapStep.effective (config := config) edge).2.2.2.1 candidate
  case rewards =>
    exact fun i => Nat.le_of_eq (preKeyCharge_rewardsAltair candidate
      (Nat.le_trans (by decide) electra) early held edge i)
  case slashings => exact preKeyCharge_slashings candidate edge
  case pendingDeposits => exact (other rfl).elim
  case pendingConsolidations =>
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact preKeyCharge_consolidations candidate targets edge
  all_goals
    obtain ⟨validators, balances, _⟩ :=
      edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    exact fun i => Nat.le_of_eq
      (preKeyCharge_same candidate (congrArg (·.data) validators) balances i)

/-- Each epoch stage keeps caps and the indexed assignment provenance. -/
private theorem CapStep.epochEdge {f : Fork} {a b : BeaconState preset f} {k : EpochStage}
    (edge : EpochStage.Edge config checks k a b) :
    CapStepR config a b ∧ (∀ c, PartialsAt c a → PartialsAt c b) := by
  cases k
  case registry => exact ⟨(CapStepR.registry edge).1, (CapStepR.registry edge).2.2.1⟩
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact ⟨(CapStep.pending edge).1, (CapStep.pending edge).2.2.1⟩
    · exact edge ▸ ⟨CapStepR.refl _, fun _ => id⟩
  case effectiveBalances =>
    exact ⟨(CapStep.effective edge).1, (CapStep.effective (config := config) edge).2.2.1⟩
  case rewards =>
    have step : CapStepR config a b :=
      CapStepR.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (by simp only [EpochStage.Edge] at edge; rw [processRewardsAndPenalties_frame edge])
      (by rw [processRewardsAndPenalties_frame edge])
      (fun fwd _ held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩))) fwd
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member))
    refine ⟨step, ?_⟩
    intro _ held
    apply held.transfer edge.registryLifecycle step.forward
    intro electra entry member
    rw [processRewardsAndPenalties_frame edge] at member
    exact member
  case slashings =>
    have step : CapStepR config a b :=
      CapStepR.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (by simp only [EpochStage.Edge] at edge; rw [processSlashings_frame edge])
      (by rw [processSlashings_frame edge])
      (fun fwd _ held => held.transfer (.of_data (congrArg (·.data)
        (edge.validators_eq ⟨nofun, nofun, nofun⟩))) fwd
        (fun _ _ member => (edge.samePendingQueue nofun) ▸ member))
    refine ⟨step, ?_⟩
    intro _ held
    apply held.transfer edge.registryLifecycle step.forward
    intro electra entry member
    rw [processSlashings_frame edge] at member
    exact member
  case pendingConsolidations =>
    have targets : getCurrentEpoch a ≤ getCurrentEpoch b →
        ∀ c, TargetsAt c a → TargetsAt c b := by
      intro fwd c held
      simp only [EpochStage.Edge] at edge
      split at edge
      · intro electra entry member index named
        obtain ⟨result, passed, _, queue⟩ := processPendingConsolidations_pass edge
        rw [queue] at member
        have before : entry ∈ (a.pendingConsolidations electra).data.toList :=
          List.mem_of_mem_drop member
        obtain ⟨v, found, assigned, active⟩ := held electra entry before index named
        exact ⟨v, by rw [(processPendingConsolidations_kept edge).1]; exact found, assigned,
          fun reach => UInt64.le_trans (active reach) fwd⟩
      · cases edge; exact held
    have step : CapStepR config a b := by
      refine CapStepR.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
        ?_ ?_ targets
      · simp only [EpochStage.Edge] at edge
        split at edge
        · exact (frame_processPendingConsolidations edge).slot
        · exact edge ▸ rfl
      · simp only [EpochStage.Edge] at edge
        split at edge
        · exact processPendingConsolidations_proposerLookahead edge
        · exact edge ▸ rfl
    refine ⟨step, ?_⟩
    · intro _ held
      apply held.transfer edge.registryLifecycle step.forward
      simp only [EpochStage.Edge] at edge
      split at edge
      · rw [processPendingConsolidations_pendingPartialWithdrawals edge]
        exact fun _ _ => id
      · cases edge; exact fun _ _ => id
  case proposerLookahead =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · have assigned := fun held => AssignedProposers.refresh held edge
      simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨{ CapStepR.data (s := a) (t := a) with
        proposers := fun _ => assigned }, fun _ => id⟩
    · exact edge ▸ ⟨CapStepR.refl _, fun _ => id⟩
  all_goals
    suffices fields : b.proposerLookahead = a.proposerLookahead ∧
        b.pendingPartialWithdrawals = a.pendingPartialWithdrawals by
      have step : CapStepR config a b :=
        CapStepR.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
        (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2 fields.1
        (fun fwd _ held => held.transfer (.of_data (congrArg (·.data)
          (edge.validators_eq ⟨nofun, nofun, nofun⟩))) fwd
          (fun _ _ member => (edge.samePendingQueue nofun) ▸ member))
      exact ⟨step, fun _ held => held.transfer edge.registryLifecycle step.forward
        (by rw [fields.2]; exact fun _ _ => id)⟩
    constructor <;>
    simp only [EpochStage.Edge] at edge
    all_goals
    first
    | (obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok edge
       · rfl
       · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
         rw [← rest])
    | (split at edge
       · rw [processInactivityUpdates_frame edge]
       · exact edge ▸ rfl)
    | (split at edge
       · rw [processEth1DataReset_frame edge]
       · exact edge ▸ rfl)
    | (split at edge
       · rw [processBuilderPendingPayments_eq edge]
       · exact edge ▸ rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge; rfl)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge; rfl)
    | (split at edge
       · unfold processHistoricalSummariesUpdate at edge
         simp only [bind, Except.bind, pure, Except.pure] at edge
         repeat' (split at edge <;> try cases edge)
         all_goals rfl
       · unfold processHistoricalRootsUpdate at edge
         simp only [bind_ok_iff, liftAccessor_ok] at edge
         obtain ⟨_, _, edge⟩ := edge
         split at edge
         · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at edge
           obtain ⟨_, _, _, _, rfl⟩ := edge
           rfl
         · cases edge; rfl)
    | (split at edge
       · subst edge; rfl
       · obtain ⟨u, computed, _, _, restored⟩ :=
           processParticipationRecordUpdates_eq (state := a) (Nat.lt_of_not_le (by assumption))
         obtain rfl := Except.ok.inj (computed.symm.trans edge)
         first
         | exact congrArg (·.proposerLookahead) restored
         | exact congrArg (·.pendingPartialWithdrawals) restored)
    | (split at edge
       · unfold processSyncCommitteeUpdates at edge
         simp only [bind, Except.bind, pure, Except.pure] at edge
         repeat' (split at edge <;> try cases edge)
         all_goals rfl
       · exact edge ▸ rfl)
    | (split at edge
       · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
         obtain ⟨_, _, _, _, rfl⟩ := edge; rfl
       · exact edge ▸ rfl)

private theorem CapStep.epoch_of {f : Fork} {s t : BeaconState preset f}
    (Q : List EpochStage → BeaconState preset f → Prop)
    (start : Q EpochStage.epochStages s)
    (each : ∀ k rest a b, EpochStage.Edge config checks k a b →
      CapStepR config s a → (BalancesMatch s → BalancesMatch a) →
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance a) →
      Q (k :: rest) a → Q rest b)
    (ok : processEpoch config checks s = .ok t) :
    CapStepR config s t ∧ (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧ Q [] t := by
  let R := fun (a b : BeaconState preset f) => CapStepR config a b ∧
    (BalancesMatch a → BalancesMatch b) ∧
    (∀ c, PartialsAt c a → PartialsAt c b) ∧
    (f < .glamsterdam →
      preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
      (∀ {h : Fork} (v : Validator),
        preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
      BalancesMatch a → AssignedTargets a →
      UnassignedEligibleBalance a → UnassignedEligibleBalance b)
  have refl (a) : R a a := ⟨CapStepR.refl a, id, fun _ => id, fun _ _ _ _ _ _ => id⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c :=
    ⟨one.1.trans two.1, two.2.1 ∘ one.2.1,
      fun c => two.2.2.1 c ∘ one.2.2.1 c,
      fun early activation aligned caps matched targets held =>
        two.2.2.2 early activation aligned caps (one.2.1 matched)
          (one.1.targets early targets)
          (one.2.2.2 early activation aligned caps matched targets held)⟩
  have step k {a b : BeaconState preset f}
      (edge : EpochStage.Edge config checks k a b) : R a b := by
      refine ⟨(CapStep.epochEdge edge).1, ?_, (CapStep.epochEdge edge).2, ?_⟩
      · by_cases justification : k = .justification
        · subst k
          obtain ⟨validators, balances, _⟩ :=
            edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          simpa only [BalancesMatch, validators, balances] using (id : BalancesMatch a → _)
        · exact (EpochStage.Edge.frame edge justification).balancesMatch
      · intro early activation aligned caps matched targets held
        cases k
        case registry => exact (CapStepR.registry edge).2.1 activation held
        case rewards => exact held.rewards early edge
        case slashings => exact held.slashings early edge
        case effectiveBalances =>
          exact (CapStep.effective (config := config) edge).2.1 aligned caps held
        case pendingDeposits | pendingConsolidations =>
          simp only [EpochStage.Edge] at edge
          split at edge
          · first
            | exact (CapStep.pending edge).2.1 matched held
            | exact held.consolidations targets edge
          · cases edge; exact held
        all_goals
          obtain ⟨validators, balances, _⟩ :=
            edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          exact held.transfer (congrArg (·.data) validators)
            (fun _ _ b _ _ read low => ⟨b, by rw [balances]; exact read, low⟩)
  have whole := (processEpoch_trace ok).induction_on
    (fun rest b => R s b ∧ Q rest b) ⟨refl s, start⟩ (by
      intro k rest a b computed held
      have edge := EpochStage.action_cases.mp computed
      exact ⟨trans held.1 (step k edge),
        each k rest a b edge held.1.1 held.1.2.1 held.1.2.2.2 held.2⟩)
  exact ⟨whole.1.1, whole.1.2.2.1, whole.1.2.2.2, whole.2⟩

private theorem CapStepR.epoch {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) :
    CapStepR config s t ∧ (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (f < .glamsterdam → Invariant s → getCurrentEpoch s < FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        MaxEffectiveBalancesAligned preset →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        TargetsAt True s → UnassignedEligibleBalance s → ScheduledFree s →
          ScheduledFree t ((getCurrentEpoch s).toNat + 1)) := by
  classical
  let Q (rest : List EpochStage) (a : BeaconState preset f) :=
    rest <:+ EpochStage.epochStages ∧ a.slot = s.slot ∧
    (EpochStage.justification ∈ rest → rest = EpochStage.epochStages ∧ a = s) ∧
    (f < .glamsterdam → Invariant s → getCurrentEpoch s < FAR_FUTURE_EPOCH →
      preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
      MaxEffectiveBalancesAligned preset →
      (∀ {h : Fork} (v : Validator),
        preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
      TargetsAt True s → UnassignedEligibleBalance s → ScheduledFree s →
        a.finalizedCheckpoint.epoch ≤ getCurrentEpoch s ∧
        ScheduledFree a ((getCurrentEpoch s).toNat +
          if EpochStage.effectiveBalances ∈ rest then 0 else 1))
  have initial : Q EpochStage.epochStages s := by
    refine ⟨List.suffix_rfl, rfl, fun _ => ⟨rfl, rfl⟩, ?_⟩
    intro _ valid _ _ _ _ _ _ held
    refine ⟨UInt64.le_trans valid.ordered.1 (UInt64.le_trans valid.ordered.2
      (UInt64.le_trans valid.settled (getPreviousEpoch_le s))), ?_⟩
    simpa [EpochStage.epochStages, EpochStage.prefixStages, EpochStage.middleStages] using held
  have whole := CapStep.epoch_of Q initial (fun k rest a b edge previous matched funded state => by
    obtain ⟨schedule, slot, first, carried⟩ := state
    have scheduleStep := epoch_schedule_step edge first
    have slotStep := edge.slot_eq
    refine ⟨(List.suffix_cons k rest).trans schedule, slotStep.trans slot,
      scheduleStep.1, ?_⟩
    · intro early valid finite activation aligned caps targets unassigned held
      obtain ⟨checkpoint, reserve⟩ := carried early valid finite activation aligned caps targets
        unassigned held
      have checkpointStep := scheduleStep.2 valid checkpoint
      refine ⟨checkpointStep, ?_⟩
      by_cases before : .effectiveBalances ∈ rest
      · have input : ScheduledFree a := by
          simpa only [List.mem_cons, before, or_true, ↓reduceIte, Nat.add_zero,
            getCurrentEpoch, slot] using reserve
        have output : ScheduledFree b := by
          cases k
          case registry =>
            exact (CapStepR.registry edge).2.2.2.2 activation
              (UInt64.lt_of_le_of_lt checkpoint finite)
              (funded early activation aligned.1
                caps valid.balancesMatch targets.old unassigned) input
          case rewards =>
            exact input.rewards early edge
          case slashings =>
            exact input.slashings early edge
          case effectiveBalances =>
            simp only [EpochStage.epochStages, EpochStage.prefixStages,
              EpochStage.middleStages, EpochStage.tailStages, List.cons_append,
              List.nil_append, List.suffix_cons_iff, List.suffix_nil, List.cons.injEq,
              reduceCtorEq, false_and, false_or, true_and, or_false] at schedule
            obtain rfl := schedule
            simp at before
          case pendingDeposits =>
            simp only [EpochStage.Edge] at edge
            split at edge
            · exact (CapStep.pending edge).2.2.2.2 (matched valid.balancesMatch) input
            · subst b
              exact input
          case pendingConsolidations =>
            simp only [EpochStage.Edge] at edge
            split at edge
            · exact input.consolidations (previous.targetsAt early True targets) edge
            · subst b
              exact input
          all_goals
            obtain ⟨validators, balances, _⟩ :=
              edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
            exact input.reframe (by simp only [getCurrentEpoch, slotStep, Nat.le_refl])
              (by simp only [getCurrentEpoch, slotStep, Nat.le_refl])
              (congrArg (·.data) validators) (congrArg (·.data) balances)
        simpa only [before, ↓reduceIte, Nat.add_zero, getCurrentEpoch, slotStep, slot] using output
      · by_cases effective : k = .effectiveBalances
        · subst k
          have input : ScheduledFree a := by
            simpa only [List.mem_cons, true_or, ↓reduceIte, Nat.add_zero, getCurrentEpoch, slot]
              using reserve
          have output := (CapStep.effective (config := config) edge).2.2.2.2 aligned.1 caps
            (input.restrict (Nat.le_succ _))
          simpa only [before, ↓reduceIte, getCurrentEpoch, slot] using output
        · have input : ScheduledFree a ((getCurrentEpoch s).toNat + 1) := by
            simpa only [List.mem_cons, eq_comm, effective, before, false_or, or_false,
              ↓reduceIte] using reserve
          have late : k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧
              k ≠ .pendingDeposits ∧ k ≠ .pendingConsolidations := by
            simp only [EpochStage.epochStages, EpochStage.prefixStages,
              EpochStage.middleStages, EpochStage.tailStages, List.cons_append,
              List.nil_append, List.suffix_cons_iff, List.suffix_nil, List.cons.injEq,
              reduceCtorEq] at schedule
            rcases schedule with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
            all_goals obtain ⟨rfl, rfl⟩ := h
            all_goals simp_all
          obtain ⟨validators, balances, _⟩ :=
            edge.records ⟨late.1, late.2.1, late.2.2.1, late.2.2.2.1,
              late.2.2.2.2, effective⟩
          have output := input.reframe (Nat.le_refl _)
            (by simp only [getCurrentEpoch, slotStep, Nat.le_refl])
            (congrArg (·.data) validators) (congrArg (·.data) balances)
          simpa only [before, ↓reduceIte] using output) ok
  exact ⟨whole.1, whole.2.1, whole.2.2.1, by
    intro early valid finite activation aligned caps targets unassigned held
    exact (whole.2.2.2.2.2.2 early valid finite activation aligned caps targets unassigned
      held).2⟩

private theorem CapStepR.slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) :
    CapStepR config s t ∧ (∀ c, PartialsAt c s → PartialsAt c t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (f < .glamsterdam → Invariant s → getCurrentEpoch s < FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        MaxEffectiveBalancesAligned preset →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        TargetsAt True s → UnassignedEligibleBalance s → ScheduledFree s →
          ScheduledFree t) := by
  have later := (runKept_advanceSlot ok).later
  obtain ⟨next, cached, advanced, sum, cache, advance, rfl⟩ := advanceSlot_ok ok
  have cachedInvariant := (frame_processSlot cache).invariant
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · rename_i boundary
    obtain ⟨step, partials, funded, scheduled⟩ := CapStepR.epoch advance
    have same : advanced.slot = s.slot := by
      obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame advance
      rw [frame.slot, processJustificationAndFinalization_slot justifiedOk]
    refine ⟨{
      capped := step.capped
      monotone := step.monotone
      forward := later
      forks := step.forks
      proposers := step.proposers
      retired := step.retired
      withdrawal := step.withdrawal
      appended := step.appended
      frozen := step.frozen
      targetsAt := ?_ }, ?_, ?_, ?_⟩
    · intro early c held
      refine (step.targetsAt early c held).transfer (.of_data rfl) ?_ (fun _ _ => id)
      have : getCurrentEpoch advanced = getCurrentEpoch s := by
        rw [getCurrentEpoch, getCurrentEpoch, same]
      exact UInt64.le_trans (UInt64.le_of_eq this) later
    · intro c held
      refine (partials c held).transfer (.of_data rfl) ?_ (fun _ _ => id)
      have : getCurrentEpoch advanced = getCurrentEpoch s := by
        rw [getCurrentEpoch, getCurrentEpoch, same]
      exact UInt64.le_trans (UInt64.le_of_eq this) later
    · intro early activation aligned caps matched targets held
      exact (funded early activation aligned caps matched targets held).transfer rfl
        (fun _ _ b _ _ read low => ⟨b, read, low⟩)
    · intro early valid finite activation aligned caps targets unassigned held
      have reserve := scheduled early (cachedInvariant valid) finite activation aligned caps
        targets unassigned held
      have epochs := nextSlot_epoch_of_boundary sum boundary
      exact reserve.reframe (by simpa only [getCurrentEpoch_toNat] using Nat.le_of_eq epochs.symm)
        (by simp only [getCurrentEpoch_toNat, same]; omega) rfl rfl
  · cases advance
    exact ⟨{
      capped := id
      monotone := fun _ v found => ⟨v, found, UInt64.le_refl _⟩
      forward := later
      forks := Nat.le_refl _
      proposers := fun _ => id
      targetsAt := fun _ _ held => held.transfer (.of_data rfl) later (fun _ _ => id)
      retired := (CapStepR.refl (config := config) s).retired
      withdrawal := (CapStepR.refl s).withdrawal
      appended := (CapStepR.refl s).appended
      frozen := (CapStepR.refl (config := config) s).frozen },
      fun _ held => held.transfer (.of_data rfl) later (fun _ _ => id),
      fun _ _ _ _ _ _ held => held.transfer rfl
        (fun _ _ b _ _ read low => ⟨b, read, low⟩),
      fun _ _ _ _ _ _ _ _ held => held.transfer later rfl
        (fun _ _ b _ _ _ read low => ⟨b, read, low⟩)⟩

private theorem CapStep.carry {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h) (slot : t.slot = s.slot := by rfl)
    (proposers : h < .glamsterdam → AssignedProposers s → AssignedProposers t := by
      intro _ _
      unfold AssignedProposers
      intro fulu
      have impossible := fulu
      simp +decide at impossible)
    (targets : h < .glamsterdam → ∀ c, TargetsAt c s → TargetsAt c t := by
      intro _ c held
      unfold TargetsAt
      intro electra entry member
      first
      | (have impossible := electra; simp +decide at impossible)
      | simp [carryFields] at member) : CapStepR config s t where
  capped capped v member := UInt64.le_trans (capped v (same ▸ member))
    (withdrawalMaxEffectiveBalance_mono activation compounding forks id)
  monotone _i v found := ⟨v, same ▸ found,
    withdrawalMaxEffectiveBalance_mono activation compounding forks id⟩
  forward := by
    rw [getCurrentEpoch, getCurrentEpoch, slot]
    exact UInt64.le_refl _
  forks := forks
  proposers := proposers
  targetsAt := targets
  retired i v w before after _ flag _ := by
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨flag, rfl, rfl⟩
  withdrawal i v w before after := by
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨fun flag assigned => ⟨flag, assigned, rfl⟩,
      fun _ unslashed slashed => by simp [unslashed] at slashed⟩

  appended _ j w outside found _ := by
    rw [same] at found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    omega
  frozen i v w before after _ := by
    rw [same, before, Option.some.injEq] at after
    subst w
    exact ⟨rfl, id⟩

private theorem CapStep.preActivation {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queuePreActivation s electra i = .ok t) :
    CapStepR config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      t.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok balance
  refine ⟨?_, ?_, ?_⟩
  · have changed := CapStep.setValidator (config := config) (v := v)
      (by simpa only [getValidator, BeaconState.putBalance] using found)
      (by exact UInt64.le_refl _) (by intro _; exact UInt64.zero_le) validator
    exact {
      capped := changed.capped
      monotone := changed.monotone
      forward := changed.forward
      forks := changed.forks
      proposers := changed.proposers
      targetsAt := changed.targetsAt
      retired := changed.retired
      withdrawal := changed.withdrawal
      appended := changed.appended
      frozen := changed.frozen }
  · intro held
    obtain ⟨_, rfl⟩ := setValidator_ok validator
    intro j w located pending
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at located
    split at located
    · rename_i equal
      subst j
      cases located
      have before := getValidator_eq_ok_iff.mp found
      have unslashed := (held i.toNat v before pending).2.2
      exact ⟨⟨0, by simp [BeaconState.putValidator, BeaconState.putBalance], UInt64.le_refl _⟩,
        fun impossible => (impossible rfl).elim, unslashed⟩
    · rename_i different
      obtain ⟨⟨b, read, low⟩, eligible, unslashed⟩ := held j w located pending
      refine ⟨⟨b, ?_, low⟩, eligible, unslashed⟩
      simpa [BeaconState.putValidator, BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, different] using read
  · obtain ⟨_, rfl⟩ := setValidator_ok validator
    rfl

/-- Queueing a waiting key leaves each assigned key, with its record and balance, as it was. -/
private theorem queuePreActivation_assigned {a b : BeaconState preset .pectra}
    {index : ValidatorIndex}
    (pending : ∀ v, a.validators.data[index.toNat]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH)
    (ok : queuePreActivation a (by decide) index = .ok b) :
    b.slot = a.slot ∧ b.validators.data.size = a.validators.data.size ∧
      ∀ (j : Nat) (v : Validator), a.validators.data[j]? = some v →
        ∃ w, b.validators.data[j]? = some w ∧ w.activationEpoch = v.activationEpoch ∧
          (v.activationEpoch ≠ FAR_FUTURE_EPOCH →
            w = v ∧ b.balances.data[j]? = a.balances.data[j]?) := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok balance
  obtain ⟨inside, rfl⟩ := setValidator_ok validator
  have read : a.validators.data[index.toNat]? = some v := by
    unfold getValidator at found
    split at found <;> simp_all
  refine ⟨rfl, by simp [BeaconState.putValidator, BeaconState.putBalance], ?_⟩
  intro j old oldFound
  by_cases equal : index.toNat = j
  · subst j
    have same := Option.some.inj (oldFound.symm.trans read)
    subst old
    exact ⟨{ v with effectiveBalance := 0, activationEligibilityEpoch := FAR_FUTURE_EPOCH },
      by simp [BeaconState.putValidator, BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set],
      rfl, fun assigned => (assigned (pending v read)).elim⟩
  · refine ⟨old, ?_, rfl, fun _ => ⟨rfl, ?_⟩⟩
    · simpa [BeaconState.putValidator, BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set, Array.getElem?_set, equal] using oldFound
    · simp [BeaconState.putValidator, BeaconState.putBalance, equal]

/-- Every index that the Electra upgrade queues belongs to a key with no assigned activation. -/
private theorem preActivationIndices_waiting {a : BeaconState preset .pectra}
    {index : ValidatorIndex} (member : index ∈ preActivationIndices a) :
    ∃ v, a.validators.data[index.toNat]? = some v ∧ v.activationEpoch = FAR_FUTURE_EPOCH := by
  obtain ⟨⟨v, i⟩, sorted, rfl⟩ := List.mem_map.mp member
  rw [List.mem_mergeSort] at sorted
  obtain ⟨member, waiting⟩ := List.mem_filter.mp sorted
  have found : a.validators.data[i]? = some v := by
    simpa using List.mem_zipIdx_iff_getElem?.mp member
  have small := toNat_toUInt64_of_lt (state := a) (a.validators.bound (by decide))
    (Array.getElem?_eq_some_iff.mp found).1
  exact ⟨v, by simpa [small] using found, by simpa using waiting⟩

/-- The queued keys leave the assigned ones of the registry as they were. -/
private theorem queuePreActivation_fold_assigned (a b : BeaconState preset .pectra)
    (ok : (preActivationIndices a).foldlM
      (fun s i => queuePreActivation s (by decide) i) a = .ok b) :
    b.slot = a.slot ∧ b.validators.data.size = a.validators.data.size ∧
      ∀ (j : Nat) (v : Validator), a.validators.data[j]? = some v →
        ∃ w, b.validators.data[j]? = some w ∧ w.activationEpoch = v.activationEpoch ∧
          (v.activationEpoch ≠ FAR_FUTURE_EPOCH →
            w = v ∧ b.balances.data[j]? = a.balances.data[j]?) := by
  refine foldlM_ok_invariant_of_mem (xs := preActivationIndices a)
    (P := fun s => s.slot = a.slot ∧ s.validators.data.size = a.validators.data.size ∧
      ∀ (j : Nat) (v : Validator), a.validators.data[j]? = some v →
        ∃ w, s.validators.data[j]? = some w ∧ w.activationEpoch = v.activationEpoch ∧
          (v.activationEpoch ≠ FAR_FUTURE_EPOCH →
            w = v ∧ s.balances.data[j]? = a.balances.data[j]?))
    ?_ ⟨rfl, rfl, fun j v found => ⟨v, found, rfl, fun _ => ⟨rfl, rfl⟩⟩⟩ ok
  intro s x t member ⟨slot, size, kept⟩ step
  obtain ⟨va, foundA, waiting⟩ := preActivationIndices_waiting member
  obtain ⟨w, located, epoch, _⟩ := kept x.toNat va foundA
  obtain ⟨slot', size', next⟩ := queuePreActivation_assigned (a := s) (b := t) (index := x)
    (fun v found => by
      rw [located, Option.some.injEq] at found
      subst v
      exact epoch.trans waiting) step
  refine ⟨slot'.trans slot, size'.trans size, ?_⟩
  intro j v found
  obtain ⟨u, locatedU, epochU, keepU⟩ := kept j v found
  obtain ⟨z, locatedZ, epochZ, keepZ⟩ := next j u locatedU
  refine ⟨z, locatedZ, epochZ.trans epochU, fun assigned => ?_⟩
  obtain ⟨rfl, balanceU⟩ := keepU assigned
  obtain ⟨sameZ, balanceZ⟩ := keepZ (epochU ▸ assigned)
  exact ⟨sameZ, balanceZ.trans balanceU⟩

private theorem ScheduledFree.preActivation {a b : BeaconState preset .pectra}
    (held : ScheduledFree a) (slot : b.slot = a.slot)
    (size : b.validators.data.size = a.validators.data.size)
    (kept : ∀ (j : Nat) (v : Validator), a.validators.data[j]? = some v →
      ∃ w, b.validators.data[j]? = some w ∧ w.activationEpoch = v.activationEpoch ∧
        (v.activationEpoch ≠ FAR_FUTURE_EPOCH →
          w = v ∧ b.balances.data[j]? = a.balances.data[j]?)) :
    ScheduledFree b := by
  intro j w located future assigned
  have outside : j < a.validators.data.size := by
    have := (Array.getElem?_eq_some_iff.mp located).1
    omega
  have read : a.validators.data[j]? = some a.validators.data[j] :=
    Array.getElem?_eq_some_iff.mpr ⟨outside, rfl⟩
  obtain ⟨u, locatedU, epoch, keep⟩ := kept j _ read
  obtain rfl := Option.some.inj (located.symm.trans locatedU)
  obtain ⟨same, balances⟩ := keep (epoch ▸ assigned)
  have cur : getCurrentEpoch b = getCurrentEpoch a := by simp only [getCurrentEpoch, slot]
  have future' : (getCurrentEpoch a).toNat < a.validators.data[j].activationEpoch.toNat := by
    rw [← cur, ← epoch]
    exact future
  obtain ⟨minimum, funding, unslashed⟩ := held j _ read future' (epoch ▸ assigned)
  subst same
  refine ⟨minimum, fun distant => ?_, unslashed⟩
  obtain ⟨balance, located, low⟩ := funding (by rw [← cur]; exact distant)
  exact ⟨balance, by rw [balances]; exact located, low⟩

private theorem ScheduledFree.compoundingExcess {config : Config}
    {a b : BeaconState preset .pectra}
    {index : Nat} (held : ScheduledFree a)
    (bound : ∀ v ∈ a.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE)
    (ok : queueCompoundingExcess a (by decide) index = .ok b) :
    ScheduledFree b ∧ ∀ v ∈ b.validators.data,
      v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE := by
  unfold queueCompoundingExcess at ok
  split at ok
  · split at ok
    · have excess := liftAccessor_ok.mp ok
      exact ⟨(CapStep.excess (config := config) excess).2.2.2 held
          (fun v found _ _ => bound v (Array.mem_of_getElem? found)),
        fun w member => bound w
          (by rw [queueExcessActiveBalance_validators excess] at member; exact member)⟩
    · cases ok; exact ⟨held, bound⟩
  · cases ok; exact ⟨held, bound⟩

private theorem CapStepR.upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) :
    CapStepR config s.state t.val.state ∧
      (t.val.fork < .glamsterdam → ∀ c, PartialsAt c s.state → PartialsAt c t.val.state) ∧
      (t.val.fork < .glamsterdam →
        (∀ v ∈ s.state.validators.data,
          v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset s.fork v) →
        UnassignedEligibleBalance s.state → UnassignedEligibleBalance t.val.state) ∧
      (t.val.fork < .glamsterdam →
        (.pectra ≤ t.val.fork → ∀ v ∈ s.state.validators.data,
          v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset s.fork v) →
        ScheduledFree s.state → ScheduledFree t.val.state) := by
  have frame := upgradeFrame_upgradeNext ok
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact ⟨CapStep.carry (upgradeToAltair_spec upgraded).1
      activation compounding (by change Fork.phase0 ≤ .altair; decide) frame.slot,
      fun _ _ _ impossible => (by decide : ¬ Fork.pectra ≤ .altair) impossible |>.elim,
      fun _ _ held => held.transfer (upgradeToAltair_spec upgraded).1
        (fun _ _ b _ _ read low => ⟨b, by
          rw [(upgradeToAltair_spec upgraded).2.1]; exact read, low⟩),
      fun _ _ held => held.reframe
        (by
          change (getCurrentEpoch state).toNat ≤ (getCurrentEpoch _).toNat
          rw [getCurrentEpoch, getCurrentEpoch, show _ = state.slot from frame.slot])
        (by
          change (getCurrentEpoch state).toNat ≤ (getCurrentEpoch _).toNat
          rw [getCurrentEpoch, getCurrentEpoch, show _ = state.slot from frame.slot])
        (upgradeToAltair_spec upgraded).1
        (upgradeToAltair_spec upgraded).2.1⟩
  · subst ok
    exact ⟨CapStep.carry rfl activation compounding (by change Fork.altair ≤ .bellatrix; decide),
      fun _ _ _ impossible => (by decide : ¬ Fork.pectra ≤ .bellatrix) impossible |>.elim,
      (fun _ _ held => held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
      fun _ _ held => held.reframe (Nat.le_refl _) (Nat.le_refl _) rfl rfl⟩
  · subst ok
    exact ⟨CapStep.carry rfl activation compounding (by change Fork.bellatrix ≤ .shapella; decide),
      fun _ _ _ impossible => (by decide : ¬ Fork.pectra ≤ .shapella) impossible |>.elim,
      (fun _ _ held => held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
      fun _ _ held => held.reframe (Nat.le_refl _) (Nat.le_refl _) rfl rfl⟩
  · subst ok
    exact ⟨CapStep.carry rfl activation compounding (by change Fork.shapella ≤ .dencun; decide),
      fun _ _ _ impossible => (by decide : ¬ Fork.pectra ≤ .dencun) impossible |>.elim,
      (fun _ _ held => held.transfer rfl (fun _ _ b _ _ read low => ⟨b, read, low⟩)),
      fun _ _ held => held.reframe (Nat.le_refl _) (Nat.le_refl _) rfl rfl⟩
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    let R := fun (a b : BeaconState preset .pectra) => CapStepR config a b ∧
      ((∀ v ∈ a.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) →
        ∀ v ∈ b.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) ∧
      ((∀ v ∈ a.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE) →
        UnassignedEligibleBalance a → UnassignedEligibleBalance b) ∧
      b.pendingPartialWithdrawals = a.pendingPartialWithdrawals
    have trans {a b c} (one : R a b) (two : R b c) : R a c :=
      ⟨one.1.trans two.1, two.2.1 ∘ one.2.1,
        (fun bound => two.2.2.1 (one.2.1 bound) ∘ one.2.2.1 bound),
        two.2.2.2.trans one.2.2.2⟩
    have queuedStep : R _ _ := foldlM_ok_invariant (R _)
      (fun a index b previous computed => trans previous (by
        refine ⟨(CapStep.preActivation computed).1, ?_,
          (fun _ => (CapStep.preActivation (config := config) computed).2.1),
          (CapStep.preActivation (config := config) computed).2.2⟩
        intro bound
        simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at computed
        obtain ⟨v, _, _, _, _, _, middle, balance, last, validator, rfl⟩ := computed
        obtain ⟨_, rfl⟩ := setBalance_ok balance
        obtain ⟨inside, rfl⟩ := setValidator_ok validator
        intro w member
        rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
        · exact bound w old
        · exact UInt64.zero_le))
      ⟨CapStepR.refl _, id, (fun _ => id), rfl⟩ queued
    have compoundedStep : R _ _ := foldlM_ok_invariant (R _)
      (fun a index b previous computed => trans previous (by
        unfold queueCompoundingExcess at computed
        split at computed
        · split at computed
          · have excess := liftAccessor_ok.mp computed
            exact ⟨(CapStep.excess excess).1,
              fun bound w member => bound w
                (by rw [queueExcessActiveBalance_validators excess] at member; exact member),
              (fun bound held => (CapStep.excess (config := config) excess).2.1 held
                (fun v found _ => bound v (Array.mem_of_getElem? found))),
              (CapStep.excess (config := config) excess).2.2.1⟩
          · cases computed; exact ⟨CapStepR.refl _, id, (fun _ => id), rfl⟩
        · cases computed; exact ⟨CapStepR.refl _, id, (fun _ => id), rfl⟩))
      ⟨CapStepR.refl _, id, (fun _ => id), rfl⟩ compounded
    refine ⟨(CapStep.carry (s := state) (by rfl)
      activation compounding (by decide) (by rfl)
      (by intro _ _ fulu; exact (by decide : ¬ Fork.fusaka ≤ .pectra) fulu |>.elim)
      (by intro _ _ _ electra entry member
          simp [carryFields, show ¬ Fork.pectra ≤ .dencun by decide] at member)).trans
        (queuedStep.1.trans compoundedStep.1), ?_, ?_,
        ?_⟩
    · intro _ _ _ electra entry member
      rw [compoundedStep.2.2.2, queuedStep.2.2.2] at member
      simp [carryFields, show ¬ Fork.pectra ≤ .dencun by decide] at member
    · intro _ capped held
      have bound : ∀ v ∈ state.validators.data,
          v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE := by
        intro v member
        exact UInt64.le_trans (capped v member) (by
          simpa [withdrawalMaxEffectiveBalance, show ¬ Fork.pectra ≤ .dencun by decide]
            using activation)
      exact compoundedStep.2.2.1 (queuedStep.2.1 bound)
        (queuedStep.2.2.1 bound (held.transfer rfl
          (fun _ _ b _ _ read low => ⟨b, read, low⟩)))
    · intro _ cappedAll held
      have capped := cappedAll (show Fork.pectra ≤ .pectra by decide)
      have bound : ∀ v ∈ state.validators.data,
          v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE := by
        intro v member
        exact UInt64.le_trans (capped v member) (by
          simpa [withdrawalMaxEffectiveBalance, show ¬ Fork.pectra ≤ .dencun by decide]
            using activation)
      have kept := queuePreActivation_fold_assigned _ _ queued
      have waiting := ScheduledFree.preActivation
        (held.reframe (Nat.le_refl _) (Nat.le_refl _) rfl rfl) kept.1 kept.2.1 kept.2.2
      exact (foldlM_ok_invariant (fun b => ScheduledFree b ∧
        ∀ v ∈ b.validators.data, v.effectiveBalance ≤ preset.MIN_ACTIVATION_BALANCE)
        (fun _ _ _ previous computed =>
          ScheduledFree.compoundingExcess (config := config) previous.1 previous.2
            computed)
        ⟨waiting, queuedStep.2.1 bound⟩ compounded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    refine ⟨CapStep.carry (upgradeToFulu_spec upgraded).1
      activation compounding (by change Fork.pectra ≤ .fusaka; decide) frame.slot
      (fun _ _ => ?_) (fun _ _ held => ?_), ?_, fun _ _ held =>
        held.transfer (upgradeToFulu_spec upgraded).1
          (fun _ _ b _ _ read low => ⟨b, by
            rw [(upgradeToFulu_spec upgraded).2.1]; exact read, low⟩),
        fun _ _ held => held.transfer
          (by rw [getCurrentEpoch, getCurrentEpoch, show _ = state.slot from frame.slot]
              exact UInt64.le_refl _)
          (upgradeToFulu_spec upgraded).1
          (fun _ _ b _ _ _ read low => ⟨b, by
            rw [(upgradeToFulu_spec upgraded).2.1]; exact read, low⟩)⟩
    · obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      intro _ i member
      exact initializeProposerLookahead_assigned (liftAccessor_ok.mp initialized) i member
    · obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      intro electra entry member index named
      obtain ⟨v, found, assigned, active⟩ :=
        held (show Fork.pectra ≤ .pectra by decide) entry
          (by simpa [carryFields, carryList] using member) index named
      refine ⟨v, by simpa [carryFields, carryRooted] using found, assigned,
        fun reach => UInt64.le_trans (active reach) ?_⟩
      rw [getCurrentEpoch, getCurrentEpoch, show _ = state.slot from frame.slot]
      exact UInt64.le_refl _
    · intro _ c held electra entry member
      obtain ⟨lookahead, initialized, final⟩ := bind_ok_iff.mp upgraded
      cases final
      obtain ⟨v, found, assigned, active⟩ :=
        held (show Fork.pectra ≤ .pectra by decide) entry
          (by simpa [carryFields, carryList] using member)
      refine ⟨v, by simpa [carryFields, carryRooted] using found, assigned,
        fun reach => UInt64.le_trans (active reach) ?_⟩
      rw [getCurrentEpoch, getCurrentEpoch, show _ = state.slot from frame.slot]
      exact UInt64.le_refl _
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact ⟨CapStep.carry (upgradeToGloas_spec upgraded).1
      activation compounding (by change Fork.fusaka ≤ .glamsterdam; decide) frame.slot
      (fun early => (Nat.lt_irrefl _ early).elim)
      (fun early => (Nat.lt_irrefl _ early).elim),
      (fun early => (Nat.lt_irrefl _ early).elim),
      (fun early => (Nat.lt_irrefl _ early).elim),
      fun early => (Nat.lt_irrefl _ early).elim⟩
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain rfl := upgradeToHeze_ok_iff.mp upgraded
    exact ⟨CapStep.carry (upgradeHezeFields_lists state).1
      activation compounding (by change Fork.glamsterdam ≤ .hegota; decide) frame.slot
      (fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim)
      (fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim),
      (fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim),
      (fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim),
      fun early => ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim⟩

private theorem preKeyCharge_upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t)
    (electra : .pectra ≤ s.fork) (early : t.val.fork < .glamsterdam)
    (candidate : Nat → Bool) :
    ∀ i, preKeyCharge candidate t.val.state i = preKeyCharge candidate s.state i := by
  obtain ⟨fork, state⟩ := s
  cases fork <;> simp +decide at electra
  all_goals
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨validators, balances, _⟩ := upgradeToFulu_spec upgraded
    intro i
    simp only [preKeyCharge, validators, balances, withdrawalMaxEffectiveBalance,
      show Fork.pectra ≤ .pectra from by decide,
      show Fork.pectra ≤ .fusaka from by decide]
  · obtain ⟨_, _, rfl⟩ := ok
    exact (Nat.lt_irrefl _ early).elim
  · obtain ⟨_, _, rfl⟩ := ok
    exact ((by decide : ¬ Fork.hegota < .glamsterdam) early).elim

private theorem CapStep.upgrades {s t : ForkedBeaconState preset}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processUpgrades config checks s = .ok t) :
    CapStepR config s.state t.state ∧
      (t.fork < .glamsterdam → ∀ c, PartialsAt c s.state → PartialsAt c t.state) ∧
      (t.fork < .glamsterdam →
        (∀ v ∈ s.state.validators.data,
          v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset s.fork v) →
        UnassignedEligibleBalance s.state → UnassignedEligibleBalance t.state) ∧
      (.pectra ≤ s.fork → t.fork < .glamsterdam → ∀ candidate i,
        preKeyCharge candidate t.state i = preKeyCharge candidate s.state i) ∧
      (t.fork < .glamsterdam →
        (.pectra ≤ t.fork → ∀ v ∈ s.state.validators.data,
          v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset s.fork v) →
        ScheduledFree s.state → ScheduledFree t.state) := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    obtain ⟨first, partials, funded, scheduled⟩ := CapStepR.upgrade activation compounding nextOk
    obtain ⟨last, assigned, retained, charge, reserve⟩ := ih next rest
    exact ⟨first.trans last,
      (fun early c => assigned early c ∘ partials (Nat.lt_of_le_of_lt last.forks early) c),
      (fun early capped => retained early (first.capped capped) ∘
        funded (Nat.lt_of_le_of_lt last.forks early) capped),
      fun electra early candidate i =>
        (charge (Nat.le_trans electra first.forks) early candidate i).trans
          (preKeyCharge_upgrade nextOk electra (Nat.lt_of_le_of_lt last.forks early)
            candidate i),
      fun early capped => reserve early
          (fun reached => first.capped (capped reached)) ∘
        scheduled (Nat.lt_of_le_of_lt last.forks early)
          (fun reached => capped (Nat.le_trans reached last.forks))⟩
  | case2 s notDue =>
    cases ok
    exact ⟨CapStepR.refl _, fun _ _ => id, (fun _ _ => id), (fun _ _ _ _ => rfl), fun _ _ => id⟩

private theorem CapStep.step {s t : ForkedBeaconState preset}
    (step : Step config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) :
    CapStepR config s.state t.state ∧ (∀ c, PartialsAt c s.state → PartialsAt c t.state) := by
  cases step with
  | block engine signed due ok =>
    have block := CapStepR.block compounding (applySignedBlock_ok ok).2.1
    exact ⟨block.1, block.2.1 early⟩
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨first, partials, _⟩ := CapStepR.slot slotOk
    obtain ⟨last, assigned, _⟩ := CapStep.upgrades activation compounding upgrades
    exact ⟨first.trans last, fun c => assigned early c ∘ partials c⟩

/-- Each step of a run is a cap step, at every fork. -/
private theorem CapStepR.run_all {s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    CapStepR config s.state t.state := by
  induction run with
  | nil => exact CapStepR.refl _
  | snoc pre step ih =>
    refine ih.trans ?_
    cases step with
    | block engine signed due ok =>
      exact (CapStepR.block compounding (applySignedBlock_ok ok).2.1).1
    | slot ok =>
      obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
      exact (CapStepR.slot slotOk).1.trans (CapStep.upgrades activation compounding upgrades).1

/-- A validator's withdrawal cap is at least the maximum effective balance before Electra. -/
theorem minimum_cap
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {h : Fork} (v : Validator) :
    preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  split
  · split
    · exact UInt64.le_trans activation compounding
    · exact activation
  · exact UInt64.le_refl _

private theorem genesis_assigned_queues {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    AssignedPartials g.state ∧ AssignedTargets g.state ∧ AssignedProposers g.state := by
  obtain ⟨_, _, _, before, initialized⟩ := genesis
  refine ⟨?_, ?_, ?_⟩ <;> intro fork
  all_goals exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) fork)).elim

private theorem genesis_reached_queues {g : ForkedBeaconState preset} (reached : Prop)
    (genesis : Genesis (config := config) (checks := checks) g) :
    PartialsAt reached g.state ∧ TargetsAt reached g.state := by
  obtain ⟨_, _, _, before, initialized⟩ := genesis
  refine ⟨?_, ?_⟩ <;> intro fork
  all_goals exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) fork)).elim

private theorem CapStep.run_of {g s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (shared : Run config checks g s)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (base : CapStepR config g.state s.state ∧
      (∀ c, PartialsAt c g.state → PartialsAt c s.state) ∧
      (Invariant g.state → Invariant s.state) ∧
      (Genesis (config := config) (checks := checks) g → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch s.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance s.state))
    (Q : ∀ {a}, Run config checks s a → Prop) (initial : Q .nil)
    (next : ∀ {a b}, (pre : Run config checks s a) → (step : Step config checks a b) →
      b.fork < .glamsterdam → CapStepR config g.state a.state →
      (∀ c, PartialsAt c g.state → PartialsAt c a.state) →
      (Invariant g.state → Invariant a.state) →
      (Genesis (config := config) (checks := checks) g → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch a.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance a.state) →
      Q pre → Q (pre.snoc step))
    (early : t.fork < .glamsterdam) :
    (CapStepR config g.state t.state ∧ (∀ c, PartialsAt c g.state → PartialsAt c t.state) ∧
      (Invariant g.state → Invariant t.state) ∧
      (Genesis (config := config) (checks := checks) g → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch t.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance t.state)) ∧
      Q run := by
  induction run with
  | nil => exact ⟨base, initial⟩
  | snoc pre step ih =>
    obtain ⟨⟨first, assigned, invariant, funded⟩, carried⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
    refine ⟨?_, next pre step early first assigned invariant funded carried⟩
    obtain ⟨last, partials⟩ := CapStep.step step activation compounding early
    refine ⟨first.trans last, fun c => partials c ∘ assigned c, ?_, ?_⟩
    · intro held
      cases step with
      | block _ _ _ ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant
          (invariant held)
      | slot ok => exact (advanceSlotAcross_invariant (invariant held) ok).1
    · intro genesis aligned finite
      have finiteBefore := UInt64.lt_of_le_of_lt last.forward finite
      have held := funded genesis aligned finiteBefore
      have genesisWitness := genesis
      obtain ⟨_, _, _, _, initialized⟩ := genesisWitness
      obtain ⟨initialPartials, initialTargets, _⟩ := genesis_assigned_queues genesis
      have valid := invariant genesis.invariant
      have capped := first.capped genesis.effectiveBalance_capped
      have targets := first.targets (Nat.lt_of_le_of_lt last.forks early) initialTargets
      have assigned := (assigned False initialPartials.at).old
      cases step with
      | block engine signed due ok =>
        exact (CapStepR.block compounding (applySignedBlock_ok ok).2.1).2.2.1 early
          ((shared.append pre).activationExitOrder genesis) valid.exitsOrdered assigned
          finiteBefore capped
          valid.balancesMatch
          (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
            (shared.append pre).chainSteps).2
          (fun altair => ((shared.append pre).syncCommittee_activation_assigned genesis altair).1)
          held
      | slot ok =>
        obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
        obtain ⟨slotStep, _, slotFunded, _⟩ := CapStepR.slot slotOk
        obtain ⟨upStep, _, upFunded, _⟩ := CapStep.upgrades activation compounding upgrades
        exact upFunded early (slotStep.capped capped)
          (slotFunded (Nat.lt_of_le_of_lt upStep.forks early) activation aligned.1
            (minimum_cap activation compounding) valid.balancesMatch targets held)

private theorem CapStepR.run {s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) :
    CapStepR config s.state t.state ∧ (∀ c, PartialsAt c s.state → PartialsAt c t.state) ∧
      (Invariant s.state → Invariant t.state) ∧
      (Genesis (config := config) (checks := checks) s → MaxEffectiveBalancesAligned preset →
        getCurrentEpoch t.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance t.state) :=
  (CapStep.run_of run .nil activation compounding
    ⟨CapStepR.refl _, fun _ => id, id,
      fun genesis _ _ => genesis_unassigned_eligible_balance genesis⟩
    (fun _ => True) trivial
    (fun _ _ _ _ _ _ _ _ => trivial) early).1

private theorem genesis_scheduled_reserve {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ScheduledFree g.state := by
  obtain ⟨hash, time, deposits, _, initialized⟩ := genesis
  intro i v found future assigned
  have classified := initializeBeaconStateFromEth1_activation_epochs initialized v
    (Array.mem_of_getElem? found)
  rcases classified with unassigned | first
  · exact False.elim (assigned unassigned)
  · simp only [first, GENESIS_EPOCH, UInt64.toNat_zero] at future
    omega

private theorem run_scheduled_walk {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : x.fork < .glamsterdam) (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    UnassignedEligibleBalance x.state ∧ ScheduledFree x.state := by
  let Q := fun {a} (_ : Run config checks g a) =>
    getCurrentEpoch a.state < FAR_FUTURE_EPOCH → ScheduledFree a.state
  have whole := CapStep.run_of run .nil activation compounding
    ⟨CapStepR.refl _, fun _ => id, id, fun h _ _ => genesis_unassigned_eligible_balance h⟩
    Q (fun _ => genesis_scheduled_reserve genesis)
    (fun {a b} pre step before first assigned invariant funded held => by
      intro finiteB
      have last := (CapStep.step step activation compounding before).1
      have finiteA := UInt64.lt_of_le_of_lt last.forward finiteB
      have valid := invariant genesis.invariant
      have capped := first.capped genesis.effectiveBalance_capped
      obtain ⟨partials, targets⟩ := genesis_reached_queues True genesis
      cases step with
      | block engine signed due ok =>
        exact (CapStepR.block compounding (applySignedBlock_ok ok).2.1).2.2.2.2
          before (pre.activationExitOrder genesis) valid.exitsOrdered (assigned True partials)
          capped valid.balancesMatch
          (by obtain ⟨_, _, _, _, initialized⟩ := genesis
              exact (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
                pre.chainSteps).2)
          (fun altair => (pre.syncCommittee_activation_bounded genesis altair).1)
          (held finiteA)
      | slot ok =>
        obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
        have slot := CapStepR.slot slotOk
        have upgrade := CapStep.upgrades activation compounding upgrades
        exact upgrade.2.2.2.2 before (fun _ => slot.1.capped capped)
          (slot.2.2.2 (Nat.lt_of_le_of_lt last.forks before) valid finiteA activation aligned
            (minimum_cap activation compounding)
            (first.targetsAt (Nat.lt_of_le_of_lt last.forks before) True targets)
            (funded genesis aligned finiteA) (held finiteA))) early
  exact ⟨whole.1.2.2.2 genesis aligned finite, whole.2 finite⟩

theorem run_scheduled_reserve {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : x.fork < .glamsterdam) (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    ScheduledEligibleBalance x.state :=
  fun _ => (run_scheduled_walk run genesis activation compounding aligned early finite).2

/-- A key without an activation epoch keeps its effective balance funded.

From Electra, the eligible keys that are not yet active also keep their activation reserve. -/
theorem run_eligible_balance {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .glamsterdam)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    UnassignedEligibleBalance x.state ∧ ScheduledEligibleBalanceElectra x.state := by
  obtain ⟨unassigned, scheduled⟩ :=
    run_scheduled_walk run genesis activation compounding aligned early finite
  refine ⟨unassigned, fun _ i v found guard future => ?_⟩
  by_cases far : v.activationEpoch = FAR_FUTURE_EPOCH
  · obtain ⟨⟨b, read, low⟩, minimum, unslashed⟩ := unassigned i v found far
    exact ⟨fun _ => ⟨b, read, low⟩, minimum (guard.resolve_left (not_not.mpr far)), unslashed⟩
  · obtain ⟨minimum, funding, unslashed⟩ :=
      scheduled i v found (UInt64.lt_iff_toNat_lt.mp future) far
    exact ⟨funding, minimum, unslashed⟩

theorem run_unassigned_eligible_balance {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .glamsterdam)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    UnassignedEligibleBalance x.state :=
  (run_eligible_balance run genesis activation compounding aligned early finite).1

private theorem preKeyCharge_assigned {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (lifecycle : RegistryLifecycle s t)
    (candidate : Nat → Bool) {i : Nat} {v : Validator}
    (found : s.validators.data[i]? = some v)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    preKeyCharge candidate t i = preKeyCharge candidate s i := by
  obtain ⟨w, read, kept⟩ := lifecycle.validators i v found
  have later : w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [kept.activationEpoch assigned]
    exact assigned
  simp only [preKeyCharge, found, read, Option.map_some, assigned, later,
    ↓reduceIte, Option.getD_some]

private theorem preKeyCharge_pending {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (candidate : Nat → Bool)
    (ok : processPendingDeposits config checks s electra = .ok t)
    (matched : BalancesMatch s) (activation : ActivationExitOrder s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (budget : Nat)
    (funded : (∑ i ∈ Finset.range t.validators.data.size,
      if (s.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false then 0
      else ((t.balances.data[i]?.map UInt64.toNat).getD 0) -
        ((s.balances.data[i]?.map UInt64.toNat).getD 0)) +
      (t.depositBalanceToConsume electra).toNat ≤ budget) :
    (∑ i ∈ Finset.range t.validators.data.size, preKeyCharge candidate t i) +
      (t.depositBalanceToConsume electra).toNat ≤
        (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) + budget := by
  have growth := (CapStep.pending (config := config) ok).2.2.2.1 matched candidate
  have each (i : Nat) : preKeyCharge candidate t i ≤ preKeyCharge candidate s i +
      if (s.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false then 0
      else ((t.balances.data[i]?.map UInt64.toNat).getD 0) -
        ((s.balances.data[i]?.map UInt64.toNat).getD 0) := by
    split
    · rename_i withdrawn
      cases found : s.validators.data[i]? with
      | none => simp [found] at withdrawn
      | some v =>
        have member := Array.mem_of_getElem? found
        have first := UInt64.le_iff_toNat_le.mp (activation v member)
        have second := UInt64.le_iff_toNat_le.mp (exits v member)
        have last := UInt64.lt_iff_toNat_lt.mp finite
        have assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
          simp only [found, Option.map_some, Option.getD_some, decide_eq_true_eq] at withdrawn
          intro far
          rw [far] at first
          omega
        rw [preKeyCharge_assigned (registryLifecycle_processPendingDeposits ok)
          candidate found assigned]
        omega
    · exact growth i
  have sums := Finset.sum_le_sum (s := Finset.range t.validators.data.size)
    (fun i _ => each i)
  rw [Finset.sum_add_distrib] at sums
  rw [preKeyCharge_sum_range candidate s (registryLifecycle_processPendingDeposits ok).size_le]
    at sums
  omega

private theorem preKeyCharge_epoch {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (aligned : MaxEffectiveBalancesAligned preset)
    (caps : ∀ {h : Fork} (v : Validator),
      preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v)
    (valid : Invariant s) (ordered : ActivationExitOrder s) (targets : AssignedTargets s)
    (held : UnassignedEligibleBalance s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (candidate : Nat → Bool)
    (pendingLaw : ∀ (a b : BeaconState preset f),
      processPendingDeposits config checks a electra = .ok b → BalancesMatch a →
      (∑ i ∈ Finset.range b.validators.data.size,
        if (a.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch a).toNat))).getD false then 0
        else ((b.balances.data[i]?.map UInt64.toNat).getD 0) -
          ((a.balances.data[i]?.map UInt64.toNat).getD 0)) +
        (b.depositBalanceToConsume electra).toNat ≤
          (a.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (ok : processEpoch config checks s = .ok t) :
    (∑ i ∈ Finset.range t.validators.data.size, preKeyCharge candidate t i) +
      (t.depositBalanceToConsume electra).toNat ≤
        (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) +
          (s.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  let cap := config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  let pendingStage : EpochStage → Bool := fun k =>
    match k with | .pendingDeposits => true | _ => false
  let total (a : BeaconState preset f) :=
    (∑ i ∈ Finset.range a.validators.data.size, preKeyCharge candidate a i) +
      (a.depositBalanceToConsume electra).toNat
  let Q (rest : List EpochStage) (a : BeaconState preset f) :=
    (EpochStage.justification ∈ rest → rest = EpochStage.epochStages ∧ a = s) ∧
      a.slot = s.slot ∧
      ActivationExitOrder a ∧ ExitsOrdered a ∧
      a.finalizedCheckpoint.epoch ≤ getCurrentEpoch s ∧
      total a + cap * rest.countP pendingStage ≤ total s + cap
  have finalized : s.finalizedCheckpoint.epoch ≤ getCurrentEpoch s :=
    UInt64.le_trans valid.ordered.1 (UInt64.le_trans valid.ordered.2
      (UInt64.le_trans valid.settled (getPreviousEpoch_le s)))
  have start : Q EpochStage.epochStages s := by
    refine ⟨fun _ => ⟨rfl, rfl⟩, rfl, ordered, valid.exitsOrdered, finalized, ?_⟩
    simp [EpochStage.epochStages, EpochStage.prefixStages, EpochStage.middleStages,
      EpochStage.tailStages, pendingStage]
  have whole := CapStep.epoch_of Q start (fun k rest a b edge previous matched funded state => by
    obtain ⟨first, slot, activationOrder, exits, checkpoint, budget⟩ := state
    have finiteA : getCurrentEpoch a < FAR_FUTURE_EPOCH := by
      simpa only [getCurrentEpoch, slot] using finite
    have scheduleStep := epoch_schedule_step edge first
    refine ⟨scheduleStep.1, edge.slot_eq.trans slot, edge.activationExitOrder activationOrder,
      ?_, scheduleStep.2 valid checkpoint, ?_⟩
    · by_cases justification : k = .justification
      · subst k
        obtain ⟨validators, _, _⟩ := edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        simpa only [ExitsOrdered, validators] using exits
      · exact (EpochStage.Edge.frame edge justification).exitsOrdered exits
    · by_cases pending : k = .pendingDeposits
      · subst k
        have processed : processPendingDeposits config checks a electra = .ok b := by
          simpa only [EpochStage.Edge, electra, ↓reduceDIte] using edge
        have paid := preKeyCharge_pending candidate processed (matched valid.balancesMatch)
          activationOrder exits finiteA _ (pendingLaw a b processed (matched valid.balancesMatch))
        have count : (EpochStage.pendingDeposits :: rest).countP pendingStage =
            rest.countP pendingStage + 1 := by
          simp only [List.countP_cons, pendingStage, ↓reduceIte]
        rw [count] at budget
        rw [Nat.mul_add, Nat.mul_one] at budget
        change total b + cap * rest.countP pendingStage ≤ total s + cap
        have paid' : total b ≤ total a + cap := by
          simpa only [total, cap, Nat.add_assoc] using paid
        omega
      · have keywise := preKeyCharge_epochEdge edge pending electra early activation
          (funded early activation aligned.1 caps valid.balancesMatch targets held)
          (previous.targets early targets) (UInt64.lt_of_le_of_lt checkpoint finite)
          candidate
        have summed := Finset.sum_le_sum (s := Finset.range b.validators.data.size)
          (fun i _ => keywise i)
        rw [preKeyCharge_sum_range candidate a edge.registryLifecycle.size_le] at summed
        have carry := edge.depositCarry pending
        have absent : pendingStage k = false := by cases k <;> simp_all [pendingStage]
        simp only [List.countP_cons, absent, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero] at budget
        change total b + cap * rest.countP pendingStage ≤ total s + cap
        dsimp only [total] at budget ⊢
        rw [carry]
        omega) ok
  simpa only [total, cap, List.countP_nil, Nat.mul_zero, Nat.add_zero]
    using whole.2.2.2.2.2.2.2.2

private theorem preKeyCharge_slot {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (candidate : Nat → Bool)
    (epochBound : ∀ (a b : BeaconState preset f),
      processSlot s = .ok a →
      getCurrentEpoch s < FAR_FUTURE_EPOCH →
      a.validators = s.validators → a.balances = s.balances →
      a.slot = s.slot → a.depositBalanceToConsume = s.depositBalanceToConsume →
      processEpoch config checks a = .ok b →
      (∑ i ∈ Finset.range b.validators.data.size, preKeyCharge candidate b i) +
        (b.depositBalanceToConsume electra).toNat ≤
          (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) +
            (s.depositBalanceToConsume electra).toNat +
              config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (ok : advanceSlot config checks s = .ok t) :
    (∑ i ∈ Finset.range t.validators.data.size, preKeyCharge candidate t i) +
      (t.depositBalanceToConsume electra).toNat ≤
        (∑ i ∈ Finset.range s.validators.data.size, preKeyCharge candidate s i) +
          (s.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
              ((getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat) := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have slot := (frame_processSlot cachedOk).slot
  have fields : cached.validators = s.validators ∧ cached.balances = s.balances ∧
      cached.depositBalanceToConsume = s.depositBalanceToConsume := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl, rfl⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epoch := nextSlot_epoch_of_boundary sum boundary
    have finite : getCurrentEpoch s < FAR_FUTURE_EPOCH := by
      have limit := next.toNat_lt
      have lower := getCurrentEpoch_toNat_le_slot s
      apply UInt64.lt_iff_toNat_lt.mpr
      change (getCurrentEpoch s).toNat < 18446744073709551615
      omega
    have paid := epochBound cached epoched cachedOk finite fields.1 fields.2.1 slot fields.2.2
      epochedOk
    have difference : next.toNat / preset.SLOTS_PER_EPOCH.toNat -
        s.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = 1 := by omega
    simpa only [preKeyCharge, getCurrentEpoch_toNat, difference, Nat.mul_one] using paid
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have epoch := nextSlot_epoch_of_inside sum inside
    have difference : next.toNat / preset.SLOTS_PER_EPOCH.toNat -
        s.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = 0 := by omega
    simp only [preKeyCharge, getCurrentEpoch_toNat, difference, Nat.mul_zero,
      Nat.add_zero, fields.1, fields.2.1, fields.2.2, Nat.le_refl]

private theorem preKeyCharge_upgrades {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (candidate : Nat → Bool)
    (charge : ∀ i, preKeyCharge candidate t.state i = preKeyCharge candidate s.state i)
    (ok : processUpgrades config checks s = .ok t) :
    (∑ i ∈ Finset.range t.state.validators.data.size, preKeyCharge candidate t.state i) +
      (t.state.depositBalanceToConsume (Nat.le_trans electra
        (processUpgrades_fork_le ok))).toNat =
        (∑ i ∈ Finset.range s.state.validators.data.size, preKeyCharge candidate s.state i) +
          (s.state.depositBalanceToConsume electra).toNat := by
  have total :
      (∑ i ∈ Finset.range t.state.validators.data.size, preKeyCharge candidate t.state i) =
        ∑ i ∈ Finset.range s.state.validators.data.size, preKeyCharge candidate s.state i := by
    rw [← preKeyCharge_sum_range candidate t.state
      (Nat.le_max_right s.state.validators.data.size t.state.validators.data.size),
      ← preKeyCharge_sum_range candidate s.state (Nat.le_max_left _ _)]
    exact Finset.sum_congr rfl (fun i _ => charge i)
  have carry := depositCarry_processUpgrades ok early
  have later : .pectra ≤ t.fork := Nat.le_trans electra (processUpgrades_fork_le ok)
  simp only [electra, later, ↓reduceDIte] at carry
  rw [total, carry]

private theorem preKeyCharge_step {s t : ForkedBeaconState preset}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (candidate : Nat → Bool)
    (blocks : ∀ (engine : ExecutionEngine preset s.fork)
      (block : BeaconBlock preset s.fork) (b : BeaconState preset s.fork),
      processBlock config checks engine s.state block = .ok b →
      (∑ i ∈ Finset.range b.validators.data.size, preKeyCharge candidate b i) +
        (b.depositBalanceToConsume electra).toNat ≤
          (∑ i ∈ Finset.range s.state.validators.data.size,
            preKeyCharge candidate s.state i) + (s.state.depositBalanceToConsume electra).toNat)
    (epochs : ∀ (a b : BeaconState preset s.fork),
      processSlot s.state = .ok a →
      getCurrentEpoch s.state < FAR_FUTURE_EPOCH →
      a.validators = s.state.validators → a.balances = s.state.balances →
      a.slot = s.state.slot → a.depositBalanceToConsume = s.state.depositBalanceToConsume →
      processEpoch config checks a = .ok b →
      (∑ i ∈ Finset.range b.validators.data.size, preKeyCharge candidate b i) +
        (b.depositBalanceToConsume electra).toNat ≤
          (∑ i ∈ Finset.range s.state.validators.data.size,
            preKeyCharge candidate s.state i) +
            (s.state.depositBalanceToConsume electra).toNat +
              config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (step : Step config checks s t) :
    (∑ i ∈ Finset.range t.state.validators.data.size, preKeyCharge candidate t.state i) +
      (if h : .pectra ≤ t.fork then (t.state.depositBalanceToConsume h).toNat else 0) ≤
        (∑ i ∈ Finset.range s.state.validators.data.size, preKeyCharge candidate s.state i) +
          (s.state.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
              ((getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat) := by
  cases step with
  | block engine signed due ok =>
    have bound := blocks engine signed.message _ (applySignedBlock_ok ok).2.1
    have slot := (frame_processBlock (applySignedBlock_ok ok).2.1).slot
    simpa only [electra, ↓reduceDIte, getCurrentEpoch, slot, Nat.sub_self, Nat.mul_zero,
      Nat.add_zero] using bound
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have bound := preKeyCharge_slot electra candidate epochs slotOk
    have up := CapStep.upgrades activation compounding upgrades
    have unchanged := preKeyCharge_upgrades (s := ⟨s.fork, advanced⟩) electra early candidate
      (up.2.2.2.1 electra early candidate) upgrades
    have slot := processUpgrades_slot upgrades
    have later : Fork.pectra ≤ t.fork :=
      Nat.le_trans electra (processUpgrades_fork_le (forked := ⟨s.fork, advanced⟩) upgrades)
    simp only [later, ↓reduceDIte]
    rw [unchanged]
    simpa only [getCurrentEpoch, slot] using bound

theorem preKeyCharge_run {g x u : ForkedBeaconState preset}
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (head : Run config checks x u)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : u.fork < .glamsterdam)
    (candidate : Nat → Bool)
    (pendingLaw : ∀ {f : Fork} (a b : BeaconState preset f) (e : .pectra ≤ f),
      f < .glamsterdam → processPendingDeposits config checks a e = .ok b → BalancesMatch a →
      (∑ i ∈ Finset.range b.validators.data.size,
        if (a.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch a).toNat))).getD false then 0
        else ((b.balances.data[i]?.map UInt64.toNat).getD 0) -
          ((a.balances.data[i]?.map UInt64.toNat).getD 0)) +
        (b.depositBalanceToConsume e).toNat ≤ (a.depositBalanceToConsume e).toNat +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (blockLaw : ∀ {f : Fork} (a b : BeaconState preset f)
      (engine : ExecutionEngine preset f) (block : BeaconBlock preset f),
      f < .glamsterdam → processBlock config checks engine a block = .ok b →
      b.depositBalanceToConsume = a.depositBalanceToConsume) :
    (∑ i ∈ Finset.range u.state.validators.data.size, preKeyCharge candidate u.state i) +
      (if h : .pectra ≤ u.fork then (u.state.depositBalanceToConsume h).toNat else 0) ≤
        (∑ i ∈ Finset.range x.state.validators.data.size, preKeyCharge candidate x.state i) +
          (x.state.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
              ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) := by
  let total (a : ForkedBeaconState preset) :=
    (∑ i ∈ Finset.range a.state.validators.data.size, preKeyCharge candidate a.state i) +
      (if h : .pectra ≤ a.fork then (a.state.depositBalanceToConsume h).toNat else 0)
  let cap := config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  let Q := fun {a : ForkedBeaconState preset} (_ : Run config checks x a) =>
    .pectra ≤ a.fork ∧ getCurrentEpoch x.state ≤ getCurrentEpoch a.state ∧
      total a ≤ total x + cap *
        ((getCurrentEpoch a.state).toNat - (getCurrentEpoch x.state).toNat)
  have before := Nat.lt_of_le_of_lt (fork_le_of_chainSteps head.chainSteps) early
  have result := CapStep.run_of head shared activation compounding
    (CapStepR.run shared activation compounding before) Q
    ⟨electra, UInt64.le_refl _, by simp [total]⟩
    (fun {a b} pre step early first partials invariant funded previous => by
      have last := (CapStep.step step activation compounding early).1
      refine ⟨Nat.le_trans previous.1 last.forks,
        UInt64.le_trans previous.2.1 last.forward, ?_⟩
      obtain ⟨_, initialTargets, initialProposers⟩ := genesis_assigned_queues genesis
      have valid := invariant genesis.invariant
      obtain ⟨_, _, _, phase0, initialized⟩ := genesis
      have earlyA := Nat.lt_of_le_of_lt last.forks early
      have reachable := shared.append pre
      have ordered := reachable.activationExitOrder ⟨_, _, _, phase0, initialized⟩
      have capped := first.capped
        (Genesis.effectiveBalance_capped ⟨_, _, _, phase0, initialized⟩)
      have targets := first.targets earlyA initialTargets
      have paid := preKeyCharge_step activation compounding previous.1 early candidate
        (fun engine block after ok => by
          have charge := (CapStepR.block compounding ok).2.2.2.1 previous.1 earlyA
            (first.proposers earlyA initialProposers) valid.balancesMatch
            (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
              reachable.chainSteps).2
            (fun altair => (reachable.syncCommittee_activation_assigned
              ⟨_, _, _, phase0, initialized⟩ altair).1) candidate
          have summed := Finset.sum_le_sum (s := Finset.range after.validators.data.size)
            (fun i _ => charge i)
          rw [preKeyCharge_sum_range candidate a.state
            (frame_processBlock ok).registryGrows] at summed
          rw [blockLaw _ _ engine block earlyA ok]
          omega)
        (fun cached after cacheOk finiteA validators balances slot carry ok => by
          have held := funded ⟨_, _, _, phase0, initialized⟩ aligned finiteA
          have cacheValid := (frame_processSlot cacheOk).invariant valid
          have cacheTargets : AssignedTargets cached := by
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cacheOk
            exact targets
          have epoch := preKeyCharge_epoch previous.1 earlyA activation aligned
            (minimum_cap activation compounding) cacheValid
            (by simpa only [ActivationExitOrder, validators] using ordered) cacheTargets
            (held.transfer (congrArg (·.data) validators) (fun i v amount found pending read low =>
              ⟨amount, by rw [balances]; exact read, low⟩))
            (by simpa only [getCurrentEpoch, slot] using finiteA) candidate
            (fun c d ok matched => pendingLaw c d previous.1 earlyA ok matched) ok
          simpa only [preKeyCharge, validators, balances, carry] using epoch) step
      have prior := previous.2.2
      have low := UInt64.le_iff_toNat_le.mp previous.2.1
      have high := UInt64.le_iff_toNat_le.mp last.forward
      have difference : (getCurrentEpoch b.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch a.state).toNat - (getCurrentEpoch x.state).toNat) +
            ((getCurrentEpoch b.state).toNat - (getCurrentEpoch a.state).toNat) := by omega
      dsimp only [total, cap] at prior ⊢
      simp only [previous.1, ↓reduceDIte] at paid prior
      rw [difference, Nat.mul_add]
      omega) early
  simpa only [Q, total, cap, electra, ↓reduceDIte] using result.2.2.2

/-- Every stage of an epoch trace is a cap step. -/
private theorem CapStepR.epochTrace {f : Fork} {s t : BeaconState preset f}
    {stages : List EpochStage}
    (trace : EpochTrace (EpochStage.action config checks) stages s t) : CapStepR config s t := by
  apply trace.transport (CapStepR config) CapStepR.refl (fun one two => one.trans two)
  intro k member a b computed
  have edge := EpochStage.action_cases.mp computed
  exact (CapStep.epochEdge edge).1

theorem CapStep.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
      (ScheduledEligibleBalance s → ScheduledEligibleBalance t) := by
  obtain ⟨step, funded, partials, charge, scheduled⟩ := CapStepR.exit ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge,
    fun held early => scheduled (held early)⟩

theorem CapStep.processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    CapStep config s t ∧
      (BalancesMatch s → UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (.pectra ≤ f → BalancesMatch s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (BalancesMatch s → ScheduledEligibleBalance s → ScheduledEligibleBalance t) := by
  obtain ⟨step, funded, partials, charge, scheduled⟩ := CapStepR.processDeposit ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge,
    fun matched held early => scheduled matched (held early)⟩

theorem CapStep.registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) :
    CapStep config s t ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (.pectra ≤ f → preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        UnassignedEligibleBalance s → s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
        ∀ (candidate : Nat → Bool) j, preKeyCharge candidate t j ≤ preKeyCharge candidate s j) ∧
      (preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        s.finalizedCheckpoint.epoch < FAR_FUTURE_EPOCH →
        UnassignedEligibleBalance s → ScheduledEligibleBalance s → ScheduledEligibleBalance t) := by
  obtain ⟨step, funded, partials, charge, scheduled⟩ := CapStepR.registry ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge,
    fun activation finite funded held early => scheduled activation finite funded (held early)⟩

theorem CapStep.blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledEligibleBalance s → ScheduledEligibleBalance t) := by
  obtain ⟨step, funded, partials, charge, scheduled⟩ := CapStepR.blsChange ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge,
    fun held early => scheduled (held early)⟩

theorem CapStep.consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  obtain ⟨step, funded, partials, charge, _⟩ := CapStepR.consolidationRequest order ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge⟩

theorem CapStep.withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (∀ candidate i, preKeyCharge candidate t i ≤ preKeyCharge candidate s i) := by
  obtain ⟨step, funded, partials, charge, _⟩ := CapStepR.withdrawalRequest ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge⟩

theorem CapStep.proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam → AssignedProposers s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledEligibleBalance s → ScheduledEligibleBalance t) := by
  obtain ⟨step, funded, partials, charge, scheduled⟩ := CapStepR.proposerSlashing ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge,
    fun held early => scheduled (held early)⟩

theorem CapStep.attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    CapStep config s t ∧ (UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam → AssignedProposers s → ∀ candidate i,
        preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (ScheduledEligibleBalance s → ScheduledEligibleBalance t) := by
  obtain ⟨step, funded, partials, charge, scheduled⟩ := CapStepR.attesterSlashing ok
  exact ⟨step.toCapStep, funded, fun held => (partials False held.at).old, charge,
    fun held early => scheduled (held early)⟩

theorem CapStep.block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) :
    CapStep config s t ∧
      (f < .glamsterdam → AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam → ActivationExitOrder s → ExitsOrdered s → AssignedPartials s →
        getCurrentEpoch s < FAR_FUTURE_EPOCH → EffectiveBalancesCapped s →
        BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH) →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (.pectra ≤ f → f < .glamsterdam → AssignedProposers s →
        BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH) →
        ∀ candidate i,
          preKeyCharge candidate t i ≤ preKeyCharge candidate s i) ∧
      (f < .glamsterdam → ActivationExitOrder s → ExitsOrdered s →
        EffectiveBalancesCapped s → BalancesMatch s → PubkeysDistinct s →
        (∀ altair : .altair ≤ f,
          ∀ key ∈ (s.currentSyncCommittee altair).value.pubkeys.toList,
            ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
              v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
              v.activationEpoch.toNat ≤ (getCurrentEpoch s).toNat + 1) →
        ScheduledEligibleBalance s → ScheduledEligibleBalance t) := by
  obtain ⟨step, partials, funded, charge, scheduled⟩ := CapStepR.block order ok
  exact ⟨step.toCapStep, fun early held => (partials early False held.at).old, funded, charge,
    fun early activation exits capped matched unique bounded held earlyPectra =>
      scheduled early activation exits
        (fun electra => (Nat.not_le_of_lt earlyPectra electra).elim) capped matched unique
        bounded (held earlyPectra)⟩

theorem CapStep.epoch {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) :
    CapStep config s t ∧ (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (Invariant s → getCurrentEpoch s < FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        MaxEffectiveBalancesAligned preset →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        AssignedTargets s → UnassignedEligibleBalance s → ScheduledEligibleBalance s →
          ScheduledEligibleBalance t ((getCurrentEpoch s).toNat + 1)) := by
  obtain ⟨step, partials, funded, scheduled⟩ := CapStepR.epoch ok
  exact ⟨step.toCapStep, fun held => (partials False held.at).old, funded,
    fun valid finite activation aligned caps _ unassigned held early =>
      scheduled (Nat.lt_trans early (by decide)) valid finite activation aligned caps
        (fun electra => (Nat.not_le_of_lt early electra).elim) unassigned (held early)⟩

theorem CapStep.slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) :
    CapStep config s t ∧ (AssignedPartials s → AssignedPartials t) ∧
      (f < .glamsterdam →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        BalancesMatch s → AssignedTargets s →
        UnassignedEligibleBalance s → UnassignedEligibleBalance t) ∧
      (Invariant s → getCurrentEpoch s < FAR_FUTURE_EPOCH →
        preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE →
        MaxEffectiveBalancesAligned preset →
        (∀ {h : Fork} (v : Validator),
          preset.MAX_EFFECTIVE_BALANCE ≤ withdrawalMaxEffectiveBalance preset h v) →
        AssignedTargets s → UnassignedEligibleBalance s → ScheduledEligibleBalance s →
          ScheduledEligibleBalance t) := by
  obtain ⟨step, partials, funded, scheduled⟩ := CapStepR.slot ok
  exact ⟨step.toCapStep, fun held => (partials False held.at).old, funded,
    fun valid finite activation aligned caps _ unassigned held early =>
      scheduled (Nat.lt_trans early (by decide)) valid finite activation aligned caps
        (fun electra => (Nat.not_le_of_lt early electra).elim) unassigned (held early)⟩

theorem CapStep.upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) :
    CapStep config s.state t.val.state ∧
      (t.val.fork < .glamsterdam → AssignedPartials s.state → AssignedPartials t.val.state) ∧
      (t.val.fork < .glamsterdam →
        (∀ v ∈ s.state.validators.data,
          v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset s.fork v) →
        UnassignedEligibleBalance s.state → UnassignedEligibleBalance t.val.state) ∧
      (ScheduledEligibleBalance s.state → ScheduledEligibleBalance t.val.state) := by
  obtain ⟨step, partials, funded, scheduled⟩ := CapStepR.upgrade activation compounding ok
  exact ⟨step.toCapStep, fun early held => (partials early False held.at).old, funded,
    fun held early =>
      scheduled (Nat.lt_trans early (by decide))
        (fun reached => (Nat.not_le_of_lt early reached).elim)
        (held (Nat.lt_trans t.property early))⟩

/-- Along a run, each step is a cap step, and the invariant of the transition is kept.

Proved only before Gloas: the queued partial withdrawals stay assigned.

Proved only before Gloas: an unassigned validator keeps its eligible balance.

That needs a run from genesis, aligned caps and a finite epoch. -/
theorem CapStep.run {s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    CapStep config s.state t.state ∧
      (t.fork < .glamsterdam → AssignedPartials s.state → AssignedPartials t.state) ∧
      (Invariant s.state → Invariant t.state) ∧
      (t.fork < .glamsterdam → Genesis (config := config) (checks := checks) s →
        MaxEffectiveBalancesAligned preset →
        getCurrentEpoch t.state < FAR_FUTURE_EPOCH → UnassignedEligibleBalance t.state) :=
  ⟨(CapStepR.run_all run activation compounding).toCapStep,
    fun early held => ((CapStepR.run run activation compounding early).2.1 False held.at).old,
    fun held => Run.invariant held run,
    fun early => (CapStepR.run run activation compounding early).2.2.2⟩

/-- Every stage of an epoch trace is a cap step. -/
theorem CapStep.epochTrace {f : Fork} {s t : BeaconState preset f}
    {stages : List EpochStage}
    (trace : EpochTrace (EpochStage.action config checks) stages s t) : CapStep config s t :=
  (CapStepR.epochTrace trace).toCapStep


end Internal

end EthLib.Consensus
