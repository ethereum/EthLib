module

public import EthLib.Consensus.Proofs.Transition.Totality.EpochExits
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock
public import EthLib.Consensus.Transition.StateTransition
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.ParentPayload
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests

/-!
# Proofs: the exit queue after one block

A block moves the exit and consolidation queues through exits, slashings and two kinds of request.

Each validator that starts to exit moves the end of its queue by at most its cost.

That cost is its effective balance in increments, plus one, and the validator then stops owing it.

So the end of each queue, plus the cost still owed, rises only through two kinds of steps.

A new validator owes its cost from the moment it joins.

A partial withdrawal moves the exit queue with no exit.

It moves it by at most its amount, capped by the balance of the validator, in increments, plus one.

Before Electra an exit moves the latest exit epoch by at most one, which is within its cost.

From Electra, the churn carried for exits stays within one churn bound or its value before.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}

/-- The withdrawal requests that a block body carries, from Electra.

Before Gloas they come with the payload of the block, and from Gloas with that of its parent. -/
def blockWithdrawalRequests (body : BeaconBlockBody preset fork) : List WithdrawalRequest :=
  if gloas : .glamsterdam ≤ fork then (body.parentExecutionRequests gloas).withdrawals.data.toList
  else if electra : .pectra ≤ fork then
    (body.executionRequests ⟨electra, Nat.lt_of_not_le gloas⟩).withdrawals.data.toList
  else []

/-- A bound on the epochs by which the withdrawal requests of a block move the exit queue.

A partial withdrawal takes at most its requested amount and at most the balance of its validator.

Each withdrawal request counts the smaller of its amount and a cap, in increments, plus one.

The cap stands for a bound on the balance of the validator. -/
def partialExitCost (preset : Preset) (cap : Nat) (body : BeaconBlockBody preset fork) : Nat :=
  ((blockWithdrawalRequests body).map fun request =>
    min request.amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum

/-- The cost in the exit queue of the validators from a position on, whether they exit or not.

Each one counts its effective balance in increments, plus one. -/
def exitCostFrom (preset : Preset) (state : BeaconState preset fork) (count : Nat) : Nat :=
  ((state.validators.data.toList.drop count).map fun validator =>
    validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum

/-! ## The costs, read through the exit epochs and the effective balances -/

section Costs

/-- The exit epoch and the effective balance of each validator, in registry order. -/
private def keys (s : BeaconState preset fork) : List (Epoch × Gwei) :=
  s.validators.data.toList.map fun v => (v.exitEpoch, v.effectiveBalance)

/-- The cost of a validator: its effective balance in increments, plus one. -/
private def costK (preset : Preset) (k : Epoch × Gwei) : Nat :=
  k.2.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1

/-- The cost a validator still owes: its cost if it has not started to exit, and zero otherwise. -/
private def owedK (preset : Preset) (k : Epoch × Gwei) : Nat :=
  if k.1 = FAR_FUTURE_EPOCH then costK preset k else 0

private theorem length_keys (s : BeaconState preset fork) :
    (keys s).length = s.validators.data.size := by
  simp [keys]

private theorem exitCost_keys (s : BeaconState preset fork) :
    exitCost preset s = ((keys s).map (owedK preset)).sum := by
  unfold exitCost keys
  generalize s.validators.data.toList = l
  induction l with
  | nil => rfl
  | cons v rest ih =>
    by_cases far : v.exitEpoch = FAR_FUTURE_EPOCH <;>
      simp [far, owedK, costK, ih]

private theorem exitCostFrom_keys (s : BeaconState preset fork) (n : Nat) :
    exitCostFrom preset s n = (((keys s).map (costK preset)).drop n).sum := by
  simp [exitCostFrom, keys, costK, List.map_drop, List.map_map, Function.comp_def]

private theorem effectiveBalanceSum_keys (s : BeaconState preset fork) :
    effectiveBalanceSum s = ((keys s).map (·.2.toNat)).sum := by
  simp [effectiveBalanceSum, keys, List.map_map, Function.comp_def]

private theorem keys_putValidator (s : BeaconState preset fork) {i : Nat}
    (inside : i < s.validators.data.size) (v : Validator) :
    keys (s.putValidator i inside v) = (keys s).set i (v.exitEpoch, v.effectiveBalance) := by
  simp [keys, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    List.map_set]

private theorem keys_getElem? {s : BeaconState preset fork} {i : Nat} {v : Validator}
    (found : s.validators.data[i]? = some v) :
    (keys s)[i]? = some (v.exitEpoch, v.effectiveBalance) := by
  simp [keys, found]

end Costs

/-! ## The bound carried through the block -/

section Bound

variable {start : BeaconState preset fork} {ceiling : Nat}

/-- The parameters that keep each churn at least one increment.

They also keep each exit that succeeds below the far future epoch. -/
private structure Rates (preset : Preset) (config : Config) : Prop where
  increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT
  minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  maximum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
  activation : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat

/-- The bounds that a state keeps along the block, with a bound and a budget spent.

The bound covers the first epoch of a new exit, each exit epoch that is set and both queue ends.

The bound plus the cost still owed is at most the ceiling plus the cost owed at the start.

It adds the cost of the validators that joined, and the budget spent. -/
private structure Holds (config : Config) (start : BeaconState preset fork) (ceiling : Nat)
    (s : BeaconState preset fork) (r u : Nat) : Prop where
  opens : (getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ r
  size : start.validators.data.size ≤ s.validators.data.size
  exits : ∀ k ∈ keys s, k.1 ≠ FAR_FUTURE_EPOCH → k.1.toNat ≤ r
  exitQueue : ∀ electra : .pectra ≤ fork, (s.earliestExitEpoch electra).toNat ≤ r
  consolidationQueue : ∀ electra : .pectra ≤ fork,
    (s.earliestConsolidationEpoch electra).toNat ≤ r
  churn : ∀ electra : .pectra ≤ fork, (s.exitBalanceToConsume electra).toNat ≤
    max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config s)
  potential : r + exitCost preset s ≤
    ceiling + exitCost preset start + exitCostFrom preset s start.validators.data.size + u

private theorem Holds.spend {s : BeaconState preset fork} {r u v : Nat}
    (holds : Holds config start ceiling s r u) (le : u ≤ v) : Holds config start ceiling s r v :=
  { holds with potential := Nat.le_trans holds.potential (by omega) }

/-- A step keeps the bounds, and spends at most a cost of the budget. -/
private def Moves (config : Config) (start : BeaconState preset fork) (ceiling cost : Nat)
    (a b : BeaconState preset fork) : Prop :=
  ∀ r u, Holds config start ceiling a r u → ∃ r', Holds config start ceiling b r' (u + cost)

private theorem Moves.refl (a : BeaconState preset fork) : Moves config start ceiling 0 a a :=
  fun r _ holds => ⟨r, holds⟩

private theorem Moves.trans {c d : Nat} {a b e : BeaconState preset fork}
    (one : Moves config start ceiling c a b) (two : Moves config start ceiling d b e) :
    Moves config start ceiling (c + d) a e := fun r u holds => by
  obtain ⟨r₁, middle⟩ := one r u holds
  obtain ⟨r₂, last⟩ := two r₁ (u + c) middle
  exact ⟨r₂, by rwa [Nat.add_assoc] at last⟩

private theorem Moves.trans₀ {a b e : BeaconState preset fork}
    (one : Moves config start ceiling 0 a b) (two : Moves config start ceiling 0 b e) :
    Moves config start ceiling 0 a e :=
  one.trans two

private theorem Moves.mono {c d : Nat} {a b : BeaconState preset fork} (le : c ≤ d)
    (moves : Moves config start ceiling c a b) : Moves config start ceiling d a b :=
  fun r u holds => by
    obtain ⟨r', after⟩ := moves r u holds
    exact ⟨r', after.spend (by omega)⟩

/-- A fold whose every step keeps the bounds for free keeps them for free. -/
private theorem Moves.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Moves config start ceiling 0 a b) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) :
    Moves config start ceiling 0 a b :=
  (foldlM_ok_steps (Moves config start ceiling 0) Moves.refl Moves.trans₀ each computed).1

/-- A fold whose every step spends a cost of its item spends the sum of those costs. -/
private theorem Moves.foldlM_sum {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    {f : α → Nat} (each : ∀ a x b, step a x = .ok b → Moves config start ceiling (f x) a b) :
    ∀ {items : List α} {a b : BeaconState preset fork}, items.foldlM step a = .ok b →
      Moves config start ceiling ((items.map f).sum) a b
  | [], a, b, computed => by
    cases computed
    exact Moves.refl a
  | x :: rest, a, b, computed => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, folded⟩ := computed
    simpa using (each _ _ _ first).trans (Moves.foldlM_sum each folded)

/-- A step that keeps the slot and the queues, and keeps each validator or appends new ones.

Its new validators have not started to exit. -/
private structure Plain (a b : BeaconState preset fork) : Prop where
  slot : b.slot = a.slot
  appended : ∃ extra, keys b = keys a ++ extra ∧ ∀ k ∈ extra, k.1 = FAR_FUTURE_EPOCH
  exitQueue : b.earliestExitEpoch = a.earliestExitEpoch
  consolidationQueue : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch
  churn : b.exitBalanceToConsume = a.exitBalanceToConsume

private theorem Plain.refl (a : BeaconState preset fork) : Plain a a :=
  ⟨rfl, ⟨[], by simp, by simp⟩, rfl, rfl, rfl⟩

private theorem Plain.trans {a b c : BeaconState preset fork} (one : Plain a b)
    (two : Plain b c) : Plain a c := by
  obtain ⟨extra, keysOne, farOne⟩ := one.appended
  obtain ⟨more, keysTwo, farTwo⟩ := two.appended
  refine ⟨two.slot.trans one.slot, ⟨extra ++ more, by rw [keysTwo, keysOne, List.append_assoc],
    fun k member => ?_⟩, two.exitQueue.trans one.exitQueue,
    two.consolidationQueue.trans one.consolidationQueue, two.churn.trans one.churn⟩
  rcases List.mem_append.mp member with inside | inside
  · exact farOne k inside
  · exact farTwo k inside

/-- A step that keeps the registry, the slot and the queues is plain. -/
private theorem Plain.of_validators {a b : BeaconState preset fork}
    (validators : b.validators = a.validators := by rfl) (slot : b.slot = a.slot := by rfl)
    (exitQueue : b.earliestExitEpoch = a.earliestExitEpoch := by rfl)
    (consolidationQueue : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch := by rfl)
    (churn : b.exitBalanceToConsume = a.exitBalanceToConsume := by rfl) : Plain a b :=
  ⟨slot, ⟨[], by simp [keys, validators], by simp⟩, exitQueue, consolidationQueue, churn⟩

/-- A plain step keeps the bounds for free. -/
private theorem Plain.moves {a b : BeaconState preset fork} (plain : Plain a b) :
    Moves config start ceiling 0 a b := fun r u holds => by
  obtain ⟨extra, keysEq, far⟩ := plain.appended
  have sized := holds.size
  rw [← length_keys a] at sized
  have owed : (extra.map (owedK preset)).sum = (extra.map (costK preset)).sum :=
    congrArg List.sum (List.map_congr_left fun k member => by simp [owedK, far k member])
  have grows : effectiveBalanceSum a ≤ effectiveBalanceSum b := by
    rw [effectiveBalanceSum_keys, effectiveBalanceSum_keys, keysEq, List.map_append,
      List.sum_append]
    omega
  refine ⟨r, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa [getCurrentEpoch, plain.slot] using holds.opens
  · rw [← length_keys b, keysEq, List.length_append]
    omega
  · intro k member set
    rw [keysEq] at member
    rcases List.mem_append.mp member with inside | inside
    · exact holds.exits k inside set
    · exact absurd (far k inside) set
  · intro electra
    rw [plain.exitQueue]
    exact holds.exitQueue electra
  · intro electra
    rw [plain.consolidationQueue]
    exact holds.consolidationQueue electra
  · intro electra
    rw [plain.churn]
    refine Nat.le_trans (holds.churn electra) (max_le_max (Nat.le_refl _) ?_)
    unfold exitChurnCeiling
    omega
  · have potential := holds.potential
    rw [exitCost_keys, exitCostFrom_keys] at potential ⊢
    rw [keysEq, List.map_append, List.map_append, List.sum_append, List.drop_append_of_le_length
      (by simpa using sized), List.sum_append, owed]
    omega

/-- A map that does not see the change at one position keeps its values. -/
private theorem map_set_of_eq {β : Type} {l : List (Epoch × Gwei)} {i : Nat}
    {x y : Epoch × Gwei} {f : Epoch × Gwei → β} (found : l[i]? = some y) (same : f x = f y) :
    (l.set i x).map f = l.map f := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_set]
  split
  · subst_vars
    obtain ⟨inside, rfl⟩ := List.getElem?_eq_some_iff.mp found
    simp [same, inside]
  · rfl

/-- A validator that starts to exit stops owing its cost, and the bound grows by that cost. -/
private theorem Holds.exit {a b : BeaconState preset fork} {r u i : Nat} {e : Epoch} {w : Gwei}
    (holds : Holds config start ceiling a r u) (slot : b.slot = a.slot)
    (found : (keys a)[i]? = some (FAR_FUTURE_EPOCH, w))
    (set : keys b = (keys a).set i (e, w)) (started : e ≠ FAR_FUTURE_EPOCH)
    (epoch : e.toNat ≤ r + costK preset (FAR_FUTURE_EPOCH, w))
    (exitQueue : ∀ electra : .pectra ≤ fork,
      (b.earliestExitEpoch electra).toNat ≤ r + costK preset (FAR_FUTURE_EPOCH, w))
    (consolidationQueue : ∀ electra : .pectra ≤ fork,
      (b.earliestConsolidationEpoch electra).toNat ≤ r + costK preset (FAR_FUTURE_EPOCH, w))
    (churn : ∀ electra : .pectra ≤ fork, (b.exitBalanceToConsume electra).toNat ≤
      max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config a)) :
    Holds config start ceiling b (r + costK preset (FAR_FUTURE_EPOCH, w)) u := by
  have inside : i < (keys a).length := (List.getElem?_eq_some_iff.mp found).1
  have costs : (keys b).map (costK preset) = (keys a).map (costK preset) := by
    rw [set]
    exact map_set_of_eq found rfl
  have sums : effectiveBalanceSum b = effectiveBalanceSum a := by
    rw [effectiveBalanceSum_keys, effectiveBalanceSum_keys, set,
      map_set_of_eq (x := (e, w)) found rfl]
  have owed := sum_set_add (l := (keys a).map (owedK preset)) (i := i) (by simpa using inside) 0
  have owedAt : ((keys a).map (owedK preset))[i]'(by simpa using inside) =
      costK preset (FAR_FUTURE_EPOCH, w) := by
    simp [(List.getElem?_eq_some_iff.mp found).2, owedK]
  have owedSet : (keys b).map (owedK preset) = ((keys a).map (owedK preset)).set i 0 := by
    rw [set, List.map_set]
    simp [owedK, started]
  refine ⟨?_, ?_, ?_, exitQueue, consolidationQueue, ?_, ?_⟩
  · have opens := holds.opens
    simp only [getCurrentEpoch, slot] at opens ⊢
    omega
  · rw [← length_keys b, set, List.length_set, length_keys]
    exact holds.size
  · intro k member finite
    rw [set] at member
    rcases List.mem_or_eq_of_mem_set member with old | rfl
    · have := holds.exits k old finite
      omega
    · exact epoch
  · intro electra
    unfold exitChurnCeiling
    rw [sums]
    exact churn electra
  · have potential := holds.potential
    rw [exitCost_keys, exitCostFrom_keys] at potential ⊢
    rw [costs, owedSet]
    rw [owedAt] at owed
    omega

/-- A step that keeps each validator may move both queues, and spends the move from the budget. -/
private theorem Holds.shift {a b : BeaconState preset fork} {r u c : Nat}
    (holds : Holds config start ceiling a r u) (slot : b.slot = a.slot) (same : keys b = keys a)
    (exitQueue : ∀ electra : .pectra ≤ fork, (b.earliestExitEpoch electra).toNat ≤ r + c)
    (consolidationQueue : ∀ electra : .pectra ≤ fork,
      (b.earliestConsolidationEpoch electra).toNat ≤ r + c)
    (churn : ∀ electra : .pectra ≤ fork, (b.exitBalanceToConsume electra).toNat ≤
      max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config a)) :
    Holds config start ceiling b (r + c) (u + c) := by
  refine ⟨?_, ?_, ?_, exitQueue, consolidationQueue, ?_, ?_⟩
  · have opens := holds.opens
    simp only [getCurrentEpoch, slot] at opens ⊢
    omega
  · rw [← length_keys b, same, length_keys]
    exact holds.size
  · intro k member finite
    rw [same] at member
    have := holds.exits k member finite
    omega
  · intro electra
    unfold exitChurnCeiling
    rw [effectiveBalanceSum_keys, same, ← effectiveBalanceSum_keys]
    exact churn electra
  · have potential := holds.potential
    rw [exitCost_keys, exitCostFrom_keys] at potential ⊢
    rw [same]
    omega

end Bound

/-! ## The churn of the queues -/

section Churn

/-- Epochs of a churn of at least one increment hold an amount plus less than one churn.

Then there are at most the amount in increments, plus one. -/
private theorem epochs_le_div_add_one {epochs churn increment left amount : Nat}
    (positive : 0 < increment) (least : increment ≤ churn)
    (spent : epochs * churn ≤ left + amount) (below : left < churn) :
    epochs ≤ amount / increment + 1 := by
  cases epochs with
  | zero => exact Nat.zero_le _
  | succ epochs =>
    rw [Nat.add_mul, Nat.one_mul] at spent
    have scaled := Nat.mul_le_mul_left epochs least
    have bounded : epochs * increment ≤ amount := by omega
    have := (Nat.le_div_iff_mul_le positive).mpr bounded
    omega

/-- A queue whose churn is at least one increment places an amount within its cost.

The churn left over is at most the larger of the one before and the churn. -/
private theorem churnQueue_bound {earliest first churn left₀ amount epoch left : UInt64}
    {r increment : Nat}
    (computed : churnQueue earliest first churn left₀ amount = .ok (epoch, left))
    (positive : 0 < increment) (least : increment ≤ churn.toNat)
    (earliestLe : earliest.toNat ≤ r) (firstLe : first.toNat ≤ r) :
    epoch.toNat ≤ r + (amount.toNat / increment + 1) ∧
      left.toNat ≤ max left₀.toNat churn.toNat := by
  obtain ⟨placed, spent, last⟩ := churnQueue_spend computed
  have openLe : (max earliest first).toNat ≤ r := by
    rw [Uint64.toNat_max]
    omega
  have availableLe : (if earliest < max earliest first then churn else left₀).toNat ≤
      max left₀.toNat churn.toNat := by
    split <;> omega
  generalize (if earliest < max earliest first then churn else left₀) = available
    at spent availableLe
  have placed := UInt64.le_iff_toNat_le.mp placed
  rcases last with same | below
  · subst same
    rw [Nat.sub_self, Nat.zero_mul] at spent
    have := Nat.zero_le (amount.toNat / increment)
    constructor <;> omega
  · have epochs := epochs_le_div_add_one (epochs := epoch.toNat - (max earliest first).toNat)
      (amount := amount.toNat) positive least (by omega) below
    constructor <;> omega

/-- The total active balance is at most one increment plus the sum of the effective balances. -/
private theorem getTotalActiveBalance_le {s : BeaconState preset fork} {total : Gwei}
    (computed : getTotalActiveBalance s = .ok total) :
    total.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum s := by
  obtain ⟨-, fits, rfl⟩ := getTotalBalance_ok_iff.mp (getTotalActiveBalance_ok computed)
  have marked : sumMarked s.validators.data (markIndices s.validators.data.size
      (getActiveValidatorIndices s (getCurrentEpoch s))) ≤ effectiveBalanceSum s := by
    rw [sumMarked_eq_sum, effectiveBalanceSum_eq_sum_range]
    refine sum_map_le_sum_map fun j _ => ?_
    split <;> omega
  rw [UInt64.max_def]
  split
  · rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
    omega
  · omega

/-- A share of a total, at least the least churn and rounded down to an increment, is bounded.

It is at least one increment, and at most the least churn plus the total. -/
private theorem roundToIncrement_share_bounds (total quotient : Gwei)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
          (total / quotient))).toNat ∧
      (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
          (total / quotient))).toNat ≤
        config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + total.toNat := by
  rw [toNat_roundToIncrement, Uint64.toNat_max, UInt64.toNat_div]
  have positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    UInt64.lt_iff_toNat_lt.mp increment
  have minimum := UInt64.le_iff_toNat_le.mp minimum
  have share := Nat.div_le_self total.toNat quotient.toNat
  have amountLower : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (total.toNat / quotient.toNat) := by
    omega
  have amountUpper : max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total.toNat / quotient.toNat) ≤
        config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + total.toNat := by
    omega
  generalize max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (total.toNat / quotient.toNat) =
    amount at *
  have split := Nat.mod_add_div amount preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  have whole : 1 ≤ amount / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    (Nat.le_div_iff_mul_le positive).mpr (by omega)
  have lower : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := Nat.le_mul_of_pos_right preset.EFFECTIVE_BALANCE_INCREMENT.toNat whole
    omega
  exact ⟨lower, Nat.le_trans (Nat.sub_le _ _) amountUpper⟩

/-- A churn of exits that is computed is at least one increment and at most one churn bound. -/
private theorem exitChurnLimit_bounds (rates : Rates preset config) {s : BeaconState preset fork}
    {churn : Gwei} (computed : exitChurnLimit config s = .ok churn) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ churn.toNat ∧
      churn.toNat ≤ exitChurnCeiling config s := by
  unfold exitChurnLimit at computed
  split at computed
  · simp only [getExitChurnLimit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨total, totalOk, rfl⟩ := computed
    have totalLe := getTotalActiveBalance_le totalOk
    obtain ⟨lower, upper⟩ := roundToIncrement_share_bounds (config := config) total
      config.CHURN_LIMIT_QUOTIENT_GLOAS rates.increment rates.minimum
    unfold exitChurnCeiling
    exact ⟨lower, by omega⟩
  · simp only [getActivationExitChurnLimit, getBalanceChurnLimit, bind_ok_iff, pure,
      Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, ⟨total, totalOk, rfl⟩, rfl⟩ := computed
    have totalLe := getTotalActiveBalance_le totalOk
    obtain ⟨lower, upper⟩ := roundToIncrement_share_bounds (config := config) total
      config.CHURN_LIMIT_QUOTIENT rates.increment rates.minimum
    have maximum := UInt64.le_iff_toNat_le.mp rates.maximum
    rw [Uint64.toNat_min]
    unfold exitChurnCeiling
    constructor <;> omega

variable {start : BeaconState preset fork} {ceiling : Nat}

/-- An exit churn spent within the bounds places its amount within its cost.

The churn left over stays within its bound. -/
private theorem exitChurn_bound (rates : Rates preset config) {a b : BeaconState preset fork}
    {electra : .pectra ≤ fork} {amount : Gwei} {epoch : Epoch} {r u : Nat}
    (holds : Holds config start ceiling a r u)
    (computed : computeExitEpochAndUpdateChurn config a electra amount = .ok (b, epoch)) :
    ∃ left, b = { a with
        exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => epoch } ∧
      epoch.toNat ≤ r + (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ∧
      left.toNat ≤ max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config a) := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨first, firstOk, churn, churnOk, ⟨queued, left⟩, queueOk, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  have firstLe := (computeActivationExitEpoch_ok_iff.mp firstOk).2
  have opens := holds.opens
  obtain ⟨lower, upper⟩ := exitChurnLimit_bounds rates churnOk
  have positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    UInt64.lt_iff_toNat_lt.mp rates.increment
  obtain ⟨epochLe, leftLe⟩ := churnQueue_bound queueOk positive lower (holds.exitQueue electra)
    (by omega)
  have carried := holds.churn electra
  exact ⟨left, rfl, epochLe, by omega⟩

/-- The latest exit epoch that is set stays within a bound that covers its start and each one. -/
private theorem foldl_latest_le {r : Nat} :
    ∀ (l : List Validator) (latest : Epoch), latest.toNat ≤ r →
      (∀ v ∈ l, v.exitEpoch.toNat ≤ r) →
      (l.foldl (fun latest v => max latest v.exitEpoch) latest).toNat ≤ r
  | [], _, le, _ => le
  | v :: rest, latest, le, each => by
    rw [List.foldl_cons]
    refine foldl_latest_le rest _ ?_ fun w member => each w (List.mem_cons_of_mem _ member)
    rw [Uint64.toNat_max]
    exact max_le le (each v List.mem_cons_self)

/-- Before Electra, an exit epoch lands at most one epoch past the bound. -/
private theorem exitQueueEpoch_bound {a : BeaconState preset fork} {epoch : Epoch} {r u : Nat}
    (holds : Holds config start ceiling a r u)
    (computed : exitQueueEpoch config a = .ok epoch) : epoch.toNat ≤ r + 1 := by
  simp only [exitQueueEpoch, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨earliest, earliestOk, rest⟩ := computed
  have earliestLe := (computeActivationExitEpoch_ok_iff.mp earliestOk).2
  have opens := holds.opens
  have latestLe := foldl_latest_le (r := r)
    (a.validators.data.toList.filter (·.exitEpoch != FAR_FUTURE_EPOCH)) earliest (by omega)
    (fun v member => by
      obtain ⟨inside, set⟩ := List.mem_filter.mp member
      exact holds.exits (v.exitEpoch, v.effectiveBalance) (List.mem_map_of_mem inside)
        (by simpa using set))
  generalize List.foldl (fun latest v => latest ⊔ v.exitEpoch) earliest
    (List.filter (fun x => x.exitEpoch != FAR_FUTURE_EPOCH) a.validators.data.toList) = latest
    at rest latestLe
  split at rest
  · obtain ⟨_, value⟩ := Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp rest)
    simp only [UInt64.toNat_one] at value
    omega
  · simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst rest
    omega

end Churn

/-! ## Plain steps -/

section Plain

private theorem Plain.of_setValidator {a b : BeaconState preset fork} {i : ValidatorIndex}
    {old v : Validator} (found : getValidator a i = .ok old) (set : a.setValidator i v = .ok b)
    (exitSame : v.exitEpoch = old.exitEpoch)
    (balanceSame : v.effectiveBalance = old.effectiveBalance) : Plain a b := by
  rw [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] at found
  rw [setValidator_eq_setValidatorAt] at set
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  obtain ⟨_, at_⟩ := List.getElem?_eq_some_iff.mp (keys_getElem? found)
  refine ⟨rfl, ⟨[], ?_, by simp⟩, rfl, rfl, rfl⟩
  rw [keys_putValidator, exitSame, balanceSame, List.append_nil, ← at_, List.set_getElem_self]

private theorem Plain.setBalance {a b : BeaconState preset fork} {i : ValidatorIndex}
    {x : Gwei} (ok : a.setBalance i x = .ok b) : Plain a b := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  exact Plain.of_validators

private theorem Plain.increase {a b : BeaconState preset fork} {i : ValidatorIndex}
    {x : Gwei} (ok : increaseBalance a i x = .ok b) : Plain a b :=
  Plain.setBalance (increaseBalance_ok ok).choose_spec

private theorem Plain.decrease {a b : BeaconState preset fork} {i : ValidatorIndex}
    {x : Gwei} (ok : decreaseBalance a i x = .ok b) : Plain a b :=
  Plain.setBalance (decreaseBalance_ok ok).choose_spec

private theorem Plain.excess {a b : BeaconState preset fork} {electra : .pectra ≤ fork}
    {index : ValidatorIndex} (ok : queueExcessActiveBalance a electra index = .ok b) :
    Plain a b := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    exact (Plain.setBalance set).trans Plain.of_validators
  · cases ok
    exact Plain.refl _

private theorem Plain.compounding {a b : BeaconState preset fork} {electra : .pectra ≤ fork}
    {index : ValidatorIndex} (ok : switchToCompoundingValidator a electra index = .ok b) :
    Plain a b := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (Plain.of_setValidator found set rfl rfl).trans (Plain.excess queued)

/-- A consolidation request with one key for both validators can only switch it to compounding. -/
private theorem Plain.sameKey {a b : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest} (same : request.sourcePubkey = request.targetPubkey)
    (ok : processConsolidationRequest config a electra request = .ok b) : Plain a b := by
  unfold processConsolidationRequest at ok
  simp only [same, beq_self_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact Plain.refl _)
    | exact Plain.compounding (liftAccessor_ok.mp ok)

end Plain

/-! ## The steps that start an exit or move a queue -/

section Exits

variable {start : BeaconState preset fork} {ceiling : Nat}

/-- An exit queue within the bounds places an amount within its cost, and keeps the registry. -/
private theorem exitQueue_bound (rates : Rates preset config) {a b : BeaconState preset fork}
    {amount : Gwei} {epoch : Epoch} {r u : Nat}
    (holds : Holds config start ceiling a r u)
    (computed : exitQueue config a amount = .ok (b, epoch)) :
    epoch.toNat ≤ r + (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ∧
      b.validators = a.validators ∧ b.slot = a.slot ∧
      (∀ electra : .pectra ≤ fork, (b.earliestExitEpoch electra).toNat ≤
        r + (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1)) ∧
      b.earliestConsolidationEpoch = a.earliestConsolidationEpoch ∧
      ∀ electra : .pectra ≤ fork, (b.exitBalanceToConsume electra).toNat ≤
        max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config a) := by
  unfold exitQueue at computed
  split at computed
  · obtain ⟨left, rfl, epochLe, leftLe⟩ := exitChurn_bound rates holds computed
    exact ⟨epochLe, rfl, rfl, fun _ => epochLe, rfl, fun _ => leftLe⟩
  · rename_i notElectra
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨queued, queueOk, rfl, rfl⟩ := computed
    have := exitQueueEpoch_bound holds queueOk
    have := Nat.zero_le (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    exact ⟨by omega, rfl, rfl, fun electra => absurd electra notElectra, rfl,
      fun electra => absurd electra notElectra⟩

/-- An exit within the bounds keeps them, and its validator pays for the move of the queue. -/
private theorem moves_exit (rates : Rates preset config) {a b : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config a index = .ok b) :
    Moves config start ceiling 0 a b := by
  obtain ⟨v, found, ⟨-, rfl⟩ | ⟨far, queued, e, withdrawable, queue, delayed, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Moves.refl _
  intro r u holds
  obtain ⟨epochLe, validators, slot, exitLe, consolidation, churnLe⟩ :=
    exitQueue_bound rates holds queue
  rw [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] at found
  rw [setValidator_eq_setValidatorAt] at set
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  -- The withdrawal delay keeps the exit below the far future.
  have started : e ≠ FAR_FUTURE_EPOCH := by
    intro equal
    have fits := (Uint64.addChecked_ok_iff.mp delayed).1
    have farValue : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have := rates.delay
    rw [equal, farValue] at fits
    omega
  have keysQueued : keys queued = keys a := by simp [keys, validators]
  refine ⟨_, Holds.exit holds slot (i := index.toNat) (w := v.effectiveBalance)
    (by rw [keys_getElem? found, far]) (by rw [keys_putValidator, keysQueued]) started epochLe
    exitLe (fun electra => ?_) churnLe⟩
  have := holds.consolidationQueue electra
  show (queued.earliestConsolidationEpoch electra).toNat ≤ _
  rw [consolidation]
  omega

/-- A partial withdrawal moves the exit queue by at most its amount in increments, plus one.

Its amount counts up to a cap on the sum of the balances, which bounds what it withdraws. -/
private theorem moves_partialWithdrawal (rates : Rates preset config)
    {a b : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei} {cap : Nat} (capped : balanceSum a ≤ cap)
    (computed : requestPartialWithdrawal config a electra index validator amount owed = .ok b) :
    Moves config start ceiling
      (min amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) a b := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨balance, read, kept, _, computed⟩ := computed
  split at computed
  · rename_i allowed
    simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨queued, epoch⟩, churned, _, _, _, _, rfl⟩ := computed
    intro r u holds
    obtain ⟨left, rfl, epochLe, leftLe⟩ := exitChurn_bound rates holds churned
    have bounded : balance.toNat ≤ cap := by
      obtain ⟨inside, found⟩ := Array.getElem?_eq_some_iff.mp (getBalance_eq_ok_iff.mp read)
      refine Nat.le_trans ?_ capped
      apply List.single_le_sum (fun _ _ => Nat.zero_le _)
      exact List.mem_map.mpr ⟨balance, found ▸ by simp, rfl⟩
    have below : (balance - kept).toNat ≤ balance.toNat := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at allowed
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt allowed.2)]
      exact Nat.sub_le _ _
    have smaller : (min (balance - kept) amount).toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        min amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
      Nat.div_le_div_right (by rw [Uint64.toNat_min]; omega)
    refine ⟨_, Holds.shift holds rfl (by simp [keys]) (fun _ => ?_) (fun electra => ?_)
      (fun _ => leftLe)⟩
    · show epoch.toNat ≤ _
      omega
    · have := holds.consolidationQueue electra
      have := Nat.zero_le (min amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      show (a.earliestConsolidationEpoch electra).toNat ≤ _
      omega
  · cases computed
    exact (Moves.refl a).mono (Nat.zero_le _)

/-- A withdrawal request spends at most its amount in increments, plus one.

Its amount counts up to a cap on the sum of the balances. -/
private theorem moves_withdrawalRequest (rates : Rates preset config)
    {a b : BeaconState preset fork} {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    {cap : Nat} (capped : balanceSum a ≤ cap)
    (computed : processWithdrawalRequest config a electra request = .ok b) :
    Moves config start ceiling
      (min request.amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) a b := by
  rcases withdrawalRequest_cases computed with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · exact (Moves.refl _).mono (Nat.zero_le _)
  · exact (moves_exit rates exited).mono (Nat.zero_le _)
  · exact moves_partialWithdrawal rates capped withdrawn

/-- Withdrawal requests keep the balances, and count each amount up to a cap on their sum. -/
private theorem moves_withdrawalRequests (rates : Rates preset config)
    {electra : .pectra ≤ fork} {cap : Nat} :
    ∀ {requests : List WithdrawalRequest} {a b : BeaconState preset fork},
      balanceSum a ≤ cap →
      requests.foldlM (processWithdrawalRequest config · electra ·) a = .ok b →
      Moves config start ceiling ((requests.map fun request =>
        min request.amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum) a b
  | [], a, b, _, computed => by
    cases computed
    exact Moves.refl a
  | x :: rest, a, b, capped, computed => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, folded⟩ := computed
    have kept : balanceSum middle = balanceSum a := by
      simp only [balanceSum, processWithdrawalRequest_balances first]
    simpa using (moves_withdrawalRequest rates capped first).trans
      (moves_withdrawalRequests rates (kept ▸ capped) folded)

/-- Deposit requests keep the balances. -/
private theorem depositRequests_balanceSum {electra : .pectra ≤ fork}
    {requests : List DepositRequest} {a b : BeaconState preset fork}
    (computed : requests.foldlM (processDepositRequest · electra ·) a = .ok b) :
    balanceSum b = balanceSum a := by
  have kept := foldlM_ok_invariant (fun s : BeaconState preset fork => s.balances = a.balances)
    (fun _ _ _ before ok => (processDepositRequest_ok ok).2.2.trans before) rfl computed
  simp only [balanceSum, kept]

/-- A consolidation churn above the activation balance places its source within its cost. -/
private theorem consolidationChurn_bound (rates : Rates preset config)
    {a b : BeaconState preset fork} {electra : .pectra ≤ fork} {amount churn : Gwei}
    {epoch : Epoch} {r u : Nat} (holds : Holds config start ceiling a r u)
    (churnOk : getConsolidationChurnLimit config a = .ok churn)
    (above : preset.MIN_ACTIVATION_BALANCE < churn)
    (computed :
      computeConsolidationEpochAndUpdateChurn config a electra amount = .ok (b, epoch)) :
    ∃ left, b = { a with
        consolidationBalanceToConsume := fun _ => left,
        earliestConsolidationEpoch := fun _ => epoch } ∧
      epoch.toNat ≤ r + (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨first, firstOk, used, usedOk, ⟨queued, left⟩, queueOk, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  obtain rfl : used = churn := Except.ok.inj (usedOk.symm.trans churnOk)
  have firstLe := (computeActivationExitEpoch_ok_iff.mp firstOk).2
  have opens := holds.opens
  have positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    UInt64.lt_iff_toNat_lt.mp rates.increment
  have lower : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ used.toNat := by
    have := UInt64.le_iff_toNat_le.mp rates.activation
    have := UInt64.lt_iff_toNat_lt.mp above
    omega
  obtain ⟨epochLe, -⟩ := churnQueue_bound queueOk positive lower
    (holds.consolidationQueue electra) (by omega)
  exact ⟨left, rfl, epochLe⟩

/-- A consolidation that is accepted exits its source, which pays for the move of the queue. -/
private theorem moves_queueConsolidation (rates : Rates preset config)
    {a b : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator} {churn : Gwei}
    (churnOk : getConsolidationChurnLimit config a = .ok churn)
    (above : preset.MIN_ACTIVATION_BALANCE < churn)
    (sourceAt : a.validators.data[sourceIndex.toNat]? = some source)
    (stays : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed : queueConsolidation config a electra sourceIndex source targetIndex = .ok b) :
    Moves config start ceiling 0 a b := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    Uint64.addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churned, epoch⟩, churnStep, _, ⟨fits, -⟩, marked, set, _, _, final⟩ := computed
  simp only [Except.ok.injEq] at final
  subst final
  intro r u holds
  obtain ⟨left, rfl, epochLe⟩ := consolidationChurn_bound rates holds churnOk above churnStep
  rw [setValidator_eq_setValidatorAt] at set
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  -- The withdrawal delay keeps the exit below the far future.
  have started : epoch ≠ FAR_FUTURE_EPOCH := by
    intro equal
    have farValue : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have := rates.delay
    rw [equal, farValue] at fits
    omega
  refine ⟨_, Holds.exit holds rfl (i := sourceIndex.toNat) (w := source.effectiveBalance)
    (by rw [keys_getElem? sourceAt, stays]) (keys_putValidator _ inside _) started epochLe
    (fun electra => ?_) (fun _ => epochLe) (fun electra => holds.churn electra)⟩
  have := holds.exitQueue electra
  have := Nat.zero_le (source.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
  show (a.earliestExitEpoch electra).toNat ≤ _
  simp only [costK]
  omega

/-- A consolidation request keeps the bounds, whether it switches, consolidates or does nothing. -/
private theorem moves_consolidationRequest (rates : Rates preset config)
    {a b : BeaconState preset fork} {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (computed : processConsolidationRequest config a electra request = .ok b) :
    Moves config start ceiling 0 a b := by
  by_cases same : request.sourcePubkey = request.targetPubkey
  · exact (Plain.sameKey same computed).moves
  · rcases eq_or_queueConsolidation_of_processConsolidationRequest same computed with
      rfl | ⟨_, _, _, _, accepted, queued⟩
    · exact Moves.refl _
    · obtain ⟨churn, churnOk, above⟩ := accepted.churn
      exact moves_queueConsolidation rates churnOk above accepted.sourceAt accepted.sourceStays
        queued

end Exits

/-! ## The other steps of a block -/

section Others

private theorem Plain.add {a b : BeaconState preset fork} {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry a key credentials amount = .ok b) : Plain a b := by
  have pushed := addValidatorToRegistry_validators_eq_push ok
  have shape : b.slot = a.slot ∧ b.earliestExitEpoch = a.earliestExitEpoch ∧
      b.earliestConsolidationEpoch = a.earliestConsolidationEpoch ∧
      b.exitBalanceToConsume = a.exitBalanceToConsume := by
    unfold addValidatorToRegistry at ok
    split at ok
    · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
        pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
      exact ⟨rfl, rfl, rfl, rfl⟩
    · split at ok <;> cases ok
      exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨shape.1, ⟨[((getValidatorFromDeposit preset fork key credentials amount).exitEpoch,
    (getValidatorFromDeposit preset fork key credentials amount).effectiveBalance)],
    by simp [keys, pushed], by simp [getValidatorFromDeposit]⟩, shape.2.1, shape.2.2.1,
    shape.2.2.2⟩

private theorem Plain.deposit {a b : BeaconState preset fork} {before : fork < .hegota}
    {deposit : Deposit} (ok : processDeposit config checks before a deposit = .ok b) :
    Plain a b := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  refine (Plain.of_validators : Plain a { a with eth1DepositIndex := fun _ => next }).trans ?_
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, pending⟩
  · exact Plain.refl _
  · exact Plain.of_validators
  · exact (Plain.add added).trans Plain.of_validators
  · rcases applyPendingDeposit_cases pending with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact Plain.refl _
    · exact Plain.increase raised
    · exact Plain.add added

private theorem Plain.depositRequest {a b : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : DepositRequest} (ok : processDepositRequest a electra request = .ok b) :
    Plain a b := by
  obtain ⟨recordedStart, recorded⟩ :=
    recordDepositRequestsStart_eq (state := a) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact Plain.of_validators

private theorem Plain.withdrawals {a b : BeaconState preset fork} {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals a capella payload = .ok b) : Plain a b := by
  have expected {a b : BeaconState preset fork} {expected : ExpectedWithdrawals}
      (applied : applyExpectedWithdrawals a capella expected = .ok b) : Plain a b := by
    apply applyExpectedWithdrawals_of_setters Plain Plain.refl (fun one two => one.trans two)
      (fun withdrawn => by rw [applyWithdrawal_eq withdrawn]; exact Plain.of_validators)
      _ _ _ _ _ _ applied
    all_goals exact fun _ _ => Plain.of_validators
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact expected applied
    · cases ok
      exact Plain.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact expected applied

private theorem Plain.blockExecution {a b : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine a body bellatrix = .ok b) : Plain a b := by
  have payload {a b : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (paid : processExecutionPayload config engine a body execution = .ok b) : Plain a b := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    exact Plain.of_validators
  unfold processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact (Plain.withdrawals withdrawn).trans Plain.of_validators
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (Plain.withdrawals withdrawn).trans (payload paid)
  · dsimp only at ok
    split at ok
    · exact payload ok
    · cases ok
      exact Plain.refl _

private theorem Plain.attestation {a b : BeaconState preset fork}
    {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : processAttestation config checks a parentSlot attestation = .ok b) : Plain a b := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte] at ok
    unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨updated, _⟩, folded, _, _, _, raisedOk, final⟩ := ok
    have flagged : Plain a (setEpochParticipation a
        (attestation.data.target.epoch == getCurrentEpoch a) updated) := by
      unfold setEpochParticipation
      split <;> exact Plain.of_validators
    have raised := flagged.trans (Plain.increase raisedOk)
    split at final
    · rw [recordPaymentWeight_eq final]
      exact raised.trans Plain.of_validators
    · cases final
      exact raised
  · obtain ⟨_, _, _, _, _, recorded, _⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) ok
    have kept := recordPendingAttestation_ok recorded
    split at kept
    all_goals
      obtain ⟨_, rest⟩ := kept
      rw [← rest]
      exact Plain.of_validators

variable {start : BeaconState preset fork} {ceiling : Nat}

private theorem moves_slash (rates : Rates preset config) {a b : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config a index whistleblower = .ok b) :
    Moves config start ceiling 0 a b := by
  obtain ⟨exited, validator, _, marked, _, _, slashings, lowered, _, _, raised, last, exitedOk,
    foundOk, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ := slashValidator_ok ok
  -- The last steps change only the balances, the slashed balances and the builder payments.
  have tail : Plain marked b := by
    have chain := ((Plain.of_validators : Plain marked { marked with slashings }).trans
      (Plain.decrease loweredOk)).trans ((Plain.increase raisedOk).trans (Plain.increase lastOk))
    subst done
    split
    · exact chain.trans Plain.of_validators
    · exact chain
  exact (moves_exit rates exitedOk).trans₀
    ((Plain.of_setValidator foundOk markedOk rfl rfl).trans tail).moves

private theorem moves_proposerSlashing (rates : Rates preset config)
    {a b : BeaconState preset fork} {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks a slashing = .ok b) :
    Moves config start ceiling 0 a b := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact moves_slash rates slashed

private theorem moves_attesterSlashing (rates : Rates preset config)
    {a b : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks a slashing = .ok b) :
    Moves config start ceiling 0 a b := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant
    (fun step : BeaconState preset fork × Bool => Moves config start ceiling 0 a step.1)
    (fun step _ _ before ok => ?_) (Moves.refl a) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact before.trans₀ (moves_slash rates slashed)
  · cases ok
    exact before

/-- The requests of a block before Gloas spend the cost of its withdrawal requests.

That cost counts each amount up to a cap on the sum of the balances where the requests start. -/
private theorem moves_executionRequests (rates : Rates preset config)
    {a b : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam} {cap : Nat} (capped : balanceSum a ≤ cap)
    (ok : processExecutionRequests config a body electra = .ok b) :
    Moves config start ceiling (partialExitCost preset cap body) a b := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  have cost : partialExitCost preset cap body =
      ((body.executionRequests electra).withdrawals.data.toList.map fun request =>
        min request.amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum := by
    have notGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le.mpr electra.2
    simp only [partialExitCost, blockWithdrawalRequests, notGloas, electra.1, ↓reduceDIte]
  rw [cost]
  have whole : Moves config start ceiling _ a b :=
    (Moves.foldlM (fun _ _ _ ok => (Plain.depositRequest ok).moves) deposits).trans
    ((moves_withdrawalRequests rates
        ((depositRequests_balanceSum deposits).trans_le capped) withdrawals).trans
      (Moves.foldlM (fun _ _ _ ok => moves_consolidationRequest rates ok) consolidations))
  exact whole.mono (by omega)

/-- From Gloas, the payload of the parent spends the cost of its withdrawal requests.

That cost counts each amount up to a cap on the sum of the balances before the payload. -/
private theorem moves_parentPayload (rates : Rates preset config)
    {a b : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} {cap : Nat} (capped : balanceSum a ≤ cap)
    (ok : processParentExecutionPayload config checks a gloas body = .ok b) :
    Moves config start ceiling (partialExitCost preset cap body) a b := by
  rcases processParentExecutionPayload_ok ok with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, exited, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, recorded⟩
  · exact (Moves.refl _).mono (Nat.zero_le _)
  have cost : partialExitCost preset cap body =
      ((body.parentExecutionRequests gloas).withdrawals.data.toList.map fun request =>
        min request.amount.toNat cap / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum := by
    simp only [partialExitCost, blockWithdrawalRequests, gloas, ↓reduceDIte]
  rw [cost]
  have settledPlain : Plain a settled := by
    rw [settleParentPayment_eq settledOk]
    exact Plain.of_validators
  have settledCapped : balanceSum settled ≤ cap := by
    rw [settleParentPayment_eq settledOk]
    exact capped
  have builders := foldlM_ok_invariant (Plain _)
    (fun _ _ _ before ok => before.trans (by
      obtain ⟨_, rfl⟩ := processBuilderDepositRequest_eq ok
      exact Plain.of_validators)) (Plain.refl _) buildersOk
  have exits := foldlM_ok_invariant (Plain _)
    (fun _ _ _ before ok => before.trans (by
      obtain ⟨_, rfl⟩ := processBuilderExitRequest_eq ok
      exact Plain.of_validators)) (Plain.refl _) exitsOk
  have last : Plain exited b := by
    rw [recorded]
    exact Plain.of_validators
  have whole := (settledPlain.moves (config := config) (start := start)
    (ceiling := ceiling)).trans <|
    (Moves.foldlM (fun _ _ _ ok => (Plain.depositRequest ok).moves) depositsOk).trans <|
    (moves_withdrawalRequests rates
      ((depositRequests_balanceSum depositsOk).trans_le settledCapped) withdrawalsOk).trans <|
    (Moves.foldlM (fun _ _ _ ok => moves_consolidationRequest rates ok) consolidationsOk).trans <|
    builders.moves.trans <| exits.moves.trans last.moves
  exact whole.mono (by omega)

/-- The operations of a block spend the cost of its withdrawal requests before Gloas only.

That cost counts each amount up to a cap on the sum of the balances where the requests start. -/
private theorem moves_operations (rates : Rates preset config)
    {a b : BeaconState preset fork} {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    {cap : Nat} (capped : ∀ (before : fork < .hegota) changed,
      RequestsStart config checks body parentSlot before a changed → balanceSum changed ≤ cap)
    (ok : processOperations config checks a body parentSlot = .ok b) :
    Moves config start ceiling
      (if .glamsterdam ≤ fork then 0 else partialExitCost preset cap body) a b := by
  have proposers {a b : BeaconState preset fork}
      (ok : body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks) a =
        .ok b) : Moves config start ceiling 0 a b :=
    Moves.foldlM (fun _ _ _ ok => moves_proposerSlashing rates ok) ok
  have attesters {a b : BeaconState preset fork}
      (ok : body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks) a =
        .ok b) : Moves config start ceiling 0 a b :=
    Moves.foldlM (fun _ _ _ ok => moves_attesterSlashing rates ok) ok
  have attestations {a b : BeaconState preset fork}
      (ok : body.attestations.data.toList.foldlM (processAttestation config checks · parentSlot ·)
        a = .ok b) : Moves config start ceiling 0 a b :=
    Moves.foldlM (fun _ _ _ ok => (Plain.attestation ok).moves) ok
  have exits {a b : BeaconState preset fork}
      (ok : body.voluntaryExits.data.toList.foldlM (processVoluntaryExit config checks) a =
        .ok b) : Moves config start ceiling 0 a b :=
    Moves.foldlM (fun _ _ _ ok => moves_exit rates (processVoluntaryExit_initiates ok)) ok
  have change {a b : BeaconState preset fork} {signed : SignedBLSToExecutionChange}
      (ok : processBlsToExecutionChange config checks a signed = .ok b) :
      Moves config start ceiling 0 a b := by
    obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
    exact (Plain.of_setValidator found set rfl rfl).moves
  unfold processOperations at ok
  split at ok
  · rename_i gloas
    simp only [gloas, ↓reduceIte]
    unfold processOperationsGloas at ok
    simp only [bind_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := ok
    exact (proposers proposersOk).trans₀ <| (attesters attestersOk).trans₀ <|
      (attestations attestedOk).trans₀ <| (exits exitsOk).trans₀ <|
      (Moves.foldlM (fun _ _ _ ok => change ok) changesOk).trans₀
      (Moves.foldlM (fun _ _ _ ok => by rw [processPayloadAttestation_eq ok]; exact Moves.refl _)
        paid)
  · rename_i gloas
    simp only [gloas, ↓reduceIte]
    simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
      exitsOk, changed, changesOk, requestsOk⟩ := ok
    have changes : Moves config start ceiling 0 exited changed := by
      unfold processBlsToExecutionChanges at changesOk
      split at changesOk
      · rw [← Array.foldlM_toList] at changesOk
        exact Moves.foldlM (fun _ _ _ ok => change ok) changesOk
      · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
        exact changesOk ▸ Moves.refl _
    have requested : Moves config start ceiling (partialExitCost preset cap body) changed b := by
      split at requestsOk
      · exact moves_executionRequests rates (capped _ changed ⟨_, _, _, _, _, proposersOk,
          attestersOk, attestedOk, depositedOk, exitsOk, changesOk⟩) requestsOk
      · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
        exact requestsOk ▸ (Moves.refl _).mono (Nat.zero_le _)
    have whole : Moves config start ceiling _ a b :=
      (proposers proposersOk).trans <| (attesters attestersOk).trans <|
      (attestations attestedOk).trans <|
      (Moves.foldlM (fun _ _ _ ok => (Plain.deposit ok).moves) depositedOk).trans <|
      (exits exitsOk).trans <| changes.trans requested
    exact whole.mono (by omega)

/-- The steps of a block before its operations spend the cost of its withdrawal requests.

They spend it from Gloas only, with each amount counted up to a cap on the sum of the balances. -/
private theorem moves_operationsInput (rates : Rates preset config)
    {engine : ExecutionEngine preset fork} {a input : BeaconState preset fork}
    {block : BeaconBlock preset fork} {cap : Nat} (capped : balanceSum a ≤ cap)
    (started : OperationsInput config checks engine a block input) :
    Moves config start ceiling
      (if .glamsterdam ≤ fork then partialExitCost preset cap block.body else 0) a input := by
  obtain ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk, randaoOk,
    eth1Ok⟩ := started
  have paid : Moves config start ceiling
      (if .glamsterdam ≤ fork then partialExitCost preset cap block.body else 0) a parented := by
    split at paidOk
    · rename_i gloas
      simp only [gloas, ↓reduceIte]
      exact moves_parentPayload rates capped paidOk
    · rename_i gloas
      simp only [gloas, ↓reduceIte]
      cases paidOk
      exact Moves.refl _
  have header : Plain parented headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    exact Plain.of_validators
  have execution : Plain headed executed := by
    split at executionOk
    · exact Plain.blockExecution executionOk
    · cases executionOk
      exact Plain.refl _
  have randao : Plain executed revealed := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    exact Plain.of_validators
  have eth1 : Plain revealed input := by
    split at eth1Ok
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
      rw [← rest]
      exact Plain.of_validators
    · cases eth1Ok
      exact Plain.refl _
  exact (paid.trans (header.trans (execution.trans (randao.trans eth1))).moves).mono
    (Nat.le_of_eq (Nat.add_zero _))

end Others

/-- The bounds of a block on both queues, the exit epochs and the churn carried for exits. -/
private theorem processBlock_exits_churn {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (activation : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {ceiling : Nat}
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (queues : ∀ electra : .pectra ≤ fork, (state.earliestExitEpoch electra).toNat ≤ ceiling ∧
      (state.earliestConsolidationEpoch electra).toNat ≤ ceiling)
    {cap : Nat}
    (capped : balanceSum state + pendingDepositSum state + blockDepositAmount block.body +
        (slashedBalanceSum after - slashedBalanceSum state) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        blockRewardCap preset state ≤ cap) :
    ∃ reached, reached + exitCost preset after ≤
        ceiling + exitCost preset state + exitCostFrom preset after state.validators.data.size +
          partialExitCost preset cap block.body ∧
      (getCurrentEpoch after).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ reached ∧
      (∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch.toNat ≤ reached) ∧
      ∀ electra : .pectra ≤ fork, (after.earliestExitEpoch electra).toNat ≤ reached ∧
        (after.earliestConsolidationEpoch electra).toNat ≤ reached ∧
        (after.exitBalanceToConsume electra).toNat ≤
          max (state.exitBalanceToConsume electra).toNat (exitChurnCeiling config after) := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  have rates : Rates preset config := ⟨increment, minimum, maximum, activation, delay⟩
  have tail : Plain last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact Plain.of_validators
    · cases synced
      exact Plain.refl _
  have whole := ((moves_operationsInput (start := state) (ceiling := ceiling) rates
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _)
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) capped))))
    started).trans (moves_operations rates (fun _ _ reached =>
      Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _)
        (processBlock_supply_le_cap_of_requestsStart computed started reached)) capped)
      operated)).trans tail.moves
  -- The start holds the bounds with the ceiling and nothing spent.
  have initial : Holds config state ceiling state ceiling 0 := by
    refine ⟨first, Nat.le_refl _, fun k member finite => ?_, fun electra => (queues electra).1,
      fun electra => (queues electra).2, fun _ => Nat.le_max_left _ _, by omega⟩
    obtain ⟨validator, inside, rfl⟩ := List.mem_map.mp member
    exact exits validator (Array.mem_toList_iff.mp inside) finite
  obtain ⟨reached, final⟩ := whole ceiling 0 initial
  have spent : 0 + ((if .glamsterdam ≤ fork then partialExitCost preset cap block.body else 0) +
      (if .glamsterdam ≤ fork then 0 else partialExitCost preset cap block.body) + 0) =
        partialExitCost preset cap block.body := by
    split <;> simp
  rw [spent] at final
  refine ⟨reached, final.potential, final.opens, fun validator member finite => final.exits _
    (List.mem_map_of_mem (Array.mem_toList_iff.mpr member)) finite,
    fun electra => ⟨final.exitQueue electra, final.consolidationQueue electra,
      final.churn electra⟩⟩


/-- A block raises the end of each exit queue, plus the cost still owed, by a bounded amount.

Before the block, each exit epoch that is set is at most a ceiling.

From Electra, the ends of the exit and consolidation queues are at most that ceiling too.

The ceiling covers the first epoch at which a new exit can take effect.

The increment is positive.

It is at most the least churn, the largest churn and the least balance to activate.

The withdrawal delay is positive, so no exit that succeeds lands on the far future epoch.

A cap is at least the bound on the supply of the block.

It then bounds the sum of the balances where each withdrawal request of the block runs.

After the block, some bound covers each exit epoch that is set and, from Electra, both queue ends.

It also covers the first epoch at which a new exit can take effect.

That bound plus the cost still owed is at most the ceiling plus the cost owed before the block.

It adds the cost of the validators that joined in the block.

It also adds the cost of the withdrawal requests of the block, with their amounts capped. -/
theorem processBlock_exits {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (activation : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {ceiling : Nat}
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (queues : ∀ electra : .pectra ≤ fork, (state.earliestExitEpoch electra).toNat ≤ ceiling ∧
      (state.earliestConsolidationEpoch electra).toNat ≤ ceiling)
    {cap : Nat}
    (capped : balanceSum state + pendingDepositSum state + blockDepositAmount block.body +
        (slashedBalanceSum after - slashedBalanceSum state) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        blockRewardCap preset state ≤ cap) :
    ∃ reached, reached + exitCost preset after ≤
        ceiling + exitCost preset state + exitCostFrom preset after state.validators.data.size +
          partialExitCost preset cap block.body ∧
      (getCurrentEpoch after).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ reached ∧
      (∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch.toNat ≤ reached) ∧
      ∀ electra : .pectra ≤ fork, (after.earliestExitEpoch electra).toNat ≤ reached ∧
        (after.earliestConsolidationEpoch electra).toNat ≤ reached := by
  obtain ⟨reached, potential, opens, exited, queued⟩ := processBlock_exits_churn computed
    increment minimum maximum activation delay first exits queues capped
  exact ⟨reached, potential, opens, exited, fun electra =>
    ⟨(queued electra).1, (queued electra).2.1⟩⟩

/-- From Electra, the churn carried for exits after a block is within a bound.

That bound is the larger of the churn before the block and one churn bound after it.

The increment is positive.

It is at most the least churn, the largest churn and the least balance to activate.

The withdrawal delay is positive. -/
theorem processBlock_exitBalanceToConsume_le {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (activation : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electra : .pectra ≤ fork) :
    (after.exitBalanceToConsume electra).toNat ≤
      max (state.exitBalanceToConsume electra).toNat (exitChurnCeiling config after) := by
  -- Any ceiling above every epoch of 64 bits meets the hypotheses on the queues.
  obtain ⟨_, _, _, _, queued⟩ := processBlock_exits_churn computed increment minimum maximum
    activation delay (ceiling := 2 ^ 64 + (getCurrentEpoch state).toNat + 1 +
      preset.MAX_SEED_LOOKAHEAD.toNat) (by omega)
    (fun validator _ _ => by have := validator.exitEpoch.toNat_lt; omega)
    (fun electra => ⟨by have := (state.earliestExitEpoch electra).toNat_lt; omega,
      by have := (state.earliestConsolidationEpoch electra).toNat_lt; omega⟩)
    (Nat.le_refl _)
  exact (queued electra).2.2

end EthLib.Consensus
