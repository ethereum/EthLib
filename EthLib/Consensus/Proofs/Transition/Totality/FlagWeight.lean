module

public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock
import EthLib.Base.Proofs.List
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.Time
import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the weight of the flags within an epoch

From Altair, a block pays its proposer for the attestations it includes.

That reward is at most the rise of the weight of the flags, over 448.

Within an epoch the base reward per increment stays.

So these rises add up to at most the weight at its end.

That weight sums over the validators with a flag set, in the previous and the current epoch.

The base reward per increment shrinks as the total active balance grows.

So the weight needs a bound by the active balances, not by the effective balances of the registry.

It holds when each validator with a flag set in an epoch is active at that epoch.

The active balance of the previous epoch still needs its own bound by the run.

An empty slot that does not end an epoch keeps the flags, the registry and the active balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}

/-- The sum of the effective balances of the validators active at an epoch. -/
def activeBalanceAt (state : BeaconState preset fork) (epoch : Epoch) : Nat :=
  ((state.validators.data.toList.filter (isActiveValidator · epoch)).map
    (·.effectiveBalance.toNat)).sum

/-- The weight of the flags is within the active balances of the two recent epochs.

Each epoch counts 54 times the base reward of one increment.

It counts it once per whole increment of the active balance at that epoch.

Both epochs read the effective balances of the state, not those at that epoch.

The base reward is that of one increment at the total active balance of the state.

It holds trivially before Altair, and when the total active balance cannot be computed. -/
def FlagsWithinActive (state : BeaconState preset fork) : Prop :=
  flagRewardWeight preset (blockPerIncrement preset state) state ≤
    (activeBalanceAt state (getPreviousEpoch state) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      activeBalanceAt state (getCurrentEpoch state) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
      blockPerIncrement preset state * 54

/-- Dividing each element of a list, rounding down, gives at most the sum divided. -/
private theorem sum_div_le (d : Nat) : ∀ l : List Nat, (l.map (· / d)).sum ≤ l.sum / d
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_div_le d l
    have := Nat.div_add_div_le_add_div (x := x) (y := l.sum) (z := d)
    omega

/-- The weight of the flags of one epoch of participation, at a base reward per increment. -/
private def weigh (perIncrement : Nat) (state : BeaconState preset fork)
    (participation : EpochParticipation preset fork) : Nat :=
  ((List.range state.validators.data.size).map fun j =>
    ((participation.data[j]?).map fun flags =>
      ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
        if hasFlag flags flag.val.toUInt64 then
          ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0 /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement *
              PARTICIPATION_FLAG_WEIGHTS[flag].toNat
        else 0).sum).getD 0).sum

/-- From Altair, the weight of the flags is that of the previous plus that of the current epoch. -/
private theorem flagRewardWeight_eq (altair : .altair ≤ fork) (perIncrement : Nat)
    (state : BeaconState preset fork) :
    flagRewardWeight preset perIncrement state =
      weigh perIncrement state (state.previousEpochParticipation altair) +
        weigh perIncrement state (state.currentEpochParticipation altair) := by
  unfold flagRewardWeight
  split
  · rfl
  · rename_i no
    exact absurd altair no

/-- The three flag weights add up to 54. -/
private theorem flag_weights_sum :
    ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
      PARTICIPATION_FLAG_WEIGHTS[flag].toNat).sum = 54 := by
  decide +kernel

/-- No flag is set in a zero byte. -/
private theorem hasFlag_zero (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
    hasFlag 0 flag.val.toUInt64 = false := by
  revert flag
  decide +kernel

/-- One epoch of participation weighs at most 54 times the given base reward per increment.

That reward counts once per whole increment of the marked effective balances.

Each position with a flag set must be marked. -/
private theorem weigh_le (perIncrement : Nat) (state : BeaconState preset fork)
    (participation : EpochParticipation preset fork) (marks : Array Bool)
    (marked : ∀ (j : Nat) (flags : ParticipationFlags), participation.data[j]? = some flags →
      flags ≠ 0 → j < state.validators.data.size → (marks[j]?).getD false = true) :
    weigh perIncrement state participation ≤
      sumMarked state.validators.data marks / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        perIncrement * 54 := by
  set inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  set n := state.validators.data.size
  let eff : Nat → Nat := fun j =>
    ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0
  let mark : Nat → Nat → Nat := fun j x => if (marks[j]?).getD false then x else 0
  have term : ∀ j ∈ List.range n,
      ((participation.data[j]?).map fun flags =>
        ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
          if hasFlag flags flag.val.toUInt64 then
            eff j / inc * perIncrement * PARTICIPATION_FLAG_WEIGHTS[flag].toNat
          else 0).sum).getD 0 ≤ mark j (eff j / inc) * perIncrement * 54 := by
    intro j member
    have lt := List.mem_range.mp member
    cases found : participation.data[j]? with
    | none => simp
    | some flags =>
      by_cases zero : flags = 0
      · subst zero
        simp [hasFlag_zero]
      · have yes := marked j flags found zero lt
        simp only [mark, yes, ite_true, Option.map_some, Option.getD_some]
        calc _ ≤ ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
              eff j / inc * perIncrement * PARTICIPATION_FLAG_WEIGHTS[flag].toNat).sum :=
              List.sum_le_sum fun flag _ => by split <;> omega
          _ = eff j / inc * perIncrement * 54 := by
              rw [sum_map_mul_left, flag_weights_sum]
  have step1 : weigh perIncrement state participation ≤
      ((List.range n).map fun j => mark j (eff j / inc) * perIncrement * 54).sum :=
    sum_map_le_sum_map (fun j m => term j m)
  have step2 : ((List.range n).map fun j => mark j (eff j / inc) * perIncrement * 54).sum =
      ((List.range n).map fun j => mark j (eff j / inc)).sum * perIncrement * 54 := by
    rw [sum_map_mul_right, sum_map_mul_right]
  have step3 : ((List.range n).map fun j => mark j (eff j / inc)).sum ≤
      sumMarked state.validators.data marks / inc := by
    rw [sumMarked_eq_sum]
    have eq : ((List.range n).map fun j => mark j (eff j / inc)) =
        ((List.range n).map fun j => mark j (eff j)).map (· / inc) := by
      rw [List.map_map]
      refine List.map_congr_left fun j _ => ?_
      simp only [mark, Function.comp]
      split <;> simp
    rw [eq]
    exact sum_div_le inc _
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := Nat.mul_le_mul_right 54 (Nat.mul_le_mul_right perIncrement step3)

/-- The sum of a function over the positions of a list is the sum over its elements. -/
private theorem sum_range_getElem? (g : Validator → Nat) :
    ∀ l : List Validator, ((List.range l.length).map fun j => ((l[j]?).map g).getD 0).sum =
      (l.map g).sum
  | [] => by simp
  | x :: t => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    rw [sum_range_getElem? g t]

/-- The sum of the effective balances of the validators that pass a test, as a sum of all. -/
private theorem sum_filter_effective (p : Validator → Bool) :
    ∀ l : List Validator, ((l.filter p).map (·.effectiveBalance.toNat)).sum =
      (l.map fun v => if p v then v.effectiveBalance.toNat else 0).sum
  | [] => rfl
  | x :: t => by
    rw [List.filter_cons]
    cases h : p x <;> simp [h, sum_filter_effective p t]

/-- The marked sum for the marks of an epoch is the active balance at that epoch. -/
private theorem sumMarked_active (state : BeaconState preset fork) (epoch : Epoch) :
    sumMarked state.validators.data (state.validators.data.map (isActiveValidator · epoch)) =
      activeBalanceAt state epoch := by
  rw [sumMarked_eq_sum, activeBalanceAt, sum_filter_effective,
    ← Array.length_toList]
  rw [← sum_range_getElem? (fun v => if isActiveValidator v epoch = true then
    v.effectiveBalance.toNat else 0) state.validators.data.toList]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Array.getElem?_map, Array.getElem?_toList]
  cases state.validators.data[j]? <;> simp

/-- The weight of the flags is within the active balances when only active validators have flags.

From Altair, each validator with a flag set in an epoch must be active at that epoch.

Attestations set flags only for committee members, who are active at the epoch of their target.

That invariant is not proved here. -/
theorem FlagsWithinActive.of_active {state : BeaconState preset fork}
    (previous : ∀ altair : .altair ≤ fork, ∀ (j : Nat) (flags : ParticipationFlags),
      (state.previousEpochParticipation altair).data[j]? = some flags → flags ≠ 0 →
      ∀ validator, state.validators.data[j]? = some validator →
        isActiveValidator validator (getPreviousEpoch state))
    (current : ∀ altair : .altair ≤ fork, ∀ (j : Nat) (flags : ParticipationFlags),
      (state.currentEpochParticipation altair).data[j]? = some flags → flags ≠ 0 →
      ∀ validator, state.validators.data[j]? = some validator →
        isActiveValidator validator (getCurrentEpoch state)) :
    FlagsWithinActive state := by
  unfold FlagsWithinActive
  by_cases altair : .altair ≤ fork
  · rw [flagRewardWeight_eq altair]
    have each : ∀ (participation : EpochParticipation preset fork) (epoch : Epoch),
        (∀ (j : Nat) (flags : ParticipationFlags), participation.data[j]? = some flags →
          flags ≠ 0 → ∀ validator, state.validators.data[j]? = some validator →
            isActiveValidator validator epoch) →
        weigh (blockPerIncrement preset state) state participation ≤
          activeBalanceAt state epoch / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            blockPerIncrement preset state * 54 := by
      intro participation epoch flagged
      have := weigh_le (blockPerIncrement preset state) state participation
        (state.validators.data.map (isActiveValidator · epoch)) fun j flags found nonzero lt => by
          obtain ⟨validator, hv⟩ : ∃ validator, state.validators.data[j]? = some validator :=
            ⟨_, Array.getElem?_eq_getElem lt⟩
          simp [Array.getElem?_map, hv, flagged j flags found nonzero validator hv]
      rwa [sumMarked_active] at this
    have first := each _ _ (previous altair)
    have second := each _ _ (current altair)
    rw [Nat.add_mul, Nat.add_mul]
    omega
  · unfold flagRewardWeight
    split
    · rename_i yes
      exact absurd yes altair
    · exact Nat.zero_le _

/-- An empty slot that does not end an epoch keeps the flags, the registry and the active balance.

It keeps the epoch too.

So it keeps the base reward of one increment, and the weight of the flags at any base reward. -/
theorem advanceSlot_flagsKept {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after)
    (inside : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0) :
    after.validators = state.validators ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      after.previousEpochParticipation = state.previousEpochParticipation ∧
      after.currentEpochParticipation = state.currentEpochParticipation ∧
      getTotalActiveBalance after = getTotalActiveBalance state ∧
      blockPerIncrement preset after = blockPerIncrement preset state ∧
      ∀ perIncrement, flagRewardWeight preset perIncrement after =
        flagRewardWeight preset perIncrement state := by
  obtain ⟨next, cached, epoched, nextEq, cachedOk, epochOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have notZero : ¬ next % preset.SLOTS_PER_EPOCH = 0 := by
    intro zero
    have := congrArg UInt64.toNat zero
    rw [UInt64.toNat_mod, nextEq] at this
    exact inside this
  unfold epochIfLast at epochOk
  simp only [notZero, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
  subst epochOk
  have epoch : computeEpochAtSlot preset next = computeEpochAtSlot preset state.slot := by
    unfold computeEpochAtSlot
    rw [← UInt64.toNat_inj, UInt64.toNat_div, UInt64.toNat_div]
    exact nextSlot_epoch_of_inside nextEq notZero
  have active : ∀ s : BeaconState preset fork, s.validators = state.validators →
      s.slot = next → getTotalActiveBalance s = getTotalActiveBalance state := by
    intro s validators slot
    simp only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getTotalBalance,
      getCurrentEpoch, slot, epoch, validators]
    rfl
  refine ⟨rfl, epoch, rfl, rfl, ?_, ?_, fun _ => rfl⟩
  · apply active <;> rfl
  · unfold blockPerIncrement
    rw [show getTotalActiveBalance _ = getTotalActiveBalance state from by
      apply active <;> rfl]

/-- An empty slot that does not end an epoch keeps the bound on the weight of the flags. -/
theorem advanceSlot_flagsWithinActive {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after)
    (inside : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0) :
    FlagsWithinActive after ↔ FlagsWithinActive state := by
  obtain ⟨validators, epoch, -, -, -, perIncrement, weight⟩ :=
    advanceSlot_flagsKept computed inside
  unfold FlagsWithinActive activeBalanceAt getPreviousEpoch
  rw [validators, epoch, perIncrement, weight]

end EthLib.Consensus
