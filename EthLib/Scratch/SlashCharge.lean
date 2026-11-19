module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinSum

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety PinSplit

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Charge

variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The slashing credits of C's run are paid for each key by its envelope or its charge.

A key of R's registry is paid by the envelope on its effective balance.

A key beyond it is paid by the charge that its exit leaves. -/
private theorem slashing_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (env cr : ℕ → ℕ)
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < pulled.validators.data.size → effectiveAt a i ≤ env i)
    (created : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, pulled.validators.data.size ≤ i →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ cr i) :
    (eventsC.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      ∑ i ∈ (Finset.range counted.validators.data.size).filter (fun i =>
          (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
            (counted.validators.data[i]?.map (·.slashed)).getD false = true),
        (if i < pulled.validators.data.size then
          env i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else cr i) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  refine slashing_credits_le (shared.append fromFin) tailC h.genesis h.early h.caps.compounding
    highC endEpochC _ _ ?_ replayedC
  intro a b step member i inside flag
  obtain ⟨pre, post, cut, aEarly, -⟩ := Run.contains_step_facts member h.early
  have above : fork ≤ a.fork := fork_le_of_chainSteps pre.chainSteps
  have below : a.fork ≤ fork := Nat.le_trans step.chainStep.fork_le
    (fork_le_of_chainSteps post.chainSteps)
  have sameFork : a.fork = fork := Fork.ctorIdx_injective (Nat.le_antisymm below above)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at flag
  obtain ⟨unslashedA, slashedB⟩ := flag
  have insideCounted : i < counted.validators.data.size :=
    Nat.lt_of_lt_of_le (Finset.mem_range.mp inside) post.registryLifecycle.size_le
  have unslashedSplit : (split.validators.data[i]?.map (·.slashed)).getD false = false := by
    cases found : split.validators.data[i]? with
    | none => rfl
    | some w =>
      cases flagged : w.slashed with
      | false => simp [flagged]
      | true =>
        obtain ⟨u, read, marked⟩ := pre.slashedPersistence i w found flagged
        simp [read, marked] at unslashedA
  have slashedCounted : (counted.validators.data[i]?.map (·.slashed)).getD false = true := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at slashedB
    | some w =>
      have marked : w.slashed = true := by simpa [found] using slashedB
      obtain ⟨u, read, kept⟩ := post.slashedPersistence i w found marked
      simp [read, kept]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr insideCounted, unslashedSplit,
    slashedCounted⟩, ?_⟩
  by_cases registered : i < pulled.validators.data.size
  · simp only [registered, ↓reduceIte, sameFork]
    exact Nat.div_le_div_right (registry step member i registered)
  · simp only [registered, ↓reduceIte, sameFork]
    exact created step member i (Nat.le_of_not_lt registered)
      (by simp [unslashedA, slashedB])

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that a step slashes with its exit unset is charged its effective balance before the step.

The slashing assigns its exit, so the step records a departure charge of that amount.

The charge of the run at the key is that one. -/
private theorem slash_exit_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (old new : Validator) (foundA : a.state.validators.data[i]? = some old)
    (foundB : b.state.validators.data[i]? = some new) (unset : old.exitEpoch = FAR_FUTURE_EPOCH)
    (slashed : new.slashed = true) :
    effectiveAt a i ≤
      ((tailC.departureCharges.find? fun c => c.index == i).map (·.amount)).getD 0 := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨pre, post, cut, -, -⟩ := Run.contains_step_facts member h.early
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have assigned : new.exitEpoch ≠ FAR_FUTURE_EPOCH :=
    run_slashed_exit_assigned (((shared.append fromFin).append pre).snoc step) h.genesis
      h.caps.activation h.caps.compounding bEarly h.delay i new foundB slashed
  have inStep : (⟨i, new.exitEpoch.toNat, old.effectiveBalance.toNat⟩ : DepartureCharge) ∈
      step.departureCharges := by
    apply List.mem_filterMap.mpr
    refine ⟨(old, i), ?_, ?_⟩
    · simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using foundA
    · simp [foundB, unset, assigned]
  have inRun : (⟨i, new.exitEpoch.toNat, old.effectiveBalance.toNat⟩ : DepartureCharge) ∈
      tailC.departureCharges := by
    rw [cut, Run.departureCharges_append]
    simp [Run.departureCharges, inStep]
  have found : (tailC.departureCharges.find? fun c => c.index == i).isSome = true :=
    List.find?_isSome.mpr ⟨_, inRun, beq_iff_eq.mpr rfl⟩
  obtain ⟨c, chosen⟩ := Option.isSome_iff_exists.mp found
  have selected := List.find?_some chosen
  have same := charge_unique tailC (List.mem_of_find?_eq_some chosen) inRun
    (beq_iff_eq.mp selected)
  subst same
  rw [chosen]
  simp [effectiveAt, foundA]

end Charge

end PinSum
end EthLib.Consensus.Models.Network
