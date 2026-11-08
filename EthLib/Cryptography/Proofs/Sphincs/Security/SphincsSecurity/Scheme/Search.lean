module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Lemmas

/-!
# Exhausting a search

The randomizer search and the counter search of the signer hash a sequence of distinct inputs.

Each search stops at the first answer that its test accepts.

This file bounds the probability that such a search exhausts all its trials.

The lazy random oracle answers an input outside its cache with a uniform draw.

So one trial rejects with probability the share of answers that the test rejects.

The trial caches its answer at an input that no later trial visits.

So each step of the induction keeps the later inputs fresh and adds one rejection factor.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace SphincsSecurity.Completeness

variable [Params]

variable {β γ : Type}

/-- A search: query the input of trial `t`, and stop at the first answer that the decoder accepts.

On acceptance it runs the success computation on the trial number and the decoded value.

Both searches of the signer have this shape. -/
def searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) : Nat → Nat → OracleComp HashSpec (Option γ)
  | 0, _ => pure none
  | n + 1, t => do
      let answer ← Concrete.oracleHash (inputs t)
      match decode answer with
      | some value => some <$> success t value
      | none => searchLoop inputs decode success n (t + 1)

/-- The share of answers that one trial rejects. -/
noncomputable def failMass (decode : HashOutput → Option β) : ℝ≥0∞ :=
  ((Finset.univ.filter fun u => decode u = none).card : ℝ≥0∞) / (Fintype.card HashOutput : ℝ≥0∞)

omit [Params] in
/-- The rejection share is the probability that one uniform answer is rejected. -/
theorem failMass_eq_probEvent (decode : HashOutput → Option β) :
    failMass decode = Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[decode u = none] :=
  (SampleableType.prEvent_uniformSample _).symm

omit [Params] in
/-- A query on an uncached input samples its answer uniformly. -/
theorem fresh_run (input : HashInput) (cache : QueryCache HashSpec) (hfresh : cache input = none)
    {δ : Type} (next : HashOutput × QueryCache HashSpec → ProbComp δ) (p : δ → Prop) :
    Pr{let x ← (randomOracle (spec := HashSpec) input).run cache >>= next}[p x]
      = ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹
          * Pr{let x ← next (u, cache.cacheQuery input u)}[p x] := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh]
  rw [show (uniformSampleImpl (spec := HashSpec) input) = ($ᵗ HashOutput : ProbComp HashOutput)
    from rfl, bind_map_left, OracleComp.prEvent_bind_eq_tsum]
  exact tsum_congr fun u => by rw [SampleableType.prEvent_uniformSample_eq_singleton]

omit [Params] in
/-- Let the inputs of the trials below `bound` be distinct.

Let the inputs of the trials from `t` to `bound - 1` be outside the cache.

If `t + n <= bound`, then `n` trials from `t` all fail with probability at most `rho^n`.

Here `rho` is the share of answers that one trial rejects.

The counter search meets these conditions with `bound = 2^32`, its number of trials. -/
theorem probEvent_searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) (bound : Nat)
    (hinj : ∀ s s', s < bound → s' < bound → inputs s = inputs s' → s = s') :
    ∀ (n t : Nat), t + n ≤ bound → ∀ cache : QueryCache HashSpec,
      (∀ s, t ≤ s → s < bound → cache (inputs s) = none) →
      Pr{let r ← (simulateQ randomOracle
          (searchLoop inputs decode success n t)).run cache}[r.1 = none]
        ≤ failMass decode ^ n := by
  intro n
  induction n with
  | zero => intro t _ cache _; simp [searchLoop]
  | succ n ih =>
      intro t hbound cache hfresh
      rw [searchLoop]
      simp only [Concrete.oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind]
      rw [fresh_run (inputs t) cache (hfresh t (Nat.le_refl t) (by omega))]
      have hterm : ∀ u : HashOutput,
          Pr{let r ← ((simulateQ randomOracle
              (match decode u with
                | some value => some <$> success t value
                | none => searchLoop inputs decode success n (t + 1))).run
              (cache.cacheQuery (inputs t) u))}[r.1 = none]
            ≤ (if decode u = none then failMass decode ^ n else 0) := by
        intro u
        cases hu : decode u with
        | some value =>
            simp only [reduceCtorEq, ite_false, simulateQ_map, StateT.run_map, prEvent_map]
            simp
        | none =>
            simp only [ite_true]
            refine ih (t + 1) (by omega) _ (fun s hs hsb => ?_)
            have hne : inputs s ≠ inputs t := fun hcon => by
              have hst := hinj s t hsb (by omega) hcon
              omega
            exact (QueryCache.cacheQuery_of_ne cache u hne).trans
              (hfresh s (Nat.le_of_succ_le hs) hsb)
      refine le_trans (ENNReal.tsum_le_tsum (fun u => mul_le_mul_right (hterm u) _)) ?_
      rw [tsum_fintype, Finset.sum_congr rfl (fun u _ => by rw [mul_ite, mul_zero]),
        Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        pow_succ', failMass, div_eq_mul_inv, ← mul_assoc]

end SphincsSecurity.Completeness
