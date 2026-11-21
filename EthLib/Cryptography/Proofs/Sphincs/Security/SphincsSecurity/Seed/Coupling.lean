module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Seed.Model
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Statement
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.Prelude
public import EthLib.Cryptography.Proofs.HashSig.ProgrammedTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Preparing the derivation table

Preparation queries the input of `PK.seed` first.

It then queries the derivation of every secret at the public seed that the first answer gives.

It queries the input of `SK.prf` last, in the order in which uniform material is drawn.

In the random oracle model, its answers and final cache come from uniform material.

Take a computation that runs from an empty cache.

It has the same output distribution when it runs from the cache programmed with uniform material.

So the master seed can be sampled after the material, also when the hash queries are counted.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SphincsSecurity.Security.SeedCoupling

export EthLib.Cryptography.HashSig (evalDist_independent_uniform_pair)

variable [Params]
open SeedModel Completeness
open EthLib.Cryptography.HashSig
  (cacheFin cacheTable cacheTable_apply cacheTable_apply_of_not_mem queryTable
    evalDist_queryTable_fresh)

-- For this section: its last proof unifies `ℕ` with `Multiplicative ℕ`, the counted cost type.
set_option backward.isDefEq.respectTransparency false

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- The input of the derivation of each secret, at the public seed of the given parameter output.

The inputs are fixed once the parameter output is, whatever the answers at them. -/
def derivationInputs (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) : HashInput :=
  keygenHashInput (truncateHash parameterOutput) (secretDomain position) seed

theorem derivationInputs_injective (seed : MasterSeed) (parameterOutput : HashOutput) :
    Function.Injective (derivationInputs seed parameterOutput) := by
  intro left right h
  exact secretDomain_injective (keygenInput_injective h).2.1

theorem derivationInputs_ne_parameter (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) :
    derivationInputs seed parameterOutput position ≠ parameterInput seed :=
  fun h => keySeedInput_ne_keygenHashInput seed seed 0 _ _ h.symm

theorem derivationInputs_ne_prf (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) : derivationInputs seed parameterOutput position ≠ prfInput seed :=
  fun h => keySeedInput_ne_keygenHashInput seed seed 1 _ _ h.symm

/-- Write the parameter output, the values of the secrets and then `SK.prf` into a cache.

The result is the programmed cache. -/
theorem cacheTable_eq_programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) :
    (cacheTable (base.cacheQuery (parameterInput seed) (parameterOutput material))
      (derivationInputs seed (parameterOutput material)) material.2).cacheQuery (prfInput seed)
        (prf material) =
      programCache base seed material := by
  classical
  refine QueryCache.ext fun input => ?_
  by_cases hprf : input = prfInput seed
  · subst input
    rw [QueryCache.cacheQuery_self, programCache_prf]
  rw [QueryCache.cacheQuery_of_ne _ _ hprf]
  by_cases hp : input = parameterInput seed
  · subst input
    rw [cacheTable_apply_of_not_mem _ _ _ _
      (fun position =>
        (derivationInputs_ne_parameter seed (parameterOutput material) position).symm)]
    rw [QueryCache.cacheQuery_self, programCache_parameter]
  · by_cases hs : ∃ position, input = derivationInputs seed (parameterOutput material) position
    · obtain ⟨position, rfl⟩ := hs
      rw [cacheTable_apply _ _ (derivationInputs_injective seed (parameterOutput material))]
      exact (programCache_secret base seed material position).symm
    · rw [cacheTable_apply_of_not_mem _ _ _ _ (by simpa only [not_exists] using hs),
        QueryCache.cacheQuery_of_ne _ _ hp, programCache_other _ _ _ _ hp hprf]
      intro position heq
      exact hs ⟨position, heq⟩

/-- Query the input of `PK.seed`, then the derivation of every secret at that public seed.

Then query the input of `SK.prf`: this is the order in which uniform material is drawn. -/
noncomputable def prepareTable (seed : MasterSeed) : OracleComp HashSpec Material := do
  let parameterOutput ← liftM (HashSpec.query (parameterInput seed))
  let outputs ← queryTable (derivationInputs seed parameterOutput)
  let prf ← liftM (HashSpec.query (prfInput seed))
  return ((parameterOutput, prf), outputs)

attribute [local irreducible] cacheTable cacheFin programCache

/-- From an empty cache, preparation returns uniform material.

Its final cache is the empty cache programmed with that material. -/
theorem evalDist_prepareTable (seed : MasterSeed) :
    (simulateQ randomOracle (prepareTable seed)).run ∅ =ᵈ
      (fun material => (material, programCache ∅ seed material)) <$> sampleMaterial := by
  unfold prepareTable
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [QueryImpl.withCaching_run_none _ (by rfl)]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp,
    sampleMaterial, map_bind]
  apply EvalDistEq.bind_right
  intro parameterOutput
  have hfresh : ∀ position, ((∅ : QueryCache HashSpec).cacheQuery
      (parameterInput seed) parameterOutput) (derivationInputs seed parameterOutput position) =
        none := by
    intro position
    rw [QueryCache.cacheQuery_of_ne _ _
      (derivationInputs_ne_parameter seed parameterOutput position)]
    rfl
  have htable := evalDist_queryTable_fresh (R := HashOutput)
    (derivationInputs seed parameterOutput) (derivationInputs_injective seed parameterOutput)
    ((∅ : QueryCache HashSpec).cacheQuery (parameterInput seed) parameterOutput) hfresh
  refine (htable.bind_left _).trans ?_
  rw [bind_map_left]
  apply EvalDistEq.bind_right
  intro outputs
  have hprf : (cacheTable ((∅ : QueryCache HashSpec).cacheQuery (parameterInput seed)
      parameterOutput) (derivationInputs seed parameterOutput) outputs) (prfInput seed) = none := by
    rw [cacheTable_apply_of_not_mem _ _ _ _
      (fun position => (derivationInputs_ne_prf seed parameterOutput position).symm),
      QueryCache.cacheQuery_of_ne _ _ (prfInput_ne_parameterInput seed)]
    rfl
  dsimp only
  rw [QueryImpl.withCaching_run_none _ hprf]
  simp only [Functor.map_map]
  have hfun : ∀ prf : HashOutput,
      (((parameterOutput, prf), outputs), (cacheTable
        ((∅ : QueryCache HashSpec).cacheQuery (parameterInput seed) parameterOutput)
        (derivationInputs seed parameterOutput) outputs).cacheQuery (prfInput seed) prf) =
      (((parameterOutput, prf), outputs), programCache ∅ seed ((parameterOutput, prf), outputs)) :=
    fun prf => congrArg
      (fun cache : QueryCache HashSpec => (((parameterOutput, prf), outputs), cache))
      (cacheTable_eq_programCache (∅ : QueryCache HashSpec) seed ((parameterOutput, prf), outputs))
  simp only [hfun]
  rfl

omit [Params] in
/-- Run a preparation first, then the computation from the cache that the preparation leaves.

This does not change the output distribution of the computation. -/
theorem evalDist_presample_computation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl computation).run' cache =ᵈ
      ((simulateQ romImpl preparation).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2) :=
  EthLib.Cryptography.HashSig.evalDist_presample_computation computation preparation cache

/-- Fix a seed, and take a computation that runs from an empty cache.

It has the same output distribution when it runs from the cache programmed with uniform material.

The computation may use the seed, and the programmed cache holds the entries that name it. -/
theorem evalDist_prepared_continuation {α : Type} (computation : OracleComp OracleWorld α)
    (seed : MasterSeed) :
    (simulateQ romImpl computation).run' ∅ =ᵈ
      (sampleMaterial >>= fun material =>
        (simulateQ romImpl computation).run' (programCache ∅ seed material)) := by
  refine (evalDist_presample_computation computation
    (liftM (prepareTable seed) : OracleComp OracleWorld Material) ∅).trans ?_
  rw [simulate_lift_hash]
  refine ((evalDist_prepareTable seed).bind_left _).trans ?_
  rw [bind_map_left]

/-- The computation, paired with the number of its hash queries.

Queries with a cached answer count, and uniform draws do not. -/
noncomputable def countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  QueryCap.counted (fun input : OracleWorld.Domain => input matches .inr _) computation

omit [Params] in
theorem simulateQ_countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    simulateQ romImpl (countHashQueries computation) =
      (simulateQ countedOracle computation).run := by
  rw [countHashQueries, QueryCap.simulate_withCost, countedOracle, Completeness.romImpl]
  congr 3
  funext input
  cases input <;> rfl

/-- Sample the seed and run from an empty cache.

This has the same output distribution as sampling the material and then the seed.

The second experiment runs from the programmed cache. -/
theorem evalDist_seeded_prepared {α : Type} (next : MasterSeed → OracleComp OracleWorld α) :
    (simulateQ romImpl
      ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run' ∅ =ᵈ
      (sampleMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
        (simulateQ romImpl (next seed)).run' (programCache ∅ seed material)) := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_lift_prob,
    bind_map_left, map_bind]
  refine EvalDistEq.trans
    (my := (sampleMasterSeed >>= fun seed => sampleMaterial >>= fun material =>
      (simulateQ romImpl (next seed)).run' (programCache ∅ seed material))) ?_ ?_
  · apply EvalDistEq.bind_right
    intro seed
    exact evalDist_prepared_continuation (next seed) seed
  · exact EvalDistEq.bind_bind_swap _ _ _

omit [Params] in
theorem countHashQueries_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    countHashQueries (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← countHashQueries (next answer)
      pure (result.1,
        (if (fun query : OracleWorld.Domain => query matches .inr _) input then 1 else 0) +
          result.2)) := rfl

omit [Params] in
theorem countHashQueries_lift_prob {α : Type} (computation : ProbComp α) :
    countHashQueries (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, 0)) <$> (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind]
      change countHashQueries (liftM (OracleWorld.query (.inl input)) >>= _) = _
      simp only [countHashQueries_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      rfl

omit [Params] in
theorem countHashQueries_sampling_bind {α β : Type} (sampling : ProbComp α)
    (next : α → OracleComp OracleWorld β) :
    countHashQueries ((liftM sampling : OracleComp OracleWorld α) >>= next) =
      (liftM sampling : OracleComp OracleWorld α) >>= fun value =>
        countHashQueries (next value) := by
  rw [countHashQueries, QueryCap.counted_bind]
  change (countHashQueries (liftM sampling : OracleComp OracleWorld α) >>= _) = _
  rw [countHashQueries_lift_prob, bind_map_left]
  simp only [Nat.zero_add, Prod.mk.eta, bind_pure]
  rfl

/-- The seed can be sampled after the material also when the hash queries are counted. -/
theorem evalDist_seeded_prepared_counted {α : Type}
    (next : MasterSeed → OracleComp OracleWorld α) :
    (simulateQ countedOracle
      ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run.run' ∅ =ᵈ
      (sampleMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
        (simulateQ countedOracle (next seed)).run.run' (programCache ∅ seed material)) := by
  rw [← simulateQ_countHashQueries, countHashQueries_sampling_bind]
  simpa only [simulateQ_countHashQueries] using
    evalDist_seeded_prepared (fun seed => countHashQueries (next seed))

end SphincsSecurity.Security.SeedCoupling
