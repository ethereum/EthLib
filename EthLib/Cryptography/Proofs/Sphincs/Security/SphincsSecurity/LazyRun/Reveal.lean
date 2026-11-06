module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Uniform
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.Prelude

/-!
# Revealing and guessing hidden coordinates

A table of independent uniform digest coordinates is hidden, and a run reveals some of them.

The revealed coordinates form a knowledge cache, and the completion samples the others uniformly.

Revealing a coordinate commutes with the completion.

A guess at a coordinate that is still hidden is right with probability exactly `2^-128`.

The completion samples the hidden coordinates afresh, so no result conditions on failed guesses.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security.HiddenReveal

variable [Params]
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq ι
noncomputable local instance tableSampleable : SampleableType (ι → Digest) :=
    SampleableType.ofFintype _

abbrev Knowledge (ι : Type) := QueryCache (ι →ₒ Digest)
abbrev ViewSpec (ι : Type) := unifSpec + ((ι →ₒ Digest) + ((ι × Digest) →ₒ Unit))

/-- A uniform table that agrees with the knowledge cache on the revealed coordinates. -/
noncomputable def completion (known : Knowledge ι) : ProbComp (ι → Digest) :=
  tableExtending known <$> ($ᵗ (ι → Digest) : ProbComp (ι → Digest))

omit [Fintype ι] in
omit [Params] in
theorem completion_known (known : Knowledge ι) (coordinate : ι) (value : Digest)
    (hknown : known coordinate = some value) (table : ι → Digest) :
    tableExtending known table coordinate = value := by simp [tableExtending, hknown]

omit [Params] in
/-- Revealing a coordinate commutes with the completion of the table.

The continuation may read the revealed value and the whole completed table. -/
theorem completion_reveal {α : Type} (known : Knowledge ι) (coordinate : ι)
    (next : Digest → (ι → Digest) → ProbComp α) :
    (completion known >>= fun table => next (table coordinate) table) =ᵈ
      (do
        let (value, known') ← (randomOracle (spec := ι →ₒ Digest) coordinate).run known
        completion known' >>= next value) := by
  cases hc : known coordinate with
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
      simp only [completion, bind_map_left, completion_known known coordinate value hc]
      rfl
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      simp only [completion, bind_map_left]
      refine (FiniteGraphSampling.evalDist_table_extract (Answer := Digest) coordinate
        (fun table _ => next (tableExtending known table coordinate)
          (tableExtending known table))).trans ?_
      refine EvalDistEq.bind_right _ fun value => EvalDistEq.bind_right _ fun table => ?_
      have heq : tableExtending known (Function.update table coordinate value) =
          tableExtending (known.cacheQuery coordinate value) table := by
        rw [tableExtending_cacheQuery, tableExtending_update_of_none known table hc]
      simp only [heq, tableExtending, hc, Function.update_self, Option.getD_none]
      rfl

omit [Params] in
/-- A guess at a coordinate that is still hidden is right with probability exactly `2^-128`. -/
theorem completion_guess (known : Knowledge ι) (coordinate : ι) (value : Digest)
    (hunknown : known coordinate = none) :
    Pr{let table ← completion known}[table coordinate = value] = 1 / (2 : ℝ≥0∞) ^ 128 := by
  rw [completion, prEvent_map]
  change Pr{let table ← ($ᵗ (ι → Digest) : ProbComp (ι → Digest))}[
    (known coordinate).getD (table coordinate) = value] = _
  simp only [hunknown, Option.getD_none]
  have hdist : (do let table ← ($ᵗ (ι → Digest) : ProbComp (ι → Digest)); pure (table coordinate))
      =ᵈ ($ᵗ Digest : ProbComp Digest) := by
    refine (FiniteGraphSampling.evalDist_table_extract (Answer := Digest) coordinate
      (fun _ answer => (pure answer : ProbComp Digest))).trans ?_
    refine (EvalDistEq.bind_right _ fun answer => OracleComp.EvalDistEq.bind_const _ _).trans ?_
    rw [bind_pure]
  have h := hdist.prEvent_eq (· = value)
  simp only [bind_pure_comp, prEvent_map] at h
  rw [h, SampleableType.prEvent_uniformSample_eq_singleton,
    show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat, one_div]

/-- The run of a computation that reveals and guesses coordinates of a fixed table.

It stops at a right guess at a coordinate that is still hidden. -/
noncomputable def run {α : Type} (table : ι → Digest) (computation : OracleComp (ViewSpec ι) α) :
    Knowledge ι → ProbComp (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun input _ next known =>
      match input with
      | .inl draw => do
          let value ← liftM (unifSpec.query draw)
          next value known
      | .inr (.inl coordinate) =>
          next (table coordinate) (known.cacheQuery coordinate (table coordinate))
      | .inr (.inr guess) =>
          if known guess.1 = none ∧ table guess.1 = guess.2 then pure none
          else next () known) computation

omit [Fintype ι] in
omit [Params] in
theorem run_pure {α : Type} (table : ι → Digest) (value : α) (known : Knowledge ι) :
    run table (pure value) known = pure (some value) := rfl

end SphincsSecurity.Security.HiddenReveal
