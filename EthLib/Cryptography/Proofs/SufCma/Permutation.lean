module

public import EthLib.Cryptography.Proofs.SufCma
public import EthLib.Cryptography.Proofs.LazyPermutation

/-!
# Proofs: the strong-unforgeability game in the random-permutation model

The oracles are coins, a permutation `π` of a finite set and its inverse.

The model samples `π` lazily, from the empty cache, and passes coins through.

A run in this model has the output law of a run against a uniform permutation drawn first.

The permutation is the bijective random oracle of [Fersch, Kiltz, Poettering, CCS 2016][fkp], §4.

[fkp]: https://doi.org/10.1145/2976749.2978413
-/

@[expose] public section

namespace EthLib.Cryptography.SufCma

open OracleComp OracleSpec ENNReal LazyPermutation

/-- **The random-permutation model** of a finite set `A`.

Coins pass through, and `π` and `π⁻¹` are sampled one answer at a time from the empty cache. -/
noncomputable def randomPermutationModel (A : Type) [FinEnum A] : Model (PermSpec A) where
  State := PermCache A
  setup := pure []
  handler := lazyPermImpl

variable {A : Type} [FinEnum A]

/-- In the random-permutation model, a run is the lazy run from the empty cache. -/
theorem runIn_randomPermutationModel {α : Type} (oa : OracleComp (unifSpec + PermSpec A) α) :
    runIn (randomPermutationModel A) oa = (simulateQ lazyPermImpl oa).run' [] :=
  pure_bind _ _

/-- In the random-permutation model, a counted run is the counted lazy run from the empty cache. -/
theorem countedRunIn_randomPermutationModel {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) :
    countedRunIn (randomPermutationModel A) oa =
      (simulateQ (lazyPermImpl.withAddCost hashCost) oa).run.run' [] :=
  pure_bind _ _

/-- **A run in the random-permutation model is a run against a uniform permutation.** -/
theorem runIn_randomPermutationModel_evalDistEq {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) :
    runIn (randomPermutationModel A) oa =ᵈ
      ($ᵗ (Equiv.Perm A) >>= fun π => simulateQ (permImpl π) oa) := by
  rw [runIn_randomPermutationModel]
  exact (uniformSample_bind_simulateQ_permImpl_evalDistEq oa).symm

/-- An event has the same probability in the model as against a uniform permutation drawn first. -/
theorem prEvent_runIn_randomPermutationModel {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) (P : α → Prop) :
    Pr{let x ← runIn (randomPermutationModel A) oa}[P x] =
      Pr{let π ← $ᵗ (Equiv.Perm A); let x ← simulateQ (permImpl π) oa}[P x] :=
  ((runIn_randomPermutationModel_evalDistEq oa).prEvent_eq P).trans (by
    simp only [QueryImpl.passthrough_add, PFunctor.Handler.liftTarget_self, map_bind])

end EthLib.Cryptography.SufCma
