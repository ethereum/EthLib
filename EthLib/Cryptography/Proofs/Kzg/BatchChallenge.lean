module

public import EthLib.Cryptography.Proofs.Kzg.BatchBinding
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Proofs: a random challenge is rarely a root of the error polynomial

The batch check hashes its openings to the challenge `r`.

With the hash as a random oracle, a query on new openings returns a uniform `r`.

The openings, and so the error polynomial, are fixed before that query.

A nonzero polynomial of degree at most `d` has at most `d` roots in `Fr`.

So a uniform `r` is a root with probability at most `d / |Fr|`.

For a batch of at most `n` openings, the degree is below `n`, so the bound is `(n - 1) / |Fr|`.

The game below draws one challenge after the adversary has chosen its openings.

It does not let the adversary query the oracle itself, so it bounds one attempt.

An adversary that tries `q` sets of openings gets `q` such chances, which this file does not state.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open OracleComp ENNReal Polynomial
open scoped EthLib.Cryptography.Bls.Fr

/-- The adversary chooses openings `x`, with error polynomial `errorPoly x`.

Then the challenge is drawn uniformly, as a random oracle answers a new query. -/
def batchRootExperiment {X : Type} (adversary : ProbComp X) : ProbComp (X × Fr) :=
  adversary >>= fun x => Prod.mk x <$> ($ᵗ Fr)

/-- A nonzero polynomial of degree at most `d` has at most `d` roots in `Fr`. -/
theorem card_roots_filter_le (P : Fr[X]) {d : Nat} (hd : P.natDegree ≤ d) [DecidablePred
    fun r : Fr => P ≠ 0 ∧ P.eval r = 0] :
    (Finset.univ.filter fun r : Fr => P ≠ 0 ∧ P.eval r = 0).card ≤ d := by
  classical
  by_cases hP : P = 0
  · simp [hP]
  calc (Finset.univ.filter fun r : Fr => P ≠ 0 ∧ P.eval r = 0).card
      ≤ P.roots.toFinset.card := Finset.card_le_card fun r hr => by
        simp only [Finset.mem_filter] at hr
        exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr hr.2.2)
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ d := hd

/-- **One challenge is a root with probability at most `d / |Fr|`.**

Let every error polynomial have degree at most `d`.

The event is that the polynomial of the openings is not zero, and has the challenge as a root.

Its probability is at most `d / r`, for the modulus `r` of `Fr`. -/
theorem prEvent_batchRoot_le {X : Type} (errorPoly : X → Fr[X]) (adversary : ProbComp X)
    {d : Nat} (hdeg : ∀ x, (errorPoly x).natDegree ≤ d) :
    Pr{let y ← batchRootExperiment adversary}[errorPoly y.1 ≠ 0 ∧ (errorPoly y.1).eval y.2 = 0] ≤
      d / Fr.modulus := by
  unfold batchRootExperiment
  refine prEvent_bind_le_of_forall_le adversary _ _ fun x => ?_
  classical
  rw [prEvent_map, SampleableType.prEvent_uniformSample, Fintype.card_fin]
  gcongr
  exact_mod_cast card_roots_filter_le (errorPoly x) (hdeg x)

/-- **The bound for batches of at most `n` openings.**

The adversary chooses the values and points of a batch.

It also chooses the scalars `c` and `w` that the commitments and proofs represent.

Then a uniform challenge is a root of a nonzero error polynomial.

Its probability is at most `(n - 1) / r`. -/
theorem prEvent_batchErrorPoly_root_le {X : Type} (τ : Fr) (c y w z : X → Nat → Fr)
    (size : X → Nat) {n : Nat} (hsize : ∀ x, size x ≤ n) (adversary : ProbComp X) :
    Pr{let p ← batchRootExperiment adversary}[
        batchErrorPoly τ (c p.1) (y p.1) (w p.1) (z p.1) (size p.1) ≠ 0 ∧
        (batchErrorPoly τ (c p.1) (y p.1) (w p.1) (z p.1) (size p.1)).eval p.2 = 0] ≤
      (n - 1 : Nat) / Fr.modulus :=
  prEvent_batchRoot_le (fun x => batchErrorPoly τ (c x) (y x) (w x) (z x) (size x)) adversary
    fun x => (natDegree_batchErrorPoly_le τ _ _ _ _ _).trans (Nat.sub_le_sub_right (hsize x) 1)

end EthLib.Cryptography.Kzg
