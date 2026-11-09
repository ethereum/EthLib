module

public import EthLib.Cryptography.Proofs.Kzg.BatchBinding
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# Proofs: a batch challenge from a random oracle is rarely a root of the error polynomial

The batch check hashes its openings to the challenge `r`.

Here the hash is a random oracle, and the adversary may query it.

It may hash many batches and keep one whose challenge is a root of its error polynomial.

A nonzero polynomial of degree at most `d` has at most `d` roots in `Fr`.

So each new query lands on a root with probability at most `d / |Fr|`.

The adversary makes at most `q` queries, and the verifier makes one more.

So the adversary wins with probability at most `(q + 1) d / |Fr|`.

For a batch of at most `n` openings, `d` is `n - 1`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open OracleComp OracleSpec ENNReal Polynomial
open scoped EthLib.Cryptography.Bls.Fr

/-- Uniform sampling of `Fr`, through its `r` elements. -/
noncomputable instance : SampleableType Fr :=
  SampleableType.ofEquiv (Fintype.equivFinOfCardEq Bls.Fr.card_eq).symm

/-- The game of the batch challenge, with the hash as an oracle from batches `X` to `Fr`.

The adversary queries the oracle as it likes, then outputs a batch.

The verifier hashes that batch to its challenge. -/
def batchRomExperiment {X : Type} (adversary : OracleComp (X →ₒ Fr) X) :
    OracleComp (X →ₒ Fr) (X × Fr) := do
  let x ← adversary
  let r ← liftM ((X →ₒ Fr).query x)
  return (x, r)

/-- An injective map into an integral domain preserves the bound on polynomial roots. -/
theorem card_roots_embedding_le {R : Type*} [CommRing R] [IsDomain R]
    (embed : Fr ↪ R) (P : R[X]) {d : Nat} (hd : P.natDegree ≤ d)
    [DecidablePred fun r : Fr => P ≠ 0 ∧ P.eval (embed r) = 0] :
    (Finset.univ.filter fun r : Fr => P ≠ 0 ∧ P.eval (embed r) = 0).card ≤ d := by
  classical
  by_cases hP : P = 0
  · simp [hP]
  let roots := Finset.univ.filter fun r : Fr => P ≠ 0 ∧ P.eval (embed r) = 0
  have hroots : roots.map embed ⊆ P.roots.toFinset := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hr
    exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (Finset.mem_filter.mp hx).2.2)
  calc roots.card = (roots.map embed).card := by simp
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ d := hd

/-- Uniform field elements hit roots along an embedding with probability at most `d / |Fr|`. -/
theorem prEvent_uniform_embedding_root_le {R : Type*} [CommRing R] [IsDomain R]
    (embed : Fr ↪ R) (P : R[X]) {d : Nat} (hd : P.natDegree ≤ d) :
    Pr{let r ← $ᵗ Fr}[P ≠ 0 ∧ P.eval (embed r) = 0] ≤ d / Fr.modulus := by
  classical
  rw [SampleableType.prEvent_uniformSample, Bls.Fr.card_eq]
  gcongr
  exact_mod_cast card_roots_embedding_le embed P hd

/-- A nonzero polynomial of degree at most `d` has at most `d` roots in `Fr`. -/
theorem card_roots_filter_le (P : Fr[X]) {d : Nat} (hd : P.natDegree ≤ d) [DecidablePred
    fun r : Fr => P ≠ 0 ∧ P.eval r = 0] :
    (Finset.univ.filter fun r : Fr => P ≠ 0 ∧ P.eval r = 0).card ≤ d :=
  card_roots_embedding_le (Function.Embedding.refl Fr) P hd

/-- **The adversary of `q` queries wins with probability at most `(q + 1) d / r`.**

The hash is a lazily sampled random oracle.

Each admissible batch has an error polynomial of degree at most `d`.

The adversary wins when its batch is admissible, and its error polynomial is not zero.

It must also have the challenge of the batch as a root.

The bound counts the `q` queries of the adversary and the one of the verifier. -/
theorem prEvent_batchRomRoot_le {X : Type} [DecidableEq X] (errorPoly : X → Fr[X])
    (admissible : X → Prop) {d : Nat} (hdeg : ∀ x, admissible x → (errorPoly x).natDegree ≤ d)
    (adversary : OracleComp (X →ₒ Fr) X) {q : Nat} (hq : IsTotalQueryBound adversary q) :
    Pr{let p ← (simulateQ randomOracle (batchRomExperiment adversary)).run' ∅}[
        admissible p.1 ∧ errorPoly p.1 ≠ 0 ∧ (errorPoly p.1).eval p.2 = 0] ≤
      (q + 1) * (d / Fr.modulus) := by
  have hbound : IsTotalQueryBound (batchRomExperiment adversary) (q + 1) :=
    isTotalQueryBound_bind hq fun _ =>
      isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ => trivial⟩
  have h := prEvent_randomOracle_le_of_bad_queries (batchRomExperiment adversary) (q + 1) hbound
    (fun p => admissible p.1 ∧ errorPoly p.1 ≠ 0 ∧ (errorPoly p.1).eval p.2 = 0)
    (fun x g => admissible x ∧ errorPoly x ≠ 0 ∧ (errorPoly x).eval (g x) = 0)
    (d / Fr.modulus) ?_ ?_
  · simpa using h
  · -- A new query is uniform, so it is a root with probability at most `d / r`.
    intro x g
    classical
    simp only [Function.update_self]
    by_cases ha : admissible x
    · calc _ ≤ Pr{let u ← $ᵗ Fr}[errorPoly x ≠ 0 ∧ (errorPoly x).eval u = 0] :=
            prEvent_mono _ _ _ fun _ h => h.2
        _ ≤ _ := prEvent_uniform_embedding_root_le (Function.Embedding.refl Fr)
          (errorPoly x) (hdeg x ha)
    · simp only [ha, false_and, prEvent_false]
      exact zero_le
  · -- A winning batch is the last query of the game.
    intro g hev
    refine ⟨⟨evalWithAnswerFn (QueryImpl.ofFn g) adversary, g _⟩, ?_, ?_⟩
    · rw [batchRomExperiment, tableQueryLog_bind, tableQueryLog_query_bind]
      simp
    · simpa [batchRomExperiment, evalWithAnswerFn_bind] using hev

/-- The inputs of the hash of a batch of openings. -/
structure OpeningBatch where
  commitments : Array KZGCommitment
  zs : Array Fr
  ys : Array Fr
  proofs : Array KZGProof
deriving DecidableEq

/-- **The bound for batches of at most `n` openings.**

The hash of the batch check is a random oracle on its inputs.

In a batch `x`, let commitment `i` represent `c x i`, and proof `i` represent `w x i`.

The adversary makes `q` queries, then outputs a batch of at most `n` openings.

The event is that the challenge of that batch is a root of its error polynomial, which is not zero.

Its probability is at most `(q + 1) (n - 1) / r`. -/
theorem prEvent_batchErrorPoly_root_le (τ : Fr) (c w : OpeningBatch → Nat → Fr) {n : Nat}
    (adversary : OracleComp (OpeningBatch →ₒ Fr) OpeningBatch) {q : Nat}
    (hq : IsTotalQueryBound adversary q) :
    Pr{let p ← (simulateQ randomOracle (batchRomExperiment adversary)).run' ∅}[
        p.1.commitments.size ≤ n ∧
        batchErrorPoly τ (c p.1) (p.1.ys[·]!) (w p.1) (p.1.zs[·]!) p.1.commitments.size ≠ 0 ∧
        (batchErrorPoly τ (c p.1) (p.1.ys[·]!) (w p.1) (p.1.zs[·]!)
          p.1.commitments.size).eval p.2 = 0] ≤
      (q + 1) * ((n - 1 : Nat) / Fr.modulus) :=
  prEvent_batchRomRoot_le
    (fun x => batchErrorPoly τ (c x) (x.ys[·]!) (w x) (x.zs[·]!) x.commitments.size)
    (fun x => x.commitments.size ≤ n)
    (fun _ hx => (natDegree_batchErrorPoly_le τ _ _ _ _ _).trans (Nat.sub_le_sub_right hx 1))
    adversary hq

end EthLib.Cryptography.Kzg
