module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame

/-!
# Proofs: the lazy ECDSA game over the joint state of its two caches

The lazy game keeps two caches.

The signing oracle keeps its answers, and the permutation oracle keeps the pairs of `Π`.

A signer that only asks for `Π` cannot set it.

Theorem 1 of the source needs one that does: it signs without the key and sets `Π` to match.

So here every oracle of the lazy game reads and writes both caches at once.

The signer is a parameter, which may change the cache of `Π` as it likes.

A signer that breaks the partial bijection of that cache leaves the model of a permutation.

With the real signer, run against the lazy permutation, this is the lazy game.

The run also returns the forgery and both final caches.

Draw `Π` at the end, uniform among the permutations that agree with its final cache.

Then the forgery, the result, the signing cache and `Π` have the joint law of the game.

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

The signer that sets `Π` is the one of their Theorem 1, in its games G2 and G3.

The joint state is the challenger's side of those games.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- The joint state: the answers of the signing oracle, and the pairs of `Π` answered so far. -/
abbrev JointState (F A M : Type) := Cache F M × PermCache A

/-- A signing oracle that reads and writes both caches. -/
abbrev JointSigner (F A M : Type) := M → StateT (JointState F A M) ProbComp (Option (F × F))

/-- The oracles of the game over the joint state, with a signing oracle.

Coins leave both caches unchanged.

`Π` and its inverse are the lazy permutation on the second cache.

They leave the signing cache unchanged. -/
def jointImpl [FinEnum A] (signer : JointSigner F A M) :
    QueryImpl (Spec F A M) (StateT (JointState F A M) ProbComp)
  | .inl n => fun s => (·, s) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl α) => fun s =>
    (fun z => (z.1, (s.1, z.2))) <$> (lazyPermOracle (.inl α)).run s.2
  | .inr (.inr (.inl β)) => fun s =>
    (fun z => (z.1, (s.1, z.2))) <$> (lazyPermOracle (.inr β)).run s.2
  | .inr (.inr (.inr m)) => signer m

/-- A signing oracle that asks the permutation oracle, run against the lazy permutation.

It reads and writes the cache of `Π` only through its queries. -/
def liftSigner [FinEnum A] (signer : SignerQ F A M) : JointSigner F A M := fun m s =>
  (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ lazyPermImpl ((signer m).run s.1)).run s.2

/-- Take a signer that asks for `Π`, and run its oracles against the lazy permutation.

Those are the joint oracles with that signer lifted to the joint state. -/
theorem flattenStateT_mapStateTBase_implQ [FinEnum A] (signer : SignerQ F A M) :
    (lazyPermImpl.mapStateTBase (implQ signer)).flattenStateT =
      jointImpl (liftSigner signer) := by
  funext q
  refine StateT.ext fun s => ?_
  rcases q with n | α | β | m
  · change (fun y => (y.1.1, (y.1.2, y.2))) <$> (simulateQ lazyPermImpl
        ((·, s.1) <$> query (spec := unifSpec + PermSpec A) (.inl n))).run s.2 =
      (·, s) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
    simp [Functor.map_map, lazyPermImpl]
  · change (fun y => (y.1.1, (y.1.2, y.2))) <$> (simulateQ lazyPermImpl
        ((·, s.1) <$> query (spec := unifSpec + PermSpec A) (.inr (.inl α)))).run s.2 =
      (fun z => (z.1, (s.1, z.2))) <$> (lazyPermOracle (.inl α)).run s.2
    simp [Functor.map_map, lazyPermImpl]
  · change (fun y => (y.1.1, (y.1.2, y.2))) <$> (simulateQ lazyPermImpl
        ((·, s.1) <$> query (spec := unifSpec + PermSpec A) (.inr (.inr β)))).run s.2 =
      (fun z => (z.1, (s.1, z.2))) <$> (lazyPermOracle (.inr β)).run s.2
    simp [Functor.map_map, lazyPermImpl]
  · rfl

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Run the adversary on the key `X` with a signing oracle, and check its forgery.

It keeps the forgery, the result and the final signing cache. -/
def runCacheQ [DecidableEq M] (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (signer : SignerQ F A M) : PermComp A ((M × F × F) × Bool × Cache F M) := do
  let ((m, t, s), cache) ← (simulateQ (implQ signer) (adversary.main X)).run []
  if signed cache m then return ((m, t, s), false, cache) else
    (((m, t, s), ·, cache)) <$> verifyQ scheme X m t s

/-- The run that keeps the forgery and the signing cache, keeping only the result, is the run. -/
theorem result_map_runCacheQ [DecidableEq M] (scheme : Scheme F G A M)
    (adversary : Adversary F G A M) (X : G) (signer : SignerQ F A M) :
    (fun z => z.2.1) <$> runCacheQ scheme adversary X signer = runQ scheme adversary X signer := by
  simp only [runCacheQ, runQ, map_bind]
  refine bind_congr fun z => ?_
  split_ifs <;> simp

variable [FinEnum A]

/-- Run the adversary on the key `X` over the joint state, and check its forgery.

Both caches start empty.

The check asks the lazy permutation for `Π` on the second cache, once or never.

It returns the forgery, the result and both final caches. -/
def jointRun [DecidableEq M] (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (signer : JointSigner F A M) : ProbComp ((M × F × F) × Bool × JointState F A M) := do
  let ((m, t, s), (cache, perm)) ← (simulateQ (jointImpl signer) (adversary.main X)).run ([], [])
  if signed cache m then return ((m, t, s), false, (cache, perm)) else
    (fun z => ((m, t, s), z.1, (cache, z.2))) <$>
      (simulateQ lazyPermImpl (verifyQ scheme X m t s)).run perm

variable [SampleableType F] [DecidableEq M]

/-- The lazy game over the joint state: draw the key, then run with the real signer.

It returns the forgery, the result and both final caches. -/
def jointExperiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp ((M × F × F) × Bool × JointState F A M) := do
  let x ← $ᵗ F
  jointRun scheme adversary (x • scheme.g) (liftSigner (signQ scheme fuel x))

/-- The game, keeping the forgery, the result, the final signing cache and the permutation `Π`. -/
def experimentView (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp ((M × F × F) × Bool × Cache F M × Equiv.Perm A) := do
  let π ← $ᵗ (Equiv.Perm A)
  let x ← $ᵗ F
  let X := x • scheme.g
  let ((m, t, s), cache) ← (simulateQ (impl scheme fuel π x) (adversary.main X)).run []
  return ((m, t, s), !signed cache m && verify scheme π X m t s, cache, π)

/-- The game that also returns the forgery, its signing cache and `Π` is the game.

That holds once all but the result is dropped. -/
theorem result_map_experimentView (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    (fun z => z.2.1) <$> experimentView scheme fuel adversary =
      experiment scheme fuel adversary := by
  simp [experimentView, experiment]

omit [SampleableType F] in
/-- Run against the lazy permutation from the empty cache, keeping the forgery and signing cache.

That is the joint run with the signer lifted. -/
theorem simulateQ_lazyPermImpl_runCacheQ (scheme : Scheme F G A M)
    (adversary : Adversary F G A M) (X : G) (signer : SignerQ F A M) :
    (simulateQ lazyPermImpl (runCacheQ scheme adversary X signer)).run [] =
      (fun z => ((z.1, z.2.1, z.2.2.1), z.2.2.2)) <$>
        jointRun scheme adversary X (liftSigner signer) := by
  simp only [runCacheQ, jointRun, simulateQ_bind, StateT.run_bind,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, flattenStateT_mapStateTBase_implQ,
    bind_map_left, map_bind]
  refine bind_congr fun z => ?_
  obtain ⟨⟨m, t, s⟩, cache, perm⟩ := z
  by_cases h : signed cache m
  · simp [h]
  · simp [h]

/-- The lazy game is the joint game, keeping only the result. -/
theorem lazyExperiment_eq_result_map_jointExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    lazyExperiment scheme fuel adversary =
      (fun z => z.2.1) <$> jointExperiment scheme fuel adversary := by
  simp only [lazyExperiment, experimentQ, jointExperiment, StateT.run'_eq, simulateQ_bind,
    StateT.run_bind, simulateQ_lazyPermImpl_liftM_run, bind_map_left, map_bind]
  refine bind_congr fun x => ?_
  rw [← result_map_runCacheQ, simulateQ_map, StateT.run_map, simulateQ_lazyPermImpl_runCacheQ]
  simp [Functor.map_map]

/-- The game with its forgery, signing cache and `Π` has the law of the joint game.

The joint game draws `Π` at the end, from its final cache of `Π`.

It draws it uniformly among the permutations that agree with that cache. -/
theorem experimentView_evalDistEq_jointExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    experimentView scheme fuel adversary =ᵈ
      (do
        let (σ, b, cache, perm) ← jointExperiment scheme fuel adversary
        let π ← uniformExtension perm
        pure (σ, b, cache, π)) := by
  let oa : PermComp A ((M × F × F) × Bool × Cache F M) := do
    let x ← ($ᵗ F : ProbComp F)
    runCacheQ scheme adversary (x • scheme.g) (signQ scheme fuel x)
  have heager : experimentView scheme fuel adversary = (do
      let π ← $ᵗ (Equiv.Perm A)
      let z ← simulateQ (permImpl π) oa
      pure (z.1, z.2.1, z.2.2, π)) := by
    simp only [experimentView, oa, simulateQ_bind, simulateQ_permImpl_liftM, bind_assoc]
    refine bind_congr fun π => bind_congr fun x => ?_
    simp only [runCacheQ, simulateQ_bind, bind_assoc]
    rw [simulateQ_StateT_compose (implQ (signQ scheme fuel x)) (permImpl π) (impl scheme fuel π x)
      (simulateQ_permImpl_implQ scheme fuel π x)]
    refine bind_congr fun z => ?_
    obtain ⟨⟨m, t, s⟩, cache⟩ := z
    by_cases h : signed cache m
    · simp [h]
    · have hv := simulateQ_permImpl_verifyQ scheme π (x • scheme.g) m t s
      simp only [h, Bool.false_eq_true, ite_false, simulateQ_map, hv]
      simp
  have hlazy : (simulateQ lazyPermImpl oa).run [] =
      (fun z => ((z.1, z.2.1, z.2.2.1), z.2.2.2)) <$> jointExperiment scheme fuel adversary := by
    simp only [oa, jointExperiment, simulateQ_bind, StateT.run_bind,
      simulateQ_lazyPermImpl_liftM_run, bind_map_left, map_bind, simulateQ_lazyPermImpl_runCacheQ]
  rw [heager]
  refine (EvalDistEq.of_eq ?_).trans
    (((uniformSample_bind_simulateQ_permImpl_joint_evalDistEq oa).map
      fun w => (w.1.1, w.1.2.1, w.1.2.2, w.2)).trans (EvalDistEq.of_eq ?_))
  · simp
  · rw [hlazy]
    simp

end EthLib.Cryptography.Secp256k1.Security
