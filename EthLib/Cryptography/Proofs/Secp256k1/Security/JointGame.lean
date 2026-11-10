module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame

/-!
# Proofs: the ECDSA game over the joint state of its oracles

The game as a program asks a permutation oracle for `Π`.

Its signing oracle keeps a cache of answers, and the permutation oracle keeps a state of its own.

A signer that only asks for `Π` cannot set it.

Theorem 1 of the source needs one that does: it signs without the key and sets `Π` to match.

So here every oracle reads and writes both states at once.

The permutation oracle and the signer are parameters.

With a signer that asks for `Π`, run against that oracle, this is the game as a program.

The run also returns the forgery and both final states.

The lazy permutation is one such oracle.

With it and the real signer, keeping only the result, this is the lazy game.

Then draw `Π` uniformly among the permutations that agree with the final cache of `Π`.

The forgery, the result, the signing cache and `Π` then have the joint law of the game.

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

The signer that sets `Π` is the one in the proof of their Theorem 1.

The joint state is the challenger's side of the games of that proof.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M σ : Type}

/-- The joint state: the answers of the signing oracle, and the state of the permutation oracle. -/
abbrev JointState (F M σ : Type) := Cache F M × σ

/-- A signing oracle that reads and writes the joint state.

The check of the forgery reads the signing cache that this oracle keeps.

So the oracle must record each answer, as the real signer does.

It may also change the state of the permutation oracle.

A signer that breaks the partial bijection of the lazy permutation's cache leaves the model.

No permutation then agrees with the cache, and the draw at the end gives the identity. -/
abbrev JointSigner (F M σ : Type) := M → StateT (JointState F M σ) ProbComp (Option (F × F))

/-- The oracles of the game over the joint state, with a permutation oracle and a signing oracle.

Coins leave both states unchanged.

`Π` and its inverse go to the permutation oracle on the second state.

They leave the signing cache unchanged. -/
def jointImpl (perm : QueryImpl (PermSpec A) (StateT σ ProbComp)) (signer : JointSigner F M σ) :
    QueryImpl (Spec F A M) (StateT (JointState F M σ) ProbComp)
  | .inl n => fun s => (·, s) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl α) => fun s => (fun z => (z.1, (s.1, z.2))) <$> (perm (.inl α)).run s.2
  | .inr (.inr (.inl β)) => fun s => (fun z => (z.1, (s.1, z.2))) <$> (perm (.inr β)).run s.2
  | .inr (.inr (.inr m)) => signer m

/-- A signing oracle that asks for `Π`, run against the permutation oracle.

It reads and writes the state of that oracle only through its queries. -/
def liftSigner (perm : QueryImpl (PermSpec A) (StateT σ ProbComp)) (signer : SignerQ F A M) :
    JointSigner F M σ := fun m s =>
  (fun z => (z.1.1, (z.1.2, z.2))) <$>
    (simulateQ (unifSpec.passthrough + perm) ((signer m).run s.1)).run s.2

/-- Take a signer that asks for `Π`, and run its oracles against the permutation oracle.

Those are the joint oracles with that signer lifted to the joint state. -/
theorem flattenStateT_mapStateTBase_implQ (perm : QueryImpl (PermSpec A) (StateT σ ProbComp))
    (signer : SignerQ F A M) :
    ((unifSpec.passthrough + perm).mapStateTBase (implQ signer)).flattenStateT =
      jointImpl perm (liftSigner perm signer) := by
  funext q
  refine StateT.ext fun s => ?_
  rcases q with n | α | β | m
  · change (fun y => (y.1.1, (y.1.2, y.2))) <$> (simulateQ (unifSpec.passthrough + perm)
        ((·, s.1) <$> query (spec := unifSpec + PermSpec A) (.inl n))).run s.2 =
      (·, s) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
    simp [Functor.map_map]
  · change (fun y => (y.1.1, (y.1.2, y.2))) <$> (simulateQ (unifSpec.passthrough + perm)
        ((·, s.1) <$> query (spec := unifSpec + PermSpec A) (.inr (.inl α)))).run s.2 =
      (fun z => (z.1, (s.1, z.2))) <$> (perm (.inl α)).run s.2
    simp [Functor.map_map]
  · change (fun y => (y.1.1, (y.1.2, y.2))) <$> (simulateQ (unifSpec.passthrough + perm)
        ((·, s.1) <$> query (spec := unifSpec + PermSpec A) (.inr (.inr β)))).run s.2 =
      (fun z => (z.1, (s.1, z.2))) <$> (perm (.inr β)).run s.2
    simp [Functor.map_map]
  · rfl

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]

/-- Run the adversary on the key `X` over the joint state, and check its forgery.

The signing cache starts empty, and the permutation oracle starts from `init`.

The check asks the permutation oracle for `Π`, once or never.

It returns the forgery, the result and both final states. -/
def jointRun (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (perm : QueryImpl (PermSpec A) (StateT σ ProbComp)) (init : σ)
    (signer : JointSigner F M σ) : ProbComp ((M × F × F) × Bool × JointState F M σ) := do
  let ((m, t, s), (cache, ps)) ←
    (simulateQ (jointImpl perm signer) (adversary.main X)).run ([], init)
  if signed cache m then return ((m, t, s), false, (cache, ps)) else
    (fun z => ((m, t, s), z.1, (cache, z.2))) <$>
      (simulateQ (unifSpec.passthrough + perm) (verifyQ scheme X m t s)).run ps

/-- Run the program with a signer that asks for `Π` against the permutation oracle.

That is the joint run with the signer lifted. -/
theorem simulateQ_runCacheQ (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (perm : QueryImpl (PermSpec A) (StateT σ ProbComp)) (init : σ) (signer : SignerQ F A M) :
    (simulateQ (unifSpec.passthrough + perm) (runCacheQ scheme adversary X signer)).run init =
      (fun z => ((z.1, z.2.1, z.2.2.1), z.2.2.2)) <$>
        jointRun scheme adversary X perm init (liftSigner perm signer) := by
  simp only [runCacheQ, jointRun, simulateQ_bind, StateT.run_bind,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, flattenStateT_mapStateTBase_implQ,
    bind_map_left, map_bind]
  refine bind_congr fun z => ?_
  obtain ⟨⟨m, t, s⟩, cache, ps⟩ := z
  by_cases h : signed cache m
  · simp [h]
  · simp [h]

variable [SampleableType F] [FinEnum A]

/-- The lazy game over the joint state: draw the key, then run with the real signer.

The permutation oracle is the lazy permutation, from the empty cache.

It returns the forgery, the result and both final caches. -/
def jointExperiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp ((M × F × F) × Bool × JointState F M (PermCache A)) := do
  let x ← $ᵗ F
  jointRun scheme adversary (x • scheme.g) lazyPermOracle []
    (liftSigner lazyPermOracle (signQ scheme fuel x))

/-- Run the program with the forgery and the signing cache against the lazy permutation.

That is the joint lazy game. -/
theorem simulateQ_lazyPermImpl_experimentViewQ (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    (simulateQ lazyPermImpl (experimentViewQ scheme fuel adversary)).run [] =
      (fun z => ((z.1, z.2.1, z.2.2.1), z.2.2.2)) <$> jointExperiment scheme fuel adversary := by
  simp only [experimentViewQ, jointExperiment, simulateQ_bind, StateT.run_bind,
    simulateQ_lazyPermImpl_liftM_run, bind_map_left, map_bind]
  exact bind_congr fun x => simulateQ_runCacheQ scheme adversary _ lazyPermOracle [] _

/-- Keep only the result of the joint lazy game, and it is the lazy game. -/
theorem lazyExperiment_eq_result_map_jointExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    lazyExperiment scheme fuel adversary =
      (fun z => z.2.1) <$> jointExperiment scheme fuel adversary := by
  rw [lazyExperiment, ← result_map_experimentViewQ, StateT.run'_eq, simulateQ_map,
    StateT.run_map, simulateQ_lazyPermImpl_experimentViewQ]
  simp [Functor.map_map]

/-- The game with its forgery, signing cache and `Π` has the law of the joint lazy game.

Run the joint lazy game, then draw `Π` from its final cache of `Π`.

The draw is uniform among the permutations that agree with that cache. -/
theorem experimentView_evalDistEq_jointExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    experimentView scheme fuel adversary =ᵈ
      (do
        let (f, b, cache, c) ← jointExperiment scheme fuel adversary
        let π ← uniformExtension c
        pure (f, b, cache, π)) := by
  rw [experimentView_eq_permImpl]
  refine (EvalDistEq.of_eq ?_).trans
    (((uniformSample_bind_simulateQ_permImpl_joint_evalDistEq
      (experimentViewQ scheme fuel adversary)).map
      fun w => (w.1.1, w.1.2.1, w.1.2.2, w.2)).trans (EvalDistEq.of_eq ?_))
  · simp
  · rw [simulateQ_lazyPermImpl_experimentViewQ]
    simp

end EthLib.Cryptography.Secp256k1.Security
