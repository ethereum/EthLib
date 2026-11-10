module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Proofs: the ECDSA game over the joint state of its oracles

The game as a program asks a permutation oracle for `Π`.

Its signing oracle keeps a cache of answers, and the permutation oracle keeps a state of its own.

A signer that only asks for `Π` cannot set it.

Theorem 1 of the source needs one that does: it signs without the key and sets `Π` to match.

So here the signing oracle reads and writes both states at once.

The permutation oracle and the signer of new messages are parameters.

The signing oracle answers a repeated message from its cache, and records each new answer.

With the real signer, run against the permutation oracle, this is the game as a program.

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

open OracleComp OracleSpec LazyPermutation

variable {F G A M σ : Type}

/-- The joint state: the answers of the signing oracle, and the state of the permutation oracle. -/
abbrev JointState (F M σ : Type) := Cache F M × σ

/-- A signer of new messages, which may read and write the state of the permutation oracle.

Its answer `none` means that signing failed, and the message stays fresh.

Over the lazy permutation, a signer may write a pair that no permutation agrees with.

The draw at the end then gives the identity, and the joint law of the game no longer holds. -/
abbrev FreshSigner (F M σ : Type) := M → StateT σ ProbComp (Option (F × F))

variable [DecidableEq M]

/-- The oracles of the game over the joint state, with a permutation oracle and a signer.

Coins leave both states unchanged.

`Π` and its inverse go to the permutation oracle on the second state.

They leave the signing cache unchanged.

A repeated message gets the answer it got first.

A new message goes to the signer, and its answer joins the signing cache. -/
def jointImpl (perm : QueryImpl (PermSpec A) (StateT σ ProbComp)) (fresh : FreshSigner F M σ) :
    QueryImpl (Spec F A M) (StateT (JointState F M σ) ProbComp)
  | .inl n => fun s => (·, s) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl α) => fun s => (fun z => (z.1, (s.1, z.2))) <$> (perm (.inl α)).run s.2
  | .inr (.inr (.inl β)) => fun s => (fun z => (z.1, (s.1, z.2))) <$> (perm (.inr β)).run s.2
  | .inr (.inr (.inr m)) => fun s =>
    match s.1.lookup m with
    | some a => pure (a, s)
    | none => (fun z => (z.1, (s.1 ++ [(m, z.1)], z.2))) <$> (fresh m).run s.2

/-- A signer of new messages that asks for `Π`, run against the permutation oracle.

It reads and writes the state of that oracle only through its queries. -/
def liftFresh (perm : QueryImpl (PermSpec A) (StateT σ ProbComp))
    (fresh : M → PermComp A (Option (F × F))) : FreshSigner F M σ := fun m ps =>
  (simulateQ (unifSpec.passthrough + perm) (fresh m)).run ps

/-- Map the state of the permutation oracle, and the joint oracles commute with the map.

It suffices that each query of `Π`, and each call of the signer, commutes with it. -/
theorem map_run_jointImpl_of_proj {σ₁ σ₂ : Type}
    (perm₁ : QueryImpl (PermSpec A) (StateT σ₁ ProbComp))
    (perm₂ : QueryImpl (PermSpec A) (StateT σ₂ ProbComp)) (fresh₁ : FreshSigner F M σ₁)
    (fresh₂ : FreshSigner F M σ₂) (proj : σ₁ → σ₂)
    (hperm : ∀ q s, Prod.map id proj <$> (perm₁ q).run s = (perm₂ q).run (proj s))
    (hfresh : ∀ m s, Prod.map id proj <$> (fresh₁ m).run s = (fresh₂ m).run (proj s))
    (q : (Spec F A M).Domain) (s : JointState F M σ₁) :
    Prod.map id (Prod.map id proj) <$> (jointImpl perm₁ fresh₁ q).run s =
      (jointImpl perm₂ fresh₂ q).run (Prod.map id proj s) := by
  obtain ⟨cache, c⟩ := s
  rcases q with n | α | β | m
  · change Prod.map id (Prod.map id proj) <$>
        (·, (cache, c)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) =
      (·, (cache, proj c)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
    simp [Functor.map_map]
  · change Prod.map id (Prod.map id proj) <$> (fun z => (z.1, (cache, z.2))) <$>
        (perm₁ (.inl α)).run c = (fun z => (z.1, (cache, z.2))) <$> (perm₂ (.inl α)).run (proj c)
    rw [← hperm]
    simp [Functor.map_map]
  · change Prod.map id (Prod.map id proj) <$> (fun z => (z.1, (cache, z.2))) <$>
        (perm₁ (.inr β)).run c = (fun z => (z.1, (cache, z.2))) <$> (perm₂ (.inr β)).run (proj c)
    rw [← hperm]
    simp [Functor.map_map]
  · change Prod.map id (Prod.map id proj) <$> (match cache.lookup m with
        | some a => pure (a, (cache, c))
        | none => (fun z : Option (F × F) × σ₁ => (z.1, (cache ++ [(m, z.1)], z.2))) <$>
          (fresh₁ m).run c) =
      (match cache.lookup m with
        | some a => pure (a, (cache, proj c))
        | none => (fun z : Option (F × F) × σ₂ => (z.1, (cache ++ [(m, z.1)], z.2))) <$>
          (fresh₂ m).run (proj c))
    cases cache.lookup m with
    | some a => simp
    | none =>
      rw [← hfresh]
      simp [Functor.map_map]

omit [DecidableEq M] in
/-- A signer lifted against `Π`'s oracle commutes with a map of the state, when each query does. -/
theorem map_run_liftFresh_of_proj {σ₁ σ₂ : Type}
    (perm₁ : QueryImpl (PermSpec A) (StateT σ₁ ProbComp))
    (perm₂ : QueryImpl (PermSpec A) (StateT σ₂ ProbComp)) (proj : σ₁ → σ₂)
    (hperm : ∀ q s, Prod.map id proj <$> (perm₁ q).run s = (perm₂ q).run (proj s))
    (fresh : M → PermComp A (Option (F × F))) (m : M) (s : σ₁) :
    Prod.map id proj <$> (liftFresh perm₁ fresh m).run s =
      (liftFresh perm₂ fresh m).run (proj s) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ proj (fun t s => ?_) (fresh m) s
  rcases t with n | q
  · simp [StateT.run_monadLift, Functor.map_map]
  · exact hperm q s

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Run the adversary on the key `X` over the joint state, and check its forgery.

The signing cache starts empty, and the permutation oracle starts from `init`.

The check asks the permutation oracle for `Π`, once or never.

It returns the forgery, the result, the final signing cache and the final state of that oracle. -/
def jointRun (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (perm : QueryImpl (PermSpec A) (StateT σ ProbComp)) (init : σ) (fresh : FreshSigner F M σ) :
    ProbComp (((M × F × F) × Bool × Cache F M) × σ) := do
  let ((m, t, s), (cache, ps)) ←
    (simulateQ (jointImpl perm fresh) (adversary.main X)).run ([], init)
  if signed cache m then return (((m, t, s), false, cache), ps) else
    (fun z => (((m, t, s), z.1, cache), z.2)) <$>
      (simulateQ (unifSpec.passthrough + perm) (verifyQ scheme X m t s)).run ps

/-- Map the state of the permutation oracle, and the joint run commutes with the map.

It suffices that each query of `Π`, and each call of the signer, commutes with it. -/
theorem map_jointRun_of_proj {σ₁ σ₂ : Type} (scheme : Scheme F G A M)
    (adversary : Adversary F G A M) (X : G) (perm₁ : QueryImpl (PermSpec A) (StateT σ₁ ProbComp))
    (perm₂ : QueryImpl (PermSpec A) (StateT σ₂ ProbComp)) (init : σ₁)
    (fresh₁ : FreshSigner F M σ₁) (fresh₂ : FreshSigner F M σ₂) (proj : σ₁ → σ₂)
    (hperm : ∀ q s, Prod.map id proj <$> (perm₁ q).run s = (perm₂ q).run (proj s))
    (hfresh : ∀ m s, Prod.map id proj <$> (fresh₁ m).run s = (fresh₂ m).run (proj s)) :
    Prod.map id proj <$> jointRun scheme adversary X perm₁ init fresh₁ =
      jointRun scheme adversary X perm₂ (proj init) fresh₂ := by
  have hrun := map_run_simulateQ_eq_of_query_map_eq _ _ (Prod.map id proj)
    (map_run_jointImpl_of_proj perm₁ perm₂ fresh₁ fresh₂ proj hperm hfresh) (adversary.main X)
    ([], init)
  simp only [jointRun]
  rw [show (([] : Cache F M), proj init) = Prod.map id proj ([], init) from rfl, ← hrun,
    map_bind, bind_map_left]
  refine bind_congr fun z => ?_
  obtain ⟨⟨m, t, s⟩, cache, c⟩ := z
  by_cases h : signed cache m
  · simp [h]
  · simp only [h, Bool.false_eq_true, ite_false, Prod.map_snd, Prod.map_fst, id_eq]
    rw [← map_run_simulateQ_eq_of_query_map_eq (unifSpec.passthrough + perm₁)
      (unifSpec.passthrough + perm₂) proj (fun t s => by
        rcases t with n | q
        · simp [StateT.run_monadLift, Functor.map_map]
        · exact hperm q s)]
    simp [Functor.map_map]

variable [SampleableType F]

omit [DecidableEq G] in
/-- Run the game's oracles, with the real signing oracle under the key `x`, against `Π`'s oracle.

Those are the joint oracles with the real signer of new messages. -/
theorem flattenStateT_mapStateTBase_implQ_signQ (perm : QueryImpl (PermSpec A) (StateT σ ProbComp))
    (scheme : Scheme F G A M) (fuel : ℕ) (x : F) :
    ((unifSpec.passthrough + perm).mapStateTBase (implQ (signQ scheme fuel x))).flattenStateT =
      jointImpl perm (liftFresh perm fun m => signFreshQ scheme x m fuel) := by
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
  · change (fun y => (y.1.1, (y.1.2, y.2))) <$>
        (simulateQ (unifSpec.passthrough + perm) (signQ scheme fuel x m s.1)).run s.2 = _
    obtain ⟨cache, ps⟩ := s
    change _ = match cache.lookup m with
      | some a => pure (a, (cache, ps))
      | none => (fun z : Option (F × F) × σ => (z.1, (cache ++ [(m, z.1)], z.2))) <$>
        (simulateQ (unifSpec.passthrough + perm) (signFreshQ scheme x m fuel)).run ps
    simp only [signQ]
    cases cache.lookup m with
    | some a => simp
    | none => simp [Functor.map_map]

/-- Run the program with the real signer against the permutation oracle.

That is the joint run with the real signer of new messages. -/
theorem simulateQ_runCacheQ_run (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (perm : QueryImpl (PermSpec A) (StateT σ ProbComp)) (init : σ) (fuel : ℕ) (x : F) :
    (simulateQ (unifSpec.passthrough + perm)
        (runCacheQ scheme adversary X (signQ scheme fuel x))).run init =
      jointRun scheme adversary X perm init
        (liftFresh perm fun m => signFreshQ scheme x m fuel) := by
  simp only [runCacheQ, jointRun, simulateQ_bind, StateT.run_bind,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, flattenStateT_mapStateTBase_implQ_signQ,
    bind_map_left]
  refine bind_congr fun z => ?_
  obtain ⟨⟨m, t, s⟩, cache, ps⟩ := z
  by_cases h : signed cache m <;> simp [h]

variable [FinEnum A]

/-- The lazy game over the joint state: draw the key, then run with the real signer.

The permutation oracle is the lazy permutation, from the empty cache.

It returns the forgery, the result and both final caches. -/
def jointExperiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp (((M × F × F) × Bool × Cache F M) × PermCache A) := do
  let x ← $ᵗ F
  jointRun scheme adversary (x • scheme.g) lazyPermOracle []
    (liftFresh lazyPermOracle fun m => signFreshQ scheme x m fuel)

/-- Run the program with the forgery and the signing cache against the lazy permutation.

That is the joint lazy game. -/
theorem simulateQ_lazyPermImpl_experimentViewQ_run (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    (simulateQ lazyPermImpl (experimentViewQ scheme fuel adversary)).run [] =
      jointExperiment scheme fuel adversary := by
  simp only [experimentViewQ, jointExperiment, simulateQ_bind, StateT.run_bind,
    simulateQ_lazyPermImpl_liftM_run, bind_map_left]
  exact bind_congr fun x => simulateQ_runCacheQ_run scheme adversary _ lazyPermOracle [] fuel x

/-- Keep only the result of the joint lazy game, and it is the lazy game. -/
theorem lazyExperiment_eq_result_map_jointExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    lazyExperiment scheme fuel adversary =
      (fun z => z.1.2.1) <$> jointExperiment scheme fuel adversary := by
  rw [lazyExperiment, experimentQ, StateT.run'_eq, simulateQ_map, StateT.run_map,
    simulateQ_lazyPermImpl_experimentViewQ_run]
  simp [Functor.map_map]

/-- The game with its forgery, signing cache and `Π` has the law of the joint lazy game.

Run the joint lazy game, then draw `Π` from its final cache of `Π`.

The draw is uniform among the permutations that agree with that cache. -/
theorem experimentView_evalDistEq_jointExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    experimentView scheme fuel adversary =ᵈ
      (do
        let (f, c) ← jointExperiment scheme fuel adversary
        let π ← uniformExtension c
        pure (f.1, f.2.1, f.2.2, π)) := by
  rw [experimentView_eq_permImpl]
  refine (EvalDistEq.of_eq ?_).trans
    (((uniformSample_bind_simulateQ_permImpl_joint_evalDistEq
      (experimentViewQ scheme fuel adversary)).map
      fun w => (w.1.1, w.1.2.1, w.1.2.2, w.2)).trans (EvalDistEq.of_eq ?_))
  · simp
  · rw [simulateQ_lazyPermImpl_experimentViewQ_run]
    simp

end EthLib.Cryptography.Secp256k1.Security
