module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad

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

The draw at the end then gives the identity, and the joint law of the game no longer holds.

It runs over coins alone, unless another base monad is given. -/
abbrev FreshSigner (F M σ : Type) (μ : Type → Type := ProbComp) :=
  M → StateT σ μ (Option (F × F))

variable [DecidableEq M]

/-- The oracles of the game over the joint state, with a permutation oracle and a signer.

Coins leave both states unchanged.

`Π` and its inverse go to the permutation oracle on the second state.

They leave the signing cache unchanged.

A repeated message gets the answer it got first.

A new message goes to the signer, and its answer joins the signing cache.

The base monad lifts the coins, so the oracles may themselves ask an outer oracle for `Π`. -/
def jointImpl {μ : Type → Type} [Monad μ] [MonadLiftT ProbComp μ]
    (perm : QueryImpl (PermSpec A) (StateT σ μ)) (fresh : FreshSigner F M σ μ) :
    QueryImpl (Spec F A M) (StateT (JointState F M σ) μ)
  | .inl n => fun s =>
    (·, s) <$> (liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) : μ _)
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

/-- Joint oracles that ask for `Π`, run against an oracle of `Π`, are joint oracles on both states.

The oracle of `Π` keeps its own state, beside the state of the permutation oracle.

It suffices that each query of `Π`, and each call of the signer, runs that way to the new one. -/
theorem map_run_simulateQ_jointImpl {τ : Type} (base : QueryImpl (PermSpec A) (StateT τ ProbComp))
    (perm : QueryImpl (PermSpec A) (StateT σ (PermComp A)))
    (fresh : FreshSigner F M σ (PermComp A))
    (perm' : QueryImpl (PermSpec A) (StateT (σ × τ) ProbComp)) (fresh' : FreshSigner F M (σ × τ))
    (hperm : ∀ q s l, (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (unifSpec.passthrough + base) ((perm q).run s)).run l = (perm' q).run (s, l))
    (hfresh : ∀ m s l, (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (unifSpec.passthrough + base) ((fresh m).run s)).run l = (fresh' m).run (s, l))
    {α : Type} (oa : OracleComp (Spec F A M) α) (cache : Cache F M) (s : σ) (l : τ) :
    (fun y => (y.1.1, (y.1.2.1, (y.1.2.2, y.2)))) <$>
        (simulateQ (unifSpec.passthrough + base)
          ((simulateQ (jointImpl perm fresh) oa).run (cache, s))).run l =
      (simulateQ (jointImpl perm' fresh') oa).run (cache, (s, l)) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  refine Eq.trans ?_ (map_run_simulateQ_eq_of_query_map_eq
    ((unifSpec.passthrough + base).mapStateTBase (jointImpl perm fresh)).flattenStateT _
    (fun s : (Cache F M × σ) × τ => (s.1.1, (s.1.2, s.2))) (fun t s => ?_) oa ((cache, s), l))
  · rfl
  obtain ⟨⟨c, p⟩, l⟩ := s
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run, Functor.map_map]
  rcases t with n | α | β | m
  · change (fun a => Prod.map id (fun s => (s.1.1, s.1.2, s.2)) (a.1.1, a.1.2, a.2)) <$>
        (simulateQ (unifSpec.passthrough + base) ((·, (c, p)) <$>
          (liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) : PermComp A _))).run l =
      (·, (c, (p, l))) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
    rw [simulateQ_map, StateT.run_map, simulateQ_passthrough_add_liftM_run]
    simp [Functor.map_map]
  · change (fun a => Prod.map id (fun s => (s.1.1, s.1.2, s.2)) (a.1.1, a.1.2, a.2)) <$>
        (simulateQ (unifSpec.passthrough + base) ((fun z => (z.1, (c, z.2))) <$>
          (perm (.inl α)).run p)).run l = (fun z => (z.1, (c, z.2))) <$> (perm' (.inl α)).run (p, l)
    rw [← hperm]
    simp [Functor.map_map]
  · change (fun a => Prod.map id (fun s => (s.1.1, s.1.2, s.2)) (a.1.1, a.1.2, a.2)) <$>
        (simulateQ (unifSpec.passthrough + base) ((fun z => (z.1, (c, z.2))) <$>
          (perm (.inr β)).run p)).run l = (fun z => (z.1, (c, z.2))) <$> (perm' (.inr β)).run (p, l)
    rw [← hperm]
    simp [Functor.map_map]
  · change (fun a => Prod.map id (fun s => (s.1.1, s.1.2, s.2)) (a.1.1, a.1.2, a.2)) <$>
        (simulateQ (unifSpec.passthrough + base) (match c.lookup m with
          | some a => pure (a, (c, p))
          | none => (fun z => (z.1, (c ++ [(m, z.1)], z.2))) <$> (fresh m).run p)).run l =
      match c.lookup m with
      | some a => pure (a, (c, (p, l)))
      | none => (fun z => (z.1, (c ++ [(m, z.1)], z.2))) <$> (fresh' m).run (p, l)
    cases c.lookup m with
    | some a => simp
    | none =>
      rw [← hfresh]
      simp [Functor.map_map]

/-! ## Domination until a bad event -/

/-- The joint oracles keep an invariant of the state of the permutation oracle.

It suffices that each query of `Π`, and each call of the signer, keeps it. -/
theorem preservesInv_jointImpl {perm : QueryImpl (PermSpec A) (StateT σ ProbComp)}
    {fresh : FreshSigner F M σ} {P : σ → Prop} (hperm : QueryImpl.PreservesInv perm P)
    (hfresh : ∀ m, StateT.PreservesInv (fresh m) P) :
    QueryImpl.PreservesInv (jointImpl perm fresh) fun s => P s.2 := by
  rintro q ⟨cache, c⟩ hs z hz
  rcases q with n | α | β | m
  · change z ∈ support ((·, (cache, c)) <$>
      (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hs
  · change z ∈ support ((fun z => (z.1, (cache, z.2))) <$> (perm (.inl α)).run c) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hperm _ c hs w hw
  · change z ∈ support ((fun z => (z.1, (cache, z.2))) <$> (perm (.inr β)).run c) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hperm _ c hs w hw
  · change z ∈ support (match cache.lookup m with
        | some a => pure (a, (cache, c))
        | none => (fun z : Option (F × F) × σ => (z.1, (cache ++ [(m, z.1)], z.2))) <$>
          (fresh m).run c) at hz
    rcases h : cache.lookup m with _ | a <;> rw [h] at hz
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact hfresh m c hs w hw
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs

/-- The joint oracles with a first oracle of `Π` and signer are dominated by a second pair.

The domination holds until a bad event of the first state, read through `f` on the second state.

It suffices that each query of `Π`, and each call of the signer, is dominated in the same way. -/
theorem dominatedUntilBad_jointImpl {σ₁ σ₂ : Type}
    {perm₁ : QueryImpl (PermSpec A) (StateT σ₁ ProbComp)}
    {perm₂ : QueryImpl (PermSpec A) (StateT σ₂ ProbComp)} {fresh₁ : FreshSigner F M σ₁}
    {fresh₂ : FreshSigner F M σ₂} {f : σ₁ → σ₂} {inv bad : σ₁ → Prop}
    (hperm : QueryImpl.DominatedUntilBad perm₁ perm₂ f inv bad)
    (hfresh : ∀ m s, inv s → ¬bad s → ∀ Q : Option (F × F) × σ₂ → Prop,
      Pr{let z ← (fresh₁ m).run s}[Q (z.1, f z.2) ∧ ¬bad z.2] ≤
        Pr{let z ← (fresh₂ m).run (f s)}[Q z]) :
    QueryImpl.DominatedUntilBad (jointImpl perm₁ fresh₁) (jointImpl perm₂ fresh₂)
      (Prod.map id f) (fun s => inv s.2) fun s => bad s.2 := by
  rintro q ⟨cache, c⟩ hinv hbad Q
  rcases q with n | α | β | m
  · change Pr{let z ← (·, (cache, c)) <$>
        (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))}[
          Q (z.1, Prod.map id f z.2) ∧ ¬bad z.2.2] ≤
      Pr{let z ← (·, (cache, f c)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))}[Q z]
    rw [prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · change Pr{let z ← (fun z => (z.1, (cache, z.2))) <$> (perm₁ (.inl α)).run c}[
          Q (z.1, Prod.map id f z.2) ∧ ¬bad z.2.2] ≤
      Pr{let z ← (fun z => (z.1, (cache, z.2))) <$> (perm₂ (.inl α)).run (f c)}[Q z]
    rw [prEvent_map, prEvent_map]
    exact hperm (.inl α) c hinv hbad fun w : A × σ₂ => Q (w.1, (cache, w.2))
  · change Pr{let z ← (fun z => (z.1, (cache, z.2))) <$> (perm₁ (.inr β)).run c}[
          Q (z.1, Prod.map id f z.2) ∧ ¬bad z.2.2] ≤
      Pr{let z ← (fun z => (z.1, (cache, z.2))) <$> (perm₂ (.inr β)).run (f c)}[Q z]
    rw [prEvent_map, prEvent_map]
    exact hperm (.inr β) c hinv hbad fun w : A × σ₂ => Q (w.1, (cache, w.2))
  · change Pr{let z ← (match cache.lookup m with
          | some a => pure (a, (cache, c))
          | none => (fun z : Option (F × F) × σ₁ => (z.1, (cache ++ [(m, z.1)], z.2))) <$>
            (fresh₁ m).run c)}[Q (z.1, Prod.map id f z.2) ∧ ¬bad z.2.2] ≤
      Pr{let z ← (match cache.lookup m with
          | some a => pure (a, (cache, f c))
          | none => (fun z : Option (F × F) × σ₂ => (z.1, (cache ++ [(m, z.1)], z.2))) <$>
            (fresh₂ m).run (f c))}[Q z]
    rcases cache.lookup m with _ | a
    · rw [prEvent_map, prEvent_map]
      exact hfresh m c hinv hbad fun w => Q (w.1, (cache ++ [(m, w.1)], w.2))
    · exact prEvent_pure_le_pure _ _ _ _ fun h => h.1

/-- Over the joint state, a computation that asks only coins and `Π` runs on the second state.

The signing cache stays as it is. -/
theorem simulateQ_jointImpl_keyOnlyLift_run (perm : QueryImpl (PermSpec A) (StateT σ ProbComp))
    (fresh : FreshSigner F M σ) {α : Type} (oa : PermComp A α) (cache : Cache F M) (s : σ) :
    (simulateQ (jointImpl perm fresh) (simulateQ keyOnlyLift oa)).run (cache, s) =
      (fun z => (z.1, (cache, z.2))) <$> (simulateQ (unifSpec.passthrough + perm) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | a | b
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change ((·, (cache, s)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) >>= _ = _
      simp [ih]
    all_goals
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [add_apply_inr, StateT.run, keyOnlyLift_inr_inl, keyOnlyLift_inr_inr,
        HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, jointImpl, id_map, bind_map_left, map_bind]
      exact bind_congr fun z : A × σ => ih z.1 z.2

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

/-- The adversary's run on the key `X`, then the check of its forgery, with the game's oracles.

The check asks `Π` through the same oracles as the adversary. -/
def runWithCheck (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G) :
    OracleComp (Spec F A M) ((M × F × F) × Bool) := do
  let z ← adversary.main X
  let b ← simulateQ keyOnlyLift (verifyQ scheme X z.1 z.2.1 z.2.2)
  pure (z, b)

/-- The joint run wins exactly when the run with an unconditional check wins on a new message.

The event on a win may also read the forgery and the final signing cache. -/
theorem prEvent_jointRun_eq_runWithCheck (scheme : Scheme F G A M)
    (adversary : Adversary F G A M) (X : G) (perm : QueryImpl (PermSpec A) (StateT σ ProbComp))
    (init : σ) (fresh : FreshSigner F M σ) (R : M × F × F → Cache F M → Prop) :
    Pr{let r ← jointRun scheme adversary X perm init fresh}[
      r.1.2.1 = true ∧ R r.1.1 r.1.2.2] =
    Pr{let r ← (simulateQ (jointImpl perm fresh) (runWithCheck scheme adversary X)).run
        ([], init)}[signed r.2.1 r.1.1.1 = false ∧ r.1.2 = true ∧ R r.1.1 r.2.1] := by
  simp only [jointRun, runWithCheck, simulateQ_bind, simulateQ_pure, StateT.run_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun z => ?_
  obtain ⟨⟨m, t, s⟩, cache, ps⟩ := z
  rw [simulateQ_jointImpl_keyOnlyLift_run, bind_map_left]
  by_cases h : signed cache m <;> simp [h]

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
