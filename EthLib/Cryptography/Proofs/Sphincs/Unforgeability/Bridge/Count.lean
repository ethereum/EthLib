module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Win
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.Prelude
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.GraphView.HashCalls

/-!
# Proofs: the hash calls of a run, under one answer function

A run of a counted game in the random oracle model is a run under some fixed answer function.

The coins stay random, and the count is the same.

Under one answer function, two games can be compared run by run.

A run of one game gives a run of the other with the same result, and the counts compare.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec
open HashSig (HashSpec OracleWorld)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure)

/-- A query is a hash call, not a coin. -/
def isHashCall (input : OracleWorld.Domain) : Prop := input.isRight

instance : DecidablePred isHashCall := fun input ↦ inferInstanceAs (Decidable (input.isRight))

/-- A count of the counted oracle is a count of the counted game under some answer function.

The cost function must charge 1 for each hash call and 0 for each coin. -/
theorem mem_support_counted_iff {α : Type} (oa : OracleComp OracleWorld α)
    (cost : OracleWorld.Domain → Nat)
    (hcost : ∀ input, cost input = if isHashCall input then 1 else 0) (result : α × Nat) :
    result ∈ support ((simulateQ (HashSpec.romImpl.withAddCost cost) oa).run.run' ∅) ↔
      ∃ f : QueryImpl HashSpec Id, result ∈ support
        (simulateQ (unifFwdAnswerImpl f) (HashSig.counted isHashCall oa)) := by
  rw [show cost = fun input ↦ if isHashCall input then 1 else 0 from funext hcost,
    ← HashSig.simulate_withCost]
  have hrun : result ∈ support
      ((simulateQ HashSpec.romImpl (HashSig.counted isHashCall oa)).run' ∅) ↔
        ∃ cache, (result, cache) ∈ support
          ((simulateQ HashSpec.romImpl
            (HashSig.counted isHashCall oa)).run ∅) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨fun ⟨⟨_, cache⟩, h, hx⟩ ↦ ⟨cache, hx ▸ h⟩, fun ⟨cache, h⟩ ↦ ⟨_, h, rfl⟩⟩
  refine hrun.trans ((exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff _ ∅
    result).symm.trans ?_)
  exact ⟨fun ⟨f, _, hf⟩ ↦ ⟨f, hf⟩, fun ⟨f, hf⟩ ↦ ⟨f, fun _ _ h ↦ by simp at h, hf⟩⟩

variable (f : QueryImpl HashSpec Id)

/-- Mapping the answer adds no hash call. -/
theorem hashCalls_map {β γ : Type} (oc : OracleComp HashSpec β) (g : β → γ) :
    hashCalls f (g <$> oc) = hashCalls f oc := by
  rw [map_eq_bind_pure_comp, hashCalls_bind, Function.comp_apply, hashCalls_pure, Nat.add_zero]

/-- A run under the answer function `f`, with its number of hash calls.

Coins stay uniform. -/
noncomputable def countedRun {α : Type} (oa : OracleComp OracleWorld α) : ProbComp (α × Nat) :=
  simulateQ (unifFwdAnswerImpl f) (HashSig.counted isHashCall oa)

theorem countedRun_pure {α : Type} (x : α) : countedRun f (pure x) = pure (x, 0) := by
  simp only [countedRun, HashSig.counted_pure, simulateQ_pure]

theorem countedRun_bind {α β : Type} (oa : OracleComp OracleWorld α)
    (k : α → OracleComp OracleWorld β) :
    countedRun f (oa >>= k) = (do
      let first ← countedRun f oa
      let second ← countedRun f (k first.1)
      pure (second.1, first.2 + second.2)) := by
  simp only [countedRun, HashSig.counted_bind, simulateQ_bind, simulateQ_pure]

theorem countedRun_map {α β : Type} (oa : OracleComp OracleWorld α) (g : α → β) :
    countedRun f (g <$> oa) = (fun r ↦ (g r.1, r.2)) <$> countedRun f oa := by
  simp only [countedRun, HashSig.counted_map, simulateQ_map]

/-- A run of a mapped computation is a run of the computation, with its result mapped. -/
theorem mem_support_countedRun_map {α β : Type} (oa : OracleComp OracleWorld α) (g : α → β)
    (r : β × Nat) (hr : r ∈ support (countedRun f (g <$> oa))) :
    ∃ run ∈ support (countedRun f oa), r = (g run.1, run.2) := by
  rw [countedRun_map, support_map] at hr
  obtain ⟨run, hrun, rfl⟩ := hr
  exact ⟨run, hrun, rfl⟩

/-- A run of a computation, with its result mapped, is a run of the mapped computation. -/
theorem mem_support_countedRun_map_of_mem {α β : Type} (oa : OracleComp OracleWorld α)
    (g : α → β) (a : α) (n : Nat) (h : (a, n) ∈ support (countedRun f oa)) :
    (g a, n) ∈ support (countedRun f (g <$> oa)) := by
  rw [countedRun_map, support_map]
  exact ⟨(a, n), h, rfl⟩

/-! ## The counted oracles as the plain random oracle with a cost -/

/-- The cost of a query: 0 for a coin and 1 for a hash call. -/
def hashCost : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- The cost of a query is 1 exactly when it is a hash call. -/
theorem hashCost_eq (input : OracleWorld.Domain) :
    hashCost input = if isHashCall input then 1 else 0 := by
  cases input <;> rfl

/-- The counted oracle is the plain random oracle, charging 1 per hash call. -/
theorem countedOracle_eq : countedOracle = HashSpec.romImpl.withAddCost hashCost := rfl

/-- The experiment runs the game against the plain random oracle, charging 1 per hash call. -/
theorem experiment_eq (adversary : Adversary) :
    experiment adversary =
      (simulateQ (HashSpec.romImpl.withAddCost hashCost) (gameCore adversary)).run.run' ∅ := by
  rw [experiment, countedOracle_eq]

/-- The model's counted oracle is the plain random oracle, charging 1 per hash call. -/
theorem modelCountedOracle_eq :
    SphincsSecurity.Security.countedOracle = HashSpec.romImpl.withAddCost hashCost := rfl

/-- The model's experiment runs its game against the plain random oracle, at 1 per hash call. -/
theorem modelExperiment_eq (adversary : SphincsSecurity.Security.Adversary) :
    SphincsSecurity.Security.experiment adversary =
      (simulateQ (HashSpec.romImpl.withAddCost hashCost)
        (SphincsSecurity.Security.gameCore adversary)).run.run' ∅ := by
  rw [SphincsSecurity.Security.experiment, modelCountedOracle_eq]

/-- A computation equal to a counted run has the same results as that run. -/
theorem mem_support_iff_of_eq_withAddCost {α : Type} (oa : OracleComp OracleWorld α)
    (X : ProbComp (α × Nat))
    (hX : X = (simulateQ (HashSpec.romImpl.withAddCost hashCost) oa).run.run' ∅) (r : α × Nat) :
    r ∈ support X ↔
      r ∈ support ((simulateQ (HashSpec.romImpl.withAddCost hashCost) oa).run.run' ∅) := by
  subst hX
  exact Iff.rfl

/-- A result of a computation equal to a counted run is a run under some answer function. -/
theorem exists_countedRun_of_mem_support {α : Type} (oa : OracleComp OracleWorld α)
    (X : ProbComp (α × Nat))
    (hX : X = (simulateQ (HashSpec.romImpl.withAddCost hashCost) oa).run.run' ∅) (r : α × Nat)
    (h : r ∈ support X) : ∃ f, r ∈ support (countedRun f oa) :=
  (mem_support_counted_iff oa hashCost hashCost_eq r).1
    ((mem_support_iff_of_eq_withAddCost oa X hX r).1 h)

/-- A run under some answer function is a result of a computation equal to the counted run. -/
theorem mem_support_of_countedRun {α : Type} (oa : OracleComp OracleWorld α)
    (X : ProbComp (α × Nat))
    (hX : X = (simulateQ (HashSpec.romImpl.withAddCost hashCost) oa).run.run' ∅) (r : α × Nat)
    (h : r ∈ support (countedRun f oa)) : r ∈ support X :=
  (mem_support_iff_of_eq_withAddCost oa X hX r).2
    ((mem_support_counted_iff oa hashCost hashCost_eq r).2 ⟨f, h⟩)

/-- A hash computation runs as under `f`, with its hash calls as the count. -/
theorem countedRun_liftM {β : Type} (oc : OracleComp HashSpec β) :
    countedRun f (liftM oc : OracleComp OracleWorld β) =
      pure (evalWithAnswerFn f oc, hashCalls f oc) := by
  induction oc using OracleComp.inductionOn with
  | pure x => exact countedRun_pure f x
  | query_bind t k ih =>
    rw [← liftComp_eq_liftM, liftComp_bind, liftComp_liftM_query]
    simp only [liftComp_eq_liftM]
    rw [countedRun_bind]
    have hq : countedRun f (liftM (HashSpec.query t) : OracleComp OracleWorld _) =
        pure (f t, 1) := by
      change simulateQ (unifFwdAnswerImpl f)
        (HashSig.counted isHashCall
          (liftM (OracleWorld.query (.inr t)))) = _
      rw [HashSig.counted_query]
      simp only [simulateQ_map, simulateQ_spec_query, unifFwdAnswerImpl, isHashCall,
        Sum.isRight_inr, ↓reduceIte]
      rfl
    have he : evalWithAnswerFn f (liftM (HashSpec.query t) : OracleComp HashSpec _) = f t :=
      simulateQ_spec_query f t
    have hc : hashCalls f (liftM (HashSpec.query t) : OracleComp HashSpec _) = 1 := by
      rw [← bind_pure (liftM (HashSpec.query t) : OracleComp HashSpec _)]
      simp only [hashCalls, SphincsSecurity.Security.queriedInputs_query_bind,
        SphincsSecurity.Security.queriedInputs_pure, List.length_singleton]
    rw [hq, pure_bind, ih, pure_bind, hashCalls_bind, evalWithAnswerFn_bind, he, hc]

/-- Every run of `y` under `f` has a run of `x` with the same result.

Its count `n` bounds the count of `y`: `a` times that count is at most `b * n`. -/
def CountLe (a b : Nat) {α : Type} (x y : OracleComp OracleWorld α) : Prop :=
  ∀ r ∈ support (countedRun f y), ∃ n, (r.1, n) ∈ support (countedRun f x) ∧ a * r.2 ≤ b * n

namespace CountLe

variable {f} {a b : Nat}

theorem refl (hab : a ≤ b) {α : Type} (x : OracleComp OracleWorld α) : CountLe f a b x x :=
  fun r hr ↦ ⟨r.2, hr, Nat.mul_le_mul_right _ hab⟩

theorem bind {α β : Type} {x y : OracleComp OracleWorld α} {kx ky : α → OracleComp OracleWorld β}
    (h : CountLe f a b x y) (hk : ∀ v, CountLe f a b (kx v) (ky v)) :
    CountLe f a b (x >>= kx) (y >>= ky) := by
  intro r hr
  rw [countedRun_bind, mem_support_bind_iff] at hr
  obtain ⟨first, hfirst, hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨second, hsecond, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨n₁, hn₁, hle₁⟩ := h first hfirst
  obtain ⟨n₂, hn₂, hle₂⟩ := hk first.1 second hsecond
  refine ⟨n₁ + n₂, ?_, ?_⟩
  · rw [countedRun_bind, mem_support_bind_iff]
    refine ⟨(first.1, n₁), hn₁, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨(second.1, n₂), hn₂, by simp⟩
  · rw [Nat.mul_add, Nat.mul_add]
    exact Nat.add_le_add hle₁ hle₂

theorem map {α β : Type} {x y : OracleComp OracleWorld α} (h : CountLe f a b x y) (g : α → β) :
    CountLe f a b (g <$> x) (g <$> y) := by
  intro r hr
  rw [countedRun_map, support_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  obtain ⟨n, hn, hle⟩ := h r' hr'
  exact ⟨n, by rw [countedRun_map, support_map]; exact ⟨(r'.1, n), hn, rfl⟩, hle⟩

/-- Two hash computations with one answer under `f`, whose calls compare. -/
theorem lift {β : Type} {x y : OracleComp HashSpec β}
    (heq : evalWithAnswerFn f x = evalWithAnswerFn f y)
    (hle : a * hashCalls f y ≤ b * hashCalls f x) :
    CountLe f a b (liftM x : OracleComp OracleWorld β) (liftM y) := by
  intro r hr
  rw [countedRun_liftM, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨hashCalls f x, by rw [countedRun_liftM, heq]; exact rfl, hle⟩

/-- After one hash computation, only its answer under `f` matters. -/
theorem lift_bind {β γ : Type} (oc : OracleComp HashSpec β)
    {kx ky : β → OracleComp OracleWorld γ} (h : CountLe f a b (kx (evalWithAnswerFn f oc))
      (ky (evalWithAnswerFn f oc))) (hab : a ≤ b) :
    CountLe f a b ((liftM oc : OracleComp OracleWorld β) >>= kx) (liftM oc >>= ky) := by
  intro r hr
  rw [countedRun_bind, countedRun_liftM, pure_bind, mem_support_bind_iff] at hr
  obtain ⟨second, hsecond, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨n, hn, hle⟩ := h second hsecond
  refine ⟨hashCalls f oc + n, ?_, ?_⟩
  · rw [countedRun_bind, countedRun_liftM, pure_bind, mem_support_bind_iff]
    exact ⟨(second.1, n), hn, by simp⟩
  · rw [Nat.mul_add, Nat.mul_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hab) hle

/-- An adversary's run with two logging oracles, whose answers compare request by request. -/
theorem run_simulateQ_withLogging {ιS : Type} {S : OracleSpec.{0, 0} ιS} {α : Type}
    (s₁ s₂ : QueryImpl S (OracleComp OracleWorld)) (h : ∀ t, CountLe f a b (s₁ t) (s₂ t))
    (hab : a ≤ b) (A : OracleComp (OracleWorld + S) α) :
    CountLe f a b
      (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog S) (OracleComp OracleWorld)) + QueryImpl.withLogging s₁) A).run
      (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog S) (OracleComp OracleWorld)) + QueryImpl.withLogging s₂) A).run := by
  induction A using OracleComp.inductionOn with
  | pure a => exact refl hab _
  | query_bind t k ih =>
    rcases t with t | t
    · simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
      refine bind (refl hab _) fun x ↦ ?_
      simp only [map_eq_bind_pure_comp]
      exact bind (ih x.1) fun _ ↦ refl hab _
    · simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.add_apply_inr,
        QueryImpl.withLogging_apply, WriterT.run_tell, bind_assoc,
        map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      have hl : ∀ s : QueryImpl S (OracleComp OracleWorld),
          (liftM (s t) : WriterT (QueryLog S) (OracleComp OracleWorld) _).run =
            s t >>= fun u ↦ pure (u, ∅) := fun s ↦ by
          change (monadLift (s t) : WriterT (QueryLog S) (OracleComp OracleWorld) _).run = _
          rw [WriterT.run_monadLift', map_eq_bind_pure_comp]; rfl
      simp only [hl, bind_assoc, pure_bind]
      exact bind (h t) fun u ↦ bind (ih u) fun _ ↦ refl hab _

end CountLe

open EthLib.Cryptography.Sphincs

/-- If every request compares under `f`, so do EthLib's game and the game with the model's signer.

A request compares when `a` times the model's calls is at most `b` times EthLib's. -/
theorem countLe_signedGame {a b : Nat} (hab : a ≤ b) (adversary : Adversary)
    (hreq : ∀ (S0 : SphincsSecurity.MasterSeed) (m : Message),
      a * hashCalls f (SphincsSecurity.Seeded.sign
        (evalWithAnswerFn f (SphincsSecurity.Seeded.keygen S0 : OracleComp HashSpec _)).2
        (toMessage m) : OracleComp HashSpec _) ≤
      b * hashCalls f (signWith H ⟨ofSeed S0⟩ m)) :
    CountLe f a b (gameCore adversary) (signedGame adversary) := by
  have hverify : ∀ (pk : SphincsSecurity.PublicKey) (forgery : Forgery),
      verifyWith H (ofPublicKey pk) forgery.message forgery.signature =
        (SphincsSecurity.Concrete.verify pk (toMessage forgery.message)
          (toSignature forgery.signature) : OracleComp HashSpec Bool) := fun pk forgery ↦ by
    have h := verifyWith_queryH (m := OracleComp HashSpec) pk (toMessage forgery.message)
      (toSignature forgery.signature)
    rwa [ofMessage_toMessage, ofSignature_toSignature] at h
  unfold gameCore signedGame sampleSeed signingOracle
  simp only [← liftComp_eq_liftM, liftComp_map, bind_map_left, keyGenWith_queryH, hverify]
  simp only [liftComp_eq_liftM]
  refine CountLe.bind (CountLe.refl hab _) fun seed ↦ ?_
  refine CountLe.lift_bind _ ?_ hab
  refine CountLe.bind (CountLe.run_simulateQ_withLogging _ _ (fun m ↦ ?_) hab _)
    fun _ ↦ CountLe.refl hab _
  rw [← liftComp_eq_liftM, ← liftComp_eq_liftM, ← liftComp_map, ← liftComp_map]
  simp only [liftComp_eq_liftM]
  apply CountLe.lift
  · conv_lhs => rw [← ofMessage_toMessage m]
    rw [signWith_answers f seed (toMessage m), evalWithAnswerFn_map]
  · rw [hashCalls_map, hashCalls_map]
    exact hreq seed m

omit f in
/-- If every signing request compares under every answer function, budgets transfer.

An adversary with `q` hash calls against EthLib gives one with `b * q / a` against the model. -/
theorem hasHashQueryBound_translate {a b : Nat} (ha : 0 < a) (hab : a ≤ b)
    (hreq : ∀ (f : QueryImpl HashSpec Id) (S0 : SphincsSecurity.MasterSeed) (m : Message),
      a * hashCalls f (SphincsSecurity.Seeded.sign
        (evalWithAnswerFn f (SphincsSecurity.Seeded.keygen S0 : OracleComp HashSpec _)).2
        (toMessage m) : OracleComp HashSpec _) ≤
      b * hashCalls f (signWith H ⟨ofSeed S0⟩ m))
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound adversary q) :
    SphincsSecurity.Security.HasHashQueryBound (translate adversary) (b * q / a) := by
  intro result hr
  obtain ⟨f, hr⟩ := exists_countedRun_of_mem_support _ _
    (modelExperiment_eq (translate adversary)) result hr
  rw [gameCore_translate] at hr
  obtain ⟨⟨run, n⟩, hrun, rfl⟩ := mem_support_countedRun_map f _ _ result hr
  have hsigned : (wins run, n) ∈ support (countedRun f (signedGame adversary)) := by
    rw [signedGame_eq]
    exact mem_support_countedRun_map_of_mem f _ wins run n hrun
  obtain ⟨n', hn', hle⟩ := countLe_signedGame f hab adversary (hreq f) _ hsigned
  have hq' := hq _ (mem_support_of_countedRun f _ _ (experiment_eq adversary) _ hn')
  exact (Nat.le_div_iff_mul_le ha).2 (by
    rw [Nat.mul_comm]
    exact hle.trans (Nat.mul_le_mul_left _ hq'))

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
