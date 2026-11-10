module

public import EthLib.Cryptography.Proofs.IndependentAnswers
public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.OracleComp.Coercions.SubSpec.Measure
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Proofs: independent answers to a permutation, asked of one outside oracle

The oracle with independent answers draws each new forward answer itself.

Here each new forward answer is one query to an outside oracle with no input.

New inverse answers still come from coins.

Before it asks the outside oracle, a new forward query asks the coins at the code of its point.

That query changes no law, since its answer is dropped, but it records the point in the transcript.

The cache and the flag change as before, and each new forward query is logged with its answer.

Each logged pair stays in the cache.

While the flag is down, no two cached pairs share their query or their answer.

With uniform answers from the outside oracle, the output, the cache and the flag keep their law.

A replay forking lemma rewinds a run at one query of an oracle.

So a run in this form can be rewound at a new forward query of the permutation.

Its transcript of the outside oracles follows the log of new forward pairs in lockstep.

The `k`-th answer of the outside oracle is the answer of the `k`-th pair of the log.

Just before it, the transcript holds a coin query at the code of the point of that pair.

So two runs whose transcripts agree before the `k`-th outside answer share the `k`-th point.

Answering the coins and the outside oracle with uniform draws keeps the law of a run.

A run can also stop just before a query to the outside oracle, and complete it with a given answer.

A replay fork there, with an event, is no likelier than two independent completions meeting it.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The change is the forward part of their Game G2 of Figure 7, in the proof of their Theorem 2.

Its lines 01 and 19 answer new forward queries with values `β_1, …, β_Q` drawn up front.

The inverse answers stay those of their Game G1, line 25.

Their Game G2 also changes those, in lines 26 to 28, which this run leaves out.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal

variable {A : Type}

/-- The oracles of a run in this form: coins, and one outside oracle with no input. -/
abbrev OutsideSpec (A : Type) := unifSpec + (Unit →ₒ A)

/-- The state: the cache and the flag of independent answers, then the log.

The log holds each new forward query with its answer, the first one first. -/
abbrev OutsideState (A : Type) := IndepState A × List (A × A)

variable [FinEnum A]

/-- The code of a point of `A`: its position in the enumeration of `A`.

A new forward query asks the coins at this index, so the transcript records the point. -/
abbrev queryCode (a : A) : ℕ := (FinEnum.equiv a : Fin (FinEnum.card A))

/-- The permutation oracle with independent answers, the new forward ones asked outside.

A query answered before gets its answer again, in either direction.

A new forward query first asks the coins once, at the code of its point, and drops the answer.

That marks the point in the transcript of the outside oracles.

It then asks the outside oracle once, and joins the log with its answer.

A new inverse query gets a uniform value of `A` from coins.

The cache and the flag change by the same rules as with independent answers. -/
def outsideOracle : QueryImpl (PermSpec A) (StateT (OutsideState A) (OracleComp (OutsideSpec A)))
  | .inl a => fun s =>
    match s.1.1.lookup a with
    | some b => pure (b, s)
    | none => do
      let _ ← (query (spec := OutsideSpec A) (.inl (queryCode a)) :
        OracleComp (OutsideSpec A) (Fin (queryCode a + 1)))
      (fun b : A => (b, (IndepState.addForward s.1 a b, s.2 ++ [(a, b)]))) <$>
        (query (spec := OutsideSpec A) (.inr ()) : OracleComp (OutsideSpec A) A)
  | .inr b => fun s =>
    match (s.1.1.map Prod.swap).lookup b with
    | some a => pure (a, s)
    | none =>
      (fun a => (a, (IndepState.addInverse s.1 a b, s.2))) <$>
        liftComp (uniformOutside [] b) (OutsideSpec A)

/-- The oracles of this form: coins, passed to the coins outside, then the oracle above. -/
def outsideImpl :
    QueryImpl (unifSpec + PermSpec A) (StateT (OutsideState A) (OracleComp (OutsideSpec A)))
  | .inl n => fun s =>
    (·, s) <$> (query (spec := OutsideSpec A) (.inl n) : OracleComp (OutsideSpec A) (Fin (n + 1)))
  | .inr t => outsideOracle t

/-- Each step adds at most one pair to the log, and a coin query adds none. -/
theorem length_log_le_of_mem_support_outsideImpl (t : (unifSpec + PermSpec A).Domain)
    (s : OutsideState A) (z) (hz : z ∈ support ((outsideImpl t).run s)) :
    z.2.2.length ≤ s.2.length + if t.isRight = true then 1 else 0 := by
  rcases t with n | a | b
  · simp only [outsideImpl, StateT.run, support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · simp only [outsideImpl, outsideOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨_, -, _, -, rfl⟩ := hz
      simp
  · simp only [outsideImpl, outsideOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp

/-- A run that asks the permutation at most `Q` times adds at most `Q` pairs to the log. -/
theorem length_log_le_of_mem_support_simulateQ_outsideImpl {α : Type} {oa : PermComp A α}
    {Q : ℕ} (hQ : IsQueryBoundP oa (·.isRight = true) Q) (s : OutsideState A) (z)
    (hz : z ∈ support ((simulateQ outsideImpl oa).run s)) : z.2.2.length ≤ s.2.length + Q :=
  hQ.cost_le_of_mem_support_run_simulateQ (impl := outsideImpl) (fun s => s.2.length)
    (fun t ht s w hw => by simpa [ht] using length_log_le_of_mem_support_outsideImpl t s w hw)
    (fun t ht s w hw => by simpa [ht] using length_log_le_of_mem_support_outsideImpl t s w hw)
    s z hz

/-! ## The cache and the log -/

/-- What a run with the outside oracle keeps true of its state.

Each pair of the log is a pair of the cache.

While the flag is down, no two cached pairs share their query or their answer.

The flag rises when a new answer repeats a cached value in the direction of its query. -/
def OutsideInv (s : OutsideState A) : Prop :=
  (∀ p ∈ s.2, p ∈ s.1.1) ∧ (s.1.2 = false → s.1.1.IsPartialBijection)

omit [FinEnum A] in
/-- The empty state meets the invariant. -/
theorem outsideInv_empty : OutsideInv ((([] : PermCache A), false), ([] : List (A × A))) := by
  refine ⟨fun p hp => by simp at hp, fun _ => ?_⟩
  simp [PermCache.IsPartialBijection]

/-- A lookup that finds nothing means the query is not a cached query. -/
private theorem not_mem_map_fst_of_lookup_eq_none {c : PermCache A} {a : A}
    (h : c.lookup a = none) : a ∉ c.map Prod.fst := fun ha => by
  obtain ⟨p, hp, hpa⟩ := List.mem_map.1 ha
  exact ne_of_lookup_eq_none h p hp hpa

/-- A reversed lookup that finds nothing means the answer is not a cached answer. -/
private theorem not_mem_map_snd_of_lookup_swap_eq_none {c : PermCache A} {b : A}
    (h : (c.map Prod.swap).lookup b = none) : b ∉ c.map Prod.snd := by
  have := not_mem_map_fst_of_lookup_eq_none h
  simpa [Function.comp_def] using this

/-- A new forward pair keeps the invariant. -/
private theorem outsideInv_forward {s : OutsideState A} (hs : OutsideInv s) {a b : A}
    (ha : s.1.1.lookup a = none) :
    OutsideInv ((IndepState.addForward s.1 a b, s.2 ++ [(a, b)]) : OutsideState A) := by
  obtain ⟨h1, h2⟩ := hs
  have hna := not_mem_map_fst_of_lookup_eq_none ha
  refine ⟨fun p hp => ?_, fun hf => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact List.mem_cons_of_mem _ (h1 p hp)
    · exact List.mem_cons_self
  · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
    obtain ⟨hf1, hf2⟩ := hf
    obtain ⟨hn1, hn2⟩ := h2 hf1
    exact ⟨by simpa [hna] using hn1, by simpa [hf2] using hn2⟩

/-- A new inverse pair keeps the invariant. -/
private theorem outsideInv_inverse {s : OutsideState A} (hs : OutsideInv s) {a b : A}
    (hb : (s.1.1.map Prod.swap).lookup b = none) :
    OutsideInv ((IndepState.addInverse s.1 a b, s.2) : OutsideState A) := by
  obtain ⟨h1, h2⟩ := hs
  have hnb := not_mem_map_snd_of_lookup_swap_eq_none hb
  refine ⟨fun p hp => List.mem_cons_of_mem _ (h1 p hp), fun hf => ?_⟩
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hn1, hn2⟩ := h2 hf1
  exact ⟨by simpa [hf2] using hn1, by simpa [hnb] using hn2⟩

/-- A forward query of `a` that returns `b` leaves the pair `(a, b)` in the cache. -/
theorem mem_cache_of_mem_support_outsideOracle_inl (a : A) (s : OutsideState A) (z)
    (hz : z ∈ support ((outsideOracle (.inl a)).run s)) : (a, z.1) ∈ z.2.1.1 := by
  simp only [outsideOracle, StateT.run] at hz
  split at hz
  · rename_i b hb
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact mem_of_lookup_eq_some hb
  · simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨_, -, _, -, rfl⟩ := hz
    exact List.mem_cons_self

/-- One step keeps the invariant. -/
theorem outsideInv_of_mem_support_outsideImpl (t : (unifSpec + PermSpec A).Domain)
    {s : OutsideState A} (hs : OutsideInv s) {z} (hz : z ∈ support ((outsideImpl t).run s)) :
    OutsideInv z.2 := by
  rcases t with n | a | b
  · simp only [outsideImpl, StateT.run, support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact hs
  · simp only [outsideImpl, outsideOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
    · rename_i ha
      simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨_, -, _, -, rfl⟩ := hz
      exact outsideInv_forward hs ha
  · simp only [outsideImpl, outsideOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
    · rename_i hb
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact outsideInv_inverse hs hb

/-- **A run with the outside oracle keeps the invariant.**

Each logged pair stays cached, and while the flag is down the cache is a partial bijection. -/
theorem outsideInv_of_mem_support_simulateQ_outsideImpl {α : Type} (oa : PermComp A α)
    {s : OutsideState A} (hs : OutsideInv s) {z : α × OutsideState A}
    (hz : z ∈ support ((simulateQ outsideImpl oa).run s)) : OutsideInv z.2 := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz'⟩ := hz
    exact ih w.1 (outsideInv_of_mem_support_outsideImpl t hs hw) hz'

/-! ## The transcript of the outside oracles -/

/-- An entry of the transcript of the outside oracles: a query and its answer. -/
abbrev OutsideEntry (A : Type) := (t : (OutsideSpec A).Domain) × (OutsideSpec A).Range t

/-- The transcript of a run, given the new forward pairs that the run logged, the first one first.

Each other coin query of the run adds one entry with its index and its answer.

Each new forward pair `(a, b)` adds two entries: a coin query at the code of `a`, then `b`.

The transcript holds nothing else. -/
inductive OutsideTranscript : List (A × A) → List (OutsideEntry A) → Prop
  /-- The empty run. -/
  | nil : OutsideTranscript [] []
  /-- A coin query, with its index and its answer, before the rest of the run. -/
  | coin {new : List (A × A)} {log : List (OutsideEntry A)} (n : ℕ) (u : Fin (n + 1)) :
      OutsideTranscript new log → OutsideTranscript new (⟨.inl n, u⟩ :: log)
  /-- A new forward pair `(a, b)`, before the rest of the run. -/
  | forward {new : List (A × A)} {log : List (OutsideEntry A)} (a b : A)
      (u : Fin (queryCode a + 1)) :
      OutsideTranscript new log →
        OutsideTranscript ((a, b) :: new) (⟨.inl (queryCode a), u⟩ :: ⟨.inr (), b⟩ :: log)

/-- Two runs, one after the other, have the transcripts and the logs of both, in order. -/
theorem OutsideTranscript.append {new₁ new₂ : List (A × A)} {log₁ log₂ : List (OutsideEntry A)}
    (h₁ : OutsideTranscript new₁ log₁) (h₂ : OutsideTranscript new₂ log₂) :
    OutsideTranscript (new₁ ++ new₂) (log₁ ++ log₂) := by
  induction h₁ with
  | nil => exact h₂
  | coin n u _ ih => exact .coin n u ih
  | forward a b u _ ih => exact .forward a b u ih

/-- The answers of the outside oracle in a transcript are the answers of the log, in order. -/
theorem OutsideTranscript.getQ_inr {new : List (A × A)} {log : QueryLog (OutsideSpec A)}
    (h : OutsideTranscript new log) :
    log.getQ (· = .inr ()) = new.map fun p => (⟨.inr (), p.2⟩ : OutsideEntry A) := by
  induction h with
  | nil => rfl
  | coin n u _ ih => simp [QueryLog.getQ_cons, ih]
  | forward a b u _ ih => simp [QueryLog.getQ_cons, ih]

/-- The `k`-th answer of the outside oracle is the answer of the `k`-th pair of the log. -/
theorem OutsideTranscript.getQueryValue?_inr {new : List (A × A)}
    {log : QueryLog (OutsideSpec A)} (h : OutsideTranscript new log) (k : ℕ) :
    log.getQueryValue? (.inr ()) k = new[k]?.map Prod.snd := by
  unfold QueryLog.getQueryValue?
  rw [h.getQ_inr, List.getElem?_map]
  cases new[k]? <;> rfl

/-- The outside oracle answers as many times as the log has pairs. -/
theorem OutsideTranscript.countQ_inr {new : List (A × A)} {log : QueryLog (OutsideSpec A)}
    (h : OutsideTranscript new log) : log.countQ (· = .inr ()) = new.length := by
  simp [QueryLog.countQ, h.getQ_inr]

/-- Cut a transcript just before an answer of the outside oracle, with `k` answers before the cut.

The `k`-th pair of the log is some `(a, b)`, and the last entry before the cut asks the code of `a`.
-/
private theorem OutsideTranscript.getLast?_of_eq_append_aux {new : List (A × A)}
    {log : QueryLog (OutsideSpec A)} (h : OutsideTranscript new log)
    {p rest : QueryLog (OutsideSpec A)} {v : A} (hlog : log = p ++ ⟨.inr (), v⟩ :: rest) :
    ∃ (a b : A) (u : Fin (queryCode a + 1)), new[p.countQ (· = .inr ())]? = some (a, b) ∧
      p.getLast? = some ⟨.inl (queryCode a), u⟩ := by
  induction h generalizing p with
  | nil => simp at hlog
  | coin n u _ ih =>
    rcases p with _ | ⟨e, p⟩
    · simp at hlog
    · simp only [List.cons_append, List.cons.injEq] at hlog
      obtain ⟨rfl, hlog⟩ := hlog
      obtain ⟨a, b, u', hk, hl⟩ := ih hlog
      refine ⟨a, b, u', by simpa using hk, ?_⟩
      simp [List.getLast?_cons, hl]
  | forward a b u _ ih =>
    rcases p with _ | ⟨e, _ | ⟨e', p⟩⟩
    · simp at hlog
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hlog
      obtain ⟨rfl, -, -⟩ := hlog
      exact ⟨a, b, u, rfl, rfl⟩
    · simp only [List.cons_append, List.cons.injEq] at hlog
      obtain ⟨rfl, rfl, hlog⟩ := hlog
      obtain ⟨a', b', u', hk, hl⟩ := ih hlog
      refine ⟨a', b', u', by simpa using hk, ?_⟩
      simp [List.getLast?_cons, hl]

/-- Cut a transcript just before an answer of the outside oracle.

Say `k` outside answers come before the cut.

Then the log has a `k`-th pair, and the last entry before the cut is a coin query at its code. -/
theorem OutsideTranscript.getLast?_of_eq_append {new : List (A × A)}
    {log : QueryLog (OutsideSpec A)} (h : OutsideTranscript new log)
    {p rest : QueryLog (OutsideSpec A)} {v : A} (hlog : log = p ++ ⟨.inr (), v⟩ :: rest) :
    ∃ hk : p.countQ (· = .inr ()) < new.length,
      ∃ u : Fin (queryCode new[p.countQ (· = .inr ())].1 + 1),
        p.getLast? = some ⟨.inl (queryCode new[p.countQ (· = .inr ())].1), u⟩ := by
  obtain ⟨a, b, u, hk, hl⟩ := h.getLast?_of_eq_append_aux hlog
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hk
  refine ⟨hlt, ?_⟩
  rw [heq]
  exact ⟨u, hl⟩

/-- A run of coins alone, lifted to the outside oracles, has a transcript and logs no pair. -/
theorem outsideTranscript_of_mem_support_withQueryLog_liftComp {β : Type} (pc : ProbComp β)
    {z : β} {log : QueryLog (OutsideSpec A)}
    (h : (z, log) ∈ support (OracleComp.withQueryLog (liftComp pc (OutsideSpec A)))) :
    OutsideTranscript [] log := by
  induction pc using OracleComp.inductionOn generalizing z log with
  | pure x =>
    simp only [liftComp_pure, OracleComp.withQueryLog_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at h
    exact h.2 ▸ .nil
  | query_bind t k ih =>
    have hq : (liftM (unifSpec.query t) : OracleComp (OutsideSpec A) (unifSpec.Range t)) =
        liftM ((OutsideSpec A).query (.inl t)) := rfl
    rw [liftComp_bind, liftComp_liftM_query, hq, OracleComp.withQueryLog_bind,
      OracleComp.withQueryLog_query] at h
    simp only [bind_pure_comp, support_bind, support_map, Set.mem_iUnion,
      Set.mem_image] at h
    obtain ⟨_, ⟨u, -, rfl⟩, ⟨z', l'⟩, hl', hzl⟩ := h
    simp only [Prod.map, id, Prod.mk.injEq] at hzl
    obtain ⟨rfl, rfl⟩ := hzl
    exact .coin t u (ih u hl')

omit [FinEnum A] in
/-- Mapping the output of a run leaves its transcript of queries unchanged. -/
private theorem withQueryLog_map {β γ : Type} (f : β → γ) (mx : OracleComp (OutsideSpec A) β) :
    (f <$> mx).withQueryLog = Prod.map f id <$> mx.withQueryLog := by
  rw [map_eq_bind_pure_comp, OracleComp.withQueryLog_bind]
  simp only [Function.comp_apply, OracleComp.withQueryLog_pure, map_pure, bind_pure_comp]
  congr 1
  funext p
  simp [Prod.map]

omit [FinEnum A] in
/-- One query to the outside oracles logs itself with its answer. -/
private theorem withQueryLog_query_outside (t : (OutsideSpec A).Domain) :
    (query (spec := OutsideSpec A) t : OracleComp (OutsideSpec A) _).withQueryLog =
      (query (spec := OutsideSpec A) t : OracleComp (OutsideSpec A) _) >>=
        fun u => pure (u, [⟨t, u⟩]) :=
  OracleComp.withQueryLog_query t

/-- One step extends the log by some pairs, and its transcript is the one of those pairs. -/
private theorem outsideTranscript_of_mem_support_withQueryLog_outsideImpl
    (t : (unifSpec + PermSpec A).Domain) (s : OutsideState A) {z : _ × OutsideState A}
    {log : QueryLog (OutsideSpec A)}
    (h : (z, log) ∈ support (OracleComp.withQueryLog ((outsideImpl t).run s))) :
    ∃ new, z.2.2 = s.2 ++ new ∧ OutsideTranscript new log := by
  rcases t with n | a | b
  · simp only [outsideImpl, StateT.run, withQueryLog_map] at h
    erw [withQueryLog_query_outside] at h
    simp only [support_map, support_bind, support_pure, Set.mem_image, Set.mem_iUnion,
      Set.mem_singleton_iff] at h
    obtain ⟨_, ⟨u, -, rfl⟩, hz⟩ := h
    simp only [Prod.map, id, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨[], by simp, .coin n u .nil⟩
  · simp only [outsideImpl, outsideOracle, StateT.run] at h
    split at h
    · simp only [OracleComp.withQueryLog_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], by simp, .nil⟩
    · rw [OracleComp.withQueryLog_bind, withQueryLog_map] at h
      erw [withQueryLog_query_outside, withQueryLog_query_outside] at h
      simp only [bind_pure_comp, support_bind, support_map, Set.mem_iUnion,
        Set.mem_image] at h
      obtain ⟨_, ⟨u, -, rfl⟩, _, ⟨_, ⟨b, -, rfl⟩, rfl⟩, hz⟩ := h
      simp only [Prod.map, id, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨[(a, b)], rfl, .forward a b u .nil⟩
  · simp only [outsideImpl, outsideOracle, StateT.run] at h
    split at h
    · simp only [OracleComp.withQueryLog_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], by simp, .nil⟩
    · rw [withQueryLog_map] at h
      simp only [support_map, Set.mem_image] at h
      obtain ⟨⟨c, l⟩, hl, hz⟩ := h
      simp only [Prod.map, id, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨[], by simp, outsideTranscript_of_mem_support_withQueryLog_liftComp _ hl⟩

/-- **The transcript follows the log of new forward pairs in lockstep.**

Run a program from a state `s`, with the transcript of the outside oracles.

The run extends the log of `s` by some pairs, and its transcript is the one of those pairs. -/
theorem outsideTranscript_of_mem_support_withQueryLog {α : Type} (oa : PermComp A α)
    (s : OutsideState A) {z : α × OutsideState A} {log : QueryLog (OutsideSpec A)}
    (h : (z, log) ∈ support (OracleComp.withQueryLog ((simulateQ outsideImpl oa).run s))) :
    ∃ new, z.2.2 = s.2 ++ new ∧ OutsideTranscript new log := by
  induction oa using OracleComp.inductionOn generalizing s z log with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, OracleComp.withQueryLog_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, .nil⟩
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, OracleComp.withQueryLog_bind, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image] at h
    obtain ⟨⟨w, l₁⟩, hw, ⟨z', l₂⟩, hz', hz⟩ := h
    simp only [Prod.map, id, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    obtain ⟨new₁, hnew₁, htr₁⟩ :=
      outsideTranscript_of_mem_support_withQueryLog_outsideImpl t s hw
    obtain ⟨new₂, hnew₂, htr₂⟩ := ih w.1 w.2 hz'
    exact ⟨new₁ ++ new₂, by rw [hnew₂, hnew₁, List.append_assoc], htr₁.append htr₂⟩

variable [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

omit [FinEnum A] in
/-- The outside oracle, with uniform answers, is a uniform value of `A`. -/
theorem query_outside_evalDistEq :
    EvalDistEq (query (spec := OutsideSpec A) (.inr ()) : OracleComp (OutsideSpec A) A)
      ($ᵗ A : ProbComp A) := by
  let : MeasurableSpace A := ⊤
  have : DiscreteMeasurableSpace A := ⟨fun _ => trivial⟩
  refine EvalDistEq.of_evalDist_eq (α := A) ?_
  rw [SampleableType.evalDist_uniformSample]
  exact evalDist_query_uniform (spec := OutsideSpec A) (.inr ())

omit [FinEnum A] [SampleableType A] in
/-- A value returned outright has the same law in both runs. -/
theorem pure_outside_evalDistEq {α : Type} (x : α) :
    EvalDistEq (pure x : OracleComp (OutsideSpec A) α) (pure x : ProbComp α) :=
  EvalDistEq.of_forall_prEvent_eq fun p => by
    classical
    rw [prEvent_pure, prEvent_pure]

/-- With the log dropped, each step has the law of the step with independent answers. -/
theorem outsideImpl_run_evalDistEq (t : (unifSpec + PermSpec A).Domain) (s : IndepState A)
    (l : List (A × A)) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (outsideImpl t).run (s, l))
      ((indepPermImpl t).run s) := by
  obtain ⟨c, f⟩ := s
  rcases t with n | a | b
  · rw [passthrough_add_inl_run]
    simp only [outsideImpl, StateT.run, Functor.map_map]
    exact (evalDistEq_liftM_query_uniform (spec := unifSpec) (superSpec := OutsideSpec A) n).map _
  · rw [indepPermImpl_inr, indepPermOracle_inl_run]
    simp only [outsideImpl, outsideOracle, StateT.run]
    cases c.lookup a with
    | some b => simpa only [map_pure] using pure_outside_evalDistEq _
    | none =>
      simp only [map_bind, Functor.map_map]
      exact (EvalDistEq.bind_const _ _).trans
        ((query_outside_evalDistEq.trans (uniformOutside_nil_evalDistEq a).symm).map _)
  · rw [indepPermImpl_inr, indepPermOracle_inr_run]
    simp only [outsideImpl, outsideOracle, StateT.run]
    cases (c.map Prod.swap).lookup b with
    | some a => simpa only [map_pure] using pure_outside_evalDistEq _
    | none =>
      simp only [Functor.map_map]
      exact (evalDistEq_liftComp_uniform _).map _

/-- **Asking new forward answers outside keeps the law of the run with independent answers.**

Drop the log at the end: the output, the cache and the flag have the same law. -/
theorem simulateQ_outsideImpl_run_evalDistEq {α : Type} (oa : PermComp A α) (s : IndepState A)
    (l : List (A × A)) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (simulateQ outsideImpl oa).run (s, l))
      ((simulateQ indepPermImpl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s l with
  | pure x => simpa only [simulateQ_pure, StateT.run_pure, map_pure] using pure_outside_evalDistEq _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, map_bind]
    refine (EvalDistEq.bind_right ((outsideImpl t).run (s, l))
      (g := fun z => liftComp ((simulateQ indepPermImpl (k z.1)).run z.2.1) (OutsideSpec A))
      fun z => ?_).trans ?_
    · simpa only [Prod.mk.eta] using
        (ih z.1 z.2.1 z.2.2).trans (evalDistEq_liftComp_uniform _).symm
    · have h := (outsideImpl_run_evalDistEq t s l).bind
        (f := fun z => liftComp ((simulateQ indepPermImpl (k z.1)).run z.2) (OutsideSpec A))
        (g := fun z => (simulateQ indepPermImpl (k z.1)).run z.2)
        fun _ => evalDistEq_liftComp_uniform _
      simpa only [bind_map_left] using h

/-! ## The oracles answered by uniform draws, and the stopped run -/

omit [FinEnum A] [UniformAnswerMeasure (Unit →ₒ A)] in
/-- The oracles of the run with the outside oracle: coins passed through, and uniform answers. -/
abbrev outsideSample : QueryImpl (OutsideSpec A) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := (Unit →ₒ A))

omit [FinEnum A] in
/-- The coins and the uniform answers have the law of the outside oracles. -/
theorem simulateQ_outsideSample_evalDistEq {α : Type}
    (oa : OracleComp (OutsideSpec A) α) :
    EvalDistEq (m' := OracleComp (OutsideSpec A)) (simulateQ outsideSample oa) oa := by
  let : MeasurableSpace α := ⊤
  refine EvalDistEq.of_evalDist_eq
    (evalDist_simulateQ_eq_of_forall (spec := OutsideSpec A) outsideSample (fun t => ?_) oa)
  rw [OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn]
  rcases t with n | u
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
    exact evalDist_liftM_query_uniform (spec := unifSpec) n
  · let : MeasurableSpace A := ⊤
    let : MeasurableSpace ((OutsideSpec A).Range (.inr u)) := ‹MeasurableSpace A›
    simp only [QueryImpl.add_apply_inr, uniformSampleImpl_apply]
    exact SampleableType.evalDist_uniformSample

omit [FinEnum A] in
/-- An event of a run of the outside oracles has the same chance once the oracles are sampled. -/
theorem prEvent_simulateQ_outsideSample (X : OracleComp (OutsideSpec A) Prop) :
    prEvent (simulateQ outsideSample X) = prEvent X := by
  have h := (simulateQ_outsideSample_evalDistEq X).prEvent_eq (fun e => e)
  simpa only [id_map'] using h

omit [FinEnum A] in
/-- The outputs of a run of the outside oracles do not change once the oracles are sampled. -/
theorem support_simulateQ_outsideSample {α : Type}
    (oa : OracleComp (OutsideSpec A) α) :
    support (simulateQ outsideSample oa) = support oa := by
  let : MeasurableSpace α := ⊤
  ext y
  rw [mem_support_iff_evalDist_singleton_pos, mem_support_iff_evalDist_singleton_pos,
    (simulateQ_outsideSample_evalDistEq oa).evalDist_eq]

omit [FinEnum A] [UniformAnswerMeasure (Unit →ₒ A)] in
/-- Completing a query to the outside oracle draws a uniform answer, then completes with it. -/
theorem simulateQ_outsideSample_complete {α : Type} {main : OracleComp (OutsideSpec A) α} {n : ℕ}
    (occ : PFunctor.FreeM.Cursor.Occurrence (P := (OutsideSpec A).toPFunctor) (.inr ()) main n) :
    simulateQ outsideSample (occ.complete : OracleComp (OutsideSpec A) _) =
      $ᵗ A >>= fun a =>
        simulateQ outsideSample (occ.completeWith a : OracleComp (OutsideSpec A) _) := by
  rw [PFunctor.FreeM.Cursor.Occurrence.complete_eq_liftBind]
  change simulateQ outsideSample ((liftM ((OutsideSpec A).query (.inr ())) :
    OracleComp (OutsideSpec A) _) >>= occ.completeWith) = _
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

omit [FinEnum A] [UniformAnswerMeasure (Unit →ₒ A)] in
/-- A completion with a given answer keeps that answer. -/
theorem answer_of_mem_support_simulateQ_completeWith {α : Type}
    {main : OracleComp (OutsideSpec A) α} {n : ℕ}
    (occ : PFunctor.FreeM.Cursor.Occurrence (P := (OutsideSpec A).toPFunctor) (.inr ()) main n)
    {a : A} {c : occ.Completion}
    (hc : c ∈ support
      (simulateQ outsideSample (occ.completeWith a : OracleComp (OutsideSpec A) _))) :
    c.answer = a := by
  change c ∈ support (simulateQ outsideSample
    ((PFunctor.FreeM.Cursor.Occurrence.Completion.mk a) <$>
      (PFunctor.FreeM.withPath (occ.resume a) : OracleComp (OutsideSpec A) _))) at hc
  rw [simulateQ_map, support_map] at hc
  obtain ⟨_, -, rfl⟩ := hc
  rfl

/-- Binds with pointwise equal events, the second one already a proposition. -/
private theorem prEvent_bind_congr_prop {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {β γ : Type} (mx : m β)
    (f : β → m γ) (g : β → m Prop) (p : γ → Prop)
    (h : ∀ x, Pr{let y ← f x}[p y] = prEvent (g x)) :
    Pr{let y ← mx >>= f}[p y] = prEvent (mx >>= g) :=
  (prEvent_bind_congr mx f g p (fun e => e) fun x => by simpa using h x).trans (by simp)

omit [SampleableType A] in
/-- **A fork at index `s` is no likelier than two completions of the run stopped at `s`.**

Take the event that the fork succeeds, its first output has fork index `s`, and `D` holds.

Stop the run before its query to the outside oracle that follows `s` earlier ones.

Complete that query twice, independently.

The event is at most as likely as both completions having fork index `s` with `D`. -/
theorem prEvent_contextFork_le_splitAt {α : Type}
    (main : OracleComp (OutsideSpec A) α) (qb : ℕ ⊕ Unit → ℕ)
    (cf : α → Option (Fin (qb (.inr ()) + 1))) (s : Fin (qb (.inr ()) + 1))
    (D : α → α → Prop)
    (cont : PFunctor.FreeM.Cursor.Split (P := (OutsideSpec A).toPFunctor) (.inr ()) main s →
      OracleComp (OutsideSpec A) Prop)
    (hk₁ : ∀ path, cont (.missing path) = pure False)
    (hk₂ : ∀ occ, cont (.found occ) = do
      let c₁ ← occ.complete
      let c₂ ← occ.complete
      pure (cf (PFunctor.FreeM.output main c₁.path) = some s ∧
        cf (PFunctor.FreeM.output main c₂.path) = some s ∧
        D (PFunctor.FreeM.output main c₁.path) (PFunctor.FreeM.output main c₂.path))) :
    Pr{let r ← contextFork main qb (.inr ()) cf}[
      ∃ x₁ x₂, r = some (x₁, x₂) ∧ cf x₁ = some s ∧ D x₁ x₂] ≤
    prEvent (PFunctor.FreeM.Cursor.splitAt (P := (OutsideSpec A).toPFunctor) (.inr ()) main s >>=
      cont) := by
  classical
  let Fv : Option (PFunctor.FreeM.Cursor.ForkView (P := (OutsideSpec A).toPFunctor) (.inr ())
      main s) → Prop := fun v? => ∃ v, v? = some v ∧
    cf (PFunctor.FreeM.output main v.firstPath) = some s ∧
    cf (PFunctor.FreeM.output main v.secondPath) = some s ∧
    D (PFunctor.FreeM.output main v.firstPath) (PFunctor.FreeM.output main v.secondPath)
  have hR : Pr{let v ← (PFunctor.FreeM.Cursor.forkAt (P := (OutsideSpec A).toPFunctor) (.inr ())
      main s : OracleComp (OutsideSpec A) _)}[Fv v] =
    prEvent (PFunctor.FreeM.Cursor.splitAt (P := (OutsideSpec A).toPFunctor) (.inr ()) main s >>=
      cont) := by
    unfold PFunctor.FreeM.Cursor.forkAt
    refine prEvent_bind_congr_prop (m := OracleComp (OutsideSpec A)) _ _ _ _ fun sp => ?_
    cases sp with
    | missing path =>
      rw [PFunctor.FreeM.Cursor.Split.completeFork_missing, hk₁]
      simp [Fv]
    | found occ =>
      rw [PFunctor.FreeM.Cursor.Split.completeFork_found, hk₂]
      refine prEvent_bind_congr_prop (m := OracleComp (OutsideSpec A)) _ _ _ _ fun c₁ => ?_
      rw [bind_pure_comp]
      refine (prEvent_map (m := OracleComp (OutsideSpec A)) occ.complete _ _).trans
        (prEvent_congr _ _ _ fun c₂ => ?_)
      simp [Fv, PFunctor.FreeM.Cursor.ForkView.firstPath, PFunctor.FreeM.Cursor.ForkView.secondPath]
  rw [← hR, PFunctor.FreeM.Cursor.forkAt_eq_locateAndForkAt]
  rw [show contextFork main qb (.inr ()) cf =
    Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs <$>
      contextForkWitness main qb (.inr ()) cf from rfl, prEvent_map]
  unfold contextForkWitness
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete]
  unfold PFunctor.FreeM.Cursor.locateAndForkAt
  refine prEvent_bind_mono_of_forall_le (OracleComp.ofFreeM _) _ _ _ _ fun path => ?_
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | k
  · dsimp only
    rw [prEvent_pure]
    simp
  by_cases hks : k = s
  · subst hks
    dsimp only
    rcases hloc : PFunctor.FreeM.Cursor.locateAt? (P := (OutsideSpec A).toPFunctor) (.inr ())
        main path k with _ | located
    · dsimp only
      rw [prEvent_pure]
      simp
    · dsimp only
      rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete]
      refine ((prEvent_map (m := OracleComp (OutsideSpec A)) located.occurrence.complete _
        _).trans_le (prEvent_mono _ _ _ fun second h => ?_)).trans_eq
        ((prEvent_map (m := OracleComp (OutsideSpec A)) _ _ _).trans
          (prEvent_map (m := OracleComp (OutsideSpec A)) _ _ _)).symm
      obtain ⟨x₁, x₂, hm, -, hD⟩ := h
      simp only [acceptContextForkWitness, classifyForkView] at hm
      by_cases ha : located.completion.answer = second.answer
      · simp [ha] at hm
      by_cases hc : cf (PFunctor.FreeM.output main located.completion.path) = some k ∧
          cf (PFunctor.FreeM.output main second.path) = some k
      · simp only [PFunctor.FreeM.Cursor.ForkView.firstAnswer,
          PFunctor.FreeM.Cursor.ForkView.secondAnswer, PFunctor.FreeM.Cursor.ForkView.firstPath,
          PFunctor.FreeM.Cursor.ForkView.secondPath, ha, hc, ite_false, ite_true, and_self,
          Option.isSome_some, Option.map_some, Option.some.injEq] at hm
        simp only [PFunctor.FreeM.Cursor.SelectedForkView.outputs_mk, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact ⟨_, rfl, hc.1, hc.2, hD⟩
      · simp [PFunctor.FreeM.Cursor.ForkView.firstAnswer,
          PFunctor.FreeM.Cursor.ForkView.secondAnswer, PFunctor.FreeM.Cursor.ForkView.firstPath,
          PFunctor.FreeM.Cursor.ForkView.secondPath, ha, hc] at hm
  · dsimp only
    refine le_of_eq_of_le ?_ zero_le
    rcases hloc : PFunctor.FreeM.Cursor.locateAt? (P := (OutsideSpec A).toPFunctor) (.inr ())
        main path k with _ | located
    · dsimp only
      rw [prEvent_pure]
      simp
    · dsimp only
      refine (prEvent_map (m := OracleComp (OutsideSpec A)) located.occurrence.complete _ _).trans
        (prEvent_eq_zero_of_forall_not _ _ fun second h => ?_)
      obtain ⟨x₁, x₂, hm, hs, -⟩ := h
      simp only [acceptContextForkWitness, classifyForkView] at hm
      by_cases ha : located.completion.answer = second.answer
      · simp [ha] at hm
      by_cases hc : cf (PFunctor.FreeM.output main located.completion.path) = some k ∧
          cf (PFunctor.FreeM.output main second.path) = some k
      · simp only [PFunctor.FreeM.Cursor.ForkView.firstAnswer,
          PFunctor.FreeM.Cursor.ForkView.secondAnswer, PFunctor.FreeM.Cursor.ForkView.firstPath,
          PFunctor.FreeM.Cursor.ForkView.secondPath, ha, hc, ite_false, ite_true, and_self,
          Option.isSome_some, Option.map_some, Option.some.injEq,
          PFunctor.FreeM.Cursor.SelectedForkView.outputs_mk, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact hks (Option.some.inj (hc.1.symm.trans hs))
      · simp [PFunctor.FreeM.Cursor.ForkView.firstAnswer,
          PFunctor.FreeM.Cursor.ForkView.secondAnswer, PFunctor.FreeM.Cursor.ForkView.firstPath,
          PFunctor.FreeM.Cursor.ForkView.secondPath, ha, hc] at hm

omit [FinEnum A] in
/-- An event of two completions of the run stopped at `n` keeps its chance with sampled oracles. -/
theorem prEvent_splitAt_eq_sample {α : Type}
    (main : OracleComp (OutsideSpec A) α) (n : ℕ) (P : α → α → Prop)
    (k : PFunctor.FreeM.Cursor.Split (P := (OutsideSpec A).toPFunctor) (.inr ()) main n →
      OracleComp (OutsideSpec A) Prop)
    (hk₁ : ∀ path, k (.missing path) = pure False)
    (hk₂ : ∀ occ, k (.found occ) = do
      let c₁ ← occ.complete
      let c₂ ← occ.complete
      pure (P (PFunctor.FreeM.output main c₁.path) (PFunctor.FreeM.output main c₂.path)))
    (k' : PFunctor.FreeM.Cursor.Split (P := (OutsideSpec A).toPFunctor) (.inr ()) main n →
      ProbComp Prop)
    (hk'₁ : ∀ path, k' (.missing path) = pure False)
    (hk'₂ : ∀ occ, k' (.found occ) = do
      let a₁ ← $ᵗ A
      let c₁ ← simulateQ outsideSample (occ.completeWith a₁)
      let a₂ ← $ᵗ A
      let c₂ ← simulateQ outsideSample (occ.completeWith a₂)
      pure (P (PFunctor.FreeM.output main c₁.path) (PFunctor.FreeM.output main c₂.path))) :
    prEvent (PFunctor.FreeM.Cursor.splitAt (P := (OutsideSpec A).toPFunctor) (.inr ()) main n >>=
      k) =
    prEvent (simulateQ outsideSample
      (PFunctor.FreeM.Cursor.splitAt (P := (OutsideSpec A).toPFunctor) (.inr ()) main n) >>=
      k') := by
  rw [← prEvent_simulateQ_outsideSample, simulateQ_bind]
  refine congrArg prEvent (bind_congr fun sp => ?_)
  cases sp with
  | missing path => rw [hk₁, hk'₁]; rfl
  | found occ =>
    rw [hk₂, hk'₂]
    simp [simulateQ_outsideSample_complete]

end EthLib.Cryptography.LazyPermutation
