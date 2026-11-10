module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnly
public import EthLib.Cryptography.Proofs.IndependentOutside
public import VCVio.CryptoFoundations.ReplayFork

/-!
# Proofs: the key-only game with new forward answers asked of one oracle

Run the key-only forger on a fixed key, with independent answers to `Π`.

Ask each new forward answer of one outside oracle with no input, and log it with its query.

The run then ends with the forgery, the result of the check, the cache, the flag and the log.

With the key drawn uniformly, it wins with the chance of the game with independent answers.

The run logs at most one more pair than the forger asks for `Π` or its inverse.

When the outside oracle answered the conversion of a forgery, a replay fork can rewind there.

The fork index is the position of the forgery's point in the log of new forward pairs.

The new forward queries of both runs at that index then share the point and differ in answer.

The forking lemma bounds the chance of such a fork from below.

A later proof can split forgeries from forward and inverse pairs on this run.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The run is their Game G1 of Figure 7, in the proof of their Theorem 2.

It takes the forward change of their Game G2, lines 01 and 19: the values `β_1, …, β_Q`.

Here each is asked of the outside oracle when needed.

Their Game G2 also changes the inverse answers, in lines 26 to 28, which this run leaves out.

Their `Q` counts the query of the conversion, which their forger asks first.

Here the check may ask it, hence one more pair.

The fork is the forking algorithm of their Figure 2, on an analogue of their Figure 8.

In that analogue, a forgery on an inverse pair gives no fork index.

Their Lemma 1 is the general forking lemma of Bellare and Neven.

The fork here reruns the run from the selected query on, with fresh answers and fresh coins.

Its bound has the form of their Lemma 1 for one fixed key, with `q + 1` for `Q` and `|A|` for `|B|`.

Their Lemma 1 draws the key at random; no theorem averages over the key yet.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- The end of a run of a key-only forger with new forward answers asked outside. -/
structure KeyOnlyTrace (F A M : Type) where
  /-- The message and the claimed signature `(t, s)`. -/
  forgery : M × F × F
  /-- Whether the check of the forgery passed. -/
  verified : Bool
  /-- The pairs of `Π` answered, the most recent first. -/
  cache : PermCache A
  /-- Whether a new answer repeated a cached value in the direction of its query. -/
  bad : Bool
  /-- The new forward queries with their answers, the first one first. -/
  forward : List (A × A)

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

variable [FinEnum A]

/-- The run on the key `X`, with new forward answers asked outside, from the empty state. -/
def keyOnlyOutsideRun (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) (X : G) :
    OracleComp (OutsideSpec A) (KeyOnlyTrace F A M) :=
  (fun r => ⟨r.1.1, r.1.2, r.2.1.1, r.2.1.2, r.2.2⟩) <$>
    (simulateQ outsideImpl (keyOnlyRunQ scheme adversary X)).run (([], false), [])

/-- The run logs at most `q + 1` pairs.

Take a forger that asks for `Π` or its inverse at most `q` times on the key `X`. -/
theorem length_forward_le_of_mem_support_keyOnlyOutsideRun (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {q : ℕ}
    (hq : IsQueryBoundP (adversary.main X) (·.isRight = true) q)
    {tr : KeyOnlyTrace F A M} (htr : tr ∈ support (keyOnlyOutsideRun scheme adversary X)) :
    tr.forward.length ≤ q + 1 := by
  simp only [keyOnlyOutsideRun, support_map, Set.mem_image] at htr
  obtain ⟨r, hr, rfl⟩ := htr
  simpa using length_log_le_of_mem_support_simulateQ_outsideImpl
    (isQueryBoundP_keyOnlyRunQ scheme adversary X hq) _ r hr

/-! ## The fork at the forgery's point -/

/-- The point at which the check of a forgery `(m, t, s)` asks `Π`, on the key `X`.

It is the encoding of `U / s`, where `U = H(m) g + t X`. -/
def forgeryPoint (scheme : Scheme F G A M) (X : G) (z : M × F × F) : A :=
  scheme.encode (z.2.2⁻¹ • (scheme.hash z.1 • scheme.g + z.2.1 • X))

/-- The bound on each oracle index that the fork reads: `q` for the outside oracle.

The fork reads only the outside oracle, so the bound on the coins is never used. -/
def forkBound (q : ℕ) : ℕ ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr () => q

/-- The fork index of a run: the position of the forgery's point in the log of new forward pairs.

It is `none` unless the check passed with no flag raised.

It is also `none` when the point is not in the log, or not among its first `q + 1` pairs. -/
def forkIndex (scheme : Scheme F G A M) (X : G) (q : ℕ) (tr : KeyOnlyTrace F A M) :
    Option (Fin (forkBound q (.inr ()) + 1)) :=
  if tr.verified && !tr.bad then
    match tr.forward.findIdx? fun p => decide (p.1 = forgeryPoint scheme X tr.forgery) with
    | some j => if h : j < q + 1 then some ⟨j, h⟩ else none
    | none => none
  else none

omit [DecidableEq F] [DecidableEq G] in
/-- A run with a fork index passed the check with no flag raised.

The pair of the log at that index is a new forward query at the forgery's point. -/
theorem verified_and_forward_of_forkIndex_eq_some {scheme : Scheme F G A M} {X : G} {q : ℕ}
    {tr : KeyOnlyTrace F A M} {j : Fin (forkBound q (.inr ()) + 1)}
    (h : forkIndex scheme X q tr = some j) :
    tr.verified = true ∧ tr.bad = false ∧
      ∃ hj : (j : ℕ) < tr.forward.length, tr.forward[j].1 = forgeryPoint scheme X tr.forgery := by
  unfold forkIndex at h
  split_ifs at h with hv
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hv
  refine ⟨hv.1, hv.2, ?_⟩
  split at h
  · rename_i k hk
    split_ifs at h with hkq
    cases h
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
    exact ⟨hlt, by simpa using hp⟩
  · cases h

/-- The transcript of a run of the outside oracles is the one of its log of new forward pairs. -/
theorem outsideTranscript_of_mem_support_keyOnlyOutsideRun (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {tr : KeyOnlyTrace F A M}
    {log : QueryLog (OutsideSpec A)}
    (h : (tr, log) ∈ support (replayFirstRun (keyOnlyOutsideRun scheme adversary X))) :
    OutsideTranscript tr.forward log := by
  rw [replayFirstRun, keyOnlyOutsideRun, map_eq_bind_pure_comp,
    OracleComp.withQueryLog_bind] at h
  simp only [Function.comp_apply, OracleComp.withQueryLog_pure, map_pure, support_bind,
    support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  obtain ⟨⟨r, l⟩, hr, hz⟩ := h
  simp only [Prod.map, id, Prod.mk.injEq, List.append_nil] at hz
  obtain ⟨rfl, rfl⟩ := hz
  obtain ⟨new, hnew, htr⟩ := outsideTranscript_of_mem_support_withQueryLog _ _ hr
  simpa [hnew] using htr

/-- The fork index of a run always points at a query of the outside oracle in its transcript. -/
theorem cfReachable_forkIndex (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M)
    (X : G) (q : ℕ) :
    CfReachable (keyOnlyOutsideRun scheme adversary X) (forkBound q) (.inr ())
      (forkIndex scheme X q) := by
  intro tr log h j hj
  obtain ⟨-, -, hlt, -⟩ := verified_and_forward_of_forkIndex_eq_some hj
  have htr := outsideTranscript_of_mem_support_keyOnlyOutsideRun scheme adversary X h
  rw [htr.getQueryValue?_inr, List.getElem?_eq_getElem hlt]
  rfl

/-- **Both runs of the fork ask `Π` at the same point, and get different answers.**

Take two runs that the fork returns, on the key `X`.

They have the same fork index `j`.

Their `j`-th new forward pairs have the same point and different answers. -/
theorem forward_point_eq_answer_ne_of_mem_support_contextFork (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (q : ℕ) {tr₁ tr₂ : KeyOnlyTrace F A M}
    (h : some (tr₁, tr₂) ∈ support
      (contextFork (keyOnlyOutsideRun scheme adversary X) (forkBound q) (.inr ())
        (forkIndex scheme X q))) :
    ∃ j, forkIndex scheme X q tr₁ = some j ∧ forkIndex scheme X q tr₂ = some j ∧
      ∃ (h₁ : (j : ℕ) < tr₁.forward.length) (h₂ : (j : ℕ) < tr₂.forward.length),
        tr₁.forward[j].1 = tr₂.forward[j].1 ∧ tr₁.forward[j].2 ≠ tr₂.forward[j].2 := by
  set main := keyOnlyOutsideRun scheme adversary X
  obtain ⟨path, s, located, second, hpath, hcf₁, -, hne, hcf₂, rfl, rfl⟩ :=
    contextFork_success main (forkBound q) (.inr ()) (forkIndex scheme X q) h
  have hT₁ := outsideTranscript_of_mem_support_keyOnlyOutsideRun scheme adversary X
    (replayPathResult_mem_support_replayFirstRun main path hpath)
  have hT₂ := outsideTranscript_of_mem_support_keyOnlyOutsideRun scheme adversary X
    (replayPathResult_mem_support_replayFirstRun main second.path
      (mem_support_replayFirstPath main second.path))
  let before : QueryLog (OutsideSpec A) := located.occurrence.before
  let log₁ : QueryLog (OutsideSpec A) := PFunctor.FreeM.Path.trace main path
  let log₂ : QueryLog (OutsideSpec A) := PFunctor.FreeM.Path.trace main second.path
  let rest₁ : QueryLog (OutsideSpec A) := PFunctor.FreeM.Path.trace
    (located.occurrence.resume located.completion.answer) located.completion.suffix
  let rest₂ : QueryLog (OutsideSpec A) := PFunctor.FreeM.Path.trace
    (located.occurrence.resume second.answer) second.suffix
  have hlog₁ : log₁ = before ++ ⟨.inr (), located.completion.answer⟩ :: rest₁ :=
    (congrArg (PFunctor.FreeM.Path.trace main) located.path_eq).symm.trans
      (PFunctor.FreeM.Cursor.Occurrence.trace_plug
        located.occurrence located.completion.answer located.completion.suffix)
  have hlog₂ : log₂ = before ++ ⟨.inr (), second.answer⟩ :: rest₂ :=
    PFunctor.FreeM.Cursor.Occurrence.trace_plug located.occurrence second.answer second.suffix
  have hc : before.countQ (· = .inr ()) = s := by
    rw [QueryLog.countQ_eq_occurrences]
    simp [before]
  obtain ⟨hk₁, u₁, hl₁⟩ := hT₁.getLast?_of_eq_append (log := log₁) hlog₁
  obtain ⟨hk₂, u₂, hl₂⟩ := hT₂.getLast?_of_eq_append (log := log₂) hlog₂
  have hv₁ : log₁.getQueryValue? (.inr ()) (before.countQ (· = .inr ())) = _ :=
    hT₁.getQueryValue?_inr _
  have hv₂ : log₂.getQueryValue? (.inr ()) (before.countQ (· = .inr ())) = _ :=
    hT₂.getQueryValue?_inr _
  rw [hlog₁, QueryLog.getQueryValue?_append_self_at_countQ, List.getElem?_eq_getElem hk₁]
    at hv₁
  rw [hlog₂, QueryLog.getQueryValue?_append_self_at_countQ, List.getElem?_eq_getElem hk₂]
    at hv₂
  rw [hl₁] at hl₂
  simp only [Option.some.injEq, Option.map_some] at hl₂ hv₁ hv₂
  have hcode := Sum.inl_injective (congrArg Sigma.fst hl₂)
  clear hl₁ hl₂ u₁ u₂
  generalize before.countQ (· = .inr ()) = n at hc hk₁ hk₂ hcode hv₁ hv₂
  subst hc
  refine ⟨s, hcf₁, hcf₂, hk₁, hk₂, FinEnum.equiv.injective (Fin.ext hcode), ?_⟩
  simpa only [Fin.getElem_fin, ← hv₁, ← hv₂] using hne

/-- **The forking lemma for the run on one key.**

Let `acc` be the chance that the run has a fork index.

Then the fork succeeds with chance at least `acc (acc / (q + 1) - 1 / |A|)`. -/
theorem le_prEvent_isSome_contextFork_keyOnlyOutsideRun
    [UniformAnswerMeasure (Unit →ₒ A)] (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (q : ℕ) :
    (let acc := Pr{let tr ← keyOnlyOutsideRun scheme adversary X}[
        (forkIndex scheme X q tr).isSome]
     acc * (acc / (q + 1 : ℝ≥0∞) - (FinEnum.card A : ℝ≥0∞)⁻¹)) ≤
      Pr{let r ← (contextFork (keyOnlyOutsideRun scheme adversary X) (forkBound q) (.inr ())
        (forkIndex scheme X q))}[r.isSome] := by
  have h := le_prEvent_isSome_contextFork (keyOnlyOutsideRun scheme adversary X) (forkBound q)
    (.inr ()) (forkIndex scheme X q)
    (CfReachable.toPathCfReachable (cfReachable_forkIndex scheme adversary X q))
  simp only [← prEvent_isSome_eq_sum] at h
  have hcard : Fintype.card ((OutsideSpec A).Range (.inr ())) = FinEnum.card A := by
    rw [FinEnum.card_eq_fintypeCard]
    rfl
  simpa only [forkBound, Nat.cast_add, Nat.cast_one, hcard] using h

variable [SampleableType F]

variable [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

/-- **The key-only game with independent answers, with new forward answers asked outside.**

Draw the key uniformly, and run the forger on it with the outside oracle uniform.

The check passes with no flag raised as often as the forger wins with independent answers. -/
theorem keyOnlyIndepAdvantage_eq_outside (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) :
    keyOnlyIndepAdvantage scheme adversary =
      Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
         let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
        tr.verified = true ∧ tr.bad = false] := by
  have hL : keyOnlyIndepExperiment scheme adversary =
      (fun z => z.1 && !z.2) <$> (do
        let x ← ($ᵗ F : ProbComp F)
        (fun r : ((M × F × F) × Bool) × IndepState A => (r.1.2, r.2.2)) <$>
          (simulateQ indepPermImpl (keyOnlyRunQ scheme adversary (x • scheme.g))).run
            ([], false)) := by
    rw [keyOnlyIndepExperiment, keyOnlyExperimentQ, simulateQ_bind, StateT.run_bind,
      simulateQ_passthrough_add_liftM_run]
    simp
  have hR : EvalDistEq
      (do
        let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
        (fun tr : KeyOnlyTrace F A M => (tr.verified, tr.bad)) <$>
          keyOnlyOutsideRun scheme adversary (x • scheme.g))
      (do
        let x ← ($ᵗ F : ProbComp F)
        (fun r : ((M × F × F) × Bool) × IndepState A => (r.1.2, r.2.2)) <$>
          (simulateQ indepPermImpl (keyOnlyRunQ scheme adversary (x • scheme.g))).run
            ([], false)) := by
    refine (evalDistEq_liftComp_uniform _).bind fun x => ?_
    have h := (simulateQ_outsideImpl_run_evalDistEq
      (keyOnlyRunQ scheme adversary (x • scheme.g)) ([], false) []).map (fun r => (r.1.2, r.2.2))
    simpa [keyOnlyOutsideRun, Functor.map_map] using h
  rw [keyOnlyIndepAdvantage, hL, prEvent_map, ← hR.prEvent_eq]
  congr 1
  simp [map_bind, Functor.map_map, Bool.and_eq_true]

end EthLib.Cryptography.Secp256k1.Security
