module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnly
public import EthLib.Cryptography.Proofs.IndependentOutside
public import VCVio.CryptoFoundations.ReplayFork
import VCVio.EvalDist.Inequalities

/-!
# Proofs: the key-only game with new forward answers asked of one oracle

Run the key-only forger on a fixed key, with independent answers to `Π`.

Ask each new forward answer of one outside oracle with no input, and log it with its query.

The run then ends with the forgery, the result of the check, the cache, the flag and the log.

With the key drawn uniformly, it wins with the chance of the game with independent answers.

The run logs at most one more pair than the forger asks for `Π` or its inverse.

When the outside oracle answered the conversion of a forgery, a replay fork can rewind there.

Stop a path of the run just before a query to the outside oracle with `s` earlier ones.

Every completion of that query logs at least `s + 1` pairs.

Its pair at position `s` has the same point for every completion.

The answer of that pair is the answer that completed the query.

The fork index is the position of the forgery's point in the log of new forward pairs.

The new forward queries of both runs at that index then share the point and differ in answer.

The forking lemma bounds the chance of such a fork from below.

On the key `x g`, the forgery's point is the encoding of `((H(m) + t x) / s) g`.

Say two forgeries `(m, t, s)` and `(m', t', s')` have these scalars equal up to a sign `η`.

Then they give the key, when `H(m) / t ≠ H(m') / t'`.

A forger with at most `q` queries to `Π` or its inverse logs at most `q + 1` pairs.

So a win with no flag raised has a fork index, or its point is not in the log.

With a uniform key, the chance to win with independent answers is then at most a sum.

It is the chance of a fork index plus the chance that the check passes on a point not in the log.

This is the split of their Game G3, which stops with `0` in line 12 on an inverse pair.

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

With the key drawn uniformly, the bound also holds, as in their Lemma 1.
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

omit [DecidableEq F] [DecidableEq G] [FinEnum A] in
/-- The forgery's point on the key `x g` is the encoding of `((H(m) + t x) / s) g`. -/
theorem forgeryPoint_smul (scheme : Scheme F G A M) (x t s : F) (m : M) :
    forgeryPoint scheme (x • scheme.g) (m, t, s) =
      scheme.encode ((s⁻¹ * (scheme.hash m + t * x)) • scheme.g) := by
  simp only [forgeryPoint, smul_smul, ← add_smul, mul_add]

/-- The key from two forgeries `(m, t, s)` and `(m', t', s')` on one point, for a sign `η`.

It is `(s r - H(m)) / t`, where `r = (H(m) / t - H(m') / t') / (s / t - η s' / t')`. -/
def forwardKey (scheme : Scheme F G A M) (z z' : M × F × F) (η : F) : F :=
  let r := (scheme.hash z.1 / z.2.1 - scheme.hash z'.1 / z'.2.1) /
    (z.2.2 / z.2.1 - η * z'.2.2 / z'.2.1)
  (z.2.2 * r - scheme.hash z.1) / z.2.1

omit [DecidableEq F] [DecidableEq G] [AddCommGroup G] [Module F G] [FinEnum A] in
/-- Take two forgeries on the key `x g` whose scalars `(H(m) + t x) / s` agree up to a sign `η`.

Then the key for `η` is `x`, when `t`, `s`, `t'` and `s'` are nonzero.

It also needs `H(m) / t` and `H(m') / t'` to differ. -/
theorem forwardKey_eq_of {scheme : Scheme F G A M} {x η : F} {z z' : M × F × F}
    (ht : z.2.1 ≠ 0) (hs : z.2.2 ≠ 0) (ht' : z'.2.1 ≠ 0) (hs' : z'.2.2 ≠ 0)
    (hη : z'.2.2⁻¹ * (scheme.hash z'.1 + z'.2.1 * x) =
      η * (z.2.2⁻¹ * (scheme.hash z.1 + z.2.1 * x)))
    (hdiv : scheme.hash z.1 / z.2.1 ≠ scheme.hash z'.1 / z'.2.1) :
    forwardKey scheme z z' η = x := by
  obtain ⟨m, t, s⟩ := z
  obtain ⟨m', t', s'⟩ := z'
  simp only at ht hs ht' hs' hη hdiv
  set r := s⁻¹ * (scheme.hash m + t * x) with hr
  have h1 : scheme.hash m = s * r - t * x := by rw [hr]; field_simp; ring
  have h2 : scheme.hash m' = s' * (η * r) - t' * x := by rw [← hη]; field_simp; ring
  have hden : s / t - η * s' / t' ≠ 0 := by
    intro h0
    apply hdiv
    have : (s * r - t * x) / t - (s' * (η * r) - t' * x) / t' = r * (s / t - η * s' / t') := by
      field_simp; ring
    rw [h1, h2]
    exact sub_eq_zero.mp (by rw [this, h0, mul_zero])
  have hrr : (scheme.hash m / t - scheme.hash m' / t') / (s / t - η * s' / t') = r := by
    rw [div_eq_iff hden, h1, h2]; field_simp; ring
  simp only [forwardKey]
  rw [hrr, h1]; field_simp; ring

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

/-- **Completions of one query to the outside oracle log one point there, with their answers.**

Take a query to the outside oracle with `s` earlier ones, on a path of the run on the key `X`.

Complete it twice, each time with an answer and a path for the rest of the run.

Both runs then log at least `s + 1` pairs.

Their pairs at position `s`, counted from `0`, have the same point.

The answer of each is the answer that completed the query. -/
theorem forward_getElem_of_completion_keyOnlyOutsideRun (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {s : ℕ}
    (occ : PFunctor.FreeM.Cursor.Occurrence (P := (OutsideSpec A).toPFunctor) (.inr ())
      (keyOnlyOutsideRun scheme adversary X) s)
    (c₁ c₂ : occ.Completion) :
    ∃ (h₁ : s < (PFunctor.FreeM.output _ c₁.path).forward.length)
      (h₂ : s < (PFunctor.FreeM.output _ c₂.path).forward.length),
      (PFunctor.FreeM.output _ c₁.path).forward[s].1 =
          (PFunctor.FreeM.output _ c₂.path).forward[s].1 ∧
        (PFunctor.FreeM.output _ c₁.path).forward[s].2 = c₁.answer ∧
        (PFunctor.FreeM.output _ c₂.path).forward[s].2 = c₂.answer := by
  have hT₁ := outsideTranscript_of_mem_support_keyOnlyOutsideRun scheme adversary X
    (replayPathResult_mem_support_replayFirstRun (keyOnlyOutsideRun scheme adversary X) c₁.path
      (mem_support_replayFirstPath (keyOnlyOutsideRun scheme adversary X) c₁.path))
  have hT₂ := outsideTranscript_of_mem_support_keyOnlyOutsideRun scheme adversary X
    (replayPathResult_mem_support_replayFirstRun (keyOnlyOutsideRun scheme adversary X) c₂.path
      (mem_support_replayFirstPath (keyOnlyOutsideRun scheme adversary X) c₂.path))
  let before : QueryLog (OutsideSpec A) := occ.before
  let log₁ : QueryLog (OutsideSpec A) :=
    PFunctor.FreeM.Path.trace (keyOnlyOutsideRun scheme adversary X) c₁.path
  let log₂ : QueryLog (OutsideSpec A) :=
    PFunctor.FreeM.Path.trace (keyOnlyOutsideRun scheme adversary X) c₂.path
  let rest₁ : QueryLog (OutsideSpec A) := PFunctor.FreeM.Path.trace
    (occ.resume c₁.answer) c₁.suffix
  let rest₂ : QueryLog (OutsideSpec A) := PFunctor.FreeM.Path.trace
    (occ.resume c₂.answer) c₂.suffix
  have hlog₁ : log₁ = before ++ ⟨.inr (), c₁.answer⟩ :: rest₁ :=
    PFunctor.FreeM.Cursor.Occurrence.trace_plug occ c₁.answer c₁.suffix
  have hlog₂ : log₂ = before ++ ⟨.inr (), c₂.answer⟩ :: rest₂ :=
    PFunctor.FreeM.Cursor.Occurrence.trace_plug occ c₂.answer c₂.suffix
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
  exact ⟨hk₁, hk₂, FinEnum.equiv.injective (Fin.ext hcode), hv₁.symm, hv₂.symm⟩

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
  obtain ⟨hk₁, hk₂, hpt, ha₁, ha₂⟩ :=
    forward_getElem_of_completion_keyOnlyOutsideRun scheme adversary X
    located.occurrence located.completion second
  simp only [located.path_eq] at hk₁ hpt ha₁
  refine ⟨s, hcf₁, hcf₂, hk₁, hk₂, hpt, ?_⟩
  exact fun hq => hne (ha₁.symm.trans (hq.trans ha₂))

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

/-- **The forking lemma for the run on a uniform key.**

Draw the key uniformly, and let `acc` be the chance that the run has a fork index.

Then the fork on the same key succeeds with chance at least `acc (acc / (q + 1) - 1 / |A|)`.

The mean of the bounds of the forking lemma on each key is at least this bound.

The reason is that the mean of a square is at least the square of the mean. -/
theorem le_prEvent_isSome_contextFork_keyOnlyOutsideRun_uniform [SampleableType F]
    [UniformAnswerMeasure (Unit →ₒ A)] (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (q : ℕ) :
    (let acc := Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
                   let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
        (forkIndex scheme (x • scheme.g) q tr).isSome]
     acc * (acc / (q + 1 : ℝ≥0∞) - (FinEnum.card A : ℝ≥0∞)⁻¹)) ≤
      Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
         let r ← contextFork (keyOnlyOutsideRun scheme adversary (x • scheme.g)) (forkBound q)
           (.inr ()) (forkIndex scheme (x • scheme.g) q)}[r.isSome] := by
  let : MeasurableSpace F := ⊤
  dsimp only
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  exact OracleComp.EvalDist.marginalized_jensen_forking_bound_of_discrete _ _ _ _ _
    (fun _ => prEvent_le_one _)
    (fun x => le_prEvent_isSome_contextFork_keyOnlyOutsideRun scheme adversary _ q)

/-! ## Runs of the fork -/

omit [FinEnum A] in
/-- The output of every path through a run with the outside oracles is a possible output of it. -/
theorem output_mem_support_of_path {α : Type}
    (main : OracleComp (OutsideSpec A) α) (path : PFunctor.FreeM.Path main) :
    PFunctor.FreeM.output main path ∈ support main := by
  have h : PFunctor.FreeM.output main path ∈
      support (PFunctor.FreeM.output main <$> replayFirstPath main) := by
    rw [support_map]
    exact ⟨path, mem_support_replayFirstPath main path, rfl⟩
  rwa [map_output_replayFirstPath] at h

/-- Both runs that the fork returns are runs of the key-only forger on the key `X`. -/
theorem mem_support_keyOnlyOutsideRun_of_mem_support_contextFork (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (q : ℕ) {tr₁ tr₂ : KeyOnlyTrace F A M}
    (h : some (tr₁, tr₂) ∈ support
      (contextFork (keyOnlyOutsideRun scheme adversary X) (forkBound q) (.inr ())
        (forkIndex scheme X q))) :
    tr₁ ∈ support (keyOnlyOutsideRun scheme adversary X) ∧
      tr₂ ∈ support (keyOnlyOutsideRun scheme adversary X) := by
  obtain ⟨path, s, located, second, hpath, hcf₁, -, hne, hcf₂, rfl, rfl⟩ :=
    contextFork_success (keyOnlyOutsideRun scheme adversary X) (forkBound q) (.inr ())
      (forkIndex scheme X q) h
  exact ⟨output_mem_support_of_path _ path, output_mem_support_of_path _ second.path⟩

/-! ## The split of a win -/

/-- On a run with no flag raised, a passed check has a fork index or a point outside the log. -/
private theorem forkIndex_isSome_or_notMem (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {q : ℕ}
    (hq : IsQueryBoundP (adversary.main X) (·.isRight = true) q) {tr : KeyOnlyTrace F A M}
    (htr : tr ∈ support (keyOnlyOutsideRun scheme adversary X))
    (h : tr.verified = true ∧ tr.bad = false) :
    (forkIndex scheme X q tr).isSome ∨
      (tr.verified = true ∧ forgeryPoint scheme X tr.forgery ∉ tr.forward.map Prod.fst) := by
  obtain ⟨hv, hb⟩ := h
  by_cases hm : forgeryPoint scheme X tr.forgery ∈ tr.forward.map Prod.fst
  · left
    have hlen := length_forward_le_of_mem_support_keyOnlyOutsideRun scheme adversary X hq htr
    have hsome : (tr.forward.findIdx? fun p => decide (p.1 = forgeryPoint scheme X tr.forgery)
        ).isSome := by
      rw [List.findIdx?_isSome]
      simpa using hm
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hlt, -, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
    simp [forkIndex, hv, hb, hk, show k < q + 1 by omega]
  · exact Or.inr ⟨hv, hm⟩

/-- **A win with no flag raised has a fork index, or its point is not in the log.**

Take a forger that asks for `Π` or its inverse at most `q` times on the key `X`.

The log then has at most `q + 1` pairs, so a point in the log is at a position the fork reads. -/
theorem prEvent_verified_and_not_bad_le_forkIndex_add_notMem
    [UniformAnswerMeasure (Unit →ₒ A)] (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {q : ℕ}
    (hq : IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    Pr{let tr ← keyOnlyOutsideRun scheme adversary X}[tr.verified = true ∧ tr.bad = false] ≤
      Pr{let tr ← keyOnlyOutsideRun scheme adversary X}[(forkIndex scheme X q tr).isSome] +
        Pr{let tr ← keyOnlyOutsideRun scheme adversary X}[tr.verified = true ∧
          forgeryPoint scheme X tr.forgery ∉ tr.forward.map Prod.fst] := by
  refine (prEvent_mono_of_support _ _ (fun tr => (forkIndex scheme X q tr).isSome ∨
    (tr.verified = true ∧ forgeryPoint scheme X tr.forgery ∉ tr.forward.map Prod.fst))
    fun tr htr h => forkIndex_isSome_or_notMem scheme adversary X hq htr h).trans
    (prEvent_or_le _ _ _)

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

/-- **The key-only game with independent answers splits into the forward and inverse cases.**

Take a forger that asks for `Π` or its inverse at most `q` times, on every key.

Its chance to win with independent answers is at most the sum of two chances, with a uniform key.

The first is the chance that the run has a fork index.

The second is the chance that the check passes on a point that is not in the log. -/
theorem keyOnlyIndepAdvantage_le_forkIndex_add_notMem (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) {q : ℕ}
    (hq : ∀ X, IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    keyOnlyIndepAdvantage scheme adversary ≤
      Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
         let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
        (forkIndex scheme (x • scheme.g) q tr).isSome] +
      Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
         let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
        tr.verified = true ∧
          forgeryPoint scheme (x • scheme.g) tr.forgery ∉ tr.forward.map Prod.fst] := by
  rw [keyOnlyIndepAdvantage_eq_outside]
  simp only [prEvent_bind_eq_tsum_prEvent, ← ENNReal.tsum_add, ← mul_add]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  exact prEvent_verified_and_not_bad_le_forkIndex_add_notMem scheme adversary _ (hq _)

end EthLib.Cryptography.Secp256k1.Security
