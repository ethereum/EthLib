module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnlyOutside

/-!
# Proofs: a key-only forgery on a new forward answer of `Π`

Run the key-only forger on the key `X`, with new forward answers asked of the outside oracle.

Say the check of its forgery `(m, t, s)` passes.

Then `X`, `t`, `s` and `U = H(m) g + t X` are nonzero.

Let `R* = s⁻¹ U`; the forgery's point is its encoding `φ(R*)`.

The cache holds a pair at that point whose answer `β` has `ψ(β) = t`.

Say also that no flag was raised, and that the forgery's point is in the log of new forward pairs.

The pair of the log at that point is then the pair the check read.

So `ψ(β_j) = t`, where `β_j` is the answer of the pair at the fork index `j`.

The log lists the first query first, and its positions count from `0`.

The fork returns two such runs, at the same fork index.

Their forgeries share their point, their answers there differ, and `ψ` maps each to its own `t`.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

This is the fact behind the forward case of the proof of their Theorem 2.

In their Game G3 of Figure 7, lines 11, 13 and 14, the answer `β*` with `ψ(β*) = t` is some `β_j`.

Their Figure 8, line 12, finds `j` by that answer, counted from `1`.

The fork index here finds it by the point; with no flag raised, both give the same pair.

Their Game G1 stops with `0` when a new answer repeats, in lines 20 and 29.

Here the flag rises instead.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec LazyPermutation

variable {F G A M : Type}

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [FinEnum A]

/-- The run of the forger and its check ends after the forger, with or without the check's query.

When the check asks, its answer is that of a forward query at the forgery's point. -/
private theorem of_mem_support_outsideImpl_keyOnlyRunQ (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (s : OutsideState A)
    {r : ((M × F × F) × Bool) × OutsideState A}
    (hr : r ∈ support ((simulateQ outsideImpl (keyOnlyRunQ scheme adversary X)).run s)) :
    ∃ w s₁, (w, s₁) ∈ support ((simulateQ outsideImpl (adversary.main X)).run s) ∧
      (r = ((w, false), s₁) ∨
        (X ≠ 0 ∧ w.2.1 ≠ 0 ∧ w.2.2 ≠ 0 ∧ scheme.hash w.1 • scheme.g + w.2.1 • X ≠ 0 ∧
          ∃ y ∈ support ((outsideOracle (.inl (forgeryPoint scheme X w))).run s₁),
            r = ((w, decide (scheme.reduce y.1 = w.2.1)), y.2))) := by
  simp only [keyOnlyRunQ, simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion,
    exists_prop] at hr
  obtain ⟨⟨w, s₁⟩, hw, ⟨b, s₂⟩, hb, hz⟩ := hr
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  refine ⟨w, s₁, hw, ?_⟩
  obtain ⟨m, t, σ⟩ := w
  simp only [verifyQ] at hb
  split_ifs at hb with hc
  · obtain ⟨hX, ht, hσ, hU⟩ := hc
    right
    refine ⟨hX, ht, hσ, hU, ?_⟩
    simp only [conversionQ, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hb
    obtain ⟨y, ⟨x, hx, rfl⟩, h⟩ := hb
    refine ⟨x, ?_, ?_⟩
    · simpa [HasQuery.instOfMonadLift_query, simulateQ_query, outsideImpl, forgeryPoint] using hx
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      simp only [← h1, ← h2]
  · left
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rfl

/-- The key-only run on `X`, from the empty state, ends in a state that meets the invariant.

Each logged pair is cached, and with no flag raised the cache is a partial bijection. -/
theorem outsideInv_of_mem_support_keyOnlyOutsideRun (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {tr : KeyOnlyTrace F A M}
    (htr : tr ∈ support (keyOnlyOutsideRun scheme adversary X)) :
    OutsideInv ((tr.cache, tr.bad), tr.forward) := by
  simp only [keyOnlyOutsideRun, support_map, Set.mem_image] at htr
  obtain ⟨r, hr, rfl⟩ := htr
  obtain ⟨w, s₁, hw, h | ⟨-, -, -, -, y, hy, rfl⟩⟩ :=
    of_mem_support_outsideImpl_keyOnlyRunQ scheme adversary X _ hr
  · subst h
    exact outsideInv_of_mem_support_simulateQ_outsideImpl (adversary.main X) outsideInv_empty hw
  · exact outsideInv_of_mem_support_outsideImpl (.inr (.inl _))
      (outsideInv_of_mem_support_simulateQ_outsideImpl (adversary.main X) outsideInv_empty hw) hy

/-- **A forgery that passes the check.**

The key, `t`, `s` and `U = H(m) g + t X` are nonzero.

The cache holds a pair at the forgery's point whose answer `ψ` maps to `t`. -/
theorem of_verified_of_mem_support_keyOnlyOutsideRun (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {tr : KeyOnlyTrace F A M}
    (htr : tr ∈ support (keyOnlyOutsideRun scheme adversary X)) (hv : tr.verified = true) :
    X ≠ 0 ∧ tr.forgery.2.1 ≠ 0 ∧ tr.forgery.2.2 ≠ 0 ∧
      scheme.hash tr.forgery.1 • scheme.g + tr.forgery.2.1 • X ≠ 0 ∧
      ∃ β, (forgeryPoint scheme X tr.forgery, β) ∈ tr.cache ∧ scheme.reduce β = tr.forgery.2.1 := by
  simp only [keyOnlyOutsideRun, support_map, Set.mem_image] at htr
  obtain ⟨r, hr, rfl⟩ := htr
  obtain ⟨w, s₁, -, h | ⟨hX, ht, hs, hU, y, hy, rfl⟩⟩ :=
    of_mem_support_outsideImpl_keyOnlyRunQ scheme adversary X _ hr
  · subst h
    simp at hv
  · simp only [decide_eq_true_eq] at hv
    exact ⟨hX, ht, hs, hU, y.1, mem_cache_of_mem_support_outsideOracle_inl _ _ _ hy, hv⟩

/-- **The check of a forgery with a fork index read the logged answer at that index.**

Take a run on the key `X` whose fork index is `j`.

The pair of the log at position `j` is at the forgery's point, and `ψ` maps its answer to `t`. -/
theorem reduce_forward_eq_of_forkIndex_eq_some (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) {X : G} {q : ℕ} {tr : KeyOnlyTrace F A M}
    (htr : tr ∈ support (keyOnlyOutsideRun scheme adversary X))
    {j : Fin (forkBound q (.inr ()) + 1)} (hj : forkIndex scheme X q tr = some j) :
    ∃ h : (j : ℕ) < tr.forward.length,
      tr.forward[j].1 = forgeryPoint scheme X tr.forgery ∧
        scheme.reduce tr.forward[j].2 = tr.forgery.2.1 := by
  obtain ⟨hv, hbad, hlt, hpt⟩ := verified_and_forward_of_forkIndex_eq_some hj
  obtain ⟨-, -, -, -, β, hβ, hr⟩ :=
    of_verified_of_mem_support_keyOnlyOutsideRun scheme adversary X htr hv
  obtain ⟨hlog, hpb⟩ := outsideInv_of_mem_support_keyOnlyOutsideRun scheme adversary X htr
  have hmem : tr.forward[(j : ℕ)] ∈ tr.cache := hlog _ (List.getElem_mem hlt)
  have heq : tr.forward[(j : ℕ)] = (forgeryPoint scheme X tr.forgery, β) :=
    List.inj_on_of_nodup_map (hpb hbad).1 hmem hβ (by simpa using hpt)
  refine ⟨hlt, hpt, ?_⟩
  have h2 := congrArg Prod.snd heq
  simp only at h2
  simpa only [Fin.getElem_fin, h2] using hr

/-! ## Both runs of the fork -/

/-- **The two forgeries of a fork share their point, and `ψ` maps each answer there to its `t`.**

Take two runs that the fork returns, on the key `X`, with the common fork index `j`.

The pairs of their logs at position `j` are at the point of each forgery, and that point is shared.

Their answers there differ, and `ψ` maps each to the `t` of its own forgery.

Both checks passed, so the two forgeries have the same point. -/
theorem forward_eq_of_mem_support_contextFork (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (q : ℕ) {tr₁ tr₂ : KeyOnlyTrace F A M}
    (h : some (tr₁, tr₂) ∈ support
      (contextFork (keyOnlyOutsideRun scheme adversary X) (forkBound q) (.inr ())
        (forkIndex scheme X q))) :
    ∃ j, forkIndex scheme X q tr₁ = some j ∧ forkIndex scheme X q tr₂ = some j ∧
      ∃ (h₁ : (j : ℕ) < tr₁.forward.length) (h₂ : (j : ℕ) < tr₂.forward.length),
        tr₁.forward[j].1 = forgeryPoint scheme X tr₁.forgery ∧
        tr₂.forward[j].1 = forgeryPoint scheme X tr₂.forgery ∧
        tr₁.forward[j].1 = tr₂.forward[j].1 ∧ tr₁.forward[j].2 ≠ tr₂.forward[j].2 ∧
        scheme.reduce tr₁.forward[j].2 = tr₁.forgery.2.1 ∧
        scheme.reduce tr₂.forward[j].2 = tr₂.forgery.2.1 ∧
        forgeryPoint scheme X tr₁.forgery = forgeryPoint scheme X tr₂.forgery ∧
        tr₁.verified = true ∧ tr₂.verified = true := by
  obtain ⟨j, hj₁, hj₂, h₁, h₂, hpt, hne⟩ :=
    forward_point_eq_answer_ne_of_mem_support_contextFork scheme adversary X q h
  obtain ⟨ht₁, ht₂⟩ :=
    mem_support_keyOnlyOutsideRun_of_mem_support_contextFork scheme adversary X q h
  obtain ⟨_, e₁, r₁⟩ := reduce_forward_eq_of_forkIndex_eq_some scheme adversary ht₁ hj₁
  obtain ⟨_, e₂, r₂⟩ := reduce_forward_eq_of_forkIndex_eq_some scheme adversary ht₂ hj₂
  obtain ⟨v₁, -⟩ := verified_and_forward_of_forkIndex_eq_some hj₁
  obtain ⟨v₂, -⟩ := verified_and_forward_of_forkIndex_eq_some hj₂
  exact ⟨j, hj₁, hj₂, h₁, h₂, e₁, e₂, hpt, hne, r₁, r₂, e₁.symm.trans (hpt.trans e₂), v₁,
    v₂⟩

end EthLib.Cryptography.Secp256k1.Security
