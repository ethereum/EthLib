module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnlyOutside
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Redraw
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Proofs: a key-only forgery on an inverse answer of `Π` gives the discrete logarithm

Run the key-only forger with independent answers, as in the run with the outside oracle.

Redraw each new inverse answer that encodes a nonzero multiple of the base point.

The redrawn answer comes with its discrete logarithm.

That keeps the law of the run.

Say the check passes, and the forgery's point was not a new forward query of the log.

Then the point was an inverse answer, so the run knows the discrete logarithm `a` of a point `R`.

The forgery's point is the encoding of `R* = (H(m) g + t X) / s`, so `R* = R` or `R* = -R`.

Then `s R* = H(m) g + t X` gives the key `x` with `X = x g`.

So this case wins at most as often as a solver of the discrete logarithm.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

This is the step from Game G2 to Game G3 of the proof of their Theorem 2, in their Figure 7.

Their Game G3 stops with `0` in line 12 when the forgery's pair is an inverse pair.

The discrete-logarithm game here draws the key from all scalars, as the key-only game does.

Their key generation and their Definition 1 draw it from the nonzero scalars.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- The state of the run with redrawn inverse answers.

It is the state of the run with the outside oracle, then the known discrete logarithms.

Each known one is a redrawn inverse answer `α` with the scalar `a` such that `α` encodes `a g`. -/
abbrev DLogState (F A : Type) := OutsideState A × List (A × F)

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [FinEnum F] [FinEnum A]

/-- The permutation with independent answers, its new inverse answers redrawn.

A query answered before gets its answer again, in either direction.

A new forward query gets a uniform value of `A`, and joins the cache and the log.

A new inverse query gets a redrawn answer, which joins the cache.

Its discrete logarithm, when the redraw gives one, joins the known ones.

The flag rises by the same rules as with independent answers.

The forward branch is the outside oracle's.

It has a uniform draw in place of the outside query, and no coin query. -/
def dlogOracle (scheme : Scheme F G A M) (inImage : A → Bool) :
    QueryImpl (PermSpec A) (StateT (DLogState F A) ProbComp)
  | .inl a => fun s =>
    match s.1.1.1.lookup a with
    | some b => pure (b, s)
    | none =>
      (fun b : A => (b, ((IndepState.addForward s.1.1 a b, s.1.2 ++ [(a, b)]), s.2))) <$>
        (uniformOutside [] a : ProbComp A)
  | .inr b => fun s =>
    match (s.1.1.1.map Prod.swap).lookup b with
    | some a => pure (a, s)
    | none =>
      (fun r : A × Option F =>
        (r.1, ((IndepState.addInverse s.1.1 r.1 b, s.1.2), s.2 ++ r.2.toList.map (r.1, ·)))) <$>
        redrawInverse scheme inImage b

/-- The oracles of the run with redrawn inverse answers: coins, passed through, then `Π`. -/
abbrev dlogImpl (scheme : Scheme F G A M) (inImage : A → Bool) :
    QueryImpl (unifSpec + PermSpec A) (StateT (DLogState F A) ProbComp) :=
  unifSpec.passthrough + dlogOracle scheme inImage

section Law

variable [UniformAnswerMeasure (Unit →ₒ A)] [SampleableType A]

omit [DecidableEq G] in
/-- Dropping the known discrete logarithms, one step has the law of the outside oracle's step. -/
private theorem dlogImpl_run_evalDistEq {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α)
    (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0) (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg)
    (t : (unifSpec + PermSpec A).Domain) (s : OutsideState A) (known : List (A × F)) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (dlogImpl scheme inImage t).run (s, known))
      ((outsideImpl t).run s) := by
  obtain ⟨⟨c, f⟩, l⟩ := s
  rcases t with n | a | b
  · rw [passthrough_add_inl_run]
    simp only [outsideImpl, StateT.run, Functor.map_map]
    exact ((evalDistEq_liftM_query_uniform (spec := unifSpec) (superSpec := OutsideSpec A)
      n).symm).map _
  · change EvalDistEq (_ <$> (match c.lookup a with
      | some b => pure (b, (((c, f), l), known))
      | none => _)) _
    simp only [outsideImpl, outsideOracle, StateT.run]
    cases c.lookup a with
    | some b => simpa only [map_pure] using (pure_outside_evalDistEq _).symm
    | none =>
      simp only [Functor.map_map]
      exact ((EvalDistEq.bind_const _ _).trans
        ((query_outside_evalDistEq.trans (uniformOutside_nil_evalDistEq a).symm).map _)).symm
  · change EvalDistEq (_ <$> (match (c.map Prod.swap).lookup b with
      | some a => pure (a, (((c, f), l), known))
      | none => _)) _
    simp only [outsideImpl, outsideOracle, StateT.run]
    cases (c.map Prod.swap).lookup b with
    | some a => simpa only [map_pure] using (pure_outside_evalDistEq _).symm
    | none =>
      simp only [Functor.map_map]
      have h := ((redrawInverse_fst_evalDistEq hImage hg h2 hsemi hneg b).trans
        (evalDistEq_liftComp_uniform (superSpec := OutsideSpec A) _).symm).map
        fun a => (a, IndepState.addInverse (c, f) a b, l)
      simp only [Functor.map_map] at h
      exact h

omit [DecidableEq G] in
/-- **Redrawing the inverse answers keeps the law of the run with the outside oracle.**

Drop the known discrete logarithms at the end.

The output and the state then have the law of the run with the outside oracle.

The base point must be nonzero, and `2` must be nonzero in the scalars.

The encoding must be semi-injective, and opposite points must share their encoding.

The test must agree with the search over all scalars. -/
theorem simulateQ_dlogImpl_run_evalDistEq {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α)
    (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0) (hsemi : scheme.SemiInjective)
    (hneg : scheme.EncodeNeg) {α : Type}
    (oa : PermComp A α) (s : OutsideState A) (known : List (A × F)) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (simulateQ (dlogImpl scheme inImage) oa).run (s, known))
      ((simulateQ outsideImpl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s known with
  | pure x =>
    simpa only [simulateQ_pure, StateT.run_pure, map_pure] using (pure_outside_evalDistEq _).symm
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, map_bind]
    let g := fun y : _ × OutsideState A => (simulateQ outsideImpl (k y.1)).run y.2
    have h₁ := ((evalDistEq_liftComp_uniform (superSpec := OutsideSpec A)
      ((dlogImpl scheme inImage t).run (s, known))).symm).bind
      (f := fun z => (fun z => (z.1, z.2.1)) <$>
        (simulateQ (dlogImpl scheme inImage) (k z.1)).run z.2)
      (g := fun z => g (z.1, z.2.1)) fun z => ih z.1 z.2.1 z.2.2
    refine h₁.trans ?_
    have h₂ := (((evalDistEq_liftComp_uniform (superSpec := OutsideSpec A)
      ((dlogImpl scheme inImage t).run (s, known))).map fun z => (z.1, z.2.1)).trans
      (dlogImpl_run_evalDistEq hImage hg h2 hsemi hneg t s known)).bind_left g
    simpa only [bind_map_left] using h₂

end Law

/-- What the run with redrawn inverse answers keeps true of its state.

Each known discrete logarithm `a` of `α` is nonzero, and `α` encodes `a g`.

The point of each cached pair is in the log, or has a known discrete logarithm.

Otherwise it encodes no nonzero multiple of the base point. -/
def DLogInv (scheme : Scheme F G A M) (s : DLogState F A) : Prop :=
  (∀ e ∈ s.2, e.2 ≠ 0 ∧ scheme.encode (e.2 • scheme.g) = e.1) ∧
    ∀ p ∈ s.1.1.1, p.1 ∈ s.1.2.map Prod.fst ∨ p.1 ∈ s.2.map Prod.fst ∨
      ∀ a : F, a ≠ 0 → scheme.encode (a • scheme.g) ≠ p.1

omit [DecidableEq F] [DecidableEq G] in
/-- A query of the permutation keeps the state, adds a forward pair, or adds a redrawn pair. -/
private theorem dlogOracle_step (scheme : Scheme F G A M) (inImage : A → Bool)
    (q : (PermSpec A).Domain) (s : DLogState F A) (z)
    (hz : z ∈ support ((dlogOracle scheme inImage q).run s)) :
    z.2 = s ∨ (∃ a b, z.2 = ((IndepState.addForward s.1.1 a b, s.1.2 ++ [(a, b)]), s.2)) ∨
      ∃ b α o, (α, o) ∈ support (redrawInverse scheme inImage b) ∧
        z.2 = ((IndepState.addInverse s.1.1 α b, s.1.2), s.2 ++ o.toList.map (α, ·)) := by
  rcases q with a | b
  · change z ∈ support (match s.1.1.1.lookup a with
      | some b => pure (b, s)
      | none => _) at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨b, -, rfl⟩ := hz
      exact Or.inr (Or.inl ⟨a, b, rfl⟩)
  · change z ∈ support (match (s.1.1.1.map Prod.swap).lookup b with
      | some a => pure (a, s)
      | none => _) at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨⟨α, o⟩, hr, rfl⟩ := hz
      exact Or.inr (Or.inr ⟨b, α, o, hr, rfl⟩)

omit [DecidableEq G] in
/-- The run with redrawn answers keeps the invariant, when the test agrees with the search. -/
theorem dlogImpl_preservesInv (scheme : Scheme F G A M) (inImage : A → Bool)
    (hImage : ∀ α, inImage α = encodesPoint scheme α) :
    QueryImpl.PreservesInv (dlogImpl scheme inImage) (DLogInv scheme) := by
  rintro (n | q) s ⟨hk, hc⟩ z hz
  · rw [passthrough_add_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact ⟨hk, hc⟩
  rcases dlogOracle_step scheme inImage q s z hz with h | ⟨a, b, h⟩ | ⟨b, α, o, hr, h⟩
  · rw [h]; exact ⟨hk, hc⟩
  · rw [h]
    refine ⟨hk, fun p hp => ?_⟩
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · rcases hc p hp with h1 | h1 | h1
      · simp [h1]
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
  · rw [h]
    refine ⟨fun e he => ?_, fun p hp => ?_⟩
    · simp only [List.mem_append] at he
      rcases he with he | he
      · exact hk e he
      · cases o with
        | none => simp at he
        | some a =>
          simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at he
          subst he
          exact of_mem_support_redrawInverse_some hr
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · cases o with
        | none => exact Or.inr (Or.inr (of_mem_support_redrawInverse_none hImage hr))
        | some a => simp
      · rcases hc p hp with h1 | h1 | h1
        · exact Or.inl h1
        · simp [h1]
        · exact Or.inr (Or.inr h1)

omit [DecidableEq F] [DecidableEq G] in
/-- After a forward query on `a`, the cache has a pair whose first entry is `a`. -/
private theorem mem_of_mem_support_dlogOracle_inl (scheme : Scheme F G A M)
    (inImage : A → Bool) (a : A) (s : DLogState F A) (z)
    (hz : z ∈ support ((dlogOracle scheme inImage (.inl a)).run s)) :
    a ∈ z.2.1.1.1.map Prod.fst := by
  change z ∈ support (match s.1.1.1.lookup a with
    | some b => pure (b, s)
    | none => _) at hz
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rename_i h
    by_contra hn
    rw [List.lookup_eq_none_iff.mpr fun p hp => ?_] at h
    · simp at h
    · exact bne_iff_ne.mpr fun h' => hn (List.mem_map.mpr ⟨p, hp, h'.symm⟩)
  · simp only [support_map, Set.mem_image] at hz
    obtain ⟨b, -, rfl⟩ := hz
    simp

/-- A forgery that passes the check has nonzero `t`, `s` and `U = H(m) g + t X`.

Its point is the point of a pair of the final cache. -/
theorem of_mem_support_dlogImpl_keyOnlyRunQ (scheme : Scheme F G A M) (inImage : A → Bool)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (s : DLogState F A)
    {z : ((M × F × F) × Bool) × DLogState F A}
    (hz : z ∈ support
      ((simulateQ (dlogImpl scheme inImage) (keyOnlyRunQ scheme adversary X)).run s))
    (hv : z.1.2 = true) :
    z.1.1.2.1 ≠ 0 ∧ z.1.1.2.2 ≠ 0 ∧
      scheme.hash z.1.1.1 • scheme.g + z.1.1.2.1 • X ≠ 0 ∧
      forgeryPoint scheme X z.1.1 ∈ z.2.1.1.1.map Prod.fst := by
  simp only [keyOnlyRunQ, simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion,
    exists_prop] at hz
  obtain ⟨⟨w, s₁⟩, -, ⟨b, s₂⟩, hb, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only at hb hv ⊢
  subst hv
  obtain ⟨m, t, σ⟩ := w
  simp only [verifyQ] at hb
  split_ifs at hb with hc
  · obtain ⟨-, ht, hσ, hU⟩ := hc
    refine ⟨ht, hσ, hU, ?_⟩
    simp only [conversionQ, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hb
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := hb
    rw [show s₂ = y.2 from (Prod.ext_iff.mp h).2.symm]
    exact mem_of_mem_support_dlogOracle_inl scheme inImage
      (scheme.encode (σ⁻¹ • (scheme.hash m • scheme.g + t • X))) s₁ y
      (by simpa [HasQuery.instOfMonadLift_query, simulateQ_query, add_apply_inr] using hy)
  · simp at hb

/-- The key from a forgery `(m, t, s)` on the key `X`, and a scalar `a`.

When the forgery's point encodes `a g`, the point `R* = (H(m) g + t X) / s` is `a g` or `-a g`.

Then the key is `(s a - H(m)) / t` or `(-s a - H(m)) / t`; the first is kept if it gives `X`. -/
def extractInverse (scheme : Scheme F G A M) (X : G) (z : M × F × F) (a : F) : F :=
  let c := z.2.1⁻¹ * (z.2.2 * a - scheme.hash z.1)
  if c • scheme.g = X then c else z.2.1⁻¹ * (-(z.2.2 * a) - scheme.hash z.1)

omit [DecidableEq F] [FinEnum F] [FinEnum A] in
/-- The key from a valid forgery whose point encodes `a g`, for a nonzero `a`, is the key.

The base point must be nonzero, and the encoding semi-injective. -/
theorem extractInverse_eq {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) {x a t s : F} {m : M} (ht : t ≠ 0) (hs : s ≠ 0)
    (hU : scheme.hash m • scheme.g + t • x • scheme.g ≠ 0) (ha : a ≠ 0)
    (henc : scheme.encode (a • scheme.g) = forgeryPoint scheme (x • scheme.g) (m, t, s)) :
    extractInverse scheme (x • scheme.g) (m, t, s) a = x := by
  have hinj := smul_left_injective F hg
  have hR0 : (s⁻¹ * (scheme.hash m + t * x)) • scheme.g ≠ 0 := by
    rw [mul_smul, add_smul, mul_smul]; exact smul_ne_zero (inv_ne_zero hs) hU
  have ha0 : a • scheme.g ≠ 0 := smul_ne_zero ha hg
  rw [forgeryPoint_smul] at henc
  have key : s⁻¹ * (scheme.hash m + t * x) = a ∨ s⁻¹ * (scheme.hash m + t * x) = -a := by
    rcases hsemi _ _ ha0 hR0 henc with h | h
    · exact Or.inl (hinj h)
    · exact Or.inr (hinj (show _ • _ = _ • _ by rw [h, neg_smul]))
  simp only [extractInverse]
  rcases key with h | h
  · have hc : t⁻¹ * (s * a - scheme.hash m) = x := by
      rw [← h]; field_simp; ring
    rw [hc]; simp
  · split_ifs with hc
    · exact hinj hc
    · rw [show a = -(s⁻¹ * (scheme.hash m + t * x)) by rw [h, neg_neg]]
      field_simp; ring

/-- The solver of the discrete logarithm from a key-only forger, for forgeries on inverse pairs.

It runs the forger on its instance `X`, with independent answers and redrawn inverse answers.

It runs the forger once, with the given test and uniform draws, so it is efficient when the test is.

It reads the base point of the scheme, not its first argument.

If it knows the discrete logarithm of the forgery's point, it returns the key it gives.

Otherwise it returns `0`. -/
def inverseSolver (scheme : Scheme F G A M) (inImage : A → Bool)
    (adversary : KeyOnlyAdversary F G A M) : DiffieHellman.DLogAdversary F G := fun _ X => do
  let z ← (simulateQ (dlogImpl scheme inImage) (keyOnlyRunQ scheme adversary X)).run
    ((([], false), []), [])
  pure <| match z.2.2.lookup (forgeryPoint scheme X z.1.1) with
    | some a => extractInverse scheme X z.1.1 a
    | none => 0

variable [UniformAnswerMeasure (Unit →ₒ A)] [SampleableType A] [SampleableType F]

/-- **A key-only forgery on an inverse pair gives the discrete logarithm.**

Draw the key, and run the forger with the outside oracle on it.

Say the check passes, and the forgery's point is not in the log of new forward pairs.

That happens at most as often as the solver above finds the discrete logarithm of the key.

The base point must be nonzero, and `2` must be nonzero in the scalars.

The encoding must be semi-injective, and opposite points must share their encoding.

The test must agree with the search over all scalars. -/
theorem prEvent_inverse_le_dlog {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α)
    (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0) (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg)
    (adversary : KeyOnlyAdversary F G A M) :
    Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
       let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
      tr.verified = true ∧
        forgeryPoint scheme (x • scheme.g) tr.forgery ∉ tr.forward.map Prod.fst] ≤
      Pr{let b ← DiffieHellman.dlogExperiment scheme.g (inverseSolver scheme inImage adversary)}[
        b = true] := by
  have hrun : ∀ x : F, EvalDistEq
      ((fun z => decide (z.1.2 = true ∧ forgeryPoint scheme (x • scheme.g) z.1.1 ∉
        z.2.1.2.map Prod.fst)) <$> (simulateQ (dlogImpl scheme inImage)
          (keyOnlyRunQ scheme adversary (x • scheme.g))).run ((([], false), []), []))
      ((fun tr : KeyOnlyTrace F A M => decide (tr.verified = true ∧
        forgeryPoint scheme (x • scheme.g) tr.forgery ∉ tr.forward.map Prod.fst)) <$>
          keyOnlyOutsideRun scheme adversary (x • scheme.g)) := fun x => by
    have h := (simulateQ_dlogImpl_run_evalDistEq hImage hg h2 hsemi hneg
      (keyOnlyRunQ scheme adversary (x • scheme.g)) (([], false), []) []).map
      fun r => decide (r.1.2 = true ∧ forgeryPoint scheme (x • scheme.g) r.1.1 ∉
        r.2.2.map Prod.fst)
    simp only [Functor.map_map] at h
    simpa only [keyOnlyOutsideRun, Functor.map_map] using h
  have hL := (((evalDistEq_liftComp_uniform (superSpec := OutsideSpec A) ($ᵗ F : ProbComp F)).symm
    ).bind hrun).prEvent_eq (· = true)
  simp only [map_bind, Functor.map_map, decide_eq_true_eq] at hL
  rw [← hL]
  simp only [DiffieHellman.dlogExperiment, inverseSolver, bind_assoc, pure_bind]
  simp only [map_bind, map_pure, decide_eq_true_eq]
  refine prEvent_bind_mono_of_support _ _ _ fun x _ => ?_
  simp only [bind_pure_comp]
  refine prEvent_mono_of_support _ _ _ fun z hz hE => ?_
  obtain ⟨ht, hs, hU, hmem⟩ := of_mem_support_dlogImpl_keyOnlyRunQ scheme inImage adversary _ _ hz
    hE.1
  obtain ⟨hk, hc⟩ := simulateQ_run_preservesInv (dlogImpl scheme inImage) (DLogInv scheme)
    (dlogImpl_preservesInv scheme inImage hImage) _ _ (by simp [DLogInv]) z hz
  obtain ⟨⟨⟨m, t, s⟩, v⟩, st⟩ := z
  simp only at ht hs hU hmem hE hk hc ⊢
  obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hmem
  cases hl : st.2.lookup (forgeryPoint scheme (x • scheme.g) (m, t, s)) with
  | some a =>
    obtain ⟨l₁, l₂, heq, -⟩ := List.lookup_eq_some_iff.mp hl
    obtain ⟨ha, henc⟩ := hk (forgeryPoint scheme (x • scheme.g) (m, t, s), a) (by rw [heq]; simp)
    exact extractInverse_eq hg hsemi ht hs hU ha henc
  | none =>
    exfalso
    have hc0 : s⁻¹ * (scheme.hash m + t * x) ≠ 0 := by
      refine mul_ne_zero (inv_ne_zero hs) fun h0 => hU ?_
      rw [smul_smul, ← add_smul, h0, zero_smul]
    rcases hc p hp with h1 | h1 | h1
    · exact hE.2 (hpeq ▸ h1)
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h1
      have h3 := List.lookup_eq_none_iff.mp hl q hq
      rw [hqe, hpeq] at h3
      simp at h3
    · exact h1 _ hc0 (by rw [hpeq, forgeryPoint_smul])

end EthLib.Cryptography.Secp256k1.Security
