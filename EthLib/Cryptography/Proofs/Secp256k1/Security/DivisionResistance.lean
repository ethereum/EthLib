module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.ForwardCase

/-!
# Proofs: the division resistance of the hash, and the forward case of a fork

This game measures the division resistance of the hash `H` relative to `ψ`.

Draw `β` uniformly from the answers that `ψ` maps to a nonzero scalar.

From `β`, the first stage returns a message `m` and a state.

Draw `β'` the same way, independently.

From the state and `β'`, the second stage returns a message `m'`.

The adversary wins if `H(m) / ψ(β) = H(m') / ψ(β')`.

The messages may be equal.

Either stage may abort, and then the adversary loses.

Here `H` is fixed, as in the game of forgery, while their §2.3 draws a key for it first.

So an adversary that knows a zero of `H` always wins.

A bound therefore charges a named adversary, here the reduction from a fork.

A fork of the key-only run gives two forgeries `(m, t, s)` and `(m', t', s')`.

The fork fails to give the key when `H(m) / t = H(m') / t'`.

With a uniform key, the reduction below wins the game at least that often, divided by `q + 1`.

It draws the key and a guess of the fork index.

Its first stage runs the forger up to the guessed query of the outside oracle.

It answers that query with `β`, runs the rest, and checks that the fork index is the guess.

It passes the run before the query on as its state.

Its second stage answers the same query with `β'`, runs the rest again, and checks the same.

Both stages answer every other query with uniform values, as the fork does.

Their stages share the coins `ρ`.

Here, as in the fork of this library, the coins after the guessed query are fresh.

Their second stage aborts when `β = β'`; here it does not, which only adds wins.

The first stage runs the forger once, and the second runs only its part after the guessed query.

No theorem states the running time.

With a fork index `j`, the check of a forgery read the answer at `j`, so `ψ` maps it to `t`.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The game is their Definition 5, and the reduction is their Figure 10.

Their `Q` is `q + 1` here.

Their reduction draws the key from the nonzero scalars; here it draws it from all of them.

That matches the key-only game here.

The fork answers its query with a uniform value of all of `A`.

The game draws only the answers that `ψ` maps to a nonzero scalar.

The forgery's `t` is nonzero, so the event of the fork has no larger chance than the game.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- An adversary against the division resistance of the hash relative to `ψ`, in two stages. -/
structure DivisionAdversary (A M : Type) where
  /-- The state that the first stage passes on to the second. -/
  State : Type
  /-- The first stage: from `β`, a message and a state, or `none` when it aborts. -/
  choose : A → ProbComp (Option (M × State))
  /-- The second stage: from the state and `β'`, a message, or `none` when it aborts. -/
  finish : State → A → ProbComp (Option M)

variable [Field F] [DecidableEq F] [FinEnum A]

/-- The answers that `ψ` maps to a nonzero scalar, the set `B*` of the source. -/
def nonzeroAnswers (scheme : Scheme F G A M) : List A :=
  (FinEnum.toList A).filter fun β => scheme.reduce β ≠ 0

/-- The game of division resistance of the hash relative to `ψ`.

The adversary loses if either stage aborts.

If no answer maps to a nonzero scalar, the draw fails and the adversary loses. -/
def divisionExperiment (scheme : Scheme F G A M) (adversary : DivisionAdversary A M) :
    ProbComp Bool := do
  let some β ← ($ nonzeroAnswers scheme : OptionT ProbComp A).run | pure false
  let some (m, state) ← adversary.choose β | pure false
  let some β' ← ($ nonzeroAnswers scheme : OptionT ProbComp A).run | pure false
  let some m' ← adversary.finish state β' | pure false
  pure (decide (scheme.hash m / scheme.reduce β = scheme.hash m' / scheme.reduce β'))

/-- The probability that the adversary wins the game of division resistance. -/
noncomputable def divisionAdvantage (scheme : Scheme F G A M)
    (adversary : DivisionAdversary A M) : ℝ≥0∞ :=
  Pr{let b ← divisionExperiment scheme adversary}[b = true]

variable [AddCommGroup G] [Module F G] [DecidableEq G]

/-- What the first stage of the reduction passes on to the second.

It is the key, the guess of the fork index, and the run before the guessed query. -/
structure DivisionState (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M)
    (q : ℕ) where
  /-- The key. -/
  key : F
  /-- The guess of the fork index. -/
  guess : Fin (forkBound q (.inr ()) + 1)
  /-- The run of the forger on the key, stopped before its guessed query to the outside oracle. -/
  occurrence : PFunctor.FreeM.Cursor.Occurrence (P := (OutsideSpec A).toPFunctor) (.inr ())
    (keyOnlyOutsideRun scheme adversary (key • scheme.g)) guess

/-- **With the fork index `s`, `ψ` maps the answer that completed the query to `t`.**

Stop the run on the key `X` before a query to the outside oracle with `s` earlier ones.

Complete it, and say the fork index of the run is `s`.

Then `ψ` maps the completing answer to the forgery's `t`. -/
theorem reduce_answer_eq_of_forkIndex (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (q : ℕ) {s : Fin (forkBound q (.inr ()) + 1)}
    (occ : PFunctor.FreeM.Cursor.Occurrence (P := (OutsideSpec A).toPFunctor) (.inr ())
      (keyOnlyOutsideRun scheme adversary X) s)
    (c : occ.Completion)
    (h : forkIndex scheme X q (PFunctor.FreeM.output _ c.path) = some s) :
    scheme.reduce c.answer = (PFunctor.FreeM.output _ c.path).forgery.2.1 := by
  obtain ⟨hk, -, -, ha, -⟩ := forward_getElem_of_completion_keyOnlyOutsideRun scheme adversary X
    occ c c
  obtain ⟨_, _, hr⟩ := reduce_forward_eq_of_forkIndex_eq_some scheme adversary
    (output_mem_support_of_path _ c.path) h
  rw [← ha]
  exact hr

/-- With the fork index `s`, the answer that completed the query maps to a nonzero scalar. -/
private theorem answer_mem_nonzeroAnswers (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) (q : ℕ) {s : Fin (forkBound q (.inr ()) + 1)}
    (occ : PFunctor.FreeM.Cursor.Occurrence (P := (OutsideSpec A).toPFunctor) (.inr ())
      (keyOnlyOutsideRun scheme adversary X) s)
    (c : occ.Completion)
    (h : forkIndex scheme X q (PFunctor.FreeM.output _ c.path) = some s) :
    c.answer ∈ nonzeroAnswers scheme := by
  obtain ⟨hv, -⟩ := verified_and_forward_of_forkIndex_eq_some h
  obtain ⟨-, ht, -⟩ := of_verified_of_mem_support_keyOnlyOutsideRun scheme adversary X
    (output_mem_support_of_path _ c.path) hv
  simp only [nonzeroAnswers, List.mem_filter, decide_eq_true_eq]
  rw [reduce_answer_eq_of_forkIndex scheme adversary X q occ c h]
  exact ⟨FinEnum.mem_toList (α := A) _, ht⟩

variable [SampleableType F] [SampleableType A]

/-- The second half of either stage of the reduction.

It answers the guessed query with `β` and runs the rest of the forger.

It returns the forgery's message if the fork index is the guess. -/
def DivisionState.complete {scheme : Scheme F G A M} {adversary : KeyOnlyAdversary F G A M}
    {q : ℕ} (state : DivisionState scheme adversary q) (β : A) : ProbComp (Option M) := do
  let c ← simulateQ outsideSample (state.occurrence.completeWith β)
  let tr := PFunctor.FreeM.output _ c.path
  pure (if forkIndex scheme (state.key • scheme.g) q tr = some state.guess then
    some tr.forgery.1 else none)

/-- The reduction from a fork of the key-only forger to division resistance, after Figure 10.

The first stage draws the key and the guess, and runs the forger up to the guessed query.

It aborts if the forger asks the outside oracle at most `s` times, where `s` is the guess.

Both stages then complete the query, one with `β` and the other with `β'`.

Each stage aborts unless the fork index of its run is the guess. -/
def divisionReduction (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M)
    (q : ℕ) : DivisionAdversary A M where
  State := DivisionState scheme adversary q
  choose β := do
    let x ← $ᵗ F
    let s ← $ᵗ Fin (forkBound q (.inr ()) + 1)
    let split ← simulateQ outsideSample (PFunctor.FreeM.Cursor.splitAt
      (P := (OutsideSpec A).toPFunctor) (.inr ())
      (keyOnlyOutsideRun scheme adversary (x • scheme.g)) s)
    match split with
    | .missing _ => pure none
    | .found occ =>
      let state : DivisionState scheme adversary q := ⟨x, s, occ⟩
      (fun m => m.map fun m => (m, state)) <$> state.complete β
  finish state β' := state.complete β'

variable [UniformAnswerMeasure (Unit →ₒ A)]

omit [FinEnum A] [UniformAnswerMeasure (Unit →ₒ A)] in
/-- Take a uniform draw from `A`, kept only when it lies on a list without repeats.

It has no more weight than a uniform draw from that list. -/
private theorem prEvent_uniformSample_bind_le [Fintype A] {β γ : Type} (B : List A)
    (hB : B.Nodup) (k : A → ProbComp β) (g : Option A → ProbComp γ) (p : β → Prop)
    (p' : γ → Prop) (h0 : ∀ a ∉ B, Pr{let y ← k a}[p y] = 0)
    (hle : ∀ a ∈ B, Pr{let y ← k a}[p y] ≤ Pr{let y ← g (some a)}[p' y]) :
    Pr{let y ← $ᵗ A >>= k}[p y] ≤ Pr{let y ← ($ B : OptionT ProbComp A).run >>= g}[p' y] := by
  rw [prEvent_bind_eq_sum_fintype, prEvent_bind_eq_sum_fintype, Fintype.sum_option]
  refine le_add_left (Finset.sum_le_sum fun a _ => ?_)
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  by_cases ha : a ∈ B
  · have hsel : Pr{let o ← ($ B : OptionT ProbComp A).run}[o = some a] =
        (B.length : ℝ≥0∞)⁻¹ := by
      classical
      rw [prEvent_congr _ _ (fun o => o.elim False (· = a)) (fun o => by cases o <;> simp),
        ← OptionT.prEvent_eq_run, ProbComp.prEvent_uniformSelectList]
      have h1 : B.countP (fun b => decide (b = a)) = 1 := by
        rw [← List.count_eq_one_of_mem hB ha, List.count_eq_countP]
        exact List.countP_congr fun b _ => by simp
      rw [h1]
      simp
    rw [hsel]
    refine mul_le_mul' ?_ (hle a ha)
    refine ENNReal.inv_le_inv.mpr ?_
    exact_mod_cast hB.length_le_card
  · rw [h0 a ha, mul_zero]
    exact zero_le


omit [FinEnum A] [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)] in
/-- Binds whose events are pointwise bounded by a finite multiple of other events. -/
private theorem prEvent_bind_le_const_mul {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    (f g : α → m Prop) {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : ∀ a, prEvent (f a) ≤ c * prEvent (g a)) :
    prEvent (mx >>= f) ≤ c * prEvent (mx >>= g) := by
  let : MeasurableSpace α := ⊤
  have h' : ∀ a, Pr{let y ← f a}[y] ≤ c * Pr{let y ← g a}[y] := fun a => by
    simpa using h a
  have hf := prEvent_bind_eq_lintegral_of_discrete mx f (fun y => y)
  have hg := prEvent_bind_eq_lintegral_of_discrete mx g (fun y => y)
  simp only [id_map'] at hf hg
  rw [hf, hg, ← MeasureTheory.lintegral_const_mul' _ _ hc]
  exact MeasureTheory.lintegral_mono h'

omit [FinEnum A] [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)] in
/-- A bind of propositions whose continuations are bounded on the support is bounded. -/
private theorem prEvent_bind_le_prEvent_of_support {β γ : Type} (mx : ProbComp β)
    (f : β → ProbComp Prop) (g : β → ProbComp γ) (p : γ → Prop)
    (h : ∀ a ∈ support mx, prEvent (f a) ≤ Pr{let y ← g a}[p y]) :
    prEvent (mx >>= f) ≤ Pr{let y ← mx >>= g}[p y] := by
  have := prEvent_bind_mono_of_forall_le_of_support mx f g (fun y => y) p
    (fun a ha => by rw [id_map']; exact h a ha)
  rwa [id_map'] at this

omit [FinEnum A] [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)] in
/-- A bind of propositions whose continuations have no chance on the support has no chance. -/
private theorem prEvent_bind_eq_zero_of_support {β : Type} (mx : ProbComp β)
    (f : β → ProbComp Prop) (h : ∀ a ∈ support mx, prEvent (f a) = 0) :
    prEvent (mx >>= f) = 0 := by
  refine le_antisymm ?_ zero_le
  have := prEvent_bind_le_of_forall_le_of_support mx f (fun y => y) (ε := 0)
    (fun a ha => by rw [id_map', h a ha])
  rwa [id_map'] at this

/-- **A fork whose two forgeries divide to the same scalar wins the game of division resistance.**

Draw the key uniformly, and fork the key-only run at the forgery's query.

Say the fork returns forgeries `(m, t, s)` and `(m', t', s')` with `H(m) / t = H(m') / t'`.

That happens at most `q + 1` times as often as the reduction wins the game.

Here `q` bounds only the fork index, so no bound on the queries of the forger is assumed. -/
theorem prEvent_contextFork_div_eq_le_divisionAdvantage (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (q : ℕ) :
    Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
       let r ← contextFork (keyOnlyOutsideRun scheme adversary (x • scheme.g)) (forkBound q)
         (.inr ()) (forkIndex scheme (x • scheme.g) q)}[
      ∃ tr₁ tr₂, r = some (tr₁, tr₂) ∧
        scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 =
          scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1] ≤
      (q + 1) * divisionAdvantage scheme (divisionReduction scheme adversary q) := by
  classical
  let E : Option (KeyOnlyTrace F A M × KeyOnlyTrace F A M) → Prop := fun r =>
    ∃ tr₁ tr₂, r = some (tr₁, tr₂) ∧
      scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 = scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1
  let fork : F → OracleComp (OutsideSpec A) (Option (KeyOnlyTrace F A M × KeyOnlyTrace F A M)) :=
    fun x => contextFork (keyOnlyOutsideRun scheme adversary (x • scheme.g)) (forkBound q)
      (.inr ()) (forkIndex scheme (x • scheme.g) q)
  let P : F → Fin (forkBound q (.inr ()) + 1) → KeyOnlyTrace F A M → KeyOnlyTrace F A M → Prop :=
    fun x s tr₁ tr₂ => forkIndex scheme (x • scheme.g) q tr₁ = some s ∧
      forkIndex scheme (x • scheme.g) q tr₂ = some s ∧
      scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 = scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1
  let κO : (x : F) → (s : Fin (forkBound q (.inr ()) + 1)) →
      PFunctor.FreeM.Cursor.Split (P := (OutsideSpec A).toPFunctor) (.inr ())
        (keyOnlyOutsideRun scheme adversary (x • scheme.g)) s → OracleComp (OutsideSpec A) Prop :=
    fun x s sp => match sp with
    | .missing _ => pure False
    | .found occ => do
      let c₁ ← occ.complete
      let c₂ ← occ.complete
      pure (P x s (PFunctor.FreeM.output _ c₁.path) (PFunctor.FreeM.output _ c₂.path))
  let κ : (x : F) → (s : Fin (forkBound q (.inr ()) + 1)) →
      PFunctor.FreeM.Cursor.Split (P := (OutsideSpec A).toPFunctor) (.inr ())
        (keyOnlyOutsideRun scheme adversary (x • scheme.g)) s → ProbComp Prop :=
    fun x s sp => match sp with
    | .missing _ => pure False
    | .found occ => do
      let a₁ ← $ᵗ A
      let c₁ ← simulateQ outsideSample (occ.completeWith a₁)
      let a₂ ← $ᵗ A
      let c₂ ← simulateQ outsideSample (occ.completeWith a₂)
      pure (P x s (PFunctor.FreeM.output _ c₁.path) (PFunctor.FreeM.output _ c₂.path))
  let Φ : F → Fin (forkBound q (.inr ()) + 1) → ProbComp Prop := fun x s =>
    simulateQ outsideSample (PFunctor.FreeM.Cursor.splitAt (P := (OutsideSpec A).toPFunctor)
      (.inr ()) (keyOnlyOutsideRun scheme adversary (x • scheme.g)) s) >>= κ x s
  have hstep1 : ∀ x : F, Pr{let r ← fork x}[E r] ≤
      ((q : ℝ≥0∞) + 1) * Pr{let s ← $ᵗ Fin (forkBound q (.inr ()) + 1); let e ← Φ x s}[e] := by
    intro x
    have hsplit : Pr{let r ← fork x}[E r] ≤ ∑ s : Fin (forkBound q (.inr ()) + 1),
        Pr{let r ← fork x}[∃ tr₁ tr₂, r = some (tr₁, tr₂) ∧
          forkIndex scheme (x • scheme.g) q tr₁ = some s ∧
          scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 =
            scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1] := by
      refine (prEvent_mono_of_support _ _ _ fun r hr hE => ?_).trans (prEvent_exists_le _ _)
      obtain ⟨tr₁, tr₂, rfl, hD⟩ := hE
      obtain ⟨j, hj, -⟩ := forward_point_eq_answer_ne_of_mem_support_contextFork scheme adversary
        (x • scheme.g) q hr
      exact ⟨j, tr₁, tr₂, rfl, hj, hD⟩
    refine hsplit.trans ?_
    have hsum : ∀ s : Fin (forkBound q (.inr ()) + 1), Pr{let r ← fork x}[∃ tr₁ tr₂,
        r = some (tr₁, tr₂) ∧ forkIndex scheme (x • scheme.g) q tr₁ = some s ∧
          scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 =
            scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1] ≤ prEvent (Φ x s) := fun s =>
      (prEvent_contextFork_le_splitAt _ _ _ s _ (κO x s) (fun _ => rfl) (fun _ => rfl)).trans_eq
        (prEvent_splitAt_eq_sample _ _ (P x s) _ (fun _ => rfl) (fun _ => rfl) (κ x s)
          (fun _ => rfl) (fun _ => rfl))
    refine (Finset.sum_le_sum fun s _ => hsum s).trans_eq ?_
    have h := prEvent_bind_eq_sum_fintype ($ᵗ Fin (forkBound q (.inr ()) + 1)) (Φ x) (fun e => e)
    simp only [id_map'] at h
    rw [h]
    simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
    rw [← Finset.mul_sum, ← mul_assoc]
    have hq : ((q : ℝ≥0∞) + 1) * ((forkBound q (.inr ()) + 1 : ℕ) : ℝ≥0∞)⁻¹ = 1 := by
      simp only [forkBound, Nat.cast_add, Nat.cast_one]
      exact ENNReal.mul_inv_cancel (by simp) (by simp)
    rw [hq, one_mul]
  have hstep2 : Pr{let x ← $ᵗ F; let s ← $ᵗ Fin (forkBound q (.inr ()) + 1); let e ← Φ x s}[e] ≤
      divisionAdvantage scheme (divisionReduction scheme adversary q) := by
    let S : (x : F) → (s : Fin (forkBound q (.inr ()) + 1)) → ProbComp
        (PFunctor.FreeM.Cursor.Split (P := (OutsideSpec A).toPFunctor) (.inr ())
          (keyOnlyOutsideRun scheme adversary (x • scheme.g)) s) := fun x s =>
      simulateQ outsideSample (PFunctor.FreeM.Cursor.splitAt (P := (OutsideSpec A).toPFunctor)
        (.inr ()) (keyOnlyOutsideRun scheme adversary (x • scheme.g)) s)
    let κa : (x : F) → (s : Fin (forkBound q (.inr ()) + 1)) → A →
        PFunctor.FreeM.Cursor.Split (P := (OutsideSpec A).toPFunctor) (.inr ())
          (keyOnlyOutsideRun scheme adversary (x • scheme.g)) s → ProbComp Prop :=
      fun x s a sp => match sp with
      | .missing _ => pure False
      | .found occ => do
        let c₁ ← simulateQ outsideSample (occ.completeWith a)
        let a₂ ← $ᵗ A
        let c₂ ← simulateQ outsideSample (occ.completeWith a₂)
        pure (P x s (PFunctor.FreeM.output _ c₁.path) (PFunctor.FreeM.output _ c₂.path))
    have hswap : prEvent ($ᵗ F >>= fun x => $ᵗ Fin (forkBound q (.inr ()) + 1) >>= Φ x) =
        prEvent ($ᵗ A >>= fun a => $ᵗ F >>= fun x => $ᵗ Fin (forkBound q (.inr ()) + 1) >>=
          fun s => S x s >>= κa x s a) := by
      rw [prEvent_bind_bind_swap_of_uniform ($ᵗ A)]
      refine prEvent_bind_congr_of_support _ _ _ fun x _ => ?_
      rw [prEvent_bind_bind_swap_of_uniform ($ᵗ A)]
      refine prEvent_bind_congr_of_support _ _ _ fun s _ => ?_
      rw [prEvent_bind_bind_swap_of_uniform ($ᵗ A)]
      refine prEvent_bind_congr_of_support _ _ _ fun sp _ => ?_
      cases sp with
      | missing path =>
        change prEvent (pure False : ProbComp Prop) =
          prEvent ($ᵗ A >>= fun _ => (pure False : ProbComp Prop))
        rw [OracleComp.prEvent_bind_const]
      | found occ => rfl
    refine hswap.trans_le ?_
    unfold divisionAdvantage divisionExperiment
    have hnd : (nonzeroAnswers scheme).Nodup := (FinEnum.nodup_toList).filter _
    refine (prEvent_uniformSample_bind_le (nonzeroAnswers scheme) hnd
      (fun a => $ᵗ F >>= fun x => $ᵗ Fin (forkBound q (.inr ()) + 1) >>= fun s =>
        S x s >>= κa x s a) _ (fun e => e) _ ?_ ?_).trans_eq' (by rw [id_map'])
    · intro a ha
      rw [id_map']
      refine prEvent_bind_eq_zero_of_support _ _ fun x _ => ?_
      refine prEvent_bind_eq_zero_of_support _ _ fun s _ => ?_
      refine prEvent_bind_eq_zero_of_support _ _ fun sp _ => ?_
      cases sp with
      | missing path => simp [κa]
      | found occ =>
        refine prEvent_bind_eq_zero_of_support _ _ fun c₁ hc₁ => ?_
        refine prEvent_bind_eq_zero_of_support _ _ fun a₂ _ => ?_
        refine prEvent_bind_eq_zero_of_support _ _ fun c₂ _ => ?_
        rw [prEvent_pure_prop, ite_eq_right]
        rintro ⟨h₁, -⟩
        have hmem := answer_mem_nonzeroAnswers scheme adversary _ q occ c₁ h₁
        rw [answer_of_mem_support_simulateQ_completeWith occ hc₁] at hmem
        exact ha hmem
    · intro a ha
      rw [id_map']
      dsimp only [divisionReduction]
      rw [bind_assoc]
      refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun x _ => ?_
      rw [bind_assoc]
      refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun s _ => ?_
      rw [bind_assoc]
      refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun sp _ => ?_
      cases sp with
      | missing path =>
        exact (by simp [κa] : prEvent (κa x s a (.missing path)) = 0).trans_le zero_le
      | found occ =>
        dsimp only [DivisionState.complete]
        rw [bind_map_left, bind_assoc]
        refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun c₁ hc₁ => ?_
        have hans₁ := answer_of_mem_support_simulateQ_completeWith occ hc₁
        simp only [pure_bind]
        by_cases hok : forkIndex scheme (x • scheme.g) q
            (PFunctor.FreeM.output _ c₁.path) = some s
        · rw [ite_eq_left hok]
          dsimp only [Option.map_some]
          have hr₁ := reduce_answer_eq_of_forkIndex scheme adversary _ q occ c₁ hok
          rw [hans₁] at hr₁
          refine (prEvent_uniformSample_bind_le (nonzeroAnswers scheme) hnd
            (fun a₂ => simulateQ outsideSample (occ.completeWith a₂) >>= fun c₂ =>
              pure (P x s (PFunctor.FreeM.output _ c₁.path) (PFunctor.FreeM.output _ c₂.path)))
            _ (fun e => e) _ ?_ ?_).trans_eq' (by rw [id_map'])
          · intro a₂ ha₂
            rw [id_map']
            refine prEvent_bind_eq_zero_of_support _ _ fun c₂ hc₂ => ?_
            rw [prEvent_pure_prop, ite_eq_right]
            rintro ⟨-, h₂, -⟩
            have hmem := answer_mem_nonzeroAnswers scheme adversary _ q occ c₂ h₂
            rw [answer_of_mem_support_simulateQ_completeWith occ hc₂] at hmem
            exact ha₂ hmem
          · intro a₂ ha₂
            rw [id_map']
            dsimp only
            rw [bind_assoc]
            refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun c₂ hc₂ => ?_
            have hans₂ := answer_of_mem_support_simulateQ_completeWith occ hc₂
            simp only [pure_bind]
            rw [prEvent_pure_prop]
            by_cases hP : P x s (PFunctor.FreeM.output _ c₁.path) (PFunctor.FreeM.output _ c₂.path)
            · rw [ite_eq_left hP]
              obtain ⟨-, hok₂, hD⟩ := hP
              have hr₂ := reduce_answer_eq_of_forkIndex scheme adversary _ q occ c₂ hok₂
              rw [hans₂] at hr₂
              rw [ite_eq_left hok₂]
              dsimp only
              rw [hr₁, hr₂, prEvent_pure]
              simp [hD]
            · rw [ite_eq_right hP]
              exact zero_le
        · refine le_of_eq_of_le ?_ zero_le
          refine prEvent_bind_eq_zero_of_support _ _ fun a₂ _ => ?_
          refine prEvent_bind_eq_zero_of_support _ _ fun c₂ _ => ?_
          rw [prEvent_pure_prop, ite_eq_right]
          exact fun h => hok h.1
  have htrans : Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A); let r ← fork x}[E r] =
      Pr{let x ← $ᵗ F; let r ← simulateQ outsideSample (fork x)}[E r] := by
    have h := ((evalDistEq_liftComp_uniform (superSpec := OutsideSpec A) ($ᵗ F : ProbComp F)).bind
      (f := fun x => E <$> fork x) (g := fun x => E <$> simulateQ outsideSample (fork x))
      fun x => ((simulateQ_outsideSample_evalDistEq (fork x)).map E).symm).prEvent_eq
        (fun e => e)
    simpa only [id_map'] using h
  change Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A); let r ← fork x}[E r] ≤ _
  rw [htrans]
  calc Pr{let x ← $ᵗ F; let r ← simulateQ outsideSample (fork x)}[E r]
      ≤ ((q : ℝ≥0∞) + 1) *
          Pr{let x ← $ᵗ F; let s ← $ᵗ Fin (forkBound q (.inr ()) + 1); let e ← Φ x s}[e] :=
        prEvent_bind_le_const_mul (m := ProbComp) _ _ _ (by simp) fun x =>
          ((simulateQ_outsideSample_evalDistEq (fork x)).prEvent_eq E).trans_le (hstep1 x)
    _ ≤ _ := by gcongr

end EthLib.Cryptography.Secp256k1.Security
