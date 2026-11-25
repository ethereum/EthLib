module

public import EthLib.Cryptography.Proofs.Sponge.Proj
public import EthLib.Cryptography.Proofs.Sponge.Support

/-!
# Proofs: the sponge's queries of path values can wait until the end of the game

In the random-oracle model, a computation whose answers nothing reads commutes with any other.

So the visible game may ask the values of the hashed paths after the distinguisher stops.

The joint law of the output, the visible state and the cache stays the same.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge.Indiff

open OracleComp OracleSpec LazyPermutation Indifferentiability

/-! ## The end phase -/

section Setting

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-- The end phase: the sponge's queries of path values, for each hashed message. -/
noncomputable def endPhase : List Msg → OracleComp (unifSpec + ASpec Msg Dg E C) Unit
  | [] => pure ()
  | m :: ms => do
    skel (C := C) P [] (P.pad m)
    endPhase ms

/-- The visible game, then the end phase on the messages it hashed. -/
noncomputable def visRun (pre : Bool) {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (vs : VState Dg E C Msg) :
    OracleComp (unifSpec + ASpec Msg Dg E C) (α × VState Dg E C Msg) :=
  (simulateQ (visImpl P iv pre) oa).run vs >>= fun z => endPhase P z.2.2.1 >>= fun _ => pure z

omit [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- The queries of path values cache the value of each path they ask, and keep the cache. -/
theorem skel_support (pre bs : List (Dg × E)) (c : ACache Msg Dg E C)
    {z : Unit × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl (skel (C := C) P pre bs)).run c)) :
    c ≤ z.2 ∧ ∀ i < bs.length, cachedPathValue P z.2 (pre ++ bs.take (i + 1)) ≠ none := by
  induction bs generalizing pre c with
  | nil =>
    simp only [skel, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, by simp⟩
  | cons B bs ih =>
    simp only [skel, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨v, c₁⟩, h₁, w₂, h₂, hz⟩ := hz
    rw [drawSt_run] at h₂
    simp only [support_map, Set.mem_image] at h₂
    obtain ⟨u, -, rfl⟩ := h₂
    obtain ⟨hc₁, hv, -⟩ := pathValue_support P _ c h₁
    obtain ⟨hc, hcached⟩ := ih (pre ++ [B]) c₁ hz
    refine ⟨le_trans hc₁ hc, fun i hi => ?_⟩
    rcases i with _ | i
    · simp [cachedPathValue_mono P hc hv]
    · simpa [List.take_succ_cons] using hcached i (by simp at hi; omega)

omit [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- Queries of path values at cached paths change nothing. -/
theorem skel_run_of_cached (pre bs : List (Dg × E)) (c : ACache Msg Dg E C)
    (h : ∀ i < bs.length, cachedPathValue P c (pre ++ bs.take (i + 1)) ≠ none) :
    (simulateQ (ASpec Msg Dg E C).romImpl (skel (C := C) P pre bs)).run c =ᵈ
      (pure ((), c) : ProbComp (Unit × ACache Msg Dg E C)) := by
  induction bs generalizing pre with
  | nil => simp [skel]
  | cons B bs ih =>
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (h 0 (by simp))
    simp only [List.take_succ_cons, List.take_zero] at hv
    simp only [skel, simulateQ_bind, StateT.run_bind, pathValue_run_of_cachedPathValue P _ c hv,
      pure_bind,
      drawSt_run, bind_map_left]
    refine (EvalDistEq.bind_right _ fun u => ih (pre ++ [B]) fun i hi => ?_).trans ?_
    · simpa [List.take_succ_cons] using h (i + 1) (by simp; omega)
    · exact EvalDistEq.bind_const _ _

omit [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- After the end phase, the values of all paths of the hashed messages are cached. -/
theorem endPhase_support (ms : List Msg) (c : ACache Msg Dg E C)
    {z : Unit × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl (endPhase (C := C) P ms)).run c)) :
    c ≤ z.2 ∧ ∀ m ∈ ms, ∀ i < (P.pad m).length,
      cachedPathValue P z.2 ((P.pad m).take (i + 1)) ≠ none := by
  induction ms generalizing c with
  | nil =>
    simp only [endPhase, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, by simp⟩
  | cons m ms ih =>
    simp only [endPhase, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨h1, h2⟩ := skel_support P [] (P.pad m) c hw
    obtain ⟨h3, h4⟩ := ih w.2 hz
    refine ⟨le_trans h1 h3, fun m' hm' i hi => ?_⟩
    rcases List.mem_cons.mp hm' with rfl | hm'
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (h2 i hi)
      simp only [List.nil_append] at hv
      rw [cachedPathValue_mono P h3 hv]
      simp
    · exact h4 m' hm' i hi

omit [DecidableEq Msg] in
/-- The visible game never forgets a hashed message. -/
theorem visImpl_hashed_mono (pre : Bool) {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (vs : VState Dg E C Msg) (m : Msg)
    (hm : m ∈ vs.2.1) {z : α × VState Dg E C Msg}
    (hz : z ∈ support ((simulateQ (visImpl P iv pre) oa).run vs)) : m ∈ z.2.2.1 := by
  refine simulateQ_run_preserves_inv_of_query (spec' := unifSpec + ASpec Msg Dg E C)
    (visImpl P iv pre) (fun vs => m ∈ vs.2.1) (fun t s hs z hz => ?_) oa _ hm z hz
  rcases t with (n | x | y) | m'
  · simp [visImpl] at hz
    obtain ⟨y, rfl⟩ := hz
    exact hs
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, r, -, rfl⟩ := hz
    exact hs
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · simp only [visImpl, StateT.run_mk] at hz
    split at hz
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨-, -, d, -, rfl⟩ := hz
      exact List.mem_cons_of_mem _ hs
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨d, -, rfl⟩ := hz
      exact List.mem_cons_of_mem _ hs

omit [DecidableEq Msg] in
/-- The hash step with queries of path values is these queries, then the step without them. -/
theorem visImpl_true_hash (m : Msg) (vs : VState Dg E C Msg) :
    (visImpl P iv true (.inr m)).run vs =
      (skel (C := C) P [] (P.pad m) >>= fun _ => (visImpl P iv false (.inr m)).run vs) := by
  simp [visImpl]

omit [DecidableEq Msg] in
/-- The hash step records its message. -/
theorem visImpl_hash_support (pre : Bool) (m : Msg) (vs : VState Dg E C Msg)
    {z : Dg × VState Dg E C Msg} (hz : z ∈ support ((visImpl P iv pre (.inr m)).run vs)) :
    z.2.2.1 = m :: vs.2.1 := by
  simp only [visImpl, StateT.run_mk] at hz
  split at hz
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨-, -, d, -, rfl⟩ := hz
    rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨d, -, rfl⟩ := hz
    rfl

omit [DecidableEq Msg] in
/-- A run with its end phase, after a first query. -/
theorem visRun_query_bind (pre : Bool) {α : Type}
    (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (k : (GameSpec (SpongeState Dg E C) Msg Dg).Range t →
      OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α)
    (vs : VState Dg E C Msg) :
    visRun P iv pre ((liftM ((GameSpec (SpongeState Dg E C) Msg Dg).query t) :
      OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) _) >>= k) vs =
      ((visImpl P iv pre t).run vs >>= fun p => visRun P iv pre (k p.1) p.2) := by
  simp [visRun, simulateQ_bind, StateT.run_bind, bind_assoc]

/-- **The queries of path values can wait.**

With its end phase, the visible game with these queries has the law of the game without them.

The law is that of the output, the visible state and the cache together. -/
theorem visRun_true_evalDistEq_false {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl (visRun P iv true oa vs)).run c =ᵈ
      (simulateQ (ASpec Msg Dg E C).romImpl (visRun P iv false oa vs)).run c := by
  induction oa using OracleComp.inductionOn generalizing vs c with
  | pure a => simp [visRun]
  | query_bind t k ih =>
    rw [visRun_query_bind, visRun_query_bind]
    rcases t with (n | x | y) | m
    · simp only [simulateQ_bind, StateT.run_bind]
      exact EvalDistEq.bind_right _ fun p => ih p.1.1 p.1.2 p.2
    · simp only [simulateQ_bind, StateT.run_bind]
      exact EvalDistEq.bind_right _ fun p => ih p.1.1 p.1.2 p.2
    · simp only [simulateQ_bind, StateT.run_bind]
      exact EvalDistEq.bind_right _ fun p => ih p.1.1 p.1.2 p.2
    · rw [visImpl_true_hash, bind_assoc]
      set Y := ((visImpl P iv false (.inr m)).run vs >>= fun p =>
        visRun P iv false (k p.1) p.2) with hY
      calc (simulateQ (ASpec Msg Dg E C).romImpl (skel (C := C) P [] (P.pad m) >>= fun _ =>
            (visImpl P iv false (.inr m)).run vs >>= fun p =>
              visRun P iv true (k p.1) p.2)).run c
          =ᵈ (simulateQ (ASpec Msg Dg E C).romImpl (skel (C := C) P [] (P.pad m) >>= fun _ =>
            Y >>= fun r => pure r)).run c := by
            simp only [hY, bind_pure, simulateQ_bind, StateT.run_bind]
            exact EvalDistEq.bind_right _ fun w => EvalDistEq.bind_right _ fun p =>
              ih p.1.1 p.1.2 p.2
        _ =ᵈ (simulateQ (ASpec Msg Dg E C).romImpl (Y >>= fun r =>
            skel (C := C) P [] (P.pad m) >>= fun _ => pure r)).run c :=
            run_bind_bind_comm _ Y (fun _ r => pure r) c
        _ =ᵈ (simulateQ (ASpec Msg Dg E C).romImpl Y).run c := by
            simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
            conv_rhs => rw [← bind_pure ((simulateQ (ASpec Msg Dg E C).romImpl Y).run c)]
            refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
            -- After the end phase, the postponed queries hit the cache.
            have hcached : ∀ i < (P.pad m).length,
                cachedPathValue P z.2 ([] ++ (P.pad m).take (i + 1)) ≠ none := by
              intro i hi
              simp only [hY, visRun, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
                simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨p, hp, w, hw, e, he, rfl⟩ := hz
              have hpm := visImpl_hash_support P iv false m vs
                (fst_mem_support_of_mem_support_run hp)
              have hwm := visImpl_hashed_mono P iv false (k p.1.1) p.1.2 m
                (by rw [hpm]; exact List.mem_cons_self) (fst_mem_support_of_mem_support_run hw)
              simpa using (endPhase_support P w.1.2.2.1 w.2 he).2 m hwm i hi
            refine (EvalDistEq.bind_left (skel_run_of_cached P [] (P.pad m) z.2 hcached)
              _).trans ?_
            simp

end Setting

end EthLib.Cryptography.Sponge.Indiff
