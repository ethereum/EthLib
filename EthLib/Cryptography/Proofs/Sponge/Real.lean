module

public import EthLib.Cryptography.Proofs.Sponge.Ideal
public import EthLib.Cryptography.Proofs.Sponge.InvMain

/-!
# Proofs: the real side of the combined game is the real world over independent answers

A new pair of the full view takes a new uniform draw, or the value of a path asked by nobody.

That value is a uniform state too, so the real side answers as the oracle with independent answers.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E))

/-! ## Values of paths asked by nobody -/

/-- No answer that the value of `β` reads is cached. -/
def FreshVal (c : ACache Msg Dg E C) (β : List (Dg × E)) : Prop :=
  c (.inr β) = none ∧ ∀ m, P.unpad β = some m → c (.inl m) = none

omit [DecidableEq Dg] [DecidableEq E] in
/-- A uniform state with its digest part replaced by a uniform digest is a uniform state. -/
theorem uniform_digest_evalDistEq :
    (($ᵗ Dg) >>= fun d => ($ᵗ (SpongeState Dg E C)) >>= fun t =>
      (pure ((d, t.1.2), t.2) : ProbComp (SpongeState Dg E C))) =ᵈ ($ᵗ (SpongeState Dg E C)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (Dg × E) C,
    SampleableType.uniformSample_prod_eq_bind Dg E]
  simp only [bind_assoc, pure_bind]
  exact EvalDistEq.bind_right _ fun d => EvalDistEq.bind_const _ _

/-- **The value of a path asked by nobody is a uniform state.** -/
theorem val_fresh_evalDistEq {β : List (Dg × E)} {c : ACache Msg Dg E C}
    (h : FreshVal P c β) :
    Prod.fst <$> (simulateQ (ASpec Msg Dg E C).romImpl (val P β)).run c =ᵈ
      ($ᵗ (SpongeState Dg E C)) := by
  rcases hm : P.unpad β with _ | m
  · rw [val_run_fresh_none P hm c h.1]
    simp
  · rw [val_run_fresh_some P hm c h.1, randomOracle.run_eq]
    simp only [h.2 m hm, bind_assoc, pure_bind, map_bind, map_pure]
    exact uniform_digest_evalDistEq

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] in
/-- Asking the value of one path leaves every other path asked by nobody. -/
theorem freshVal_of_val_support {β γ : List (Dg × E)} {c c' : ACache Msg Dg E C}
    (hne : γ ≠ β) (hagree : ∀ t, ¬ ValPt (C := C) P β t → c' t = c t) (h : FreshVal P c γ) :
    FreshVal P c' γ := by
  refine ⟨by rw [hagree (.inr γ) (by simpa [ValPt] using hne)]; exact h.1, fun m hm => ?_⟩
  rw [hagree (.inl m) (fun hβ => hne ?_)]
  · exact h.2 m hm
  · simp only [ValPt] at hβ
    rw [← (P.unpad_eq_some_iff γ m).mp hm, ← (P.unpad_eq_some_iff β m).mp hβ]

/-! ## The walk of the full view -/

section Walk

variable [XorOp Dg] [XorOp E] [DecidableEq C] [FinEnum (SpongeState Dg E C)]

/-- **The walk of the full view is the sponge over independent answers.**

Along a path whose prefixes that nobody used are asked by nobody, the two end alike in law. -/
theorem allWalk_evalDistEq (used : List (Dg × E) → Bool) (pre : List (Dg × E))
    (s : SpongeState Dg E C) (A : PermCache (SpongeState Dg E C)) (bs : List (Dg × E))
    (c : ACache Msg Dg E C) (f : Bool)
    (hfresh : ∀ i < bs.length, used (pre ++ bs.take (i + 1)) = false →
      FreshVal P c (pre ++ bs.take (i + 1))) :
    Prod.fst <$> (simulateQ (ASpec Msg Dg E C).romImpl (allWalk P used pre s A bs)).run c =ᵈ
      Prod.map id Prod.fst <$> (absorbAll (fun x => indepPermOracle
        (A := SpongeState Dg E C) (.inl x)) s bs).run (A, f) := by
  induction bs generalizing pre s A c f with
  | nil => simp [allWalk]
  | cons B bs ih =>
    -- The rest of the walk, from any cache that the first value can leave.
    have hrest : ∀ w ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
        (val P (pre ++ [B]))).run c), ∀ (y : SpongeState Dg E C)
        (A' : PermCache (SpongeState Dg E C)) (f' : Bool),
        Prod.fst <$> (simulateQ (ASpec Msg Dg E C).romImpl
          (allWalk P used (pre ++ [B]) y A' bs)).run w.2 =ᵈ
          Prod.map id Prod.fst <$> (absorbAll (fun x => indepPermOracle
            (A := SpongeState Dg E C) (.inl x)) y bs).run (A', f') := by
      intro w hw y A' f'
      obtain ⟨-, -, hagree⟩ := val_support P _ c hw
      refine ih (pre ++ [B]) y A' w.2 f' fun i hi hu => ?_
      have hne : pre ++ [B] ++ bs.take (i + 1) ≠ pre ++ [B] := by
        intro h
        have h2 : bs.take (i + 1) = [] := by simpa using h
        rw [List.take_eq_nil_iff] at h2
        rcases h2 with h2 | h2
        · omega
        · subst h2
          simp at hi
      have := hfresh (i + 1) (by simp; omega) (by simpa [List.take_succ_cons] using hu)
      simp only [List.take_succ_cons] at this
      exact freshVal_of_val_support P hne hagree (by simpa using this)
    simp only [allWalk, absorbAll_cons, simulateQ_bind, StateT.run_bind, drawSt_run,
      bind_map_left, map_bind]
    rw [indepPermOracle_inl_run]
    rcases hx : A.lookup (absorb s B) with _ | y
    · -- A new state: its answer is a new uniform draw on the right.
      simp only [lookup_eq_of_decidableEq hx, bind_map_left]
      by_cases hu : used (pre ++ [B]) = true
      · -- A used path: the walk takes the uniform draw, and the value is discarded.
        simp only [hu, ↓reduceIte]
        refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
          (uniformOutside_nil_evalDistEq (A := SpongeState Dg E C) (absorb s B)).symm _)
        refine EvalDistEq.trans ?_ (EvalDistEq.bind_const
          ((simulateQ (ASpec Msg Dg E C).romImpl (val P (pre ++ [B]))).run c) _)
        exact EvalDistEq.bind_congr_of_support _ fun w hw => EvalDistEq.bind_right _ fun u =>
          hrest w hw u _ _
      · -- A path asked by nobody: its value is a uniform state.
        simp only [Bool.not_eq_true] at hu
        simp only [hu, Bool.false_eq_true, ↓reduceIte]
        refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
          (uniformOutside_nil_evalDistEq (A := SpongeState Dg E C) (absorb s B)).symm _)
        refine EvalDistEq.trans ?_ (bind_fst_evalDistEq (val_fresh_evalDistEq P
          (by simpa using hfresh 0 (by simp) (by simpa using hu))) _)
        exact EvalDistEq.bind_congr_of_support _ fun w hw =>
          (EvalDistEq.bind_const _ _).trans (hrest w hw w.1 _ _)
    · -- A recorded state: both sides follow the recorded pair.
      simp only [lookup_eq_of_decidableEq hx, pure_bind]
      refine (EvalDistEq.bind_congr_of_support _ fun w hw =>
        (EvalDistEq.bind_const _ _).trans (hrest w hw y A f)).trans ?_
      exact EvalDistEq.bind_const _ _

end Walk

/-! ## The paths that the combined game has asked -/

section Used

variable [XorOp Dg] [XorOp E] [DecidableEq C] (iv : SpongeState Dg E C)

/-- The oracles are cached only at used paths and at messages whose padding is used. -/
def UInv (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) : Prop :=
  (∀ β, c (.inr β) ≠ none → usedPath P cs.sim.chains cs.hashed β = true) ∧
    (∀ m, c (.inl m) ≠ none → usedPath P cs.sim.chains cs.hashed (P.pad m) = true)

omit [DecidableEq Msg] [SampleableType Dg] [SampleableType E] [SampleableType C]
  [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- A path that nobody used is asked by nobody. -/
theorem freshVal_of_uInv {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (h : UInv P cs c)
    {β : List (Dg × E)} (hβ : usedPath P cs.sim.chains cs.hashed β = false) :
    FreshVal P c β := by
  refine ⟨by
    by_contra h'
    rw [h.1 β h'] at hβ
    exact Bool.noConfusion hβ, fun m hm => ?_⟩
  by_contra h'
  have := h.2 m h'
  rw [(P.unpad_eq_some_iff β m).mp hm, hβ] at this
  exact Bool.noConfusion this

omit [DecidableEq Msg] [SampleableType Dg] [SampleableType E] [SampleableType C]
  [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- Used paths stay used as rooted paths and hashed messages accumulate. -/
theorem usedPath_mono {VC VC' : List (SpongeState Dg E C × List (Dg × E))} {L L' : List Msg}
    (hVC : ∀ p ∈ VC, p ∈ VC') (hL : ∀ m ∈ L, m ∈ L') {β : List (Dg × E)}
    (h : usedPath P VC L β = true) : usedPath P VC' L' β = true := by
  rw [usedPath_eq_true_iff] at h ⊢
  rcases h with h | ⟨m, hm, h⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact Or.inl (List.mem_map.mpr ⟨p, hVC p hp, rfl⟩)
  · exact Or.inr ⟨m, hL m hm, h⟩

omit [DecidableEq Msg] [SampleableType Dg] [SampleableType E] [SampleableType C]
  [XorOp Dg] [XorOp E] [DecidableEq C] in
/-- A nonempty prefix of the padding of a hashed message is used. -/
theorem usedPath_of_prefix {VC : List (SpongeState Dg E C × List (Dg × E))} {L : List Msg}
    {m : Msg} (hm : m ∈ L) {β : List (Dg × E)} (h : β ≠ [] ∧ β <+: P.pad m) :
    usedPath P VC L β = true := by
  exact usedPath_eq_true_iff.mpr (Or.inr ⟨m, hm, h⟩)

/-- **Every step of the combined game keeps the paths it asks used.** -/
theorem uInv_combStep (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hU : UInv P cs c)
    {z : ((_ × _) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combStep P iv t).run cs)).run c)) : UInv P z.1.2 z.2 := by
  rcases t with (n | x | y) | m
  · obtain ⟨h1, h2⟩ := combStep_coin_support P iv n cs c hz
    rw [h1, h2]
    exact hU
  · obtain ⟨u, r, hr, hz1⟩ := combFwd_support P iv x cs c hz
    rw [hz1]
    rcases visFwd_support P x u cs.sim c hr with ⟨y, hy, hrz⟩ | ⟨s, β, hy, hch, hv, hrz⟩ |
        ⟨hy, hch, hrz⟩
    · -- A recorded query: nothing new is asked.
      simp only [Prod.mk.injEq] at hrz
      obtain ⟨rfl, hc⟩ := hrz
      rw [hc]
      exact hU
    · -- A new rooted state: its path becomes rooted, so used.
      dsimp only at hv hrz
      rw [hrz]
      obtain ⟨-, -, hagree⟩ := val_support P _ c hv
      have hmono : ∀ γ, usedPath P cs.sim.chains cs.hashed γ = true →
          usedPath P ((r.1, β ++ [blockTo s x]) :: cs.sim.chains) cs.hashed γ = true :=
        fun γ h => usedPath_mono P (fun p hp => List.mem_cons_of_mem _ hp) (fun _ h => h) h
      have hnew : usedPath P ((r.1, β ++ [blockTo s x]) :: cs.sim.chains) cs.hashed
          (β ++ [blockTo s x]) = true := by
        simp [usedPath]
      refine ⟨fun γ hγ => ?_, fun m' hm' => ?_⟩
      · by_cases hγβ : γ = β ++ [blockTo s x]
        · subst hγβ
          exact hnew
        · exact hmono γ (hU.1 γ (by rwa [← hagree (.inr γ) (by simpa [ValPt] using hγβ)]))
      · by_cases hm : P.unpad (β ++ [blockTo s x]) = some m'
        · rw [(P.unpad_eq_some_iff _ m').mp hm]
          exact hnew
        · exact hmono _ (hU.2 m' (by rwa [← hagree (.inl m') (by simpa [ValPt] using hm)]))
    · -- A new state that is not rooted: nothing new is asked.
      simp only [Prod.mk.injEq] at hrz
      obtain ⟨rfl, hc⟩ := hrz
      rw [hc]
      exact hU
  · obtain ⟨u, rfl⟩ := combInv_support iv y cs c hz
    have hsim : (invOut iv cs y u).2.sim.chains = cs.sim.chains := by
      simp only [invOut, visInv]
      split <;> rfl
    exact ⟨fun β hβ => by rw [hsim]; exact hU.1 β hβ, fun m hm => by rw [hsim]; exact hU.2 m hm⟩
  · obtain ⟨w, c₁, d, hw, hd, hz1⟩ := combHash_support P iv m cs c hz
    obtain ⟨-, -, hagree, -⟩ := allWalk_support P _ [] iv cs.all (P.pad m) c hw
    obtain ⟨-, -, hagree'⟩ := randomOracle_run_support _ c₁ hd
    rw [hz1]
    have hmono : ∀ β, usedPath P cs.sim.chains cs.hashed β = true →
        usedPath P cs.sim.chains (m :: cs.hashed) β = true := fun β h =>
      usedPath_mono P (fun p hp => hp) (fun m' hm' => List.mem_cons_of_mem _ hm') h
    -- A changed entry is the hash of `m`, or read by the value of a prefix of its padding.
    have hchanged : ∀ t, z.2 t ≠ c t → t = .inl m ∨
        ∃ i < (P.pad m).length, ValPt (C := C) P ((P.pad m).take (i + 1)) t := by
      intro t ht
      by_cases htm : t = .inl m
      · exact Or.inl htm
      · right
        by_contra hno
        push Not at hno
        exact ht ((hagree' t htm).trans (hagree t fun i hi => by simpa using hno i hi))
    refine ⟨fun β hβ => ?_, fun m' hm' => ?_⟩
    · by_cases hc : c (.inr β) = none
      · rcases hchanged (.inr β) (by rw [hc]; exact hβ) with h | ⟨i, hi, h⟩
        · exact absurd h (by simp)
        · simp only [ValPt] at h
          subst h
          exact usedPath_of_prefix P List.mem_cons_self
            ⟨List.ne_nil_of_length_pos (by simp; omega), List.take_prefix _ _⟩
      · exact hmono β (hU.1 β hc)
    · by_cases hc : c (.inl m') = none
      · rcases hchanged (.inl m') (by rw [hc]; exact hm') with h | ⟨i, hi, h⟩
        · simp only [Sum.inl.injEq] at h
          subst h
          exact usedPath_of_prefix P List.mem_cons_self ⟨P.pad_ne_nil m', List.prefix_refl _⟩
        · simp only [ValPt] at h
          rw [(P.unpad_eq_some_iff _ m').mp h]
          exact usedPath_of_prefix P List.mem_cons_self
            ⟨List.ne_nil_of_length_pos (by simp; omega), List.take_prefix _ _⟩
      · exact hmono _ (hU.2 m' hc)

end Used

/-! ## The real world over independent answers, without the repeat flag -/

section Flag

variable [XorOp Dg] [XorOp E] [FinEnum (SpongeState Dg E C)]

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] in
/-- The sponge over independent answers ends alike whatever the repeat flag. -/
theorem absorbAll_indep_flag (s : SpongeState Dg E C) (bs : List (Dg × E))
    (A : PermCache (SpongeState Dg E C)) (f : Bool) :
    Prod.map id Prod.fst <$> (absorbAll (fun x => indepPermOracle
      (A := SpongeState Dg E C) (.inl x)) s bs).run (A, f) =
      Prod.map id Prod.fst <$> (absorbAll (fun x => indepPermOracle
        (A := SpongeState Dg E C) (.inl x)) s bs).run (A, false) := by
  induction bs generalizing s A f with
  | nil => simp
  | cons B bs ih =>
    simp only [absorbAll_cons, StateT.run_bind, map_bind]
    rw [indepPermOracle_inl_run, indepPermOracle_inl_run]
    split
    · simp only [pure_bind]
      exact ih _ _ _
    · simp only [bind_map_left]
      exact bind_congr fun b => (ih _ _ _).trans (ih _ _ _).symm

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] in
/-- A call of the permutation in the real world over independent answers. -/
theorem funImpl_inl (iv : SpongeState Dg E C)
    (t : (unifSpec + PermSpec (SpongeState Dg E C)).Domain) :
    funImpl P iv (.inl t) = indepPermImpl t := rfl

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] in
/-- A hash call in the real world over independent answers is the sponge. -/
theorem funImpl_inr (iv : SpongeState Dg E C) (m : Msg) :
    funImpl P iv (.inr m) = sponge P iv (fun x => indepPermOracle (.inl x)) m := rfl

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] in
/-- The real world over independent answers ends alike whatever the repeat flag. -/
theorem funImpl_flag (iv : SpongeState Dg E C) (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (A : PermCache (SpongeState Dg E C)) (f : Bool) :
    Prod.map id Prod.fst <$> (funImpl P iv t).run (A, f) =
      Prod.map id Prod.fst <$> (funImpl P iv t).run (A, false) := by
  rcases t with (n | x | y) | m
  · rw [funImpl_inl, passthrough_add_inl_run, passthrough_add_inl_run]
    simp [Functor.map_map]
  · rw [funImpl_inl, indepPermImpl_inr, indepPermOracle_inl_run, indepPermOracle_inl_run]
    split <;> simp [Functor.map_map]
  · rw [funImpl_inl, indepPermImpl_inr, indepPermOracle_inr_run, indepPermOracle_inr_run]
    split <;> simp [Functor.map_map]
  · rw [funImpl_inr]
    simp only [sponge, StateT.run_map, Functor.map_map]
    have h := congrArg (fun X => Prod.map SpongeState.out id <$> X)
      (absorbAll_indep_flag iv (P.pad m) A f)
    simp only [Functor.map_map] at h
    exact h

/-- The real world over independent answers, with the repeat flag dropped from the state. -/
def funCacheImpl (iv : SpongeState Dg E C) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (PermCache (SpongeState Dg E C)) ProbComp) :=
  fun t => StateT.mk fun A => Prod.map id Prod.fst <$> (funImpl P iv t).run (A, false)

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] in
/-- **The repeat flag changes no output.** -/
theorem run'_simulateQ_funImpl {α : Type} (iv : SpongeState Dg E C)
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α)
    (A : PermCache (SpongeState Dg E C)) (f : Bool) :
    (simulateQ (funImpl P iv) oa).run' (A, f) = (simulateQ (funCacheImpl P iv) oa).run' A :=
  run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst (fun t s => funImpl_flag P iv t s.1 s.2) oa _

end Flag

/-! ## The real side of the combined game -/

section Step

variable [XorOp Dg] [XorOp E] [DecidableEq C] [FinEnum (SpongeState Dg E C)]
  (iv : SpongeState Dg E C)

omit [FinEnum (SpongeState Dg E C)] in
/-- One step of the folded real side of the combined game. -/
theorem foldReal_run (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) :
    ((foldReal P iv) t).run (cs, c) = (fun z => (z.1.1.1, (z.1.2, z.2))) <$>
      (simulateQ (ASpec Msg Dg E C).romImpl ((combStep P iv t).run cs)).run c := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp [combReal, StateT.run_map, simulateQ_map, Functor.map_map]

/-- **One step of the real side is one step of the real world over independent answers**.

The visible view, the cache of the random oracles and the repeat flag are forgotten. -/
theorem combReal_step_evalDistEq (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) (hU : UInv P cs c) :
    Prod.map id (fun s => s.1.all) <$> ((foldReal P iv) t).run (cs, c) =ᵈ
      (funCacheImpl P iv t).run cs.all := by
  rw [foldReal_run, Functor.map_map]
  change _ =ᵈ Prod.map id Prod.fst <$> (funImpl P iv t).run (cs.all, false)
  rcases t with (n | x | y) | m
  · rw [funImpl_inl, passthrough_add_inl_run]
    simp [combStep, unifFwdImpl, Functor.map_map]
  · rw [funImpl_inl, indepPermImpl_inr, indepPermOracle_inl_run]
    simp only [combStep, combFwd, StateT.run_mk, simulateQ_bind, StateT.run_bind, drawSt_run,
      simulateQ_pure, StateT.run_pure, bind_map_left, map_bind, map_pure]
    rcases hA : cs.all.lookup x with _ | y
    · -- A new pair of the full view.
      simp only [lookup_eq_of_decidableEq hA, fwdOut, Prod.map_apply, id_eq, Functor.map_map]
      refine EvalDistEq.trans ?_
        ((uniformOutside_nil_evalDistEq (A := SpongeState Dg E C) x).symm.map _)
      rcases hy : cs.sim.edges.lookup x with _ | y'
      · rcases hch : chainOf cs.sim.chains x with _ | ⟨s, β⟩
        · -- A new state that is not rooted: the uniform draw.
          simp only [visFwd, hy, hch, simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp]
          exact EvalDistEq.rfl
        · simp only [visFwd, hy, hch, simulateQ_bind, StateT.run_bind, simulateQ_pure,
            StateT.run_pure, bind_assoc, pure_bind]
          by_cases hu : usedPath P cs.sim.chains cs.hashed (β ++ [blockTo s x]) = true
          · -- A used path: the full view takes the uniform draw.
            simp only [hu, ↓reduceIte]
            refine (EvalDistEq.bind_right _ fun u => EvalDistEq.bind_const _ _).trans ?_
            simp only [bind_pure_comp]
            exact EvalDistEq.rfl
          · -- A path asked by nobody: its value is a uniform state.
            simp only [Bool.not_eq_true] at hu
            simp only [hu, Bool.false_eq_true, ↓reduceIte]
            refine (EvalDistEq.bind_const _ _).trans ?_
            refine (bind_fst_evalDistEq (val_fresh_evalDistEq P (freshVal_of_uInv P hU hu))
              (fun v => pure (v, (x, v) :: cs.all))).trans ?_
            simp only [bind_pure_comp]
            exact EvalDistEq.rfl
      · -- A pair of the visible view only: the uniform draw.
        simp only [visFwd, hy, simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp]
        exact EvalDistEq.rfl
    · -- A recorded pair of the full view: both draws are discarded.
      simp only [lookup_eq_of_decidableEq hA, fwdOut, Prod.map_apply, id_eq, map_pure]
      refine (EvalDistEq.bind_right _ fun u => EvalDistEq.bind_const _ _).trans ?_
      exact EvalDistEq.bind_const _ _
  · rw [funImpl_inl, indepPermImpl_inr, indepPermOracle_inr_run]
    simp only [combStep, combInv, StateT.run_mk, simulateQ_bind, StateT.run_bind, drawSt_run,
      simulateQ_pure, StateT.run_pure, bind_map_left, map_bind, map_pure, invOut]
    rcases hA : (cs.all.map Prod.swap).lookup y with _ | x
    · -- A new answer: uniform on both sides.
      simp only [lookup_eq_of_decidableEq hA, Prod.map_apply, id_eq, Functor.map_map,
        bind_pure_comp]
      exact (uniformOutside_nil_evalDistEq (A := SpongeState Dg E C) y).symm.map _
    · -- A recorded answer: the draw is discarded.
      simp only [lookup_eq_of_decidableEq hA, Prod.map_apply, id_eq, map_pure]
      exact EvalDistEq.bind_const _ _
  · rw [funImpl_inr]
    simp only [combStep, combHash, StateT.run_mk, simulateQ_bind, StateT.run_bind, run_queryRight,
      simulateQ_pure, StateT.run_pure, map_bind, map_pure, hashOut, sponge, StateT.run_map,
      Functor.map_map, Prod.map_apply, id_eq]
    -- The hash itself is not part of the real answer.
    refine (EvalDistEq.bind_right _ fun w => EvalDistEq.bind_const _ _).trans ?_
    have hw := (allWalk_evalDistEq P _ [] iv cs.all (P.pad m) c false fun i hi hu =>
      freshVal_of_uInv P hU (by simpa using hu)).map (fun p => (p.1.out, p.2))
    simpa [Functor.map_map, map_eq_bind_pure_comp] using hw

/-- **The real side of the combined game is the real world over independent answers.**

From the first states, both runs give each output with one chance. -/
theorem combReal_run_evalDistEq {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) :
    (simulateQ (foldReal P iv) oa).run' ((CState.init iv : CState Dg E C Msg), ∅) =ᵈ
      (simulateQ (funImpl P iv) oa).run' ([], false) := by
  rw [run'_simulateQ_funImpl]
  exact run'_simulateQ_evalDistEq_of_inv (foldReal P iv) (funCacheImpl P iv)
    (fun s => UInv P s.1 s.2) (fun s => s.1.all)
    (fun t s hs z hz => by
      obtain ⟨w, hw, hz2⟩ := mem_support_foldComb_run P iv (fun _ => Prod.fst) t s hz
      rw [hz2]
      exact uInv_combStep P iv t hs hw)
    (fun t s hs => combReal_step_evalDistEq P iv t s.1 s.2 hs) oa _
    ⟨fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩

end Step

end EthLib.Cryptography.Sponge
