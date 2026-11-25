module

public import EthLib.Cryptography.Proofs.Sponge.InvHash

/-!
# Proofs: the invariant holds along every run of the combined game

The first state satisfies the invariant, and every step of the combined game keeps it.

So an answer of the full view differs from that of the simulator only after a collision.

The random oracles of the game are folded into its state, so the run is a run over coins.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg] [SampleableType Dg]
  [SampleableType E] [SampleableType C] in
/-- The first state satisfies the invariant. -/
theorem inv_init : Inv P iv (CState.init iv : CState Dg E C Msg) ∅ := by
  refine ⟨⟨List.mem_singleton_self _, fun p hp => ?_, fun p hp hne => ?_, fun β hβ => ?_⟩,
    fun _ _ => ⟨⟨by simp [CState.init, SimState.init], by simp [CState.init, SimState.init],
      by simp [CState.init, SimState.init], by simp [CState.init, SimState.init]⟩,
      fun e => ?_, rfl⟩⟩
  · simp only [CState.init, SimState.init, List.mem_singleton] at hp
    subst hp
    simp [svC]
  · simp only [CState.init, SimState.init, List.mem_singleton] at hp
    subst hp
    exact absurd rfl hne
  · simp [CState.init, HPath] at hβ
  · simp only [CState.init, SimState.init, GEdge, List.not_mem_nil, false_or, false_iff]
    rintro ⟨β, B, s, v, hβ, -⟩
    simp [Hidden, CState.vis, HPath] at hβ

/-- A coin of the combined game keeps the state and the cache. -/
theorem combStep_coin_support (n : ℕ) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    {z : ((Fin (n + 1) × Fin (n + 1)) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combStep P iv (.inl (.inl n))).run cs)).run c)) : z.1.2 = cs ∧ z.2 = c := by
  simp [combStep, unifFwdImpl] at hz
  obtain ⟨a, rfl⟩ := hz
  exact ⟨rfl, rfl⟩

/-- The combined game with its random oracles folded into the state, with chosen answers. -/
noncomputable abbrev foldComb
    (sel : (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain) →
      (GameSpec (SpongeState Dg E C) Msg Dg).Range t ×
        (GameSpec (SpongeState Dg E C) Msg Dg).Range t →
          (GameSpec (SpongeState Dg E C) Msg Dg).Range t) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (CState Dg E C Msg × ACache Msg Dg E C) ProbComp) :=
  ((ASpec Msg Dg E C).romImpl.mapStateTBase fun t => sel t <$> combStep P iv t).flattenStateT

/-- The steps of the folded game reach the states of the combined step. -/
theorem mem_support_foldComb_run
    (sel : (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain) →
      (GameSpec (SpongeState Dg E C) Msg Dg).Range t ×
        (GameSpec (SpongeState Dg E C) Msg Dg).Range t →
          (GameSpec (SpongeState Dg E C) Msg Dg).Range t)
    (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (s : CState Dg E C Msg × ACache Msg Dg E C) {z}
    (hz : z ∈ support ((foldComb P iv sel t).run s)) :
    ∃ w ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combStep P iv t).run s.1)).run s.2), z.2 = (w.1.2, w.2) := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run] at hz
  simp only [StateT.run_map, simulateQ_map, support_map, Set.mem_image] at hz
  obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
  exact ⟨w', hw', rfl⟩

/-- The ideal side of the combined game, with its random oracles folded into the state. -/
noncomputable abbrev foldIdeal :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (CState Dg E C Msg × ACache Msg Dg E C) ProbComp) :=
  ((ASpec Msg Dg E C).romImpl.mapStateTBase (combIdeal P iv)).flattenStateT

/-- The real side of the combined game, with its random oracles folded into the state. -/
noncomputable abbrev foldReal :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (CState Dg E C Msg × ACache Msg Dg E C) ProbComp) :=
  ((ASpec Msg Dg E C).romImpl.mapStateTBase (combReal P iv)).flattenStateT

/-- The folded ideal side is the folded game with the ideal answers. -/
theorem foldIdeal_eq : foldIdeal P iv = foldComb P iv (fun _ => Prod.snd) := rfl

/-- The folded real side is the folded game with the real answers. -/
theorem foldReal_eq : foldReal P iv = foldComb P iv (fun _ => Prod.fst) := rfl

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- **Every step of the combined game keeps the invariant.** -/
theorem inv_combStep (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hI : Inv P iv cs c)
    {z : ((_ × _) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combStep P iv t).run cs)).run c)) : Inv P iv z.1.2 z.2 := by
  rcases t with (n | x | y) | m
  · obtain ⟨h1, h2⟩ := combStep_coin_support P iv n cs c hz
    rw [h1, h2]
    exact hI
  · exact inv_combFwd hI x hz
  · obtain ⟨u, rfl⟩ := combInv_support iv y cs c hz
    exact inv_invOut u hI y
  · exact inv_combHash hI m hz

/-- The invariant holds after every step of the folded game, with either answer. -/
theorem inv_foldComb_step
    (sel : (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain) →
      (GameSpec (SpongeState Dg E C) Msg Dg).Range t ×
        (GameSpec (SpongeState Dg E C) Msg Dg).Range t →
          (GameSpec (SpongeState Dg E C) Msg Dg).Range t)
    (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (s : CState Dg E C Msg × ACache Msg Dg E C) (hs : Inv P iv s.1 s.2)
    {z} (hz : z ∈ support ((foldComb P iv sel t).run s)) : Inv P iv z.2.1 z.2.2 := by
  obtain ⟨w, hw, hz2⟩ := mem_support_foldComb_run P iv sel t s hz
  rw [hz2]
  exact inv_combStep P iv t hs hw

/-- **Answers differ only after a collision.**

On every run of the folded game from the first state, a differing answer means a collision. -/
theorem diff_imp_bad_or_EC
    (sel : (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain) →
      (GameSpec (SpongeState Dg E C) Msg Dg).Range t ×
        (GameSpec (SpongeState Dg E C) Msg Dg).Range t →
          (GameSpec (SpongeState Dg E C) Msg Dg).Range t) {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α)
    {z} (hz : z ∈ support ((simulateQ (foldComb P iv sel) oa).run
      ((CState.init iv : CState Dg E C Msg), ∅))) :
    z.2.1.diff = true → z.2.1.bad = true ∨ EC P iv z.2.1.vis z.2.2 := by
  have hI := simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _
    (fun s => Inv P iv s.1 s.2) (fun t s hs z hz => inv_foldComb_step P iv sel t s hs hz) oa _
    (inv_init P iv) z hz
  intro hdiff
  by_contra h
  push Not at h
  have hC := hI.2 (by simpa using h.1) h.2
  rw [hC.noDiff] at hdiff
  exact Bool.false_ne_true hdiff

end EthLib.Cryptography.Sponge
