module

public import EthLib.Cryptography.Proofs.Sponge.Inv

/-!
# Proofs: the simulator over path values asks the oracle on paths only at rooted paths

Along a run, the oracle on paths is asked only at the paths of rooted states, each at most once.

So the value of a new rooted state is a new uniform draw.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge.Indiff

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]
  {P : Padding Msg (Dg × E)} {iv : SpongeState Dg E C}

/-- The bookkeeping of the simulator over path values. -/
structure VStruct (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (σ : SimState Dg E C)
    (c : ACache Msg Dg E C) : Prop where
  /-- The initial state is rooted at the empty path. -/
  root : (iv, []) ∈ σ.chains
  /-- A rooted state is the state at the end of its path. -/
  chainVal : ∀ p ∈ σ.chains, svC P iv c p.2 = some p.1
  /-- A rooted state with a nonempty path is one step of the simulator from its parent. -/
  chainEdge : ∀ p ∈ σ.chains, p.2 ≠ [] → ∃ q ∈ σ.chains, ∃ B,
    p.2 = q.2 ++ [B] ∧ (absorb q.1 B, p.1) ∈ σ.edges
  /-- Rooted paths are distinct. -/
  pathsNodup : (σ.chains.map Prod.snd).Nodup
  /-- The oracle on paths has been asked at rooted paths only. -/
  tFresh : ∀ β, c (.inr β) ≠ none → β ∈ σ.chains.map Prod.snd

/-- The initial state satisfies the bookkeeping. -/
theorem vStruct_init : VStruct P iv (SimState.init iv) (∅ : ACache Msg Dg E C) := by
  refine ⟨List.mem_singleton_self _, fun p hp => ?_, fun p hp hne => ?_, by simp [SimState.init],
    fun β hβ => by simp at hβ⟩
  · simp only [SimState.init, List.mem_singleton] at hp
    subst hp
    simp [svC]
  · simp only [SimState.init, List.mem_singleton] at hp
    subst hp
    exact absurd rfl hne

/-- The bookkeeping survives new pairs and a growing cache with no new path-oracle answer. -/
theorem VStruct.mono {σ σ' : SimState Dg E C} {c c' : ACache Msg Dg E C}
    (hV : VStruct P iv σ c) (hc : c ≤ c') (hT : ∀ β, c' (.inr β) = c (.inr β))
    (hch : σ'.chains = σ.chains) (hed : ∀ e ∈ σ.edges, e ∈ σ'.edges) :
    VStruct P iv σ' c' := by
  refine ⟨hch ▸ hV.root, fun p hp => svC_mono hc (hV.chainVal p (hch ▸ hp)),
    fun p hp hne => ?_, hch ▸ hV.pathsNodup, fun β hβ => ?_⟩
  · obtain ⟨q, hq, B, h1, h2⟩ := hV.chainEdge p (hch ▸ hp) hne
    exact ⟨q, hch ▸ hq, B, h1, hed _ h2⟩
  · rw [hch]
    exact hV.tFresh β (by rwa [← hT β])

section Rooted

variable [DecidableEq Dg] [DecidableEq E] [DecidableEq C]
  [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- The path of a new rooted state is not yet rooted. -/
theorem rootedPath_notMem {σ : SimState Dg E C} {c : ACache Msg Dg E C}
    (hV : VStruct P iv σ c) {x s : SpongeState Dg E C} {β : List (Dg × E)}
    (hy : σ.edges.lookup x = none) (hch : chainOf σ.chains x = some (s, β)) :
    β ++ [blockTo s x] ∉ σ.chains.map Prod.snd := by
  intro h
  have hsβ := mem_of_chainOf_eq_some hch
  have hsx := cap_eq_of_chainOf_eq_some hch
  obtain ⟨⟨v₀, β'⟩, hv₀, rfl⟩ := List.mem_map.mp h
  obtain ⟨q, hq, B, h1, h2⟩ := hV.chainEdge _ hv₀ (by simp)
  obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
  obtain rfl := List.singleton_inj.mp h4
  have := List.inj_on_of_nodup_map hV.pathsNodup hq hsβ h3.symm
  subst this
  exact notMem_of_lookup_eq_none hy _ (by simpa [absorb_blockTo hsx] using h2)

variable [DecidableEq Msg] [SampleableType Dg] [SampleableType E] [SampleableType C]

/-- **The forward step of the simulator over path values keeps the bookkeeping.** -/
theorem vStruct_visFwd {σ : SimState Dg E C} {c : ACache Msg Dg E C} (hV : VStruct P iv σ c)
    (x u : SpongeState Dg E C) {z} (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      (visFwd P x u σ)).run c)) : VStruct P iv z.1.2.1 z.2 := by
  rcases visFwd_support P x u σ c hz with ⟨y, hy, rfl⟩ | ⟨s, β, hy, hch, hv, hrz⟩ |
      ⟨hy, hch, rfl⟩
  · exact hV
  · rw [hrz]
    have hsβ := mem_of_chainOf_eq_some hch
    have hsx := cap_eq_of_chainOf_eq_some hch
    obtain ⟨hcc, hvv, hagree⟩ := pathValue_support P _ c hv
    have hnot := rootedPath_notMem hV hy hch
    refine ⟨List.mem_cons_of_mem _ hV.root, fun p hp => ?_, fun p hp hne => ?_,
      List.nodup_cons.mpr ⟨hnot, hV.pathsNodup⟩, fun γ hγ => ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · simpa [svC] using hvv
      · exact svC_mono hcc (hV.chainVal p hp)
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨(s, β), List.mem_cons_of_mem _ hsβ, _, rfl, by
          rw [absorb_blockTo hsx]
          exact List.mem_cons_self⟩
      · obtain ⟨q, hq, B, h1, h2⟩ := hV.chainEdge p hp hne
        exact ⟨q, List.mem_cons_of_mem _ hq, B, h1, List.mem_cons_of_mem _ h2⟩
    · by_cases hγβ : γ = β ++ [blockTo s x]
      · subst hγβ
        exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (hV.tFresh γ ?_)
        rwa [← hagree (.inr γ) (by simpa [ValPt] using hγβ)]
  · exact hV.mono le_rfl (fun _ => rfl) rfl fun e he => List.mem_cons_of_mem _ he

end Rooted

section Run

variable [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]

variable (P) in
/-- A coin of the simulator over path values. -/
theorem idealT_coin_run (n : ℕ) (σ : SimState Dg E C) (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl ((idealTImpl P (.inl (.inl n))).run σ)).run c =
      (fun u => ((u, σ), c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp [idealTImpl, unifFwdImpl]

variable (P) in
/-- A hash query of the simulator over path values. -/
theorem idealT_hash_run (m : Msg) (σ : SimState Dg E C) (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl ((idealTImpl P (.inr m)).run σ)).run c =
      (fun w => ((w.1, σ), w.2)) <$> ((ASpec Msg Dg E C).randomOracle (.inl m)).run c := by
  simp [idealTImpl]

variable (P) in
/-- An inverse query of the simulator over path values. -/
theorem idealT_inv_run (y : SpongeState Dg E C) (σ : SimState Dg E C) (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl ((idealTImpl P (.inl (.inr (.inr y)))).run σ)).run c =
      (fun u => (visInv y u σ, c)) <$> ($ᵗ (SpongeState Dg E C)) := by
  simp only [idealTImpl, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

variable (P) in
/-- A forward query of the simulator over path values. -/
theorem idealT_fwd_run (x : SpongeState Dg E C) (σ : SimState Dg E C) (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl ((idealTImpl P (.inl (.inr (.inl x)))).run σ)).run c =
      ($ᵗ (SpongeState Dg E C)) >>= fun u => (fun w => ((w.1.1, w.1.2.1), w.2)) <$>
        (simulateQ (ASpec Msg Dg E C).romImpl (visFwd P x u σ)).run c := by
  simp only [idealTImpl, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- **Every step of the simulator over path values keeps the bookkeeping.** -/
theorem vStruct_idealT (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    {σ : SimState Dg E C} {c : ACache Msg Dg E C} (hV : VStruct P iv σ c) {z}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((idealTImpl P t).run σ)).run c)) : VStruct P iv z.1.2 z.2 := by
  rcases t with (n | x | y) | m
  · rw [idealT_coin_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hV
  · rw [idealT_fwd_run] at hz
    simp only [mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
      support_map, Set.mem_image] at hz
    obtain ⟨u, w, hw, rfl⟩ := hz
    exact vStruct_visFwd hV x u hw
  · rw [idealT_inv_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨u, -, rfl⟩ := hz
    simp only [visInv]
    split
    · exact hV
    · exact hV.mono le_rfl (fun _ => rfl) rfl fun e he => List.mem_cons_of_mem _ he
  · rw [idealT_hash_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hc, -, hagree⟩ := caches_of_mem_support_randomOracle_run _ c hw
    exact hV.mono hc (fun β => hagree _ (by simp)) rfl fun e he => he

end Run

end EthLib.Cryptography.Sponge.Indiff
