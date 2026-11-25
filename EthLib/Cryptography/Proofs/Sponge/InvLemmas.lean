module

public import EthLib.Cryptography.Proofs.Sponge.Inv

/-!
# Proofs: consequences of the invariant of the combined game

Without a collision, the states at the ends of distinct known paths have distinct capacities.

So distinct paths reach distinct states of the sponge.

The pairs the full view should hold then form a partial bijection.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge.Indiff

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} {P : Padding Msg (Dg × E)} {iv : SpongeState Dg E C}

/-- A path the analysis keeps track of: rooted by the simulator, or hidden. -/
def KnownPath (P : Padding Msg (Dg × E)) (cs : CState Dg E C Msg) (β : List (Dg × E)) : Prop :=
  β ∈ vPaths cs.sim ∨ Hidden P cs.vis β

/-- A prefix of a hashed padding is not empty. -/
theorem HPath.ne_nil {L : List Msg} {β : List (Dg × E)} (h : HPath P L β) : β ≠ [] := by
  obtain ⟨_, _, h, -⟩ := h
  exact h

/-- The state at the end of a nonempty path is its value. -/
theorem svC_of_ne_nil {c : ACache Msg Dg E C} {β : List (Dg × E)} (h : β ≠ []) :
    svC P iv c β = cachedPathValue P c β := by
  simp [svC, h]

/-- The state at the end of a hidden path is its value. -/
theorem svC_of_hidden {vs : VState Dg E C Msg} {c : ACache Msg Dg E C} {β : List (Dg × E)}
    (h : Hidden P vs β) : svC P iv c β = cachedPathValue P c β :=
  svC_of_ne_nil h.1.ne_nil

/-- Without its last block, a prefix of a hashed padding is empty or such a prefix. -/
theorem HPath.init {L : List Msg} {β : List (Dg × E)} {B : Dg × E} (h : HPath P L (β ++ [B])) :
    β = [] ∨ HPath P L β := by
  obtain ⟨m, hm, -, hp⟩ := h
  by_cases hβ : β = []
  · exact Or.inl hβ
  · exact Or.inr ⟨m, hm, hβ, (List.prefix_append β [B]).trans hp⟩

/-- A rooted path has its rooted state. -/
theorem exists_chain_of_mem_vPaths {σ : SimState Dg E C} {β : List (Dg × E)}
    (h : β ∈ vPaths σ) : ∃ s, (s, β) ∈ σ.chains := by
  obtain ⟨⟨s, β'⟩, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨s, hp⟩

/-- The value of a hidden path has no visible capacity. -/
theorem hidden_cap_notMem {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hEC : ¬ HiddenCollision P iv cs.vis c) {β : List (Dg × E)} {v : SpongeState Dg E C}
    (hβ : Hidden P cs.vis β) (hv : cachedPathValue P c β = some v) : v.2 ∉ knownC iv cs.sim :=
  fun h => hEC ⟨β, v, hβ, hv, Or.inl h⟩

section Xor

variable [XorOp Dg] [XorOp E] {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}

/-- The empty path is rooted. -/
theorem nil_mem_vPaths (hS : CombStruct P iv cs c) : ([] : List (Dg × E)) ∈ vPaths cs.sim :=
  List.mem_map.mpr ⟨(iv, []), hS.root, rfl⟩

/-- Known paths stay known without their last block. -/
theorem knownPath_init (hS : CombStruct P iv cs c) {β : List (Dg × E)} {B : Dg × E}
    (h : KnownPath P cs (β ++ [B])) : KnownPath P cs β := by
  rcases h with h | h
  · obtain ⟨v, hv⟩ := exists_chain_of_mem_vPaths h
    obtain ⟨q, hq, B', hβ, -⟩ := hS.chainEdge _ hv (by simp)
    have : β = q.2 := (List.append_inj' hβ rfl).1
    exact Or.inl (List.mem_map.mpr ⟨q, hq, this.symm⟩)
  · rcases h.1.init with h' | h'
    · subst h'
      exact Or.inl (nil_mem_vPaths hS)
    · by_cases hv : β ∈ vPaths cs.sim
      · exact Or.inl hv
      · exact Or.inr ⟨h', hv⟩

/-- Rooted states with the same capacity are the same. -/
theorem chain_eq_of_cap (hC : VisCons cs.sim) {p q : SpongeState Dg E C × List (Dg × E)}
    (hp : p ∈ cs.sim.chains) (hq : q ∈ cs.sim.chains) (h : p.1.2 = q.1.2) : p = q :=
  List.inj_on_of_nodup_map hC.chainCap hp hq h

/-- Rooted states with the same path are the same. -/
theorem chain_eq_of_path (hS : CombStruct P iv cs c) (hC : VisCons cs.sim)
    {p q : SpongeState Dg E C × List (Dg × E)} (hp : p ∈ cs.sim.chains)
    (hq : q ∈ cs.sim.chains) (h : p.2 = q.2) : p = q := by
  have h1 := hS.chainVal p hp
  have h2 := hS.chainVal q hq
  rw [h] at h1
  rw [h1] at h2
  exact chain_eq_of_cap hC hp hq (by rw [Option.some.inj h2])

/-- **Capacities determine known paths.**

Without a collision, the states at the ends of distinct known paths have distinct capacities. -/
theorem sv_cap_inj (hS : CombStruct P iv cs c) (hC : VisCons cs.sim)
    (hEC : ¬ HiddenCollision P iv cs.vis c)
    {β γ : List (Dg × E)} {s s' : SpongeState Dg E C} (hβ : KnownPath P cs β)
    (hγ : KnownPath P cs γ) (hs : svC P iv c β = some s) (hs' : svC P iv c γ = some s')
    (h : s.2 = s'.2) : β = γ := by
  -- The value of a hidden path has no rooted capacity.
  have hid_vis : ∀ {β γ : List (Dg × E)} {s s' : SpongeState Dg E C}, Hidden P cs.vis β →
      γ ∈ vPaths cs.sim → svC P iv c β = some s → svC P iv c γ = some s' → s.2 = s'.2 →
      False := by
    intro β γ s s' hβ hγ hs hs' h
    obtain ⟨t, ht⟩ := exists_chain_of_mem_vPaths hγ
    have := hS.chainVal _ ht
    rw [hs'] at this
    obtain rfl := Option.some.inj this
    refine hEC ⟨β, s, hβ, (svC_of_hidden hβ) ▸ hs, Or.inl ?_⟩
    rw [h]
    exact chain_cap_mem_knownC iv P hS ht
  rcases hβ with hβ | hβ <;> rcases hγ with hγ | hγ
  · obtain ⟨t, ht⟩ := exists_chain_of_mem_vPaths hβ
    obtain ⟨t', ht'⟩ := exists_chain_of_mem_vPaths hγ
    have e1 := hS.chainVal _ ht
    have e2 := hS.chainVal _ ht'
    rw [hs] at e1
    rw [hs'] at e2
    obtain rfl := Option.some.inj e1
    obtain rfl := Option.some.inj e2
    exact (Prod.mk.inj (chain_eq_of_cap hC ht ht' h)).2
  · exact (hid_vis hγ hβ hs' hs h.symm).elim
  · exact (hid_vis hβ hγ hs hs' h).elim
  · by_contra hne
    exact hEC ⟨β, s, hβ, (svC_of_hidden hβ) ▸ hs, Or.inr ⟨γ, s', hγ, Ne.symm hne,
      (svC_of_hidden hγ) ▸ hs', h.symm⟩⟩

/-- A rooted pair of the simulator is the step into the value of its rooted path. -/
theorem rootedEdge_spec (hS : CombStruct P iv cs c) {e : SpongeState Dg E C × SpongeState Dg E C}
    (h : RootedEdge cs.sim e) :
    ∃ β B s, (β ++ [B]) ∈ vPaths cs.sim ∧ svC P iv c β = some s ∧
      cachedPathValue P c (β ++ [B]) = some e.2 ∧ e.1 = absorb s B := by
  obtain ⟨s, β, B, hs, hv, he⟩ := h
  refine ⟨β, B, s, List.mem_map.mpr ⟨_, hv, rfl⟩, hS.chainVal _ hs, ?_, he⟩
  simpa [svC] using hS.chainVal _ hv

/-- The query of a pair that is not rooted is no state of the sponge on a known path. -/
theorem unrooted_ne_node (hS : CombStruct P iv cs c) (hEC : ¬ HiddenCollision P iv cs.vis c)
    {e : SpongeState Dg E C × SpongeState Dg E C} (he : e ∈ cs.sim.edges)
    (hun : ∀ p ∈ cs.sim.chains, p.1.2 ≠ e.1.2) {β : List (Dg × E)} {B : Dg × E}
    {s : SpongeState Dg E C} (hβ : KnownPath P cs β) (hs : svC P iv c β = some s) :
    e.1 ≠ absorb s B := by
  intro hx
  have hcap : e.1.2 = s.2 := by rw [hx]; rfl
  rcases hβ with hβ | hβ
  · obtain ⟨t, ht⟩ := exists_chain_of_mem_vPaths hβ
    have := hS.chainVal _ ht
    rw [hs] at this
    obtain rfl := Option.some.inj this
    exact hun _ ht hcap.symm
  · refine hEC ⟨β, s, hβ, (svC_of_hidden hβ) ▸ hs, Or.inl ?_⟩
    rw [← hcap]
    exact fst_mem_knownC iv he

/-- The pairs the full view should hold have distinct answers. -/
theorem gEdge_snd_inj (hS : CombStruct P iv cs c) (hC : VisCons cs.sim)
    (hEC : ¬ HiddenCollision P iv cs.vis c)
    {e e' : SpongeState Dg E C × SpongeState Dg E C} (he : GEdge P iv cs c e)
    (he' : GEdge P iv cs c e') (h : e.2 = e'.2) : e = e' := by
  rcases he with he | ⟨β, B, s, v, hβ, hs, hv, rfl⟩ <;>
    rcases he' with he' | ⟨β', B', s', v', hβ', hs', hv', rfl⟩
  · exact List.inj_on_of_nodup_map hC.vVals he he' h
  · have hk := snd_mem_knownC iv he
    simp only at h
    rw [h] at hk
    exact absurd hk (hidden_cap_notMem hEC hβ' hv')
  · have hk := snd_mem_knownC iv he'
    simp only at h
    rw [← h] at hk
    exact absurd hk (hidden_cap_notMem hEC hβ hv)
  · simp only at h
    subst h
    have hp := sv_cap_inj hS hC hEC (Or.inr hβ) (Or.inr hβ')
      ((svC_of_hidden hβ).trans hv) ((svC_of_hidden hβ').trans hv') rfl
    obtain ⟨rfl, hBB⟩ := List.append_inj' hp rfl
    obtain rfl : B = B' := List.singleton_inj.mp hBB
    rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    rfl

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- **States of the sponge determine known paths.** -/
theorem node_inj (hS : CombStruct P iv cs c) (hC : VisCons cs.sim)
    (hEC : ¬ HiddenCollision P iv cs.vis c)
    {β γ : List (Dg × E)} {B B' : Dg × E} {s s' : SpongeState Dg E C}
    (hβ : KnownPath P cs (β ++ [B])) (hγ : KnownPath P cs (γ ++ [B']))
    (hs : svC P iv c β = some s) (hs' : svC P iv c γ = some s')
    (h : absorb s B = absorb s' B') : β = γ ∧ B = B' := by
  have hcap : s.2 = s'.2 := by simpa using congrArg Prod.snd h
  obtain rfl := sv_cap_inj hS hC hEC (knownPath_init hS hβ) (knownPath_init hS hγ) hs hs' hcap
  rw [hs] at hs'
  obtain rfl := Option.some.inj hs'
  exact ⟨rfl, absorb_injective s h⟩

/-- The pairs the full view should hold have distinct queries. -/
theorem gEdge_fst_inj (hS : CombStruct P iv cs c) (hC : VisCons cs.sim)
    (hEC : ¬ HiddenCollision P iv cs.vis c)
    {e e' : SpongeState Dg E C × SpongeState Dg E C} (he : GEdge P iv cs c e)
    (he' : GEdge P iv cs c e') (h : e.1 = e'.1) : e = e' := by
  rcases he with he | ⟨β, B, s, v, hβ, hs, hv, rfl⟩ <;>
    rcases he' with he' | ⟨β', B', s', v', hβ', hs', hv', rfl⟩
  · exact List.inj_on_of_nodup_map hC.vKeys he he' h
  · rcases hC.vClass e he with hr | hun
    · obtain ⟨γ, G, t, hγ, ht, -, hx⟩ := rootedEdge_spec hS hr
      obtain ⟨rfl, rfl⟩ := node_inj hS hC hEC (Or.inl hγ) (Or.inr hβ') ht hs' (hx ▸ h)
      exact absurd hγ hβ'.2
    · exact absurd h (unrooted_ne_node hS hEC he hun (knownPath_init hS (Or.inr hβ')) hs')
  · rcases hC.vClass e' he' with hr | hun
    · obtain ⟨γ, G, t, hγ, ht, -, hx⟩ := rootedEdge_spec hS hr
      obtain ⟨rfl, rfl⟩ := node_inj hS hC hEC (Or.inl hγ) (Or.inr hβ) ht hs (hx ▸ h.symm)
      exact absurd hγ hβ.2
    · exact absurd h.symm (unrooted_ne_node hS hEC he' hun (knownPath_init hS (Or.inr hβ)) hs)
  · obtain ⟨rfl, rfl⟩ := node_inj hS hC hEC (Or.inr hβ) (Or.inr hβ') hs hs' h
    rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    rfl

end Xor

end EthLib.Cryptography.Sponge.Indiff
