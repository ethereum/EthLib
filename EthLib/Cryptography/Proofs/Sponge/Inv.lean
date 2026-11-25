module

public import EthLib.Cryptography.Proofs.Sponge.Support

/-!
# Proofs: the invariant of the combined game of the sponge

The full and the visible view of the combined game answer alike until a collision.

A visible collision is a draw of the simulator at a capacity it has already seen.

A hidden collision is the value of a path that only the sponge asked, at a capacity seen elsewhere.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type}

/-! ## Lookups -/

section Lookup

variable {A : Type} [DecidableEq A]

/-- A lookup finds the answer of a recorded pair whose query is unique. -/
theorem lookup_eq_some_of_mem {c : PermCache A} {x y : A} (h : (x, y) ∈ c)
    (huniq : ∀ e ∈ c, e.1 = x → e.2 = y) : c.lookup x = some y := by
  induction c with
  | nil => simp at h
  | cons e c ih =>
    obtain ⟨a, b⟩ := e
    by_cases hax : x = a
    · subst hax
      simp only [List.lookup, beq_self_eq_true]
      exact congrArg some (huniq (x, b) List.mem_cons_self rfl)
    · simp only [List.lookup, beq_false_of_ne hax]
      rcases List.mem_cons.mp h with h | h
      · exact absurd (Prod.mk.inj h).1 hax
      · exact ih h fun e he => huniq e (List.mem_cons_of_mem _ he)

/-- A reversed lookup finds the query of a recorded pair whose answer is unique. -/
theorem lookup_swap_eq_some_of_mem {c : PermCache A} {x y : A} (h : (x, y) ∈ c)
    (huniq : ∀ e ∈ c, e.2 = y → e.1 = x) : (c.map Prod.swap).lookup y = some x :=
  lookup_eq_some_of_mem (List.mem_map.mpr ⟨(x, y), h, rfl⟩) fun e he hey => by
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact huniq e' he' hey

/-- A lookup that finds an answer found a recorded pair, for any decidable equality. -/
theorem pair_mem_of_lookup_eq_some {c : PermCache A} {x y : A} (h : c.lookup x = some y) :
    (x, y) ∈ c := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- A reversed lookup that finds a query found a recorded pair. -/
theorem pair_mem_of_lookup_swap_eq_some {c : PermCache A} {x y : A}
    (h : (c.map Prod.swap).lookup y = some x) : (x, y) ∈ c := by
  obtain ⟨⟨a, b⟩, he, hxy⟩ := List.mem_map.mp (pair_mem_of_lookup_eq_some h)
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  exact he

/-- A lookup finds nothing when no recorded pair has the query. -/
theorem lookup_eq_none_of_forall {c : PermCache A} {x : A} (h : ∀ y, (x, y) ∉ c) :
    c.lookup x = none := by
  cases hx : c.lookup x with
  | none => rfl
  | some y => exact absurd (pair_mem_of_lookup_eq_some hx) (h y)

/-- A reversed lookup finds nothing when no recorded pair has the answer. -/
theorem lookup_swap_eq_none_of_forall {c : PermCache A} {y : A} (h : ∀ x, (x, y) ∉ c) :
    (c.map Prod.swap).lookup y = none := by
  cases hy : (c.map Prod.swap).lookup y with
  | none => rfl
  | some x => exact absurd (pair_mem_of_lookup_swap_eq_some hy) (h x)

/-- A lookup that finds nothing has no recorded pair with the query. -/
theorem notMem_of_lookup_eq_none {c : PermCache A} {x : A} (h : c.lookup x = none) (y : A) :
    (x, y) ∉ c := fun hm => by
  have := List.lookup_eq_none_iff.mp h _ hm
  simp at this

/-- A reversed lookup that finds nothing has no recorded pair with the answer. -/
theorem notMem_of_lookup_swap_eq_none {c : PermCache A} {y : A}
    (h : (c.map Prod.swap).lookup y = none) (x : A) : (x, y) ∉ c := fun hm =>
  notMem_of_lookup_eq_none h x (List.mem_map.mpr ⟨(x, y), hm, rfl⟩)

/-- A lookup that finds nothing means the query is no recorded query. -/
theorem notMem_map_fst_of_lookup_none {c : PermCache A} {x : A} (h : c.lookup x = none) :
    x ∉ c.map Prod.fst := fun hx => by
  obtain ⟨⟨a, b⟩, he, rfl⟩ := List.mem_map.mp hx
  exact notMem_of_lookup_eq_none h b he

/-- A reversed lookup that finds nothing means the answer is no recorded answer. -/
theorem notMem_map_snd_of_lookup_swap_none {c : PermCache A} {y : A}
    (h : (c.map Prod.swap).lookup y = none) : y ∉ c.map Prod.snd := fun hy => by
  obtain ⟨⟨a, b⟩, he, rfl⟩ := List.mem_map.mp hy
  exact notMem_of_lookup_swap_eq_none h a he

end Lookup

/-- The rooted state that the simulator finds is a rooted state with that capacity. -/
theorem chainOf_some [DecidableEq C] {VC : List (SpongeState Dg E C × List (Dg × E))}
    {x s : SpongeState Dg E C} {β : List (Dg × E)} (h : chainOf VC x = some (s, β)) :
    (s, β) ∈ VC ∧ s.2 = x.2 := by
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨List.mem_of_find?_eq_some h, h2⟩

/-- When the simulator finds no rooted state, none has that capacity. -/
theorem chainOf_none [DecidableEq C] {VC : List (SpongeState Dg E C × List (Dg × E))}
    {x : SpongeState Dg E C} (h : chainOf VC x = none) : ∀ p ∈ VC, p.1.2 ≠ x.2 := by
  intro p hp hpx
  have := List.find?_eq_none.mp h p hp
  simp [hpx] at this

/-! ## Paths -/

/-- The rooted paths of the simulator, with the empty path. -/
def vPaths (σ : SimState Dg E C) : List (List (Dg × E)) := σ.chains.map Prod.snd

/-- A nonempty prefix of the padding of a hashed message. -/
def HPath (P : Padding Msg (Dg × E)) (hashed : List Msg) (β : List (Dg × E)) : Prop :=
  ∃ m ∈ hashed, β ≠ [] ∧ β <+: P.pad m

/-- A hidden path: a prefix of a hashed padding that the simulator has not rooted. -/
def Hidden (P : Padding Msg (Dg × E)) (vs : VState Dg E C Msg) (β : List (Dg × E)) : Prop :=
  HPath P vs.2.1 β ∧ β ∉ vPaths vs.1

/-- The state at the end of a path: `iv` for the empty path, the cached value otherwise. -/
noncomputable def svC (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)
    (c : ACache Msg Dg E C) (β : List (Dg × E)) : Option (SpongeState Dg E C) :=
  if β = [] then some iv else valC P c β

/-- **A hidden collision.**

The value of a hidden path has a visible capacity, or that of another hidden path. -/
def EC (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) : Prop :=
  ∃ β v, Hidden P vs β ∧ valC P c β = some v ∧
    (v.2 ∈ knownC iv vs.1 ∨ ∃ γ w, Hidden P vs γ ∧ γ ≠ β ∧ valC P c γ = some w ∧ w.2 = v.2)

section Edges

variable [XorOp Dg] [XorOp E]

/-- A hidden pair: the step of the sponge into the value of a hidden path. -/
def HiddenEdge (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) (e : SpongeState Dg E C × SpongeState Dg E C) : Prop :=
  ∃ β B s v, Hidden P vs (β ++ [B]) ∧ svC P iv c β = some s ∧
    valC P c (β ++ [B]) = some v ∧ e = (absorb s B, v)

/-- A rooted pair of the simulator: from a rooted state, one block on, to a rooted state. -/
def RootedEdge (σ : SimState Dg E C) (e : SpongeState Dg E C × SpongeState Dg E C) : Prop :=
  ∃ s β B, (s, β) ∈ σ.chains ∧ (e.2, β ++ [B]) ∈ σ.chains ∧ e.1 = absorb s B

/-- The pairs the full view should hold: the visible ones and the hidden ones. -/
def GEdge (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) (e : SpongeState Dg E C × SpongeState Dg E C) : Prop :=
  e ∈ cs.sim.edges ∨ HiddenEdge P iv cs.vis c e

/-- The facts of the combined game that hold on every run. -/
structure Struct (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) : Prop where
  /-- The initial state is rooted at the empty path. -/
  root : (iv, []) ∈ cs.sim.chains
  /-- A rooted state is the state at the end of its path. -/
  chainVal : ∀ p ∈ cs.sim.chains, svC P iv c p.2 = some p.1
  /-- A rooted state with a nonempty path is one step of the simulator from its parent. -/
  chainEdge : ∀ p ∈ cs.sim.chains, p.2 ≠ [] → ∃ q ∈ cs.sim.chains, ∃ B,
    p.2 = q.2 ++ [B] ∧ (absorb q.1 B, p.1) ∈ cs.sim.edges
  /-- The value of every prefix of a hashed padding is cached. -/
  hCached : ∀ β, HPath P cs.hashed β → valC P c β ≠ none

/-- The facts about the state of the simulator that hold until a collision. -/
structure VisCons (σ : SimState Dg E C) : Prop where
  /-- Rooted states have distinct capacities. -/
  chainCap : (σ.chains.map fun p => p.1.2).Nodup
  /-- The recorded pairs have distinct queries. -/
  vKeys : (σ.edges.map Prod.fst).Nodup
  /-- The recorded pairs have distinct answers. -/
  vVals : (σ.edges.map Prod.snd).Nodup
  /-- A recorded pair is rooted, or its query has no rooted capacity. -/
  vClass : ∀ e ∈ σ.edges, RootedEdge σ e ∨ ∀ p ∈ σ.chains, p.1.2 ≠ e.1.2

/-- The facts of the combined game that hold until a collision. -/
structure Cons (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) : Prop where
  /-- The state of the simulator is consistent. -/
  vis : VisCons cs.sim
  /-- The full view holds exactly the visible and the hidden pairs. -/
  allMem : ∀ e, e ∈ cs.all ↔ GEdge P iv cs c e
  /-- No answer has differed. -/
  noDiff : cs.diff = false

/-- **The invariant of the combined game.**

The facts of every run hold, and so do the others while no collision has happened. -/
def Inv (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) : Prop :=
  Struct P iv cs c ∧ (cs.bad = false → ¬ EC P iv cs.vis c → Cons P iv cs c)

end Edges

/-! ## Visible capacities -/

section Known

variable (iv : SpongeState Dg E C)

/-- The visible capacities: that of `iv`, and those of both ends of each recorded pair. -/
theorem mem_knownC {σ : SimState Dg E C} {k : C} :
    k ∈ knownC iv σ ↔ k = iv.2 ∨ ∃ e ∈ σ.edges, k = e.1.2 ∨ k = e.2.2 := by
  simp [knownC]

/-- The capacity of the initial state is visible. -/
theorem iv_mem_knownC (σ : SimState Dg E C) : iv.2 ∈ knownC iv σ :=
  (mem_knownC iv).mpr (Or.inl rfl)

/-- The capacity of a recorded query is visible. -/
theorem fst_mem_knownC {σ : SimState Dg E C} {e : SpongeState Dg E C × SpongeState Dg E C}
    (he : e ∈ σ.edges) : e.1.2 ∈ knownC iv σ :=
  (mem_knownC iv).mpr (Or.inr ⟨e, he, Or.inl rfl⟩)

/-- The capacity of a recorded answer is visible. -/
theorem snd_mem_knownC {σ : SimState Dg E C} {e : SpongeState Dg E C × SpongeState Dg E C}
    (he : e ∈ σ.edges) : e.2.2 ∈ knownC iv σ :=
  (mem_knownC iv).mpr (Or.inr ⟨e, he, Or.inr rfl⟩)

/-- Recording a pair adds the capacities of its two ends. -/
theorem mem_knownC_cons {σ : SimState Dg E C} {x y : SpongeState Dg E C}
    {VC : List (SpongeState Dg E C × List (Dg × E))} {k : C} :
    k ∈ knownC iv ⟨(x, y) :: σ.edges, VC⟩ ↔ k ∈ knownC iv σ ∨ k = x.2 ∨ k = y.2 := by
  simp only [mem_knownC, List.mem_cons]
  constructor
  · rintro (h | ⟨e, he | he, h⟩)
    · exact Or.inl (Or.inl h)
    · subst he; exact Or.inr h
    · exact Or.inl (Or.inr ⟨e, he, h⟩)
  · rintro ((h | ⟨e, he, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨e, Or.inr he, h⟩
    · exact Or.inr ⟨(x, y), Or.inl rfl, h⟩

/-- The capacity of a rooted state is visible. -/
theorem chain_cap_mem_knownC [XorOp Dg] [XorOp E] (P : Padding Msg (Dg × E))
    {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hS : Struct P iv cs c)
    {p : SpongeState Dg E C × List (Dg × E)} (hp : p ∈ cs.sim.chains) :
    p.1.2 ∈ knownC iv cs.sim := by
  by_cases h : p.2 = []
  · have := hS.chainVal p hp
    simp only [svC, h, ↓reduceIte, Option.some.injEq] at this
    rw [← this]
    exact iv_mem_knownC iv _
  · obtain ⟨q, -, B, -, he⟩ := hS.chainEdge p hp h
    exact snd_mem_knownC iv he

end Known

end EthLib.Cryptography.Sponge
