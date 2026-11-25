module

public import EthLib.Cryptography.Proofs.BadOnBudget
public import EthLib.Cryptography.Proofs.Sponge.Commute
public import EthLib.Cryptography.Proofs.Sponge.Ideal

/-!
# Proofs: a collision in the visible game is unlikely

A visible collision needs a new draw of the simulator to hit one of the visible capacities.

A hidden collision needs a value of a hidden path to hit a visible capacity or another hidden one.

The values of the hidden paths are drawn in the end phase, after the game.

Together they occur with chance at most `(N (2N + 1) + N (N + 1)) / |C|` for a game of cost `N`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge.Indiff

open OracleComp OracleSpec ENNReal LazyPermutation Indifferentiability

/-! ## Collisions among the answers of the oracle on paths -/

variable {Dg E C Msg : Type}

section Coll

variable [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] [Fintype C]
  (P : Padding Msg (Dg × E))

/-- A capacity collision among the answers of the oracle on paths at the paths of `H`.

An answer at a path of `H` has a capacity in `K`, or the capacity of an answer at another path. -/
def Coll (H : Finset (List (Dg × E))) (K : List C) (c : ACache Msg Dg E C) : Prop :=
  ∃ β ∈ H, ∃ t, c (.inr β) = some t ∧
    (t.2 ∈ K ∨ ∃ γ ∈ H, γ ≠ β ∧ ∃ t', c (.inr γ) = some t' ∧ t'.2 = t.2)

/-- The capacities of the cached answers of the oracle on paths at the paths of `H`. -/
noncomputable def collCaps (H : Finset (List (Dg × E))) (c : ACache Msg Dg E C) : List C :=
  H.toList.filterMap fun γ => (c (.inr γ)).map Prod.snd

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg] [SampleableType Dg] [SampleableType E]
  [SampleableType C] [Fintype C] in
/-- At most one cached capacity per path of `H`. -/
theorem length_collCaps_le (H : Finset (List (Dg × E))) (c : ACache Msg Dg E C) :
    (collCaps H c).length ≤ H.card := by
  unfold collCaps
  exact (List.length_filterMap_le _ _).trans (by simp)

omit [SampleableType Dg] [SampleableType E] [SampleableType C] [Fintype C] in
/-- A collision after a new answer is an old one, or a capacity of the answer already present. -/
theorem coll_cacheQuery {H : Finset (List (Dg × E))} {K : List C} {c : ACache Msg Dg E C}
    {β : List (Dg × E)} (hβ : c (.inr β) = none) (t : SpongeState Dg E C)
    (h : Coll H K (c.cacheQuery (.inr β) t)) :
    Coll H K c ∨ t.2 ∈ K ++ collCaps H c := by
  obtain ⟨γ, hγ, t₀, ht₀, hcol⟩ := h
  by_cases hγβ : γ = β
  · subst hγβ
    rw [QueryCache.cacheQuery_self] at ht₀
    obtain rfl := Option.some.inj ht₀
    right
    rcases hcol with h | ⟨δ, hδ, hne, t', ht', heq⟩
    · exact List.mem_append_left _ h
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne)] at ht'
      refine List.mem_append_right _ ?_
      rw [← heq]
      simp only [collCaps, List.mem_filterMap, Finset.mem_toList, Option.map_eq_some_iff]
      exact ⟨δ, hδ, t', ht', rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hγβ)] at ht₀
    rcases hcol with h | ⟨δ, hδ, hne, t', ht', heq⟩
    · exact Or.inl ⟨γ, hγ, t₀, ht₀, Or.inl h⟩
    · by_cases hδβ : δ = β
      · subst hδβ
        rw [QueryCache.cacheQuery_self] at ht'
        obtain rfl := Option.some.inj ht'
        right
        refine List.mem_append_right _ ?_
        rw [heq]
        simp only [collCaps, List.mem_filterMap, Finset.mem_toList, Option.map_eq_some_iff]
        exact ⟨γ, hγ, t₀, ht₀, rfl⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hδβ)] at ht'
        exact Or.inl ⟨γ, hγ, t₀, ht₀, Or.inr ⟨δ, hδ, hne, t', ht', heq⟩⟩

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg] [SampleableType Dg] [SampleableType E]
  [SampleableType C] [Fintype C] in
/-- A collision reads only the answers of the oracle on paths. -/
theorem coll_congr {H : Finset (List (Dg × E))} {K : List C} {c c' : ACache Msg Dg E C}
    (h : ∀ β, c' (.inr β) = c (.inr β)) : Coll H K c' ↔ Coll H K c := by
  simp only [Coll, h]

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg] in
/-- A uniform draw lands in a list with chance at most its length over the size of the set. -/
theorem prEvent_uniform_mem_le {S : Type} [Fintype S] [DecidableEq S] [SampleableType S]
    (l : List S) : Pr{let u ← $ᵗ S}[u ∈ l] ≤ l.length / (Fintype.card S : ℝ≥0∞) := by
  rw [SampleableType.prEvent_uniformSample]
  gcongr
  calc (Finset.univ.filter fun u : S => u ∈ l).card
      ≤ l.toFinset.card := Finset.card_le_card fun u hu => by simpa using hu
    _ ≤ l.length := List.toFinset_card_le l

omit [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg] in
/-- The capacity of a uniform state lands in a list with chance at most its length over `|C|`. -/
theorem prEvent_cap_mem_le [DecidableEq C] (L : List C) :
    Pr{let t ← $ᵗ (SpongeState Dg E C)}[t.2 ∈ L] ≤ L.length / (Fintype.card C : ℝ≥0∞) :=
  SampleableType.prEvent_uniformSample_prod_le_of_forall_fst (fun t : SpongeState Dg E C => t.2 ∈ L)
    fun _ => prEvent_uniform_mem_le L

/-- **A path value makes a collision with chance at most `(|K| + |H|) / |C|`.** -/
theorem prEvent_coll_pathValue [DecidableEq C] (H : Finset (List (Dg × E))) (K : List C)
    (β : List (Dg × E)) (c : ACache Msg Dg E C) (hc : ¬Coll H K c) :
    Pr{let z ← (simulateQ (ASpec Msg Dg E C).romImpl (pathValue P β)).run c}[Coll H K z.2] ≤
      (K.length + H.card) / (Fintype.card C : ℝ≥0∞) := by
  -- The hash part of the value leaves the answers of the oracle on paths alone.
  have hro : ∀ m, ∀ w ∈ support (((ASpec Msg Dg E C).randomOracle (.inl m)).run c),
      ¬Coll H K w.2 ∧ ∀ β, w.2 (.inr β) = c (.inr β) := by
    intro m w hw
    obtain ⟨-, -, hagree⟩ := randomOracle_run_support _ c hw
    have h : ∀ β, w.2 (.inr β) = c (.inr β) := fun β => hagree _ (by simp)
    exact ⟨(coll_congr h).not.mpr hc, h⟩
  -- The answer of the oracle on paths at `β`.
  have hT : ∀ c' : ACache Msg Dg E C, ¬Coll H K c' →
      Pr{let z ← ((ASpec Msg Dg E C).randomOracle (.inr β)).run c'}[Coll H K z.2] ≤
        (K.length + H.card) / (Fintype.card C : ℝ≥0∞) := by
    intro c' hc'
    rw [randomOracle.run_eq]
    rcases h : c' (.inr β) with _ | t
    · simp only [bind_pure_comp, prEvent_map]
      calc Pr{let t ← $ᵗ (SpongeState Dg E C)}[Coll H K (c'.cacheQuery (.inr β) t)]
          ≤ Pr{let t ← $ᵗ (SpongeState Dg E C)}[t.2 ∈ K ++ collCaps H c'] :=
            prEvent_mono _ _ _ fun t ht => (coll_cacheQuery h t ht).resolve_left hc'
        _ ≤ (K ++ collCaps H c').length / (Fintype.card C : ℝ≥0∞) := prEvent_cap_mem_le _
        _ ≤ (K.length + H.card) / (Fintype.card C : ℝ≥0∞) := by
            gcongr
            rw [List.length_append]
            exact_mod_cast Nat.add_le_add_left (length_collCaps_le H c') _
    · simp [hc']
  unfold pathValue
  split
  · next m hm =>
    simp only [simulateQ_bind, StateT.run_bind, run_queryRight, simulateQ_pure, StateT.run_pure]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun w hw => ?_
    simp only [bind_pure_comp, prEvent_map]
    exact hT w.2 (hro m w hw).1
  · rw [run_queryRight]
    exact hT c hc

/-- The queries of path values make a collision with chance at most `(|K| + |H|) / |C|` a block. -/
theorem prEvent_coll_skel [DecidableEq C] (H : Finset (List (Dg × E))) (K : List C)
    (pre bs : List (Dg × E)) (c : ACache Msg Dg E C) (hc : ¬Coll H K c) :
    Pr{let z ← (simulateQ (ASpec Msg Dg E C).romImpl (skel (C := C) P pre bs)).run c}[
      Coll H K z.2] ≤ bs.length * ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)) := by
  induction bs generalizing pre c with
  | nil => simp [skel, hc]
  | cons B bs ih =>
    simp only [skel, simulateQ_bind, StateT.run_bind]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun w => Coll H K w.2) _
      (ε := bs.length * ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)))
      fun w _ hw => ?_).trans ?_
    · rw [drawSt_run, bind_map_left]
      exact prEvent_bind_le_of_forall_le _ _ _ fun u => ih _ w.2 hw
    · rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_one_mul, add_comm]
      gcongr
      exact prEvent_coll_pathValue P H K _ c hc

/-- The end phase makes a collision with chance at most `(|K| + |H|) / |C|` a hashed block. -/
theorem prEvent_coll_endPhase [DecidableEq C] (H : Finset (List (Dg × E))) (K : List C)
    (ms : List Msg) (c : ACache Msg Dg E C) (hc : ¬Coll H K c) :
    Pr{let z ← (simulateQ (ASpec Msg Dg E C).romImpl (endPhase (C := C) P ms)).run c}[
      Coll H K z.2] ≤
      (ms.map fun m => (P.pad m).length).sum *
        ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)) := by
  induction ms generalizing c with
  | nil => simp [endPhase, hc]
  | cons m ms ih =>
    simp only [endPhase, simulateQ_bind, StateT.run_bind]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun w => Coll H K w.2) _
      (ε := (ms.map fun m => (P.pad m).length).sum *
        ((K.length + H.card) / (Fintype.card C : ℝ≥0∞)))
      fun w _ hw => ih w.2 hw).trans ?_
    rw [List.map_cons, List.sum_cons, Nat.cast_add, add_mul]
    gcongr
    simpa using prEvent_coll_skel P H K [] (P.pad m) c hc

end Coll

/-! ## The visible game without the queries of path values -/

section Visible

variable [XorOp Dg] [XorOp E] [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] [Fintype C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-- The visible game without the queries of path values, with the cache in its state. -/
noncomputable abbrev visF : QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
    (StateT (VState Dg E C Msg × ACache Msg Dg E C) ProbComp) :=
  ((ASpec Msg Dg E C).romImpl.mapStateTBase (visImpl P iv false)).flattenStateT

omit [DecidableEq Msg] [Fintype C] in
/-- The hashed messages, the number of pairs and the flag after a visible step. -/
theorem visImpl_false_support (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (vs : VState Dg E C Msg) {z} (hz : z ∈ support ((visImpl P iv false t).run vs)) :
    z.2.2.1 = (match t with | .inr m => m :: vs.2.1 | _ => vs.2.1) ∧
    z.2.1.edges.length ≤ vs.1.edges.length + (match t with | .inl (.inr _) => 1 | _ => 0) ∧
    (z.2.2.2 = true → vs.2.2 = false → ∃ q, t = .inl (.inr q)) := by
  rcases t with (n | x | y) | m
  · simp [visImpl] at hz
    obtain ⟨u, rfl⟩ := hz
    exact ⟨rfl, by simp, fun h h' => by simp_all⟩
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, r, hr, rfl⟩ := hz
    refine ⟨rfl, ?_, fun _ _ => ⟨_, rfl⟩⟩
    unfold visFwd at hr
    split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
    · split at hr
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
        obtain ⟨v, -, rfl⟩ := hr
        simp
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        simp
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    refine ⟨rfl, ?_, fun _ _ => ⟨_, rfl⟩⟩
    simp only [visInv]
    split <;> simp
  · simp only [visImpl, StateT.run_mk, Bool.false_eq_true, ↓reduceIte,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨d, -, rfl⟩ := hz
    exact ⟨rfl, by simp, fun h h' => by simp_all⟩

omit [Fintype C] in
/-- The outcomes of a folded visible step come from the unfolded step. -/
theorem visF_support (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) {z} (hz : z ∈ support ((visF P iv t).run s)) :
    ∃ w ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((visImpl P iv false t).run s.1)).run s.2), z = (w.1.1, (w.1.2, w.2)) := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- The size of a visible state: its pairs and the blocks of its hashed messages. -/
def vsize (vs : VState Dg E C Msg) : ℕ :=
  vs.1.edges.length + (vs.2.1.map fun m => (P.pad m).length).sum

omit [Fintype C] in
/-- A visible step raises the size by at most its cost. -/
theorem vsize_visF (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) {z} (hz : z ∈ support ((visF P iv t).run s)) :
    vsize P z.2.1 ≤ vsize P s.1 + queryCost (fun m => (P.pad m).length) t := by
  obtain ⟨w, hw, rfl⟩ := visF_support P iv t s hz
  obtain ⟨h1, h2, -⟩ := visImpl_false_support P iv t s.1 (fst_mem_support_of_mem_support_run hw)
  rcases t with (n | q) | m
  · simp only [vsize, queryCost] at h1 h2 ⊢
    rw [h1]
    omega
  · simp only [vsize, queryCost] at h1 h2 ⊢
    rw [h1]
    omega
  · simp only [vsize, queryCost] at h1 h2 ⊢
    rw [h1, List.map_cons, List.sum_cons]
    omega

omit [XorOp Dg] [XorOp E] in
/-- The capacity of a new path value lands in a list with chance at most its length over `|C|`. -/
theorem prEvent_pathValue_cap_le (β : List (Dg × E)) (c : ACache Msg Dg E C) (h : c (.inr β) = none)
    (L : List C) :
    Pr{let w ← (simulateQ (ASpec Msg Dg E C).romImpl (pathValue P β)).run c}[w.1.2 ∈ L] ≤
      L.length / (Fintype.card C : ℝ≥0∞) := by
  rcases hm : P.unpad β with _ | m
  · rw [pathValue_run_fresh_none P hm c h, bind_pure_comp, prEvent_map]
    exact prEvent_cap_mem_le L
  · rw [pathValue_run_fresh_some P hm c h]
    refine prEvent_bind_le_of_forall_le _ _ _ fun w => ?_
    rw [bind_pure_comp, prEvent_map]
    exact prEvent_cap_mem_le L

omit [Fintype C] in
/-- The step of the simulator at a new rooted state asks the value of its path. -/
theorem visFwd_run_rooted {σ : SimState Dg E C} {x s : SpongeState Dg E C} {β : List (Dg × E)}
    (hy : σ.edges.lookup x = none) (hch : chainOf σ.chains x = some (s, β))
    (u : SpongeState Dg E C) (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl (visFwd P x u σ)).run c =
      (fun w => ((w.1, (⟨(x, w.1) :: σ.edges, (w.1, β ++ [blockTo s x]) :: σ.chains⟩ :
        SimState Dg E C), some (β ++ [blockTo s x], w.1)), w.2)) <$>
        (simulateQ (ASpec Msg Dg E C).romImpl (pathValue P (β ++ [blockTo s x]))).run c := by
  simp only [visFwd, hy, hch]
  rw [simulateQ_bind, StateT.run_bind]
  simp [map_eq_bind_pure_comp]

omit [Fintype C] in
/-- The run of a visible forward step without the queries of path values. -/
theorem visImpl_false_fwd_run (x : SpongeState Dg E C) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl
      ((visImpl P iv false (.inl (.inr (.inl x)))).run vs)).run c =
      ($ᵗ (SpongeState Dg E C)) >>= fun u => (fun w => ((w.1.1, (w.1.2.1, vs.2.1, vs.2.2 ||
        ((vs.1.edges.lookup x).isNone && decide (w.1.1.2 ∈ knownC iv vs.1)))), w.2)) <$>
        (simulateQ (ASpec Msg Dg E C).romImpl (visFwd P x u vs.1)).run c := by
  simp only [visImpl, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

omit [Fintype C] in
/-- The run of a visible inverse step. -/
theorem visImpl_false_inv_run (y : SpongeState Dg E C) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl
      ((visImpl P iv false (.inl (.inr (.inr y)))).run vs)).run c =
      (fun u => (((visInv y u vs.1).1, ((visInv y u vs.1).2, vs.2.1, vs.2.2 ||
        (((vs.1.edges.map Prod.swap).lookup y).isNone && decide (u.2 ∈ knownC iv vs.1)))), c)) <$>
        ($ᵗ (SpongeState Dg E C)) := by
  simp only [visImpl, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

end Visible

/-- The visible capacities: two per pair and that of the initial state. -/
theorem length_knownC (iv : SpongeState Dg E C) (σ : SimState Dg E C) :
    (knownC iv σ).length = 2 * σ.edges.length + 1 := by
  simp only [knownC, List.length_cons, List.length_flatMap, List.length_nil]
  induction σ.edges with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-! ## The hidden paths -/

section Hidden

variable [DecidableEq Dg] [DecidableEq E] (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-- The nonempty prefixes of a list of blocks. -/
def prefixesOf (bs : List (Dg × E)) : List (List (Dg × E)) :=
  (List.range bs.length).map fun i => bs.take (i + 1)

omit [DecidableEq Dg] [DecidableEq E] in
/-- The nonempty prefixes of a list are its prefixes that are not empty. -/
theorem mem_prefixesOf {bs β : List (Dg × E)} : β ∈ prefixesOf bs ↔ β ≠ [] ∧ β <+: bs := by
  simp only [prefixesOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, List.take_prefix _ _⟩
    simp only [ne_eq, List.take_eq_nil_iff, Nat.add_one_ne_zero, false_or]
    rintro rfl
    simp at hi
  · rintro ⟨hne, hp⟩
    have hl := hp.length_le
    have h0 : β.length ≠ 0 := by simpa using hne
    refine ⟨β.length - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega)]
    exact (List.prefix_iff_eq_take.mp hp).symm

/-- The hidden paths of a visible state. -/
def hiddenSet (vs : VState Dg E C Msg) : Finset (List (Dg × E)) :=
  ((vs.2.1.flatMap fun m => prefixesOf (P.pad m)).filter fun β => β ∉ vPaths vs.1).toFinset

/-- The hidden paths of a visible state are the paths that are hidden. -/
theorem mem_hiddenSet {vs : VState Dg E C Msg} {β : List (Dg × E)} :
    β ∈ hiddenSet P vs ↔ Hidden P vs β := by
  simp [hiddenSet, Hidden, HPath, mem_prefixesOf]

/-- There are at most as many hidden paths as hashed blocks. -/
theorem card_hiddenSet_le (vs : VState Dg E C Msg) :
    (hiddenSet P vs).card ≤ (vs.2.1.map fun m => (P.pad m).length).sum := by
  unfold hiddenSet
  refine (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans (le_of_eq ?_))
  simp only [List.length_flatMap, prefixesOf, List.length_map, List.length_range]

omit [DecidableEq Dg] [DecidableEq E] in
/-- The capacity of a cached path value is that of the answer of the oracle on paths. -/
theorem cachedPathValue_cap {c : ACache Msg Dg E C} {β : List (Dg × E)} {v : SpongeState Dg E C}
    (h : cachedPathValue P c β = some v) : ∃ t, c (.inr β) = some t ∧ t.2 = v.2 := by
  unfold cachedPathValue at h
  split at h
  · obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨t, ht, rfl⟩
  · exact ⟨v, h, rfl⟩

/-- A hidden collision is a collision among the answers at hidden paths. -/
theorem coll_of_hiddenCollision {vs : VState Dg E C Msg} {c : ACache Msg Dg E C}
    (h : HiddenCollision P iv vs c) :
    Coll (hiddenSet P vs) (knownC iv vs.1) c := by
  obtain ⟨β, v, hβ, hv, h⟩ := h
  obtain ⟨t, ht, htv⟩ := cachedPathValue_cap P hv
  refine ⟨β, (mem_hiddenSet P).mpr hβ, t, ht, ?_⟩
  rcases h with h | ⟨γ, w, hγ, hne, hw, hwv⟩
  · exact Or.inl (htv ▸ h)
  · obtain ⟨t', ht', htw⟩ := cachedPathValue_cap P hw
    exact Or.inr ⟨γ, (mem_hiddenSet P).mpr hγ, hne, t', ht', by rw [htw, hwv, htv]⟩

/-- No hidden path has an answer of the oracle on paths before the end phase. -/
theorem not_coll_of_vStruct [XorOp Dg] [XorOp E] {vs : VState Dg E C Msg}
    {c : ACache Msg Dg E C}
    (hV : VStruct P iv vs.1 c) (K : List C) : ¬Coll (hiddenSet P vs) K c := by
  rintro ⟨β, hβ, t, ht, -⟩
  exact ((mem_hiddenSet P).mp hβ).2 (hV.tFresh β (by rw [ht]; simp))

end Hidden

/-! ## The collision bound -/

section Bound

variable [XorOp Dg] [XorOp E] [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C] [Fintype C]
  [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

omit [Fintype C] in
/-- The bookkeeping of the simulator holds along the visible game. -/
theorem vStruct_visF (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) (hs : VStruct P iv s.1.1 s.2) {z}
    (hz : z ∈ support ((visF P iv t).run s)) : VStruct P iv z.2.1.1 z.2.2 := by
  obtain ⟨w, hw, rfl⟩ := visF_support P iv t s hz
  have h := visImpl_false_proj P iv t s.1
  have hw' : ((w.1.1, w.1.2.1), w.2) ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((idealTImpl P t).run s.1.1)).run s.2) := by
    rw [← h, simulateQ_map, StateT.run_map, support_map]
    exact ⟨w, hw, rfl⟩
  exact vStruct_idealT t hs hw'

/-- **A visible collision, one step at a time.**

A visible step raises the flag with chance at most its cost times the visible capacities over `|C|`.
-/
theorem prEvent_visF_bad_le (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (s : VState Dg E C Msg × ACache Msg Dg E C) (hV : VStruct P iv s.1.1 s.2)
    (hb : ¬s.1.2.2 = true) :
    Pr{let z ← (visF P iv t).run s}[z.2.1.2.2 = true] ≤
      queryCost (fun m => (P.pad m).length) t *
        ((knownC iv s.1.1).length / (Fintype.card C : ℝ≥0∞)) := by
  rcases t with (n | q) | m
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_]
    · exact zero_le
    · obtain ⟨w, hw, rfl⟩ := visF_support P iv _ s hz
      obtain ⟨-, -, h3⟩ := visImpl_false_support P iv _ s.1
        (fst_mem_support_of_mem_support_run hw)
      obtain ⟨q, hq⟩ := h3 h (by simpa using hb)
      simp at hq
  · simp only [queryCost, Nat.cast_one, one_mul]
    simp only [Bool.not_eq_true] at hb
    rw [QueryImpl.flattenStateT_mapStateTBase_apply_run, prEvent_map]
    rcases q with x | y
    · rw [visImpl_false_fwd_run]
      rcases hy : s.1.1.edges.lookup x with _ | y
      · rcases hch : chainOf s.1.1.chains x with _ | ⟨σ₀, β⟩
        · simp only [visFwd, hy, hch, simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp,
            prEvent_map]
          refine (prEvent_mono _ _ _ fun u hu => ?_).trans (prEvent_cap_mem_le (knownC iv s.1.1))
          simpa [hb] using hu
        · simp only [visFwd_run_rooted P hy hch, Functor.map_map]
          refine prEvent_bind_le_of_forall_le _ _ _ fun u => ?_
          rw [prEvent_map]
          refine (prEvent_mono _ _ _ fun w hw => ?_).trans (prEvent_pathValue_cap_le P _ s.2
            (by by_contra h'; exact rootedPath_notMem hV hy hch (hV.tFresh _ h')) _)
          simpa [hb] using hw
      · simp only [visFwd, hy, simulateQ_pure, StateT.run_pure, map_pure]
        rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_]
        · exact zero_le
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨u, -, rfl⟩ := hz
          simp [hb] at h
    · rw [visImpl_false_inv_run, prEvent_map]
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans (prEvent_cap_mem_le (knownC iv s.1.1))
      simp only [hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hu
      exact hu.2
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_]
    · exact zero_le
    · obtain ⟨w, hw, rfl⟩ := visF_support P iv _ s hz
      obtain ⟨-, -, h3⟩ := visImpl_false_support P iv _ s.1
        (fst_mem_support_of_mem_support_run hw)
      obtain ⟨q, hq⟩ := h3 h (by simpa using hb)
      simp at hq

/-- The arithmetic of the bound on hidden collisions. -/
theorem hidden_arith {v h q : ℕ} (hq : v + h ≤ q) : h * (2 * v + 1 + h) ≤ q * (q + 1) := by
  nlinarith

/-- **The collision bound.**

Run the visible game without the queries of path values, then the end phase.

A game of cost `N` makes a visible or a hidden collision there.

It does so with chance at most `(N (2N + 1) + N (N + 1)) / |C|`. -/
theorem prEvent_visRun_le {α : Type} (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α)
    {N : ℕ} (hN : WithinCost (fun m => (P.pad m).length) oa N) :
    Pr{let z ← (simulateQ (ASpec Msg Dg E C).romImpl
        (visRun P iv false oa (SimState.init iv, [], false))).run ∅}[
      z.1.2.2.2 = true ∨ HiddenCollision P iv z.1.2 z.2] ≤
      ((N * (2 * N + 1) + N * (N + 1) : ℕ) : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
  set vs₀ : VState Dg E C Msg := (SimState.init iv, [], false)
  have hfold := simulateQ_mapStateTBase_run_eq_map_flattenStateT (ASpec Msg Dg E C).romImpl
    (visImpl P iv false) oa vs₀ (∅ : ACache Msg Dg E C)
  simp only [visRun, simulateQ_bind, StateT.run_bind]
  rw [hfold, bind_map_left]
  have hinit : VStruct P iv vs₀.1 (∅ : ACache Msg Dg E C) := vStruct_init
  -- The visible collisions along the run.
  have hbad : Pr{let z ← (simulateQ (visF P iv) oa).run (vs₀, ∅)}[z.2.1.2.2 = true] ≤
      N * ((2 * N + 1 : ℕ) / (Fintype.card C : ℝ≥0∞)) :=
    prEvent_run_bad_le (visF P iv) (fun s => s.1.2.2 = true)
      (fun s => VStruct P iv s.1.1 s.2) (queryCost (fun m => (P.pad m).length))
      (fun s => vsize P s.1) N ((2 * N + 1 : ℕ) / (Fintype.card C : ℝ≥0∞))
      (fun t s hs z hz => vStruct_visF P iv t s hs hz)
      (fun t s _ z hz => vsize_visF P iv t s hz)
      (fun t s hs hb hle => (prEvent_visF_bad_le P iv t s hs hb).trans (by
        gcongr
        rw [length_knownC]
        have : s.1.1.edges.length ≤ vsize P s.1 := Nat.le_add_right _ _
        omega)) hN hinit (by simp [vs₀]) (by simp [vsize, vs₀, SimState.init])
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z => z.2.1.2.2 = true) _
    (ε := ((N * (N + 1) : ℕ) : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞)) fun z hz hzb => ?_).trans ?_
  · -- The hidden collisions of the end phase.
    have hV := simulateQ_run_preserves_inv_of_query (visF P iv)
      (fun s => VStruct P iv s.1.1 s.2) (fun t s hs z hz => vStruct_visF P iv t s hs hz) oa _
      hinit z hz
    have hsize := size_le_of_mem_support_run (visF P iv)
      (fun s => VStruct P iv s.1.1 s.2) (queryCost (fun m => (P.pad m).length))
      (fun s => vsize P s.1) (fun t s hs z hz => vStruct_visF P iv t s hs hz)
      (fun t s _ z hz => vsize_visF P iv t s hz) hN hinit z hz
    simp only [vsize, vs₀, SimState.init, List.length_nil, List.map_nil, List.sum_nil,
      add_zero, zero_add] at hsize
    simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, prEvent_map]
    refine (prEvent_mono _ _ _ fun w hw => ?_).trans
      ((prEvent_coll_endPhase P (hiddenSet P z.2.1) (knownC iv z.2.1.1) z.2.1.2.1 z.2.2
        (not_coll_of_vStruct P iv hV _)).trans ?_)
    · rcases hw with hw | hw
      · exact absurd hw hzb
      · exact coll_of_hiddenCollision P iv hw
    · rw [mul_div_assoc']
      gcongr
      have h1 := card_hiddenSet_le P z.2.1
      rw [length_knownC]
      set h := (z.2.1.2.1.map fun m => (P.pad m).length).sum
      calc (h : ℝ≥0∞) * ((2 * z.2.1.1.edges.length + 1 : ℕ) + (hiddenSet P z.2.1).card)
          ≤ (h : ℝ≥0∞) * ((2 * z.2.1.1.edges.length + 1 : ℕ) + h) := by gcongr
        _ = ((h * (2 * z.2.1.1.edges.length + 1 + h) : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ ≤ _ := by exact_mod_cast hidden_arith hsize
  · rw [Nat.cast_add, ENNReal.add_div]
    gcongr
    refine hbad.trans (le_of_eq ?_)
    rw [mul_div_assoc', Nat.cast_mul]

end Bound
