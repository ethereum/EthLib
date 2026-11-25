module

public import EthLib.Cryptography.Proofs.Sponge.Games

/-!
# Proofs: the outcomes that the steps of the combined game can reach

Each step runs in the random-oracle model of the hash and of the oracle on paths.

A step caches each value of a path that it asks, and the cache only grows.

The rest of the step is a function of these values and of the uniform draws.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} (P : Padding Msg (Dg × E))

/-- The cache of the random oracles of the intermediate games. -/
abbrev ACache (Msg Dg E C : Type) := (ASpec Msg Dg E C).QueryCache

/-- The cached value of a path, when the answers it reads are cached. -/
noncomputable def valC (c : ACache Msg Dg E C) (β : List (Dg × E)) : Option (SpongeState Dg E C) :=
  match P.unpad β with
  | some m => (c (.inl m)).bind fun d => (c (.inr β)).map fun t => ((d, t.1.2), t.2)
  | none => c (.inr β)

/-- The oracle points that the value of the path `β` reads. -/
def ValPt (β : List (Dg × E)) : (ASpec Msg Dg E C).Domain → Prop
  | .inl m => P.unpad β = some m
  | .inr γ => γ = β

/-- A cached value stays cached in a larger cache. -/
theorem valC_mono {c c' : ACache Msg Dg E C} (h : c ≤ c') {β : List (Dg × E)}
    {v : SpongeState Dg E C} (hv : valC P c β = some v) : valC P c' β = some v := by
  unfold valC at hv ⊢
  split at hv
  · obtain ⟨d, hd, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hv
    simp [h hd, h ht]
  · exact h hv

variable [DecidableEq Dg] [DecidableEq E] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]

/-- **The value step.** Asking the value of `β` caches it and keeps the cache elsewhere. -/
theorem val_support (β : List (Dg × E)) (c : ACache Msg Dg E C)
    {z : SpongeState Dg E C × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl (val P β)).run c)) :
    c ≤ z.2 ∧ valC P z.2 β = some z.1 ∧ ∀ t, ¬ ValPt (C := C) P β t → z.2 t = c t := by
  unfold val at hz
  split at hz
  · next m hm =>
    simp only [simulateQ_bind, StateT.run_bind, run_queryRight, simulateQ_pure, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨d, c₁⟩, h₁, ⟨t, c₂⟩, h₂, rfl⟩ := hz
    obtain ⟨hc₁, hd, hc₁'⟩ := randomOracle_run_support _ c h₁
    obtain ⟨hc₂, ht, hc₂'⟩ := randomOracle_run_support _ c₁ h₂
    refine ⟨le_trans hc₁ hc₂, ?_, fun t' ht' => ?_⟩
    · simp only [valC, hm]
      rw [hc₂' (.inl m) (by simp), hd, ht]
      rfl
    · simp only at ht' ⊢
      rw [hc₂' t' (by rintro rfl; exact ht' rfl), hc₁' t' (by rintro rfl; exact ht' hm)]
  · next hm =>
    rw [run_queryRight] at hz
    obtain ⟨hc, ht, hc'⟩ := randomOracle_run_support _ c hz
    refine ⟨hc, ?_, fun t' ht' => hc' t' (by rintro rfl; exact ht' rfl)⟩
    simp only [valC, hm]
    exact ht

/-- Asking a path whose value is cached returns that value and keeps the cache. -/
theorem val_run_of_valC (β : List (Dg × E)) (c : ACache Msg Dg E C) {v : SpongeState Dg E C}
    (hv : valC P c β = some v) :
    (simulateQ (ASpec Msg Dg E C).romImpl (val P β)).run c = pure (v, c) := by
  unfold valC at hv
  unfold val
  split at hv
  · next m hm =>
    obtain ⟨d, hd, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hv
    simp only [hm, simulateQ_bind, StateT.run_bind, run_queryRight,
      QueryImpl.withCaching_run_some _ hd, pure_bind, QueryImpl.withCaching_run_some _ ht,
      simulateQ_pure, StateT.run_pure]
  · next hm =>
    simp only [hm, run_queryRight, QueryImpl.withCaching_run_some _ hv]

/-- A uniform draw leaves the cache alone. -/
theorem drawSt_run (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl
      (drawSt (Msg := Msg) (Dg := Dg) (E := E) (C := C))).run c =
      (fun u => (u, c)) <$> ($ᵗ (SpongeState Dg E C)) :=
  simulateQ_romImpl_liftM_run _ _

variable [DecidableEq C] [XorOp Dg] [XorOp E]

/-- The walk of the full view, as a function of the path values `vf` and the uniform draws `us`. -/
def detWalk (used : List (Dg × E) → Bool) (vf : List (Dg × E) → SpongeState Dg E C) :
    List (Dg × E) → SpongeState Dg E C → PermCache (SpongeState Dg E C) → List (Dg × E) →
      List (SpongeState Dg E C) → SpongeState Dg E C × PermCache (SpongeState Dg E C)
  | _, s, A, [], _ => (s, A)
  | pre, s, A, B :: bs, us =>
    match A.lookup (absorb s B) with
    | some y => detWalk used vf (pre ++ [B]) y A bs us.tail
    | none =>
      let y := if used (pre ++ [B]) then us.headD s else vf (pre ++ [B])
      detWalk used vf (pre ++ [B]) y ((absorb s B, y) :: A) bs us.tail

/-- **The walk step.** The walk caches the values of its paths and keeps the cache elsewhere.

Its outcome is the walk over any function that agrees with the cached values. -/
theorem allWalk_support (used : List (Dg × E) → Bool) (pre : List (Dg × E))
    (s : SpongeState Dg E C) (A : PermCache (SpongeState Dg E C)) (bs : List (Dg × E))
    (c : ACache Msg Dg E C)
    {z : (SpongeState Dg E C × PermCache (SpongeState Dg E C)) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      (allWalk P used pre s A bs)).run c)) :
    c ≤ z.2 ∧ (∀ i < bs.length, valC P z.2 (pre ++ bs.take (i + 1)) ≠ none) ∧
      (∀ t, (∀ i < bs.length, ¬ ValPt (C := C) P (pre ++ bs.take (i + 1)) t) → z.2 t = c t) ∧
      ∃ us, ∀ vf : List (Dg × E) → SpongeState Dg E C,
        (∀ i < bs.length, valC P z.2 (pre ++ bs.take (i + 1)) =
          some (vf (pre ++ bs.take (i + 1)))) →
        z.1 = detWalk used vf pre s A bs us := by
  induction bs generalizing pre s A c with
  | nil =>
    simp only [allWalk, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, by simp, fun _ _ => rfl, [], fun _ _ => rfl⟩
  | cons B bs ih =>
    simp only [allWalk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨v, c₁⟩, h₁, w₂, h₂, hz⟩ := hz
    rw [drawSt_run] at h₂
    simp only [support_map, Set.mem_image] at h₂
    obtain ⟨u, -, rfl⟩ := h₂
    obtain ⟨hc₁, hv, hc₁'⟩ := val_support P _ c h₁
    dsimp only at hc₁ hv hc₁' hz
    -- The rest of the walk, from either next state, gives the claim for the whole list.
    have key : ∀ (y : SpongeState Dg E C) (A' : PermCache (SpongeState Dg E C)),
        z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
          (allWalk P used (pre ++ [B]) y A' bs)).run c₁) →
        c₁ ≤ z.2 ∧ c ≤ z.2 ∧
          (∀ i < (B :: bs).length, valC P z.2 (pre ++ (B :: bs).take (i + 1)) ≠ none) ∧
          (∀ t, (∀ i < (B :: bs).length,
            ¬ ValPt (C := C) P (pre ++ (B :: bs).take (i + 1)) t) → z.2 t = c t) ∧
          ∃ us', ∀ vf : List (Dg × E) → SpongeState Dg E C,
            (∀ i < (B :: bs).length, valC P z.2 (pre ++ (B :: bs).take (i + 1)) =
              some (vf (pre ++ (B :: bs).take (i + 1)))) →
            z.1 = detWalk used vf (pre ++ [B]) y A' bs us' := by
      intro y A' hz'
      obtain ⟨hc, hcached, hagree, us', hdet⟩ := ih (pre ++ [B]) y A' c₁ hz'
      refine ⟨hc, le_trans hc₁ hc, fun i hi => ?_, fun t ht => ?_, us', fun vf hvf => hdet vf ?_⟩
      · rcases i with _ | i
        · simp [valC_mono P hc hv]
        · have := hcached i (by simp at hi; omega)
          simpa [List.take_succ_cons] using this
      · rw [hagree t fun i hi => ?_, hc₁' t (by simpa using ht 0 (by simp))]
        simpa [List.take_succ_cons] using ht (i + 1) (by simp; omega)
      · intro i hi
        simpa [List.take_succ_cons] using hvf (i + 1) (by simp; omega)
    split at hz
    · next y hy =>
      obtain ⟨-, hc, hcached, hagree, us', hdet⟩ := key y A hz
      refine ⟨hc, hcached, hagree, u :: us', fun vf hvf => ?_⟩
      simp only [detWalk, hy, List.tail_cons]
      exact hdet vf hvf
    · next hy =>
      obtain ⟨hc₁z, hc, hcached, hagree, us', hdet⟩ := key _ _ hz
      refine ⟨hc, hcached, hagree, u :: us', fun vf hvf => ?_⟩
      have hvB : v = vf (pre ++ [B]) := by
        have h0 := hvf 0 (by simp)
        simp only [List.take_succ_cons, List.take_zero] at h0
        rw [valC_mono P hc₁z hv] at h0
        exact Option.some.inj h0
      simp only [detWalk, hy, List.tail_cons, List.headD_cons]
      rw [← hvB]
      exact hdet vf hvf

/-- **The forward step of the simulator over path values.**

Either `x` is recorded, or it is a new rooted state whose path value is asked.

Otherwise it is a new state that is not rooted, answered with `u`. -/
theorem visFwd_support (x u : SpongeState Dg E C) (σ : SimState Dg E C) (c : ACache Msg Dg E C)
    {z : (SpongeState Dg E C × SimState Dg E C × Option (List (Dg × E) × SpongeState Dg E C)) ×
      ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl (visFwd P x u σ)).run c)) :
    (∃ y, σ.edges.lookup x = some y ∧ z = ((y, σ, none), c)) ∨
    (∃ s β, σ.edges.lookup x = none ∧ chainOf σ.chains x = some (s, β) ∧
      (z.1.1, z.2) ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
        (val P (β ++ [blockTo s x]))).run c) ∧
      z.1 = (z.1.1, ⟨(x, z.1.1) :: σ.edges, (z.1.1, β ++ [blockTo s x]) :: σ.chains⟩,
        some (β ++ [blockTo s x], z.1.1))) ∨
    (σ.edges.lookup x = none ∧ chainOf σ.chains x = none ∧
      z = ((u, ⟨(x, u) :: σ.edges, σ.chains⟩, none), c)) := by
  unfold visFwd at hz
  split at hz
  · next y hy =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact Or.inl ⟨y, hy, hz⟩
  · next hy =>
    split at hz
    · next s β hch =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨v, c'⟩, hv, rfl⟩ := hz
      exact Or.inr (Or.inl ⟨s, β, hy, hch, hv, rfl⟩)
    · next hch =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      exact Or.inr (Or.inr ⟨hy, hch, hz⟩)

variable (iv : SpongeState Dg E C)

/-- The outcomes of the combined forward step. -/
theorem combFwd_support (x : SpongeState Dg E C) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    {z : ((SpongeState Dg E C × SpongeState Dg E C) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combFwd P iv x).run cs)).run c)) :
    ∃ u r, (r, z.2) ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      (visFwd P x u cs.sim)).run c) ∧ z.1 = fwdOut P iv cs x u r := by
  simp only [combFwd, StateT.run_mk, simulateQ_bind, StateT.run_bind, drawSt_run,
    simulateQ_pure, StateT.run_pure, bind_map_left, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, support_uniformSample, Set.mem_univ, true_and] at hz
  obtain ⟨u, ⟨r, c'⟩, hr, rfl⟩ := hz
  exact ⟨u, r, hr, rfl⟩

omit [XorOp Dg] [XorOp E] in
/-- The outcomes of the combined inverse step. -/
theorem combInv_support (y : SpongeState Dg E C) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    {z : ((SpongeState Dg E C × SpongeState Dg E C) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combInv iv y).run cs)).run c)) :
    ∃ u, z = (invOut iv cs y u, c) := by
  simp only [combInv, StateT.run_mk, simulateQ_bind, StateT.run_bind, drawSt_run,
    simulateQ_pure, StateT.run_pure, bind_map_left, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨u, -, rfl⟩ := hz
  exact ⟨u, rfl⟩

/-- The outcomes of the combined hash step. -/
theorem combHash_support (m : Msg) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C)
    {z : ((Dg × Dg) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combHash P iv m).run cs)).run c)) :
    ∃ w c₁ d, (w, c₁) ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      (allWalk P (usedPath P cs.sim.chains cs.hashed) [] iv cs.all (P.pad m))).run c) ∧
      (d, z.2) ∈ support (((ASpec Msg Dg E C).randomOracle (.inl m)).run c₁) ∧
      z.1 = hashOut cs m w d := by
  simp only [combHash, StateT.run_mk, simulateQ_bind, StateT.run_bind, run_queryRight,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨⟨w, c₁⟩, hw, ⟨d, c₂⟩, hd, rfl⟩ := hz
  exact ⟨w, c₁, d, hw, hd, rfl⟩

end EthLib.Cryptography.Sponge
