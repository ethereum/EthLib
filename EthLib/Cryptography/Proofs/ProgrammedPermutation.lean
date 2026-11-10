module

public import EthLib.Cryptography.Proofs.IndependentAnswers
public import EthLib.Cryptography.Proofs.TaggedLazyPermutation

/-!
# Proofs: a permutation programmed beside a lazy permutation

Two callers share one random permutation `Π`.

One of them programs `Π`: it draws each answer itself.

The other asks `Π` through an overlay.

Both write one cache of pairs, and each pair carries a flag.

The programming oracle answers each query with a uniform value of `A`.

It records the pair with the flag set, also when the query or the answer is cached.

The overlay answers a cached query from the cache, in either direction.

It relays a new query to the lazy permutation, and records the pair with the flag clear.

So the lazy permutation sees only the relayed pairs.

A conflict is two pairs of the cache that share a query or an answer.

Once there, a conflict stays.

Read the state of both oracles as the cache with its flags erased.

Until a conflict, the lazy permutation puts at least as much mass on each outcome.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

Their Game G2 of Figure 5 keeps the programmed pairs in `Π_S`, and the relayed pairs in `Π_O`.

Their aborts in lines 05, 11, 13 and 25 are conflicts here.

They stop the game, where here the oracles go on and an event excludes the conflict.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal
open scoped List

variable {A : Type}

/-! ## The shared cache -/

/-- The pairs of `Π` known to the overlay, the most recent first.

The flag is `true` when the pair was programmed, and `false` when it was relayed. -/
abbrev ProgrammedCache (A : Type) := TaggedCache A Bool

/-- The relayed pairs of the cache, the most recent first. -/
def ProgrammedCache.relayed (c : ProgrammedCache A) : PermCache A :=
  TaggedCache.untag (c.filter fun e => !e.2)

/-- Two pairs of the cache share a query or an answer. -/
def ProgrammedCache.Conflict (c : ProgrammedCache A) : Prop :=
  ¬(TaggedCache.untag c).IsPartialBijection

/-- A relayed pair joins the relayed pairs. -/
@[simp] theorem ProgrammedCache.relayed_cons_false (c : ProgrammedCache A) (p : A × A) :
    ProgrammedCache.relayed ((p, false) :: c) = p :: c.relayed := by
  simp [ProgrammedCache.relayed]

/-- A programmed pair leaves the relayed pairs unchanged. -/
@[simp] theorem ProgrammedCache.relayed_cons_true (c : ProgrammedCache A) (p : A × A) :
    ProgrammedCache.relayed ((p, true) :: c) = c.relayed := by
  simp [ProgrammedCache.relayed]

/-- The relayed pairs are a sublist of the cache. -/
theorem ProgrammedCache.relayed_sublist (c : ProgrammedCache A) :
    c.relayed <+ TaggedCache.untag c :=
  List.filter_sublist.map Prod.fst

/-- A conflict stays when a pair joins the cache. -/
theorem ProgrammedCache.conflict_cons {c : ProgrammedCache A} (e : (A × A) × Bool)
    (h : c.Conflict) : ProgrammedCache.Conflict (e :: c) := fun h' =>
  h ((PermCache.isPartialBijection_cons_iff _ _).1 h').2.2

/-- A new pair that makes no conflict has its query outside the queries of the cache. -/
theorem ProgrammedCache.notMem_map_fst_of_not_conflict_cons {c : ProgrammedCache A} {a b : A}
    {t : Bool} (h : ¬ProgrammedCache.Conflict (((a, b), t) :: c)) :
    a ∉ (TaggedCache.untag c).map Prod.fst :=
  ((PermCache.isPartialBijection_cons_iff _ _).1 (not_not.1 h)).1

/-- A new pair that makes no conflict has its answer outside the answers of the cache. -/
theorem ProgrammedCache.notMem_map_snd_of_not_conflict_cons {c : ProgrammedCache A} {a b : A}
    {t : Bool} (h : ¬ProgrammedCache.Conflict (((a, b), t) :: c)) :
    b ∉ (TaggedCache.untag c).map Prod.snd :=
  ((PermCache.isPartialBijection_cons_iff _ _).1 (not_not.1 h)).2.1

variable [FinEnum A]

/-- A query missing from the cache is missing from the relayed pairs. -/
theorem ProgrammedCache.relayed_lookup_eq_none {c : ProgrammedCache A} {a : A}
    (h : (TaggedCache.untag c).lookup a = none) : c.relayed.lookup a = none :=
  c.relayed_sublist.lookup_eq_none h

/-- An answer missing from the cache is missing from the relayed pairs. -/
theorem ProgrammedCache.relayed_swap_lookup_eq_none {c : ProgrammedCache A} {b : A}
    (h : ((TaggedCache.untag c).map Prod.swap).lookup b = none) :
    (c.relayed.map Prod.swap).lookup b = none :=
  (c.relayed_sublist.map Prod.swap).lookup_eq_none h

/-- A pair whose query is cached already makes a conflict. -/
theorem ProgrammedCache.conflict_cons_of_lookup {c : ProgrammedCache A} {a b b' : A} {t : Bool}
    (h : (TaggedCache.untag c).lookup a = some b) :
    ProgrammedCache.Conflict (((a, b'), t) :: c) := fun h' =>
  ((PermCache.isPartialBijection_cons_iff _ _).1 h').1
    (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup_eq_some h) :)

/-- A pair whose answer is cached already makes a conflict. -/
theorem ProgrammedCache.conflict_cons_of_swap_lookup {c : ProgrammedCache A} {a a' b : A}
    {t : Bool} (h : ((TaggedCache.untag c).map Prod.swap).lookup b = some a') :
    ProgrammedCache.Conflict (((a, b), t) :: c) := fun h' => by
  obtain ⟨q, hq, hqe⟩ := List.mem_map.1 (mem_of_lookup_eq_some h)
  exact ((PermCache.isPartialBijection_cons_iff _ _).1 h').2.1
    (List.mem_map.2 ⟨q, hq, congrArg Prod.fst hqe⟩)

/-! ## The oracles of `Π` -/

/-- The overlay of `Π`, as a program of the oracle of `Π`.

A query in its cache gets the cached answer, in either direction.

A new query goes to the oracle of `Π`, and the overlay records the relayed pair. -/
def overlayPermOracle : QueryImpl (PermSpec A) (StateT (ProgrammedCache A) (PermComp A))
  | .inl a => fun c =>
    match (TaggedCache.untag c).lookup a with
    | some b => pure (b, c)
    | none => (fun b => (b, ((a, b), false) :: c)) <$>
      query (spec := unifSpec + PermSpec A) (.inr (.inl a))
  | .inr b => fun c =>
    match ((TaggedCache.untag c).map Prod.swap).lookup b with
    | some a => pure (a, c)
    | none => (fun a => (a, ((a, b), false) :: c)) <$>
      query (spec := unifSpec + PermSpec A) (.inr (.inr b))

/-- The overlay of `Π` run against the lazy permutation.

The state is the overlay's cache and the cache of the lazy permutation. -/
def overlayLazyOracle :
    QueryImpl (PermSpec A) (StateT (ProgrammedCache A × PermCache A) ProbComp) :=
  fun q s => (fun z => (z.1.1, (z.1.2, z.2))) <$>
    (simulateQ lazyPermImpl ((overlayPermOracle q).run s.1)).run s.2

/-- The oracle of `Π` that programs each query with a uniform answer.

A forward query gets a uniform value of `A`.

It records the pair as programmed, even when the query or the answer is cached.

It leaves the cache of the lazy permutation unchanged.

An inverse query is programmed the same way, so that the oracle is total.

The signing program never asks one, so a bound on conflicts need not count it. -/
def programPermOracle :
    QueryImpl (PermSpec A) (StateT (ProgrammedCache A × PermCache A) ProbComp)
  | .inl a => fun s => (fun b => (b, (((a, b), true) :: s.1, s.2))) <$>
    (uniformOutside [] a : ProbComp A)
  | .inr b => fun s => (fun a => (a, (((a, b), true) :: s.1, s.2))) <$>
    (uniformOutside [] b : ProbComp A)

/-- The oracles of the caller that programs `Π`: coins, passed through, then the oracle above. -/
abbrev programPermImpl :
    QueryImpl (unifSpec + PermSpec A) (StateT (ProgrammedCache A × PermCache A) ProbComp) :=
  unifSpec.passthrough + programPermOracle

/-! ## Steps of the oracles of `Π` -/

/-- A forward query to the overlay reads its cache, or relays the query to the lazy permutation. -/
theorem overlayLazyOracle_inl_run (a : A) (c : ProgrammedCache A) (l : PermCache A) :
    (overlayLazyOracle (.inl a)).run (c, l) =
      match (TaggedCache.untag c).lookup a with
      | some b => pure (b, (c, l))
      | none => (fun z => (z.1, (((a, z.1), false) :: c, z.2))) <$>
        (lazyPermOracle (.inl a)).run l := by
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ lazyPermImpl
      (match (TaggedCache.untag c).lookup a with
        | some b => pure (b, c)
        | none => (fun b => (b, ((a, b), false) :: c)) <$>
          query (spec := unifSpec + PermSpec A) (.inr (.inl a)))).run l = _
  cases (TaggedCache.untag c).lookup a with
  | some b => simp
  | none => simp [Functor.map_map]

/-- An inverse query to the overlay reads its cache, or relays the query to the lazy permutation. -/
theorem overlayLazyOracle_inr_run (b : A) (c : ProgrammedCache A) (l : PermCache A) :
    (overlayLazyOracle (.inr b)).run (c, l) =
      match ((TaggedCache.untag c).map Prod.swap).lookup b with
      | some a => pure (a, (c, l))
      | none => (fun z => (z.1, (((z.1, b), false) :: c, z.2))) <$>
        (lazyPermOracle (.inr b)).run l := by
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ lazyPermImpl
      (match ((TaggedCache.untag c).map Prod.swap).lookup b with
        | some a => pure (a, c)
        | none => (fun a => (a, ((a, b), false) :: c)) <$>
          query (spec := unifSpec + PermSpec A) (.inr (.inr b)))).run l = _
  cases ((TaggedCache.untag c).map Prod.swap).lookup b with
  | some a => simp
  | none => simp [Functor.map_map]

/-- A query to the overlay keeps both caches, or adds one relayed pair to the overlay's cache.

When the relayed pairs are the cache of the lazy permutation, that pair joins it too. -/
theorem overlayLazyOracle_step (q : (PermSpec A).Domain) (s : ProgrammedCache A × PermCache A)
    (z) (hz : z ∈ support ((overlayLazyOracle q).run s)) :
    z.2 = s ∨ ∃ p, z.2.1 = (p, false) :: s.1 ∧ (s.2 = s.1.relayed → z.2.2 = p :: s.2) := by
  obtain ⟨c, l⟩ := s
  rcases q with a | b
  · rw [overlayLazyOracle_inl_run] at hz
    rcases h : (TaggedCache.untag c).lookup a with _ | b <;> simp only [h] at hz
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      refine Or.inr ⟨(a, w.1), rfl, fun hl => ?_⟩
      simp only at hl
      subst hl
      rw [lazyPermOracle_inl_run, ProgrammedCache.relayed_lookup_eq_none h] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨b, -, rfl⟩ := hw
      rfl
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
  · rw [overlayLazyOracle_inr_run] at hz
    rcases h : ((TaggedCache.untag c).map Prod.swap).lookup b with _ | a <;> simp only [h] at hz
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      refine Or.inr ⟨(w.1, b), rfl, fun hl => ?_⟩
      simp only at hl
      subst hl
      rw [lazyPermOracle_inr_run, ProgrammedCache.relayed_swap_lookup_eq_none h] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨a, -, rfl⟩ := hw
      rfl
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])

/-- The overlay keeps its relayed pairs equal to the cache of the lazy permutation. -/
theorem preservesInv_overlayLazyOracle_relayed :
    QueryImpl.PreservesInv (overlayLazyOracle (A := A)) fun s => s.2 = s.1.relayed := by
  intro q s hs z hz
  rcases overlayLazyOracle_step q s z hz with h | ⟨p, h₁, h₂⟩
  · rw [h]
    exact hs
  · rw [h₂ hs, h₁, ProgrammedCache.relayed_cons_false, hs]

/-- A conflict in the cache of the overlay stays. -/
theorem preservesInv_overlayLazyOracle_conflict :
    QueryImpl.PreservesInv (overlayLazyOracle (A := A)) fun s => s.1.Conflict := by
  intro q s hs z hz
  rcases overlayLazyOracle_step q s z hz with h | ⟨p, h, -⟩
  · rw [h]
    exact hs
  · rw [h]
    exact ProgrammedCache.conflict_cons _ hs

/-- A query to the programming oracle adds one programmed pair, and keeps the lazy cache. -/
theorem programPermOracle_step (q : (PermSpec A).Domain) (s : ProgrammedCache A × PermCache A)
    (z) (hz : z ∈ support ((programPermOracle q).run s)) :
    ∃ p, z.2 = ((p, true) :: s.1, s.2) := by
  rcases q with a | b
  · change z ∈ support ((fun b => (b, (((a, b), true) :: s.1, s.2))) <$>
      (uniformOutside [] a : ProbComp A)) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨b, -, rfl⟩ := hz
    exact ⟨_, rfl⟩
  · change z ∈ support ((fun a => (a, (((a, b), true) :: s.1, s.2))) <$>
      (uniformOutside [] b : ProbComp A)) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨a, -, rfl⟩ := hz
    exact ⟨_, rfl⟩

/-- The programming oracle, beside the coins, keeps the relayed pairs and the lazy cache. -/
theorem preservesInv_programPermImpl_relayed :
    QueryImpl.PreservesInv (programPermImpl (A := A)) fun s => s.2 = s.1.relayed :=
  (preservesInv_passthrough _).add fun q s hs z hz => by
    obtain ⟨p, h⟩ := programPermOracle_step q s z hz
    rw [h]
    exact hs.trans (ProgrammedCache.relayed_cons_true _ _).symm

/-- A conflict stays under the programming oracle, beside the coins. -/
theorem preservesInv_programPermImpl_conflict :
    QueryImpl.PreservesInv (programPermImpl (A := A)) fun s => s.1.Conflict :=
  (preservesInv_passthrough _).add fun q s hs z hz => by
    obtain ⟨p, h⟩ := programPermOracle_step q s z hz
    rw [h]
    exact ProgrammedCache.conflict_cons _ hs

/-! ## Domination until a conflict -/

/-- Until a conflict, the overlay is dominated by the lazy permutation on the whole cache. -/
theorem dominatedUntilBad_overlayLazyOracle :
    QueryImpl.DominatedUntilBad (overlayLazyOracle (A := A)) lazyPermOracle
      (fun s => TaggedCache.untag s.1) (fun s => s.2 = s.1.relayed) fun s => s.1.Conflict := by
  rintro (a | b) ⟨c, l⟩ hl - Q
  · simp only at hl ⊢
    rw [overlayLazyOracle_inl_run, hl]
    rcases h : (TaggedCache.untag c).lookup a with _ | b
    · simp only [h, lazyPermOracle_inl_run, ProgrammedCache.relayed_lookup_eq_none h]
      rw [prEvent_map, prEvent_map, prEvent_map]
      refine (prEvent_mono _ _
        (fun b => Q (b, (a, b) :: TaggedCache.untag c) ∧ b ∉ (TaggedCache.untag c).map Prod.snd)
        fun b hb => ⟨hb.1, ProgrammedCache.notMem_map_snd_of_not_conflict_cons hb.2⟩).trans
        (prEvent_uniformOutside_and_notMem_le
          (c.relayed_sublist.map Prod.snd).subset a a _)
    · simp only [h, lazyPermOracle_inl_run]
      exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
  · simp only at hl ⊢
    rw [overlayLazyOracle_inr_run, hl]
    rcases h : ((TaggedCache.untag c).map Prod.swap).lookup b with _ | a
    · simp only [h, lazyPermOracle_inr_run, ProgrammedCache.relayed_swap_lookup_eq_none h]
      rw [prEvent_map, prEvent_map, prEvent_map]
      refine (prEvent_mono _ _
        (fun a => Q (a, (a, b) :: TaggedCache.untag c) ∧ a ∉ (TaggedCache.untag c).map Prod.fst)
        fun a ha => ⟨ha.1, ProgrammedCache.notMem_map_fst_of_not_conflict_cons ha.2⟩).trans
        (prEvent_uniformOutside_and_notMem_le
          (c.relayed_sublist.map Prod.fst).subset b b _)
    · simp only [h, lazyPermOracle_inr_run]
      exact prEvent_pure_le_pure _ _ _ _ fun h => h.1

/-- Until a conflict, the programming oracle is dominated by the lazy permutation. -/
theorem dominatedUntilBad_programPermImpl :
    QueryImpl.DominatedUntilBad (programPermImpl (A := A)) lazyPermImpl
      (fun s => TaggedCache.untag s.1) (fun s => s.2 = s.1.relayed) fun s => s.1.Conflict := by
  refine dominatedUntilBad_passthrough_add ?_
  rintro (a | b) ⟨c, l⟩ - - Q
  · rw [lazyPermOracle_inl_run]
    change Pr{let z ← (fun b => (b, (((a, b), true) :: c, l))) <$>
      (uniformOutside [] a : ProbComp A)}[
        Q (z.1, TaggedCache.untag z.2.1) ∧ ¬ProgrammedCache.Conflict z.2.1] ≤ _
    rcases h : (TaggedCache.untag c).lookup a with _ | b
    · rw [prEvent_map, prEvent_map]
      exact (prEvent_mono _ _
        (fun b => Q (b, (a, b) :: TaggedCache.untag c) ∧ b ∉ (TaggedCache.untag c).map Prod.snd)
        fun b hb => ⟨hb.1, ProgrammedCache.notMem_map_snd_of_not_conflict_cons hb.2⟩).trans
        (prEvent_uniformOutside_nil_and_notMem_le _ a a _)
    · rw [prEvent_map, prEvent_eq_zero_of_forall_mem_support _ _
        fun y _ hy => hy.2 (ProgrammedCache.conflict_cons_of_lookup h)]
      exact zero_le
  · rw [lazyPermOracle_inr_run]
    change Pr{let z ← (fun a => (a, (((a, b), true) :: c, l))) <$>
      (uniformOutside [] b : ProbComp A)}[
        Q (z.1, TaggedCache.untag z.2.1) ∧ ¬ProgrammedCache.Conflict z.2.1] ≤ _
    rcases h : ((TaggedCache.untag c).map Prod.swap).lookup b with _ | a
    · rw [prEvent_map, prEvent_map]
      exact (prEvent_mono _ _
        (fun a => Q (a, (a, b) :: TaggedCache.untag c) ∧ a ∉ (TaggedCache.untag c).map Prod.fst)
        fun a ha => ⟨ha.1, ProgrammedCache.notMem_map_fst_of_not_conflict_cons ha.2⟩).trans
        (prEvent_uniformOutside_nil_and_notMem_le _ b b _)
    · rw [prEvent_map, prEvent_eq_zero_of_forall_mem_support _ _
        fun y _ hy => hy.2 (ProgrammedCache.conflict_cons_of_swap_lookup h)]
      exact zero_le

end EthLib.Cryptography.LazyPermutation
