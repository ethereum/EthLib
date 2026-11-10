module

public import EthLib.Cryptography.Proofs.LazyPermutation
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Proofs: a lazy permutation that records where each pair came from

The lazy permutation keeps the pairs `(a, π a)` answered so far.

Here each pair also carries a tag, set by the query that first answered it.

The oracle takes two tags: one for its forward queries, one for its inverse queries.

Several callers can share one cache, each with its own tags.

Every query only adds pairs at the head of the cache.

So a pair, once in the cache, stays in it with its tag.

A caller that writes the cache directly, and not through queries, can set any tag.

Erase the tags, and the oracle is the lazy permutation, run on the erased cache.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The proofs of their Theorems 1 and 2 keep the pairs of the bijection in separate lists.

In §4.1, Figure 5, the list `Π_O` holds the pairs of the forger's queries in both directions.

Their Figure 6 relays those queries to the challenger.

In both figures the list `Π_S` holds the pairs that the signatures set.

In §4.2, Figure 7, one list holds the pairs of forward queries, and one those of inverse queries.

A set of tags can stand for each such list.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec

variable {A τ : Type}

/-- The pairs `(a, π a)` answered so far, each with its tag, the most recent first. -/
abbrev TaggedCache (A τ : Type) := List ((A × A) × τ)

/-- The cache without its tags. -/
def TaggedCache.untag (c : TaggedCache A τ) : PermCache A :=
  c.map Prod.fst

/-- A pair that joins the cache joins the cache without its tags. -/
@[simp] theorem TaggedCache.untag_cons (e : (A × A) × τ) (c : TaggedCache A τ) :
    TaggedCache.untag (e :: c) = e.1 :: TaggedCache.untag c :=
  rfl

variable [FinEnum A]

/-- The answer to `a` and its tag, from the most recent pair whose first entry is `a`. -/
def TaggedCache.lookupTagged (c : TaggedCache A τ) (a : A) : Option (A × τ) :=
  (c.find? fun e => e.1.1 = a).map fun e => (e.1.2, e.2)

/-- Erasing the tag of a lookup is the lookup in the erased cache. -/
theorem TaggedCache.map_fst_lookupTagged (c : TaggedCache A τ) (a : A) :
    (c.lookupTagged a).map Prod.fst = c.untag.lookup a := by
  induction c with
  | nil => rfl
  | cons e c ih =>
    obtain ⟨⟨a', b⟩, o⟩ := e
    by_cases h : a' = a
    · subst h
      simp [TaggedCache.lookupTagged, TaggedCache.untag]
    · have hne : (a == a') = false := beq_false_of_ne (Ne.symm h)
      simp only [TaggedCache.lookupTagged, TaggedCache.untag, List.find?_cons, h, decide_false,
        List.map_cons, List.lookup, hne] at ih ⊢
      exact ih

/-- The lazy permutation as an oracle, with each new pair tagged.

A new forward query tags its pair with `fwd`, and a new inverse query with `inv`.

A query answered before gets its answer again, and the tag of its pair stays. -/
def taggedLazyPermOracle (fwd inv : τ) :
    QueryImpl (PermSpec A) (StateT (TaggedCache A τ) ProbComp)
  | .inl a => fun c =>
    match c.untag.lookup a with
    | some b => pure (b, c)
    | none =>
      (fun b => (b, ((a, b), fwd) :: c)) <$> (uniformOutside (c.untag.map Prod.snd) a : ProbComp A)
  | .inr b => fun c =>
    match (c.untag.map Prod.swap).lookup b with
    | some a => pure (a, c)
    | none =>
      (fun a => (a, ((a, b), inv) :: c)) <$> (uniformOutside (c.untag.map Prod.fst) b : ProbComp A)

/-- Each query of the tagged oracle, with the tags erased, is the query of the lazy permutation. -/
theorem map_run_taggedLazyPermOracle (fwd inv : τ) (q : (PermSpec A).Domain)
    (c : TaggedCache A τ) :
    Prod.map id TaggedCache.untag <$> (taggedLazyPermOracle fwd inv q).run c =
      (lazyPermOracle q).run c.untag := by
  rcases q with a | b
  · change Prod.map id TaggedCache.untag <$> (match c.untag.lookup a with
        | some b => pure (b, c)
        | none => (fun b => (b, ((a, b), fwd) :: c)) <$>
          (uniformOutside (c.untag.map Prod.snd) a : ProbComp A)) =
      (match c.untag.lookup a with
        | some b => pure (b, c.untag)
        | none => (fun b => (b, (a, b) :: c.untag)) <$>
          (uniformOutside (c.untag.map Prod.snd) a : ProbComp A))
    cases c.untag.lookup a with
    | some b => simp
    | none => simp [Functor.map_map, TaggedCache.untag]
  · change Prod.map id TaggedCache.untag <$> (match (c.untag.map Prod.swap).lookup b with
        | some a => pure (a, c)
        | none => (fun a => (a, ((a, b), inv) :: c)) <$>
          (uniformOutside (c.untag.map Prod.fst) b : ProbComp A)) =
      (match (c.untag.map Prod.swap).lookup b with
        | some a => pure (a, c.untag)
        | none => (fun a => (a, (a, b) :: c.untag)) <$>
          (uniformOutside (c.untag.map Prod.fst) b : ProbComp A))
    cases (c.untag.map Prod.swap).lookup b with
    | some a => simp
    | none => simp [Functor.map_map, TaggedCache.untag]

/-- A run against the tagged oracle, with the tags erased, is the run against the lazy one. -/
theorem map_run_simulateQ_taggedLazyPermOracle {α : Type} (fwd inv : τ)
    (oa : PermComp A α) (c : TaggedCache A τ) :
    Prod.map id TaggedCache.untag <$>
        (simulateQ (unifSpec.passthrough + taggedLazyPermOracle fwd inv) oa).run c =
      (simulateQ lazyPermImpl oa).run c.untag := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t s => ?_) oa c
  rcases t with n | q
  · simp [lazyPermImpl, StateT.run_monadLift, Functor.map_map]
  · exact map_run_taggedLazyPermOracle fwd inv q s

/-- After a forward query, the cache holds the answer to it.

Its tag is the one that `a` had before, or `fwd` if `a` was new. -/
theorem lookup_of_mem_support_taggedLazyPermOracle_forward (fwd inv : τ) {a b : A}
    {c c' : TaggedCache A τ}
    (h : (b, c') ∈ support ((taggedLazyPermOracle fwd inv (.inl a)).run c)) :
    c'.lookupTagged a = some (b, ((c.lookupTagged a).map Prod.snd).getD fwd) := by
  change (b, c') ∈ support (match c.untag.lookup a with
    | some b => pure (b, c)
    | none => (fun b => (b, ((a, b), fwd) :: c)) <$>
      (uniformOutside (c.untag.map Prod.snd) a : ProbComp A)) at h
  rcases hl : c.untag.lookup a with _ | b₀ <;> rw [hl] at h
  · simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
    obtain ⟨b₁, -, rfl, rfl⟩ := h
    rw [← TaggedCache.map_fst_lookupTagged, Option.map_eq_none_iff] at hl
    rw [hl]
    simp [TaggedCache.lookupTagged]
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [← TaggedCache.map_fst_lookupTagged, Option.map_eq_some_iff] at hl
    obtain ⟨⟨b₁, o⟩, ho, rfl⟩ := hl
    simp [ho]

/-- A query of the tagged oracle only adds a pair at the head of the cache. -/
theorem suffix_of_mem_support_taggedLazyPermOracle (fwd inv : τ) (q : (PermSpec A).Domain)
    {b : (PermSpec A).Range q} {c c' : TaggedCache A τ}
    (h : (b, c') ∈ support ((taggedLazyPermOracle fwd inv q).run c)) : c <:+ c' := by
  rcases q with a | b'
  · change (b, c') ∈ support (match c.untag.lookup a with
      | some b => pure (b, c)
      | none => (fun b => (b, ((a, b), fwd) :: c)) <$>
        (uniformOutside (c.untag.map Prod.snd) a : ProbComp A)) at h
    rcases hl : c.untag.lookup a with _ | b₀ <;> rw [hl] at h
    · simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
      obtain ⟨b₁, -, -, rfl⟩ := h
      exact List.suffix_cons _ c
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      exact h.2 ▸ List.suffix_refl c
  · change (b, c') ∈ support (match (c.untag.map Prod.swap).lookup b' with
      | some a => pure (a, c)
      | none => (fun a => (a, ((a, b'), inv) :: c)) <$>
        (uniformOutside (c.untag.map Prod.fst) b' : ProbComp A)) at h
    rcases hl : (c.untag.map Prod.swap).lookup b' with _ | a₀ <;> rw [hl] at h
    · simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
      obtain ⟨a₁, -, -, rfl⟩ := h
      exact List.suffix_cons _ c
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      exact h.2 ▸ List.suffix_refl c

/-- A run against the tagged oracle only adds pairs at the head of the cache.

So a pair, once in the cache, stays in it with its tag.

A newer pair with the same first entry can still hide it from a lookup. -/
theorem suffix_of_mem_support_simulateQ_taggedLazyPermOracle {α : Type} (fwd inv : τ)
    (oa : PermComp A α) (c : TaggedCache A τ) :
    ∀ z ∈ support ((simulateQ (unifSpec.passthrough + taggedLazyPermOracle fwd inv) oa).run c),
      c <:+ z.2 :=
  simulateQ_run_preservesInv _ (fun st => c <:+ st) (fun t s hs z hz => hs.trans (by
    rcases t with n | q
    · obtain ⟨u, s'⟩ := z
      simp [StateT.run_monadLift] at hz
      simp_all
    · exact suffix_of_mem_support_taggedLazyPermOracle fwd inv q
        (b := z.1) (c' := z.2) hz)) oa c (List.suffix_refl c)

end EthLib.Cryptography.LazyPermutation
