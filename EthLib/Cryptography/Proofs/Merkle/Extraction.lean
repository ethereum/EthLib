module

public import EthLib.Cryptography.Proofs.Merkle.RandomOracle
public import EthLib.Cryptography.Proofs.RandomOracleFromCache

/-!
# Straight-line extraction of a Merkle commitment

From the queries made before a root is published, an extractor reads what any opening can show.

A verified opening that disagrees with it has a small probability, bounded by query counts.

Source: Chiesa and Yogev, "Building Cryptographic Proofs from Hash Functions", Lemma 18.5.1.

<https://snargsbook.org>

The model differs from the book's.

- One random oracle hashes every node, on the input (position, left child, right child).
- The leaves are digests, with no leaf hash and no salt.
- So the results cover trees that tweak each node hash by its position, not untweaked trees.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.RandomOracle

open OracleComp OracleSpec ENNReal

variable {R : Type}

/-! ## The extractor -/

/-- A cached pair of children with answer `v` at position `p`, if any (by classical choice). -/
noncomputable def invert (c : (NodeInput R →ₒ R).QueryCache) (p : Position) (v : R) :
    Option (R × R) :=
  open Classical in
  if h : ∃ x : R × R, c (p, x.1, x.2) = some v then some h.choose else none

/-- The node the extractor reads at a position, walking down from the root `r` at level `h`.

It costs at most `h` cache lookups by inspection, but that is not proved. -/
noncomputable def extract (c : (NodeInput R →ₒ R).QueryCache) (h : Nat) (r : R)
    (p : Position) : Option R :=
  if p.level < h then
    (extract c h r p.parent).bind fun v =>
      (invert c p.parent v).map fun x => if p.isLeft then x.1 else x.2
  else if p = ⟨h, 0⟩ then some r else none
termination_by h - p.level
decreasing_by simp only [Position.parent_level]; omega

/-- The pair an inversion returns is cached, with the inverted node as its answer. -/
theorem cache_of_invert {c : (NodeInput R →ₒ R).QueryCache} {p : Position} {v : R} {x : R × R}
    (hx : invert c p v = some x) : c (p, x.1, x.2) = some v := by
  unfold invert at hx
  split at hx
  · rename_i h
    cases hx
    exact h.choose_spec
  · cases hx

/-- With no collision, inverting an answer returns the pair cached for it. -/
theorem invert_of_cache {c : (NodeInput R →ₒ R).QueryCache} (hc : ¬ Collision c)
    {p : Position} {a b v : R} (hv : c (p, a, b) = some v) : invert c p v = some (a, b) := by
  have hx : ∃ x : R × R, c (p, x.1, x.2) = some v := ⟨(a, b), hv⟩
  obtain ⟨x, hx'⟩ : ∃ x, invert c p v = some x := by
    unfold invert
    simp [hx]
  rw [hx']
  -- Two different pairs with the answer `v` at one position would collide.
  have hcx := cache_of_invert hx'
  by_contra hne
  exact hc ⟨(p, x.1, x.2), (p, a, b), v, fun h => hne (by simp_all), hcx, hv⟩

/-- The extractor reads the root at the top. -/
theorem extract_top (c : (NodeInput R →ₒ R).QueryCache) (h : Nat) (r : R) :
    extract c h r ⟨h, 0⟩ = some r := by
  rw [extract]
  simp

/-- Below the top, the extractor reads a node by inverting its parent. -/
theorem extract_of_lt (c : (NodeInput R →ₒ R).QueryCache) (h : Nat) (r : R) {p : Position}
    (hp : p.level < h) :
    extract c h r p = (extract c h r p.parent).bind fun v =>
      (invert c p.parent v).map fun x => if p.isLeft then x.1 else x.2 := by
  rw [extract]
  simp only [hp, ↓reduceIte]

/-- At the top level and above, the extractor reads only the root, at index 0. -/
theorem extract_of_not_lt (c : (NodeInput R →ₒ R).QueryCache) (h : Nat) (r : R) {p : Position}
    (hp : ¬ p.level < h) : extract c h r p = if p = ⟨h, 0⟩ then some r else none := by
  rw [extract]
  simp only [hp, ↓reduceIte]

/-! ## A verified climb reads back as the extracted path -/

/-- With no collision, a climb that the cache replays to the root starts at the extracted node. -/
theorem extract_climb (c : (NodeInput R →ₒ R).QueryCache) (hc : ¬ Collision c) (h : Nat)
    (r : R) : ∀ (t : List R) (p : Position) (b : R), p.ancestor t.length = ⟨h, 0⟩ →
      simulateQ c.toPartialImpl (climb queryNode p b t) = some r →
      extract c h r p = some b := by
  intro t
  induction t with
  | nil =>
    intro p b hp hclimb
    simp only [List.length_nil, Position.ancestor_zero] at hp
    subst hp
    simp only [climb, simulateQ_pure] at hclimb
    cases hclimb
    exact extract_top c h _
  | cons s t ih =>
    intro p b hp hclimb
    simp only [climb, queryNode, simulateQ_bind, simulateQ_spec_query,
      QueryCache.toPartialImpl_apply] at hclimb
    obtain ⟨v, hv, hrest⟩ := Option.bind_eq_some_iff.mp hclimb
    have hpar := ih p.parent v (by simpa [Position.ancestor_parent] using hp) hrest
    have hlt : p.level < h := by
      have := congrArg Position.level hp
      simp at this
      omega
    -- Inverting `v` gives the ordered pair, whose child on the side of `p` is the start.
    have hinv := invert_of_cache hc (p := p.parent) hv
    rw [extract_of_lt c h r hlt, hpar]
    simp only [Option.bind_some, hinv, Option.map_some, ordered]
    split <;> simp_all

/-- With no collision, the `k`-th sibling of such a climb is the extracted one. -/
theorem extract_climb_sibling (c : (NodeInput R →ₒ R).QueryCache) (hc : ¬ Collision c)
    (h : Nat) (r : R) : ∀ (t : List R) (p : Position) (b : R), p.ancestor t.length = ⟨h, 0⟩ →
      simulateQ c.toPartialImpl (climb queryNode p b t) = some r →
      ∀ k (hk : k < t.length), extract c h r (p.ancestor k).sibling = some t[k] := by
  intro t
  induction t with
  | nil => intro p b _ _ k hk; simp at hk
  | cons s t ih =>
    intro p b hp hclimb k hk
    simp only [climb, queryNode, simulateQ_bind, simulateQ_spec_query,
      QueryCache.toPartialImpl_apply] at hclimb
    obtain ⟨v, hv, hrest⟩ := Option.bind_eq_some_iff.mp hclimb
    have hp' : p.parent.ancestor t.length = ⟨h, 0⟩ := by
      simpa [Position.ancestor_parent] using hp
    cases k with
    | zero =>
      have hpar := extract_climb c hc h r t p.parent v hp' hrest
      have hlt : p.sibling.level < h := by
        have := congrArg Position.level hp
        simp at this
        simp
        omega
      -- Inverting `v` gives the ordered pair, whose child on the sibling's side is `s`.
      have hinv := invert_of_cache hc (p := p.parent) hv
      rw [Position.ancestor_zero, extract_of_lt c h r hlt, Position.sibling_parent, hpar]
      simp only [Option.bind_some, hinv, Option.map_some, ordered, Position.isLeft_sibling]
      split <;> simp_all
    | succ k =>
      have := ih p.parent v hp' hrest k (by simpa using hk)
      simpa [Position.ancestor_parent] using this

/-- A leaf index below `2^h` has the root position as its ancestor `h` levels up. -/
theorem ancestor_leaf_top {h j : Nat} (hj : j < 2 ^ h) :
    (⟨0, j⟩ : Position).ancestor h = ⟨h, 0⟩ := by
  rw [Position.ancestor_mk_zero, Nat.div_eq_of_lt hj]

/-- With no collision, a verified opening of leaf `j` has the extracted leaf. -/
theorem extract_leaf (c : (NodeInput R →ₒ R).QueryCache) (hc : ¬ Collision c) {h j : Nat}
    {r b : R} {t : List R} (hj : j < 2 ^ h) (ht : t.length = h)
    (hclimb : simulateQ c.toPartialImpl (climb queryNode ⟨0, j⟩ b t) = some r) :
    extract c h r ⟨0, j⟩ = some b :=
  extract_climb c hc h r t ⟨0, j⟩ b (ht ▸ ancestor_leaf_top (ht ▸ hj)) hclimb

/-- With no collision, a verified opening of leaf `j` has the extracted siblings. -/
theorem extract_leaf_sibling (c : (NodeInput R →ₒ R).QueryCache) (hc : ¬ Collision c)
    {h j : Nat} {r b : R} {t : List R} (hj : j < 2 ^ h) (ht : t.length = h)
    (hclimb : simulateQ c.toPartialImpl (climb queryNode ⟨0, j⟩ b t) = some r)
    (k : Nat) (hk : k < t.length) :
    extract c h r ((⟨0, j⟩ : Position).ancestor k).sibling = some t[k] :=
  extract_climb_sibling c hc h r t ⟨0, j⟩ b (ht ▸ ancestor_leaf_top (ht ▸ hj)) hclimb k hk

/-! ## What a query after the commitment can change -/

/-- The values the extractor can read: the root, and each child of a cached query. -/
def extractionTargets (c : (NodeInput R →ₒ R).QueryCache) (r : R) : Set R :=
  insert r {v | ∃ x u, c x = some u ∧ (x.2.1 = v ∨ x.2.2 = v)}

/-- Every node the extractor reads is a target. -/
theorem extract_mem_extractionTargets {c : (NodeInput R →ₒ R).QueryCache} {h : Nat} {r : R}
    {p : Position} {v : R} (hv : extract c h r p = some v) : v ∈ extractionTargets c r := by
  by_cases hlt : p.level < h
  · rw [extract_of_lt c h r hlt] at hv
    obtain ⟨w, -, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hv
    refine Or.inr ⟨(p.parent, x.1, x.2), w, cache_of_invert hx, ?_⟩
    split <;> simp
  · rw [extract_of_not_lt c h r hlt] at hv
    split at hv
    · cases hv
      exact Or.inl rfl
    · cases hv

/-- A query absent from the cache at commitment `c` has a target of `c` as its answer. -/
def LateInversion (c : (NodeInput R →ₒ R).QueryCache) (r : R)
    (c' : (NodeInput R →ₒ R).QueryCache) : Prop :=
  ∃ x, c x = none ∧ ∃ v, c' x = some v ∧ v ∈ extractionTargets c r

/-- Caches `c ≤ c'` that read different nodes, with no collision in `c'`, give a late inversion.

Here `c'` reads a node, and `c` reads another node, or nothing. -/
theorem lateInversion_of_extract {c c' : (NodeInput R →ₒ R).QueryCache} (hle : c ≤ c')
    (hc' : ¬ Collision c') {h : Nat} {r : R} {p : Position} {b : R}
    (hb : extract c' h r p = some b) (hne : extract c h r p ≠ some b) :
    LateInversion c r c' := by
  induction hn : h - p.level generalizing p b with
  | zero =>
    have hlt : ¬ p.level < h := by omega
    rw [extract_of_not_lt c' h r hlt, ← extract_of_not_lt c h r hlt] at hb
    exact (hne hb).elim
  | succ n ih =>
    have hlt : p.level < h := by omega
    rw [extract_of_lt c' h r hlt] at hb
    obtain ⟨w, hw, hb⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hb
    by_cases hpar : extract c h r p.parent = some w
    · have hcx' := cache_of_invert hx
      rcases hcx : c (p.parent, x.1, x.2) with _ | u
      · -- The pair `x` was queried late, and its answer `w` is a target.
        exact ⟨_, hcx, w, hcx', extract_mem_extractionTargets hpar⟩
      · have hu : u = w := by
          have := hle hcx
          rw [hcx'] at this
          exact (Option.some_inj.mp this).symm
        subst hu
        -- The smaller cache has no collision either, so it inverts `w` to `x` as well.
        have hc : ¬ Collision c := fun ⟨y, z, v, hyz, hy, hz⟩ =>
          hc' ⟨y, z, v, hyz, hle hy, hle hz⟩
        have hinv := invert_of_cache hc hcx
        refine (hne ?_).elim
        rw [extract_of_lt c h r hlt, hpar]
        simp [hinv]
    · exact ih hw hpar (by simp; omega)

/-! ## Counting what a late query can hit -/

/-- A cache of `n` entries has at most `2n + 1` targets. -/
theorem encard_extractionTargets_le (c : (NodeInput R →ₒ R).QueryCache) (r : R) :
    ((extractionTargets c r).encard : ℝ≥0∞) ≤ 2 * QueryCache.enncard c + 1 := by
  let f₁ : (Σ _ : NodeInput R, R) → R := fun s => s.1.2.1
  let f₂ : (Σ _ : NodeInput R, R) → R := fun s => s.1.2.2
  have hsub : extractionTargets c r ⊆ insert r (f₁ '' c.toSet ∪ f₂ '' c.toSet) := by
    rintro v (rfl | ⟨x, u, hx, hv | hv⟩)
    · exact Set.mem_insert _ _
    · exact Or.inr (Or.inl ⟨⟨x, u⟩, hx, hv⟩)
    · exact Or.inr (Or.inr ⟨⟨x, u⟩, hx, hv⟩)
  have h : (extractionTargets c r).encard ≤ 2 * c.toSet.encard + 1 :=
    calc (extractionTargets c r).encard
        ≤ (insert r (f₁ '' c.toSet ∪ f₂ '' c.toSet)).encard := Set.encard_le_encard hsub
      _ ≤ (f₁ '' c.toSet ∪ f₂ '' c.toSet).encard + 1 := Set.encard_insert_le _ _
      _ ≤ (f₁ '' c.toSet).encard + (f₂ '' c.toSet).encard + 1 := by
          gcongr; exact Set.encard_union_le _ _
      _ ≤ c.toSet.encard + c.toSet.encard + 1 := by
          gcongr <;> exact Set.encard_image_le _ _
      _ = 2 * c.toSet.encard + 1 := by rw [two_mul]
  rw [QueryCache.enncard]
  exact_mod_cast h

/-! ## The commit-then-open game -/

/-- An opening of one leaf: its index, its value, and its siblings from the bottom up. -/
structure Opening (R : Type) where
  /-- The index of the leaf, from the left, starting at 0. -/
  index : Nat
  /-- The value claimed for the leaf. -/
  leaf : R
  /-- The siblings of the leaf and of its ancestors, from the bottom up. -/
  siblings : List R

/-- The verifier: `h` siblings, an index below `2^h`, and a climb to the root `r`. -/
def verifyOpening [DecidableEq R] (h : Nat) (r : R) (o : Opening R) :
    OracleComp (NodeInput R →ₒ R) Bool :=
  if o.siblings.length = h ∧ o.index < 2 ^ h then
    (fun top => decide (top = r)) <$> climb queryNode ⟨0, o.index⟩ o.leaf o.siblings
  else pure false

/-- The verifier on each opening of a list, with its verdict. -/
def verifyOpenings [DecidableEq R] (h : Nat) (r : R) (os : List (Opening R)) :
    OracleComp (NodeInput R →ₒ R) (List (Opening R × Bool)) :=
  os.mapM fun o => (o, ·) <$> verifyOpening h r o

/-- The verifier makes at most `h` oracle calls. -/
theorem verifyOpening_queryBound [DecidableEq R] (h : Nat) (r : R) (o : Opening R) :
    IsQueryBoundP (verifyOpening h r o) (fun _ => True) h := by
  unfold verifyOpening
  split
  · rename_i hs
    rw [isQueryBoundP_map_iff, ← hs.1]
    exact (climb_queryBound _ _ _).isQueryBoundP
  · trivial

/-- Verifying `n` openings makes at most `n * h` oracle calls. -/
theorem verifyOpenings_queryBound [DecidableEq R] (h : Nat) (r : R) :
    ∀ os : List (Opening R),
      IsQueryBoundP (verifyOpenings h r os) (fun _ => True) (os.length * h)
  | [] => trivial
  | o :: os => by
    simp only [verifyOpenings, List.mapM_cons]
    refine (isQueryBoundP_bind (n := h) (m := os.length * h + 0) ?_ fun _ _ =>
      isQueryBoundP_bind (verifyOpenings_queryBound h r os) fun _ _ => by simp).mono ?_
    · rw [isQueryBoundP_map_iff]
      exact verifyOpening_queryBound h r o
    · simp only [List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- A replay of the list verifier replays the verifier on each opening. -/
theorem verifyOpening_of_verifyOpenings [DecidableEq R] {c : (NodeInput R →ₒ R).QueryCache}
    {h : Nat} {r : R} : ∀ {os : List (Opening R)} {res : List (Opening R × Bool)},
      simulateQ c.toPartialImpl (verifyOpenings h r os) = some res →
      ∀ ob ∈ res, simulateQ c.toPartialImpl (verifyOpening h r ob.1) = some ob.2
  | [], res, hres => by
    simp only [verifyOpenings, List.mapM_nil, simulateQ_pure] at hres
    cases hres
    simp
  | o :: os, res, hres => by
    simp only [verifyOpenings, List.mapM_cons, simulateQ_bind, simulateQ_map,
      simulateQ_pure] at hres
    obtain ⟨⟨o', b⟩, hb, hres⟩ := Option.bind_eq_some_iff.mp hres
    obtain ⟨ok, hok, hpair⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    obtain ⟨rest, hrest, hres⟩ := Option.bind_eq_some_iff.mp hres
    cases hres
    intro ob hob
    rcases List.mem_cons.mp hob with rfl | hob
    · exact hok
    · exact verifyOpening_of_verifyOpenings hrest ob hob

/-- The adversary outputs `n` openings from its state, and the verifier checks them. -/
def openPhase [DecidableEq R] {σ : Type} {n : Nat} (h : Nat) (r : R)
    (opening : σ → OracleComp (unifSpec + (NodeInput R →ₒ R)) (Vector (Opening R) n))
    (st : σ) : OracleComp (unifSpec + (NodeInput R →ₒ R)) (List (Opening R × Bool)) := do
  let os ← opening st
  liftComp (verifyOpenings h r os.toList) (unifSpec + (NodeInput R →ₒ R))

/-- The opening phase makes `q + n * h` oracle calls. -/
theorem openPhase_queryBound [DecidableEq R] {σ : Type} {n : Nat} (h : Nat) (r : R)
    {opening : σ → OracleComp (unifSpec + (NodeInput R →ₒ R)) (Vector (Opening R) n)} {q : Nat}
    (hopening : ∀ st, IsQueryBoundP (opening st) (fun t => t.isRight = true) q) (st : σ) :
    IsQueryBoundP (openPhase h r opening st) (fun t => t.isRight = true) (q + n * h) :=
  isQueryBoundP_bind (hopening st) fun os _ => by
    have := verifyOpenings_queryBound h r os.toList
    rw [Vector.length_toList] at this
    exact IsQueryBoundP.liftComp_subSpec (fun _ => iff_of_true trivial rfl) this

/-- An accepting replay of the verifier gives the shape checks and a replayed climb to `r`. -/
theorem climb_of_verifyOpening [DecidableEq R] {c : (NodeInput R →ₒ R).QueryCache} {h : Nat}
    {r : R} {o : Opening R} (hv : simulateQ c.toPartialImpl (verifyOpening h r o) = some true) :
    o.siblings.length = h ∧ o.index < 2 ^ h ∧
      simulateQ c.toPartialImpl (climb queryNode ⟨0, o.index⟩ o.leaf o.siblings) = some r := by
  unfold verifyOpening at hv
  split at hv
  · rename_i hs
    refine ⟨hs.1, hs.2, ?_⟩
    rw [simulateQ_map] at hv
    obtain ⟨top, htop, hv⟩ := Option.map_eq_some_iff.mp hv
    simp only [decide_eq_true_eq] at hv
    rwa [← hv]
  · simp at hv

/-- The final cache of the opening phase replays the list verifier. -/
theorem verifyOpenings_of_mem_support_openPhase [SampleableType R] [DecidableEq R] {σ : Type}
    {n h : Nat} {r : R}
    {opening : σ → OracleComp (unifSpec + (NodeInput R →ₒ R)) (Vector (Opening R) n)} {st : σ}
    {c : (NodeInput R →ₒ R).QueryCache}
    {y : List (Opening R × Bool) × (NodeInput R →ₒ R).QueryCache}
    (hy : y ∈ support ((simulateQ (NodeInput R →ₒ R).romImpl (openPhase h r opening st)).run c)) :
    ∃ os : List (Opening R), simulateQ y.2.toPartialImpl (verifyOpenings h r os) = some y.1 := by
  simp only [openPhase, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
  obtain ⟨⟨os, c₁⟩, -, hy⟩ := hy
  -- The verifier only calls the oracle, and its final cache replays each call.
  rw [QueryImpl.simulateQ_add_liftComp_right] at hy
  exact ⟨_, QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching _ _ hy⟩

/-- What a run of the game leaves for the extractor. -/
structure Transcript (R : Type) where
  /-- The root the adversary commits to. -/
  root : R
  /-- The oracle cache at the moment of the commitment, which the extractor reads. -/
  committed : (NodeInput R →ₒ R).QueryCache
  /-- The openings the adversary outputs later, each with the verifier's verdict. -/
  openings : List (Opening R × Bool)
  /-- The oracle cache at the end of the run. -/
  final : (NodeInput R →ₒ R).QueryCache

/-- The commit-then-open game: commit to a root, record the cache, then open `n` leaves. -/
def commitOpen [SampleableType R] [DecidableEq R] {σ : Type} {n : Nat} (h : Nat)
    (commit : OracleComp (unifSpec + (NodeInput R →ₒ R)) (R × σ))
    (opening : σ → OracleComp (unifSpec + (NodeInput R →ₒ R)) (Vector (Opening R) n)) :
    ProbComp (Transcript R) := do
  let z ← (simulateQ (NodeInput R →ₒ R).romImpl commit).run ∅
  let y ← (simulateQ (NodeInput R →ₒ R).romImpl (openPhase h z.1.1 opening z.1.2)).run z.2
  return ⟨z.1.1, z.2, y.1, y.2⟩

/-- The leaf or a sibling of an opening differs from what the extractor reads. -/
def DisagreesWithExtraction (c : (NodeInput R →ₒ R).QueryCache) (h : Nat) (r : R)
    (o : Opening R) : Prop :=
  extract c h r ⟨0, o.index⟩ ≠ some o.leaf ∨
    ∃ k, ∃ hk : k < o.siblings.length,
      extract c h r ((⟨0, o.index⟩ : Position).ancestor k).sibling ≠ some o.siblings[k]

/-- Some accepted opening disagrees with the extractor on the cache at commitment. -/
def EscapesExtraction (h : Nat) (w : Transcript R) : Prop :=
  ∃ ob ∈ w.openings, ob.2 = true ∧ DisagreesWithExtraction w.committed h w.root ob.1

/-- An escaping run has a collision or a late inversion in its final cache. -/
theorem collision_or_lateInversion_of_escapesExtraction [SampleableType R] [DecidableEq R]
    {σ : Type} {n h : Nat} {commit : OracleComp (unifSpec + (NodeInput R →ₒ R)) (R × σ)}
    {opening : σ → OracleComp (unifSpec + (NodeInput R →ₒ R)) (Vector (Opening R) n)}
    {w : Transcript R} (hw : w ∈ support (commitOpen h commit opening))
    (he : EscapesExtraction h w) :
    Collision w.final ∨ LateInversion w.committed w.root w.final := by
  simp only [commitOpen, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨z, -, y, hy, rfl⟩ := hw
  obtain ⟨⟨o, ok⟩, hmem, hacc, hdis⟩ := he
  dsimp only at hacc hdis ⊢
  subst hacc
  have hle : z.2 ≤ y.2 :=
    le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ hy
  obtain ⟨os, hos⟩ := verifyOpenings_of_mem_support_openPhase hy
  obtain ⟨hlen, hj, hclimb⟩ := climb_of_verifyOpening (verifyOpening_of_verifyOpenings hos _ hmem)
  by_cases hc : Collision y.2
  · exact Or.inl hc
  refine Or.inr ?_
  rcases hdis with hne | ⟨k, hk, hne⟩
  · exact lateInversion_of_extract hle hc (extract_leaf y.2 hc hj hlen hclimb) hne
  · exact lateInversion_of_extract hle hc (extract_leaf_sibling y.2 hc hj hlen hclimb k hk) hne

/-- Lemma 18.5.1: escape has probability at most `Q^2 / N + (q_2 + n h)(2 q_1 + 1) / N`.

Here `Q = q_1 + q_2 + n h`, and `N` is the number of possible answers. -/
theorem prEvent_escapesExtraction_le [SampleableType R] [DecidableEq R] {σ : Type} {n : Nat}
    (h : Nat) (commit : OracleComp (unifSpec + (NodeInput R →ₒ R)) (R × σ))
    (opening : σ → OracleComp (unifSpec + (NodeInput R →ₒ R)) (Vector (Opening R) n))
    {q₁ q₂ : Nat}
    (hcommit : IsQueryBoundP commit (fun t => t.isRight = true) q₁)
    (hopening : ∀ st, IsQueryBoundP (opening st) (fun t => t.isRight = true) q₂) :
    Pr{let w ← commitOpen h commit opening}[EscapesExtraction h w] ≤
      ((q₁ + q₂ + n * h : Nat) : ℝ≥0∞) * ((q₁ + q₂ + n * h : Nat) / (Nat.card R : ℝ≥0∞)) +
        ((q₂ + n * h : Nat) : ℝ≥0∞) * ((2 * q₁ + 1 : Nat) / (Nat.card R : ℝ≥0∞)) := by
  have hN : (Nat.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.card_pos.ne' : Nat.card R ≠ 0)
  calc Pr{let w ← commitOpen h commit opening}[EscapesExtraction h w]
      ≤ Pr{let w ← commitOpen h commit opening}[
          Collision w.final ∨ LateInversion w.committed w.root w.final] :=
        prEvent_mono_of_support _ _ _ fun _ hw he =>
          collision_or_lateInversion_of_escapesExtraction hw he
    _ ≤ Pr{let w ← commitOpen h commit opening}[Collision w.final] +
          Pr{let w ← commitOpen h commit opening}[LateInversion w.committed w.root w.final] :=
        prEvent_or_le _ _ _
    _ ≤ _ := add_le_add ?_ ?_
  · -- Collision term: the final cache is that of one run of both phases.
    have hrun : (fun w => w.final) <$> commitOpen h commit opening =
        Prod.snd <$> (simulateQ (NodeInput R →ₒ R).romImpl
          (commit >>= fun x => openPhase h x.1 opening x.2)).run ∅ := by
      simp [commitOpen, simulateQ_bind, StateT.run_bind, map_bind]
    have hq := isQueryBoundP_bind hcommit fun x _ => openPhase_queryBound h x.1 hopening x.2
    rw [← prEvent_map (commitOpen h commit opening) (fun w => w.final) Collision, hrun,
      prEvent_map]
    simpa [Nat.add_assoc] using prEvent_collision_le _ hq
  · -- Late-inversion term: fix the commitment phase, then use the fresh-answer bound.
    rw [commitOpen]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
    simp only [bind_pure_comp, prEvent_map]
    have hsize := enncard_le_of_mem_support_run_unifFwdImpl_add_randomOracle hcommit hz
    refine prEvent_run_le_of_fresh_bound_from (LateInversion z.2 z.1.1) _
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hN) (fun t c hc ht => ?_) _
      (openPhase_queryBound h z.1.1 hopening z.1.2) z.2
      (fun ⟨x, hx, v, hv, _⟩ => by simp [hx] at hv) (ne_top_of_le_ne_top (by simp) hsize)
    -- A fresh answer causes a late inversion only by landing on a target.
    calc Pr{let u ← $ᵗ R}[LateInversion z.2 z.1.1 (c.cacheQuery t u)]
        ≤ Pr{let u ← $ᵗ R}[u ∈ extractionTargets z.2 z.1.1] :=
          prEvent_mono _ _ _ fun u ⟨x, hx, v, hv, hmem⟩ => by
            by_cases hxt : x = t
            · subst x
              simp only [QueryCache.cacheQuery_self, Option.some_inj] at hv
              rwa [hv]
            · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hv
              exact (hc ⟨x, hx, v, hv, hmem⟩).elim
      _ ≤ ((extractionTargets z.2 z.1.1).encard : ℝ≥0∞) / Nat.card R := by
          let : MeasurableSpace R := ⊤
          rw [prEvent_eq_evalDist_of_discrete]
          exact SampleableType.evalDist_uniformSample_le_encard_div _
      _ ≤ _ := by
          gcongr
          refine (encard_extractionTargets_le _ _).trans ?_
          push_cast
          gcongr

end EthLib.Cryptography.Merkle.RandomOracle
