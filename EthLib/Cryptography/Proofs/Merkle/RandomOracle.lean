module

public import EthLib.Cryptography.Proofs.Merkle.Binding
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Classical random-oracle collision bounds

The oracle samples each new input uniformly and remembers its answer.

Source: Bellare and Rogaway, "Random Oracles are Practical", section 2 (Oracles).

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>

Repeated inputs are not collisions, but still count towards the query budget.

The birthday bound here is the loose bound `q^2 / N`, for `N` possible answers.

The proof charges each fresh answer at most `q / N`, including private sampling for free.

These are ideal-oracle statements, not claims about the structure of a concrete hash.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.RandomOracle

open OracleComp OracleSpec ENNReal

variable {D R α : Type} [DecidableEq D]

/-- Two different queried inputs have the same cached answer. -/
def Collision (c : (D →ₒ R).QueryCache) : Prop :=
  ∃ x y r, x ≠ y ∧ c x = some r ∧ c y = some r

/-- A fresh answer can create a collision only by matching an old answer. -/
theorem collision_cacheQuery {c : (D →ₒ R).QueryCache} {t : D} {u : R}
    (hc : ¬ Collision c) (_ht : c t = none) :
    Collision (c.cacheQuery t u) → u ∈ Sigma.snd '' c.toSet := by
  rintro ⟨x, y, r, hxy, hx, hy⟩
  by_cases hxt : x = t
  · subst x
    have hyr : c y = some r := by
      rwa [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy)] at hy
    have hur : u = r := by simpa using hx
    exact ⟨⟨y, r⟩, hyr, hur.symm⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hx
    by_cases hyt : y = t
    · subst y
      have hur : u = r := by simpa using hy
      exact ⟨⟨x, r⟩, hx, hur.symm⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hyt] at hy
      exact (hc ⟨x, y, r, hxy, hx, hy⟩).elim

/-- The collision probability of an adaptive classical client is at most `q * (q / N)`.

Here `N = Nat.card R`, private randomness is free, and the initial cache is empty.
-/
theorem prEvent_collision_le [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (D →ₒ R).romImpl oa).run ∅}[Collision z.2] ≤
      q * ((q : ℝ≥0∞) / Nat.card R) := by
  classical
  -- The budget bounds the cache only on reachable runs, so include it in the bad predicate.
  let P := fun c : (D →ₒ R).QueryCache => Collision c ∧ QueryCache.enncard c ≤ q
  have hfresh (t : D) (c : (D →ₒ R).QueryCache) (hc : ¬ P c) (ht : c t = none) :
      Pr{let u ← $ᵗ R}[P (c.cacheQuery t u)] ≤ (q : ℝ≥0∞) / Nat.card R := by
    by_cases hsize : QueryCache.enncard c ≤ q
    · have hnoc : ¬ Collision c := fun h => hc ⟨h, hsize⟩
      calc
        _ ≤ Pr{let u ← $ᵗ R}[u ∈ Sigma.snd '' c.toSet] :=
          prEvent_mono _ _ _ fun _ h => collision_cacheQuery hnoc ht h.1
        _ ≤ _ := by
          let : MeasurableSpace R := ⊤
          rw [prEvent_eq_evalDist_of_discrete]
          apply (SampleableType.evalDist_uniformSample_le_encard_div _).trans
          gcongr
          exact (ENat.toENNReal_le.mpr (Set.encard_image_le _ _)).trans hsize
    -- An oversized cache cannot re-enter the bounded bad predicate after another query.
    · have hfalse : ∀ u : R, ¬ P (c.cacheQuery t u) := by
        intro u h
        exact hsize ((QueryCache.enncard_mono
          (QueryCache.le_cacheQuery c ht)).trans h.2)
      simp only [hfalse, prEvent_false]
      exact zero_le
  have h := prEvent_run_le_of_fresh_bound_of_isQueryBoundP P
    (by simp [P, Collision]) ((q : ℝ≥0∞) / Nat.card R)
    (ENNReal.div_ne_top (by simp) (by exact_mod_cast (Nat.card_pos.ne' : Nat.card R ≠ 0)))
    hfresh oa hq
  -- Every reachable cache respects the budget, so the bounded event loses no collisions.
  exact (prEvent_mono_of_support _ _ _ fun z hz hc =>
    ⟨hc, enncard_le_of_mem_support_run_unifFwdImpl_add_randomOracle hq hz⟩).trans h

/-- The cache contains a query with the fixed target digest. -/
def Hits (r : R) (c : (D →ₒ R).QueryCache) : Prop := ∃ x, c x = some r

/-- A fixed target digest has hit probability at most `q / N` in `q` queries.

For a second preimage of a fixed honest input `x`, take `D` to exclude `x`.

The honest digest is fixed before this run, and all other oracle cells remain independent.
-/
theorem prEvent_hits_le [SampleableType R]
    (r : R) (oa : OracleComp (unifSpec + (D →ₒ R)) α) {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (D →ₒ R).romImpl oa).run ∅}[Hits r z.2] ≤
      (q : ℝ≥0∞) / Nat.card R := by
  classical
  have hfresh (t : D) (c : (D →ₒ R).QueryCache) (hc : ¬ Hits r c) (_ht : c t = none) :
      Pr{let u ← $ᵗ R}[Hits r (c.cacheQuery t u)] ≤ 1 / (Nat.card R : ℝ≥0∞) := by
    calc
      _ ≤ Pr{let u ← $ᵗ R}[u = r] := prEvent_mono _ _ _ fun u ⟨x, hx⟩ => by
        by_cases hxt : x = t
        · subst x
          simpa using hx
        · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hx
          exact (hc ⟨x, hx⟩).elim
      _ = _ := by simp [SampleableType.prEvent_uniformSample_eq_singleton_natCard, one_div]
  have h := prEvent_run_le_of_fresh_bound_of_isQueryBoundP (Hits r)
    (by simp [Hits]) (1 / (Nat.card R : ℝ≥0∞))
    (ENNReal.div_ne_top (by simp) (by exact_mod_cast (Nat.card_pos.ne' : Nat.card R ≠ 0)))
    hfresh oa hq
  simpa [div_eq_mul_inv] using h

/-- An oracle input includes the parent position and its ordered children.

This models a position-tweaked node hash, with an injective encoding of this tuple.
-/
abbrev NodeInput (R : Type) := Nat × Nat × R × R

/-- Read a complete oracle table as the node hash of the deterministic binding searches. -/
def nodeHash (g : NodeInput R → R) (level j : Nat) (a b : R) : Id R :=
  pure (g (level, j, a, b))

/-- A completed search whose two witness inputs were queried gives a cache collision.

The coverage hypothesis must include the search's queries, not only the adversary's queries.
-/
theorem collision_of_findCollision [DecidableEq R] (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (p q : List R) (level j : Nat) (a b : R)
    (hcovered : ∀ w, findCollision (nodeHash g) level j a b p q = some w →
      c (w.level, w.j, w.x.1, w.x.2) = some (g (w.level, w.j, w.x.1, w.x.2)) ∧
      c (w.level, w.j, w.y.1, w.y.2) = some (g (w.level, w.j, w.y.1, w.y.2)))
    (h : (findCollision (nodeHash g) level j a b p q).isSome) : Collision c := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hne, heq⟩ := (findCollision_valid (nodeHash g) p q level j a b w hw).1
  obtain ⟨hx, hy⟩ := hcovered w hw
  refine ⟨(w.level, w.j, w.x.1, w.x.2), (w.level, w.j, w.y.1, w.y.2),
    g (w.level, w.j, w.x.1, w.x.2), ?_, hx, ?_⟩
  · intro hxy
    exact hne (by simpa using congrArg (fun x : NodeInput R => x.2.2) hxy)
  · simpa [nodeHash] using hy.trans (congrArg some heq.symm)

/-- A second preimage search also gives a collision when both witness inputs were queried.

The honest children and their parent must be computed with the same oracle.
-/
theorem collision_of_findSecondPreimage [DecidableEq R] (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → Id R)
    (q : List R) (level j : Nat) (b : R)
    (hcovered : ∀ w, findSecondPreimage (nodeHash g) leaves level j b q = some w →
      let x := ((node (nodeHash g) leaves w.level (2 * w.j)).run,
        (node (nodeHash g) leaves w.level (2 * w.j + 1)).run)
      c (w.level + 1, w.j, x.1, x.2) = some (g (w.level + 1, w.j, x.1, x.2)) ∧
      c (w.level + 1, w.j, w.y.1, w.y.2) =
        some (g (w.level + 1, w.j, w.y.1, w.y.2)))
    (h : (findSecondPreimage (nodeHash g) leaves level j b q).isSome) : Collision c := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hne, heq⟩ := (findSecondPreimage_valid (nodeHash g) leaves q level j b w hw).1
  obtain ⟨hx, hy⟩ := hcovered w hw
  let x := ((node (nodeHash g) leaves w.level (2 * w.j)).run,
    (node (nodeHash g) leaves w.level (2 * w.j + 1)).run)
  refine ⟨(w.level + 1, w.j, w.y.1, w.y.2), (w.level + 1, w.j, x.1, x.2),
    g (w.level + 1, w.j, w.y.1, w.y.2), ?_, hy, ?_⟩
  · intro hxy
    exact hne (by simpa [x] using congrArg (fun z : NodeInput R => z.2.2) hxy)
  · change g (w.level + 1, w.j, w.y.1, w.y.2) =
        g (w.level + 1, w.j, x.1, x.2) at heq
    exact hx.trans (congrArg some heq.symm)

/-- The collision search with its hash calls exposed to the oracle.

It makes two calls per visited level and stops at the first collision.
-/
def findCollisionM [DecidableEq R] : (level j : Nat) → (a b : R) →
    (p q : List R) → OracleComp (NodeInput R →ₒ R) (Option (Merkle.Collision R))
  | level, j, a, b, s :: p, t :: q => do
    let x := ordered j a s
    let y := ordered j b t
    let parentA ← liftM ((NodeInput R →ₒ R).query (level + 1, j / 2, x.1, x.2))
    let parentB ← liftM ((NodeInput R →ₒ R).query (level + 1, j / 2, y.1, y.2))
    if x ≠ y ∧ parentA = parentB then return some ⟨level + 1, j / 2, x, y⟩
    else findCollisionM (level + 1) (j / 2) parentA parentB p q
  | _, _, _, _, _, _ => pure none

/-- The oracle search is the existing deterministic search under every complete answer table. -/
theorem evalWithAnswerFn_findCollisionM [DecidableEq R] (g : NodeInput R → R) :
    ∀ (p q : List R) (level j : Nat) (a b : R),
      evalWithAnswerFn (QueryImpl.ofFn g) (findCollisionM level j a b p q) =
        findCollision (nodeHash g) level j a b p q := by
  intro p
  induction p with
  | nil => intros; rfl
  | cons s p ih =>
    intro q level j a b
    cases q with
    | nil => rfl
    | cons t q =>
      simp only [findCollisionM, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, findCollision, nodeHash]
      dsimp only [Id.run, pure]
      by_cases h : ordered j a s ≠ ordered j b t ∧
          g (level + 1, j / 2, (ordered j a s).1, (ordered j a s).2) =
            g (level + 1, j / 2, (ordered j b t).1, (ordered j b t).2)
      · simp [h.1, h.2, evalWithAnswerFn_pure]
      · simp only [h, ↓reduceIte]
        exact ih q _ _ _ _

/-- Two calls per common level suffice, even if the lists have different lengths. -/
theorem findCollisionM_queryBound [DecidableEq R] :
    ∀ (p q : List R) (level j : Nat) (a b : R),
      IsTotalQueryBound (findCollisionM level j a b p q)
        (2 * min p.length q.length) := by
  intro p
  induction p with
  | nil => intros; trivial
  | cons s p ih =>
    intro q level j a b
    cases q with
    | nil => trivial
    | cons t q =>
      simp only [List.length_cons, min_add_add_right,
        findCollisionM, isTotalQueryBound_query_bind_iff]
      refine ⟨by omega, fun x => ⟨by omega, fun y => ?_⟩⟩
      split
      · trivial
      · convert ih q (level + 1) (j / 2) x y using 1
        omega

/-- Replaying a successful search from a cache exposes a collision in that cache. -/
theorem collision_of_partial_findCollisionM [DecidableEq R]
    (c : (NodeInput R →ₒ R).QueryCache) :
    ∀ (p q : List R) (level j : Nat) (a b : R) (w : Merkle.Collision R),
      simulateQ c.toPartialImpl (findCollisionM level j a b p q) = some (some w) →
        Collision c := by
  intro p
  induction p with
  | nil => intro q level j a b w hw; simp [findCollisionM] at hw
  | cons s p ih =>
    intro q level j a b w hw
    cases q with
    | nil => simp [findCollisionM] at hw
    | cons t q =>
      simp only [findCollisionM, simulateQ_bind, simulateQ_spec_query,
        QueryCache.toPartialImpl_apply] at hw
      obtain ⟨x, hx, hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨y, hy, hw⟩ := Option.bind_eq_some_iff.mp hw
      split at hw
      · rename_i h
        refine ⟨(level + 1, j / 2, (ordered j a s).1, (ordered j a s).2),
          (level + 1, j / 2, (ordered j b t).1, (ordered j b t).2), x, ?_, hx, ?_⟩
        · intro heq
          exact h.1 (by simpa using congrArg (fun z : NodeInput R => z.2.2) heq)
        · simpa [h.2] using hy
      · exact ih q _ _ x y w hw

/-- The birthday bound for a client without private sampling. -/
theorem prEvent_collision_le_total [SampleableType R]
    (oa : OracleComp (D →ₒ R) α) {q : Nat} (hq : IsTotalQueryBound oa q) :
    Pr{let z ← (simulateQ (D →ₒ R).randomOracle oa).run ∅}[Collision z.2] ≤
      q * ((q : ℝ≥0∞) / Nat.card R) := by
  have hb : IsQueryBoundP (liftComp oa (unifSpec + (D →ₒ R)))
      (fun t => t.isRight = true) q := by
    induction oa using OracleComp.inductionOn generalizing q with
    | pure x => trivial
    | query_bind t k ih =>
      rw [liftComp_bind, liftComp_query]
      change IsQueryBoundP
        (liftM ((unifSpec + (D →ₒ R)).query (.inr t)) >>= fun u =>
          liftComp (k u) (unifSpec + (D →ₒ R))) _ q
      exact ⟨Or.inr hq.1, fun u => ih u (hq.2 u)⟩
  have h := prEvent_collision_le (liftComp oa (unifSpec + (D →ₒ R))) hb
  simpa only [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftComp_right] using h

/-- The existing Merkle collision search succeeds with probability at most `(2h)^2 / N`.

Here `h` is the shorter path length, and the oracle cache starts empty.
-/
theorem prEvent_findCollisionM_le [SampleableType R] [DecidableEq R]
    (p q : List R) (level j : Nat) (a b : R) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).randomOracle
      (findCollisionM level j a b p q)).run ∅}[z.1.isSome] ≤
        (2 * min p.length q.length : Nat) *
          ((2 * min p.length q.length : Nat) / (Nat.card R : ℝ≥0∞)) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le_total _ (findCollisionM_queryBound p q level j a b))
  intro z hz hs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  -- The final cache replays every query of this run without sampling again.
  have hp := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl (findCollisionM level j a b p q) hz
  rw [hw] at hp
  exact collision_of_partial_findCollisionM z.2 p q level j a b w hp

/-- The probability bound transfers to any event that returns a covered Merkle collision.

The budget covers the whole computation, including extraction and honest-tree construction.
-/
theorem prEvent_findCollision_le [SampleableType R] [DecidableEq R]
    (oa : OracleComp (unifSpec + (NodeInput R →ₒ R)) α) (event : α → Prop) {Q : Nat}
    (hQ : IsQueryBoundP oa (fun t => t.isRight = true) Q)
    (hsearch : ∀ z ∈ support ((simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅),
      event z.1 → ∃ (g : NodeInput R → R) (p q : List R) (level j : Nat) (a b : R),
        (findCollision (nodeHash g) level j a b p q).isSome ∧
        ∀ w, findCollision (nodeHash g) level j a b p q = some w →
          z.2 (w.level, w.j, w.x.1, w.x.2) = some (g (w.level, w.j, w.x.1, w.x.2)) ∧
          z.2 (w.level, w.j, w.y.1, w.y.2) = some (g (w.level, w.j, w.y.1, w.y.2))) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅}[event z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_collision_le oa hQ)
  intro z hz he
  obtain ⟨g, p, q, level, j, a, b, hs, hc⟩ := hsearch z hz he
  exact collision_of_findCollision g z.2 p q level j a b hc hs

/-- A covered second preimage search has the same birthday bound.

Unlike a fixed target, its honest ancestor can depend on previous oracle answers.
-/
theorem prEvent_findSecondPreimage_le [SampleableType R] [DecidableEq R]
    (oa : OracleComp (unifSpec + (NodeInput R →ₒ R)) α) (event : α → Prop) {Q : Nat}
    (hQ : IsQueryBoundP oa (fun t => t.isRight = true) Q)
    (hsearch : ∀ z ∈ support ((simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅),
      event z.1 → ∃ (g : NodeInput R → R) (leaves : Nat → Id R)
        (q : List R) (level j : Nat) (b : R),
        (findSecondPreimage (nodeHash g) leaves level j b q).isSome ∧
        ∀ w, findSecondPreimage (nodeHash g) leaves level j b q = some w →
          let x := ((node (nodeHash g) leaves w.level (2 * w.j)).run,
            (node (nodeHash g) leaves w.level (2 * w.j + 1)).run)
          z.2 (w.level + 1, w.j, x.1, x.2) = some (g (w.level + 1, w.j, x.1, x.2)) ∧
          z.2 (w.level + 1, w.j, w.y.1, w.y.2) =
            some (g (w.level + 1, w.j, w.y.1, w.y.2))) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅}[event z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_collision_le oa hQ)
  intro z hz he
  obtain ⟨g, leaves, q, level, j, b, hs, hc⟩ := hsearch z hz he
  exact collision_of_findSecondPreimage g z.2 leaves q level j b hc hs

/-- The same node hash, with calls exposed rather than answered by a fixed table. -/
def queryNode (level j : Nat) (a b : R) : OracleComp (NodeInput R →ₒ R) R :=
  liftM ((NodeInput R →ₒ R).query (level, j, a, b))

/-- One node-hash call costs one query. -/
theorem queryNode_queryBound (level j : Nat) (a b : R) :
    IsTotalQueryBound (queryNode level j a b) 1 := by
  change IsTotalQueryBound
    (liftM ((NodeInput R →ₒ R).query (level, j, a, b)) >>= pure) 1
  exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ => trivial⟩

/-- Computing an honest node from fixed leaves makes `2^level - 1` hash calls. -/
theorem node_queryBound (leaves : Nat → R) : ∀ level j,
    IsTotalQueryBound (node queryNode (fun j => pure (leaves j)) level j)
      (2 ^ level - 1) := by
  intro level
  induction level with
  | zero => intro j; trivial
  | succ level ih =>
    intro j
    rw [node_succ]
    have h := isTotalQueryBound_bind (ih (2 * j)) fun a =>
      isTotalQueryBound_bind (ih (2 * j + 1)) fun b =>
        queryNode_queryBound (level + 1) j a b
    convert h using 1
    have := Nat.one_le_two_pow (n := level)
    rw [Nat.pow_succ]
    omega

/-- Worst-case calls of the literal second-preimage search, including honest recomputation.

At each level it hashes the candidate and computes the two honest children and parent.

Repeated honest calls still count, even though the oracle answers them from its cache.
-/
def secondPreimageQueries : Nat → Nat → Nat
  | _, 0 => 0
  | level, n + 1 =>
    1 + 2 * (2 ^ level - 1) + (2 ^ (level + 1) - 1) + secondPreimageQueries (level + 1) n

/-- The literal second-preimage search with all hash calls exposed.

The honest leaves are fixed values, so reading a leaf makes no oracle call.
-/
def findSecondPreimageM [DecidableEq R] (leaves : Nat → R) :
    (level j : Nat) → R → List R →
      OracleComp (NodeInput R →ₒ R) (Option (SecondPreimage R))
  | level, j, b, t :: q => do
    let y := ordered j b t
    let parent ← queryNode (level + 1) (j / 2) y.1 y.2
    let left ← node queryNode (fun j => pure (leaves j)) level (2 * (j / 2))
    let right ← node queryNode (fun j => pure (leaves j)) level (2 * (j / 2) + 1)
    let honest ← node queryNode (fun j => pure (leaves j)) (level + 1) (j / 2)
    if y ≠ (left, right) ∧ parent = honest then return some ⟨level, j / 2, y⟩
    else findSecondPreimageM leaves (level + 1) (j / 2) parent q
  | _, _, _, [] => pure none

/-- The literal second-preimage search respects its stated worst-case budget. -/
theorem findSecondPreimageM_queryBound [DecidableEq R] (leaves : Nat → R) :
    ∀ (q : List R) (level j : Nat) (b : R),
      IsTotalQueryBound (findSecondPreimageM leaves level j b q)
        (secondPreimageQueries level q.length) := by
  intro q
  induction q with
  | nil => intros; trivial
  | cons t q ih =>
    intro level j b
    simp only [findSecondPreimageM]
    have h := isTotalQueryBound_bind
      (queryNode_queryBound (level + 1) (j / 2) (ordered j b t).1 (ordered j b t).2)
      fun parent => isTotalQueryBound_bind (node_queryBound leaves level (2 * (j / 2)))
      fun left => isTotalQueryBound_bind (node_queryBound leaves level (2 * (j / 2) + 1))
      fun right => isTotalQueryBound_bind (node_queryBound leaves (level + 1) (j / 2))
      fun honest => show IsTotalQueryBound
        (if ordered j b t ≠ (left, right) ∧ parent = honest then
          pure (some ⟨level, j / 2, ordered j b t⟩)
        else findSecondPreimageM leaves (level + 1) (j / 2) parent q)
        (secondPreimageQueries (level + 1) q.length) from by
          split
          · trivial
          · exact ih _ _ _
    convert h using 1
    simp only [List.length_cons, secondPreimageQueries]
    omega

/-- Computing a node against a complete table gives the deterministic honest node. -/
theorem evalWithAnswerFn_node (g : NodeInput R → R) (leaves : Nat → R) : ∀ level j,
    evalWithAnswerFn (QueryImpl.ofFn g)
      (node queryNode (fun j => pure (leaves j)) level j) =
        (node (nodeHash g) (fun j => pure (leaves j)) level j).run := by
  intro level
  induction level with
  | zero => intro j; rfl
  | succ level ih =>
    intro j
    simp only [node, evalWithAnswerFn_bind, ih, queryNode,
      evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
    rfl

/-- The second-preimage oracle search agrees with the existing search for every answer table. -/
theorem evalWithAnswerFn_findSecondPreimageM [DecidableEq R]
    (g : NodeInput R → R) (leaves : Nat → R) : ∀ (q : List R) (level j : Nat) (b : R),
    evalWithAnswerFn (QueryImpl.ofFn g) (findSecondPreimageM leaves level j b q) =
      findSecondPreimage (nodeHash g) (fun j => pure (leaves j)) level j b q := by
  intro q
  induction q with
  | nil => intros; rfl
  | cons t q ih =>
    intro level j b
    simp only [findSecondPreimageM, evalWithAnswerFn_bind, evalWithAnswerFn_node,
      queryNode, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, findSecondPreimage]
    change evalWithAnswerFn (QueryImpl.ofFn g)
      (if ordered j b t ≠
          ((node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2))).run,
            (node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2) + 1)).run) ∧
          g (level + 1, j / 2, (ordered j b t).1, (ordered j b t).2) =
            (node (nodeHash g) (fun j => pure (leaves j)) (level + 1) (j / 2)).run
        then pure _ else _) = (if _ then _ else _)
    by_cases h : ordered j b t ≠
        ((node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2))).run,
          (node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2) + 1)).run) ∧
        g (level + 1, j / 2, (ordered j b t).1, (ordered j b t).2) =
          (node (nodeHash g) (fun j => pure (leaves j)) (level + 1) (j / 2)).run
    · have h' : ordered j b t ≠
          ((node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2))).run,
            (node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2) + 1)).run) ∧
          (nodeHash g (level + 1) (j / 2) (ordered j b t).1 (ordered j b t).2).run =
            (node (nodeHash g) (fun j => pure (leaves j)) (level + 1) (j / 2)).run := h
      rw [ite_eq_left h, ite_eq_left h']
      rfl
    · have h' : ¬ (ordered j b t ≠
          ((node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2))).run,
            (node (nodeHash g) (fun j => pure (leaves j)) level (2 * (j / 2) + 1)).run) ∧
          (nodeHash g (level + 1) (j / 2) (ordered j b t).1 (ordered j b t).2).run =
            (node (nodeHash g) (fun j => pure (leaves j)) (level + 1) (j / 2)).run) := h
      rw [ite_eq_right h, ite_eq_right h']
      exact ih _ _ _

/-- A fixed honest input is excluded from the adversary's query domain.

Conditioned on its digest `r`, each remaining cell is still independent and uniform.

Thus finding a second preimage of that input in `q` classical calls costs at most `q / N`.
-/
theorem prEvent_secondPreimage_le [SampleableType R] (honest : D) (r : R)
    (oa : OracleComp (unifSpec + ({x : D // x ≠ honest} →ₒ R)) α) {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ ({x : D // x ≠ honest} →ₒ R).romImpl oa).run ∅}[∃ x,
      z.2 x = some r] ≤ (q : ℝ≥0∞) / Nat.card R :=
  prEvent_hits_le r oa hq

/-- A successful partial node computation caches its final parent call. -/
theorem cached_parent_of_partial_node (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (hf : c.AgreesWithFn (QueryImpl.ofFn g))
    (leaves : Nat → R) (level j : Nat) (a : R)
    (ha : simulateQ c.toPartialImpl
      (node queryNode (fun j => pure (leaves j)) (level + 1) j) = some a) :
    c (level + 1, j,
      (node (nodeHash g) (fun j => pure (leaves j)) level (2 * j)).run,
      (node (nodeHash g) (fun j => pure (leaves j)) level (2 * j + 1)).run) = some a := by
  simp only [node_succ, simulateQ_bind] at ha
  obtain ⟨left, hl, ha⟩ := Option.bind_eq_some_iff.mp ha
  obtain ⟨right, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  have hleft := c.evalWithAnswerFn_eq_of_agreesWithFn hf _ hl
  have hright := c.evalWithAnswerFn_eq_of_agreesWithFn hf _ hr
  rw [evalWithAnswerFn_node] at hleft hright
  simp only [queryNode, simulateQ_spec_query, QueryCache.toPartialImpl_apply] at ha
  rwa [← hleft, ← hright] at ha

/-- A successful partial second-preimage search exposes two distinct cached inputs. -/
theorem collision_of_partial_findSecondPreimageM [SampleableType R] [DecidableEq R]
    (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → R) :
    ∀ (q : List R) (level j : Nat) (b : R) (w : SecondPreimage R),
      simulateQ c.toPartialImpl (findSecondPreimageM leaves level j b q) = some (some w) →
        Collision c := by
  -- Complete the cache only to identify the repeated honest-child computations.
  obtain ⟨g, hg⟩ := c.exists_agreesWithFn
  intro q
  induction q with
  | nil => intro level j b w hw; simp [findSecondPreimageM] at hw
  | cons t q ih =>
    intro level j b w hw
    simp only [findSecondPreimageM, simulateQ_bind] at hw
    obtain ⟨parent, hp, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨left, hl, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨right, hr, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨honest, hh, hw⟩ := Option.bind_eq_some_iff.mp hw
    split at hw
    · rename_i h
      have hg' : c.AgreesWithFn (QueryImpl.ofFn (fun t => g t)) := hg
      have hleft := c.evalWithAnswerFn_eq_of_agreesWithFn hg' _ hl
      have hright := c.evalWithAnswerFn_eq_of_agreesWithFn hg' _ hr
      rw [evalWithAnswerFn_node] at hleft hright
      have hc := cached_parent_of_partial_node (fun t => g t) c hg leaves
        level (j / 2) honest hh
      rw [hleft, hright] at hc
      refine ⟨(level + 1, j / 2, (ordered j b t).1, (ordered j b t).2),
        (level + 1, j / 2, left, right), parent, ?_, ?_, ?_⟩
      · intro heq
        exact h.1 (by simpa using congrArg (fun z : NodeInput R => z.2.2) heq)
      · simpa [queryNode, simulateQ_spec_query, QueryCache.toPartialImpl_apply] using hp
      · simpa [h.2] using hc
    · exact ih _ _ parent w hw

/-- The literal second-preimage search has the birthday bound at its full query budget.

The bound includes recomputing honest ancestors, rather than treating them as fixed targets.
-/
theorem prEvent_findSecondPreimageM_le [SampleableType R] [DecidableEq R]
    (leaves : Nat → R) (q : List R) (level j : Nat) (b : R) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).randomOracle
      (findSecondPreimageM leaves level j b q)).run ∅}[z.1.isSome] ≤
        (secondPreimageQueries level q.length : ℝ≥0∞) *
          ((secondPreimageQueries level q.length : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le_total _ (findSecondPreimageM_queryBound leaves q level j b))
  intro z hz hs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  have hp := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl (findSecondPreimageM leaves level j b q) hz
  rw [hw] at hp
  exact collision_of_partial_findSecondPreimageM z.2 leaves q level j b w hp

end EthLib.Cryptography.Merkle.RandomOracle
