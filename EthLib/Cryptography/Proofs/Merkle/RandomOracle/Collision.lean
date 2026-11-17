module

public import EthLib.Cryptography.Proofs.Merkle.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Classical random-oracle collision bounds

A random oracle is a uniformly random function, chosen once for every party.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>

The oracle here samples each new input uniformly and remembers its answer.

Repeated inputs are not collisions, but still count towards the query budget.

The birthday bound here is the loose bound `q^2 / N`, for `N` possible answers.

It exceeds the standard bound `q(q - 1) / (2N)` by the factor `2q / (q - 1)`.

That factor is at most 4 for `q >= 2`, and close to 2 for large `q`.

The proof charges each fresh answer at most `q / N`, and private uniform sampling is not counted.

These are ideal-oracle statements, not claims about the structure of a concrete hash.

## Words used here

- The cache is the table of inputs the oracle has answered so far, with their answers.
- The query budget `q` bounds the oracle calls of a computation, repeated inputs included.
- Private uniform sampling is the computation's own randomness, which makes no oracle call.
- A witness is covered when both inputs it names are in the cache, with the oracle's answers.

## The chain of the argument

- A run of `q` queries puts a collision in its cache with probability at most `q^2 / N`.
- The Merkle searches run against the oracle only make queries.
- A search that succeeds on covered inputs puts a collision in the cache.
- So a forged path is found with probability at most the birthday bound of the whole budget.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.RandomOracle

open OracleComp OracleSpec ENNReal

variable {D R α : Type} [DecidableEq D]

/-- Two different queried inputs have the same cached answer.

This is a collision of the oracle, not of the Merkle node hash.

The theorems below turn a Merkle collision into one of these. -/
def Collision (c : (D →ₒ R).QueryCache) : Prop :=
  ∃ x y r, x ≠ y ∧ c x = some r ∧ c y = some r

/-- A fresh answer can create a collision only by matching an old answer.

So a fresh query creates a collision with probability at most the cache size over `N`. -/
theorem collision_cacheQuery {c : (D →ₒ R).QueryCache} {t : D} {u : R}
    (hc : ¬ Collision c) (_ht : c t = none) :
    Collision (c.cacheQuery t u) → u ∈ Sigma.snd '' c.toSet := by
  rintro ⟨x, y, r, hxy, hx, hy⟩
  -- One of the two colliding inputs must be the new input `t`.
  by_cases hxt : x = t
  · -- The new answer `u` equals the old answer for `y`.
    subst x
    have hyr : c y = some r := by
      rwa [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy)] at hy
    have hur : u = r := by simpa using hx
    exact ⟨⟨y, r⟩, hyr, hur.symm⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hx
    by_cases hyt : y = t
    · -- The new answer `u` equals the old answer for `x`.
      subst y
      have hur : u = r := by simpa using hy
      exact ⟨⟨x, r⟩, hx, hur.symm⟩
    · -- Neither input is new, so the collision was already in the old cache.
      rw [QueryCache.cacheQuery_of_ne _ _ hyt] at hy
      exact (hc ⟨x, y, r, hxy, hx, hy⟩).elim

/-- The birthday bound: `q` oracle queries find a collision with probability at most `q * (q / N)`.

The computation is adaptive: each query may depend on the answers before it.

Here `N = Nat.card R`, private uniform sampling is not counted, and the initial cache is empty.
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

/-- An experiment is won with probability at most `q * (q / N)`.

The hypothesis: each replay of the extraction that ends in a win exposes a collision of the cache.

A replay answers the extraction's calls from the cache, and fails on an input the cache lacks.

Here `N = Nat.card R`, and `q` bounds the oracle calls of the whole experiment, repeats included.

The initial cache is empty, and private uniform sampling is not counted. -/
theorem prEvent_experimentWith_le [SampleableType R] {γ β : Type}
    (extraction : γ → OracleComp (D →ₒ R) β) (wins : β → Prop)
    (collision : ∀ {cache : (D →ₒ R).QueryCache} {claim : γ} {outcome : β},
      simulateQ cache.toPartialImpl (extraction claim) = some outcome → wins outcome →
        Collision cache)
    (adversary : OracleComp (unifSpec + (D →ₒ R)) γ) {q : Nat}
    (hq : IsQueryBoundP (experimentWith extraction adversary) (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (D →ₒ R).romImpl (experimentWith extraction adversary)).run ∅}[
      wins z.1] ≤ q * ((q : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le (experimentWith extraction adversary) hq)
  intro z hz hwins
  simp only [experimentWith, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨claim, cache⟩, -, hz⟩ := hz
  -- The extraction calls only the oracle, which answers with caching.
  rw [QueryImpl.simulateQ_add_liftComp_right] at hz
  -- The final cache replays the extraction without sampling again.
  exact collision (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    _ (extraction claim) hz) hwins

/-- A successful collision search whose witness is covered gives a collision of the cache.

The search runs against a complete table that agrees with the cache on the two inputs.

The coverage hypothesis must include the search's queries, not only the adversary's queries.
-/
theorem collision_of_findCollision [DecidableEq R] (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (s t : List R) (p : Position) (a b : R)
    (hcovered : ∀ w, findCollision (nodeHash g) p a b s t = some w →
      c (w.position, w.x.1, w.x.2) = some (g (w.position, w.x.1, w.x.2)) ∧
      c (w.position, w.y.1, w.y.2) = some (g (w.position, w.y.1, w.y.2)))
    (h : (findCollision (nodeHash g) p a b s t).isSome) : Collision c := by
  -- The search found a valid collision: two different pairs with one hash.
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hne, heq⟩ := (findCollision_valid (nodeHash g) s t p a b w hw).1
  -- Both oracle inputs are in the cache, with the table's answers.
  obtain ⟨hx, hy⟩ := hcovered w hw
  refine ⟨(w.position, w.x.1, w.x.2), (w.position, w.y.1, w.y.2),
    g (w.position, w.x.1, w.x.2), ?_, hx, ?_⟩
  · -- The inputs share the position, so different pairs make different inputs.
    intro hxy
    exact hne (by simpa using congrArg (fun x : NodeInput R => x.2) hxy)
  · -- The two cached answers are the two equal hashes.
    simpa [nodeHash] using hy.trans (congrArg some heq.symm)

/-- A successful second-preimage search whose witness is covered gives a collision of the cache.

The two colliding inputs are the forged pair and the honest children, at one position.

The honest children and their parent must be computed with the same oracle.
-/
theorem collision_of_findSecondPreimage [DecidableEq R] (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → Id R)
    (t : List R) (p : Position) (b : R)
    (hcovered : ∀ w, findSecondPreimage (nodeHash g) leaves p b t = some w →
      let x := ((node (nodeHash g) leaves w.position.left).run,
        (node (nodeHash g) leaves w.position.right).run)
      c (w.position, x.1, x.2) = some (g (w.position, x.1, x.2)) ∧
      c (w.position, w.y.1, w.y.2) = some (g (w.position, w.y.1, w.y.2)))
    (h : (findSecondPreimage (nodeHash g) leaves p b t).isSome) : Collision c := by
  -- The search found a valid second preimage: a wrong pair that hashes to the honest node.
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨⟨hlevel, hne, heq⟩, -, -⟩ := findSecondPreimage_valid (nodeHash g) leaves t p b w hw
  -- Both oracle inputs are in the cache, with the table's answers.
  obtain ⟨hx, hy⟩ := hcovered w hw
  let x := ((node (nodeHash g) leaves w.position.left).run,
    (node (nodeHash g) leaves w.position.right).run)
  refine ⟨(w.position, w.y.1, w.y.2), (w.position, x.1, x.2),
    g (w.position, w.y.1, w.y.2), ?_, hy, ?_⟩
  · -- The inputs share the position, so different pairs make different inputs.
    intro hxy
    exact hne (by simpa [x] using congrArg (fun z : NodeInput R => z.2) hxy)
  · -- The honest node lies above the leaves, so it is the hash of its honest children.
    rw [node_children_run _ leaves hlevel] at heq
    change g (w.position, w.y.1, w.y.2) = g (w.position, x.1, x.2) at heq
    exact hx.trans (congrArg some heq.symm)

/-- Replaying a successful collision search from a cache exposes a collision in that cache.

The replay answers each call from the cache, and fails on an input the cache lacks.

So both inputs of the collision it returns are in the cache. -/
theorem collision_of_partial_findCollision [DecidableEq R]
    (c : (NodeInput R →ₒ R).QueryCache) :
    ∀ (s t : List R) (p : Position) (a b : R) (w : Merkle.Collision R),
      simulateQ c.toPartialImpl (findCollision queryNode p a b s t) = some (some w) →
        Collision c := by
  intro s
  induction s with
  | nil => intro t p a b w hw; simp [findCollision] at hw
  | cons u s ih =>
    intro t p a b w hw
    cases t with
    | nil => simp [findCollision] at hw
    | cons v t =>
      -- The replay read both parents of this level from the cache.
      simp only [findCollision, queryNode, simulateQ_bind, simulateQ_spec_query,
        QueryCache.toPartialImpl_apply] at hw
      obtain ⟨x, hx, hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨y, hy, hw⟩ := Option.bind_eq_some_iff.mp hw
      split at hw
      · -- The search stopped here: two different pairs have one cached answer.
        rename_i h
        refine ⟨(p.parent, (ordered p a u).1, (ordered p a u).2),
          (p.parent, (ordered p b v).1, (ordered p b v).2), x, ?_, hx, ?_⟩
        · intro heq
          exact h.1 (by simpa using congrArg (fun z : NodeInput R => z.2) heq)
        · simpa [h.2] using hy
      · -- The search went on, so the collision is in the replay of the rest.
        exact ih t _ x y w hw

/-- The birthday bound for a computation that only calls the oracle. -/
theorem prEvent_collision_le_total [SampleableType R]
    (oa : OracleComp (D →ₒ R) α) {q : Nat} (hq : IsTotalQueryBound oa q) :
    Pr{let z ← (simulateQ (D →ₒ R).randomOracle oa).run ∅}[Collision z.2] ≤
      q * ((q : ℝ≥0∞) / Nat.card R) := by
  -- Lifted next to a source of private randomness it never uses, it keeps its query budget.
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
  -- Apply the general bound, then drop the unused source of randomness.
  have h := prEvent_collision_le (liftComp oa (unifSpec + (D →ₒ R))) hb
  simpa only [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftComp_right] using h

/-- The collision search against the oracle succeeds with probability at most `(2h)^2 / N`.

Here `h` is the shorter path length, and the oracle cache starts empty.

The paths and leaves are fixed before the oracle is sampled.

Paths chosen after seeing oracle answers need the bound for covered events.
-/
theorem prEvent_findCollision_queryNode_le [SampleableType R] [DecidableEq R]
    (s t : List R) (p : Position) (a b : R) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).randomOracle
      (findCollision queryNode p a b s t)).run ∅}[z.1.isSome] ≤
        (2 * min s.length t.length : Nat) *
          ((2 * min s.length t.length : Nat) / (Nat.card R : ℝ≥0∞)) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le_total _ (findCollision_queryBound s t p a b))
  intro z hz hs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  -- The final cache replays every query of this run without sampling again.
  have hp := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl (findCollision queryNode p a b s t) hz
  rw [hw] at hp
  exact collision_of_partial_findCollision z.2 s t p a b w hp

/-- Any event that yields a covered Merkle collision has the birthday bound of the whole budget.

On every run where the event holds, a collision search over some table must succeed.

Its witness must be covered by the final cache.

The budget covers the whole computation, including extraction and honest-tree construction.
-/
theorem prEvent_findCollision_le [SampleableType R] [DecidableEq R]
    (oa : OracleComp (unifSpec + (NodeInput R →ₒ R)) α) (event : α → Prop) {Q : Nat}
    (hQ : IsQueryBoundP oa (fun t => t.isRight = true) Q)
    (hsearch : ∀ z ∈ support ((simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅),
      event z.1 → ∃ (g : NodeInput R → R) (s t : List R) (p : Position) (a b : R),
        (findCollision (nodeHash g) p a b s t).isSome ∧
        ∀ w, findCollision (nodeHash g) p a b s t = some w →
          z.2 (w.position, w.x.1, w.x.2) = some (g (w.position, w.x.1, w.x.2)) ∧
          z.2 (w.position, w.y.1, w.y.2) = some (g (w.position, w.y.1, w.y.2))) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅}[event z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card R) := by
  -- The event implies a collision of the final cache, which has the birthday bound.
  refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_collision_le oa hQ)
  intro z hz he
  obtain ⟨g, s, t, p, a, b, hs, hc⟩ := hsearch z hz he
  exact collision_of_findCollision g z.2 s t p a b hc hs

/-- Any event that yields a covered second preimage has the same birthday bound.

The bound is a collision bound, not the `q / N` bound for a fixed target.

The honest node is computed with the same oracle, so it can depend on earlier answers.
-/
theorem prEvent_findSecondPreimage_le [SampleableType R] [DecidableEq R]
    (oa : OracleComp (unifSpec + (NodeInput R →ₒ R)) α) (event : α → Prop) {Q : Nat}
    (hQ : IsQueryBoundP oa (fun t => t.isRight = true) Q)
    (hsearch : ∀ z ∈ support ((simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅),
      event z.1 → ∃ (g : NodeInput R → R) (leaves : Nat → Id R)
        (t : List R) (p : Position) (b : R),
        (findSecondPreimage (nodeHash g) leaves p b t).isSome ∧
        ∀ w, findSecondPreimage (nodeHash g) leaves p b t = some w →
          let x := ((node (nodeHash g) leaves w.position.left).run,
            (node (nodeHash g) leaves w.position.right).run)
          z.2 (w.position, x.1, x.2) = some (g (w.position, x.1, x.2)) ∧
          z.2 (w.position, w.y.1, w.y.2) = some (g (w.position, w.y.1, w.y.2))) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅}[event z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card R) := by
  -- The event implies a collision of the final cache, which has the birthday bound.
  refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_collision_le oa hQ)
  intro z hz he
  obtain ⟨g, leaves, t, p, b, hs, hc⟩ := hsearch z hz he
  exact collision_of_findSecondPreimage g z.2 leaves t p b hc hs

/-- Replaying a successful second-preimage search from a cache exposes a collision in that cache.

The two inputs are the forged pair and the honest children, at the same parent position. -/
theorem collision_of_partial_findSecondPreimage [SampleableType R] [DecidableEq R]
    (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → R) :
    ∀ (t : List R) (p : Position) (b : R) (w : SecondPreimage R),
      simulateQ c.toPartialImpl
        (findSecondPreimage queryNode (fun j => pure (leaves j)) p b t) = some (some w) →
        Collision c := by
  -- Complete the cache only to identify the repeated honest-child computations.
  obtain ⟨g, hg⟩ := c.exists_agreesWithFn
  intro t
  induction t with
  | nil => intro p b w hw; simp [findSecondPreimage] at hw
  | cons v t ih =>
    intro p b w hw
    -- The replay read the forged parent and the three honest nodes of this level.
    simp only [findSecondPreimage, simulateQ_bind] at hw
    obtain ⟨parent, hp, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨left, hl, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨right, hr, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨honest, hh, hw⟩ := Option.bind_eq_some_iff.mp hw
    split at hw
    · -- The search stopped here: the forged pair and the honest children share one answer.
      rename_i h
      have hg' : c.AgreesWithFn (QueryImpl.ofFn (fun t => g t)) := hg
      have hleft := c.evalWithAnswerFn_eq_of_agreesWithFn hg' _ hl
      have hright := c.evalWithAnswerFn_eq_of_agreesWithFn hg' _ hr
      rw [evalWithAnswerFn_node] at hleft hright
      have hc := cached_parent_of_partial_node (fun t => g t) c hg leaves p honest hh
      rw [hleft, hright] at hc
      refine ⟨(p.parent, (ordered p b v).1, (ordered p b v).2),
        (p.parent, left, right), parent, ?_, ?_, ?_⟩
      · intro heq
        exact h.1 (by simpa using congrArg (fun z : NodeInput R => z.2) heq)
      · simpa [queryNode, simulateQ_spec_query, QueryCache.toPartialImpl_apply] using hp
      · simpa [h.2] using hc
    · -- The search went on, so the collision is in the replay of the rest.
      exact ih _ parent w hw

/-- The second-preimage search against the oracle has the birthday bound at its full budget.

The bound includes recomputing honest ancestors, rather than treating them as fixed targets.

The path and leaves are fixed before the oracle is sampled.

A path chosen after seeing oracle answers needs the bound for covered events.
-/
theorem prEvent_findSecondPreimage_queryNode_le [SampleableType R] [DecidableEq R]
    (leaves : Nat → R) (t : List R) (p : Position) (b : R) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).randomOracle
      (findSecondPreimage queryNode (fun j => pure (leaves j)) p b t)).run ∅}[z.1.isSome] ≤
        (secondPreimageQueries p.level t.length : ℝ≥0∞) *
          ((secondPreimageQueries p.level t.length : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le_total _ (findSecondPreimage_queryBound leaves t p b))
  intro z hz hs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  have hp := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl (findSecondPreimage queryNode (fun j => pure (leaves j)) p b t) hz
  rw [hw] at hp
  exact collision_of_partial_findSecondPreimage z.2 leaves t p b w hp

/-- There are `2^256` digests of 32 bytes.

So `N = 2^256` in the bounds above, for a 32-byte hash such as SHA-256. -/
theorem card_bytes32 : Nat.card (Vector UInt8 32) = 2 ^ 256 := by
  -- A 32-byte vector is a function from 32 positions to 256 byte values.
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 32), Nat.card_fun,
    Nat.card_eq_fintype_card (α := UInt8), ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  simp

end EthLib.Cryptography.Merkle.RandomOracle
