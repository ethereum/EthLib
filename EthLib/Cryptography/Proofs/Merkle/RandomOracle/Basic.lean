module

public import EthLib.Cryptography.Proofs.Merkle.Binding.Collision
public import EthLib.Cryptography.Proofs.Merkle.Binding.SecondPreimage
public import VCVio.OracleComp.QueryTracking.SubSpec
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Proofs: Merkle trees in the random-oracle model

A random oracle is a uniformly random function, chosen once for every party.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>

Each oracle input is a node position with its two children, so the oracle is a node hash.

The file counts the oracle calls of a tree, a climb and the two searches.

It also replays a tree, a climb or a search from a cache of answers.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.RandomOracle

open OracleComp OracleSpec ENNReal

variable {D R α : Type} [DecidableEq D]

/-- An experiment: the adversary outputs a claim, then an extraction runs on it.

For example, the claim is a forged path, and the extraction is the collision search on it.

The extraction only calls the oracle. -/
def experimentWith {γ β : Type} (extraction : γ → OracleComp (D →ₒ R) β)
    (adversary : OracleComp (unifSpec + (D →ₒ R)) γ) : OracleComp (unifSpec + (D →ₒ R)) β := do
  let claim ← adversary
  liftComp (extraction claim) (unifSpec + (D →ₒ R))

omit [DecidableEq D] in
/-- The experiment makes the adversary's oracle calls and those of the extraction.

It needs the adversary to make at most `q` calls, and the extraction at most `n` on every claim. -/
theorem experimentWith_queryBound {γ β : Type} {extraction : γ → OracleComp (D →ₒ R) β}
    {adversary : OracleComp (unifSpec + (D →ₒ R)) γ} {q n : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q)
    (hn : ∀ claim, IsQueryBoundP (extraction claim) (fun _ => True) n) :
    IsQueryBoundP (experimentWith extraction adversary) (fun t => t.isRight = true) (q + n) :=
  -- The adversary spends its `q` calls, then the extraction its `n`, on whatever claim it got.
  isQueryBoundP_bind hq fun claim _ => IsQueryBoundP.liftComp_subSpec
    (fun _ => iff_of_true trivial rfl) (hn claim)

/-- An oracle input includes the parent position and its ordered children.

This models a node hash tweaked by its position.

A concrete hash matches it through an injective encoding of this tuple.

Such an encoding exists for levels and positions inside the encodable range.
-/
abbrev NodeInput (R : Type) := Position × R × R

/-- Read a complete oracle table as a node hash in the identity monad.

A complete table gives an answer for every input, as a fixed function does. -/
def nodeHash (g : NodeInput R → R) (p : Position) (a b : R) : Id R :=
  pure (g (p, a, b))

/-- The same node hash, with each call made to the oracle rather than read from a table.

Run against a random oracle, it is the node hash of the random-oracle model. -/
def queryNode (p : Position) (a b : R) : OracleComp (NodeInput R →ₒ R) R :=
  liftM ((NodeInput R →ₒ R).query (p, a, b))

/-- One node-hash call costs one query. -/
theorem queryNode_queryBound (p : Position) (a b : R) :
    IsTotalQueryBound (queryNode p a b) 1 := by
  -- The call is one query followed by returning its answer.
  change IsTotalQueryBound
    (liftM ((NodeInput R →ₒ R).query (p, a, b)) >>= pure) 1
  exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ => trivial⟩

/-- The collision search against the oracle makes two calls per common level.

The bound holds even if the lists have different lengths.

The search stops when the shorter list runs out. -/
theorem findCollision_queryBound [DecidableEq R] :
    ∀ (s t : List R) (p : Position) (a b : R),
      IsTotalQueryBound (findCollision queryNode p a b s t)
        (2 * min s.length t.length) := by
  intro s
  induction s with
  | nil => intros; trivial
  | cons u s ih =>
    intro t p a b
    cases t with
    | nil => trivial
    | cons v t =>
      -- This level makes two queries, one per climb.
      simp only [List.length_cons, min_add_add_right,
        findCollision, queryNode, isTotalQueryBound_query_bind_iff]
      refine ⟨by omega, fun x => ⟨by omega, fun y => ?_⟩⟩
      split
      · -- A collision here stops the search, with no more queries.
        trivial
      · -- Otherwise the rest of the search makes two queries per remaining common level.
        convert ih t p.parent x y using 1
        omega

/-- Computing an honest node from fixed leaves makes `2^level - 1` hash calls.

A subtree with `2^level` leaves has `2^level - 1` inner nodes, one call each. -/
theorem node_queryBound (leaves : Nat → R) : ∀ p : Position,
    IsTotalQueryBound (node queryNode (fun j => pure (leaves j)) p)
      (2 ^ p.level - 1) := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => trivial
  | succ level ih =>
    -- Two subtrees, then one call: (2^level - 1) + (2^level - 1) + 1 = 2^(level + 1) - 1.
    rw [node_succ]
    have h := isTotalQueryBound_bind (ih (2 * j)) fun a =>
      isTotalQueryBound_bind (ih (2 * j + 1)) fun b =>
        queryNode_queryBound ⟨level + 1, j⟩ a b
    convert h using 1
    have := Nat.one_le_two_pow (n := level)
    simp only [Nat.pow_succ]
    omega

/-- Worst-case calls of the second-preimage search, including honest recomputation.

At each level it hashes the candidate and computes the two honest children and parent.

Repeated honest calls still count, even though the oracle answers them from its cache.

From level `l` over `n` siblings, the budget is `2^(l+n+2) - 2^(l+2) - 2n`.

The search queries at most `2^(l+n) - 1 + n` distinct inputs.

On a path of length at least 1, the budget is one to four times that count.

It nears four only for long paths.
-/
def secondPreimageQueries : Nat → Nat → Nat
  | _, 0 => 0
  | level, n + 1 =>
    1 + 2 * (2 ^ level - 1) + (2 ^ (level + 1) - 1) + secondPreimageQueries (level + 1) n

/-- The second-preimage search against the oracle respects its worst-case budget.

The honest leaves are fixed values, so reading a leaf makes no oracle call. -/
theorem findSecondPreimage_queryBound [DecidableEq R] (leaves : Nat → R) :
    ∀ (t : List R) (p : Position) (b : R),
      IsTotalQueryBound (findSecondPreimage queryNode (fun j => pure (leaves j)) p b t)
        (secondPreimageQueries p.level t.length) := by
  intro t
  induction t with
  | nil => intros; trivial
  | cons v t ih =>
    intro p b
    simp only [findSecondPreimage]
    -- This level makes one call for the forged pair, then computes three honest nodes.
    have h := isTotalQueryBound_bind
      (queryNode_queryBound p.parent (ordered p b v).1 (ordered p b v).2)
      fun parent => isTotalQueryBound_bind (node_queryBound leaves p.parent.left)
      fun left => isTotalQueryBound_bind (node_queryBound leaves p.parent.right)
      fun right => isTotalQueryBound_bind (node_queryBound leaves p.parent)
      fun honest => show IsTotalQueryBound
        (if ordered p b v ≠ (left, right) ∧ parent = honest then
          pure (some ⟨p.parent, ordered p b v⟩)
        else findSecondPreimage queryNode (fun j => pure (leaves j)) p.parent parent t)
        (secondPreimageQueries p.parent.level t.length) from by
          split
          · -- A second preimage here stops the search.
            trivial
          · -- Otherwise the rest of the search spends the budget of the levels above.
            exact ih _ _
    -- The calls of this level add up to its term of the budget.
    convert h using 1
    simp only [List.length_cons, secondPreimageQueries, Position.left_level,
      Position.right_level, Position.parent_level, Nat.add_sub_cancel]
    omega

/-- Answering every call of a node from a complete table gives the node of that table's hash. -/
theorem evalWithAnswerFn_node (g : NodeInput R → R) (leaves : Nat → R) : ∀ p : Position,
    evalWithAnswerFn (QueryImpl.ofFn g)
      (node queryNode (fun j => pure (leaves j)) p) =
        (node (nodeHash g) (fun j => pure (leaves j)) p).run := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => rfl
  | succ level ih =>
    -- The children agree by induction, and the last call reads the table.
    simp only [node_succ, evalWithAnswerFn_bind, ih, queryNode,
      evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
    rfl

/-- A parent computed by a replay from a cache has its final call in that cache.

The call hashes the parent's two honest children, at the parent's position.

The cache must agree with a complete table, which gives the honest children. -/
theorem cached_parent_of_partial_node (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (hf : c.AgreesWithFn (QueryImpl.ofFn g))
    (leaves : Nat → R) (p : Position) (a : R)
    (ha : simulateQ c.toPartialImpl
      (node queryNode (fun j => pure (leaves j)) p.parent) = some a) :
    c (p.parent,
      (node (nodeHash g) (fun j => pure (leaves j)) p.parent.left).run,
      (node (nodeHash g) (fun j => pure (leaves j)) p.parent.right).run) = some a := by
  -- The parent replays its left child, then its right child, then its own call.
  rw [node_children _ _ (p := p.parent) (by simp)] at ha
  simp only [simulateQ_bind] at ha
  obtain ⟨left, hl, ha⟩ := Option.bind_eq_some_iff.mp ha
  obtain ⟨right, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  -- The replayed children are the honest children of the table.
  have hleft := c.evalWithAnswerFn_eq_of_agreesWithFn hf _ hl
  have hright := c.evalWithAnswerFn_eq_of_agreesWithFn hf _ hr
  rw [evalWithAnswerFn_node] at hleft hright
  -- The final call was read from the cache, on those two children.
  simp only [queryNode, simulateQ_spec_query, QueryCache.toPartialImpl_apply] at ha
  rwa [← hleft, ← hright] at ha

/-! ## The tree read from a cache -/

/-- Answering every call of a climb from a complete table gives the climb of that table's hash. -/
theorem evalWithAnswerFn_climb (g : NodeInput R → R) : ∀ (t : List R) (p : Position) (b : R),
    evalWithAnswerFn (QueryImpl.ofFn g) (climb queryNode p b t) =
      (climb (nodeHash g) p b t).run
  | [], _, _ => rfl
  | v :: t, p, b => by
    simp only [climb, evalWithAnswerFn_bind, queryNode, evalWithAnswerFn_liftM_query,
      QueryImpl.ofFn_apply]
    exact evalWithAnswerFn_climb g t _ _

/-- Answering every call of the siblings from a complete table gives the siblings of its hash. -/
theorem evalWithAnswerFn_siblings (g : NodeInput R → R) (leaves : Nat → R) :
    ∀ (n : Nat) (p : Position),
      evalWithAnswerFn (QueryImpl.ofFn g) (siblings queryNode (fun j => pure (leaves j)) p n) =
        (siblings (nodeHash g) (fun j => pure (leaves j)) p n).run := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih =>
    intro p
    simp only [siblings, evalWithAnswerFn_bind, evalWithAnswerFn_node, ih, evalWithAnswerFn_pure]
    rfl

/-- A cache that replays node `i / 2^k` at level `level + k` replays node `i` at level `level`. -/
theorem partial_node_go_isSome (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → R)
    (level : Nat) : ∀ (k i : Nat),
      (simulateQ c.toPartialImpl
        (node.go queryNode (fun j => pure (leaves j)) (level + k) (i / 2 ^ k))).isSome →
      (simulateQ c.toPartialImpl
        (node.go queryNode (fun j => pure (leaves j)) level i)).isSome
  | 0, i, h => by simpa using h
  | k + 1, i, h => by
    apply partial_node_go_isSome c leaves level k i
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
    rw [show level + (k + 1) = level + k + 1 by omega, node.go, simulateQ_bind] at hr
    obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
    rw [simulateQ_bind] at hr
    obtain ⟨b, hb, -⟩ := Option.bind_eq_some_iff.mp hr
    -- Node `i / 2^k` is a child of node `i / 2^(k + 1)`.
    have hdiv : i / 2 ^ (k + 1) = i / 2 ^ k / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ k) with h2 | h2
    · have : i / 2 ^ k = 2 * (i / 2 ^ (k + 1)) := by omega
      rw [this, ha]; rfl
    · have : i / 2 ^ k = 2 * (i / 2 ^ (k + 1)) + 1 := by omega
      rw [this, hb]; rfl

/-- A cache that replays the ancestor of a node, `k` levels up, replays the node. -/
theorem partial_node_isSome_of_ancestor (c : (NodeInput R →ₒ R).QueryCache)
    (leaves : Nat → R) (k : Nat) (p : Position)
    (h : (simulateQ c.toPartialImpl
      (node queryNode (fun j => pure (leaves j)) (p.ancestor k))).isSome) :
    (simulateQ c.toPartialImpl (node queryNode (fun j => pure (leaves j)) p)).isSome :=
  partial_node_go_isSome c leaves p.level k p.index h

/-- A cache that replays the ancestor of a node, `n` levels up, replays its `n` siblings. -/
theorem partial_siblings_isSome (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → R) :
    ∀ (n : Nat) (p : Position),
      (simulateQ c.toPartialImpl
        (node queryNode (fun j => pure (leaves j)) (p.ancestor n))).isSome →
      (simulateQ c.toPartialImpl
        (siblings queryNode (fun j => pure (leaves j)) p n)).isSome := by
  intro n
  induction n with
  | zero => intro p _; rfl
  | succ n ih =>
    intro p h
    -- The sibling and the parent sit below the same ancestor.
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (partial_node_isSome_of_ancestor c leaves
      (n + 1) p.sibling (by rwa [← Position.ancestor_parent, Position.sibling_parent,
        Position.ancestor_parent]))
    obtain ⟨rest, hrest⟩ := Option.isSome_iff_exists.mp
      (ih p.parent (by rwa [Position.ancestor_parent]))
    simp [siblings, simulateQ_bind, hs, hrest]

/-- A climb against the oracle makes one call per sibling. -/
theorem climb_queryBound : ∀ (t : List R) (p : Position) (b : R),
    IsTotalQueryBound (climb queryNode p b t) t.length
  | [], _, _ => trivial
  | v :: t, p, b => by
    simp only [climb, queryNode, List.length_cons, isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun x => by simpa using climb_queryBound t p.parent x⟩

end EthLib.Cryptography.Merkle.RandomOracle
