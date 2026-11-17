module

public import EthLib.Cryptography.Proofs.Merkle.Multiproof.Basic
public import EthLib.Cryptography.Proofs.Merkle.Binding.Collision

/-!
# Proofs: a multiproof binds its opened nodes

Two multiproofs that rebuild one root open the same values, or a search finds a collision.

The search walks both rebuilds down from the root to two different pairs hashed to one node.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Position → α → α → Id α)

/-- Walk two rebuilds down in lockstep from level `level` and index `j`, and return a collision.

A node given by either rebuild ends the walk there, since that rebuild does not hash it.

The result is `none` when the walk finds no two different pairs with one hash. -/
def findMultiproofCollision [DecidableEq α] (first second : List (Position × α)) :
    (level j : Nat) → Option (Collision α)
  | 0, _ => none
  | level + 1, j =>
    if (first.lookup ⟨level + 1, j⟩).isSome || (second.lookup ⟨level + 1, j⟩).isSome then none
    else
      match (rebuild.go hash first level (2 * j)).run,
        (rebuild.go hash first level (2 * j + 1)).run,
        (rebuild.go hash second level (2 * j)).run,
        (rebuild.go hash second level (2 * j + 1)).run with
      | some a, some a', some b, some b' =>
        -- Different pairs with one hash: this node is the collision.
        if (a, a') ≠ (b, b') ∧
            (hash ⟨level + 1, j⟩ a a').run = (hash ⟨level + 1, j⟩ b b').run then
          some ⟨⟨level + 1, j⟩, (a, a'), (b, b')⟩
        -- Otherwise the collision, if any, is further down.
        else (findMultiproofCollision first second level (2 * j)).or
          (findMultiproofCollision first second level (2 * j + 1))
      | _, _, _, _ => none

/-- What the search returns is a real collision, at a node that both rebuilds hash.

Each pair is the two children that its own rebuild determines there.

So a reduction knows exactly which two hash calls collide. -/
theorem findMultiproofCollision_valid [DecidableEq α] {first second : List (Position × α)} :
    ∀ {l j : Nat} {c : Collision α}, findMultiproofCollision hash first second l j = some c →
      c.Valid hash ∧ 1 ≤ c.position.level ∧
      first.lookup c.position = none ∧ second.lookup c.position = none ∧
      (rebuild.go hash first c.position.left.level c.position.left.index).run = some c.x.1 ∧
      (rebuild.go hash first c.position.right.level c.position.right.index).run = some c.x.2 ∧
      (rebuild.go hash second c.position.left.level c.position.left.index).run = some c.y.1 ∧
      (rebuild.go hash second c.position.right.level c.position.right.index).run = some c.y.2
  | 0, _, _, found => by simp [findMultiproofCollision] at found
  | l + 1, j, c, found => by
    unfold findMultiproofCollision at found
    split at found
    · cases found
    -- Neither rebuild is given this node.
    rename_i notGiven
    simp only [Bool.or_eq_true, not_or, Option.not_isSome_iff_eq_none] at notGiven
    split at found
    · rename_i a a' b b' ha ha' hb hb'
      split at found
      · -- The collision is at this node, with the children each rebuild determines.
        rename_i collides
        cases found
        exact ⟨collides, by simp, notGiven.1, notGiven.2, ha, ha', hb, hb'⟩
      · -- The collision is below, on one side or the other.
        rcases Option.or_eq_some_iff.mp found with left | ⟨-, right⟩
        · exact findMultiproofCollision_valid left
        · exact findMultiproofCollision_valid right
    · cases found

/-- The search never finds a collision between a rebuild and itself.

Its two pairs are equal at every node.

So the search can only succeed on two rebuilds that differ somewhere. -/
theorem findMultiproofCollision_self [DecidableEq α] (nodes : List (Position × α)) :
    ∀ l j, findMultiproofCollision hash nodes nodes l j = none
  | 0, _ => rfl
  | l + 1, j => by
    unfold findMultiproofCollision
    split
    · rfl
    split
    · -- The two pairs come from the same rebuild, so they are equal.
      rename_i a a' b b' ha ha' hb hb'
      rw [ha] at hb
      rw [ha'] at hb'
      cases hb
      cases hb'
      simp [findMultiproofCollision_self nodes l (2 * j),
        findMultiproofCollision_self nodes l (2 * j + 1)]
    · rfl

/-- A property of the nodes given that the hash outputs have holds of the collision pairs.

For example, every node given has 32 bytes and so has every digest of the hash.

So the two inputs of a collision have the shape that the hash expects. -/
theorem findMultiproofCollision_children [DecidableEq α] (P : α → Prop)
    (output : ∀ p a b, P (hash p a b).run) {first second : List (Position × α)}
    (firstNodes : ∀ e ∈ first, P e.2) (secondNodes : ∀ e ∈ second, P e.2) {l j : Nat}
    {c : Collision α} (found : findMultiproofCollision hash first second l j = some c) :
    P c.x.1 ∧ P c.x.2 ∧ P c.y.1 ∧ P c.y.2 := by
  obtain ⟨-, -, -, -, x1, x2, y1, y2⟩ := findMultiproofCollision_valid hash found
  -- Every rebuilt node is a node given or a hash output.
  have holds : ∀ nodes : List (Position × α), (∀ e ∈ nodes, P e.2) →
      ∀ l j v, (rebuild.go hash nodes l j).run = some v → P v := fun nodes given l j v rebuilt =>
    rebuild_go_induction hash (fun _ v => P v) (fun e he => given e he)
      (fun p a b _ _ _ => output p a b) l j v rebuilt
  exact ⟨holds _ firstNodes _ _ _ x1, holds _ firstNodes _ _ _ x2,
    holds _ secondNodes _ _ _ y1, holds _ secondNodes _ _ _ y2⟩

/-- Two rebuilds given a node `q` and nothing above it, equal at an ancestor, agree on `q`.

Otherwise the search from that ancestor succeeds. -/
theorem rebuild_go_binding [DecidableEq α] {first second : List (Position × α)} {q : Position}
    {a b : α} (firstAt : first.lookup q = some a) (secondAt : second.lookup q = some b)
    (firstBelow : ∀ e ∈ first, e.1.IsAncestor q → e.1 = q)
    (secondBelow : ∀ e ∈ second, e.1.IsAncestor q → e.1 = q) :
    ∀ (l j : Nat) (v : α), (⟨l, j⟩ : Position).IsAncestor q →
      (rebuild.go hash first l j).run = some v → (rebuild.go hash second l j).run = some v →
      a = b ∨ (findMultiproofCollision hash first second l j).isSome := by
  intro l
  induction l with
  | zero =>
    intro j v above firstRoot secondRoot
    -- At level 0 the node is `q` itself, which both rebuilds read as given.
    have same := above.eq_of_level_le (Nat.zero_le _)
    rw [← same] at firstAt secondAt
    rw [rebuild_go_of_lookup hash firstAt] at firstRoot
    rw [rebuild_go_of_lookup hash secondAt] at secondRoot
    exact .inl (Option.some.inj (firstRoot.trans secondRoot.symm))
  | succ l ih =>
    intro j v above firstRoot secondRoot
    by_cases atQ : (⟨l + 1, j⟩ : Position) = q
    · -- At `q` itself, both rebuilds return the value they are given.
      rw [← atQ] at firstAt secondAt
      rw [rebuild_go_of_lookup hash firstAt] at firstRoot
      rw [rebuild_go_of_lookup hash secondAt] at secondRoot
      exact .inl (Option.some.inj (firstRoot.trans secondRoot.symm))
    -- Strictly above `q`, neither rebuild is given the node.
    have absent : ∀ nodes : List (Position × α), (∀ e ∈ nodes, e.1.IsAncestor q → e.1 = q) →
        nodes.lookup ⟨l + 1, j⟩ = none := by
      intro nodes below
      cases found : nodes.lookup ⟨l + 1, j⟩ with
      | none => rfl
      | some w => exact absurd (below _ (mem_of_lookup_eq_some found) above) atQ
    have firstAbsent := absent first firstBelow
    have secondAbsent := absent second secondBelow
    rw [rebuild_go_succ_of_lookup_none hash firstAbsent] at firstRoot
    rw [rebuild_go_succ_of_lookup_none hash secondAbsent] at secondRoot
    -- Both rebuilds hash two children into the same value.
    split at firstRoot
    case h_2 => cases firstRoot
    rename_i x x' hx hx'
    split at secondRoot
    case h_2 => cases secondRoot
    rename_i y y' hy hy'
    cases firstRoot
    have sameHash := Option.some.inj secondRoot
    unfold findMultiproofCollision
    simp only [firstAbsent, secondAbsent, Option.isSome_none, Bool.or_false, Bool.false_eq_true,
      ↓reduceIte, hx, hx', hy, hy']
    split
    · exact .inr rfl
    rename_i noCollision
    -- Without a collision here, the two pairs are equal, so the children agree.
    have pairs : (x, x') = (y, y') := by
      refine Classical.byContradiction fun differ => noCollision ⟨differ, ?_⟩
      exact sameHash.symm
    simp only [Prod.mk.injEq] at pairs
    obtain ⟨rfl, rfl⟩ := pairs
    -- The child on the side of `q` is the ancestor of `q` one level below this node.
    obtain ⟨m, hm⟩ := id above
    cases m with
    | zero => exact absurd (hm.trans (Position.ancestor_zero q)) atQ
    | succ m =>
    have parent : (q.ancestor m).parent = ⟨l + 1, j⟩ := by rw [Position.parent_ancestor, hm]
    have level : (q.ancestor m).level = l := by
      have := congrArg Position.level parent
      simp only [Position.parent_level] at this
      omega
    have index : (q.ancestor m).index / 2 = j := congrArg Position.index parent
    have toQ : (q.ancestor m).IsAncestor q := ⟨m, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one (q.ancestor m).index with even | odd
    · have child : (⟨l, 2 * j⟩ : Position) = q.ancestor m :=
        Position.ext level.symm (by dsimp only; omega)
      rcases ih (2 * j) x (child ▸ toQ) hx hy with same | found
      · exact .inl same
      · exact .inr (by simp [Option.isSome_or, found])
    · have child : (⟨l, 2 * j + 1⟩ : Position) = q.ancestor m :=
        Position.ext level.symm (by dsimp only; omega)
      rcases ih (2 * j + 1) x' (child ▸ toQ) hx' hy' with same | found
      · exact .inl same
      · exact .inr (by simp [Option.isSome_or, found])

/-- Binding: two accepted multiproofs for the same opened nodes open the same values.

Otherwise the search over the two rebuilds finds a collision, which is valid by the theorem above.

The opened nodes are distinct, in the tree of height `h`, and none is an ancestor of another.

So opening a node of a committed tree to two values breaks collision resistance. -/
theorem verify_binding [DecidableEq α] {h : Nat} {opened : List Position}
    {values values' helperValues helperValues' : List α} {root : α}
    (unique : opened.Nodup) (antichain : ∀ a ∈ opened, ∀ b ∈ opened, a.IsAncestor b → a = b)
    (inside : ∀ p ∈ opened, (⟨h, 0⟩ : Position).IsAncestor p)
    (valueCount : values.length = opened.length) (valueCount' : values'.length = opened.length)
    (first : (verify hash h opened values helperValues).run = some root)
    (second : (verify hash h opened values' helperValues').run = some root) :
    values = values' ∨
      (findMultiproofCollision hash (opened.zip values ++ (helpers h opened).zip helperValues)
        (opened.zip values' ++ (helpers h opened).zip helperValues') h 0).isSome := by
  by_cases found : (findMultiproofCollision hash
      (opened.zip values ++ (helpers h opened).zip helperValues)
      (opened.zip values' ++ (helpers h opened).zip helperValues') h 0).isSome
  · exact .inr found
  refine .inl (List.ext_getElem (by omega) fun i hi hi' => ?_)
  have hk : i < opened.length := by omega
  -- No node given is strictly above an opened node: not another opened node, not a helper.
  have below : ∀ (vs hs : List α), ∀ e ∈ opened.zip vs ++ (helpers h opened).zip hs,
      e.1.IsAncestor opened[i] → e.1 = opened[i] := by
    intro vs hs e he above
    rcases List.mem_append.mp he with he | he
    · exact antichain _ (List.of_mem_zip he).1 _ (List.getElem_mem hk) above
    · exact absurd above (helper_not_isAncestor (List.of_mem_zip he).1 (List.getElem_mem hk))
  -- Both rebuilds read the opened node as given, and the root is an ancestor of it.
  rcases rebuild_go_binding hash (lookup_zip_getElem unique _ hk hi)
      (lookup_zip_getElem unique _ hk hi') (below _ _) (below _ _) h 0 root
      (inside _ (List.getElem_mem hk)) first second with same | collides
  · exact same
  · exact absurd collides found

end EthLib.Cryptography.Merkle
