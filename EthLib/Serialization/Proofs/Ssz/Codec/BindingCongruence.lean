import EthLib.Serialization.Proofs.Ssz.Codec.BindingTrace

/-! Collision-free computations preserve the roots at every aligned subtree position. -/

namespace EthLib.Serialization.Ssz.CommitmentTree

/-- The two finite computations contain no conflicting equal hash outputs. -/
def NoCollision (left right : CommitmentTree) : Prop := ¬ Collision left right

/-- Every compression input of one computation occurs in another. -/
def Included (small large : CommitmentTree) : Prop :=
  ∀ input ∈ small.messages, input ∈ large.messages

/-- Every computation contains its own hash inputs. -/
@[refl] theorem Included.refl (tree : CommitmentTree) : Included tree tree := fun _ h => h

/-- Inclusion of hash inputs composes through nested computations. -/
theorem Included.trans {a b c : CommitmentTree} (ab : Included a b) (bc : Included b c) :
    Included a c := fun input member => bc input (ab input member)

/-- A parent computation contains every input from its left subtree. -/
theorem Included.fork_left (left right : CommitmentTree) : Included left (.fork left right) :=
  fun _ member => List.mem_cons_of_mem _ (List.mem_append_left _ member)

/-- A parent computation contains every input from its right subtree. -/
theorem Included.fork_right (left right : CommitmentTree) : Included right (.fork left right) :=
  fun _ member => List.mem_cons_of_mem _ (List.mem_append_right _ member)

/-- Subcomputations inherit the absence of conflicting equal hash outputs. -/
theorem NoCollision.restrict {left right smallLeft smallRight : CommitmentTree}
    (clean : NoCollision left right) (first : Included smallLeft left)
    (second : Included smallRight right) : NoCollision smallLeft smallRight := by
  -- A collision inside the two subcomputations would also be a collision between the enclosing computations.
  rintro ⟨a, memberA, b, memberB, different, same⟩
  exact clean ⟨a, first a memberA, b, second b memberB, different, same⟩

/-- A collision-free equal parent pair has equal left children and equal right children. -/
theorem NoCollision.fork_roots {a b c d : CommitmentTree}
    (clean : NoCollision (.fork a b) (.fork c d))
    (first : (fork a b).Complete) (second : (fork c d).Complete)
    (same : (fork a b).root = (fork c d).root) : a.root = c.root ∧ b.root = d.root :=
  -- Two 32-byte children form an unambiguous 64-byte input, so a noncolliding equal parent preserves both.
  (fork_binding first second same).resolve_right clean

/-- Every leaf computation occurs in the expanded perfect tree above that position. -/
theorem perfectTrees_included (depth : Nat) (leaves : Nat → CommitmentTree)
    (i : Nat) (within : i < 2 ^ depth) : Included (leaves i) (perfectTrees depth leaves) := by
  -- Follow the selected position through successive equal-width halves of the perfect tree.
  induction depth generalizing leaves i with
  | zero =>
    obtain rfl : i = 0 := Nat.lt_one_iff.mp within
    exact Included.refl _
  | succ depth ih =>
    by_cases before : i < 2 ^ depth
    · exact (ih leaves i before).trans (Included.fork_left _ _)
    -- Positions in the right half are translated by subtracting the left half's width.
    · have shifted := ih (fun i => leaves (i + 2 ^ depth)) (i - 2 ^ depth)
        (by rw [Nat.pow_succ] at within; omega)
      simp only [Nat.sub_add_cancel (Nat.le_of_not_gt before)] at shifted
      exact shifted.trans (Included.fork_right _ _)

/-- Equal perfect-tree roots preserve each bottom root unless one of their hashes collides. -/
theorem perfectTrees_roots (depth : Nat) (left right : Nat → CommitmentTree)
    (first : (perfectTrees depth left).Complete)
    (second : (perfectTrees depth right).Complete)
    (clean : NoCollision (perfectTrees depth left) (perfectTrees depth right))
    (same : (perfectTrees depth left).root = (perfectTrees depth right).root) :
    ∀ i, i < 2 ^ depth → (left i).root = (right i).root := by
  -- Authenticate both child roots at every fork before descending toward the requested position.
  induction depth generalizing left right with
  | zero =>
    intro i within
    obtain rfl : i = 0 := Nat.lt_one_iff.mp within
    exact same
  | succ depth ih =>
    have both := clean.fork_roots first second same
    -- Every hash in a half-tree remains in its enclosing computation, so collision freedom descends.
    have leftClean := clean.restrict (Included.fork_left _ _) (Included.fork_left _ _)
    have rightClean := clean.restrict (Included.fork_right _ _) (Included.fork_right _ _)
    intro i within
    -- The half-width determines whether to keep the position or translate it into the right subtree.
    by_cases before : i < 2 ^ depth
    · exact ih left right first.1 second.1 leftClean both.1 i before
    · have shifted := ih (fun i => left (i + 2 ^ depth)) (fun i => right (i + 2 ^ depth))
        first.2 second.2 rightClean both.2 (i - 2 ^ depth)
        (by rw [Nat.pow_succ] at within; omega)
      simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt before)] using shifted

/-- A bounded tree commits to the root at every declared leaf position. -/
theorem bounded_roots (left right : Array CommitmentTree) (capacity : Nat)
    (first : (bounded left capacity).Complete)
    (second : (bounded right capacity).Complete)
    (clean : NoCollision (bounded left capacity) (bounded right capacity))
    (same : (bounded left capacity).root = (bounded right capacity).root) :
    ∀ i, i < capacity → (paddedTrees left i).root = (paddedTrees right i).root := by
  -- Every declared position lies within the rounded-up perfect-tree width.
  intro i within
  exact perfectTrees_roots _ _ _ first second clean same i
    (Nat.lt_of_lt_of_le within (le_two_pow_depthFor _))

/-- Every materialized leaf computation occurs in a bounded tree with sufficient capacity. -/
theorem bounded_included (trees : Array CommitmentTree) (capacity : Nat)
    (room : trees.size ≤ capacity) (i : Nat) (within : i < trees.size) :
    Included trees[i] (bounded trees capacity) := by
  -- A sufficient capacity puts every stored child inside the expanded perfect tree.
  have included := perfectTrees_included (depthFor capacity) (paddedTrees trees) i
    (Nat.lt_of_lt_of_le within (Nat.le_trans room (le_two_pow_depthFor _)))
  -- A stored position selects its child computation rather than the implicit zero padding.
  simpa only [bounded, paddedTrees, Array.getElem?_eq_getElem within, Option.getD_some] using included

/-- Each stored position occurs in its progressive computation, without a global capacity. -/
theorem progressive_included (trees : List CommitmentTree) (level i : Nat)
    (within : i < trees.length) : Included trees[i] (progressive trees level) := by
  -- Follow the same prefix-and-suffix decomposition as the progressive spine.
  induction trees, level using progressive.induct generalizing i with
  | case1 trees level empty =>
    -- An empty suffix contains no stored position, so the assumed position cannot lie here.
    obtain rfl := List.isEmpty_iff.mp empty
    simp at within
  | case2 trees level nonempty ih =>
    rw [progressive, ite_eq_right nonempty]
    -- Prefix capacities grow as 1, 4, 16, and so on, while later positions continue down the right spine.
    by_cases before : i < 4 ^ level
    · have member : i < (trees.take (4 ^ level)).toArray.size := by simp; omega
      -- A position in the current prefix occurs in its bounded left subtree and therefore in the whole fork.
      have included := bounded_included (trees.take (4 ^ level)).toArray (4 ^ level)
        (by simp only [List.size_toArray, List.length_take]; omega) i member
      simp only [List.getElem_toArray, List.getElem_take] at included
      exact included.trans (Included.fork_left _ _)
    -- A later position is translated past the current prefix before following the remaining spine.
    · have included := ih (i - 4 ^ level) (by simp; omega)
      simp only [List.getElem_drop, Nat.add_sub_cancel' (Nat.le_of_not_gt before)] at included
      exact included.trans (Included.fork_right _ _)

/-- Equal-length progressive trees preserve every stored root unless their hashes collide. -/
theorem progressive_roots (left right : List CommitmentTree) (level : Nat)
    (lengths : left.length = right.length)
    (first : (progressive left level).Complete)
    (second : (progressive right level).Complete)
    (clean : NoCollision (progressive left level) (progressive right level))
    (same : (progressive left level).root = (progressive right level).root) :
    ∀ i (within : i < left.length), left[i].root = right[i].root := by
  -- Equal leaf counts make both progressive spines end at the same level.
  induction left, level using progressive.induct generalizing right with
  | case1 left level empty =>
    obtain rfl := List.isEmpty_iff.mp empty
    simp
  | case2 left level nonempty ih =>
    -- If one suffix is nonempty, the equal count forces the other suffix to be nonempty too.
    have otherNonempty : ¬ right.isEmpty = true := by
      simp_all [List.isEmpty_iff, ← List.length_eq_zero_iff]
    rw [progressive.eq_def left level, ite_eq_right nonempty] at first clean same
    rw [progressive.eq_def right level, ite_eq_right otherNonempty] at second clean same
    -- The enclosing hash authenticates both the bounded prefix root and the remaining spine root.
    have both := clean.fork_roots first second same
    -- The collision-free assumption applies separately to each pair of subcomputations.
    have firstClean := clean.restrict (Included.fork_left _ _) (Included.fork_left _ _)
    have restClean := clean.restrict (Included.fork_right _ _) (Included.fork_right _ _)
    intro i within
    by_cases before : i < 4 ^ level
    -- Positions inside the current prefix are authenticated by its perfect-tree root.
    · have equal := bounded_roots _ _ _ first.1 second.1 firstClean both.1 i before
      have lbound : i < (left.take (4 ^ level)).toArray.size := by simp; omega
      have rbound : i < (right.take (4 ^ level)).toArray.size := by simp; omega
      simpa only [paddedTrees, Array.getElem?_eq_getElem lbound,
        Array.getElem?_eq_getElem rbound, Option.getD_some, List.getElem_toArray,
        List.getElem_take] using equal
    -- Later positions are authenticated recursively after removing the equal-sized prefixes.
    · have equal := ih (right.drop (4 ^ level)) (by simp [lengths]) first.2 second.2 restClean both.2
        (i - 4 ^ level) (by simp; omega)
      simpa only [List.getElem_drop, Nat.add_sub_cancel' (Nat.le_of_not_gt before)] using equal

/-- Every materialized position is committed by the selected layout tree. -/
theorem content_roots (left right : Array CommitmentTree) (limit : Option Nat)
    (lengths : left.size = right.size)
    (room : ∀ capacity, limit = some capacity → left.size ≤ capacity)
    (first : (content left limit).Complete) (second : (content right limit).Complete)
    (clean : NoCollision (content left limit) (content right limit))
    (same : (content left limit).root = (content right limit).root) :
    ∀ i (within : i < left.size), left[i].root = right[i].root := by
  -- Use the selected tree shape while preserving the common number of stored positions.
  cases limit with
  | none =>
    -- Equal counts align the two progressive spines from their first level.
    have equal := progressive_roots left.toList right.toList 0 (by simpa)
      first second clean same
    simpa only [Array.length_toList, Array.getElem_toList] using equal
  | some capacity =>
    intro i within
    -- The declared capacity includes the selected position in both bounded trees.
    have equal := bounded_roots left right capacity first second clean same i
      (Nat.lt_of_lt_of_le within (room capacity rfl))
    simpa only [paddedTrees, Array.getElem?_eq_getElem within,
      Array.getElem?_eq_getElem (show i < right.size by omega), Option.getD_some] using equal

/-- Each leaf's own hashes occur inside the selected layout tree. -/
theorem content_included (trees : Array CommitmentTree) (limit : Option Nat)
    (room : ∀ capacity, limit = some capacity → trees.size ≤ capacity)
    (i : Nat) (within : i < trees.size) : Included trees[i] (content trees limit) := by
  -- Both tree shapes retain every stored child computation when their capacity requirements hold.
  cases limit with
  | none => exact progressive_included trees.toList 0 i (by simpa)
  | some capacity => exact bounded_included trees capacity (room capacity rfl) i within

/-- A layout's mixing word is authenticated before its variable tree shape is inspected. -/
theorem withMixin_roots {left right : CommitmentTree} {a b : Bytes}
    (first : (left.withMixin (some a)).Complete)
    (second : (right.withMixin (some b)).Complete)
    (clean : NoCollision (left.withMixin (some a)) (right.withMixin (some b)))
    (same : (left.withMixin (some a)).root = (right.withMixin (some b)).root) :
    left.root = right.root ∧ a = b := clean.fork_roots first second same

/-- Hashes of the contents remain present after an optional mixing word is attached. -/
theorem withMixin_included (tree : CommitmentTree) (mixin : Option Bytes) :
    Included tree (tree.withMixin mixin) := by
  -- Attaching metadata either leaves the computation alone or places it under the left child.
  cases mixin with
  | none => exact Included.refl _
  | some word => exact Included.fork_left _ _

/-- Removing an optional mixing word preserves completeness of the contents. -/
theorem withMixin_complete {tree : CommitmentTree} {mixin : Option Bytes}
    (complete : (tree.withMixin mixin).Complete) : tree.Complete := by
  -- A complete final fork includes a complete contents subtree on its left.
  cases mixin with
  | none => exact complete
  | some word => exact complete.1

/-- Equal mixin presence authenticates the complete word and the contents separately. -/
theorem withMixin_comparison {left right : CommitmentTree} {a b : Option Bytes}
    (presence : a.isSome = b.isSome)
    (first : (left.withMixin a).Complete) (second : (right.withMixin b).Complete)
    (clean : NoCollision (left.withMixin a) (right.withMixin b))
    (same : (left.withMixin a).root = (right.withMixin b).root) :
    a = b ∧ left.root = right.root := by
  -- Equal metadata presence excludes comparing a mixed root with an unmixed root.
  cases a <;> cases b <;> simp at presence
  · exact ⟨rfl, same⟩
  -- With metadata on both sides, the final hash authenticates the contents root and the word separately.
  · have both := withMixin_roots first second clean same
    exact ⟨congrArg some both.2, both.1⟩

end EthLib.Serialization.Ssz.CommitmentTree
