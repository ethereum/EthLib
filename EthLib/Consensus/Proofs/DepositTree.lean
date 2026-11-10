module

public import EthLib.Consensus.DepositTree
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Transition.Genesis
public import EthLib.Serialization.Proofs.Ssz.Merkle.Tree
public import EthLib.Serialization.Proofs.Ssz.Typed.RootedList
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# Proofs: the deposit tree computes the SSZ deposit root

Pushing deposits one at a time builds the tree that holds them all from the left.

Its root is the SSZ root of the list of their data, which the chain votes on.

Finalization keeps the root, and a snapshot rebuilds a tree with the same later roots.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

namespace DepositMerkleTree

/-! ## The hashes are those of SSZ -/

/-- The parent of two nodes is the SSZ parent of their bytes. -/
@[simp] theorem toArray_hashPair (left right : Root) :
    (hashPair left right).toArray = combine left.toArray right.toArray :=
  rfl

/-- The root of an empty subtree is the SSZ root of the zero subtree of that height. -/
@[simp] theorem toArray_zeroNode (height : Nat) :
    (zeroNode height).toArray = zeroSubtree height := by
  induction height with
  | zero => rw [zeroSubtree_eq]; rfl
  | succ height ih =>
    rw [zeroNode, toArray_hashPair, ih, zeroSubtree_eq, zeroSubtree_eq]
    rfl

/-- A root with a count mixed in is the SSZ root with that length mixed in. -/
@[simp] theorem toArray_mixInCount (root : Root) (count : Nat) :
    (mixInCount root count).toArray = mixIn root.toArray (lengthWord count) :=
  rfl

/-! ## Pushing builds the tree of all leaves -/

/-- A subtree above the leaves with some leaves splits them between its two halves. -/
theorem create_succ_of_ne_nil {leaves : List Root} (nonempty : leaves ≠ []) (height : Nat) :
    create leaves (height + 1)
      = .node (create (leaves.take (min (2 ^ height) leaves.length)) height)
          (create (leaves.drop (min (2 ^ height) leaves.length)) height) := by
  cases leaves with
  | nil => exact absurd rfl nonempty
  | cons first rest => rfl

/-- The subtree of some leaves is full exactly when they fill all its leaves. -/
theorem isFull_create (leaves : List Root) (height : Nat) (fits : leaves.length ≤ 2 ^ height) :
    (create leaves height).isFull = decide (leaves.length = 2 ^ height) := by
  induction height generalizing leaves with
  | zero =>
    match leaves, fits with
    | [], _ => rfl
    | [_], _ => rfl
  | succ height ih =>
    by_cases empty : leaves = []
    · subst empty
      simp [create, isFull, Nat.ne_of_lt (Nat.two_pow_pos (height + 1))]
    · have nonempty := empty
      rw [create_succ_of_ne_nil nonempty, isFull, ih _ (by simp; omega)]
      simp only [List.length_drop, Nat.pow_succ] at fits ⊢
      grind

/-- Pushing into the subtree of some leaves gives the subtree of those leaves and one more. -/
theorem pushLeaf_create (leaf : Root) (leaves : List Root) (height : Nat)
    (room : leaves.length < 2 ^ height) :
    (create leaves height).pushLeaf leaf = some (create (leaves ++ [leaf]) height) := by
  induction height generalizing leaves with
  | zero =>
    match leaves, room with
    | [], _ => rfl
  | succ height ih =>
    by_cases empty : leaves = []
    · subst empty
      rfl
    · have more : leaves ++ [leaf] ≠ [] := by simp
      rw [create_succ_of_ne_nil empty, create_succ_of_ne_nil more, pushLeaf]
      simp only [Nat.pow_succ] at room
      by_cases half : leaves.length < 2 ^ height
      · rw [isFull_create _ _ (by simp; omega)]
        have split : min (2 ^ height) leaves.length = leaves.length := by omega
        have split' : min (2 ^ height) (leaves.length + 1) = leaves.length + 1 := by omega
        simp only [List.length_append, List.length_singleton, split, split']
        have whole : (leaves ++ [leaf]).take (leaves.length + 1) = leaves ++ [leaf] :=
          List.take_of_length_le (by simp)
        simp [Nat.ne_of_lt half, ih leaves half, whole]
      · rw [isFull_create _ _ (by simp; omega)]
        have split : min (2 ^ height) leaves.length = 2 ^ height := by omega
        have split' : min (2 ^ height) (leaves.length + 1) = 2 ^ height := by omega
        have rest : (leaves.drop (2 ^ height)).length < 2 ^ height := by simp; omega
        simp only [List.length_append, List.length_singleton, split, split']
        simp [split, ih _ rest, List.take_append_of_le_length (Nat.le_of_not_lt half),
          List.drop_append_of_le_length (Nat.le_of_not_lt half)]

/-- The root of the subtree of some leaves is the SSZ root of those leaves, padded with zeros. -/
theorem toArray_root_create (leaves : List Root) (height : Nat)
    (fits : leaves.length ≤ 2 ^ height) :
    (create leaves height).root.toArray
      = subtreeAt (leaves.map Vector.toArray).toArray height 0 := by
  induction height generalizing leaves with
  | zero =>
    match leaves, fits with
    | [], _ => simp [create, root, subtreeAt_leaf, zeroNode]; rfl
    | [_], _ => simp [create, root, subtreeAt_leaf]
  | succ height ih =>
    by_cases empty : leaves = []
    · subst empty
      simp [create, root, subtreeAt_past]
    · simp only [Nat.pow_succ] at fits
      rw [create_succ_of_ne_nil empty, root, toArray_hashPair, ih _ (by simp; omega),
        ih _ (by simp; omega), subtreeAt_split]
      congr 1
      · apply subtreeAt_congr
        intro i below
        simp only [Nat.zero_add, List.getElem?_toArray, List.getElem?_map, List.getElem?_take]
        grind
      · apply subtreeAt_congr
        intro i below
        simp only [Nat.zero_add, List.getElem?_toArray, List.getElem?_map, List.getElem?_drop]
        grind

/-- Finalization keeps the root of every subtree. -/
@[simp] theorem root_finalize (tree : DepositMerkleTree) (count height : Nat) :
    (tree.finalize count height).root = tree.root := by
  induction tree generalizing count height with
  | node left right ihl ihr =>
    cases height with
    | zero => rfl
    | succ height =>
      rw [finalize]
      split
      · rfl
      · simp only [root, ihl]
        split <;> simp [ihr]
  | _ => cases height <;> rfl

/-- Two halves of leaves, the right one empty unless the left one is full, make one subtree. -/
theorem root_create_append {left right : List Root} {height : Nat}
    (leftFits : left.length ≤ 2 ^ height) (rightFits : right.length ≤ 2 ^ height)
    (packed : right = [] ∨ left.length = 2 ^ height) :
    (create (left ++ right) (height + 1)).root
      = hashPair (create left height).root (create right height).root := by
  by_cases empty : left ++ right = []
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp empty
    simp [create, root, zeroNode]
  · have split : min (2 ^ height) (left ++ right).length = left.length := by
      rcases packed with rfl | full <;> simp <;> omega
    rw [create_succ_of_ne_nil empty, root, split]
    simp

/--
A sparse subtree of a height that stands for some leaves.

A finalized subtree keeps only the root of its leaves, and a zero subtree has none.

Its leaves fill from the left, so a right half has leaves only when the left half is full.
-/
inductive Holds : Nat → DepositMerkleTree → List Root → Prop where
  /-- An empty subtree holds no leaf. -/
  | zero (height : Nat) : Holds height (.zero height) []
  /-- A leaf holds itself. -/
  | leaf (hash : Root) : Holds 0 (.leaf hash) [hash]
  /-- A finalized subtree holds the leaves that fill it and give its root. -/
  | finalized {height : Nat} {leaves : List Root} (full : leaves.length = 2 ^ height) :
      Holds height (.finalized (2 ^ height) (create leaves height).root) leaves
  /-- A node holds the leaves of its left half, then those of its right half. -/
  | node {height : Nat} {left right : DepositMerkleTree} {leftLeaves rightLeaves : List Root} :
      Holds height left leftLeaves → Holds height right rightLeaves →
      (rightLeaves = [] ∨ leftLeaves.length = 2 ^ height) →
      Holds (height + 1) (.node left right) (leftLeaves ++ rightLeaves)

/-- The right half of a split of leaves is empty unless the left half is full. -/
theorem packed_split (leaves : List Root) (height : Nat) :
    leaves.drop (min (2 ^ height) leaves.length) = []
      ∨ (leaves.take (min (2 ^ height) leaves.length)).length = 2 ^ height := by
  by_cases short : leaves.length ≤ 2 ^ height
  · left
    simp
    omega
  · right
    simp
    omega

/-- The full subtree of some leaves holds them. -/
theorem holds_create (leaves : List Root) (height : Nat) (fits : leaves.length ≤ 2 ^ height) :
    Holds height (create leaves height) leaves := by
  induction height generalizing leaves with
  | zero =>
    match leaves, fits with
    | [], _ => exact .zero 0
    | [hash], _ => exact .leaf hash
  | succ height ih =>
    by_cases empty : leaves = []
    · subst empty
      exact .zero _
    · simp only [Nat.pow_succ] at fits
      have holds := Holds.node (ih _ (by simp; omega)) (ih _ (by simp; omega))
        (packed_split leaves height)
      rwa [List.take_append_drop, ← create_succ_of_ne_nil empty] at holds

namespace Holds

/-- A subtree holds at most as many leaves as its height leaves room for. -/
theorem length_le {height : Nat} {tree : DepositMerkleTree} {leaves : List Root}
    (holds : Holds height tree leaves) : leaves.length ≤ 2 ^ height := by
  induction holds with
  | zero => simp
  | leaf => simp
  | finalized full => omega
  | node _ _ packed ihl ihr =>
    simp only [List.length_append, Nat.pow_succ]
    rcases packed with rfl | full
    · simp only [List.length_nil, Nat.add_zero]
      omega
    · omega

/-- A subtree has the root of the full subtree of the leaves it holds. -/
theorem root_eq {height : Nat} {tree : DepositMerkleTree} {leaves : List Root}
    (holds : Holds height tree leaves) : tree.root = (create leaves height).root := by
  induction holds with
  | zero => simp [create, root]
  | leaf => rfl
  | finalized => rfl
  | node hl hr packed ihl ihr =>
    rw [root, ihl, ihr, root_create_append hl.length_le hr.length_le packed]

/-- A subtree is full exactly when it holds as many leaves as it has room for. -/
theorem isFull_eq {height : Nat} {tree : DepositMerkleTree} {leaves : List Root}
    (holds : Holds height tree leaves) : tree.isFull = decide (leaves.length = 2 ^ height) := by
  induction holds with
  | zero height => simp [isFull, Nat.ne_of_lt (Nat.two_pow_pos height)]
  | leaf => rfl
  | finalized full => simp [isFull, full]
  | @node h _ _ _ _ hl hr packed ihl ihr =>
    rw [isFull, ihr]
    have := hl.length_le
    have := hr.length_le
    simp only [List.length_append, Nat.pow_succ]
    rcases packed with rfl | full
    · have := Nat.two_pow_pos h
      simp only [List.length_nil, Nat.add_zero, decide_eq_decide]
      omega
    · simp [full]
      omega

/-- Pushing into a subtree with room holds one more leaf. -/
theorem pushLeaf {height : Nat} {tree : DepositMerkleTree} {leaves : List Root}
    (holds : Holds height tree leaves) (leaf : Root) (room : leaves.length < 2 ^ height) :
    ∃ pushed, tree.pushLeaf leaf = some pushed ∧ Holds height pushed (leaves ++ [leaf]) := by
  induction holds with
  | zero height =>
    exact ⟨_, rfl, holds_create _ _ (by simp; exact Nat.two_pow_pos height)⟩
  | leaf => simp at room
  | finalized full => omega
  | @node h left right leftLeaves rightLeaves hl hr packed ihl ihr =>
    have := hl.length_le
    have := hr.length_le
    simp only [List.length_append, Nat.pow_succ] at room
    rw [DepositMerkleTree.pushLeaf, hl.isFull_eq]
    by_cases full : leftLeaves.length = 2 ^ h
    · obtain ⟨pushed, pushes, holds⟩ := ihr (by omega)
      refine ⟨.node left pushed, by simp [full, pushes], ?_⟩
      rw [List.append_assoc]
      exact .node hl holds (.inr full)
    · obtain rfl : rightLeaves = [] := packed.resolve_right full
      obtain ⟨pushed, pushes, holds⟩ := ihl (by simp at room; omega)
      refine ⟨.node pushed right, by simp [full, pushes], ?_⟩
      simpa using Holds.node holds hr (.inl rfl)

end Holds

/-- The full subtree of some leaves has no finalized subtree. -/
@[simp] theorem getFinalized_create (leaves : List Root) (height : Nat) :
    (create leaves height).getFinalized = ([], 0) := by
  induction height generalizing leaves with
  | zero =>
    cases leaves <;> rfl
  | succ height ih =>
    by_cases empty : leaves = []
    · subst empty
      rfl
    · rw [create_succ_of_ne_nil empty]
      simp [getFinalized, ih]

/-- Finalizing all the leaves of a full subtree replaces it by its root. -/
theorem finalize_create_full (leaves : List Root) (height count : Nat)
    (full : leaves.length = 2 ^ height) (covers : 2 ^ height ≤ count) :
    (create leaves height).finalize count height
      = .finalized (2 ^ height) (create leaves height).root := by
  cases height with
  | zero =>
    match leaves, full with
    | [_], _ => rfl
  | succ height =>
    have empty : leaves ≠ [] := by
      intro empty
      subst empty
      have := Nat.two_pow_pos (height + 1)
      simp at full
      omega
    rw [create_succ_of_ne_nil empty, finalize, ite_eq_left covers]

/--
Finalizing the first deposits of a full subtree keeps its leaves and counts the finalized ones.

Its finalized roots rebuild a subtree that holds exactly the finalized leaves.
-/
theorem finalize_create (leaves : List Root) (height count : Nat)
    (fits : leaves.length ≤ 2 ^ height) (positive : 0 < count) (within : count ≤ leaves.length) :
    Holds height ((create leaves height).finalize count height) leaves
      ∧ ((create leaves height).finalize count height).getFinalized.2 = count
      ∧ ((create leaves height).finalize count height).getFinalized.1 ≠ []
      ∧ ∃ rebuilt,
          fromSnapshotParts ((create leaves height).finalize count height).getFinalized.1 count
            height = some rebuilt
          ∧ Holds height rebuilt (leaves.take count) := by
  induction height generalizing leaves count with
  | zero =>
    match leaves, fits with
    | [], _ =>
      simp at within
      omega
    | [hash], _ =>
      obtain rfl : count = 1 := by simp at within; omega
      have leaf : (create [hash] 0).finalize 1 0 = .finalized 1 hash := rfl
      rw [leaf]
      exact ⟨.finalized (leaves := [hash]) rfl, rfl, by simp [getFinalized],
        .finalized 1 hash, by simp [getFinalized, fromSnapshotParts],
        .finalized (leaves := [hash]) rfl⟩
  | succ height ih =>
    have empty : leaves ≠ [] := by
      intro empty
      subst empty
      simp at within
      omega
    have packed := packed_split leaves height
    simp only [Nat.pow_succ] at fits
    by_cases all : 2 ^ (height + 1) ≤ count
    · have whole : leaves.length = 2 ^ (height + 1) := by simp only [Nat.pow_succ] at all ⊢; omega
      obtain rfl : count = 2 ^ (height + 1) := by simp only [Nat.pow_succ] at all ⊢; omega
      rw [finalize_create_full leaves (height + 1) _ whole (Nat.le_refl _)]
      refine ⟨.finalized whole, rfl, by simp [getFinalized],
        .finalized (2 ^ (height + 1)) (create leaves (height + 1)).root,
        by simp [getFinalized, fromSnapshotParts], ?_⟩
      rw [List.take_of_length_le (by omega)]
      exact .finalized whole
    · have below : count < 2 ^ height * 2 := by rw [← Nat.pow_succ]; omega
      rw [create_succ_of_ne_nil empty, finalize, ite_eq_right all]
      dsimp only
      by_cases half : 2 ^ height < count
      · rw [ite_eq_left half]
        have split : min (2 ^ height) leaves.length = 2 ^ height := by omega
        rw [split] at packed ⊢
        have full : (leaves.take (2 ^ height)).length = 2 ^ height := by simp; omega
        rw [finalize_create_full _ _ _ full (Nat.le_of_lt half)]
        obtain ⟨holds, counted, nonempty, rebuilt, parts, rebuiltHolds⟩ :=
          ih (leaves.drop (2 ^ height)) (count - 2 ^ height) (by simp; omega) (by omega)
            (by simp; omega)
        have notAll : count ≠ 2 ^ (height + 1) := by rw [Nat.pow_succ]; omega
        have notPast : ¬2 ^ (height + 1) < count := by rw [Nat.pow_succ]; omega
        have notLeft : ¬count ≤ 2 ^ height := by omega
        refine ⟨?_, ?_, by simp [getFinalized],
          .node (.finalized (2 ^ height) (create (leaves.take (2 ^ height)) height).root) rebuilt,
          ?_, ?_⟩
        · have := Holds.node (.finalized full) holds (.inr full)
          rwa [List.take_append_drop] at this
        · simp [getFinalized, counted]
          omega
        · simp [getFinalized, fromSnapshotParts, notAll, notPast, notLeft, Nat.ne_of_gt positive,
            parts]
        · have := Holds.node (.finalized full) rebuiltHolds (.inr full)
          rwa [← List.take_add, Nat.add_sub_cancel' (Nat.le_of_lt half)] at this
      · rw [ite_eq_right half]
        have inLeft : count ≤ min (2 ^ height) leaves.length := by omega
        obtain ⟨holds, counted, nonempty, rebuilt, parts, rebuiltHolds⟩ :=
          ih (leaves.take (min (2 ^ height) leaves.length)) count (by simp; omega) positive
            (by simp; omega)
        obtain ⟨first, rest, listed⟩ := List.exists_cons_of_ne_nil nonempty
        have notAll : count ≠ 2 ^ (height + 1) := by rw [Nat.pow_succ]; omega
        have notPast : ¬2 ^ (height + 1) < count := by rw [Nat.pow_succ]; omega
        have inHalf : count ≤ 2 ^ height := by omega
        refine ⟨?_, ?_, by simp [getFinalized, nonempty], .node rebuilt (.zero height), ?_, ?_⟩
        · have := Holds.node holds (holds_create _ _ (by simp; omega)) packed
          rwa [List.take_append_drop] at this
        · simp [getFinalized, counted]
        · rw [listed] at parts
          simp [getFinalized, listed, fromSnapshotParts, notAll, notPast, inHalf,
            Nat.ne_of_gt positive, parts]
        · have := Holds.node rebuiltHolds (.zero height) (.inl rfl)
          simpa [List.take_take, Nat.min_eq_left inLeft] using this


end DepositMerkleTree

namespace DepositTreeSnapshot

open DepositMerkleTree

/-- The climb reads only the bits of the count at the levels it crosses. -/
theorem climbFinalized_congr {size other : Nat} (pending : List Root) (root : Root)
    (level levels : Nat)
    (same : ∀ i, level ≤ i → i < level + levels → size.testBit i = other.testBit i) :
    climbFinalized pending size root level levels
      = climbFinalized pending other root level levels := by
  induction levels generalizing pending root level with
  | zero => rfl
  | succ levels ih =>
    have next : ∀ i, level + 1 ≤ i → i < level + 1 + levels →
        size.testBit i = other.testBit i := fun i low high => same i (by omega) (by omega)
    simp only [climbFinalized, same level (Nat.le_refl _) (by omega)]
    split
    · split <;> simp [ih _ _ _ next]
    · exact ih _ _ _ next

/-- A climb that succeeds splits its roots between its lower levels and its upper levels. -/
theorem exists_of_climbFinalized_add {pending : List Root} {size : Nat} {root result : Root}
    {level levels more : Nat}
    (climbed : climbFinalized pending size root level (levels + more) = .ok result) :
    ∃ lower upper middle, pending = lower ++ upper
      ∧ climbFinalized lower size root level levels = .ok middle
      ∧ climbFinalized upper size middle (level + levels) more = .ok result := by
  induction levels generalizing pending root level with
  | zero => exact ⟨[], pending, root, rfl, rfl, by simpa using climbed⟩
  | succ levels ih =>
    rw [show levels + 1 + more = levels + more + 1 by omega] at climbed
    unfold climbFinalized at climbed
    split at climbed
    · rename_i bit
      match pending, climbed with
      | last :: earlier, climbed =>
        obtain ⟨lower, upper, middle, split, low, high⟩ := ih climbed
        refine ⟨last :: lower, upper, middle, by simp [split], ?_, ?_⟩
        · simp [climbFinalized, bit, low]
        · rwa [Nat.add_right_comm, Nat.add_assoc] at high
    · rename_i bit
      obtain ⟨lower, upper, middle, split, low, high⟩ := ih climbed
      refine ⟨lower, upper, middle, split, ?_, ?_⟩
      · simp [climbFinalized, bit, low]
      · rwa [Nat.add_right_comm, Nat.add_assoc] at high

end DepositTreeSnapshot

namespace DepositMerkleTree

open DepositTreeSnapshot

/--
A subtree rebuilt from finalized roots and a count below its capacity has the root of the climb.
-/
theorem root_fromSnapshotParts {roots : List Root} {count height : Nat}
    {tree : DepositMerkleTree} {result : Root} (below : count < 2 ^ height)
    (climbed : climbFinalized roots.reverse count (zeroNode 0) 0 height = .ok result)
    (parts : fromSnapshotParts roots count height = some tree) :
    tree.root = result := by
  induction height generalizing roots count tree result with
  | zero =>
    obtain rfl : count = 0 := by simpa using below
    cases roots with
    | nil =>
      simp only [fromSnapshotParts, Option.some.injEq] at parts
      subst parts
      simp only [List.reverse_nil, climbFinalized, List.isEmpty_nil, ite_true,
        Except.ok.injEq] at climbed
      rw [← climbed]
      rfl
    | cons first rest => simp [climbFinalized] at climbed
  | succ height ih =>
    obtain ⟨lower, upper, middle, split, low, high⟩ :=
      exists_of_climbFinalized_add (more := 1) climbed
    rw [Nat.zero_add] at high
    -- A count with no bit below the height rebuilds the empty subtree.
    have empty : ∀ {count : Nat} (rest : List Root), count < 2 ^ height →
        count % 2 ^ height = 0 → fromSnapshotParts rest count height = some (.zero height) := by
      intro count rest fits zero
      rw [Nat.mod_eq_of_lt fits] at zero
      subst zero
      cases rest <;> rw [fromSnapshotParts.eq_def] <;> simp
    by_cases bit : count.testBit height
    · match upper, high with
      | [last], high =>
        simp only [climbFinalized, bit, List.isEmpty_nil, ite_true, Except.ok.injEq] at high
        subst high
        obtain rfl : roots = last :: lower.reverse := by
          simpa using congrArg List.reverse split
        have atLeast := Nat.ge_two_pow_of_testBit bit
        have rem : count % 2 ^ height = count - 2 ^ height := by
          rw [Nat.mod_eq_sub_mod atLeast, Nat.mod_eq_of_lt (by rw [Nat.pow_succ] at below; omega)]
        have low' : climbFinalized lower.reverse.reverse (count % 2 ^ height) (zeroNode 0) 0 height
            = .ok middle := by
          rw [List.reverse_reverse, climbFinalized_congr]
          · exact low
          · intro i _ high
            simp [Nat.testBit_mod_two_pow, show i < height by omega]
        have notAll : count ≠ 2 ^ (height + 1) := Nat.ne_of_lt below
        have notPast : ¬2 ^ (height + 1) < count := Nat.not_lt_of_lt below
        have notZero : count ≠ 0 := by have := Nat.two_pow_pos height; omega
        simp only [fromSnapshotParts, notZero, notAll, notPast, ite_false] at parts
        by_cases exact : count = 2 ^ height
        · subst exact
          have whole : fromSnapshotParts (last :: lower.reverse) (2 ^ height) height
              = some (.finalized (2 ^ height) last) := by
            rw [fromSnapshotParts.eq_def]
            simp
          simp only [Nat.le_refl, ite_true, whole, Option.map_eq_map, Option.map_some,
            Option.some.injEq] at parts
          subst parts
          have := ih (Nat.mod_lt _ (Nat.two_pow_pos height)) low'
            (empty _ (Nat.mod_lt _ (Nat.two_pow_pos height)) (Nat.mod_mod _ _ ▸ by simp))
          simp [root, ← this]
        · simp only [show ¬count ≤ 2 ^ height by omega, ite_false, Option.map_eq_map,
            Option.map_eq_some_iff] at parts
          obtain ⟨right, rebuilt, rfl⟩ := parts
          rw [rem] at low'
          simp [root, ih (by omega) low' rebuilt]
      | [], high => simp [climbFinalized, bit] at high
      | _ :: _ :: _, high => simp [climbFinalized, bit] at high
    · have half : count < 2 ^ height := Nat.lt_of_not_le fun over =>
        bit (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt over below)
      cases upper with
      | cons _ _ => simp [climbFinalized, bit] at high
      | nil =>
      simp only [climbFinalized, bit, Bool.false_eq_true, List.isEmpty_nil, ite_true, ite_false,
        Except.ok.injEq] at high
      subst high
      rw [List.append_nil] at split
      rw [← split] at low
      have notAll : count ≠ 2 ^ (height + 1) := Nat.ne_of_lt below
      have notPast : ¬2 ^ (height + 1) < count := Nat.not_lt_of_lt below
      cases roots with
      | nil =>
        simp only [fromSnapshotParts, Option.some.injEq] at parts
        subst parts
        have := ih half low (by rw [fromSnapshotParts.eq_def])
        simp [root, zeroNode, ← this]
      | cons first rest =>
        by_cases zero : count = 0
        · simp only [fromSnapshotParts, zero, ite_true, Option.some.injEq] at parts
          subst parts
          subst zero
          have := ih half low (empty _ half (by simp))
          simp [root, zeroNode, ← this]
        · simp only [fromSnapshotParts, zero, notAll, notPast, Nat.le_of_lt half, ite_true,
            ite_false, Option.map_eq_map, Option.map_eq_some_iff] at parts
          obtain ⟨left, rebuilt, rfl⟩ := parts
          simp [root, ih half low rebuilt]

end DepositMerkleTree

namespace DepositTree

open DepositMerkleTree

/-- A tree has the deposit root of the leaves it holds, with their count mixed in. -/
theorem getRoot_eq {tree : DepositTree} {held : List Root}
    (holds : Holds DEPOSIT_CONTRACT_TREE_DEPTH.toNat tree.tree held)
    (counted : tree.mixInLength = held.length) :
    tree.getRoot = mixInCount (create held DEPOSIT_CONTRACT_TREE_DEPTH.toNat).root held.length := by
  rw [getRoot, holds.root_eq, counted]

/--
Pushing deposits into a tree gives the deposit root of all its leaves.

It refuses them when they are more than the deposit contract accepts.
-/
theorem map_getRoot_pushLeaves {tree : DepositTree} {held : List Root}
    (holds : Holds DEPOSIT_CONTRACT_TREE_DEPTH.toNat tree.tree held)
    (counted : tree.mixInLength = held.length)
    (room : held.length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1) (leaves : List Root) :
    (tree.pushLeaves leaves).map getRoot
      = if (held ++ leaves).length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1 then
          .ok (mixInCount (create (held ++ leaves) DEPOSIT_CONTRACT_TREE_DEPTH.toNat).root
            (held ++ leaves).length)
        else .error .treeFull := by
  induction leaves generalizing tree held with
  | nil =>
    simp only [List.append_nil, room, ite_true, ← getRoot_eq holds counted]
    rfl
  | cons leaf rest ih =>
    have := Nat.two_pow_pos DEPOSIT_CONTRACT_TREE_DEPTH.toNat
    rw [pushLeaves, List.foldlM_cons]
    by_cases full : 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1 ≤ tree.mixInLength
    · have over : ¬(held ++ leaf :: rest).length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1 := by
        simp
        omega
      rw [ite_eq_right over]
      simp [pushLeaf, full]
      rfl
    · obtain ⟨pushed, pushes, pushedHolds⟩ := holds.pushLeaf leaf (by omega)
      have step : tree.pushLeaf leaf
          = .ok { tree with tree := pushed, mixInLength := tree.mixInLength + 1 } := by
        simp [pushLeaf, full, pushes]
      rw [step]
      have := ih (tree := { tree with tree := pushed, mixInLength := tree.mixInLength + 1 })
        pushedHolds (by simp [counted]) (by simp; omega)
      simp only [pushLeaves, List.append_assoc, List.singleton_append] at this
      exact this

/--
Pushing up to `2^32 - 1` deposits into the empty tree succeeds.

The tree holds them all from the left, counts them, and has no finalized block.
-/
theorem pushLeaves_new (leaves : List Root)
    (bound : leaves.length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1) :
    DepositTree.new.pushLeaves leaves
      = .ok ⟨create leaves DEPOSIT_CONTRACT_TREE_DEPTH.toNat, leaves.length, none⟩ := by
  have := Nat.two_pow_pos DEPOSIT_CONTRACT_TREE_DEPTH.toNat
  suffices grows : ∀ held : List Root,
      (held ++ leaves).length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1 →
      pushLeaves ⟨create held DEPOSIT_CONTRACT_TREE_DEPTH.toNat, held.length, none⟩ leaves
        = .ok ⟨create (held ++ leaves) DEPOSIT_CONTRACT_TREE_DEPTH.toNat,
          (held ++ leaves).length, none⟩ from
    grows [] bound
  clear bound
  induction leaves with
  | nil =>
    intro held _
    simp
    rfl
  | cons leaf rest ih =>
    intro held fits
    simp only [List.length_append, List.length_cons] at fits
    have room : ¬2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1 ≤ held.length := by omega
    have step := pushLeaf_create leaf held DEPOSIT_CONTRACT_TREE_DEPTH.toNat (by omega)
    have next := ih (held ++ [leaf]) (by simp; omega)
    simp only [List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton] at next
    rw [pushLeaves, List.foldlM_cons]
    simp only [pushLeaf, room, step, ite_false]
    exact next.trans (by simp)

/-- Pushes into the empty tree that succeed build the full subtree of their leaves. -/
theorem new_pushLeaves_ok {leaves : List Root} {tree : DepositTree}
    (pushed : DepositTree.new.pushLeaves leaves = .ok tree) :
    leaves.length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1
      ∧ tree = ⟨create leaves DEPOSIT_CONTRACT_TREE_DEPTH.toNat, leaves.length, none⟩ := by
  by_cases bound : leaves.length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1
  · rw [pushLeaves_new leaves bound] at pushed
    cases pushed
    exact ⟨bound, rfl⟩
  · have refused := map_getRoot_pushLeaves (tree := DepositTree.new) (held := [])
      (.zero _) rfl (Nat.zero_le _) leaves
    rw [pushed, List.nil_append, ite_eq_right bound] at refused
    cases refused

/-- Elements whose roots are some roots have those roots as their leaves. -/
theorem map_toArray_of_mapM_hashTreeRoot {α : Type} [SszType α] [LawfulSszType α]
    {items : List α} {roots : List Root}
    (rooted : items.mapM SszType.hashTreeRoot = .ok roots) :
    roots.map Vector.toArray = items.map leafRoot := by
  induction items generalizing roots with
  | nil =>
    cases rooted
    rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at rooted
    split at rooted
    · cases rooted
    rename_i root itemRooted
    split at rooted
    · cases rooted
    rename_i others restRooted
    cases rooted
    have same := (SszType.hashTreeRoot_ok_iff.mp itemRooted)
    rw [← LawfulSszType.root_eq, root_eq_leafRoot, Except.ok.injEq] at same
    simp [ih restRooted, same]

/-- Every list of elements has a list of roots. -/
theorem exists_mapM_hashTreeRoot {α : Type} [SszType α] [LawfulSszType α] (items : List α) :
    ∃ roots, items.mapM SszType.hashTreeRoot = .ok roots := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons item rest ih =>
    obtain ⟨root, rooted⟩ := SszType.hashTreeRoot_total item
    obtain ⟨roots, restRooted⟩ := ih
    exact ⟨root :: roots, by simp [List.mapM_cons, rooted, restRooted]; rfl⟩

/--
After pushing the roots of some deposit data, the deposit root is the SSZ root of their list.

The list has the limit of the deposit contract, as in the deposit root of the chain.
-/
theorem hashTreeRoot_eq_getRoot_pushLeaves (deposits : Array DepositData)
    (bound : deposits.size ≤ DEPOSIT_CONTRACT_LIMIT) (roots : List Root)
    (rooted : deposits.toList.mapM SszType.hashTreeRoot = .ok roots)
    {tree : DepositTree} (pushed : DepositTree.new.pushLeaves roots = .ok tree) :
    SszType.hashTreeRoot (⟨deposits, bound⟩ : SszList DepositData DEPOSIT_CONTRACT_LIMIT)
      = .ok tree.getRoot := by
  obtain ⟨fits, rfl⟩ := new_pushLeaves_ok pushed
  have leaves := map_toArray_of_mapM_hashTreeRoot rooted
  have count : roots.length = deposits.size := by
    simpa using congrArg List.length leaves
  have width : roots.length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat :=
    Nat.le_trans fits (Nat.sub_le _ _)
  rw [SszType.hashTreeRoot_ok_iff]
  refine (hashTreeRoot_list_leafRoots (α := DepositData) rfl deposits bound).trans ?_
  rw [getRoot, toArray_mixInCount, toArray_root_create _ _ width, leaves, count,
    leafRoots_eq_map, DEPOSIT_CONTRACT_LIMIT, depthFor_pow]
  simp [← Array.toList_map]

/--
A finalization that succeeds counts at most the deposits of the tree, and at least those finalized.

The finalized roots and their count compute the root of the deposit data.

The tree keeps its count, prunes the finalized deposits and records the block.
-/
theorem finalize_ok {tree finalized : DepositTree} {eth1Data : Eth1Data} {height : UInt64}
    (done : tree.finalize eth1Data height = .ok finalized) :
    let count := eth1Data.depositCount.toNat
    let sparse :=
      if count = 0 then tree.tree else tree.tree.finalize count DEPOSIT_CONTRACT_TREE_DEPTH.toNat
    count ≤ tree.mixInLength ∧ tree.tree.getFinalized.2 ≤ count
      ∧ DepositTreeSnapshot.calculateRootOf sparse.getFinalized.1 sparse.getFinalized.2
        = .ok eth1Data.depositRoot
      ∧ finalized = { tree with
          tree := sparse
          finalizedExecutionBlock := some (eth1Data.blockHash, height) } := by
  simp only [DepositTree.finalize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    pure, Except.pure] at done
  split at done
  · cases done
  split at done
  · cases done
  split at done
  · cases done
  rename_i rooted
  split at done
  · cases done
  rename_i same
  cases done
  refine ⟨by omega, by omega, ?_, rfl⟩
  rw [rooted]
  simpa using same

/-- Finalization keeps the deposit root. -/
theorem getRoot_finalize {tree finalized : DepositTree} {eth1Data : Eth1Data} {height : UInt64}
    (done : tree.finalize eth1Data height = .ok finalized) :
    finalized.getRoot = tree.getRoot := by
  obtain ⟨-, -, -, rfl⟩ := finalize_ok done
  simp only [getRoot]
  split <;> simp

/--
A snapshot rebuilds a tree that agrees with the finalized tree on every later root.

The finalized tree holds some deposits and is finalized once.

The rebuilt tree takes the deposits after the finalized ones, then any further deposits.

Both trees then have the same deposit root, or both refuse the further deposits.
-/
theorem getRoot_fromSnapshot (leaves more : List Root) {tree finalized : DepositTree}
    {snapshot : DepositTreeSnapshot} {eth1Data : Eth1Data} {height : UInt64}
    (pushed : DepositTree.new.pushLeaves leaves = .ok tree)
    (done : tree.finalize eth1Data height = .ok finalized)
    (taken : finalized.getSnapshot = .ok snapshot) :
    ((DepositTree.fromSnapshot snapshot).bind fun rebuilt =>
        rebuilt.pushLeaves (leaves.drop eth1Data.depositCount.toNat ++ more)).map getRoot
      = (finalized.pushLeaves more).map getRoot := by
  obtain ⟨fits, rfl⟩ := new_pushLeaves_ok pushed
  obtain ⟨within, -, computed, rfl⟩ := finalize_ok done
  have countFits : eth1Data.depositCount.toNat ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1 :=
    Nat.le_trans within fits
  have leavesFit : leaves.length ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat :=
    Nat.le_trans fits (Nat.sub_le _ _)
  have key : ∀ sparse,
      sparse = (if eth1Data.depositCount.toNat = 0 then
          create leaves DEPOSIT_CONTRACT_TREE_DEPTH.toNat
        else (create leaves DEPOSIT_CONTRACT_TREE_DEPTH.toNat).finalize eth1Data.depositCount.toNat
          DEPOSIT_CONTRACT_TREE_DEPTH.toNat) →
      Holds DEPOSIT_CONTRACT_TREE_DEPTH.toNat sparse leaves
        ∧ sparse.getFinalized.2 = eth1Data.depositCount.toNat
        ∧ ∃ rebuilt, fromSnapshotParts sparse.getFinalized.1 eth1Data.depositCount.toNat
            DEPOSIT_CONTRACT_TREE_DEPTH.toNat = some rebuilt
          ∧ Holds DEPOSIT_CONTRACT_TREE_DEPTH.toNat rebuilt
            (leaves.take eth1Data.depositCount.toNat) := by
    intro sparse defined
    by_cases none : eth1Data.depositCount.toNat = 0
    · rw [ite_eq_left none] at defined
      subst defined
      rw [none, getFinalized_create]
      exact ⟨holds_create _ _ leavesFit, rfl, _, rfl, .zero _⟩
    · rw [ite_eq_right none] at defined
      subst defined
      obtain ⟨holds, counted, -, rest⟩ :=
        finalize_create leaves _ _ leavesFit (Nat.pos_of_ne_zero none) within
      exact ⟨holds, counted, rest⟩
  generalize defined : (if eth1Data.depositCount.toNat = 0 then _ else _) = sparse at computed taken
  obtain ⟨sparseHolds, counted, rebuilt, parts, rebuiltHolds⟩ := key sparse defined.symm
  rw [map_getRoot_pushLeaves (held := leaves) sparseHolds rfl fits]
  simp only [getSnapshot] at taken
  rw [counted] at computed
  generalize sparse.getFinalized = split at counted computed parts taken
  obtain ⟨roots, count⟩ := split
  simp only at counted computed parts taken
  subst counted
  simp only [DepositTreeSnapshot.fromTreeParts, bind, Except.bind, computed, pure,
    Except.pure] at taken
  split at taken
  · cases taken
    have exact : eth1Data.depositCount.toNat.toUInt64.toNat = eth1Data.depositCount.toNat := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt eth1Data.depositCount.toNat_lt]
    have below : eth1Data.depositCount.toNat ≤ leaves.length := within
    have rebuiltCount :
        eth1Data.depositCount.toNat = (leaves.take eth1Data.depositCount.toNat).length := by
      rw [List.length_take]
      omega
    simp only [fromSnapshot, DepositTreeSnapshot.calculateRoot, exact, computed, parts, bind,
      Except.bind, pure, Except.pure, ne_eq, not_true_eq_false, ite_false]
    rw [map_getRoot_pushLeaves (held := leaves.take eth1Data.depositCount.toNat) rebuiltHolds
      rebuiltCount (rebuiltCount ▸ countFits), ← List.append_assoc, List.take_append_drop]
  · cases taken

/--
Up to `2^32 - 1` deposit data push, and the deposit root is then the SSZ root of their list.
-/
theorem hashTreeRoot_eq_getRoot_new (deposits : Array DepositData)
    (bound : deposits.size ≤ 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1) :
    ∃ roots tree, deposits.toList.mapM SszType.hashTreeRoot = .ok roots ∧
      DepositTree.new.pushLeaves roots = .ok tree ∧
      SszType.hashTreeRoot
          (⟨deposits, Nat.le_trans bound (Nat.sub_le _ _)⟩ :
            SszList DepositData DEPOSIT_CONTRACT_LIMIT)
        = .ok tree.getRoot := by
  obtain ⟨roots, rooted⟩ := exists_mapM_hashTreeRoot deposits.toList
  have count : roots.length = deposits.size := by
    simpa using congrArg List.length (map_toArray_of_mapM_hashTreeRoot rooted)
  have pushed := pushLeaves_new roots (count ▸ bound)
  exact ⟨roots, _, rooted, pushed,
    hashTreeRoot_eq_getRoot_pushLeaves deposits _ roots rooted pushed⟩

/-- A tree rebuilt from a snapshot has the deposit root that the snapshot states. -/
theorem getRoot_fromSnapshot_eq {snapshot : DepositTreeSnapshot} {rebuilt : DepositTree}
    (built : DepositTree.fromSnapshot snapshot = .ok rebuilt) :
    rebuilt.getRoot = snapshot.depositRoot := by
  simp only [fromSnapshot, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure] at built
  split at built
  · cases built
  rename_i computed calculated
  simp only [DepositTreeSnapshot.calculateRoot, DepositTreeSnapshot.calculateRootOf, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at calculated
  split at calculated
  · cases calculated
  rename_i fits
  split at calculated
  · cases calculated
  rename_i result climbed
  cases calculated
  split at built
  · cases built
  rename_i same
  split at built
  · rename_i sparse parts
    cases built
    rw [getRoot, root_fromSnapshotParts (Nat.lt_of_not_le fits) climbed parts]
    exact (Decidable.of_not_not same).symm
  · cases built

end DepositTree

end EthLib.Consensus
