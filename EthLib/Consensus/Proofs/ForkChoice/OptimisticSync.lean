module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.ForkChoice.OptimisticSync
public import EthLib.Consensus.Proofs.ForkChoice.Optimistic

/-!
# Proofs: optimistic sync

A block passes the optimistic check exactly when its parent carries a payload or it is old enough.

It is old enough when its slot is far enough before the clock.

The latest verified ancestor of a block is reached through optimistic blocks only.

It is not optimistic, or its parent root is zero.

A valid payload removes exactly the block and its known ancestors from the optimistic set.

The first invalid block removes exactly the optimistic roots whose chain holds it.

A tree filtered from a node is empty exactly when no viable leaf is reached from that node.

So the second case of an optimistic node holds exactly when the filtered tree has no viable leaf.

A node whose head is optimistic is an optimistic node.

Otherwise, before Gloas, it needs a dropped block at or above the justified block.

An optimistic validator may not sign exactly under seven domain types.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- Before Bellatrix, no block carries a payload. -/
theorem isExecutionBlock_of_lt_bellatrix (before : fork < .bellatrix)
    (block : BeaconBlock preset fork) : isExecutionBlock block = false := by
  have outside : ¬(.bellatrix ≤ fork ∧ fork < .glamsterdam) :=
    fun range => absurd range.1 (Nat.not_le_of_lt before)
  simp only [isExecutionBlock, outside, ↓reduceDIte]

/-- A block may be imported optimistically exactly when its known parent allows it.

The parent carries a payload, or the slot of the block is far enough before the clock.

The sum of the slot and the number of slots is computed only for a parent without a payload. -/
theorem OptimisticStore.isOptimisticCandidateBlock_eq_ok_iff {store : OptimisticStore preset fork}
    {currentSlot safeSlots : Slot} {block : BeaconBlock preset fork} {answer : Bool} :
    store.isOptimisticCandidateBlock currentSlot block safeSlots = .ok answer ↔
      ∃ parent, store.blocks[block.parentRoot]? = some parent ∧
        ((isExecutionBlock parent = true ∧ answer = true) ∨
          (isExecutionBlock parent = false ∧ ∃ enough,
            Uint64.addChecked block.slot safeSlots = .ok enough ∧
              answer = decide (enough ≤ currentSlot))) := by
  unfold isOptimisticCandidateBlock
  cases found : store.blocks[block.parentRoot]? with
  | none =>
    simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff, not_exists,
      not_and]
    exact fun _ none => absurd none (by simp)
  | some parent =>
    simp only [Option.some.injEq, exists_eq_left']
    cases execution : isExecutionBlock parent with
    | true =>
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, true_and, Bool.true_eq_false,
        false_and, or_false]
      exact eq_comm
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, false_and, true_and, false_or]
      cases sum : Uint64.addChecked block.slot safeSlots with
      | error e =>
        simp only [Except.mapError, bind, Except.bind, reduceCtorEq, false_iff, not_exists,
          not_and]
        exact fun _ none => absurd none (by simp)
      | ok enough =>
        simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          exists_eq_left']
        exact eq_comm

namespace OptimisticStore

variable (store : OptimisticStore preset fork)

/-- The roots that a walk of optimistic blocks reaches from a block, each step to the parent.

A step leaves an optimistic block whose parent root is not zero. -/
inductive OptimisticWalk : Root → Root → Prop where
  /-- The walk may stop at once. -/
  | here (root : Root) : OptimisticWalk root root
  /-- The walk may go from an optimistic block to its parent. -/
  | parent {root last : Root} {block : BeaconBlock preset fork}
      (found : store.blocks[root]? = some block) (optimistic : store.isOptimistic root = true)
      (notGenesis : block.parentRoot ≠ Vector.replicate 32 0)
      (rest : OptimisticWalk block.parentRoot last) : OptimisticWalk root last

/-- The latest verified ancestor is reached through optimistic blocks.

It is known, and it is not optimistic or its parent root is zero. -/
theorem latestVerifiedAncestor_spec {root ancestor : Root}
    (found : store.latestVerifiedAncestor root = .ok ancestor) :
    store.OptimisticWalk root ancestor ∧ ∃ block, store.blocks[ancestor]? = some block ∧
      (store.isOptimistic ancestor = false ∨ block.parentRoot = Vector.replicate 32 0) := by
  induction root using latestVerifiedAncestor.induct (store := store) with
  | case1 root unknown =>
    rw [latestVerifiedAncestor, unknown] at found
    simp [throw, throwThe, MonadExceptOf.throw] at found
  | case2 root block known stops =>
    rw [latestVerifiedAncestor, known] at found
    simp only [stops, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at found
    subst found
    refine ⟨.here _, block, known, ?_⟩
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at stops
    exact stops
  | case3 root block known goes unknown =>
    rw [latestVerifiedAncestor, known] at found
    simp only [goes, Bool.false_eq_true, ↓reduceIte] at found
    split at found
    · simp [throw, throwThe, MonadExceptOf.throw] at found
    · simp_all
  | case4 root block known goes parent parentFound lower ih =>
    rw [latestVerifiedAncestor, known] at found
    simp only [goes, Bool.false_eq_true, ↓reduceIte] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [parentFound, Option.some.injEq] at otherFound
      subst otherFound
      simp only [lower, ↓reduceDIte] at found
      obtain ⟨walk, rest⟩ := ih found
      simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq,
        not_or, Bool.not_eq_false] at goes
      exact ⟨.parent known goes.1 goes.2 walk, rest⟩
  | case5 root block known goes parent parentFound notLower =>
    rw [latestVerifiedAncestor, known] at found
    simp only [goes, Bool.false_eq_true, ↓reduceIte] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [parentFound, Option.some.injEq] at otherFound
      subst otherFound
      simp only [notLower, ↓reduceDIte] at found
      simp [throw, throwThe, MonadExceptOf.throw] at found

/-- A valid payload removes exactly the block and its known ancestors from the optimistic set.

The head and the blocks stay as they were. -/
theorem onValidPayload_spec {root : Root} {after : OptimisticStore preset fork}
    (updated : store.onValidPayload root = .ok after) :
    ∃ ancestors, store.chain root = .ok ancestors ∧
      (∀ optimistic, optimistic ∈ after.optimisticRoots ↔
        optimistic ∈ store.optimisticRoots ∧ optimistic ∉ ancestors) ∧
      after.headBlockRoot = store.headBlockRoot ∧ after.blocks = store.blocks := by
  simp only [onValidPayload, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at updated
  obtain ⟨ancestors, chained, rfl⟩ := updated
  refine ⟨ancestors, chained, fun optimistic => ?_, rfl, rfl⟩
  simp

/-- The first invalid block removes exactly the optimistic roots whose chain holds it.

Those are the first invalid block and its known descendants.

Every other root stays, and so do the head and the blocks. -/
theorem onInvalidatedPayload_spec {first : Root} {after : OptimisticStore preset fork}
    (updated : store.onInvalidatedPayload first = .ok after) :
    (∀ optimistic, optimistic ∈ after.optimisticRoots ↔
      optimistic ∈ store.optimisticRoots ∧
        ∃ chain, store.chain optimistic = .ok chain ∧ first ∉ chain) ∧
      after.headBlockRoot = store.headBlockRoot ∧ after.blocks = store.blocks := by
  simp only [onInvalidatedPayload, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at updated
  obtain ⟨kept, keptOk, rfl⟩ := updated
  refine ⟨fun optimistic => ?_, rfl, rfl⟩
  rw [mem_filterMapM_ok keptOk]
  constructor
  · rintro ⟨root, member, checked⟩
    cases chained : store.chain root with
    | error => simp [chained, bind, Except.bind] at checked
    | ok chain =>
      by_cases holds : first ∈ chain
      · simp [chained, holds, bind, Except.bind] at checked
      · simp only [chained, holds, bind, Except.bind, List.contains_iff_mem, ↓reduceIte,
          Except.ok.injEq, Option.some.injEq] at checked
        subst checked
        exact ⟨member, chain, chained, holds⟩
  · rintro ⟨member, chain, chained, holds⟩
    refine ⟨optimistic, member, ?_⟩
    simp [chained, holds, bind, Except.bind]

end OptimisticStore

namespace Store

variable {config : Config} {store : Store preset fork}

variable (config store) in
/-- A leaf that agrees with the checkpoints, reached from a node through children. -/
inductive ViableLeafAbove : ForkChoiceNode → ForkChoiceNode → Prop where
  /-- A node without children that agrees with the checkpoints is its own viable leaf. -/
  | leaf {node : ForkChoiceNode} : store.getNodeChildren node = .ok [] →
      store.isViableLeaf config node = .ok true → ViableLeafAbove node node
  /-- A viable leaf of a child is a viable leaf of its parent. -/
  | child {node child leaf : ForkChoiceNode} {children : List ForkChoiceNode} :
      store.getNodeChildren node = .ok children → child ∈ children →
      ViableLeafAbove child leaf → ViableLeafAbove node leaf

/-- A tree filtered from a node is non-empty exactly when a viable leaf is reached from it. -/
private theorem filterNodeTree_ne_nil_iff :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes →
      (nodes ≠ [] ↔ ∃ leaf, store.ViableLeafAbove config node leaf) := by
  intro node
  induction hrank : store.nodeRank node using Nat.strong_induction_on generalizing node with
  | _ rank ih =>
  intro nodes walk
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  by_cases empty : children.isEmpty
  · have nil : children = [] := List.isEmpty_iff.mp empty
    subst nil
    simp only [empty, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨isViable, viableOk, rfl⟩ := walk
    constructor
    · intro ne
      cases isViable
      · exact absurd rfl ne
      · exact ⟨node, .leaf childrenOk viableOk⟩
    · rintro ⟨leaf, reach⟩
      cases reach with
      | leaf _ ok =>
        rw [viableOk, Except.ok.injEq] at ok
        subst ok
        simp
      | child ok mem _ =>
        rw [childrenOk, Except.ok.injEq] at ok
        subst ok
        cases mem
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at walk
  obtain ⟨viable, viableOk, rfl⟩ := walk
  have below_iff : ∀ child ∈ children, ∀ below,
      store.nodeRank child < store.nodeRank node → store.filterNodeTree config child = .ok below →
        (below ≠ [] ↔ ∃ leaf, store.ViableLeafAbove config child leaf) :=
    fun child _ below lower belowOk => ih _ (hrank ▸ lower) rfl belowOk
  constructor
  · intro ne
    have ne' : viable ≠ [] := fun h => ne (by simp [h])
    obtain ⟨y, yMem⟩ := List.exists_mem_of_ne_nil _ ne'
    obtain ⟨child, childMem, below, belowOk, yBelow⟩ := (mem_of_flatMapM_ok viableOk y).mp yMem
    split at belowOk
    · rename_i lower
      obtain ⟨leaf, reach⟩ := (below_iff child childMem below lower belowOk).mp
        (List.ne_nil_of_mem yBelow)
      exact ⟨leaf, .child childrenOk childMem reach⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  · rintro ⟨leaf, reach⟩
    cases reach with
    | leaf nil _ =>
      rw [childrenOk, Except.ok.injEq] at nil
      subst nil
      simp at empty
    | child ok childMem reach =>
      rw [childrenOk, Except.ok.injEq] at ok
      subst ok
      obtain ⟨below, belowOk⟩ := flatMapM_ok_of_mem viableOk _ childMem
      split at belowOk
      · rename_i lower
        have nonempty := (below_iff _ childMem below lower belowOk).mpr ⟨leaf, reach⟩
        obtain ⟨y, yBelow⟩ := List.exists_mem_of_ne_nil _ nonempty
        have yMem := (mem_of_flatMapM_ok viableOk y).mpr
          ⟨_, childMem, below, by simp [lower, belowOk], yBelow⟩
        have ne' : viable ≠ [] := List.ne_nil_of_mem yMem
        simp [ne']
      · simp [throw, throwThe, MonadExceptOf.throw] at belowOk

/-- A tree filtered from a node is empty exactly when no viable leaf is reached from it. -/
theorem filterNodeTree_eq_nil_iff {node : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (tree : store.filterNodeTree config node = .ok nodes) :
    nodes = [] ↔ ¬∃ leaf, store.ViableLeafAbove config node leaf := by
  rw [← filterNodeTree_ne_nil_iff tree]
  exact not_not.symm

/-- When the justified block was dropped, the tree has no viable branch. -/
theorem hasNoViableBranch_of_not_contains
    (dropped : store.blocks.contains store.justifiedCheckpoint.root = false) :
    store.hasNoViableBranch config = .ok true := by
  simp [hasNoViableBranch, dropped]
  rfl

/-- With the justified block known, the second case holds exactly when no viable leaf is reached.

The leaves are reached from the justified block, and the filter of the tree must succeed. -/
theorem hasNoViableBranch_eq_ok_true_iff
    (known : store.blocks.contains store.justifiedCheckpoint.root = true)
    {nodes : List ForkChoiceNode} (tree : store.getFilteredNodeTree config = .ok nodes) :
    store.hasNoViableBranch config = .ok true ↔
      ¬∃ leaf, store.ViableLeafAbove config ⟨store.justifiedCheckpoint.root, .pending⟩ leaf := by
  rw [← filterNodeTree_eq_nil_iff tree]
  simp [hasNoViableBranch, known, tree, bind, Except.bind, pure, Except.pure]

end Store

/-- A node whose head is optimistic is an optimistic node, whatever its block tree. -/
theorem isOptimisticNode_of_isHeadOptimistic {config : Config}
    {optimistic : OptimisticStore preset fork} (store : Store preset fork)
    (head : optimistic.isHeadOptimistic = true) :
    isOptimisticNode config optimistic store = .ok true := by
  simp [isOptimisticNode, head]
  rfl

/-- Before Gloas, a node whose head is not optimistic is optimistic exactly in the second case.

That case needs a dropped block at or above the justified block, then no viable branch. -/
theorem isOptimisticNode_of_not_isHeadOptimistic {config : Config}
    {optimistic : OptimisticStore preset fork} (store : Store preset fork)
    (head : optimistic.isHeadOptimistic = false) (before : fork < .glamsterdam)
    {dropped : Bool} (found : optimistic.invalidatedAbove store = .ok dropped) :
    isOptimisticNode config optimistic store =
      if dropped then store.hasNoViableBranch config else .ok false := by
  have notGloas : ¬(Fork.glamsterdam ≤ fork) := Nat.not_le_of_lt before
  cases dropped
  · simp [isOptimisticNode, head, notGloas, found, bind, Except.bind]
    rfl
  · simp [isOptimisticNode, head, notGloas, found, bind, Except.bind]

/-- An optimistic validator may not sign exactly under the seven domain types of the rule.

They are those of a block, an attestation, a selection proof and an aggregate and proof.

They are also those of a sync committee message, its selection proof and a contribution. -/
theorem isOptimisticRestrictedDomain_iff (domainType : DomainType) :
    isOptimisticRestrictedDomain domainType = true ↔
      domainType = DOMAIN_BEACON_PROPOSER ∨ domainType = DOMAIN_BEACON_ATTESTER ∨
        domainType = DOMAIN_SELECTION_PROOF ∨ domainType = DOMAIN_AGGREGATE_AND_PROOF ∨
        domainType = DOMAIN_SYNC_COMMITTEE ∨ domainType = DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF ∨
        domainType = DOMAIN_CONTRIBUTION_AND_PROOF := by
  simp [isOptimisticRestrictedDomain]

end EthLib.Consensus
