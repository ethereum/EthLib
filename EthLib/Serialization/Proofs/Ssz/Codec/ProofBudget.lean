import EthLib.Serialization.Proofs.Ssz.Codec.Proof
import EthLib.Serialization.Proofs.Ssz.Codec.RootLaws

/-! A value's type depth bounds every recursive descent of the Merkle walker. -/

namespace EthLib.Serialization.Ssz

private theorem boundedNode_budget_congr (layout : MerkleLayout) (left right : Nat)
    (chunks : ∀ start stop, layoutChunksAt left layout start stop =
      layoutChunksAt right layout start stop)
    (children : ∀ slots, layout.leaves = .nested slots →
      ∀ child inner, some (child, inner) ∈ slots → ∀ index,
        nodeRootAt left child inner index = nodeRootAt right child inner index)
    (index depth start capacity : Nat) :
    boundedNode left layout index depth start capacity =
      boundedNode right layout index depth start capacity := by
  -- Internal nodes hash the same interval, while deeper paths select the same child value.
  simp only [boundedNode]
  split
  · rw [chunks]
  · cases hl : layout.leaves with
    | packed data => rfl
    | nested slots =>
      dsimp only
      split
      · exact children slots hl _ _ (List.mem_of_getElem? ‹_›) _
      · rfl

private theorem progressiveNode_budget_congr (layout : MerkleLayout) (left right : Nat)
    (chunks : ∀ start stop, layoutChunksAt left layout start stop =
      layoutChunksAt right layout start stop)
    (children : ∀ slots, layout.leaves = .nested slots →
      ∀ child inner, some (child, inner) ∈ slots → ∀ index,
        nodeRootAt left child inner index = nodeRootAt right child inner index)
    (index depth start capacity : Nat) :
    progressiveNode left layout index depth start capacity =
      progressiveNode right layout index depth start capacity := by
  -- Spine traversal spends no type budget and selects the same bounded level or suffix.
  simp only [progressiveNode]
  cases walk : spineWalk layout.leaves.count index depth start capacity with
  | error e => rfl
  | ok stop =>
    simp only [Bind.bind, Except.bind]
    split
    · exact boundedNode_budget_congr layout left right chunks children _ _ _ _
    · rw [chunks]

/-- Every index has the same answer once the walk's budget covers the type depth. -/
theorem nodeRootAt_budget_eq (shape : Desc) (value : Value) (index left right : Nat)
    (leftEnough : shape.nesting ≤ left) (rightEnough : shape.nesting ≤ right) :
    nodeRootAt left shape value index = nodeRootAt right shape value index := by
  -- Only entering a nested value decreases the budget, and its type is strictly shallower.
  generalize depthEq : shape.nesting = depth
  induction depth using Nat.strongRecOn generalizing shape value index left right with
  | ind depth ih =>
    have positive : 0 < shape.nesting := by cases shape <;> simp [Desc.nesting]
    rcases left with _ | left; · omega
    rcases right with _ | right; · omega
    by_cases invalid : index < 1
    · simp [nodeRootAt, invalid, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    by_cases root : index = 1
    · simp [nodeRootAt, root]
    cases hl : merkleLayout shape value with
    | error e => simp [nodeRootAt, invalid, root, hl, Bind.bind, Except.bind]
    | ok layout =>
      -- Each retained leaf has the same root at both sufficient budgets, including sliced intervals.
      have chunks : ∀ start stop, layoutChunksAt left layout start stop =
          layoutChunksAt right layout start stop := fun start stop =>
        layoutChunksAt_budget_eq layout left right (fun slots nested child inner member => by
          have := merkleLayout_child_nesting shape value layout hl slots nested child inner member
          omega) start stop
      -- Every selected child has strictly smaller type depth, so the induction applies independently of its index.
      have children : ∀ slots, layout.leaves = .nested slots →
          ∀ child inner, some (child, inner) ∈ slots → ∀ at_,
            nodeRootAt left child inner at_ = nodeRootAt right child inner at_ := by
        intro slots nested child inner member at_
        have smaller := merkleLayout_child_nesting shape value layout hl
          slots nested child inner member
        exact ih child.nesting (by omega) child inner at_ left right
          (by omega) (by omega) rfl
      -- The same interval and child results cover both bounded trees and progressive spines.
      have bounded := boundedNode_budget_congr layout left right chunks children
      have progressive := progressiveNode_budget_congr layout left right chunks children
      simp only [nodeRootAt, show ¬index < 1 from invalid, root, ↓reduceIte,
        beq_iff_eq, hl, Bind.bind, Except.bind]
      cases hg : gindexLength index with
      | error e => rfl
      | ok full =>
        dsimp only
        cases layout.mixin <;> simp [bounded, progressive, Pure.pure, Except.pure]

/-- The public walk agrees with any budget covering the type's nesting depth. -/
theorem nodeRootAt_eq_nodeRoot (shape : Desc) (value : Value) (index budget : Nat)
    (enough : shape.nesting ≤ budget) :
    nodeRootAt budget shape value index = nodeRoot shape value index := by
  -- The public budget adds the index to the type depth, so it is always sufficient.
  exact nodeRootAt_budget_eq shape value index budget (shape.nesting + index) enough (by omega)

end EthLib.Serialization.Ssz
