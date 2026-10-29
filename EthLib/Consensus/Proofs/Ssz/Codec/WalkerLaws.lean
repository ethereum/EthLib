import EthLib.Consensus.Proofs.Ssz.Codec.ProgressiveClosure

/-! A successfully rooted value gives locally consistent reads throughout its nested Merkle tree. -/

namespace EthLib.Consensus.Ssz

private theorem assemble_closed
    (read : Nat → Except Err Bytes) (contents : Nat → Nat → Except Err Bytes)
    (word : Option Bytes) (root : Bytes)
    (rootRead : read 1 = .ok (match word with
      | none => root | some mixed => combine root mixed))
    (contentsRoot : ∀ index, contents index 0 = .ok root)
    (contentsClosed : ∀ index depth, 0 < depth → ∀ node, contents index depth = .ok node →
      ∃ parent sibling, contents (index / 2) (depth - 1) = .ok parent ∧
        contents (gindexSibling index) depth = .ok sibling ∧
        parent = if index % 2 = 0 then combine node sibling else combine sibling node)
    (reads : ∀ index, 2 ≤ index → read index = match word with
      | none => contents index (Nat.log2 index)
      | some mixed =>
        if gindexBit index (Nat.log2 index - 1) then
          if Nat.log2 index - 1 = 0 then .ok mixed else .error .pathIntoMixin
        else contents index (Nat.log2 index - 1)) : WalkerClosed read := by
  -- Parent and sibling indices preserve the leading path except at the single mixing boundary.
  intro index node named readNode
  have depth := levelOf_parent named
  change Nat.log2 index = Nat.log2 (index / 2) + 1 at depth
  have siblingDepth := levelOf_sibling named
  change Nat.log2 (gindexSibling index) = Nat.log2 index at siblingDepth
  -- A sibling shares the same parent and depth, so only the final child ordering changes.
  have siblingHalf := gindexSibling_half index
  have parentNamed : 1 ≤ index / 2 := by omega
  have siblingNamed : 2 ≤ gindexSibling index := by omega
  have current := reads index named
  rw [current] at readNode
  cases word with
  | none =>
    simp only at readNode rootRead reads
    obtain ⟨parent, sibling, parentRead, siblingRead, equation⟩ :=
      contentsClosed index (Nat.log2 index) (by omega) node readNode
    refine ⟨parent, sibling, ?_, ?_, equation⟩
    · by_cases atRoot : index / 2 = 1
      · have zero : Nat.log2 index - 1 = 0 := by rw [depth, atRoot]; rfl
        rw [zero, contentsRoot] at parentRead
        cases parentRead
        simpa [atRoot] using rootRead
      · rw [reads _ (by omega)]
        simpa only [depth, Nat.add_sub_cancel] using parentRead
    · rw [reads _ siblingNamed]
      simpa only [siblingDepth] using siblingRead
  | some mixed =>
    simp only at readNode rootRead reads
    by_cases boundary : Nat.log2 index - 1 = 0
    -- Immediately below a mixed root, the only possible indices are its contents at two and word at three.
    · have candidates : index = 2 ∨ index = 3 := by
        have bounds := gindexDepth_bounds (by omega : 1 ≤ index)
        have log : Nat.log2 index = 1 := by omega
        simp only [log] at bounds
        omega
      rcases candidates with rfl | rfl
      all_goals
        have two := reads 2 (by decide)
        have three := reads 3 (by decide)
        simp only [show Nat.log2 2 = 1 from rfl, show Nat.log2 3 = 1 from rfl,
          Nat.sub_self, show gindexBit 2 0 = false from rfl, show gindexBit 3 0 = true from rfl,
          Bool.false_eq_true, ↓reduceIte, contentsRoot, Except.ok.injEq] at readNode two three
        subst node
      · exact ⟨combine root mixed, mixed, rootRead, three, rfl⟩
      · exact ⟨combine root mixed, root, rootRead, two, rfl⟩
    · have positive : 0 < Nat.log2 index - 1 := by omega
      cases turn : gindexBit index (Nat.log2 index - 1) with
      | true => simp [turn, boundary] at readNode
      | false =>
        simp only [turn, Bool.false_eq_true, ↓reduceIte] at readNode
        obtain ⟨parent, sibling, parentRead, siblingRead, equation⟩ :=
          contentsClosed index (Nat.log2 index - 1) positive node readNode
        have parentDeep : 2 ≤ index / 2 := by
          by_cases small : index / 2 < 2
          · rw [show index / 2 = 1 by omega, show Nat.log2 1 = 0 from rfl] at depth
            omega
          · omega
        -- A parent still below the mixing boundary retains the contents’ initial left turn.
        have parentTurn : gindexBit (index / 2) (Nat.log2 (index / 2) - 1) = false := by
          have same := gindexBit_shift_top (by omega : 1 ≤ index)
            (by omega : 1 < Nat.log2 index)
          simpa only [Nat.shiftRight_eq_div_pow, Nat.pow_one] using same.trans turn
        have siblingTurn : gindexBit (gindexSibling index)
            (Nat.log2 (gindexSibling index) - 1) = false := by
          rw [siblingDepth, gindexBit_sibling_high index _ positive, turn]
        refine ⟨parent, sibling, ?_, ?_, equation⟩
        · rw [reads _ parentDeep]
          simp only [parentTurn, Bool.false_eq_true, ↓reduceIte]
          simpa only [depth, Nat.add_sub_cancel] using parentRead
        · rw [reads _ siblingNamed, siblingTurn]
          simpa only [Bool.false_eq_true, ↓reduceIte, siblingDepth] using siblingRead

/-- Every readable non-root node of a successfully rooted value authenticates to its parent. -/
theorem nodeRoot_closed (shape : Desc) (value : Value) (root : Bytes)
    (rooted : hashTreeRoot shape value = .ok root) : WalkerClosed (nodeRoot shape value) := by
  -- Successful materialization supplies child roots, allowing induction through every nested type.
  generalize depthEq : shape.nesting = depth
  induction depth using Nat.strongRecOn generalizing shape value root with
  | ind depth ih =>
    obtain ⟨layout, chunks, tree, laid, materialized, treeRoot, rootEq⟩ :=
      hashTreeRoot_materializes shape value root rooted
    let budget := shape.nesting - 1
    change layoutChunksAt budget layout = .ok chunks at materialized
    have positive : 0 < shape.nesting := by cases shape <;> simp [Desc.nesting]
    -- Whole-value root success gives each present child a successful root and a strictly smaller type depth.
    have children : ∀ slots, layout.leaves = .nested slots → ∀ child inner,
        some (child, inner) ∈ slots → child.nesting ≤ budget ∧ WalkerClosed (nodeRoot child inner) := by
      intro slots nested child inner member
      have smaller := merkleLayout_child_nesting shape value layout laid slots nested child inner member
      have enough : child.nesting ≤ budget := by dsimp [budget]; omega
      obtain ⟨childRoot, childRooted⟩ :=
        layoutChunksAt_child_root budget layout chunks materialized slots nested child inner member
      rw [hashTreeRootAt_eq_hashTreeRoot child inner budget enough] at childRooted
      exact ⟨enough, ih child.nesting (by omega) child inner childRoot childRooted rfl⟩
    let contents (index turns : Nat) : Except Err Bytes := match layout.limit with
      | some capacity => boundedNode budget layout index turns 0 capacity
      | none => progressiveNode budget layout index turns 0 1
    -- At zero remaining turns, either tree shape returns the same materialized contents root.
    have contentsRoot : ∀ index, contents index 0 = .ok tree := by
      intro index
      cases limit : layout.limit with
      | none =>
        simp only [limit, Except.ok.injEq] at treeRoot
        simp [contents, limit, progressiveNode_zero, materialized, treeRoot,
          merkleizeProgressiveFrom, show Nat.log2 1 = 0 from rfl, budget, Bind.bind, Except.bind, Pure.pure, Except.pure]
      | some capacity =>
        simp only [limit, merkleizeBoundedUnchecked] at treeRoot
        split at treeRoot <;>
          simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at treeRoot
        have read := boundedNode_window
          (layoutChunksAt_window budget layout chunks materialized) index 0 0 capacity (by omega)
        simp only [boundedTreeNode, Nat.sub_zero, gindexBelow, Nat.pow_zero, Nat.mod_one,
          Nat.zero_mul, Nat.zero_add] at read
        simpa only [contents, limit, treeRoot] using read
    -- The local contents equations are combined with the single optional mixing-word boundary.
    apply assemble_closed (nodeRoot shape value) contents layout.mixin tree
    · rw [nodeRoot_root, rooted, rootEq]
      cases layout.mixin <;> rfl
    · exact contentsRoot
    · intro index turns positiveTurns node read
      cases limit : layout.limit with
      | some capacity =>
        simp only [contents, limit] at read ⊢
        exact boundedNode_closed layout budget chunks materialized children index turns 0 capacity
          positiveTurns node read
      | none =>
        simp only [contents, limit] at read ⊢
        exact progressiveNode_closed layout budget chunks materialized children index turns 0 0
          positiveTurns node read
    · intro index named
      have notRoot : index ≠ 1 := by omega
      have logarithm : Nat.log2 index ≠ 0 := by
        have parent := levelOf_parent named
        change Nat.log2 index = _ at parent
        omega
      rw [← nodeRootAt_eq_nodeRoot shape value index (budget + 1) (by dsimp [budget]; omega)]
      simp only [nodeRootAt, show ¬index < 1 by omega, ↓reduceIte, beq_iff_eq, notRoot,
        laid, Bind.bind, Except.bind, gindexLength, gindexDepth]
      simp only [↓reduceIte, logarithm]
      cases layout.mixin <;> simp [contents, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] <;> cases layout.limit <;> rfl

end EthLib.Consensus.Ssz
