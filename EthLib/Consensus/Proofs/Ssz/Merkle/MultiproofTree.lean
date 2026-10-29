import EthLib.Consensus.Proofs.Ssz.Merkle.CommitmentTree
import EthLib.Consensus.Proofs.Ssz.Merkle.Multiproof

/-! A multiproof reconstructs the finite tree whose leaves are its supplied frontier. -/

namespace EthLib.Consensus.Ssz

/-- No supplied node lies strictly above another supplied node. -/
def ProofAntichain (nodes : List (Nat × Bytes)) : Prop :=
  -- Climbing from one supplied position to another may only reach the same position.
  ∀ i ∈ nodes.map Prod.fst, ∀ j ∈ nodes.map Prod.fst, ∀ step, i >>> step = j → i = j

/-- Expand missing parents while stopping at the nodes supplied by the proof. -/
def proofTree (nodes : List (Nat × Bytes)) : Nat → Nat → CommitmentTree
  | 0, index => .leaf ((nodeAt nodes index).getD zeroChunk)
  | height + 1, index =>
    -- Supplied nodes end expansion, while missing parents join their two reconstructed children.
    match nodeAt nodes index with
    | some value => .leaf value
    | none => .fork (proofTree nodes height (2 * index))
        (proofTree nodes height (2 * index + 1))

/-- The node reading induced by the finite reconstruction tree. -/
def proofTreeNode (source : List (Nat × Bytes)) (height index : Nat) : Bytes :=
  -- The global height minus the index depth is exactly the subtree height still to reconstruct.
  (proofTree source (height - levelOf index) index).root

/-- A supplied node is a leaf of the rebuilt tree, however much height is left below it. -/
theorem proofTree_supplied (source : List (Nat × Bytes)) (height index : Nat)
    {value : Bytes} (found : nodeAt source index = some value) :
    proofTree source height index = .leaf value := by
  -- A supplied node ends reconstruction immediately at every remaining height.
  cases height <;> simp [proofTree, found]

/-- A node above a live frontier entry cannot also be an originally supplied leaf. -/
theorem source_parent_absent {source : List (Nat × Bytes)}
    (separated : ProofAntichain source) {index : Nat}
    (supported : ∃ original ∈ source.map Prod.fst, ∃ step, original >>> step = index)
    (positive : 2 ≤ index) : nodeAt source (gindexParent index) = none := by
  -- A supplied parent would be a strict ancestor of the supplied node supporting this entry.
  cases found : nodeAt source (gindexParent index) with
  | none => rfl
  | some value =>
    obtain ⟨original, member, step, descended⟩ := supported
    have parentMember := nodeAt_member found
    have named : gindexParent index ∈ source.map Prod.fst :=
      List.mem_map.mpr ⟨_, parentMember, rfl⟩
    have ancestral : original >>> (step + 1) = gindexParent index := by
      rw [shiftRight_succ, descended]
      rfl
    have same := separated original member _ named _ ancestral
    have bounded := shiftRight_le original step
    unfold gindexParent at same
    omega

/-- An unsupplied parent is precisely the fork of its two reconstruction subtrees. -/
theorem proofTree_parent {source : List (Nat × Bytes)} {height index : Nat}
    (positive : 2 ≤ index) (bounded : levelOf index ≤ height) (even : index % 2 = 0)
    (absent : nodeAt source (gindexParent index) = none) :
    proofTree source (height - levelOf (gindexParent index)) (gindexParent index) =
      .fork (proofTree source (height - levelOf index) index)
        (proofTree source (height - levelOf (index + 1)) (index + 1)) := by
  -- Siblings have equal depths, with exactly one more remaining level at their parent.
  have parentDepth := levelOf_parent positive
  have siblingDepth : levelOf (index + 1) = levelOf index := by
    have pair := gindexSibling_even even
    have sibling : gindexSibling index = index + 1 := by omega
    rw [← sibling]
    exact levelOf_sibling positive
  have budget : height - levelOf (gindexParent index) = height - levelOf index + 1 := by
    change levelOf index = levelOf (gindexParent index) + 1 at parentDepth
    omega
  -- The absent parent expands to precisely these left and right child positions.
  have left : 2 * gindexParent index = index := by unfold gindexParent; omega
  simp only [budget, proofTree, absent, left, siblingDepth]

private theorem proofTreeNode_parent {source : List (Nat × Bytes)} {height index : Nat}
    (positive : 2 ≤ index) (bounded : levelOf index ≤ height) (even : index % 2 = 0)
    (absent : nodeAt source (gindexParent index) = none) :
    combine (proofTreeNode source height index) (proofTreeNode source height (index + 1)) =
      proofTreeNode source height (gindexParent index) := by
  -- Taking roots of the two-child tree equation gives the executable parent hash.
  exact (congrArg CommitmentTree.root (proofTree_parent positive bounded even absent)).symm

/-- Every live node is an ancestor of an originally supplied node. -/
def ProofSupported (source nodes : List (Nat × Bytes)) : Prop :=
  -- Each live position is an ancestor of at least one originally supplied position.
  ∀ index ∈ nodes.map Prod.fst,
    ∃ original ∈ source.map Prod.fst, ∃ step, original >>> step = index

/-- Folding one level preserves the origin of every live node. -/
theorem ProofSupported.fold {source nodes result : List (Nat × Bytes)} {depth : Nat}
    (supported : ProofSupported source nodes) (folded : foldLevel depth nodes = .ok result) :
    ProofSupported source result := by
  -- A surviving position is either unchanged or one level above an even child.
  intro index member
  obtain ⟨child, childMember, unchanged | joined⟩ := (foldLevel_indices folded index).mp member
  · exact unchanged.2 ▸ supported child childMember
  · obtain ⟨original, originalMember, step, descended⟩ := supported child childMember
    refine ⟨original, originalMember, step + 1, ?_⟩
    rw [shiftRight_succ, descended]
    exact joined.2.2.symm

private theorem foldLevelNodes_local_agrees {tree : Nat → Bytes} {depth : Nat}
    {nodes pending : List (Nat × Bytes)}
    (parents : ∀ index value, (index, value) ∈ pending → levelOf index = depth →
      index % 2 = 0 → combine (tree index) (tree (index + 1)) = tree (gindexParent index))
    (allAgree : NodesAgree tree nodes) (pendingAgree : NodesAgree tree pending)
    {outParents outKept : List (Nat × Bytes)}
    (folded : foldLevelNodes depth nodes pending = .ok (outParents, outKept)) :
    NodesAgree tree (outParents ++ outKept) := by
  -- Follow the executable worker while maintaining agreement for both output groups.
  induction pending generalizing outParents outKept with
  | nil => simp_all [foldLevelNodes, NodesAgree]
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    have head : value = tree index := pendingAgree index value (by simp)
    have tail : NodesAgree tree rest := fun i v member => pendingAgree i v (by simp [member])
    have remaining : ∀ i v, (i, v) ∈ rest → levelOf i = depth → i % 2 = 0 →
        combine (tree i) (tree (i + 1)) = tree (gindexParent i) :=
      fun i v member => parents i v (List.mem_cons_of_mem _ member)
    simp only [foldLevelNodes] at folded
    split at folded
    · -- Shallower nodes retain the same stored value and subtree.
      cases rec : foldLevelNodes depth nodes rest <;>
        simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
      rcases folded with ⟨rfl, rfl⟩
      have agrees := ih remaining tail rec
      simp only [NodesAgree, List.mem_append, List.mem_cons] at agrees ⊢
      grind
    · rename_i atDepth
      have atDepth : levelOf index = depth := by simpa using atDepth
      split at folded
      · rename_i even
        have even : index % 2 = 0 := by simpa using even
        cases sibling : nodeAt nodes (index + 1) with
        | none => simp [sibling, throw] at folded
        | some siblingValue =>
          -- The even child owns the hash, and lookup supplies the matching right subtree.
          have siblingAgrees := nodeAt_agrees allAgree sibling
          have parent := parents index value List.mem_cons_self atDepth even
          cases rec : foldLevelNodes depth nodes rest <;>
            simp [sibling, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
          rcases folded with ⟨rfl, rfl⟩
          have agrees := ih remaining tail rec
          simp only [NodesAgree, List.mem_append, List.mem_cons] at agrees ⊢
          grind
      · -- The odd child contributes no second parent.
        split at folded
        · simp [throw] at folded
        · exact ih remaining tail folded

/-- One executable level fold preserves the node reading of the reconstructed tree. -/
theorem foldLevel_proofTree {source nodes result : List (Nat × Bytes)} {height depth : Nat}
    (separated : ProofAntichain source) (supported : ProofSupported source nodes)
    (positive : 0 < depth) (bounded : depth ≤ height)
    (agree : NodesAgree (proofTreeNode source height) nodes)
    (folded : foldLevel depth nodes = .ok result) :
    NodesAgree (proofTreeNode source height) result := by
  -- The worker returns parents and retained nodes as the two halves of the next frontier.
  unfold foldLevel at folded
  cases rec : foldLevelNodes depth nodes nodes <;>
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
  subst result
  apply foldLevelNodes_local_agrees (tree := proofTreeNode source height) _ agree agree rec
  intro index value member atDepth even
  have low := two_le_of_level_positive atDepth positive
  apply proofTreeNode_parent low (by omega) even
  exact source_parent_absent separated (supported index (List.mem_map.mpr ⟨_, member, rfl⟩)) low

/-- Every successful fold agrees with the tree cut at its original proof frontier. -/
theorem foldToRoot_proofTree {source : List (Nat × Bytes)} {height : Nat}
    (separated : ProofAntichain source) :
    ∀ depth, depth ≤ height → ∀ nodes, ProofSupported source nodes →
      NodesAgree (proofTreeNode source height) nodes → ∀ root,
      foldToRoot depth nodes = .ok root → root = (proofTree source height 1).root := by
  -- Successive folds preserve the finite tree reading until the final root lookup.
  intro depth
  induction depth with
  | zero =>
    intro _ nodes _ agree root built
    cases found : nodeAt nodes 1 <;> simp [foldToRoot, found] at built
    subst root
    simpa [proofTreeNode, show levelOf 1 = 0 from rfl] using nodeAt_agrees agree found
  | succ depth ih =>
    intro bounded nodes supported agree root built
    simp only [foldToRoot] at built
    cases folded : foldLevel (depth + 1) nodes with
    | error fault => simp [folded, Bind.bind, Except.bind] at built
    | ok result =>
      simp only [folded, Bind.bind, Except.bind] at built
      exact ih (by omega) result (supported.fold folded)
        (foldLevel_proofTree separated supported (by omega) bounded agree folded) root built

/-- A unique index lookup returns its supplied value. -/
theorem nodeAt_of_unique {nodes : List (Nat × Bytes)}
    (unique : (nodes.map Prod.fst).Nodup) {index : Nat} {value : Bytes}
    (member : (index, value) ∈ nodes) : nodeAt nodes index = some value := by
  -- Uniqueness lets lookup skip different indices without losing the requested value.
  induction nodes with
  | nil => simp at member
  | cons pair rest ih =>
    rcases pair with ⟨key, node⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with equal | later
    · cases equal
      simp [nodeAt]
    · have unequal : key ≠ index := by
        intro equal
        exact unique.1 (equal ▸ List.mem_map.mpr ⟨(index, value), later, rfl⟩)
      simpa [nodeAt, unequal] using ih unique.2 later

/-- Successful reconstruction computes the root of the explicit proof-frontier tree. -/
theorem foldToRoot_eq_proofTree {nodes : List (Nat × Bytes)} {height : Nat}
    (separated : ProofAntichain nodes) (unique : (nodes.map Prod.fst).Nodup)
    {root : Bytes} (built : foldToRoot height nodes = .ok root) :
    root = (proofTree nodes height 1).root := by
  -- Initially every live subtree is exactly the complete node supplied at that position.
  apply foldToRoot_proofTree separated height (Nat.le_refl _) nodes _ _ root built
  · intro index member
    exact ⟨index, member, 0, by simp⟩
  · intro index value member
    dsimp only [proofTreeNode]
    rw [proofTree_supplied nodes _ _ (nodeAt_of_unique unique member)]
    rfl

private theorem nodeAt_isSome {nodes : List (Nat × Bytes)} {index : Nat} :
    (nodeAt nodes index).isSome = true ↔ index ∈ nodes.map Prod.fst := by
  -- A successful lookup returns a stored pair, and every stored index admits a lookup.
  constructor
  · intro present
    cases found : nodeAt nodes index with
    | none => simp [found] at present
    | some value => exact List.mem_map.mpr ⟨_, nodeAt_member found, rfl⟩
  · intro member
    obtain ⟨pair, member, same⟩ := List.mem_map.mp member
    have member : (index, pair.2) ∈ nodes := by cases pair; simpa using same ▸ member
    obtain ⟨value, found⟩ := nodeAt_exists member
    simp [found]

/-- Equal index frontiers determine equal reconstruction shapes. -/
theorem proofTree_sameShape {left right : List (Nat × Bytes)}
    (positions : left.map Prod.fst = right.map Prod.fst) (height index : Nat) :
    CommitmentTree.SameShape (proofTree left height index) (proofTree right height index) := by
  -- Expansion stops at the same index in both frontiers, independently of node contents.
  induction height generalizing index with
  | zero => trivial
  | succ height ih =>
    have present : (nodeAt left index).isSome = (nodeAt right index).isSome := by
      apply Bool.eq_iff_iff.mpr
      simp only [nodeAt_isSome, positions]
    cases l : nodeAt left index <;> cases r : nodeAt right index <;>
      simp only [l, r, Option.isSome_none, Option.isSome_some] at present
    · simpa [proofTree, l, r, CommitmentTree.SameShape] using And.intro (ih (2 * index)) (ih (2 * index + 1))
    · contradiction
    · contradiction
    · simp [proofTree, l, r, CommitmentTree.SameShape]

/-- Complete supplied nodes make every hash input in reconstruction exactly 64 bytes. -/
theorem proofTree_complete {nodes : List (Nat × Bytes)}
    (widths : ∀ index value, (index, value) ∈ nodes → value.size = bytesPerChunk)
    (height index : Nat) : (proofTree nodes height index).Complete := by
  -- Supplied leaves have validated widths, and absent bottom leaves use the zero chunk.
  induction height generalizing index <;> cases found : nodeAt nodes index <;>
    simp [proofTree, CommitmentTree.Complete, zeroChunk_size, *] <;>
    exact widths _ _ (nodeAt_member found)

/-- A strict ancestor of a supplied node is not supplied itself. -/
private theorem nodeAt_ancestor_absent {nodes : List (Nat × Bytes)} (separated : ProofAntichain nodes)
    {target start step : Nat} {value : Bytes} (found : nodeAt nodes target = some value)
    (descended : target >>> step = start) (above : start < target) : nodeAt nodes start = none := by
  -- A supplied ancestor would have to be the node below it, which it strictly precedes.
  cases supplied : nodeAt nodes start with
  | none => rfl
  | some _ =>
    have := separated target (List.mem_map.mpr ⟨_, nodeAt_member found, rfl⟩) start
      (List.mem_map.mpr ⟨_, nodeAt_member supplied, rfl⟩) _ descended
    omega

/-- Equality of reconstruction trees preserves every supplied node on their common frontier. -/
theorem proofTree_supplied_injective {left right : List (Nat × Bytes)}
    (leftSeparated : ProofAntichain left) (rightSeparated : ProofAntichain right)
    {target : Nat} {first second : Bytes}
    (leftFound : nodeAt left target = some first)
    (rightFound : nodeAt right target = some second) :
    ∀ distance height start, distance ≤ height → 1 ≤ start → target >>> distance = start →
      proofTree left height start = proofTree right height start → first = second := by
  -- Both frontiers contain the target, so neither can stop at an earlier ancestor.
  intro distance
  induction distance with
  | zero =>
    intro height start _ _ descended same
    simp only [Nat.shiftRight_zero] at descended
    subst start
    rw [proofTree_supplied left height target leftFound,
      proofTree_supplied right height target rightFound] at same
    exact CommitmentTree.leaf.inj same
  | succ distance ih =>
    intro height start bounded positive descended same
    obtain _ | height := height; · omega
    -- Removing the next low bit identifies the child on the common path.
    have half : (target >>> distance) / 2 = start := by
      simpa [shiftRight_succ] using descended
    have targetAbove : start < target := by have := shiftRight_le target distance; omega
    have leftAbsent := nodeAt_ancestor_absent leftSeparated leftFound descended targetAbove
    have rightAbsent := nodeAt_ancestor_absent rightSeparated rightFound descended targetAbove
    simp only [proofTree, leftAbsent, rightAbsent, CommitmentTree.fork.injEq] at same
    rcases Nat.mod_two_eq_zero_or_one (target >>> distance) with even | odd
    · exact ih height (2 * start) (by omega) (by omega) (by omega) same.1
    · exact ih height (2 * start + 1) (by omega) (by omega) (by omega) same.2

/-- A fixed valid proof frontier binds every supplied node unless reconstruction hashes collide. -/
theorem proofTree_binding {left right : List (Nat × Bytes)} {height : Nat}
    (leftSeparated : ProofAntichain left) (rightSeparated : ProofAntichain right)
    (positions : left.map Prod.fst = right.map Prod.fst)
    (leftWidths : ∀ index value, (index, value) ∈ left → value.size = bytesPerChunk)
    (rightWidths : ∀ index value, (index, value) ∈ right → value.size = bytesPerChunk)
    (same : (proofTree left height 1).root = (proofTree right height 1).root)
    {index : Nat} (positive : 1 ≤ index) (bounded : levelOf index ≤ height)
    {first second : Bytes} (leftFound : nodeAt left index = some first)
    (rightFound : nodeAt right index = some second) :
    first = second ∨ CommitmentTree.Collision (proofTree left height 1) (proofTree right height 1) := by
  -- A shared frontier fixes the complete tree shape before its hashes are compared.
  exact (CommitmentTree.binding _ _ (proofTree_complete leftWidths height 1)
    (proofTree_complete rightWidths height 1) (proofTree_sameShape positions height 1) same).imp_left
      (proofTree_supplied_injective leftSeparated rightSeparated leftFound rightFound
        (Nat.log2 index) height 1 bounded (by decide) (shiftRight_depth positive))

/--
Different proof frontiers still bind any node they both open.
Only the common path to that node is compared; sibling subtrees may have different shapes.
-/
theorem proofTree_opening_binding {left right : List (Nat × Bytes)}
    (leftSeparated : ProofAntichain left) (rightSeparated : ProofAntichain right)
    (leftWidths : ∀ index value, (index, value) ∈ left → value.size = bytesPerChunk)
    (rightWidths : ∀ index value, (index, value) ∈ right → value.size = bytesPerChunk)
    {target : Nat} {first second : Bytes}
    (leftFound : nodeAt left target = some first)
    (rightFound : nodeAt right target = some second) :
    ∀ distance leftHeight rightHeight start,
      distance ≤ leftHeight → distance ≤ rightHeight → 1 ≤ start → target >>> distance = start →
      (proofTree left leftHeight start).root = (proofTree right rightHeight start).root →
      first = second ∨ CommitmentTree.Collision
        (proofTree left leftHeight start) (proofTree right rightHeight start) := by
  -- Both frontiers contain the target, so neither can stop at an earlier ancestor.
  intro distance
  induction distance with
  | zero =>
    intro leftHeight rightHeight start _ _ _ descended same
    simp only [Nat.shiftRight_zero] at descended
    subst start
    rw [proofTree_supplied left leftHeight target leftFound,
      proofTree_supplied right rightHeight target rightFound] at same
    exact .inl same
  | succ distance ih =>
    intro leftHeight rightHeight start leftBound rightBound positive descended same
    obtain _ | leftHeight := leftHeight; · omega
    obtain _ | rightHeight := rightHeight; · omega
    -- The next child is determined by the target index, independently of the proof frontier.
    have half : (target >>> distance) / 2 = start := by
      simpa [shiftRight_succ] using descended
    have targetAbove : start < target := by have := shiftRight_le target distance; omega
    have leftAbsent := nodeAt_ancestor_absent leftSeparated leftFound descended targetAbove
    have rightAbsent := nodeAt_ancestor_absent rightSeparated rightFound descended targetAbove
    simp only [proofTree, leftAbsent, rightAbsent] at same ⊢
    have leftComplete := proofTree_complete leftWidths (leftHeight + 1) start
    have rightComplete := proofTree_complete rightWidths (rightHeight + 1) start
    simp only [proofTree, leftAbsent, rightAbsent] at leftComplete rightComplete
    -- Equal parent hashes either preserve both child roots or already witness a collision.
    rcases CommitmentTree.fork_binding leftComplete rightComplete same with children | collision
    · rcases Nat.mod_two_eq_zero_or_one (target >>> distance) with even | odd
      · exact (ih leftHeight rightHeight (2 * start) (by omega) (by omega)
          (by omega) (by omega) children.1).imp_right (·.left _ _)
      · exact (ih leftHeight rightHeight (2 * start + 1) (by omega) (by omega)
          (by omega) (by omega) children.2).imp_right (·.right _ _)
    · exact .inr collision

end EthLib.Consensus.Ssz
