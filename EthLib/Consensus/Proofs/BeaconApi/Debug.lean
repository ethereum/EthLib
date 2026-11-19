module

public import EthLib.Consensus.BeaconApi.Debug
public import EthLib.Consensus.Proofs.ForkChoice.Head
import EthLib.Base.Proofs.FilterM
import EthLib.Base.Proofs.List

/-!
# Proofs: the views of the tree of the fork choice

A node of the tree names another as its parent exactly when it is a child of that node.

Before Gloas each block has exactly one view, which the API calls full.

When some leaf is viable, the block of the head is one of the leaves that the API gives.

The three counts of the payload committee are those of the block, at most the size of the committee.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork} {config : Config} {store : Store preset fork}
  {optimistic : OptimisticStore preset fork}

/-- The children of a node can be computed when the store holds its block. -/
private theorem getNodeChildren_ok_of_known {root : Root} {status : PayloadStatus}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    ∃ children, store.getNodeChildren ⟨root, status⟩ = .ok children := by
  unfold Store.getNodeChildren
  split
  · exact ⟨_, rfl⟩
  · dsimp only
    split
    · simp [Store.block, found, bind, Except.bind, pure, Except.pure]
    · exact ⟨_, rfl⟩

/-- The listed nodes of the tree are exactly the nodes that belong to it. -/
theorem mem_treeNodes {node : ForkChoiceNode} :
    node ∈ treeNodes store ↔ isTreeNode store node = true := by
  obtain ⟨root, status⟩ := node
  simp only [treeNodes, List.mem_flatMap, Std.TreeMap.mem_keys, isTreeNode, blockNodes]
  by_cases gloas : .glamsterdam ≤ fork
  · simp only [gloas, ↓reduceDIte, List.mem_cons, ForkChoiceNode.mk.injEq, Bool.and_eq_true,
      Std.TreeMap.contains_iff_mem]
    constructor
    · rintro ⟨a, mem, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | full⟩
      · exact ⟨mem, rfl⟩
      · exact ⟨mem, rfl⟩
      · split at full
        · rename_i verified
          simp only [List.mem_singleton, ForkChoiceNode.mk.injEq] at full
          obtain ⟨rfl, rfl⟩ := full
          exact ⟨mem, by simp [verified]⟩
        · cases full
    · rintro ⟨mem, allowed⟩
      refine ⟨root, mem, ?_⟩
      cases status
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · simp only [bne_self_eq_false, Bool.false_or] at allowed
        exact .inr (.inr (by simp [allowed]))
      · exact .inl ⟨rfl, rfl⟩
  · simp only [gloas, ↓reduceDIte, List.mem_singleton, ForkChoiceNode.mk.injEq,
      Bool.and_eq_true, Std.TreeMap.contains_iff_mem, beq_iff_eq]
    constructor
    · rintro ⟨a, mem, rfl, rfl⟩
      exact ⟨mem, rfl⟩
    · rintro ⟨mem, rfl⟩
      exact ⟨root, mem, rfl, rfl⟩

/-- A node of the tree has a node as its parent exactly when it is a child of that node.

The parent must itself belong to the tree. -/
theorem treeParent_eq_some_iff {node parent : ForkChoiceNode}
    (tree : isTreeNode store node = true) :
    treeParent store node = some parent ↔ isTreeNode store parent = true ∧
      ∃ children, store.getNodeChildren parent = .ok children ∧ node ∈ children := by
  obtain ⟨root, status⟩ := node
  simp only [isTreeNode, Bool.and_eq_true] at tree
  obtain ⟨known, allowed⟩ := tree
  rw [Std.TreeMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at known
  obtain ⟨block, found⟩ := known
  simp only [treeParent, Option.filter_eq_some_iff, parentLink, found, Option.bind_eq_bind,
    Option.bind_some]
  by_cases gloas : .glamsterdam ≤ fork
  · simp only [gloas, ↓reduceDIte] at allowed
    by_cases pending : status = .pending
    · rw [ite_eq_right (by simp [pending])]
      subst pending
      constructor
      · rintro ⟨linked, parentTree⟩
        simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at linked
        obtain ⟨parentBlock, parentFound, rfl⟩ := linked
        obtain ⟨children, childrenOk⟩ := getNodeChildren_ok_of_known parentFound
        refine ⟨parentTree, children, childrenOk, ?_⟩
        rw [Store.mem_getNodeChildren_of_gloas gloas (Store.parentPayloadStatus_ne_pending gloas)
          childrenOk]
        exact ⟨rfl, block, parentBlock, found, rfl, parentFound, rfl⟩
      · rintro ⟨parentTree, children, childrenOk, mem⟩
        by_cases parentPending : parent.payloadStatus = .pending
        · rw [Store.getNodeChildren_of_pending gloas parentPending, Except.ok.injEq] at childrenOk
          subst childrenOk
          simp only [List.mem_cons, ForkChoiceNode.mk.injEq] at mem
          rcases mem with ⟨-, nope⟩ | mem
          · cases nope
          · split at mem
            · simp only [List.mem_singleton, ForkChoiceNode.mk.injEq] at mem
              cases mem.2
            · cases mem
        · obtain ⟨-, other, parentBlock, otherFound, parentRoot, parentFound, built⟩ :=
            (Store.mem_getNodeChildren_of_gloas gloas parentPending childrenOk).mp mem
          rw [found, Option.some.injEq] at otherFound
          subst otherFound
          refine ⟨?_, parentTree⟩
          obtain ⟨parentRoot', parentStatus⟩ := parent
          simp only at parentRoot built parentFound
          subst parentRoot built
          simp [parentFound, pure]
    · rw [ite_eq_left ⟨gloas, pending⟩]
      have own : ⟨root, status⟩ ∈ (⟨root, .empty⟩ :: if store.isPayloadVerified gloas root then
          [⟨root, .full⟩] else [] : List ForkChoiceNode) := by
        cases status
        · exact List.mem_cons_self
        · simp only [bne_self_eq_false, Bool.false_or] at allowed
          simp [allowed]
        · exact absurd rfl pending
      constructor
      · rintro ⟨linked, parentTree⟩
        simp only [pure, Option.some.injEq] at linked
        subst linked
        exact ⟨parentTree, _, Store.getNodeChildren_of_pending gloas rfl, own⟩
      · rintro ⟨parentTree, children, childrenOk, mem⟩
        by_cases parentPending : parent.payloadStatus = .pending
        · rw [Store.getNodeChildren_of_pending gloas parentPending, Except.ok.injEq] at childrenOk
          subst childrenOk
          refine ⟨?_, parentTree⟩
          have sameRoot : root = parent.root := by
            simp only [List.mem_cons, ForkChoiceNode.mk.injEq] at mem
            rcases mem with ⟨same, -⟩ | mem
            · exact same
            · split at mem
              · simp only [List.mem_singleton, ForkChoiceNode.mk.injEq] at mem
                exact mem.1
              · cases mem
          obtain ⟨parentRoot', parentStatus⟩ := parent
          simp only at sameRoot parentPending
          subst sameRoot parentPending
          rfl
        · exact absurd ((Store.mem_getNodeChildren_of_gloas gloas parentPending childrenOk).mp
            mem).1 pending
  · simp only [gloas, ↓reduceDIte, beq_iff_eq] at allowed
    subst allowed
    have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
    rw [ite_eq_right (by simp [gloas])]
    constructor
    · rintro ⟨linked, parentTree⟩
      simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at linked
      obtain ⟨parentBlock, parentFound, rfl⟩ := linked
      obtain ⟨children, childrenOk⟩ := getNodeChildren_ok_of_known parentFound
      exact ⟨parentTree, children, childrenOk,
        (Store.mem_getNodeChildren before childrenOk).mpr ⟨rfl, block, found, rfl⟩⟩
    · rintro ⟨parentTree, children, childrenOk, mem⟩
      obtain ⟨-, other, otherFound, parentRoot⟩ :=
        (Store.mem_getNodeChildren before childrenOk).mp mem
      rw [found, Option.some.injEq] at otherFound
      subst otherFound
      refine ⟨?_, parentTree⟩
      obtain ⟨parentRoot', parentStatus⟩ := parent
      simp only [isTreeNode, gloas, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq] at parentTree
      obtain ⟨parentKnown, rfl⟩ := parentTree
      rw [Std.TreeMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at parentKnown
      obtain ⟨parentBlock, parentFound⟩ := parentKnown
      simp only at parentRoot
      subst parentRoot
      simp [parentFound, pure, Store.parentPayloadStatus_of_lt before]

/-- A view gives the status of the parent of its node in the tree, as the API names it.

When the tree holds that parent, the view gives the root of its block. -/
theorem nodeView_parent {tally : Except ForkChoiceError VoteTally} {node : ForkChoiceNode}
    {view : ForkChoiceNodeView} (made : nodeView config store optimistic tally node = .ok view) :
    view.parentPayloadStatus =
        (treeParent store node).map (apiPayloadStatus fork ·.payloadStatus) ∧
      ∀ parent, treeParent store node = some parent → view.parentRoot = parent.root := by
  simp only [nodeView, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
  obtain ⟨block, blockOk, _, -, _, -, _, -, rfl⟩ := made
  refine ⟨rfl, fun parent linked => ?_⟩
  rw [Store.block_ok_iff] at blockOk
  simp only [treeParent, Option.filter_eq_some_iff, parentLink, blockOk, Option.bind_eq_bind,
    Option.bind_some] at linked
  obtain ⟨linked, -⟩ := linked
  dsimp only
  split
  · rename_i cond
    rw [ite_eq_left cond] at linked
    cases linked
    rfl
  · rename_i cond
    rw [ite_eq_right cond] at linked
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at linked
    obtain ⟨_, -, rfl⟩ := linked
    rfl

/-- Before Gloas the views are one per block, in the order of roots, and each is full. -/
theorem nodeViews_preGloas_full (before : fork < .glamsterdam)
    {views : List ForkChoiceNodeView} (made : nodeViews config store optimistic = .ok views) :
    views.map (·.blockRoot) = store.blocks.keys ∧ ∀ view ∈ views, view.payloadStatus = .full := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  unfold nodeViews at made
  refine ⟨?_, fun view mem => ?_⟩
  · have rootOf : ∀ node view, nodeView config store optimistic store.justifiedTally node =
        .ok view → view.blockRoot = node.root := by
      intro node view made
      simp only [nodeView, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
      obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := made
      rfl
    rw [map_of_mapM_ok rootOf made]
    have single : blockNodes store = fun root => [⟨root, .pending⟩] := by
      funext root
      simp [blockNodes, later]
    rw [treeNodes, single]
    induction store.blocks.keys with
    | nil => rfl
    | cons root rest ih => simp [ih]
  · obtain ⟨node, -, made⟩ := mapM_ok_mem made view mem
    simp only [nodeView, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
    obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := made
    simp [apiPayloadStatus, later]

/-- A node of a known block belongs to the tree when its status is allowed.

From Gloas a full node needs the verified payload, and before Gloas the node must be pending. -/
private theorem isTreeNode_of_known {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block)
    (allowed : if gloas : .glamsterdam ≤ fork then
      node.payloadStatus ≠ .full ∨ store.isPayloadVerified gloas node.root = true
      else node.payloadStatus = .pending) :
    isTreeNode store node = true := by
  simp only [isTreeNode, Bool.and_eq_true, Std.TreeMap.contains_eq_isSome_getElem?, found,
    Option.isSome_some, true_and]
  split
  · rename_i gloas
    simp only [gloas, ↓reduceDIte] at allowed
    simpa [bne_iff_ne] using allowed
  · rename_i gloas
    simp only [gloas, ↓reduceDIte] at allowed
    simpa using allowed

/-- The block of a node of the tree is known. -/
private theorem known_of_isTreeNode {node : ForkChoiceNode} (tree : isTreeNode store node = true) :
    ∃ block, store.blocks[node.root]? = some block := by
  simp only [isTreeNode, Bool.and_eq_true] at tree
  rw [Std.TreeMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at tree
  exact tree.1

/-- Each child of a node of a known block belongs to the tree. -/
private theorem isTreeNode_of_child {node child : ForkChoiceNode}
    {children : List ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block)
    (childrenOk : store.getNodeChildren node = .ok children) (mem : child ∈ children) :
    isTreeNode store child = true := by
  by_cases gloas : .glamsterdam ≤ fork
  · by_cases pending : node.payloadStatus = .pending
    · rw [Store.getNodeChildren_of_pending gloas pending, Except.ok.injEq] at childrenOk
      subst childrenOk
      rcases List.mem_cons.mp mem with rfl | mem
      · exact isTreeNode_of_known found (by simp [gloas])
      · split at mem
        · rename_i verified
          rw [List.mem_singleton.mp mem]
          exact isTreeNode_of_known found (by simp [gloas, verified])
        · cases mem
    · obtain ⟨childPending, childBlock, -, childFound, -⟩ :=
        (Store.mem_getNodeChildren_of_gloas gloas pending childrenOk).mp mem
      exact isTreeNode_of_known childFound (by simp [gloas, childPending])
  · obtain ⟨childPending, childBlock, childFound, -⟩ :=
      (Store.mem_getNodeChildren (Nat.lt_of_not_le gloas) childrenOk).mp mem
    exact isTreeNode_of_known childFound (by simp [gloas, childPending])

/-- The viable nodes below a node of the tree belong to the tree. -/
private theorem filterNodeTree_tree :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes → isTreeNode store node = true →
      ∀ n ∈ nodes, isTreeNode store n = true := by
  intro node
  induction hrank : store.nodeRank node using Nat.strongRecOn generalizing node with
  | _ rank ih =>
  intro nodes walk tree n mem
  obtain ⟨block, found⟩ := known_of_isTreeNode tree
  rw [Store.filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  by_cases empty : children.isEmpty
  · simp only [empty, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨isViable, -, rfl⟩ := walk
    cases isViable
    · cases mem
    · rw [List.mem_singleton.mp mem]
      exact tree
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at walk
  obtain ⟨viable, viableOk, rfl⟩ := walk
  split at mem
  · cases mem
  rcases List.mem_append.mp mem with mem | same
  · obtain ⟨child, childMem, below, belowOk, nMem⟩ := (mem_of_flatMapM_ok viableOk n).mp mem
    split at belowOk
    · rename_i lowerRank
      exact ih _ (hrank ▸ lowerRank) rfl belowOk (isTreeNode_of_child found childrenOk childMem)
        n nMem
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  · rw [List.mem_singleton.mp same]
    exact tree

/-- When some leaf below the justified block is viable, the head's block is a chain head. -/
theorem chainHeads_head {head : ForkChoiceNode} {heads : List ChainHead}
    (found : store.getHead config = .ok head)
    (viable : store.getFilteredNodeTree config ≠ .ok [])
    (listed : chainHeads store optimistic = .ok heads) :
    ∃ chainHead ∈ heads, chainHead.root = head.root := by
  obtain ⟨nodes, children, tree, childrenOk, leaf⟩ := Store.getHead_leaf found
  have nonempty : nodes ≠ [] := fun nil => viable (nil ▸ tree)
  -- The head is one of the viable nodes.
  have headIn : head ∈ nodes := by
    unfold Store.getHead at found
    simp only [tree, bind, Except.bind] at found
    split at found
    · rename_i empty
      exact absurd (List.isEmpty_iff.mp empty.2) nonempty
    · rcases Store.getHeadFrom_mem found with rfl | mem
      · exact Store.filterNodeTree_self tree nonempty
      · exact mem
  -- A viable node with children has a viable child, so the head has no child.
  have noChildren : children = [] := Classical.byContradiction fun some => by
    obtain ⟨c, cMem, cIn⟩ := Store.filterNodeTree_child tree head headIn childrenOk some
    exact leaf c cMem cIn
  subst noChildren
  have startTree : isTreeNode store ⟨store.justifiedCheckpoint.root, .pending⟩ = true := by
    obtain ⟨block, blockFound⟩ := Store.filterNodeTree_known tree
    exact isTreeNode_of_known blockFound (by simp)
  have headTree := filterNodeTree_tree tree startTree head headIn
  unfold chainHeads at listed
  rw [bind_ok_iff] at listed
  obtain ⟨leaves, leavesOk, listed⟩ := listed
  have headLeaf : head ∈ leaves :=
    mem_filterM_ok_of_test leavesOk (mem_treeNodes.mpr headTree)
      (by simp [childrenOk, bind, Except.bind, pure, Except.pure])
  have rootIn : head.root ∈ (leaves.map (·.root)).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_map_of_mem headLeaf)
  obtain ⟨chainHead, chainHeadMem, step⟩ := exists_mem_of_mapM_ok listed rootIn
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
  obtain ⟨_, -, _, -, rfl⟩ := step
  exact ⟨_, chainHeadMem, rfl⟩

/-- The roots of the chain heads are those of the leaves, each once. -/
private theorem chainHeads_roots {heads : List ChainHead}
    (listed : chainHeads store optimistic = .ok heads) :
    ∃ leaves, treeLeaves store = .ok leaves ∧
      heads.map (·.root) = (leaves.map (·.root)).eraseDups := by
  unfold chainHeads at listed
  rw [bind_ok_iff] at listed
  obtain ⟨leaves, leavesOk, listed⟩ := listed
  refine ⟨leaves, leavesOk, ?_⟩
  rw [map_of_mapM_ok (q := id) ?_ listed, List.map_id]
  intro root head step
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
  obtain ⟨_, -, _, -, rfl⟩ := step
  rfl

/-- The root of a node of a block is the root of that block. -/
private theorem root_of_mem_blockNodes {root : Root} {node : ForkChoiceNode}
    (mem : node ∈ blockNodes store root) : node.root = root := by
  unfold blockNodes at mem
  split at mem
  · split at mem <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at mem <;>
      rcases mem with rfl | rfl | rfl <;> rfl
  · rw [List.mem_singleton.mp mem]

/-- A root is a chain head exactly when one of its nodes is a leaf of the tree. -/
theorem mem_chainHeads_iff {heads : List ChainHead}
    (listed : chainHeads store optimistic = .ok heads) (root : Root) :
    root ∈ heads.map (·.root) ↔ ∃ node ∈ treeNodes store, node.root = root ∧
      store.getNodeChildren node = .ok [] := by
  obtain ⟨leaves, leavesOk, roots⟩ := chainHeads_roots listed
  rw [roots, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨node, mem, rfl⟩
    refine ⟨node, mem_of_filterM_ok leavesOk mem, rfl, ?_⟩
    have passes := passes_of_mem_filterM_ok leavesOk mem
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, List.isEmpty_iff] at passes
    obtain ⟨_, childrenOk, rfl⟩ := passes
    exact childrenOk
  · rintro ⟨node, mem, rfl, childrenOk⟩
    exact ⟨node, mem_filterM_ok_of_test leavesOk mem
      (by simp [childrenOk, bind, Except.bind, pure, Except.pure]), rfl⟩

/-- Each root is a chain head at most once. -/
theorem chainHeads_nodup {heads : List ChainHead}
    (listed : chainHeads store optimistic = .ok heads) : (heads.map (·.root)).Nodup := by
  obtain ⟨leaves, -, roots⟩ := chainHeads_roots listed
  rw [roots]
  exact nodup_eraseDups _

/-- No node of the tree is listed twice. -/
theorem treeNodes_nodup : (treeNodes store).Nodup := by
  unfold treeNodes
  rw [List.Nodup, List.pairwise_flatMap]
  refine ⟨fun root _ => ?_, store.blocks.nodup_keys.imp fun ne x xMem y yMem same => ne ?_⟩
  · unfold blockNodes
    split
    · split <;> simp
    · simp
  · rw [← root_of_mem_blockNodes xMem, ← root_of_mem_blockNodes yMem, same]

/-- The views follow the nodes of the tree, by root and by the status that the API names. -/
theorem nodeViews_nodes {views : List ForkChoiceNodeView}
    (made : nodeViews config store optimistic = .ok views) :
    views.map (fun view => (view.blockRoot, view.payloadStatus)) =
      (treeNodes store).map fun node =>
        (node.root, apiPayloadStatus fork node.payloadStatus) := by
  unfold nodeViews at made
  refine map_of_mapM_ok (fun node view made => ?_) made
  simp only [nodeView, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
  obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := made
  rfl

/-- A view gives the three counts of the payload committee for the block of its node. -/
theorem nodeView_ptcCounts {tally : Except ForkChoiceError VoteTally} {node : ForkChoiceNode}
    {view : ForkChoiceNodeView} (made : nodeView config store optimistic tally node = .ok view) :
    (view.payloadAttesterCount, view.payloadAvailabilityYesCount,
      view.payloadDataAvailabilityYesCount) = ptcCounts store node.root := by
  simp only [nodeView, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
  obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := made
  rfl

/-- Each count is at most the size of the committee.

The votes for on time are among the recorded votes. -/
theorem ptcCounts_le (root : Root) :
    (ptcCounts store root).1.toNat ≤ preset.PTC_SIZE.toNat ∧
      (ptcCounts store root).2.1 ≤ (ptcCounts store root).1 ∧
      (ptcCounts store root).2.2.toNat ≤ preset.PTC_SIZE.toNat := by
  by_cases gloas : .glamsterdam ≤ fork
  · simp only [ptcCounts, gloas, ↓reduceDIte]
    generalize ((store.payloadTimelinessVote gloas)[root]?).getD _ = timely
    generalize ((store.payloadDataAvailabilityVote gloas)[root]?).getD _ = available
    have fits := preset.PTC_SIZE.toNat_lt
    have voted := List.countP_le_length (p := (·.isSome)) (l := timely.toList)
    have yes : timely.toList.countP (· == some true) ≤ timely.toList.countP (·.isSome) :=
      List.countP_mono_left fun x _ h => by simp_all
    have availableYes := List.countP_le_length (p := (· == some true)) (l := available.toList)
    simp only [Vector.length_toList] at voted availableYes
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.le_trans UInt64.toNat_ofNat_le voted
    · rw [UInt64.le_iff_toNat_le]
      simp only [UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact yes
    · exact Nat.le_trans UInt64.toNat_ofNat_le availableYes
  · simp [ptcCounts, gloas]

/-- Before Gloas the three counts are zero. -/
theorem ptcCounts_preGloas (before : fork < .glamsterdam) (root : Root) :
    ptcCounts store root = (0, 0, 0) := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [ptcCounts, later, ↓reduceDIte]

end EthLib.Consensus.BeaconApi
