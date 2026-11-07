module

public import EthLib.Consensus.Proofs.ForkChoice.Ghost
public import EthLib.Consensus.Proofs.ForkChoice.PayloadVotes
public import EthLib.Consensus.Proofs.Models.ForkChoice.PayloadTree

/-!
# Proofs: from Gloas, the head of the fork choice is LMD-GHOST over payload-status nodes

From Gloas the head rule of the store is the rule of the LMD-GHOST model over nodes.

A node of the model is a block with its payload pending, empty or full, as EIP-7732 says.

The tree of nodes stands over the tree of the known blocks of the store.

A pending node hangs under the empty or the full node of its parent, as its bid builds on it.

A vote supports the node that the store gives it.

That is the pending node in the slot of its block, and later the empty or the full node.

The theorem holds away from the payload decisions of the previous slot, and without the boost.

There the payload committee and the proposer decide, which the model leaves out.

A tie between two children goes to the greater root, then to the greater status number.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models.ForkChoice BlockTree

/-- The status of a payload in the model: none while pending, then whether the payload is present.
-/
def PayloadStatus.toStatus : PayloadStatus → Status
  | .empty => some false
  | .full => some true
  | .pending => none

/-- The node of the model for a node of the store: its root as a known root, and its status. -/
def ForkChoiceNode.toModel (node : ForkChoiceNode) : Option Root × Status :=
  (some node.root, node.payloadStatus.toStatus)

theorem PayloadStatus.toStatus_injective : Function.Injective PayloadStatus.toStatus := by
  intro a b same
  cases a <;> cases b <;> simp_all [toStatus]

/-- The tiebreaker of a status is the number of its status in the model. -/
theorem PayloadStatus.code_toNat (status : PayloadStatus) :
    status.code.toNat = status.toStatus.code := by
  cases status <;> rfl

/-- An empty or full status is present exactly when it is full. -/
theorem PayloadStatus.toStatus_of_ne_pending {status : PayloadStatus}
    (notPending : status ≠ .pending) : status.toStatus = some (status == .full) := by
  cases status <;> simp_all [toStatus]

theorem ForkChoiceNode.toModel_injective : Function.Injective ForkChoiceNode.toModel := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ same
  simp only [toModel, Prod.mk.injEq, Option.some.injEq] at same
  rw [same.1, PayloadStatus.toStatus_injective same.2]

/-- Every node of a known root in the model is the node of a node of the store. -/
theorem ForkChoiceNode.exists_toModel (root : Root) (status : Status) :
    ∃ node : ForkChoiceNode, node.toModel = (some root, status) := by
  rcases status with _ | _ | _
  · exact ⟨⟨root, .pending⟩, rfl⟩
  · exact ⟨⟨root, .empty⟩, rfl⟩
  · exact ⟨⟨root, .full⟩, rfl⟩

variable {preset : Preset} {fork : Fork}

namespace Store

variable (store : Store preset fork)

/-- Whether a root of the tree of the store builds on the full node of its parent.

A known block with a known parent builds as its bid says.

Any other root hangs under the full node of its parent.

So when every known block builds on a full parent, every root does. -/
def buildsOnFull : Option Root → Bool
  | some root =>
    match store.blocks[root]? with
    | some block =>
      match store.blocks[block.parentRoot]? with
      | some parent => parentPayloadStatus block parent == .full
      | none => true
    | none => true
  | none => true

variable {store} {lower : store.ParentsBelow}

variable (lower) in
/-- The tree of payload-status nodes over the tree of the store. -/
def nodeTree : BlockTree (Option Root × Status) :=
  (blockTree lower).payloadTree store.buildsOnFull

/-- The node of a block of the store hangs under the node of its parent that it builds on. -/
theorem nodeTree_parent_of {root : Root} {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent) :
    (nodeTree lower).parent (some root, none) =
      (some block.parentRoot, some (parentPayloadStatus block parent == .full)) := by
  rw [nodeTree, payloadTree_parent_none (Option.some_ne_none _), blockTree_parent_of found]
  simp [buildsOnFull, found, parentFound]

/-- From Gloas each child of a node in the store is its child in the tree of nodes. -/
theorem isChild_of_mem_getNodeChildren (gloas : .glamsterdam ≤ fork) {node child : ForkChoiceNode}
    {children : List ForkChoiceNode} (childrenOk : store.getNodeChildren node = .ok children)
    (mem : child ∈ children) : (nodeTree lower).IsChild child.toModel node.toModel := by
  by_cases pending : node.payloadStatus = .pending
  · rw [getNodeChildren_of_pending gloas pending, Except.ok.injEq] at childrenOk
    subst childrenOk
    have same : node.toModel = (some node.root, none) := by
      simp [ForkChoiceNode.toModel, pending, PayloadStatus.toStatus]
    rw [same]
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact payloadTree_isChild_some.mpr rfl
    · split at mem
      · rw [List.mem_singleton.mp mem]
        exact payloadTree_isChild_some.mpr rfl
      · cases mem
  · obtain ⟨childPending, block, parent, found, parentRoot, parentFound, built⟩ :=
      (mem_getNodeChildren_of_gloas gloas pending childrenOk).mp mem
    have toModel : child.toModel = (some child.root, none) := by
      simp [ForkChoiceNode.toModel, childPending, PayloadStatus.toStatus]
    rw [toModel]
    refine ⟨fun same => Option.some_ne_none _ (Prod.mk.inj same).1, ?_⟩
    rw [nodeTree_parent_of found (parentRoot ▸ parentFound), parentRoot, built,
      ← PayloadStatus.toStatus_of_ne_pending pending]
    rfl

/-! ## Ancestors -/

/-- From Gloas the ancestor walk climbs the tree of nodes.

It returns the node itself, or an empty or full node. -/
theorem getAncestor_nodeTree (gloas : .glamsterdam ≤ fork) {node ancestor : ForkChoiceNode}
    {slot : Slot} (walk : store.getAncestor node slot = .ok ancestor) :
    (nodeTree lower).Ancestor ancestor.toModel node.toModel ∧
      (ancestor = node ∨ ancestor.payloadStatus ≠ .pending) := by
  obtain ⟨-, origin, -⟩ := getAncestor_climbs (lower := lower) walk
  rcases origin with rfl | ⟨child, block, parent, found, parentFound, parentRoot, status, below⟩
  · exact ⟨.refl _, .inl rfl⟩
  have notPending : ancestor.payloadStatus ≠ .pending :=
    status ▸ parentPayloadStatus_ne_pending gloas
  refine ⟨?_, .inr notPending⟩
  -- The pending node of the child block is below the start, and the ancestor is its parent.
  have climb : (nodeTree lower).Ancestor (some child, none) node.toModel :=
    payloadTree_ancestor_none_of below
  refine Ancestor.trans ⟨1, ?_⟩ climb
  rw [Function.iterate_one, nodeTree_parent_of found parentFound, parentRoot, ← status,
    ← PayloadStatus.toStatus_of_ne_pending notPending]
  rfl

/-- The height of a node: twice the height of its block, plus one unless it is pending. -/
theorem nodeTree_height (node : ForkChoiceNode) :
    (nodeTree lower).height node.toModel =
      2 * (blockTree lower).height (some node.root) +
        if node.payloadStatus = .pending then 0 else 1 := by
  obtain ⟨root, _ | _ | _⟩ := node <;> rfl

/-- From Gloas a node descends from a known node exactly as in the tree of nodes. -/
theorem isAncestor_iff_of_gloas {start node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {result : Bool} (gloas : .glamsterdam ≤ fork) (found : store.blocks[node.root]? = some block)
    (computed : store.isAncestor start node = .ok result) :
    result = true ↔ (nodeTree lower).Ancestor node.toModel start.toModel := by
  have known : store.block node.root = .ok block := block_ok_iff.mpr found
  simp only [isAncestor, known, gloas, ↓reduceIte, bind, Except.bind] at computed
  cases walk : store.getAncestor start block.slot with
  | error e => simp [walk] at computed
  | ok ancestor =>
  simp only [walk, pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  obtain ⟨tree, origin⟩ := getAncestor_nodeTree (lower := lower) gloas walk
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨sameRoot, same | pending⟩
    · have : ancestor = node := by
        cases ancestor
        cases node
        simp_all
      exact this ▸ tree
    · -- The pending node of a block is an ancestor of its other nodes.
      have pendingNode : node.toModel = (some ancestor.root, none) := by
        simp [ForkChoiceNode.toModel, sameRoot, pending, PayloadStatus.toStatus]
      rw [pendingNode]
      exact (payloadTree_ancestor_none_of (Ancestor.refl _)).trans tree
  · intro above
    have sameRoot :=
      getAncestor_root_eq found walk (payloadTree_ancestor_fst above)
    refine ⟨sameRoot, ?_⟩
    by_cases pending : node.payloadStatus = .pending
    · exact .inr pending
    refine .inl ?_
    -- Both nodes of the block sit one level above its pending node.
    have heights := nodeTree_height (lower := lower) node
    have ancestorHeights := nodeTree_height (lower := lower) ancestor
    rw [sameRoot] at ancestorHeights
    simp only [pending, ↓reduceIte] at heights
    by_cases ancestorPending : ancestor.payloadStatus = .pending
    · have startIs : ancestor = start := origin.resolve_right (· ancestorPending)
      subst startIs
      simp only [ancestorPending, ↓reduceIte] at ancestorHeights
      have := above.height_le
      omega
    · simp only [ancestorPending, ↓reduceIte] at ancestorHeights
      have same : ancestor.toModel = node.toModel := by
        rcases above.total tree with low | high
        · by_contra ne
          have := low.height_lt (Ne.symm ne)
          omega
        · by_contra ne
          have := high.height_lt ne
          omega
      rw [ForkChoiceNode.toModel_injective same]

/-! ## Votes and weights -/

variable (store) in
/-- The latest vote of a validator, by its index, as the node of the model that it supports.

An equivocator has none. -/
def latestNode (index : ValidatorIndex) : Option (Option Root × Status) :=
  if store.equivocatingIndices.contains index then none
  else store.latestMessages[index]?.bind fun message =>
    (store.getSupportedNode message).toOption.map (·.toModel)

variable (lower) in
/-- The view of the given nodes, their ancestors and the latest votes of the store, as nodes. -/
noncomputable def nodeView (nodes : List ForkChoiceNode) :
    View ℕ (Option Root × Status) (nodeTree lower) :=
  View.ofBlocks (nodes.map (·.toModel)).toFinset (store.latestNode ·.toUInt64)

/-- From Gloas, the votes for a known node are its weight in the model of nodes.

The voters are those that count in the given state, with their effective balances. -/
theorem getAttestationScore_eq_weight_of_gloas {node : ForkChoiceNode}
    {block : BeaconBlock preset fork} {state : BeaconState preset fork} {score : Gwei}
    (gloas : .glamsterdam ≤ fork) (found : store.blocks[node.root]? = some block)
    (nodes : List ForkChoiceNode) (computed : store.getAttestationScore node state = .ok score) :
    score.toNat = weight (voters state) (balanceAt state) (nodeView lower nodes) node.toModel := by
  refine getAttestationScore_eq_weight_of_reads (vote := store.latestNode) _ (fun _ => rfl)
    ⟨fun index none => ?_, fun index equivocating => ?_,
      fun index message supported result message' honest supportedOk computed' => ?_⟩ computed
  · simp [latestNode, none]
  · simp only [latestNode, equivocating, ↓reduceIte]
  · rw [isAncestor_iff_of_gloas (lower := lower) gloas found computed']
    simp only [latestNode, honest, Bool.false_eq_true, ↓reduceIte, message']
    simp [supportedOk, Except.toOption]

variable {config : Config} {state : BeaconState preset fork}

/-- From Gloas, a known node weighs its weight in the model of nodes.

The node must not be a payload decision of the previous slot, and the boost must not apply. -/
theorem getWeight_eq_weight_of_gloas {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {weightValue : Gwei} (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (decision : store.isPreviousSlotPayloadDecision config node = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (found : store.blocks[node.root]? = some block) (nodes : List ForkChoiceNode)
    (computed : store.getWeight config node = .ok weightValue) :
    weightValue.toNat =
      weight (voters state) (balanceAt state) (nodeView lower nodes) node.toModel := by
  rw [getWeight_of_not_boost gloas decision noBoost, justifiedState] at computed
  exact getAttestationScore_eq_weight_of_gloas gloas found nodes computed

/-! ## The head -/

/-- From Gloas, the children of a viable node in the view and in the store.

The node is in the subtree of the pending node of the justified block.

A node is a child in the view exactly when it is a viable child in the store. -/
theorem mem_children_nodeView {nodes : List ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (tree : store.getFilteredNodeTree config = .ok nodes) {node : ForkChoiceNode}
    (below : (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) node.toModel)
    {children : List ForkChoiceNode} (childrenOk : store.getNodeChildren node = .ok children)
    {child : ForkChoiceNode} :
    child.toModel ∈ Models.ForkChoice.children (nodeView lower nodes) node.toModel ↔
      child ∈ children.filter (· ∈ nodes) := by
  have closed := filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
    fun _ _ _ ok _ mem => isChild_of_mem_getNodeChildren gloas ok mem
  simp only [Models.ForkChoice.mem_children, nodeView, View.mem_ofBlocks, List.mem_filter,
    decide_eq_true_eq, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨_, ⟨m, mMem, rfl⟩, above⟩, isChild⟩
    obtain ⟨c, cMem, same⟩ := (closed m mMem).2 _ (below.trans isChild.ancestor) above
    rw [← ForkChoiceNode.toModel_injective same] at cMem
    -- The child is not the start of the viable nodes, which sits above its parent.
    obtain ⟨-, -, parent⟩ := filterNodeTree_mem tree child cMem
    rcases parent with start | ⟨p, -, pChildren, pChildrenOk, childIn⟩
    · rw [start] at isChild
      exact absurd below.height_le (Nat.not_le_of_lt isChild.height_lt)
    have pChild := isChild_of_mem_getNodeChildren (lower := lower) gloas pChildrenOk childIn
    obtain rfl : p = node := ForkChoiceNode.toModel_injective (pChild.2.symm.trans isChild.2)
    rw [childrenOk, Except.ok.injEq] at pChildrenOk
    exact ⟨pChildrenOk ▸ childIn, cMem⟩
  · rintro ⟨childMem, inNodes⟩
    exact ⟨⟨_, ⟨child, inNodes, rfl⟩, .refl _⟩,
      isChild_of_mem_getNodeChildren gloas childrenOk childMem⟩

/-- The order of nodes in a tie in the model: by root as bytes, then by status. -/
abbrev nodeOrder : Option Root × Status → Lex (ℕ × ℕ) :=
  nodeKey rootValue

/-- From Gloas, the walk of the store ends where LMD-GHOST over nodes ends.

No viable node may be a payload decision of the previous slot, and the boost must not apply.

It starts from a node in the subtree of the pending node of the justified block. -/
theorem getHeadFrom_eq_ghost_of_gloas {nodes : List ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config nodes start = .ok head →
      ghost (voters state) (balanceAt state) (nodeView lower nodes) nodeOrder start.toModel =
        head.toModel := by
  intro start
  induction start using getHeadFrom.induct store with
  | _ start ih =>
  intro head below walk
  rw [getHeadFrom] at walk
  cases found : store.heaviestChild config nodes start with
  | error e => simp [found, bind, Except.bind] at walk
  | ok result =>
  obtain ⟨children, weighted, childrenOk, weightedOk, choice⟩ := heaviestChild_eq found
  -- Every child of the view is the node of a node of the store.
  have isNode : ∀ c ∈ Models.ForkChoice.children (nodeView lower nodes) start.toModel,
      ∃ child : ForkChoiceNode, c = child.toModel := by
    intro c mem
    obtain ⟨-, isChild⟩ := Models.ForkChoice.mem_children.mp mem
    obtain ⟨r, s⟩ := c
    have known : r ≠ none := by
      rcases s with _ | x
      · exact fun none => isChild.1 (by rw [none]; rfl)
      · have := (Prod.mk.inj (payloadTree_isChild_some.mp isChild)).1
        rw [← this]
        exact Option.some_ne_none _
    obtain ⟨root, rfl⟩ := Option.ne_none_iff_exists'.mp known
    obtain ⟨child, same⟩ := ForkChoiceNode.exists_toModel root s
    exact ⟨child, same.symm⟩
  cases result with
  | none =>
    simp only [found, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at walk
    subst walk
    rw [chooseHeaviest_eq_none] at choice
    subst choice
    have empty := List.length_eq_zero_iff.mp (mapM_ok_length weightedOk).symm
    refine ghost_of_not_nonempty _ _ _ _ fun ⟨c, mem⟩ => ?_
    obtain ⟨child, rfl⟩ := isNode c mem
    have := (mem_children_nodeView gloas tree below childrenOk).mp mem
    rw [empty] at this
    cases this
  | some child =>
    simp only [found, bind, Except.bind] at walk
    split at walk
    swap
    · cases walk
    obtain ⟨childKey, chosen, largest⟩ := chooseHeaviest_some choice
    obtain ⟨source, sourceMem, sourceOk⟩ := mapM_ok_mem weightedOk _ chosen
    obtain ⟨same, -, -⟩ := weighNode_ok_iff.mp sourceOk
    replace same : source = child := same.symm
    subst same
    have inView : source.toModel ∈ Models.ForkChoice.children (nodeView lower nodes)
        start.toModel :=
      (mem_children_nodeView gloas tree below childrenOk).mpr sourceMem
    -- A weighed child is known, weighs its model weight, and breaks ties by its status number.
    have weighed : ∀ c ∈ children.filter (· ∈ nodes), ∀ {y : WeightedNode},
        store.weighNode config c = .ok y →
        toLex (y.2.1.toNat, toLex (rootValue (some y.1.root), y.2.2.toNat)) =
          toLex (weight (voters state) (balanceAt state) (nodeView lower nodes) c.toModel,
            nodeOrder c.toModel) := by
      intro c cMem y yOk
      obtain ⟨-, inNodes⟩ := List.mem_filter.mp cMem
      replace inNodes : c ∈ nodes := of_decide_eq_true inNodes
      obtain ⟨yNode, yWeight, yTie⟩ := weighNode_ok_iff.mp yOk
      obtain ⟨-, ⟨block, cFound⟩, -⟩ := filterNodeTree_mem tree c inNodes
      rw [getWeight_eq_weight_of_gloas (lower := lower) gloas noBoost (noDecision c inNodes)
        justifiedState cFound nodes yWeight]
      simp only [tiebreaker, gloas, ↓reduceDIte,
        getPayloadStatusTiebreaker_of_not_decision (noDecision c inNodes), Except.ok.injEq]
        at yTie
      rw [← yTie, yNode, PayloadStatus.code_toNat]
      rfl
    -- The chosen child is above every other child, by weight, then by root and status.
    have largestModel : ∀ c ∈ Models.ForkChoice.children (nodeView lower nodes) start.toModel,
        toLex (weight (voters state) (balanceAt state) (nodeView lower nodes) c, nodeOrder c) ≤
          toLex (weight (voters state) (balanceAt state) (nodeView lower nodes) source.toModel,
            nodeOrder source.toModel) := by
      intro c mem
      obtain ⟨other, rfl⟩ := isNode c mem
      have otherMem := (mem_children_nodeView gloas tree below childrenOk).mp mem
      obtain ⟨y, yMem, otherOk⟩ := exists_mem_of_mapM_ok weightedOk otherMem
      have le := toLex_le_of_compareWeighted_tiebreaker (largest _ yMem)
      rwa [weighed other otherMem otherOk, weighed source sourceMem sourceOk] at le
    have injective : Set.InjOn nodeOrder
        (Models.ForkChoice.children (nodeView lower nodes) start.toModel) := by
      intro a aMem b bMem same
      obtain ⟨na, rfl⟩ := isNode a aMem
      obtain ⟨nb, rfl⟩ := isNode b bMem
      obtain ⟨roots, codes⟩ := Prod.ext_iff.mp (toLex.injective same)
      have rootsEq := rootValue_some_injective roots
      have statuses : na.payloadStatus = nb.payloadStatus := by
        have := codes
        simp only [ForkChoiceNode.toModel] at this
        rw [← PayloadStatus.code_toNat, ← PayloadStatus.code_toNat] at this
        cases h : na.payloadStatus <;> cases h' : nb.payloadStatus <;> simp_all [PayloadStatus.code]
      simp [ForkChoiceNode.toModel, rootsEq, statuses]
    have step : (nodeTree lower).parent source.toModel = start.toModel :=
      (isChild_of_mem_getNodeChildren gloas childrenOk (List.mem_filter.mp sourceMem).1).2
    rw [ghost_of_nonempty _ _ _ _ ⟨_, inView⟩,
      Models.ForkChoice.heaviestChild_eq inView largestModel injective]
    exact ih source ‹_› (below.trans ⟨1, step⟩) walk

variable (lower) in
/-- From Gloas, the head of the store is the head of LMD-GHOST over nodes.

No viable node may be a payload decision of the previous slot, and the boost must not apply.

Each known block must sit at a later slot than its known parent, and some node must be viable.

The model starts at the pending node of the justified block, over the view of the viable nodes.

Its voters are the validators active and not slashed in the justified state.

Its stakes are their effective balances, and an equivocator has no vote.

A tie goes to the greater root, as bytes, then to the greater status number. -/
theorem getHead_eq_ghost_of_gloas {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (found : store.getHead config = .ok head) :
    ghost (voters state) (balanceAt state) (nodeView lower nodes) nodeOrder
      (some store.justifiedCheckpoint.root, none) = head.toModel := by
  have notEmpty : ¬ (.glamsterdam ≤ fork ∧ nodes.isEmpty = true) :=
    fun ⟨_, empty⟩ => someViable (List.isEmpty_iff.mp empty)
  simp only [getHead, tree, notEmpty, ↓reduceIte, bind, Except.bind] at found
  exact getHeadFrom_eq_ghost_of_gloas gloas noBoost noDecision justifiedState tree (.refl _) found

end Store

end EthLib.Consensus
