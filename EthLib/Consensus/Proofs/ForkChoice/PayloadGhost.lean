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

The theorem holds away from the payload decisions of the previous slot.

There the payload committee and the proposer decide, which the model leaves out.

When the store applies the boost, it counts as one more vote.

That vote is for the pending node of the boosted block.

A viable boosted block whose parent is from the previous slot is left out.

The empty or full node of that parent is then a viable payload decision of the previous slot.

A tie between two children goes to the greater root, then to the greater status number.

Take a viable node whose votes exceed half of the sum of the stake and the score of the boost.

Those votes leave out the boost.

The head then descends from it.

That holds away from the payload decisions of the previous slot.
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

variable {tally : Except ForkChoiceError VoteTally}

/-- From Gloas, a known node weighs its weight in the model of nodes.

The node must not be a payload decision of the previous slot, and the boost must not apply.

The weights read a tally of the votes of the given state. -/
theorem getWeight_eq_weight_of_gloas {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {weightValue : Gwei} (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (decision : store.isPreviousSlotPayloadDecision config node = .ok false)
    (tallied : tally = .ok (store.tallyVotes state))
    (found : store.blocks[node.root]? = some block) (nodes : List ForkChoiceNode)
    (computed : store.getWeight config tally node = .ok weightValue) :
    weightValue.toNat =
      weight (voters state) (balanceAt state) (nodeView lower nodes) node.toModel := by
  rw [getWeight_of_not_boost gloas decision noBoost, tallied] at computed
  exact getAttestationScore_eq_weight_of_gloas gloas found nodes computed

variable (store config) in
/-- From Gloas, the pending node of the boosted block, when the boost applies.

The boost applies when the store says so.

When that check fails, the model has no boost.

Then the weight of each node that is not a payload decision of the previous slot fails too. -/
def boostedNode (gloas : .glamsterdam ≤ fork) : Option (Option Root × Status) :=
  match store.shouldApplyProposerBoost config gloas with
  | .ok true => some (some store.proposerBoostRoot, none)
  | _ => none

variable (store config) in
/-- From Gloas, the score of the boost as a stake: the proposer score, from the justified state.

It is 0 when the boost does not apply.

It is also 0 when the proposer score fails.

Then the weight of each node in the chain of the boosted block fails.

A payload decision of the previous slot is the exception.

So the head fails when the walk weighs such a node; otherwise no weight reads the score. -/
def boostScoreOfGloas (gloas : .glamsterdam ≤ fork) : ℕ :=
  match store.shouldApplyProposerBoost config gloas, store.getProposerScore config with
  | .ok true, .ok score => score.toNat
  | _, _ => 0

/-- From Gloas, a known node weighs its weight in the model of nodes with the boost.

The node must not be a payload decision of the previous slot.

The boost is a vote for the pending node of the boosted block.

Its stake is the score of the boost.

The weights read a tally of the votes of the given state. -/
theorem getWeight_eq_weight_withBoost_of_gloas {node : ForkChoiceNode}
    {block : BeaconBlock preset fork} {weightValue : Gwei} (gloas : .glamsterdam ≤ fork)
    (decision : store.isPreviousSlotPayloadDecision config node = .ok false)
    (tallied : tally = .ok (store.tallyVotes state))
    (found : store.blocks[node.root]? = some block) (nodes : List ForkChoiceNode)
    (computed : store.getWeight config tally node = .ok weightValue) :
    weightValue.toNat =
      weight (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((nodeView lower nodes).withBoost (store.boostedNode config gloas)) node.toModel := by
  rw [weight_withBoost]
  cases boost : store.shouldApplyProposerBoost config gloas with
  | error e =>
    cases votes : store.scoreFromTally (store.tallyVotes state) node <;>
      simp [getWeight, gloas, decision, tallied, votes, boost, bind, Except.bind] at computed
  | ok applies =>
  cases applies with
  | false =>
    rw [getWeight_eq_weight_of_gloas (lower := lower) gloas boost decision tallied found
      nodes computed]
    simp [boostedNode, boost]
  | true =>
  cases votes : store.scoreFromTally (store.tallyVotes state) node with
  | error e =>
    simp [getWeight, gloas, decision, tallied, votes, bind, Except.bind] at computed
  | ok votesValue =>
  rw [← getAttestationScore_eq_weight_of_gloas (lower := lower) gloas found nodes votes]
  cases check : store.isAncestor ⟨store.proposerBoostRoot, .pending⟩ node with
  | error e =>
    simp [getWeight, gloas, decision, tallied, votes, boost, check, bind, Except.bind]
      at computed
  | ok result =>
  -- The boost counts exactly when the pending node of the boosted block descends from the node.
  have counts : (∃ m, store.boostedNode config gloas = some m ∧
      (nodeTree lower).Ancestor node.toModel m) ↔ result = true := by
    rw [isAncestor_iff_of_gloas (lower := lower) gloas found check]
    simp [boostedNode, boost, ForkChoiceNode.toModel, PayloadStatus.toStatus]
  cases result with
  | false =>
    simp only [Bool.false_eq_true, iff_false] at counts
    simp [getWeight, gloas, decision, tallied, votes, boost, check, bind, Except.bind,
      pure, Except.pure, Except.mapError] at computed
    cases add : Uint64.addChecked votesValue 0 with
    | error e => simp [add] at computed
    | ok sum =>
      simp only [add, Except.ok.injEq] at computed
      subst computed
      rw [(Uint64.addChecked_ok_iff.mp add).2, ite_eq_right counts]
      rfl
  | true =>
    simp only [iff_true] at counts
    simp [getWeight, gloas, decision, tallied, votes, boost, check, bind, Except.bind,
      Except.mapError] at computed
    cases score : store.getProposerScore config with
    | error e => simp [score] at computed
    | ok scoreValue =>
    cases add : Uint64.addChecked votesValue scoreValue with
    | error e => simp [score, add] at computed
    | ok sum =>
      simp only [score, add, Except.ok.injEq] at computed
      subst computed
      rw [(Uint64.addChecked_ok_iff.mp add).2, ite_eq_left counts, boostScoreOfGloas, boost, score]

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

That holds in any model of its weights.

The model has the blocks of the view.

Each viable node weighs in the model what the store computes.

No viable node may be a payload decision of the previous slot.

The walk starts from a node in the subtree of the pending node of the justified block. -/
private theorem getHeadFrom_eq_ghost_of_gloas_of_weights {ν : Type} {V : Finset ν} {w : ν → ℕ}
    {G : View ν (Option Root × Status) (nodeTree lower)} {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (blocks : G.blocks = (nodeView lower nodes).blocks)
    (weighs : ∀ {node : ForkChoiceNode} {weightValue : Gwei}, node ∈ nodes →
      store.getWeight config tally node = .ok weightValue →
        weightValue.toNat = weight V w G node.toModel) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config tally nodes start = .ok head →
      ghost V w G nodeOrder start.toModel = head.toModel := by
  -- The model has the children of the view.
  have sameChildren : ∀ b, Models.ForkChoice.children G b =
      Models.ForkChoice.children (nodeView lower nodes) b := by
    intro b
    unfold Models.ForkChoice.children
    rw [blocks]
  intro start
  induction start using getHeadFrom.induct store with
  | _ start ih =>
  intro head below walk
  rw [getHeadFrom] at walk
  cases found : store.heaviestChild config tally nodes start with
  | error e => simp [found, bind, Except.bind] at walk
  | ok result =>
  obtain ⟨children, weighted, childrenOk, weightedOk, choice⟩ := heaviestChild_eq found
  -- Every child of the view is the node of a node of the store.
  have isNode : ∀ c ∈ Models.ForkChoice.children G start.toModel,
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
    have := (mem_children_nodeView gloas tree below childrenOk).mp (sameChildren _ ▸ mem)
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
    have inView : source.toModel ∈ Models.ForkChoice.children G start.toModel := by
      rw [sameChildren]
      exact (mem_children_nodeView gloas tree below childrenOk).mpr sourceMem
    -- A weighed child is known, weighs its model weight, and breaks ties by its status number.
    have weighed : ∀ c ∈ children.filter (· ∈ nodes), ∀ {y : WeightedNode},
        store.weighNode config tally c = .ok y →
        toLex (y.2.1.toNat, toLex (rootValue (some y.1.root), y.2.2.toNat)) =
          toLex (weight V w G c.toModel, nodeOrder c.toModel) := by
      intro c cMem y yOk
      obtain ⟨-, inNodes⟩ := List.mem_filter.mp cMem
      replace inNodes : c ∈ nodes := of_decide_eq_true inNodes
      obtain ⟨yNode, yWeight, yTie⟩ := weighNode_ok_iff.mp yOk
      rw [weighs inNodes yWeight]
      simp only [tiebreaker, gloas, ↓reduceDIte,
        getPayloadStatusTiebreaker_of_not_decision (noDecision c inNodes), Except.ok.injEq]
        at yTie
      rw [← yTie, yNode, PayloadStatus.code_toNat]
      rfl
    -- The chosen child is above every other child, by weight, then by root and status.
    have largestModel : ∀ c ∈ Models.ForkChoice.children G start.toModel,
        toLex (weight V w G c, nodeOrder c) ≤
          toLex (weight V w G source.toModel, nodeOrder source.toModel) := by
      intro c mem
      obtain ⟨other, rfl⟩ := isNode c mem
      have otherMem := (mem_children_nodeView gloas tree below childrenOk).mp (sameChildren _ ▸ mem)
      obtain ⟨y, yMem, otherOk⟩ := exists_mem_of_mapM_ok weightedOk otherMem
      have le := toLex_le_of_compareWeighted_tiebreaker (largest _ yMem)
      rwa [weighed other otherMem otherOk, weighed source sourceMem sourceOk] at le
    have injective : Set.InjOn nodeOrder (Models.ForkChoice.children G start.toModel) := by
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

/-- From Gloas, the walk of the store ends where LMD-GHOST over nodes ends.

No viable node may be a payload decision of the previous slot, and the boost must not apply.

It starts from a node in the subtree of the pending node of the justified block.

The weights read a tally of the votes of the given state. -/
theorem getHeadFrom_eq_ghost_of_gloas {nodes : List ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (tallied : tally = .ok (store.tallyVotes state))
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config tally nodes start = .ok head →
      ghost (voters state) (balanceAt state) (nodeView lower nodes) nodeOrder start.toModel =
        head.toModel :=
  getHeadFrom_eq_ghost_of_gloas_of_weights gloas noDecision tree rfl fun inNodes computed =>
    have ⟨_, ⟨_, found⟩, _⟩ := filterNodeTree_mem tree _ inNodes
    getWeight_eq_weight_of_gloas gloas noBoost (noDecision _ inNodes) tallied found nodes
      computed

/-- From Gloas, the walk of the store ends where LMD-GHOST over nodes with the boost ends.

No viable node may be a payload decision of the previous slot.

The boost is a vote for the pending node of the boosted block.

Its stake is the score of the boost.

It starts from a node in the subtree of the pending node of the justified block.

The weights read a tally of the votes of the given state. -/
theorem getHeadFrom_eq_ghost_withBoost_of_gloas {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (tallied : tally = .ok (store.tallyVotes state))
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config tally nodes start = .ok head →
      ghost (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((nodeView lower nodes).withBoost (store.boostedNode config gloas)) nodeOrder
        start.toModel = head.toModel :=
  getHeadFrom_eq_ghost_of_gloas_of_weights
    (G := (nodeView lower nodes).withBoost (store.boostedNode config gloas)) gloas noDecision tree
    rfl fun inNodes computed =>
    have ⟨_, ⟨_, found⟩, _⟩ := filterNodeTree_mem tree _ inNodes
    getWeight_eq_weight_withBoost_of_gloas gloas (noDecision _ inNodes) tallied found nodes
      computed

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
  exact getHeadFrom_eq_ghost_of_gloas gloas noBoost noDecision
    (justifiedTally_of_state justifiedState) tree (.refl _) found

variable (lower) in
/-- From Gloas, the head of the store is the head of LMD-GHOST over nodes with the boost.

No viable node may be a payload decision of the previous slot.

So a viable boosted block must not build on a block of the previous slot.

Each known block must sit at a later slot than its known parent, and some node must be viable.

The model starts at the pending node of the justified block, over the view of the viable nodes.

Its voters are the validators active and not slashed in the justified state.

Its stakes are their effective balances, and an equivocator has no vote.

The boost is one more vote, for the pending node of the boosted block.

Its stake is the score of the boost.

When the boost does not apply, that vote is absent.

A tie goes to the greater root, as bytes, then to the greater status number. -/
theorem getHead_eq_ghost_withBoost_of_gloas {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (found : store.getHead config = .ok head) :
    ghost (voters state).insertNone
      (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
      ((nodeView lower nodes).withBoost (store.boostedNode config gloas)) nodeOrder
      (some store.justifiedCheckpoint.root, none) = head.toModel := by
  have notEmpty : ¬ (.glamsterdam ≤ fork ∧ nodes.isEmpty = true) :=
    fun ⟨_, empty⟩ => someViable (List.isEmpty_iff.mp empty)
  simp only [getHead, tree, notEmpty, ↓reduceIte, bind, Except.bind] at found
  exact getHeadFrom_eq_ghost_withBoost_of_gloas gloas noDecision
    (justifiedTally_of_state justifiedState) tree (.refl _) found

/-! ## Every payload present -/

variable (lower) in
/-- The view of the blocks of the given nodes, their ancestors, and the block of each vote.

A vote is the block of the node that the store gives it.

So a vote for a block that the store does not hold is no vote here.

The view before Gloas keeps such a vote, and differs from this one only there. -/
noncomputable def blockView (nodes : List ForkChoiceNode) :
    View ℕ (Option Root) (blockTree lower) :=
  View.ofBlocks (nodes.map (some ·.root)).toFinset fun i => (store.latestNode i.toUInt64).map (·.1)

/-- When every known block builds on the full node of its known parent, every root does. -/
theorem buildsOnFull_of_full
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (root : Option Root) : store.buildsOnFull root = true := by
  rcases root with _ | root
  · rfl
  simp only [buildsOnFull]
  split
  · rename_i block found
    split
    · rename_i parent parentFound
      simp [fullParents root block parent found parentFound]
    · rfl
  · rfl

/-- From Gloas no vote supports an empty node when each later vote says the payload is present. -/
theorem latestNode_ne_empty (gloas : .glamsterdam ≤ fork)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (index : ValidatorIndex) (root : Option Root) :
    store.latestNode index ≠ some (root, some false) := by
  intro vote
  simp only [latestNode] at vote
  split at vote
  · cases vote
  cases message : store.latestMessages[index]? with
  | none => simp [message] at vote
  | some message' =>
  simp only [message, Option.bind_some] at vote
  cases found : store.blocks[message'.root]? with
  | none => simp [getSupportedNode_of_unknown gloas found, Except.toOption] at vote
  | some block =>
  by_cases later : block.slot < message'.slot gloas
  · simp [getSupportedNode_of_lt_slot gloas found later, present index message' block message found
      later, Except.toOption, ForkChoiceNode.toModel, PayloadStatus.toStatus] at vote
  · simp [getSupportedNode_of_same_slot gloas found (UInt64.not_lt.mp later), Except.toOption,
      ForkChoiceNode.toModel, PayloadStatus.toStatus] at vote

/-- From Gloas, the head of a model of nodes is the full node of the head of a model of blocks.

The model of nodes has the blocks of the view of nodes.

The model of blocks has the blocks of the view of blocks.

A vote of the model of blocks is the block of the vote of the model of nodes.

No vote of the model of nodes is for an empty node.

Every known block builds on the full node of its known parent.

The full node of each viable block is viable, and some node is viable. -/
private theorem ghost_full_of_gloas {ν : Type} {V : Finset ν} {w : ν → ℕ}
    {N : View ν (Option Root × Status) (nodeTree lower)}
    {G : View ν (Option Root) (blockTree lower)} {nodes : List ForkChoiceNode}
    {head : ForkChoiceNode}
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (fullViable : ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes)
    (nodeBlocks : N.blocks = (nodeView lower nodes).blocks)
    (blockBlocks : G.blocks = (blockView lower nodes).blocks)
    (hvote : ∀ v r, N.latest v ≠ some (r, some false))
    (hlatest : ∀ v, G.latest v = (N.latest v).map Prod.fst)
    (model : ghost V w N nodeOrder (some store.justifiedCheckpoint.root, none) = head.toModel) :
    head.payloadStatus = .full ∧
      some head.root = ghost V w G rootValue (some store.justifiedCheckpoint.root) := by
  have hfull : ∀ r, r ≠ (blockTree lower).genesis → store.buildsOnFull r = true :=
    fun r _ => buildsOnFull_of_full fullParents r
  -- The order of roots is injective away from the common root.
  have hroot : Set.InjOn rootValue {r | r ≠ (blockTree lower).genesis} := by
    rintro (_ | a) ha (_ | b) hb same
    · rfl
    · exact (ha rfl).elim
    · exact (hb rfl).elim
    · rw [rootValue_some_injective same]
  -- A pending node is in the view of nodes exactly when its block is in the view of blocks.
  have hpending : ∀ r, (r, none) ∈ N.blocks ↔ r ∈ G.blocks := by
    intro r
    simp only [nodeBlocks, blockBlocks, nodeView, blockView, View.mem_ofBlocks, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro ⟨_, ⟨m, mMem, rfl⟩, above⟩
      exact ⟨_, ⟨m, mMem, rfl⟩, payloadTree_ancestor_fst above⟩
    · rintro ⟨_, ⟨m, mMem, rfl⟩, above⟩
      exact ⟨_, ⟨m, mMem, rfl⟩, payloadTree_ancestor_none_of above⟩
  -- The full node of each block of the view is in the view of nodes.
  have hpayload : ∀ r ∈ G.blocks, (r, some true) ∈ N.blocks := by
    intro r mem
    simp only [blockBlocks, blockView, View.mem_ofBlocks, List.mem_toFinset, List.mem_map] at mem
    obtain ⟨_, ⟨m, mMem, rfl⟩, above⟩ := mem
    simp only [nodeBlocks, nodeView, View.mem_ofBlocks, List.mem_toFinset, List.mem_map]
    by_cases same : r = some m.root
    · exact ⟨_, ⟨⟨m.root, .full⟩, fullViable m mMem, rfl⟩, by rw [same]; exact .refl _⟩
    · -- A child of the block in the chain of the vote hangs under its full node.
      obtain ⟨c, isChild, below⟩ := above.exists_child same
      have parent : (nodeTree lower).parent (c, none) = (r, some true) := by
        rw [nodeTree, payloadTree_parent_none isChild.1, isChild.2, hfull c isChild.1]
      exact ⟨_, ⟨m, mMem, rfl⟩,
        Ancestor.trans ⟨1, parent⟩ (payloadTree_ancestor_none_of (b := m.toModel) below)⟩
  have justified : some store.justifiedCheckpoint.root ∈ G.blocks := by
    simp only [blockBlocks, blockView, View.mem_ofBlocks, List.mem_toFinset, List.mem_map]
    exact ⟨_, ⟨_, filterNodeTree_self tree someViable, rfl⟩, .refl _⟩
  have full : ghost V w N nodeOrder (some store.justifiedCheckpoint.root, none) =
      (ghost V w G rootValue (some store.justifiedCheckpoint.root), some true) :=
    ghost_payloadTree _ _ hroot hfull hpending hpayload hvote hlatest justified
  rw [full] at model
  obtain ⟨roots, status⟩ := Prod.mk.inj model
  exact ⟨PayloadStatus.toStatus_injective (status.symm.trans rfl), roots.symm⟩

/-- From Gloas, when every payload is present, the head is the full node of the head over blocks.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

That view reads each vote as the block of the node that the store gives it.

Every known block builds on the full node of its known parent.

Each vote from a later slot than its block says the payload is present.

The full node of each viable block is viable.

No viable node is a payload decision of the previous slot, and the boost does not apply.

Some node is viable. -/
theorem getHead_eq_ghost_full_of_gloas {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (fullViable : ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state) (balanceAt state) (blockView lower nodes) rootValue
        (some store.justifiedCheckpoint.root) :=
  ghost_full_of_gloas fullParents tree someViable fullViable rfl rfl
    (fun v r => latestNode_ne_empty gloas present v.toUInt64 r) (fun _ => rfl)
    (getHead_eq_ghost_of_gloas lower gloas noBoost noDecision justifiedState tree someViable found)

/-- From Gloas, when every payload is present, the head is a full node.

Its root is the head over blocks with the boost.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

That view reads each vote as the block of the node that the store gives it.

When the boost applies, it is one more vote, for the boosted block.

Its stake is the score of the boost.

Every known block builds on the full node of its known parent.

Each vote from a later slot than its block says the payload is present.

The full node of each viable block is viable.

No viable node is a payload decision of the previous slot.

Some node is viable. -/
theorem getHead_eq_ghost_full_withBoost_of_gloas {nodes : List ForkChoiceNode}
    {head : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (fullViable : ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((blockView lower nodes).withBoost ((store.boostedNode config gloas).map Prod.fst))
        rootValue (some store.justifiedCheckpoint.root) := by
  refine ghost_full_of_gloas fullParents tree someViable fullViable rfl rfl ?_ ?_
    (getHead_eq_ghost_withBoost_of_gloas lower gloas noDecision justifiedState tree someViable
      found)
  · -- The boost is a vote for a pending node.
    rintro (_ | v) r vote
    · simp [View.withBoost, boostedNode] at vote
      split at vote <;> simp_all
    · exact latestNode_ne_empty gloas present v.toUInt64 r vote
  · rintro (_ | v) <;> rfl

/-- One step of the walk over the viable nodes, from the children of its start.

Without children the start counts alone, if it is a viable leaf.

With children each child ranks lower, and its viable nodes join those of the start.

The start comes last, after some viable node of a child. -/
private theorem filterNodeTree_cases {node : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes) :
    ∃ children, store.getNodeChildren node = .ok children ∧
      ((children = [] ∧ ∃ isViable, store.isViableLeaf config node = .ok isViable ∧
          nodes = if isViable then [node] else []) ∨
        (children ≠ [] ∧ ∃ viable : List ForkChoiceNode,
          (∀ child ∈ children, ∃ below, store.nodeRank child < store.nodeRank node ∧
            store.filterNodeTree config child = .ok below ∧ ∀ y ∈ below, y ∈ viable) ∧
          (∀ y ∈ viable, ∃ child ∈ children, ∃ below,
            store.nodeRank child < store.nodeRank node ∧
            store.filterNodeTree config child = .ok below ∧ y ∈ below) ∧
          ((viable = [] ∧ nodes = []) ∨ (viable ≠ [] ∧ nodes = viable ++ [node])))) := by
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  refine ⟨children, childrenOk, ?_⟩
  by_cases empty : children.isEmpty
  · simp only [empty, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨isViable, viableOk, rfl⟩ := walk
    exact .inl ⟨List.isEmpty_iff.mp empty, isViable, viableOk, rfl⟩
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at walk
  obtain ⟨viable, viableOk, rfl⟩ := walk
  refine .inr ⟨fun none => by simp [none] at empty, viable, ?_, ?_, ?_⟩
  · intro child childMem
    obtain ⟨below, belowOk⟩ := flatMapM_ok_of_mem viableOk child childMem
    split at belowOk
    · rename_i lowerRank
      exact ⟨below, lowerRank, belowOk, fun y hy => (mem_of_flatMapM_ok viableOk y).mpr
        ⟨child, childMem, below, by simp [lowerRank, belowOk], hy⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  · intro y hy
    obtain ⟨child, childMem, below, belowOk, yMem⟩ := (mem_of_flatMapM_ok viableOk y).mp hy
    split at belowOk
    · exact ⟨child, childMem, below, ‹_›, belowOk, yMem⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  · by_cases none : viable = []
    · exact .inl ⟨none, by simp [none]⟩
    · exact .inr ⟨none, by simp [none]⟩

/-- The viable nodes below a child of a node are viable nodes of that node.

The child ranks below the node. -/
private theorem filterNodeTree_sub {node child : ForkChoiceNode}
    {nodes children : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes)
    (childrenOk : store.getNodeChildren node = .ok children) (childMem : child ∈ children) :
    ∃ below, store.nodeRank child < store.nodeRank node ∧
      store.filterNodeTree config child = .ok below ∧ ∀ y ∈ below, y ∈ nodes := by
  obtain ⟨children', childrenOk', cases⟩ := filterNodeTree_cases walk
  rw [childrenOk, Except.ok.injEq] at childrenOk'
  subst childrenOk'
  rcases cases with ⟨rfl, -⟩ | ⟨-, viable, lift, -, result⟩
  · cases childMem
  obtain ⟨below, lowerRank, belowOk, sub⟩ := lift child childMem
  refine ⟨below, lowerRank, belowOk, fun y hy => ?_⟩
  rcases result with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · cases sub y hy
  · exact List.mem_append_left _ (sub y hy)

/-- A viable node of a node is that node, or a viable node below one of its children.

The viable nodes below that child are viable nodes of the node. -/
private theorem filterNodeTree_mem_cases {node n : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes) (mem : n ∈ nodes) :
    n = node ∨ ∃ children, store.getNodeChildren node = .ok children ∧ ∃ child ∈ children,
      ∃ below, store.nodeRank child < store.nodeRank node ∧
        store.filterNodeTree config child = .ok below ∧ n ∈ below ∧
        ∀ y ∈ below, y ∈ nodes := by
  obtain ⟨children, childrenOk, cases⟩ := filterNodeTree_cases walk
  rcases cases with ⟨-, isViable, -, rfl⟩ | ⟨-, viable, -, from', result⟩
  · cases isViable
    · cases mem
    · exact .inl (List.mem_singleton.mp mem)
  rcases result with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · cases mem
  rcases List.mem_append.mp mem with mem | same
  · obtain ⟨child, childMem, below, -, belowOk, nMem⟩ := from' n mem
    obtain ⟨below', lowerRank, belowOk', sub⟩ := filterNodeTree_sub walk childrenOk childMem
    rw [belowOk, Except.ok.injEq] at belowOk'
    subst belowOk'
    exact .inr ⟨children, childrenOk, child, childMem, below, lowerRank, belowOk, nMem, sub⟩
  · exact .inl (List.mem_singleton.mp same)

/-- The start of a walk that succeeds is among its viable nodes.

That holds when every node of a known block is a viable leaf. -/
private theorem filterNodeTree_self_of_viable
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true) :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes → node ∈ nodes := by
  intro node
  induction hrank : store.nodeRank node using Nat.strongRecOn generalizing node with
  | _ rank ih =>
  intro nodes walk
  obtain ⟨children, -, cases⟩ := filterNodeTree_cases walk
  rcases cases with ⟨-, isViable, viableOk, rfl⟩ | ⟨nonempty, viable', lift, -, result⟩
  · obtain ⟨block, found⟩ := filterNodeTree_known walk
    rw [viable node block found, Except.ok.injEq] at viableOk
    subst viableOk
    exact List.mem_singleton_self _
  obtain ⟨child, childMem⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨below, lowerRank, belowOk, sub⟩ := lift child childMem
  have childIn := sub child (ih _ (hrank ▸ lowerRank) rfl belowOk)
  rcases result with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · cases childIn
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- From Gloas, each viable node of a pending node has the full node of its block among them.

That holds when the store has verified the payload of every known block.

Every node of a known block must also be a viable leaf. -/
private theorem filterNodeTree_full (gloas : .glamsterdam ≤ fork)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true) :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode}, node.payloadStatus = .pending →
      store.filterNodeTree config node = .ok nodes → ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes := by
  intro node
  induction hrank : store.nodeRank node using Nat.strongRecOn generalizing node with
  | _ rank ih =>
  intro nodes pending walk n mem
  obtain ⟨block, found⟩ := filterNodeTree_known walk
  have childrenOk := getNodeChildren_of_pending (store := store) gloas pending
  simp only [verified _ block found, ↓reduceIte] at childrenOk
  -- The full node of the start is viable.
  obtain ⟨fullBelow, -, fullOk, fullSub⟩ :=
    filterNodeTree_sub walk childrenOk (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have fullIn := fullSub _ (filterNodeTree_self_of_viable viable fullOk)
  rcases filterNodeTree_mem_cases walk mem with
    rfl | ⟨children, childrenOk', child, childMem, below, lowerRank, belowOk, nMem, sub⟩
  · exact fullIn
  rw [childrenOk, Except.ok.injEq] at childrenOk'
  subst childrenOk'
  -- The child is the empty or the full node of the start.
  have childRoot : child.root = node.root ∧ child.payloadStatus ≠ .pending := by
    rcases List.mem_cons.mp childMem with rfl | childMem
    · exact ⟨rfl, by simp⟩
    · rw [List.mem_singleton.mp childMem]
      exact ⟨rfl, by simp⟩
  rcases filterNodeTree_mem_cases belowOk nMem with rfl | ⟨grand, grandOk, q, qMem, qBelow,
    qRank, qOk, nqMem, qSub⟩
  · rw [childRoot.1]
    exact fullIn
  -- A child of an empty or full node is pending, and ranks below the start.
  have qPending := ((mem_getNodeChildren_of_gloas gloas childRoot.2 grandOk).mp qMem).1
  exact sub _ (qSub _ (ih _ (hrank ▸ Nat.lt_trans qRank lowerRank) rfl qPending qOk n nqMem))

/-- The filtered tree holds the pending node of the justified block.

That holds when every node of a known block is a viable leaf. -/
theorem justified_mem_getFilteredNodeTree {nodes : List ForkChoiceNode}
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ⟨store.justifiedCheckpoint.root, .pending⟩ ∈ nodes :=
  filterNodeTree_self_of_viable viable tree

/-- From Gloas, the filtered tree holds the full node of each block that it holds.

That holds when the store has verified the payload of every known block.

Every node of a known block must also be a viable leaf. -/
theorem full_mem_getFilteredNodeTree {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes :=
  filterNodeTree_full gloas verified viable rfl tree

/-- From Gloas, when every payload is present and verified, the head is a full node.

Its root is the head over blocks.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

Every known block builds on the full node of its known parent.

The store has verified the payload of every known block.

Each vote from a later slot than its block says the payload is present.

Every node of a known block is a viable leaf.

No viable node is a payload decision of the previous slot, and the boost does not apply. -/
theorem getHead_eq_ghost_full_of_verified {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state) (balanceAt state) (blockView lower nodes) rootValue
        (some store.justifiedCheckpoint.root) := by
  have someViable := List.ne_nil_of_mem (justified_mem_getFilteredNodeTree viable tree)
  exact getHead_eq_ghost_full_of_gloas gloas fullParents present noBoost noDecision
    justifiedState tree someViable
    (full_mem_getFilteredNodeTree gloas verified viable tree) found

/-- From Gloas, when every payload is present and verified, the head is a full node.

Its root is the head over blocks with the boost.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

When the boost applies, it is one more vote, for the boosted block.

Its stake is the score of the boost.

Every known block builds on the full node of its known parent.

The store has verified the payload of every known block.

Each vote from a later slot than its block says the payload is present.

Every node of a known block is a viable leaf.

No viable node is a payload decision of the previous slot. -/
theorem getHead_eq_ghost_full_withBoost_of_verified {nodes : List ForkChoiceNode}
    {head : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((blockView lower nodes).withBoost ((store.boostedNode config gloas).map Prod.fst))
        rootValue (some store.justifiedCheckpoint.root) := by
  have someViable := List.ne_nil_of_mem (justified_mem_getFilteredNodeTree viable tree)
  exact getHead_eq_ghost_full_withBoost_of_gloas gloas fullParents present noDecision
    justifiedState tree someViable
    (full_mem_getFilteredNodeTree gloas verified viable tree) found

/-! ## A majority of votes -/

/-- From Gloas, the walk from a viable node reaches the slot of each viable ancestor.

Every block of the chain is viable, so the walk never meets an unknown parent. -/
private theorem getAncestor_ok_of_viable_ancestor_of_gloas {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {n : ℕ} {start : ForkChoiceNode}, start ∈ nodes →
      ∀ {root : Root} {rootBlock : BeaconBlock preset fork},
        (blockTree lower).parent^[n] (some start.root) = some root →
        store.blocks[root]? = some rootBlock →
        (blockTree lower).Ancestor (some store.justifiedCheckpoint.root) (some root) →
        ∃ found, store.getAncestor start rootBlock.slot = .ok found
  | 0, start, startMem, root, rootBlock, step, rootFound, _ => by
    obtain ⟨-, ⟨startBlock, startFound⟩, -⟩ := filterNodeTree_mem tree start startMem
    cases step
    rw [rootFound, Option.some.injEq] at startFound
    subst startFound
    exact ⟨_, getAncestor_of_le rootFound (UInt64.le_refl _)⟩
  | n + 1, start, startMem, root, rootBlock, step, rootFound, belowJustified => by
    obtain ⟨-, ⟨startBlock, startFound⟩, -⟩ := filterNodeTree_mem tree start startMem
    by_cases le : startBlock.slot ≤ rootBlock.slot
    · exact ⟨_, getAncestor_of_le startFound le⟩
    · rw [Function.iterate_succ_apply, blockTree_parent_of startFound] at step
      have closed := filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
        (fun _ _ _ childrenOk _ nMem => isChild_of_mem_getNodeChildren gloas childrenOk nMem)
        start startMem
      have parentAbove : (blockTree lower).Ancestor (some root) (some startBlock.parentRoot) :=
        ⟨n, step⟩
      have justifiedAbove :
          (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none)
            (some startBlock.parentRoot, none) :=
        payloadTree_ancestor_none_of (belowJustified.trans parentAbove)
      have parentAboveStart :
          (nodeTree lower).Ancestor (some startBlock.parentRoot, none) start.toModel :=
        payloadTree_ancestor_none_of ⟨1, blockTree_parent_of startFound⟩
      obtain ⟨p, pMem, pModel⟩ := closed.2 (some startBlock.parentRoot, none) justifiedAbove
        parentAboveStart
      have pRoot : p.root = startBlock.parentRoot :=
        Option.some.inj (Prod.mk.inj pModel).1.symm
      obtain ⟨-, ⟨parentBlock, parentFound⟩, -⟩ := filterNodeTree_mem tree p pMem
      rw [pRoot] at parentFound
      -- The parent node that the start block builds on lies between that parent and the start.
      have builtNode : (nodeTree lower).parent (some start.root, none) =
          (some startBlock.parentRoot,
            (parentPayloadStatus startBlock parentBlock).toStatus) := by
        rw [nodeTree_parent_of startFound parentFound,
          PayloadStatus.toStatus_of_ne_pending (parentPayloadStatus_ne_pending gloas)]
      have builtBelow :
          (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none)
            (some startBlock.parentRoot,
              (parentPayloadStatus startBlock parentBlock).toStatus) :=
        justifiedAbove.trans ⟨1, by
          simp [nodeTree, payloadTree, statusParent,
            PayloadStatus.toStatus_of_ne_pending (parentPayloadStatus_ne_pending gloas)]⟩
      have builtAbove :
          (nodeTree lower).Ancestor
            (some startBlock.parentRoot,
              (parentPayloadStatus startBlock parentBlock).toStatus) start.toModel :=
        Ancestor.trans ⟨1, builtNode⟩ (payloadTree_ancestor_none_of (.refl _))
      obtain ⟨q, qMem, qModel⟩ := closed.2 _ builtBelow builtAbove
      have qEq : q = ⟨startBlock.parentRoot, parentPayloadStatus startBlock parentBlock⟩ :=
        ForkChoiceNode.toModel_injective qModel.symm
      subst qEq
      rw [getAncestor_step startFound le parentFound
        (lower start.root startBlock parentBlock startFound parentFound)]
      exact getAncestor_ok_of_viable_ancestor_of_gloas gloas tree qMem step rootFound
        belowJustified

variable (lower) in
/-- Take a viable node whose votes exceed half of the sum of the stake and the score of the boost.

Those votes leave out the boost.

The head is then in its subtree.

That holds from Gloas, away from the payload decisions of the previous slot.

When the boost does not apply, its score is 0.

Each known block must sit at a later slot than its known parent.

A validator counts when it is active and not slashed in the justified state.

Its stake is its effective balance, and the votes of the node are counted at that node. -/
theorem ancestor_getHead_of_majority_withBoost_of_gloas {nodes : List ForkChoiceNode}
    {node head : ForkChoiceNode} {score : Gwei} (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : node ∈ nodes)
    (votes : store.getAttestationScore node state = .ok score)
    (majority : Models.stake (balanceAt state) (voters state) +
      store.boostScoreOfGloas config gloas < 2 * score.toNat)
    (found : store.getHead config = .ok head) :
    (nodeTree lower).Ancestor node.toModel head.toModel := by
  obtain ⟨-, ⟨block, nodeFound⟩, -⟩ := filterNodeTree_mem tree node viable
  have belowJustified :
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) node.toModel :=
    (filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
      (fun _ _ _ childrenOk _ nMem => isChild_of_mem_getNodeChildren gloas childrenOk nMem) node
      viable).1
  have inView : node.toModel ∈ (nodeView lower nodes).blocks := by
    simp only [nodeView, View.mem_ofBlocks, List.mem_toFinset, List.mem_map]
    exact ⟨_, ⟨node, viable, rfl⟩, .refl _⟩
  rw [getAttestationScore_eq_weight_of_gloas (lower := lower) gloas nodeFound nodes votes,
    ← stake_boostStake] at majority
  -- The boost only adds to the weight of the node.
  replace majority := majority.trans_le (Nat.mul_le_mul_left 2 ((Nat.le_add_right _ _).trans_eq
    (weight_withBoost (G := nodeView lower nodes) (store.boostedNode config gloas)
      (store.boostScoreOfGloas config gloas) _).symm))
  have model := ancestor_ghost_of_majority _ _
    ((nodeView lower nodes).withBoost (store.boostedNode config gloas)) nodeOrder inView
    belowJustified majority
  rwa [getHead_eq_ghost_withBoost_of_gloas lower gloas noDecision justifiedState tree
    (List.ne_nil_of_mem viable) found] at model

/-- Take a viable node whose votes exceed half of the sum of the stake and the score of the boost.

Those votes leave out the boost.

The head then descends from it.

The ancestor check of the store returns true from the head back to that node.

That holds from Gloas, away from the payload decisions of the previous slot.

When the boost does not apply, its score is 0.

Each known block must sit at a later slot than its known parent.

A validator counts when it is active and not slashed in the justified state.

Its stake is its effective balance, and the votes of the node are counted at that node. -/
theorem isAncestor_getHead_of_majority_withBoost_of_gloas {nodes : List ForkChoiceNode}
    {node head : ForkChoiceNode} {score : Gwei} (lower : store.ParentsBelow)
    (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : node ∈ nodes)
    (votes : store.getAttestationScore node state = .ok score)
    (majority : Models.stake (balanceAt state) (voters state) +
      store.boostScoreOfGloas config gloas < 2 * score.toNat)
    (found : store.getHead config = .ok head) :
    store.isAncestor head node = .ok true := by
  have above := ancestor_getHead_of_majority_withBoost_of_gloas lower gloas noDecision
    justifiedState tree viable votes majority found
  obtain ⟨-, ⟨nodeBlock, nodeFound⟩, -⟩ := filterNodeTree_mem tree node viable
  have belowJustified :
      (blockTree lower).Ancestor (some store.justifiedCheckpoint.root) (some node.root) :=
    payloadTree_ancestor_fst ((filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
      (fun _ _ _ childrenOk _ nMem => isChild_of_mem_getNodeChildren gloas childrenOk nMem) node
      viable).1)
  have headIn : head ∈ nodes := by
    have notEmpty : ¬ (.glamsterdam ≤ fork ∧ nodes.isEmpty = true) :=
      fun ⟨_, empty⟩ => List.ne_nil_of_mem viable (List.isEmpty_iff.mp empty)
    have headFrom := found
    simp only [getHead, tree, notEmpty, ↓reduceIte, bind, Except.bind] at headFrom
    rcases getHeadFrom_mem headFrom with rfl | mem
    · exact (filterNodeTree_mem tree node viable).1
    · exact mem
  obtain ⟨n, step⟩ := payloadTree_ancestor_fst above
  obtain ⟨ancestor, walk⟩ := getAncestor_ok_of_viable_ancestor_of_gloas (lower := lower) gloas tree
    headIn step nodeFound belowJustified
  have computed : store.isAncestor head node = .ok (ancestor.root == node.root &&
      (ancestor.payloadStatus == node.payloadStatus || node.payloadStatus == .pending)) := by
    simp [isAncestor, block_ok_iff.mpr nodeFound, gloas, walk, bind, Except.bind, pure,
      Except.pure]
  have same := (isAncestor_iff_of_gloas (lower := lower) gloas nodeFound computed).mpr above
  exact same ▸ computed

/-- From Gloas, when the boost does not apply, its score is 0. -/
theorem boostScoreOfGloas_of_not_boost {gloas : .glamsterdam ≤ fork}
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false) :
    store.boostScoreOfGloas config gloas = 0 := by
  simp [boostScoreOfGloas, noBoost]

variable (lower) in
/-- When a viable node has more than half of the stake in votes, the head is in its subtree.

That holds from Gloas, away from the payload decisions of the previous slot, and without a boost.

Each known block must sit at a later slot than its known parent.

A validator counts when it is active and not slashed in the justified state.

Its stake is its effective balance, and the votes of the node are counted at that node. -/
theorem ancestor_getHead_of_majority_of_gloas {nodes : List ForkChoiceNode}
    {node head : ForkChoiceNode} {score : Gwei} (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : node ∈ nodes)
    (votes : store.getAttestationScore node state = .ok score)
    (majority : Models.stake (balanceAt state) (voters state) < 2 * score.toNat)
    (found : store.getHead config = .ok head) :
    (nodeTree lower).Ancestor node.toModel head.toModel :=
  ancestor_getHead_of_majority_withBoost_of_gloas lower gloas noDecision justifiedState tree viable
    votes (by rw [boostScoreOfGloas_of_not_boost noBoost, Nat.add_zero]; exact majority) found

/-- When a viable node has more than half of the stake in votes, the head descends from it.

The ancestor check of the store returns true from the head back to that node.

That holds from Gloas, away from the payload decisions of the previous slot, and without a boost.

Each known block must sit at a later slot than its known parent.

A validator counts when it is active and not slashed in the justified state.

Its stake is its effective balance, and the votes of the node are counted at that node. -/
theorem isAncestor_getHead_of_majority_of_gloas {nodes : List ForkChoiceNode}
    {node head : ForkChoiceNode} {score : Gwei} (lower : store.ParentsBelow)
    (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : node ∈ nodes)
    (votes : store.getAttestationScore node state = .ok score)
    (majority : Models.stake (balanceAt state) (voters state) < 2 * score.toNat)
    (found : store.getHead config = .ok head) :
    store.isAncestor head node = .ok true :=
  isAncestor_getHead_of_majority_withBoost_of_gloas lower gloas noDecision justifiedState tree
    viable votes (by rw [boostScoreOfGloas_of_not_boost noBoost, Nat.add_zero]; exact majority)
    found

end Store

end EthLib.Consensus
