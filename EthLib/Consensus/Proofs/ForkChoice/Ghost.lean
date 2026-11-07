module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Consensus.Proofs.ForkChoice.Head
public import EthLib.Consensus.Proofs.Models.ForkChoice.LmdGhost

/-!
# Proofs: the head of the fork choice is LMD-GHOST

The head rule of the store is the rule of the LMD-GHOST model, before Gloas and without a boost.

The model is Algorithm 3.1 of Gasper, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

The known blocks of the store form a tree, and an unknown root hangs under a common root.

The slot of a block serves as its height, so a known parent has to sit at a lower slot.

The view holds the nodes that lead to a viable leaf, and their ancestors.

A validator counts when it is active and not slashed in the justified state.

Its stake is its effective balance, and an equivocator has no latest message.

A tie between two children goes to the greater root, read as a big-endian number.

That order is the order of roots as strings of bytes.

The head descends from the justified block.

It is a viable leaf, unless no leaf is viable, and then it is the justified block.

So when some leaf is viable, the chain of the head holds the finalized block.

That is not required when the finalized epoch is genesis.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models.ForkChoice

variable {preset : Preset} {fork : Fork}

namespace Store

variable (store : Store preset fork)

/-- Each known block whose parent is known sits at a later slot than its parent. -/
def ParentsBelow : Prop :=
  ∀ (root : Root) (block parent : BeaconBlock preset fork), store.blocks[root]? = some block →
    store.blocks[block.parentRoot]? = some parent → parent.slot < block.slot

/-- The height of a root in the tree of the store.

A known block sits at its slot plus 2, an unknown root at 1, and the common root at 0. -/
def treeHeight : Option Root → ℕ
  | none => 0
  | some root =>
    match store.blocks[root]? with
    | some block => block.slot.toNat + 2
    | none => 1

/-- The parent of a root in the tree of the store.

A known block hangs under its parent root, and an unknown root under the common root. -/
def treeParent : Option Root → Option Root
  | none => none
  | some root => store.blocks[root]?.map (·.parentRoot)

variable {store}

/-- The tree of the known blocks of a store whose parents sit at lower slots. -/
def blockTree (lower : store.ParentsBelow) : BlockTree (Option Root) where
  genesis := none
  parent := store.treeParent
  height := store.treeHeight
  parent_genesis := rfl
  height_parent := by
    rintro (_ | root) hne
    · exact absurd rfl hne
    simp only [treeParent, treeHeight]
    cases found : store.blocks[root]? with
    | none => simp
    | some block =>
      simp only [Option.map_some]
      cases parentFound : store.blocks[block.parentRoot]? with
      | none => simp
      | some parent =>
        have := UInt64.lt_iff_toNat_lt.mp (lower root block parent found parentFound)
        dsimp only
        omega

variable {lower : store.ParentsBelow}

theorem blockTree_parent_of {root : Root} {block : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block) :
    (blockTree lower).parent (some root) = some block.parentRoot := by
  simp [blockTree, treeParent, found]

theorem blockTree_height_of {root : Root} {block : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block) :
    (blockTree lower).height (some root) = block.slot.toNat + 2 := by
  simp [blockTree, treeHeight, found]

/-- A root is a child of another exactly when it is a known block with that parent root. -/
theorem blockTree_isChild_iff {child root : Root} :
    (blockTree lower).IsChild (some child) (some root) ↔
      ∃ block, store.blocks[child]? = some block ∧ block.parentRoot = root := by
  simp only [BlockTree.IsChild, blockTree, ne_eq, reduceCtorEq, not_false_eq_true, true_and,
    treeParent, Option.map_eq_some_iff]

/-- Before Gloas, the ancestor walk from a known block above the slot moves to its parent. -/
theorem getAncestor_of_gt {node : ForkChoiceNode} {slot : Slot}
    {block parent : BeaconBlock preset fork} (before : fork < .glamsterdam)
    (found : store.blocks[node.root]? = some block) (above : ¬ block.slot ≤ slot)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (parentLower : parent.slot < block.slot) :
    store.getAncestor node slot = store.getAncestor ⟨block.parentRoot, .pending⟩ slot := by
  rw [getAncestor_step found above parentFound parentLower, parentPayloadStatus_of_lt before]

/-- Before Gloas, a block whose parent descends from a node descends from it too.

That needs the parent at an earlier slot than the block. -/
theorem isAncestor_of_parent {root : Root} {block parent : BeaconBlock preset fork}
    {ancestor : ForkChoiceNode} (before : fork < .glamsterdam)
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot)
    (descends : store.isAncestor ⟨block.parentRoot, .pending⟩ ancestor = .ok true) :
    store.isAncestor ⟨root, .pending⟩ ancestor = .ok true := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [isAncestor, later, ↓reduceIte, bind, Except.bind] at descends ⊢
  cases known : store.block ancestor.root with
  | error e => simp [known] at descends
  | ok ancestorBlock =>
    simp only [known] at descends ⊢
    -- The ancestor sits at or below the parent, so the walk from the block passes the parent.
    have below : ancestorBlock.slot < block.slot := by
      by_cases le : parent.slot ≤ ancestorBlock.slot
      · rw [getAncestor_of_le parentFound le] at descends
        simp only [pure, Except.pure, Except.ok.injEq, beq_iff_eq] at descends
        have same : ancestor.root = block.parentRoot := by rw [← descends]
        simp only [Store.block, same, parentFound, pure, Except.pure, Except.ok.injEq] at known
        exact known ▸ lower
      · exact UInt64.lt_trans (UInt64.lt_iff_toNat_lt.mpr (by
          have := UInt64.le_iff_toNat_le.not.mp le; omega)) lower
    rw [getAncestor_of_gt before found (fun le => absurd (UInt64.lt_of_lt_of_le below le)
      (UInt64.lt_irrefl _)) parentFound lower]
    exact descends

/-- The ancestor walk climbs the tree of the store.

It returns the node itself or a pending node, in the chain of the start.

Every block it climbs past, strictly between the start and the result, sits above the slot. -/
theorem getAncestor_climbs {node ancestor : ForkChoiceNode} {slot : Slot}
    (before : fork < .glamsterdam) (walk : store.getAncestor node slot = .ok ancestor) :
    (blockTree lower).Ancestor (some ancestor.root) (some node.root) ∧
      (ancestor = node ∨ ancestor.payloadStatus = .pending) ∧
      ∀ a, (blockTree lower).Ancestor (some ancestor.root) a →
        (blockTree lower).Ancestor a (some node.root) → a ≠ some ancestor.root →
        ∃ root block, a = some root ∧ store.blocks[root]? = some block ∧ slot < block.slot := by
  induction node using getAncestor.induct (store := store) (slot := slot) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    rw [getAncestor_of_le found le] at walk
    cases walk
    refine ⟨.refl _, .inl rfl, fun a below above ne => absurd (below.antisymm above).symm ne⟩
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound parentLower ih =>
    rw [getAncestor_step found above parentFound parentLower] at walk
    obtain ⟨chain, status, between⟩ := ih walk
    have step : (blockTree lower).parent (some node.root) = some block.parentRoot :=
      blockTree_parent_of found
    refine ⟨chain.trans ⟨1, step⟩,
      .inr (status.elim (fun same => same ▸ parentPayloadStatus_of_lt before) id), ?_⟩
    intro a below aboveA ne
    rcases aboveA.eq_or_parent with same | aboveParent
    · exact ⟨node.root, block, same, found, Nat.lt_of_not_le above⟩
    · rw [step] at aboveParent
      exact between a below aboveParent ne
  | case5 node block found above parent parentFound notLower =>
    exact absurd (lower _ block parent found parentFound) notLower

/-- Before Gloas, a pending node descends from a known pending node exactly as in the tree. -/
theorem isAncestor_iff {root : Root} {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {result : Bool} (before : fork < .glamsterdam) (found : store.blocks[node.root]? = some block)
    (pending : node.payloadStatus = .pending)
    (computed : store.isAncestor ⟨root, .pending⟩ node = .ok result) :
    result = true ↔ (blockTree lower).Ancestor (some node.root) (some root) := by
  have known : store.block node.root = .ok block := block_ok_iff.mpr found
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [isAncestor, known, later, ↓reduceIte, bind, Except.bind] at computed
  cases walk : store.getAncestor ⟨root, .pending⟩ block.slot with
  | error e => simp [walk] at computed
  | ok ancestor =>
    simp only [walk, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    obtain ⟨chain, status, between⟩ := getAncestor_climbs (lower := lower) before walk
    obtain ⟨ancestorBlock, ancestorFound, ancestorLe⟩ := getAncestor_le walk
    have ancestorPending : ancestor.payloadStatus = .pending := status.elim (· ▸ rfl) id
    rw [beq_iff_eq]
    constructor
    · rintro rfl
      exact chain
    · intro above
      -- Both roots are in the chain of the vote, so one is in the chain of the other.
      have sameRoot : ancestor.root = node.root := by
        rcases above.total chain with low | high
        · by_contra ne
          have := low.height_lt (fun h => ne (Option.some.inj h).symm)
          rw [blockTree_height_of found, blockTree_height_of ancestorFound] at this
          exact absurd (UInt64.le_iff_toNat_le.mp ancestorLe) (by omega)
        · by_contra ne
          obtain ⟨r, b, same, rFound, rAbove⟩ :=
            between _ high above (fun h => ne (Option.some.inj h).symm)
          cases same
          rw [found, Option.some.injEq] at rFound
          subst rFound
          exact absurd rAbove (UInt64.lt_irrefl _)
      cases ancestor
      cases node
      simp_all

/-! ## Votes and weights -/

/-- Whether the validator at a position of the registry counts: it is active and not slashed. -/
def counts (state : BeaconState preset fork) (index : ℕ) : Bool :=
  match state.validators.data[index]? with
  | some validator => isActiveValidator validator (getCurrentEpoch state) && !validator.slashed
  | none => false

/-- The validators that count in a state, by their positions in the registry. -/
def voters (state : BeaconState preset fork) : Finset ℕ :=
  (Finset.range state.validators.data.size).filter (counts state ·)

/-- The stake of the validator at a position of the registry: its effective balance. -/
def balanceAt (state : BeaconState preset fork) (index : ℕ) : ℕ :=
  (state.validators.data[index]?.map (·.effectiveBalance.toNat)).getD 0

variable (store) in
/-- The latest vote of a validator, by its index, as a root of the tree.

An equivocator has none. -/
def latestVote (index : ValidatorIndex) : Option (Option Root) :=
  if store.equivocatingIndices.contains index then none
  else store.latestMessages[index]?.map (some ·.root)

variable (lower) in
/-- The view of the given nodes, their ancestors and the latest votes of the store. -/
noncomputable def view (nodes : List ForkChoiceNode) : View ℕ (Option Root) (blockTree lower) :=
  View.ofBlocks (nodes.map (some ·.root)).toFinset (store.latestVote ·.toUInt64)

/-- A sum over the selected entries of a list with their positions is a sum over the positions. -/
private theorem sum_filterMap_zipIdx {α : Type} (l : List α) (select : α × ℕ → Option ℕ) :
    (l.zipIdx.filterMap select).sum =
      ∑ i ∈ Finset.range l.length, ((l[i]?).bind fun a => select (a, i)).getD 0 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.zipIdx_append, List.filterMap_append, List.sum_append, ih, List.length_append,
      List.length_singleton, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun i mem => ?_
      rw [List.getElem?_append_left (Finset.mem_range.mp mem)]
    · cases h : select (a, l.length) <;> simp [h]

open scoped Classical in
/-- One step of the vote count adds the balance of a validator whose vote is in the subtree. -/
private theorem countStep_ok {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {total total' : ℕ} {index : ValidatorIndex} {balance : Gwei} (before : fork < .glamsterdam)
    (found : store.blocks[node.root]? = some block) (pending : node.payloadStatus = .pending)
    (step : (match store.latestMessages[index]? with
        | none => pure total
        | some message => do
          if store.equivocatingIndices.contains index then return total
          if ← store.isAncestor (← store.getSupportedNode message) node then
            return total + balance.toNat
          return total : Except ForkChoiceError ℕ) = .ok total') :
    total' = total + if ∃ m, store.latestVote index = some m ∧
      (blockTree lower).Ancestor (some node.root) m then balance.toNat else 0 := by
  cases message : store.latestMessages[index]? with
  | none =>
    simp only [message, pure, Except.pure, Except.ok.injEq] at step
    simp [latestVote, message, step]
  | some message' =>
    simp only [message] at step
    by_cases equivocating : store.equivocatingIndices.contains index
    · simp only [equivocating, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at step
      have none : store.latestVote index = none := by
        simp only [latestVote, equivocating, ↓reduceIte]
      simp [none, step]
    · simp only [equivocating, Bool.false_eq_true, ↓reduceIte, getSupportedNode_of_lt before,
        bind, Except.bind, pure, Except.pure] at step
      cases computed : store.isAncestor ⟨message'.root, .pending⟩ node with
      | error e => simp [computed] at step
      | ok result =>
        have iff := isAncestor_iff (lower := lower) before found pending computed
        simp only [computed] at step
        have vote : store.latestVote index = some (some message'.root) := by
          simp only [latestVote, equivocating, Bool.false_eq_true, ↓reduceIte, message,
            Option.map_some]
        simp only [vote, Option.some.injEq, exists_eq_left']
        cases result <;> simp_all

/-- Before Gloas, the votes for a known pending node are its weight in the model.

The voters are those that count in the given state, with their effective balances. -/
theorem getAttestationScore_eq_weight {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {state : BeaconState preset fork} {score : Gwei} (before : fork < .glamsterdam)
    (found : store.blocks[node.root]? = some block) (pending : node.payloadStatus = .pending)
    (nodes : List ForkChoiceNode) (computed : store.getAttestationScore node state = .ok score) :
    score.toNat = weight (voters state) (balanceAt state) (view lower nodes) (some node.root) := by
  classical
  -- The vote count is a sum of one term per validator that counts.
  let term : ValidatorIndex × Gwei → ℕ := fun (index, balance) =>
    if ∃ m, store.latestVote index = some m ∧ (blockTree lower).Ancestor (some node.root) m then
      balance.toNat else 0
  have sum : ∀ (entries : List (ValidatorIndex × Gwei)) (start total : ℕ),
      entries.foldlM (init := start) (fun (total : ℕ) (index, balance) =>
        match store.latestMessages[index]? with
        | none => pure total
        | some message => do
          if store.equivocatingIndices.contains index then return total
          if ← store.isAncestor (← store.getSupportedNode message) node then
            return total + balance.toNat
          return total : ℕ → ValidatorIndex × Gwei → Except ForkChoiceError ℕ) = .ok total →
      total = start + (entries.map term).sum := by
    intro entries
    induction entries with
    | nil =>
      intro start total fold
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at fold
      simp [fold]
    | cons entry rest ih =>
      intro start total fold
      rw [List.foldlM_cons, bind_ok_iff] at fold
      obtain ⟨middle, first, fold⟩ := fold
      rw [ih middle total fold, countStep_ok before found pending first, List.map_cons,
        List.sum_cons, Nat.add_assoc]
  unfold getAttestationScore at computed
  rw [bind_ok_iff] at computed
  obtain ⟨total, fold, bound⟩ := computed
  have total_eq := sum _ 0 total fold
  by_cases big : 2 ^ 64 ≤ total
  · have big' : 18446744073709551616 ≤ total := big
    simp [big', throw, throwThe, MonadExceptOf.throw] at bound
  simp only [big, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at bound
  subst bound
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega), total_eq, Nat.zero_add]
  -- Both sides sum over the positions of the registry.
  simp only [weight, Models.stake, supporters, voters, Finset.sum_filter, unslashedActiveBalances,
    List.map_filterMap, sum_filterMap_zipIdx, Array.length_toList]
  refine Finset.sum_congr rfl fun i mem => ?_
  rw [Array.getElem?_toList]
  cases validator : state.validators.data[i]? with
  | none => simp [counts, validator]
  | some v =>
    by_cases active : (isActiveValidator v (getCurrentEpoch state) && !v.slashed) = true
    · have active' : isActiveValidator v (getCurrentEpoch state) = true ∧ v.slashed = false := by
        simpa using active
      simp [counts, validator, active', term, balanceAt, view, View.ofBlocks]
    · have active' : ¬(isActiveValidator v (getCurrentEpoch state) = true ∧ v.slashed = false) := by
        simpa using active
      simp [counts, validator, active']

/-! ## The viable nodes -/

/-- Viable nodes below a pending node come with that node.

Every other viable node is a known pending block whose parent is viable too. -/
theorem filterNodeTree_parent {config : Config} (before : fork < .glamsterdam) :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      node.payloadStatus = .pending → store.filterNodeTree config node = .ok nodes →
      ∀ n ∈ nodes, node ∈ nodes ∧ (n = node ∨ n.payloadStatus = .pending ∧
        ∃ block, store.blocks[n.root]? = some block ∧ ⟨block.parentRoot, .pending⟩ ∈ nodes) := by
  intro node
  induction hrank : store.nodeRank node using Nat.strong_induction_on generalizing node with
  | _ rank ih =>
  intro nodes pending walk n mem
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  by_cases empty : children.isEmpty
  · simp only [empty, ↓reduceIte, bind, Except.bind] at walk
    cases viable : store.isViableLeaf config node with
    | error e => simp [viable] at walk
    | ok isViable =>
      simp only [viable, pure, Except.pure, Except.ok.injEq] at walk
      subst walk
      cases isViable
      · cases mem
      · rw [List.mem_singleton.mp mem]
        exact ⟨List.mem_singleton_self _, .inl rfl⟩
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at walk
  obtain ⟨viable, viableOk, walk⟩ := walk
  simp only [pure, Except.pure, Except.ok.injEq] at walk
  subst walk
  by_cases none : viable.isEmpty
  · simp [none] at mem
  simp only [none, Bool.false_eq_true, ↓reduceIte] at mem ⊢
  refine ⟨List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
  rcases List.mem_append.mp mem with mem | mem
  rotate_left
  · exact .inl (List.mem_singleton.mp mem)
  · obtain ⟨child, childMem, below, belowOk, belowMem⟩ :=
      (mem_of_flatMapM_ok viableOk n).mp mem
    split at belowOk
    · rename_i lowerRank
      obtain ⟨childPending, block, childFound, parentRoot⟩ :=
        (mem_getNodeChildren before childrenOk).mp childMem
      obtain ⟨childIn, parent⟩ :=
        ih _ (hrank ▸ lowerRank) rfl childPending belowOk n belowMem
      -- Each node below the child is in the viable list of the node.
      have lift : ∀ x ∈ below, x ∈ viable :=
        fun x hx => (mem_of_flatMapM_ok viableOk x).mpr ⟨child, childMem, below, by
          simp [lowerRank, belowOk], hx⟩
      rcases parent with rfl | ⟨nPending, nBlock, nFound, nParent⟩
      · refine .inr ⟨childPending, block, childFound, List.mem_append_right _ ?_⟩
        rw [parentRoot]
        cases node
        simp_all
      · exact .inr ⟨nPending, nBlock, nFound, List.mem_append_left _ (lift _ nParent)⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk

/-- The viable nodes below a pending node lie in its subtree.

Every block between that node and a viable node is viable too. -/
theorem filterNodeTree_ancestor {config : Config} {node : ForkChoiceNode}
    {nodes : List ForkChoiceNode} (before : fork < .glamsterdam)
    (pending : node.payloadStatus = .pending)
    (walk : store.filterNodeTree config node = .ok nodes) :
    ∀ n ∈ nodes, (blockTree lower).Ancestor (some node.root) (some n.root) ∧
      ∀ a, (blockTree lower).Ancestor (some node.root) a →
        (blockTree lower).Ancestor a (some n.root) → ∃ m ∈ nodes, a = some m.root := by
  intro n
  induction hheight : (blockTree lower).height (some n.root) using Nat.strong_induction_on
    generalizing n with
  | _ height ih =>
  intro mem
  obtain ⟨-, parent⟩ := filterNodeTree_parent before pending walk n mem
  rcases parent with rfl | ⟨-, block, found, parentMem⟩
  · exact ⟨.refl _, fun a below above => ⟨n, mem, (below.antisymm above).symm⟩⟩
  have step : (blockTree lower).parent (some n.root) = some block.parentRoot :=
    blockTree_parent_of found
  have lowerHeight : (blockTree lower).height (some block.parentRoot) < height := by
    rw [← hheight, ← step]
    exact (blockTree lower).height_parent _ (Option.some_ne_none _)
  obtain ⟨chain, between⟩ := ih _ lowerHeight ⟨block.parentRoot, .pending⟩ rfl parentMem
  refine ⟨chain.trans ⟨1, step⟩, fun a below above => ?_⟩
  rcases above.eq_or_parent with rfl | above
  · exact ⟨n, mem, rfl⟩
  · rw [step] at above
    exact between a below above

/-- A viable node with no viable child is a viable leaf. -/
theorem filterNodeTree_leaf {config : Config} :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes →
      ∀ n ∈ nodes, ∀ {children : List ForkChoiceNode}, store.getNodeChildren n = .ok children →
        (∀ child ∈ children, child ∉ nodes) → store.isViableLeaf config n = .ok true := by
  intro node
  induction hrank : store.nodeRank node using Nat.strong_induction_on generalizing node with
  | _ rank ih =>
  intro nodes walk n mem leafChildren leafOk leaf
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  by_cases empty : children.isEmpty
  · simp only [empty, ↓reduceIte, bind_ok_iff] at walk
    obtain ⟨isViable, viable, walk⟩ := walk
    simp only [pure, Except.pure, Except.ok.injEq] at walk
    subst walk
    cases isViable
    · cases mem
    · rw [List.mem_singleton.mp mem]
      exact viable
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at walk
  obtain ⟨viable, viableOk, walk⟩ := walk
  simp only [pure, Except.pure, Except.ok.injEq] at walk
  subst walk
  have nonempty : viable ≠ [] := fun nil => by simp [nil] at mem
  have nodesEq : (if viable.isEmpty then [] else viable ++ [node]) = viable ++ [node] := by
    simp [List.isEmpty_iff, nonempty]
  rw [nodesEq] at mem leaf
  -- Each node below a child of the start is a viable node of the start.
  have below : ∀ x ∈ viable, ∃ child ∈ children, ∃ nodesBelow,
      store.nodeRank child < store.nodeRank node ∧
      store.filterNodeTree config child = .ok nodesBelow ∧ x ∈ nodesBelow ∧
      ∀ y ∈ nodesBelow, y ∈ viable := by
    intro x hx
    obtain ⟨child, childMem, nodesBelow, belowOk, xMem⟩ := (mem_of_flatMapM_ok viableOk x).mp hx
    split at belowOk
    · rename_i lowerRank
      refine ⟨child, childMem, nodesBelow, lowerRank, belowOk, xMem, fun y hy => ?_⟩
      exact (mem_of_flatMapM_ok viableOk y).mpr ⟨child, childMem, nodesBelow, by
        simp [lowerRank, belowOk], hy⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  rcases List.mem_append.mp mem with mem | same
  · obtain ⟨child, -, nodesBelow, lowerRank, belowOk, nMem, lift⟩ := below n mem
    exact ih _ (hrank ▸ lowerRank) rfl belowOk n nMem leafOk
      fun c hc inBelow => leaf c hc (List.mem_append_left _ (lift c inBelow))
  · -- The start has a viable child, so it is no leaf of the viable nodes.
    rw [List.mem_singleton.mp same, childrenOk, Except.ok.injEq] at leafOk
    subst leafOk
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨child, childMem, nodesBelow, -, belowOk, xMem, lift⟩ := below x hx
    have childIn := filterNodeTree_self belowOk (List.ne_nil_of_mem xMem)
    exact absurd (List.mem_append_left _ (lift child childIn)) (leaf child childMem)

/-- A viable leaf agrees with the finalized checkpoint.

Its checkpoint block at the finalized epoch is the finalized block, unless that epoch is genesis. -/
theorem isViableLeaf_finalized {config : Config} {node : ForkChoiceNode}
    (viable : store.isViableLeaf config node = .ok true) :
    store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
      store.getCheckpointBlock node.root store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root := by
  unfold isViableLeaf at viable
  simp only [bind_ok_iff] at viable
  obtain ⟨_, -, _, -, viable⟩ := viable
  -- Both branches of the justified check end with the finalized check.
  have checked : ∃ checkpointBlock,
      store.getCheckpointBlock node.root store.finalizedCheckpoint.epoch = .ok checkpointBlock ∧
        (store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
          store.finalizedCheckpoint.root = checkpointBlock) := by
    split at viable <;>
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true,
        Bool.or_eq_true, decide_eq_true_eq] at viable
    · obtain ⟨_, -, checkpointBlock, checkpointOk, -, finalized⟩ := viable
      exact ⟨checkpointBlock, checkpointOk, finalized⟩
    · obtain ⟨_, -, _, -, checkpointBlock, checkpointOk, -, finalized⟩ := viable
      exact ⟨checkpointBlock, checkpointOk, finalized⟩
  obtain ⟨checkpointBlock, checkpointOk, finalized⟩ := checked
  rcases finalized with genesis | same
  · exact .inl genesis
  · exact .inr (same ▸ checkpointOk)

/-! ## The order of roots -/

/-- A root read as a big-endian number, and the common root of the tree as 0. -/
def rootValue : Option Root → ℕ
  | none => 0
  | some root => bytesToNat root.toList

/-- Two roots compare, as strings of bytes, as their big-endian numbers. -/
theorem compare_eq_compare_rootValue (a b : Root) :
    compare a b = compare (rootValue (some a)) (rootValue (some b)) := by
  show Vector.compareLex compare a b = _
  rw [Vector.compareLex_eq_compareLex_toList]
  exact compare_eq_compare_bytesToNat (by simp)

/-- Two roots with one number are equal. -/
theorem rootValue_some_injective {a b : Root} (h : rootValue (some a) = rootValue (some b)) :
    a = b := by
  have ha := natToBytes_bytesToNat a.toList
  have hb := natToBytes_bytesToNat b.toList
  simp only [Vector.length_toList] at ha hb
  simp only [rootValue] at h
  exact Vector.toList_inj.mp (by rw [← ha, ← hb, h])

private theorem _root_.UInt64.compare_eq_compare_toNat (a b : UInt64) :
    compare a b = compare a.toNat b.toNat := by
  simp only [compare, compareOfLessAndEq, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]

/-- A weighted node at least as large as another is at least as large in the order of the model. -/
theorem toLex_le_of_compareWeighted {x y : WeightedNode}
    (ge : (compareWeighted x y).isGE) :
    toLex (y.2.1.toNat, rootValue (some y.1.root)) ≤
      toLex (x.2.1.toNat, rootValue (some x.1.root)) := by
  simp only [compareWeighted, compareLex, compareOn, UInt64.compare_eq_compare_toNat,
    compare_eq_compare_rootValue] at ge
  generalize x.2.1.toNat = a, y.2.1.toNat = b, rootValue (some x.1.root) = c,
    rootValue (some y.1.root) = d at ge ⊢
  rw [Prod.Lex.toLex_le_toLex]
  rcases Nat.lt_trichotomy a b with lt | rfl | gt
  · rw [Nat.compare_eq_lt.mpr lt] at ge
    cases ge
  · rw [Nat.compare_eq_eq.mpr rfl] at ge
    refine .inr ⟨rfl, ?_⟩
    rcases Nat.lt_trichotomy c d with lt | rfl | gt
    · rw [Nat.compare_eq_lt.mpr lt] at ge
      cases ge
    · exact Nat.le_refl _
    · exact Nat.le_of_lt gt
  · exact .inl gt

/-! ## The head -/

/-- The output of a successful map at an input is in the outputs. -/
private theorem mem_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β} {x : α} {y : β},
      xs.mapM f = .ok ys → x ∈ xs → f x = .ok y → y ∈ ys
  | [], _, _, _, _, mem, _ => by cases mem
  | x' :: xs, ys, x, y, h, mem, ok => by
    obtain ⟨y', rest, first, restOk, rfl⟩ := mapM_cons_ok.mp h
    rcases List.mem_cons.mp mem with rfl | mem
    · rw [first, Except.ok.injEq] at ok
      exact ok ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mapM_ok restOk mem ok)

variable {config : Config} {state : BeaconState preset fork}

/-- Before Gloas and without a boost, the weight of a known pending node is its weight in the model.
-/
theorem getWeight_eq_weight {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {weightValue : Gwei} (before : fork < .glamsterdam)
    (noBoost : store.proposerBoostRoot = Vector.replicate 32 0)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (found : store.blocks[node.root]? = some block) (pending : node.payloadStatus = .pending)
    (nodes : List ForkChoiceNode) (computed : store.getWeight config node = .ok weightValue) :
    weightValue.toNat =
      weight (voters state) (balanceAt state) (view lower nodes) (some node.root) := by
  rw [getWeight_of_no_boost before noBoost, justifiedState] at computed
  exact getAttestationScore_eq_weight before found pending nodes computed

/-- The children of a node of the subtree of the justified block, in the view and in the store.

A root is a child in the view exactly when its pending node is a viable child in the store. -/
theorem mem_children_view {nodes : List ForkChoiceNode} (before : fork < .glamsterdam)
    (tree : store.getFilteredNodeTree config = .ok nodes) {node : ForkChoiceNode}
    (below : (blockTree lower).Ancestor (some store.justifiedCheckpoint.root) (some node.root))
    {children : List ForkChoiceNode} (childrenOk : store.getNodeChildren node = .ok children)
    {root : Root} :
    some root ∈ Models.ForkChoice.children (view lower nodes) (some node.root) ↔
      ⟨root, .pending⟩ ∈ children.filter (· ∈ nodes) := by
  have closed := filterNodeTree_ancestor (lower := lower) before rfl tree
  have pendingNodes := filterNodeTree_parent before rfl tree
  simp only [Models.ForkChoice.mem_children, view, View.mem_ofBlocks, blockTree_isChild_iff,
    List.mem_filter, mem_getNodeChildren before childrenOk, decide_eq_true_eq, List.mem_toFinset,
    List.mem_map]
  constructor
  · rintro ⟨⟨_, ⟨n, nMem, rfl⟩, above⟩, block, found, parent⟩
    have step : (blockTree lower).parent (some root) = some node.root := by
      rw [blockTree_parent_of found, parent]
    obtain ⟨m, mMem, same⟩ := (closed n nMem).2 _ (below.trans ⟨1, step⟩) above
    cases same
    have mPending : m.payloadStatus = .pending := by
      rcases (pendingNodes m mMem).2 with rfl | ⟨mPending, -⟩
      · rfl
      · exact mPending
    refine ⟨⟨trivial, block, found, parent⟩, ?_⟩
    cases m
    simp_all
  · rintro ⟨⟨-, block, found, parent⟩, inNodes⟩
    exact ⟨⟨_, ⟨_, inNodes, rfl⟩, .refl _⟩, block, found, parent⟩

/-- Before Gloas and without a boost, the walk of the store ends where LMD-GHOST ends.

It starts from a pending node in the subtree of the justified block. -/
theorem getHeadFrom_eq_ghost {nodes : List ForkChoiceNode} (before : fork < .glamsterdam)
    (noBoost : store.proposerBoostRoot = Vector.replicate 32 0)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {start head : ForkChoiceNode}, start.payloadStatus = .pending →
      (blockTree lower).Ancestor (some store.justifiedCheckpoint.root) (some start.root) →
      store.getHeadFrom config nodes start = .ok head →
      ghost (voters state) (balanceAt state) (view lower nodes) rootValue (some start.root) =
        some head.root := by
  intro start
  induction start using getHeadFrom.induct store with
  | _ start ih =>
  intro head pending below walk
  rw [getHeadFrom] at walk
  cases found : store.heaviestChild config nodes start with
  | error e => simp [found, bind, Except.bind] at walk
  | ok result =>
  obtain ⟨children, weighted, childrenOk, weightedOk, choice⟩ := heaviestChild_eq found
  -- Every child of the view is the root of a pending node.
  have isSome : ∀ c ∈ Models.ForkChoice.children (view lower nodes) (some start.root),
      ∃ root, c = some root := by
    intro c mem
    obtain ⟨-, notGenesis, -⟩ := Models.ForkChoice.mem_children.mp mem
    exact Option.ne_none_iff_exists'.mp notGenesis
  cases result with
  | none =>
    simp only [found, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at walk
    subst walk
    rw [chooseHeaviest_eq_none] at choice
    subst choice
    have empty := List.length_eq_zero_iff.mp (mapM_ok_length weightedOk).symm
    refine ghost_of_not_nonempty _ _ _ _ fun ⟨c, mem⟩ => ?_
    obtain ⟨root, rfl⟩ := isSome c mem
    have := (mem_children_view before tree below childrenOk).mp mem
    rw [empty] at this
    cases this
  | some child =>
    simp only [found, bind, Except.bind] at walk
    split at walk
    swap
    · cases walk
    obtain ⟨childKey, chosen, largest⟩ := chooseHeaviest_some choice
    obtain ⟨source, sourceMem, sourceOk⟩ := mapM_ok_mem weightedOk _ chosen
    obtain ⟨same, childOk, -⟩ := weighNode_ok_iff.mp sourceOk
    replace same : source = child := same.symm
    subst same
    obtain ⟨childMem, -⟩ := List.mem_filter.mp sourceMem
    have sourceIn := sourceMem
    obtain ⟨childPending, block, childFound, parent⟩ :=
      (mem_getNodeChildren before childrenOk).mp childMem
    have childNode : source = ⟨source.root, .pending⟩ := by
      cases source
      simp_all
    have step : (blockTree lower).parent (some source.root) = some start.root := by
      rw [blockTree_parent_of childFound, parent]
    have inView : some source.root ∈ Models.ForkChoice.children (view lower nodes)
        (some start.root) :=
      (mem_children_view before tree below childrenOk).mpr (childNode ▸ sourceIn)
    -- The chosen child is above every other child, by weight and then by root.
    have largestModel : ∀ c ∈ Models.ForkChoice.children (view lower nodes) (some start.root),
        toLex (weight (voters state) (balanceAt state) (view lower nodes) c, rootValue c) ≤
          toLex (weight (voters state) (balanceAt state) (view lower nodes) (some source.root),
            rootValue (some source.root)) := by
      intro c mem
      obtain ⟨root, rfl⟩ := isSome c mem
      have other := (mem_children_view before tree below childrenOk).mp mem
      obtain ⟨y, otherOk⟩ := mapM_ok_of_mem weightedOk _ other
      have yMem := mem_of_mapM_ok weightedOk other otherOk
      obtain ⟨otherMem, -⟩ := List.mem_filter.mp other
      obtain ⟨-, otherBlock, otherFound, -⟩ := (mem_getNodeChildren before childrenOk).mp otherMem
      obtain ⟨yNode, weighed, -⟩ := weighNode_ok_iff.mp otherOk
      have le := toLex_le_of_compareWeighted (largest _ yMem)
      rw [yNode] at le
      dsimp only at le
      rwa [getWeight_eq_weight before noBoost justifiedState otherFound rfl nodes weighed,
        getWeight_eq_weight before noBoost justifiedState childFound childPending nodes childOk]
        at le
    have injective : Set.InjOn rootValue
        (Models.ForkChoice.children (view lower nodes) (some start.root)) := by
      intro a aMem b bMem same
      obtain ⟨ra, rfl⟩ := isSome a aMem
      obtain ⟨rb, rfl⟩ := isSome b bMem
      rw [rootValue_some_injective same]
    rw [ghost_of_nonempty _ _ _ _ ⟨_, inView⟩,
      Models.ForkChoice.heaviestChild_eq inView largestModel injective]
    exact ih source ‹_› childPending (below.trans ⟨1, step⟩) walk

/-- Before Gloas, the head is a pending node. -/
theorem getHead_pending {head : ForkChoiceNode} (before : fork < .glamsterdam)
    (found : store.getHead config = .ok head) : head.payloadStatus = .pending := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getHead, later, false_and, ↓reduceIte, bind, Except.bind] at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree] at found
  | ok nodes =>
    simp only [tree] at found
    rcases getHeadFrom_mem found with rfl | mem
    · rfl
    · rcases (filterNodeTree_parent before rfl tree head mem).2 with rfl | ⟨pending, -⟩
      · rfl
      · exact pending

/-- Before Gloas, the walk from a pending node ends at a node that descends from what it does. -/
theorem getHeadFrom_descends {nodes : List ForkChoiceNode} {ancestor : ForkChoiceNode}
    (before : fork < .glamsterdam) :
    ∀ {start head : ForkChoiceNode}, start.payloadStatus = .pending →
      store.isAncestor start ancestor = .ok true →
      store.getHeadFrom config nodes start = .ok head →
      store.isAncestor head ancestor = .ok true := by
  intro start
  induction start using getHeadFrom.induct store with
  | _ start ih =>
  intro head pending descends walk
  rw [getHeadFrom] at walk
  cases found : store.heaviestChild config nodes start with
  | error e => simp [found, bind, Except.bind] at walk
  | ok result =>
  cases result with
  | none =>
    simp only [found, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at walk
    exact walk ▸ descends
  | some child =>
    simp only [found, bind, Except.bind] at walk
    split at walk
    swap
    · cases walk
    rename_i lowerRank
    obtain ⟨children, weighted, childrenOk, weightedOk, choice⟩ := heaviestChild_eq found
    obtain ⟨_, chosen, -⟩ := chooseHeaviest_some choice
    obtain ⟨source, sourceMem, sourceOk⟩ := mapM_ok_mem weightedOk _ chosen
    have same : source = child := (weighNode_ok_iff.mp sourceOk).1.symm
    subst same
    obtain ⟨childPending, block, childFound, parent⟩ :=
      (mem_getNodeChildren before childrenOk).mp (List.mem_filter.mp sourceMem).1
    -- A node that has a child of lower rank is a known block below that child.
    cases startFound : store.blocks[start.root]? with
    | none => simp [nodeRank, startFound] at lowerRank
    | some startBlock =>
    have lower : startBlock.slot < block.slot := by
      simp only [nodeRank, childFound, startFound, childPending, pending, ↓reduceIte] at lowerRank
      have := block.slot.toNat_lt
      have := startBlock.slot.toNat_lt
      exact UInt64.lt_iff_toNat_lt.mpr (by omega)
    have startNode : start = ⟨block.parentRoot, .pending⟩ := by
      rw [parent, ← pending]
    have childNode : source = ⟨source.root, .pending⟩ := by
      rw [← childPending]
    have parentFound : store.blocks[block.parentRoot]? = some startBlock := by
      rw [parent]
      exact startFound
    have step := isAncestor_of_parent before childFound parentFound lower (startNode ▸ descends)
    exact ih source lowerRank childPending (childNode ▸ step) walk

/-- Before Gloas, the head descends from the justified block, which counts as its own descendant.
-/
theorem getHead_descends {head : ForkChoiceNode} (before : fork < .glamsterdam)
    (found : store.getHead config = .ok head) :
    store.isAncestor head ⟨store.justifiedCheckpoint.root, .pending⟩ = .ok true := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getHead, later, false_and, ↓reduceIte, bind, Except.bind] at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree] at found
  | ok nodes =>
    simp only [tree] at found
    obtain ⟨_, known⟩ := filterNodeTree_known tree
    exact getHeadFrom_descends before rfl (isAncestor_self known) found

/-- The head is a viable leaf, or no leaf is viable and the head is a node of the justified block.

That node is pending before Gloas, and empty from Gloas. -/
theorem getHead_viable {head : ForkChoiceNode} (found : store.getHead config = .ok head) :
    store.isViableLeaf config head = .ok true ∨
      store.getFilteredNodeTree config = .ok [] ∧ head = ⟨store.justifiedCheckpoint.root,
        if .glamsterdam ≤ fork then .empty else .pending⟩ := by
  obtain ⟨nodes, children, tree, childrenOk, leaf⟩ := getHead_leaf found
  simp only [getHead, tree, bind, Except.bind] at found
  split at found
  · rename_i empty
    simp only [pure, Except.pure, Except.ok.injEq] at found
    rw [List.isEmpty_iff.mp empty.2] at tree
    exact .inr ⟨tree, by simp [← found, empty.1]⟩
  · rename_i notEmpty
    rcases getHeadFrom_mem found with same | mem
    · cases nodes with
      | nil =>
        have later : ¬ .glamsterdam ≤ fork := fun gloas => notEmpty ⟨gloas, rfl⟩
        exact .inr ⟨tree, by simp [same, later]⟩
      | cons first rest =>
        -- A nonempty list of viable nodes holds the justified block.
        have justified := filterNodeTree_self tree (List.cons_ne_nil first rest)
        exact .inl (filterNodeTree_leaf tree head (same ▸ justified) childrenOk leaf)
    · exact .inl (filterNodeTree_leaf tree head mem childrenOk leaf)

/-- The head agrees with the finalized checkpoint when some leaf is viable.

Its checkpoint block at the finalized epoch is the finalized block, unless that epoch is genesis. -/
theorem getHead_finalized {head : ForkChoiceNode} (found : store.getHead config = .ok head)
    (someViable : store.getFilteredNodeTree config ≠ .ok []) :
    store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
      store.getCheckpointBlock head.root store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root :=
  isViableLeaf_finalized ((getHead_viable found).resolve_right fun ⟨noLeaf, _⟩ => someViable noLeaf)

variable (lower) in
/-- Before Gloas and without a boost, the head of the store is the head of LMD-GHOST.

Each known block must sit at a later slot than its known parent.

The model starts at the justified block, over the view of the viable nodes.

Its voters are the validators active and not slashed in the justified state.

Its stakes are their effective balances, and an equivocator has no vote.

A tie goes to the greater root, as bytes. -/
theorem getHead_eq_ghost {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (before : fork < .glamsterdam) (noBoost : store.proposerBoostRoot = Vector.replicate 32 0)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (found : store.getHead config = .ok head) :
    ghost (voters state) (balanceAt state) (view lower nodes) rootValue
      (some store.justifiedCheckpoint.root) = some head.root := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getHead, later, false_and, ↓reduceIte, tree, bind, Except.bind] at found
  exact getHeadFrom_eq_ghost before noBoost justifiedState tree rfl (.refl _) found

end Store

end EthLib.Consensus
