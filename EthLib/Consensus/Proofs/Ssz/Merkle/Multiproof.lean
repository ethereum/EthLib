import EthLib.Consensus.Proofs.Ssz.Merkle.HelperFrontier

/-! Multiproof reconstruction preserves the parent equations of a finite Merkle tree. -/

namespace EthLib.Consensus.Ssz

/-- Every stored node agrees with the tree at its claimed position. -/
def NodesAgree (tree : Nat → Bytes) (nodes : List (Nat × Bytes)) : Prop :=
  -- Each stored pair must match the reference reading at its own index.
  ∀ index value, (index, value) ∈ nodes → value = tree index

/-- Parent equations needed within a finite tree, with no conditions below its leaves. -/
def ParentsAgree (tree : Nat → Bytes) (height : Nat) : Prop :=
  -- Only even children inside the finite height range need parent equations.
  ∀ index, 2 ≤ index → levelOf index ≤ height → index % 2 = 0 →
    combine (tree index) (tree (index + 1)) = tree (gindexParent index)

/-- Looking up a stored node preserves agreement with the tree. -/
theorem nodeAt_agrees {tree : Nat → Bytes} {nodes : List (Nat × Bytes)}
    (agree : NodesAgree tree nodes) {index : Nat} {value : Bytes}
    (found : nodeAt nodes index = some value) : value = tree index := by
  -- The lookup returns a member whose stored index is the requested one.
  unfold nodeAt at found
  cases located : nodes.find? (fun pair => pair.1 == index) with
  | none => simp [located] at found
  | some pair =>
    have named : pair.1 = index := by simpa using List.find?_some located
    simp only [located, Option.map_some, Option.some.injEq] at found
    rw [← found, ← named]
    exact agree pair.1 pair.2 (List.mem_of_find?_eq_some located)

/-- Folding one level preserves every stored node's value in the finite tree. -/
theorem foldLevelNodes_agrees {tree : Nat → Bytes} {height depth : Nat}
    (parents : ParentsAgree tree height) (positive : 0 < depth) (bounded : depth ≤ height)
    {nodes pending : List (Nat × Bytes)} (allAgree : NodesAgree tree nodes)
    (pendingAgree : NodesAgree tree pending) {outParents outKept : List (Nat × Bytes)}
    (folded : foldLevelNodes depth nodes pending = .ok (outParents, outKept)) :
    NodesAgree tree (outParents ++ outKept) := by
  -- The induction follows the actual level worker, retaining both output groups.
  induction pending generalizing outParents outKept with
  | nil => simp_all [foldLevelNodes, NodesAgree]
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    have head : value = tree index := pendingAgree index value (by simp)
    have tail : NodesAgree tree rest := fun i v member => pendingAgree i v (by simp [member])
    simp only [foldLevelNodes] at folded
    split at folded
    · -- Shallower nodes are carried forward unchanged.
      cases rec : foldLevelNodes depth nodes rest <;>
        simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
      rcases folded with ⟨rfl, rfl⟩
      have agrees := ih tail rec
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
          have siblingAgrees := nodeAt_agrees allAgree sibling
          have parent := parents index (two_le_of_level_positive atDepth positive) (by omega) even
          cases rec : foldLevelNodes depth nodes rest <;>
            simp [sibling, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
          rcases folded with ⟨rfl, rfl⟩
          have agrees := ih tail rec
          simp only [NodesAgree, List.mem_append, List.mem_cons] at agrees ⊢
          grind
      · -- Odd nodes are consumed by their even sibling.
        split at folded
        · simp [throw] at folded
        · exact ih tail folded

/-- A successful level fold cannot change any node's tree value. -/
theorem foldLevel_agrees {tree : Nat → Bytes} {height depth : Nat}
    (parents : ParentsAgree tree height) (positive : 0 < depth) (bounded : depth ≤ height)
    {nodes folded : List (Nat × Bytes)} (agree : NodesAgree tree nodes)
    (built : foldLevel depth nodes = .ok folded) : NodesAgree tree folded := by
  -- The worker's two groups are exactly the concatenated result of the public fold.
  unfold foldLevel at built
  cases rec : foldLevelNodes depth nodes nodes <;>
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
  subst folded
  exact foldLevelNodes_agrees parents positive bounded agree agree rec

/-- Successful reconstruction returns the root of the finite tree supplying its nodes. -/
theorem foldToRoot_agrees {tree : Nat → Bytes} {height : Nat}
    (parents : ParentsAgree tree height) :
    ∀ depth, depth ≤ height → ∀ nodes, NodesAgree tree nodes → ∀ root,
      foldToRoot depth nodes = .ok root → root = tree 1 := by
  -- Each level preserves agreement, and the last lookup reads position one.
  intro depth
  induction depth with
  | zero =>
    intro _ nodes agree root built
    cases found : nodeAt nodes 1 <;> simp [foldToRoot, found] at built
    subst root
    exact nodeAt_agrees agree found
  | succ depth ih =>
    intro bounded nodes agree root built
    simp only [foldToRoot] at built
    cases folded : foldLevel (depth + 1) nodes with
    | error error => simp [folded, Bind.bind, Except.bind] at built
    | ok output =>
      simp only [folded, Bind.bind, Except.bind] at built
      exact ih (by omega) output (foldLevel_agrees parents (by omega) bounded agree folded)
        root built

/-- A stored index is found even when the list contains other positions first. -/
theorem nodeAt_exists {nodes : List (Nat × Bytes)} {index : Nat} {value : Bytes}
    (member : (index, value) ∈ nodes) : ∃ found, nodeAt nodes index = some found := by
  -- Searching skips only positions that differ from the requested index.
  induction nodes with
  | nil => simp at member
  | cons pair rest ih =>
    rcases pair with ⟨at_, stored⟩
    by_cases same : at_ = index
    · subst at_; exact ⟨stored, by simp [nodeAt]⟩
    · obtain ⟨found, located⟩ := ih (by simpa [same, Ne.symm same] using member)
      exact ⟨found, by simpa [nodeAt, same] using located⟩

/-- A successful lookup returns a pair actually present in the supplied node set. -/
theorem nodeAt_member {nodes : List (Nat × Bytes)} {index : Nat} {value : Bytes}
    (found : nodeAt nodes index = some value) : (index, value) ∈ nodes := by
  -- The search reports both membership and equality of the stored index.
  unfold nodeAt at found
  cases located : nodes.find? (fun pair => pair.1 == index) with
  | none => simp [located] at found
  | some pair =>
    have named : pair.1 = index := by simpa using List.find?_some located
    simp only [located, Option.map_some, Option.some.injEq] at found
    rw [← found, ← named]
    exact List.mem_of_find?_eq_some located

/-- Every node being folded has its sibling among the available nodes. -/
def SiblingsPresent (depth : Nat) (nodes pending : List (Nat × Bytes)) : Prop :=
  -- Every node processed at this level must find its opposite child in the complete live node set.
  ∀ index value, (index, value) ∈ pending → levelOf index = depth →
    ∃ sibling, (gindexSibling index, sibling) ∈ nodes

/-- Sibling coverage is enough for a level fold to finish without an incomplete-proof error. -/
theorem foldLevelNodes_complete {depth : Nat} {nodes pending : List (Nat × Bytes)}
    (covered : SiblingsPresent depth nodes pending) :
    ∃ parents kept, foldLevelNodes depth nodes pending = .ok (parents, kept) := by
  -- Each recursive call consumes one input node and needs only its sibling's presence.
  induction pending with
  | nil => exact ⟨[], [], rfl⟩
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    have tail : SiblingsPresent depth nodes rest :=
      fun i v member level => covered i v (by simp [member]) level
    -- The remaining nodes already produce valid parent and retained-node groups.
    obtain ⟨ps, ks, rec⟩ := ih tail
    by_cases atDepth : levelOf index = depth
    -- At the active depth, sibling coverage guarantees that pairing can proceed.
    · obtain ⟨sibling, member⟩ := covered index value (by simp) atDepth
      obtain ⟨found, located⟩ := nodeAt_exists member
      rcases Nat.mod_two_eq_zero_or_one index with even | odd
      -- An even child owns the parent hash and appends that parent to the output group.
      · obtain ⟨whole, siblingIndex⟩ := gindexSibling_even even
        have siblingIndex : gindexSibling index = index + 1 := by omega
        rw [siblingIndex] at located
        exact ⟨(gindexParent index, combine value found) :: ps, ks,
          by simp [foldLevelNodes, atDepth, even, located, rec,
            Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
      -- The matching even child owns the hash, so the odd child adds no duplicate parent.
      · obtain ⟨whole, siblingIndex⟩ := gindexSibling_odd odd
        have siblingIndex : gindexSibling index = index - 1 := by omega
        rw [siblingIndex] at located
        exact ⟨ps, ks, by simp [foldLevelNodes, atDepth, odd, located, rec]⟩
    · exact ⟨ps, (index, value) :: ks,
        by simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- A sibling-complete level always has a reconstruction result. -/
theorem foldLevel_complete {depth : Nat} {nodes : List (Nat × Bytes)}
    (covered : SiblingsPresent depth nodes nodes) :
    ∃ result, foldLevel depth nodes = .ok result := by
  -- Concatenating the two successful output groups cannot introduce an error.
  obtain ⟨parents, kept, built⟩ := foldLevelNodes_complete covered
  exact ⟨parents ++ kept,
    by simp [foldLevel, built, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- Reading any index sequence from a tree yields a node set agreeing with that tree. -/
theorem nodesAgree_zip_map (tree : Nat → Bytes) (indices : List Nat) :
    NodesAgree tree (indices.zip (indices.map tree)) := by
  -- Every pair consists of an index and precisely the value read at that index.
  induction indices with
  | nil => simp [NodesAgree]
  | cons index rest ih =>
    simp only [NodesAgree, List.map_cons, List.zip_cons_cons, List.mem_cons] at ih ⊢
    grind

/-- Two agreeing node sets can be supplied together without changing their meaning. -/
theorem NodesAgree.append {tree : Nat → Bytes} {left right : List (Nat × Bytes)}
    (leftAgree : NodesAgree tree left) (rightAgree : NodesAgree tree right) :
    NodesAgree tree (left ++ right) := by
  -- Each supplied pair originates in one of the two inputs.
  exact fun i value member => (List.mem_append.mp member).elim (leftAgree i value) (rightAgree i value)

/-- A successful multiproof reconstruction agrees with the finite tree supplying its nodes. -/
theorem calculateMultiMerkleRootUnchecked_agrees {tree : Nat → Bytes}
    {leaves proof : List Bytes} {indices helpers : List Nat}
    (helperIndices : getHelperIndices indices = .ok helpers)
    (leafValues : NodesAgree tree (indices.zip leaves))
    (proofValues : NodesAgree tree (helpers.zip proof))
    (parents : ParentsAgree tree
      (((indices.zip leaves ++ helpers.zip proof).map fun pair => levelOf pair.1).foldl max 0))
    {root : Bytes} (built : calculateMultiMerkleRootUnchecked leaves proof indices = .ok root) :
    root = tree 1 := by
  -- Length and helper checks precede the same level fold whose invariant was proved above.
  unfold calculateMultiMerkleRootUnchecked at built
  split at built
  · simp [throw, Bind.bind, Except.bind] at built
  · simp only [helperIndices, Bind.bind, Except.bind] at built
    split at built
    · simp [throw] at built
    · exact foldToRoot_agrees parents _ (Nat.le_refl _) _ (leafValues.append proofValues) _ built

/-- An accepted multiproof names the root of the finite tree supplying its nodes. -/
theorem verifyMerkleMultiproof_agrees {tree : Nat → Bytes}
    {leaves proof : List Bytes} {indices helpers : List Nat}
    (helperIndices : getHelperIndices indices = .ok helpers)
    (leafValues : NodesAgree tree (indices.zip leaves))
    (proofValues : NodesAgree tree (helpers.zip proof))
    (parents : ParentsAgree tree
      (((indices.zip leaves ++ helpers.zip proof).map fun pair => levelOf pair.1).foldl max 0))
    {root : Bytes} (accepted : verifyMerkleMultiproof leaves proof indices root = .ok true) :
    root = tree 1 := by
  -- Width checks can reject a proof, but only reconstruction can accept its root.
  unfold verifyMerkleMultiproof calculateMultiMerkleRoot at accepted
  cases reconstructed : calculateMultiMerkleRootUnchecked leaves proof indices <;>
    cases leafWidths : checkChunks leaves <;> cases proofWidths : checkChunks proof <;>
    simp [leafWidths, proofWidths, reconstructed, Bind.bind, Except.bind, Pure.pure,
      Except.pure] at accepted
  subst root
  exact calculateMultiMerkleRootUnchecked_agrees helperIndices leafValues proofValues parents reconstructed

/-- The position retained or created when a node is visited at one level. -/
def FoldedIndex (depth child index : Nat) : Prop :=
  -- Shallower positions are retained, while an even child contributes its parent position.
  (levelOf child ≠ depth ∧ index = child) ∨
    (levelOf child = depth ∧ child % 2 = 0 ∧ index = gindexParent child)

/-- The output positions are exactly the retained nodes and the parents of even nodes. -/
theorem foldLevelNodes_indices {depth : Nat} {nodes pending : List (Nat × Bytes)}
    {parents kept : List (Nat × Bytes)}
    (built : foldLevelNodes depth nodes pending = .ok (parents, kept)) :
    ∀ index, index ∈ (parents ++ kept).map Prod.fst ↔
      ∃ child ∈ pending.map Prod.fst, FoldedIndex depth child index := by
  -- Odd nodes contribute no duplicate parent because their even sibling owns the pair.
  induction pending generalizing parents kept with
  | nil => simp_all [foldLevelNodes]
  | cons pair rest ih =>
    rcases pair with ⟨child, value⟩
    by_cases atDepth : levelOf child = depth
    · rcases Nat.mod_two_eq_zero_or_one child with even | odd
      · cases sibling : nodeAt nodes (child + 1) <;> cases rec : foldLevelNodes depth nodes rest <;>
          simp [foldLevelNodes, atDepth, even, sibling, rec, throw, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at built
        rcases built with ⟨rfl, rfl⟩
        intro index
        simpa [FoldedIndex, atDepth, even, List.map_append, List.mem_append] using
          or_congr (Iff.rfl : (index = gindexParent child) ↔ _) (ih rec index)
      · cases sibling : nodeAt nodes (child - 1) <;>
          simp [foldLevelNodes, atDepth, odd, sibling, throw] at built
        intro index
        simpa [FoldedIndex, atDepth, odd] using ih built index
    · cases rec : foldLevelNodes depth nodes rest <;>
        simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
      rcases built with ⟨rfl, rfl⟩
      intro index
      simpa [FoldedIndex, atDepth, List.map_append, List.mem_append,
        or_comm, or_left_comm, or_assoc] using
        or_congr (Iff.rfl : (index = child) ↔ _) (ih rec index)

/-- One successful fold has precisely the positions prescribed by pairing its input level. -/
theorem foldLevel_indices {depth : Nat} {nodes result : List (Nat × Bytes)}
    (built : foldLevel depth nodes = .ok result) :
    ∀ index, index ∈ result.map Prod.fst ↔
      ∃ child ∈ nodes.map Prod.fst, FoldedIndex depth child index := by
  -- The public fold concatenates the worker's two output groups.
  unfold foldLevel at built
  cases rec : foldLevelNodes depth nodes nodes <;>
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
  subst result
  exact foldLevelNodes_indices rec

/-- Positions present after every deeper level has been folded. -/
def FrontierAt (indices helpers : List Nat) (depth : Nat) (nodes : List (Nat × Bytes)) : Prop :=
  -- Live positions stay above the remaining depth and retain every supplied or reconstructed node needed there.
  (∀ index ∈ nodes.map Prod.fst, levelOf index ≤ depth ∧
    (index = 1 ∨ index ∈ claimPaths indices ∨ index ∈ helpers)) ∧
  (∀ index ∈ indices ++ helpers, levelOf index ≤ depth → index ∈ nodes.map Prod.fst) ∧
  (∀ index, (index = 1 ∨ index ∈ claimPaths indices) → levelOf index = depth →
    index ∈ nodes.map Prod.fst)

/-- The deepest remaining nodes always have their siblings at the same frontier. -/
theorem FrontierAt.siblings {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {depth : Nat}
    {nodes : List (Nat × Bytes)} (frontier : FrontierAt indices helpers (depth + 1) nodes) :
    SiblingsPresent (depth + 1) nodes nodes := by
  -- A sibling is either already supplied or rebuilt by the deeper levels.
  intro index value member atDepth
  obtain ⟨_, support⟩ := frontier.1 index (List.mem_map.mpr ⟨(index, value), member, rfl⟩)
  have support : index ∈ claimPaths indices ∨ index ∈ helpers :=
    support.resolve_left fun root => by subst index; have : levelOf 1 = 0 := rfl; omega
  obtain ⟨positive, sibling, _⟩ := helperFrontier_sibling built support
  have sameDepth : levelOf (gindexSibling index) = depth + 1 :=
    (levelOf_sibling positive).trans atDepth
  have located : gindexSibling index ∈ nodes.map Prod.fst := by
    rcases sibling with path | helper
    · exact frontier.2.2 _ (Or.inr path) sameDepth
    · exact frontier.2.1 _ (List.mem_append.mpr (Or.inr helper)) (by omega)
  obtain ⟨pair, member, same⟩ := List.mem_map.mp located
  exact ⟨pair.2, by cases pair; simpa using same ▸ member⟩

/-- Folding the deepest remaining level preserves the complete proof frontier. -/
theorem FrontierAt.fold {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {depth : Nat}
    {nodes result : List (Nat × Bytes)} (frontier : FrontierAt indices helpers (depth + 1) nodes)
    (folded : foldLevel (depth + 1) nodes = .ok result) :
    FrontierAt indices helpers depth result := by
  -- Nodes below the frontier are replaced by their parents, while shallower claims remain.
  obtain ⟨-, valid, _⟩ := getHelperIndices_frontier built
  -- The output-index characterization distinguishes retained shallow nodes from newly created parents.
  have positions := foldLevel_indices folded
  refine ⟨?_, ?_, ?_⟩
  · intro index member
    obtain ⟨child, childMember, retained | joined⟩ := (positions index).mp member
    · obtain ⟨different, same⟩ := retained
      subst index
      obtain ⟨bounded, support⟩ := frontier.1 child childMember
      exact ⟨by omega, support⟩
    · obtain ⟨atDepth, _, same⟩ := joined
      subst index
      obtain ⟨_, support⟩ := frontier.1 child childMember
      have positive := two_le_of_level_positive atDepth (by omega)
      have support : child ∈ claimPaths indices ∨ child ∈ helpers :=
        support.resolve_left fun root => by subst child; have : levelOf 1 = 0 := rfl; omega
      have parent := (helperFrontier_sibling built support).2.2
      have parentDepth := levelOf_parent positive
      exact ⟨by unfold gindexParent; omega, parent.elim Or.inl (fun path => Or.inr (Or.inl path))⟩
  · intro index member bounded
    apply (positions index).mpr
    exact ⟨index, frontier.2.1 index member (by omega), Or.inl ⟨by omega, rfl⟩⟩
  · intro index inside atDepth
    by_cases claimed : index ∈ indices
    · apply (positions index).mpr
      exact ⟨index, frontier.2.1 index (List.mem_append.mpr (Or.inl claimed)) (by omega),
        Or.inl ⟨by omega, rfl⟩⟩
    · obtain ⟨left, _⟩ := helperFrontier_children built inside claimed
      have positive : 1 ≤ index :=
        inside.elim (by omega) fun path => by have := (claimPaths_bounds valid path).1; omega
      have childDepth : levelOf (2 * index) = depth + 1 :=
        (Nat.log2_two_mul (by omega)).trans (congrArg (· + 1) atDepth)
      have childMember : 2 * index ∈ nodes.map Prod.fst := by
        rcases left with path | helper
        · exact frontier.2.2 _ (Or.inr path) childDepth
        · exact frontier.2.1 _ (List.mem_append.mpr (Or.inr helper)) (by omega)
      apply (positions index).mpr
      exact ⟨2 * index, childMember, Or.inr ⟨childDepth, by omega, by unfold gindexParent; omega⟩⟩

/-- A complete frontier reaches the root without any missing sibling or missing root. -/
theorem FrontierAt.complete {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    ∀ depth nodes, FrontierAt indices helpers depth nodes →
      ∃ root, foldToRoot depth nodes = .ok root := by
  -- Sibling coverage makes each level total, and the final frontier contains position one.
  intro depth
  induction depth with
  | zero =>
    intro nodes frontier
    obtain ⟨pair, member, same⟩ := List.mem_map.mp (frontier.2.2 1 (Or.inl rfl) rfl)
    have rootMember : (1, pair.2) ∈ nodes := by cases pair; simpa using same ▸ member
    obtain ⟨root, found⟩ := nodeAt_exists rootMember
    exact ⟨root, by simp [foldToRoot, found]⟩
  | succ depth ih =>
    intro nodes frontier
    obtain ⟨result, folded⟩ := foldLevel_complete (frontier.siblings built)
    obtain ⟨root, reconstructed⟩ := ih result (frontier.fold built folded)
    exact ⟨root, by simp [foldToRoot, folded, reconstructed, Bind.bind, Except.bind]⟩

/-- The supplied claims and helpers form a complete frontier at any bounding depth. -/
theorem frontierAt_initial {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {depth : Nat}
    {nodes : List (Nat × Bytes)} (positions : nodes.map Prod.fst = indices ++ helpers)
    (bounded : ∀ index ∈ indices ++ helpers, levelOf index ≤ depth) :
    FrontierAt indices helpers depth nodes := by
  -- A path at the maximum depth must already be a claim, since strict ancestors are shallower.
  obtain ⟨nonempty, valid, _⟩ := getHelperIndices_frontier built
  obtain ⟨claim, claimed⟩ := List.exists_mem_of_ne_nil indices nonempty
  have positive : 0 < depth := by
    have claimDepth := levelOf_parent (valid claim claimed)
    have claimBound := bounded claim (List.mem_append.mpr (Or.inl claimed))
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro index member
    rw [positions] at member
    exact ⟨bounded index member, .inr ((List.mem_append.mp member).imp_left (claim_mem_paths valid))⟩
  · exact fun index member _ => positions ▸ member
  · intro index inside atDepth
    rw [positions]
    by_cases requested : index ∈ indices
    · exact List.mem_append.mpr (Or.inl requested)
    -- A purported unclaimed node at maximum depth would require an even deeper original claim.
    · obtain ⟨child, childPath, parent⟩ := claimPaths_child nonempty valid inside requested
      obtain ⟨childPositive, larger, largerClaimed, ordered⟩ := claimPaths_bounds valid childPath
      have parentDepth := levelOf_parent childPositive
      rw [parent, atDepth] at parentDepth
      have monotone := levelOf_mono (by omega) ordered
      have bound := bounded larger (List.mem_append.mpr (Or.inl largerClaimed))
      omega

/-- Accumulating a maximum never decreases its starting value. -/
theorem le_foldl_max (values : List Nat) (initial : Nat) : initial ≤ values.foldl max initial := by
  -- Each step replaces the accumulator by a value at least as large.
  induction values generalizing initial with
  | nil => exact Nat.le_refl _
  | cons value rest ih =>
    exact Nat.le_trans (Nat.le_max_left initial value) (ih (max initial value))

/-- Every listed depth is bounded by the maximum used to start reconstruction. -/
theorem member_le_foldl_max {values : List Nat} {value : Nat} (member : value ∈ values)
    (initial : Nat) : value ≤ values.foldl max initial := by
  -- Once an entry is included, subsequent maximum steps preserve its bound.
  induction values generalizing initial with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst value
      exact Nat.le_trans (Nat.le_max_right initial head) (le_foldl_max rest (max initial head))
    · exact ih member (max initial head)

/-- Correct counts and helper positions are sufficient for multiproof reconstruction to finish. -/
theorem calculateMultiMerkleRootUnchecked_complete {leaves proof : List Bytes} {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers)
    (leafCount : leaves.length = indices.length) (proofCount : proof.length = helpers.length) :
    ∃ root, calculateMultiMerkleRootUnchecked leaves proof indices = .ok root := by
  -- The initial node positions are exactly the validated claims followed by their helpers.
  let nodes := indices.zip leaves ++ helpers.zip proof
  have positions : nodes.map Prod.fst = indices ++ helpers := by
    simp only [nodes, List.map_append, List.map_fst_zip (by omega : indices.length ≤ leaves.length),
      List.map_fst_zip (by omega : helpers.length ≤ proof.length)]
  let depth := (nodes.map fun pair => levelOf pair.1).foldl max 0
  have bounded : ∀ index ∈ indices ++ helpers, levelOf index ≤ depth := by
    intro index member
    rw [← positions] at member
    obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp member
    apply member_le_foldl_max (initial := 0)
    exact List.mem_map.mpr ⟨pair, pairMember, congrArg levelOf same⟩
  -- The complete frontier supplies every sibling until only the root remains.
  obtain ⟨root, reconstructed⟩ :=
    (frontierAt_initial built positions bounded).complete built
  exact ⟨root, by simpa [calculateMultiMerkleRootUnchecked, leafCount, proofCount, built, nodes, depth,
    Bind.bind, Except.bind] using reconstructed⟩

/-- Every valid multiproof read from a finite tree reconstructs that tree's root. -/
theorem multiproof_rebuilds_root {tree : Nat → Bytes} {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers)
    (parents : ParentsAgree tree
      ((((indices.zip (indices.map tree)) ++ helpers.zip (helpers.map tree)).map
        fun pair => levelOf pair.1).foldl max 0)) :
    calculateMultiMerkleRootUnchecked (indices.map tree) (helpers.map tree) indices = .ok (tree 1) := by
  -- Frontier completeness supplies termination, and parent preservation identifies the root.
  obtain ⟨root, reconstructed⟩ := calculateMultiMerkleRootUnchecked_complete built
    (List.length_map ..) (List.length_map ..)
  have same := calculateMultiMerkleRootUnchecked_agrees built (nodesAgree_zip_map tree indices)
    (nodesAgree_zip_map tree helpers) parents reconstructed
  exact same ▸ reconstructed

/-- Reading only complete hash nodes passes the verifier's list-width check. -/
theorem checkChunks_map {tree : Nat → Bytes} {indices : List Nat}
    (widths : ∀ index ∈ indices, (tree index).size = bytesPerChunk) :
    checkChunks (indices.map tree) = .ok () := by
  -- Each node is checked independently before reconstruction begins.
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp_all [checkChunks, checkChunk, Bind.bind, Except.bind]

/-- A multiproof read from a finite tree of 32-byte nodes is accepted by the public verifier. -/
theorem multiproof_verifies {tree : Nat → Bytes} {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers)
    (parents : ParentsAgree tree
      ((((indices.zip (indices.map tree)) ++ helpers.zip (helpers.map tree)).map
        fun pair => levelOf pair.1).foldl max 0))
    (widths : ∀ index ∈ indices ++ helpers, (tree index).size = bytesPerChunk) :
    verifyMerkleMultiproof (indices.map tree) (helpers.map tree) indices (tree 1) = .ok true := by
  -- Width checks admit the nodes, and full reconstruction produces the expected root.
  have leafWidths := checkChunks_map (fun i member => widths i (List.mem_append.mpr (Or.inl member)))
  have proofWidths := checkChunks_map (fun i member => widths i (List.mem_append.mpr (Or.inr member)))
  simp [verifyMerkleMultiproof, calculateMultiMerkleRoot, leafWidths, proofWidths,
    multiproof_rebuilds_root built parents, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Two sibling claims immediately below the root require no auxiliary nodes. -/
theorem calculateMultiMerkleRootUnchecked_two_children (left right : Bytes) :
    calculateMultiMerkleRootUnchecked [left, right] [] [2, 3] = .ok (combine left right) := by
  -- Both children are already present, so their ordered hash is the complete root.
  have helpers : getHelperIndices [2, 3] = .ok [] := by
    with_unfolding_all rfl
  have two : Nat.log2 2 = 1 := by rfl
  have three : Nat.log2 3 = 1 := by rfl
  simp [calculateMultiMerkleRootUnchecked, helpers, foldToRoot, foldLevel, foldLevelNodes,
    nodeAt, levelOf, two, three, gindexParent, Bind.bind, Except.bind, Pure.pure, Except.pure]

end EthLib.Consensus.Ssz
