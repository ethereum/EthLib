import EthLib.Consensus.Proofs.Ssz.Merkle.MultiproofTree

/-! Collision witnesses can be located in the hashes executed by multiproof reconstruction. -/

namespace EthLib.Consensus.Ssz

/-- The inputs hashed by the even nodes owning pairs at one reconstruction level. -/
def levelMessages (depth : Nat) (nodes : List (Nat × Bytes)) : List Bytes :=
  -- Only an even node at the current depth executes a hash.
  nodes.flatMap fun (index, value) =>
    if levelOf index = depth ∧ index % 2 = 0 then
      match nodeAt nodes (index + 1) with
      | some sibling => [value ++ sibling]
      | none => []
    else []

/-- Hash inputs encountered by the actual level folds. -/
def multiproofMessages : Nat → List (Nat × Bytes) → List Bytes
  | 0, _ => []
  | depth + 1, nodes =>
    -- Record this level, then follow the exact node set passed to the next fold.
    levelMessages (depth + 1) nodes ++
      match foldLevel (depth + 1) nodes with
      | .ok result => multiproofMessages depth result
      | .error _ => []

private theorem levelMessages_member {depth index : Nat} {nodes : List (Nat × Bytes)}
    {value sibling : Bytes} (member : (index, value) ∈ nodes)
    (atDepth : levelOf index = depth) (even : index % 2 = 0)
    (found : nodeAt nodes (index + 1) = some sibling) :
    value ++ sibling ∈ levelMessages depth nodes := by
  -- An even node with its right sibling contributes exactly this concatenation to the level trace.
  apply List.mem_flatMap.mpr
  exact ⟨(index, value), member, by simp [atDepth, even, found]⟩

/-- Every hash beneath a currently stored subtree has already appeared in the trace. -/
def MessagesCovered (trees : Nat → CommitmentTree) (nodes : List (Nat × Bytes))
    (trace : List Bytes) : Prop :=
  -- Every internal hash below a live node must already occur in the accumulated trace.
  ∀ index value, (index, value) ∈ nodes → ∀ message ∈ (trees index).messages, message ∈ trace

private theorem foldLevelNodes_covered {trees : Nat → CommitmentTree} {depth : Nat}
    {nodes pending : List (Nat × Bytes)} {trace : List Bytes}
    (included : ∀ pair ∈ pending, pair ∈ nodes)
    (parents : ∀ index value, (index, value) ∈ pending → levelOf index = depth →
      index % 2 = 0 → trees (gindexParent index) = .fork (trees index) (trees (index + 1)))
    (agree : NodesAgree (fun i => (trees i).root) nodes)
    (covered : MessagesCovered trees nodes trace)
    {outParents outKept : List (Nat × Bytes)}
    (folded : foldLevelNodes depth nodes pending = .ok (outParents, outKept)) :
    MessagesCovered trees (outParents ++ outKept) (levelMessages depth nodes ++ trace) := by
  -- Each parent adds its own hash to the previously covered hashes of both children.
  induction pending generalizing outParents outKept with
  | nil =>
    simp only [foldLevelNodes, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at folded
    rcases folded with ⟨rfl, rfl⟩
    simp [MessagesCovered]
  | cons pair rest ih =>
    obtain ⟨index, value⟩ := pair
    have inNodes := included (index, value) List.mem_cons_self
    have later := @ih (fun pair member => included pair (List.mem_cons_of_mem _ member))
      (fun i v member => parents i v (List.mem_cons_of_mem _ member))
    simp only [foldLevelNodes] at folded
    split at folded
    · -- Retained nodes inherit their already covered subtree messages.
      cases rec : foldLevelNodes depth nodes rest <;>
        simp [rec, Bind.bind, Except.bind, pure, Except.pure] at folded
      rcases folded with ⟨rfl, rfl⟩
      intro i v member message hashed
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with member | same | member
      · exact later rec i v (by simp [member]) message hashed
      · cases same
        exact List.mem_append_right _ (covered _ _ inNodes _ hashed)
      · exact later rec i v (by simp [member]) message hashed
    · rename_i atDepth
      replace atDepth : levelOf index = depth := by simpa using atDepth
      split at folded
      · rename_i even
        replace even : index % 2 = 0 := by simpa using even
        cases sibling : nodeAt nodes (index + 1) <;> cases rec : foldLevelNodes depth nodes rest <;>
          simp [sibling, rec, throw, Bind.bind, Except.bind, pure, Except.pure] at folded
        rename_i siblingValue _
        rcases folded with ⟨rfl, rfl⟩
        intro i v member message hashed
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with (same | member) | member
        · -- The parent message is newly executed.
          -- Both child message sets were already covered.
          cases same
          rw [parents index value List.mem_cons_self atDepth even] at hashed
          simp only [CommitmentTree.messages, List.mem_cons, List.mem_append] at hashed
          rcases hashed with rfl | left | right
          · simp only [← agree index value inNodes, ← nodeAt_agrees agree sibling]
            exact List.mem_append_left _ (levelMessages_member inNodes atDepth even sibling)
          · exact List.mem_append_right _ (covered _ _ inNodes _ left)
          · exact List.mem_append_right _ (covered _ _ (nodeAt_member sibling) _ right)
        all_goals exact later rec i v (by simp [member]) message hashed
      · split at folded
        · simp [throw] at folded
        · exact later folded

private theorem foldLevel_covered {source nodes result : List (Nat × Bytes)}
    {height depth : Nat} {trace : List Bytes}
    (separated : ProofAntichain source) (supported : ProofSupported source nodes)
    (positive : 0 < depth) (bounded : depth ≤ height)
    (agree : NodesAgree (proofTreeNode source height) nodes)
    (covered : MessagesCovered (fun i => proofTree source (height - levelOf i) i) nodes trace)
    (folded : foldLevel depth nodes = .ok result) :
    MessagesCovered (fun i => proofTree source (height - levelOf i) i) result
      (levelMessages depth nodes ++ trace) := by
  -- The same absent-parent equation used for roots also identifies the complete hash subtrees.
  unfold foldLevel at folded
  cases rec : foldLevelNodes depth nodes nodes <;>
    simp [rec, Bind.bind, Except.bind, pure, Except.pure] at folded
  subst result
  apply foldLevelNodes_covered (trees := fun i => proofTree source (height - levelOf i) i)
    (fun _ member => member) _ agree covered rec
  intro index value member atDepth even
  have low := two_le_of_level_positive atDepth positive
  exact proofTree_parent low (by omega) even (source_parent_absent separated
    (supported index (List.mem_map.mpr ⟨_, member, rfl⟩)) low)

private theorem foldToRoot_covered {source : List (Nat × Bytes)} {height : Nat}
    (separated : ProofAntichain source) :
    ∀ depth, depth ≤ height → ∀ nodes trace, ProofSupported source nodes →
      NodesAgree (proofTreeNode source height) nodes →
      MessagesCovered (fun i => proofTree source (height - levelOf i) i) nodes trace →
      ∀ root, foldToRoot depth nodes = .ok root →
      ∀ message ∈ (proofTree source height 1).messages,
        message ∈ multiproofMessages depth nodes ++ trace := by
  -- Extend the accumulated trace at each fold until every root-subtree hash is covered.
  intro depth
  induction depth with
  | zero =>
    intro _ nodes trace _ _ covered root built message member
    simp only [foldToRoot] at built
    cases found : nodeAt nodes 1 <;> simp [found] at built
    simpa [show levelOf 1 = 0 from rfl, multiproofMessages] using
      covered 1 _ (nodeAt_member found) message member
  | succ depth ih =>
    intro bounded nodes trace supported agree covered root built message member
    simp only [foldToRoot] at built
    cases folded : foldLevel (depth + 1) nodes <;> simp [folded, Bind.bind, Except.bind] at built
    rename_i result
    have later := ih (by omega) result (levelMessages (depth + 1) nodes ++ trace)
      (supported.fold folded) (foldLevel_proofTree separated supported (by omega) bounded agree folded)
      (foldLevel_covered separated supported (by omega) bounded agree covered folded)
      root built message member
    simpa [multiproofMessages, folded, List.mem_append, or_assoc, or_left_comm, or_comm] using later

/-- Every hash in the reconstruction tree occurs in the executable multiproof fold. -/
theorem proofTree_messages_executed {nodes : List (Nat × Bytes)} {height : Nat}
    (separated : ProofAntichain nodes) (unique : (nodes.map Prod.fst).Nodup)
    {root : Bytes} (built : foldToRoot height nodes = .ok root) :
    ∀ message ∈ (proofTree nodes height 1).messages,
      message ∈ multiproofMessages height nodes := by
  -- Supplied leaves contain no internal hash messages before reconstruction starts.
  have supported : ProofSupported nodes nodes := fun index member => ⟨index, member, 0, by simp⟩
  have agree : NodesAgree (proofTreeNode nodes height) nodes := by
    intro index value member
    have found := nodeAt_of_unique unique member
    cases budget : height - levelOf index <;>
      simp [proofTreeNode, budget, proofTree, found, CommitmentTree.root]
  have covered : MessagesCovered (fun i => proofTree nodes (height - levelOf i) i) nodes [] := by
    intro index value member message hashed
    have found := nodeAt_of_unique unique member
    cases budget : height - levelOf index <;>
      simp [budget, proofTree, found, CommitmentTree.messages] at hashed
  simpa using foldToRoot_covered separated height (Nat.le_refl _) nodes []
    supported agree covered root built

/-- The deepest supplied position, determined entirely by the claim and helper indices. -/
def multiproofHeight (indices helpers : List Nat) : Nat :=
  -- The largest supplied depth determines how many upward folds are needed.
  ((indices ++ helpers).map levelOf).foldl max 0

/-- The compression inputs executed for a request with its canonical helper ordering. -/
def verifiedMultiproofMessages (leaves proof : List Bytes) (indices : List Nat) : List Bytes :=
  -- Canonical helper ordering assigns each proof value to the same position used by verification.
  match getHelperIndices indices with
  | .error _ => []
  | .ok helpers => multiproofMessages (multiproofHeight indices helpers)
      (indices.zip leaves ++ helpers.zip proof)

end EthLib.Consensus.Ssz
