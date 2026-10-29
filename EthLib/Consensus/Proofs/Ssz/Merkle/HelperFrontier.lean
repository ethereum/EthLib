import EthLib.Consensus.Proofs.Ssz.Merkle.Verify

/-! Requested paths and their missing siblings form a finite proof frontier. -/

namespace EthLib.Consensus.Ssz

/-- A positive depth excludes the root and the invalid index zero. -/
theorem two_le_of_level_positive {index depth : Nat}
    (level : levelOf index = depth) (positive : 0 < depth) : 2 ≤ index := by
  -- Both zero and one have depth zero.
  match index with
  | 0 | 1 => change 0 = depth at level; omega
  | _ + 2 => omega

/-- Ancestors below the root along all requested branches. -/
def claimPaths (indices : List Nat) : List Nat :=
  -- Each requested index contributes itself and its ancestors below the root.
  indices.flatMap fun index =>
    (List.range (Nat.log2 index)).map fun step => index >>> step

/-- Successful path collection fixes both the ancestors and the validity of every claim. -/
theorem collectPathIndices_info {indices paths : List Nat}
    (collected : collectPathIndices indices = .ok paths) :
    paths = claimPaths indices ∧ ∀ index ∈ indices, 2 ≤ index := by
  -- Validation is performed once for every requested branch.
  induction indices generalizing paths with
  | nil => simp_all [collectPathIndices, claimPaths]
  | cons index rest ih =>
    unfold collectPathIndices at collected
    cases measured : gindexLength index with
    | error error => simp [getPathIndices, measured, Bind.bind, Except.bind] at collected
    | ok depth =>
      obtain ⟨same, -, nonzero⟩ := gindexLength_ok measured
      subst depth
      cases rec : collectPathIndices rest with
      | error error => simp [getPathIndices, measured, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at collected
      | ok remaining =>
        obtain ⟨shape, valid⟩ := ih rec
        simp [getPathIndices, measured, rec, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at collected
        refine ⟨by rw [← collected, shape]; rfl, ?_⟩
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨two_le_of_level_positive (depth := Nat.log2 index) rfl (by omega), valid⟩

/-- A successful request always names at least one branch. -/
theorem rejectRelated_nonempty {indices : List Nat}
    (accepted : rejectRelated indices = .ok ()) : indices ≠ [] := by
  -- The first check rejects the empty list independently of all later checks.
  intro empty
  subst indices
  simp [rejectRelated_empty] at accepted

/-- Helper indices are exactly branch siblings that are not themselves reconstructible paths. -/
theorem getHelperIndices_frontier {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    indices ≠ [] ∧ (∀ index ∈ indices, 2 ≤ index) ∧
      ∀ index, index ∈ helpers ↔
        index ∈ (claimPaths indices).map gindexSibling ∧ index ∉ claimPaths indices := by
  -- Sorting changes only the order, while deduplication changes only multiplicity.
  unfold getHelperIndices at built
  cases accepted : rejectRelated indices with
  | error error => simp [accepted, Bind.bind, Except.bind] at built
  | ok checked =>
    cases checked
    cases collected : collectPathIndices indices with
    | error error => simp [accepted, collected, Bind.bind, Except.bind] at built
    | ok paths =>
      obtain ⟨shape, valid⟩ := collectPathIndices_info collected
      simp only [bind, Except.bind, accepted, collected, pure, Except.pure, List.contains_eq_mem,
        Except.ok.injEq] at built
      subst helpers
      refine ⟨rejectRelated_nonempty accepted, valid, ?_⟩
      intro index
      simp [List.mem_mergeSort, List.mem_filter, List.mem_eraseDups, shape]

/-- An ancestor strictly below the root still has an index of at least two. -/
theorem path_shift_positive {index step : Nat} (named : 1 ≤ index)
    (below : step < Nat.log2 index) : 2 ≤ index >>> step := by
  -- The next ancestor has not passed the root, so halving this one remains positive.
  have reaches := shiftRight_depth named
  have distance : step + 1 + (Nat.log2 index - (step + 1)) = Nat.log2 index := by omega
  have upper : 1 ≤ index >>> (step + 1) := by
    have small := shiftRight_le (index >>> (step + 1)) (Nat.log2 index - (step + 1))
    rw [← Nat.shiftRight_add, distance, reaches] at small
    exact small
  rw [shiftRight_succ] at upper
  omega

/-- Every recorded path node lies below the root and is bounded by its original claim. -/
theorem claimPaths_bounds {indices : List Nat} (valid : ∀ index ∈ indices, 2 ≤ index)
    {index : Nat} (member : index ∈ claimPaths indices) :
    2 ≤ index ∧ ∃ claim ∈ indices, index ≤ claim := by
  -- A right shift removes branch turns and cannot increase the generalized index.
  obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp member
  obtain ⟨step, inRange, same⟩ := List.mem_map.mp stepMember
  subst index
  exact ⟨path_shift_positive (by have := valid claim claimed; omega)
    (List.mem_range.mp inRange), claim, claimed, shiftRight_le _ _⟩

/-- An unclaimed ancestor has a child on one of the requested paths. -/
theorem claimPaths_child {indices : List Nat} (nonempty : indices ≠ [])
    (valid : ∀ index ∈ indices, 2 ≤ index) {index : Nat}
    (inside : index = 1 ∨ index ∈ claimPaths indices) (unclaimed : index ∉ indices) :
    ∃ child ∈ claimPaths indices, child / 2 = index := by
  -- The child is the preceding ancestor on a requested branch.
  rcases inside with root | member
  · subst index
    cases indices with
    | nil => exact False.elim (nonempty rfl)
    | cons claim rest =>
      -- A nonempty request supplies a branch whose last child sits immediately below the root.
      have named : 1 ≤ claim := by have := valid claim (by simp); omega
      have deep : 0 < Nat.log2 claim := (Nat.le_log2 (by omega)).mpr (valid claim (by simp))
      refine ⟨claim >>> (Nat.log2 claim - 1), ?_, ?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨claim, by simp, List.mem_map.mpr ?_⟩
        exact ⟨Nat.log2 claim - 1, List.mem_range.mpr (by omega), rfl⟩
      · rw [← shiftRight_succ, Nat.sub_add_cancel deep, shiftRight_depth named]
  · obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp member
    obtain ⟨step, inRange, same⟩ := List.mem_map.mp stepMember
    -- An unclaimed ancestor cannot be the branch's initial requested position.
    have positive : 0 < step := Nat.pos_of_ne_zero fun zero => by
      simp only [zero, Nat.shiftRight_zero] at same
      exact unclaimed (same ▸ claimed)
    refine ⟨claim >>> (step - 1), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨claim, claimed, List.mem_map.mpr ?_⟩
      exact ⟨step - 1, List.mem_range.mpr (by have := List.mem_range.mp inRange; omega), rfl⟩
    · rw [← shiftRight_succ, Nat.sub_add_cancel positive, same]

/-- Both children of an unclaimed ancestor are either reconstructible or supplied as helpers. -/
theorem helperFrontier_children {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {index : Nat}
    (inside : index = 1 ∨ index ∈ claimPaths indices) (unclaimed : index ∉ indices) :
    (2 * index ∈ claimPaths indices ∨ 2 * index ∈ helpers) ∧
    (2 * index + 1 ∈ claimPaths indices ∨ 2 * index + 1 ∈ helpers) := by
  -- One child follows a claim, and its sibling is either another path or a helper.
  obtain ⟨nonempty, valid, shape⟩ := getHelperIndices_frontier built
  obtain ⟨child, member, parent⟩ := claimPaths_child nonempty valid inside unclaimed
  -- The opposite child is either another requested path or exactly one required helper.
  have sibling : gindexSibling child ∈ claimPaths indices ∨ gindexSibling child ∈ helpers :=
    (Classical.em _).imp_right fun onPath =>
      (shape _).mpr ⟨List.mem_map.mpr ⟨child, member, rfl⟩, onPath⟩
  rcases Nat.mod_two_eq_zero_or_one child with even | odd
  · obtain ⟨left, right⟩ := gindexSibling_even even
    rw [parent] at left right
    exact ⟨Or.inl (left ▸ member), right ▸ sibling⟩
  · obtain ⟨right, left⟩ := gindexSibling_odd odd
    rw [parent] at left right
    exact ⟨left ▸ sibling, Or.inl (right ▸ member)⟩

/-- A child below the root is exactly one level deeper than its parent. -/
theorem levelOf_parent {index : Nat} (below : 2 ≤ index) :
    levelOf index = levelOf (index / 2) + 1 := by
  -- The recursive logarithm removes the lowest branch bit.
  exact (Nat.log2_def index).trans (ite_eq_left below)

/-- Siblings below the root have equal depths. -/
theorem levelOf_sibling {index : Nat} (below : 2 ≤ index) :
    levelOf (gindexSibling index) = levelOf index := by
  -- Both indices have the same positive parent.
  have half := gindexSibling_half index
  have other : 2 ≤ gindexSibling index := by omega
  rw [levelOf_parent other, half, ← levelOf_parent below]

/-- A smaller positive index cannot be deeper than a larger one. -/
theorem levelOf_mono {left right : Nat} (positive : 1 ≤ left) (ordered : left ≤ right) :
    levelOf left ≤ levelOf right := by
  -- The smaller index's leading bit also fits within the larger index.
  apply (Nat.le_log2 (by omega : right ≠ 0)).mpr
  exact Nat.le_trans (Nat.log2_self_le (by omega)) ordered

/-- Every original claim is the first node on its own path. -/
theorem claim_mem_paths {indices : List Nat} (valid : ∀ index ∈ indices, 2 ≤ index)
    {index : Nat} (claimed : index ∈ indices) : index ∈ claimPaths indices := by
  -- Depth is positive because a request cannot name the root itself.
  have positive : 0 < Nat.log2 index :=
    (Nat.le_log2 (Nat.ne_zero_of_lt (valid index claimed))).mpr (valid index claimed)
  apply List.mem_flatMap.mpr
  exact ⟨index, claimed, List.mem_map.mpr ⟨0, List.mem_range.mpr positive, by simp⟩⟩

/-- A path node's parent stays on the paths, unless it has reached the root. -/
theorem claimPaths_parent {indices : List Nat} (valid : ∀ index ∈ indices, 2 ≤ index)
    {index : Nat} (member : index ∈ claimPaths indices) :
    index / 2 = 1 ∨ index / 2 ∈ claimPaths indices := by
  -- The next position in the branch is one additional right shift.
  obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp member
  obtain ⟨step, inRange, same⟩ := List.mem_map.mp stepMember
  rw [← same, ← shiftRight_succ]
  have below := List.mem_range.mp inRange
  by_cases last : step + 1 = Nat.log2 claim
  · left
    rw [last, shiftRight_depth (by have := valid claim claimed; omega)]
  · right
    apply List.mem_flatMap.mpr
    exact ⟨claim, claimed, List.mem_map.mpr
      ⟨step + 1, List.mem_range.mpr (by omega), rfl⟩⟩

/-- A path or helper node has its sibling among the paths or helpers too. -/
theorem helperFrontier_sibling {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {index : Nat}
    (member : index ∈ claimPaths indices ∨ index ∈ helpers) :
    2 ≤ index ∧ (gindexSibling index ∈ claimPaths indices ∨ gindexSibling index ∈ helpers) ∧
      (index / 2 = 1 ∨ index / 2 ∈ claimPaths indices) := by
  -- Helpers are siblings of path nodes, so they inherit the same parent.
  obtain ⟨_, valid, shape⟩ := getHelperIndices_frontier built
  rcases member with path | helper
  · have positive := (claimPaths_bounds valid path).1
    refine ⟨positive, ?_, claimPaths_parent valid path⟩
    exact (Classical.em _).imp_right fun siblingPath =>
      (shape _).mpr ⟨List.mem_map.mpr ⟨index, path, rfl⟩, siblingPath⟩
  -- A helper is the sibling of a path node, so the pair shares its already classified parent.
  · obtain ⟨mapped, _⟩ := (shape index).mp helper
    obtain ⟨sibling, path, same⟩ := List.mem_map.mp mapped
    subst index
    have positive := (claimPaths_bounds valid path).1
    have half := gindexSibling_half sibling
    refine ⟨by omega, ?_, ?_⟩
    · exact Or.inl (by simpa only [gindexSibling_sibling] using path)
    · rw [half]
      exact claimPaths_parent valid path

end EthLib.Consensus.Ssz
