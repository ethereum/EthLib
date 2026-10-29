import EthLib.Serialization.Proofs.Ssz.Merkle.HelperUniqueness

/-! How many helper nodes a multiproof of several claims at one depth has to carry. -/

namespace EthLib.Serialization.Ssz

/-- The paths of a request hold one node per level below the root for each claim. -/
theorem claimPaths_length (indices : List Nat) :
    (claimPaths indices).length = (indices.map levelOf).sum := by
  -- Each claim contributes one node per level, and the level is the logarithm.
  simp [claimPaths]
  rfl

/-- Building the helper list never produces more nodes than the claims have ancestors. -/
theorem getHelperIndices_length_le_claimPaths {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    helpers.length ≤ (claimPaths indices).length := by
  unfold getHelperIndices at built
  cases accepted : rejectRelated indices <;> cases collected : collectPathIndices indices <;>
    simp [accepted, collected, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
  subst helpers
  obtain ⟨shape, _⟩ := collectPathIndices_info collected
  rw [← shape, List.length_mergeSort]
  refine Nat.le_trans (List.length_filter_le _ _) ?_
  refine Nat.le_trans (eraseDups_sublist_nodup _).1.length_le ?_
  simp

private theorem sum_map_levelOf {indices : List Nat} {depth : Nat}
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    (indices.map levelOf).sum = indices.length * depth := by
  induction indices <;> simp_all [Nat.add_mul]
  omega

/--
A proof of several nodes at one depth carries at most one helper per claim per level.

This is the crude bound: every claim pays for its whole branch, with no sharing counted.
-/
theorem getHelperIndices_length_le_depth {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    helpers.length ≤ indices.length * depth := by
  simpa [claimPaths_length, sum_map_levelOf uniform] using
    getHelperIndices_length_le_claimPaths built

/--
Claiming every node at one depth leaves the proof with nothing to carry.

Every sibling of an ancestor of a claim is an ancestor of another claim, so none is left.
-/
theorem getHelperIndices_full_level {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth)
    (complete : ∀ index, 2 ^ depth ≤ index → index < 2 ^ (depth + 1) → index ∈ indices) :
    helpers = [] := by
  obtain ⟨_, valid, frontier⟩ := getHelperIndices_frontier built
  refine List.eq_nil_iff_forall_not_mem.mpr ?_
  intro node member
  obtain ⟨mapped, missing⟩ := (frontier node).mp member
  obtain ⟨ancestor, onPath, flipped⟩ := List.mem_map.mp mapped
  obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp onPath
  obtain ⟨step, inRange, reached⟩ := List.mem_map.mp stepMember
  subst node
  have claimDepth : Nat.log2 claim = depth := uniform claim claimed
  have below : step < depth := claimDepth ▸ List.mem_range.mp inRange
  obtain ⟨lower, upper⟩ := gindexDepth_bounds (show 1 ≤ claim by have := valid claim claimed; omega)
  rw [claimDepth] at lower upper
  rw [Nat.shiftRight_eq_div_pow] at reached
  subst ancestor
  have positive : 0 < 2 ^ step := Nat.two_pow_pos step
  have split : 2 ^ depth = 2 ^ (depth - step) * 2 ^ step := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt below)]
  have splitUp : 2 ^ (depth + 1) = 2 ^ (depth - step + 1) * 2 ^ step := by
    rw [← Nat.pow_add, show depth - step + 1 + step = depth + 1 by omega]
  have ancestorLower : 2 ^ (depth - step) ≤ claim / 2 ^ step :=
    (Nat.le_div_iff_mul_le positive).mpr (by rw [← split]; exact lower)
  have ancestorUpper : claim / 2 ^ step < 2 ^ (depth - step + 1) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← splitUp]; exact upper)
  have even : 2 ^ (depth - step) = 2 * 2 ^ (depth - step - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have evenUp : 2 ^ (depth - step + 1) = 4 * 2 ^ (depth - step - 1) := by
    rw [Nat.pow_succ, even]
    omega
  have half := gindexSibling_half (claim / 2 ^ step)
  have parity := gindexSibling_parity (claim / 2 ^ step)
  have siblingLower : 2 ^ (depth - step) ≤ gindexSibling (claim / 2 ^ step) := by omega
  have siblingUpper : gindexSibling (claim / 2 ^ step) < 2 ^ (depth - step + 1) := by omega
  have targetLower : 2 ^ depth ≤ gindexSibling (claim / 2 ^ step) * 2 ^ step :=
    split ▸ Nat.mul_le_mul_right _ siblingLower
  have targetUpper : gindexSibling (claim / 2 ^ step) * 2 ^ step < 2 ^ (depth + 1) :=
    splitUp ▸ Nat.mul_lt_mul_of_lt_of_le siblingUpper (Nat.le_refl _) positive
  have targetClaimed := complete _ targetLower targetUpper
  have targetDepth : Nat.log2 (gindexSibling (claim / 2 ^ step) * 2 ^ step) = depth :=
    uniform _ targetClaimed
  refine missing (List.mem_flatMap.mpr ⟨_, targetClaimed, List.mem_map.mpr
    ⟨step, List.mem_range.mpr (targetDepth ▸ below), ?_⟩⟩)
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ positive]


/-- The ancestors of the claims, with each node named once however many claims share it. -/
def sharedPaths (indices : List Nat) : List Nat :=
  (claimPaths indices).eraseDups

/-- The shared ancestor list holds exactly the nodes that appear among the claim paths. -/
theorem mem_sharedPaths {indices : List Nat} {node : Nat} :
    node ∈ sharedPaths indices ↔ node ∈ claimPaths indices := by
  simp [sharedPaths, List.mem_eraseDups]

/-- The shared ancestor list names each node it holds once. -/
theorem sharedPaths_nodup (indices : List Nat) : (sharedPaths indices).Nodup :=
  (eraseDups_sublist_nodup _).2

private theorem length_filter_split (l : List Nat) (bound : Nat) :
    (l.filter fun node => node < bound).length + (l.filter fun node => bound ≤ node).length
      = l.length := by
  -- Each node lands in exactly one of the two filters.
  induction l with
  | nil => simp
  | cons head rest ih =>
    by_cases small : head < bound <;> simp [small, Nat.le_of_not_lt, Nat.not_le_of_lt] <;> omega

private theorem sum_map_const (l : List Nat) (value : Nat) :
    (l.map fun _ => value).sum = l.length * value := by
  induction l <;> simp_all [Nat.add_mul]
  omega

private theorem claimPaths_lt {indices : List Nat} {depth : Nat}
    (uniform : ∀ index ∈ indices, levelOf index = depth) {node : Nat}
    (member : node ∈ claimPaths indices) : node < 2 ^ (depth + 1) := by
  obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp member
  obtain ⟨step, _, reached⟩ := List.mem_map.mp stepMember
  have claimDepth : Nat.log2 claim = depth := uniform claim claimed
  have bound : claim < 2 ^ (depth + 1) := claimDepth ▸ Nat.lt_log2_self
  exact Nat.lt_of_le_of_lt (reached ▸ shiftRight_le claim step) bound

private theorem helper_lt {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) {node : Nat}
    (member : node ∈ helpers) : node < 2 ^ (depth + 1) := by
  obtain ⟨_, _, frontier⟩ := getHelperIndices_frontier built
  obtain ⟨mapped, _⟩ := (frontier node).mp member
  obtain ⟨ancestor, onPath, flipped⟩ := List.mem_map.mp mapped
  subst node
  have bound := claimPaths_lt uniform onPath
  have even : (2:Nat) ^ (depth + 1) = 2 * 2 ^ depth := Nat.pow_succ'
  have half := gindexSibling_half ancestor
  have parity := gindexSibling_parity ancestor
  omega

private theorem frontier_nodup {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    (helpers ++ sharedPaths indices).Nodup := by
  obtain ⟨_, _, frontier⟩ := getHelperIndices_frontier built
  rw [List.nodup_append]
  refine ⟨getHelperIndices_nodup built, sharedPaths_nodup indices, ?_⟩
  intro supplied member shared onPath same
  subst same
  exact ((frontier supplied).mp member).2 (mem_sharedPaths.mp onPath)

private theorem children_length (parents : List Nat) :
    (parents.flatMap fun parent => [2 * parent, 2 * parent + 1]).length
      = 2 * parents.length := by
  simp [List.length_flatMap, sum_map_const]
  omega

private theorem frontier_subset_children {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    helpers ++ sharedPaths indices ⊆
      (((sharedPaths indices).filter fun node => node < 2 ^ depth) ++ [1]).flatMap
        fun parent => [2 * parent, 2 * parent + 1] := by
  intro node member
  obtain ⟨classified, bound⟩ : (node ∈ claimPaths indices ∨ node ∈ helpers) ∧
      node < 2 ^ (depth + 1) := by
    rcases List.mem_append.mp member with supplied | shared
    · exact ⟨Or.inr supplied, helper_lt built uniform supplied⟩
    · have onPath := mem_sharedPaths.mp shared
      exact ⟨Or.inl onPath, claimPaths_lt uniform onPath⟩
  have even : (2:Nat) ^ (depth + 1) = 2 * 2 ^ depth := Nat.pow_succ'
  have small : node / 2 < 2 ^ depth := by omega
  obtain ⟨_, _, parent⟩ := helperFrontier_sibling built classified
  refine List.mem_flatMap.mpr ⟨node / 2, ?_, ?_⟩
  · rcases parent with root | onPath
    · simp [root]
    · exact List.mem_append_left _ (List.mem_filter.mpr
        ⟨mem_sharedPaths.mpr onPath, by simpa using small⟩)
  -- The node is the even or the odd child of its half.
  · simp
    omega

private theorem claim_lower {indices : List Nat} {depth : Nat}
    (valid : ∀ index ∈ indices, 2 ≤ index)
    (uniform : ∀ index ∈ indices, levelOf index = depth) {claim : Nat}
    (claimed : claim ∈ indices) : 2 ^ depth ≤ claim := by
  have claimDepth : Nat.log2 claim = depth := uniform claim claimed
  exact claimDepth ▸ Nat.log2_self_le (by have := valid claim claimed; omega)

/--
The shared ancestors outnumber the helpers by at least twice the claim count, less two.

Every claim and every helper is a child of a shared ancestor above the claimed level.

The shared ancestors at the claimed level are the claims themselves.
-/
theorem getHelperIndices_length_add_le {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    helpers.length + 2 * indices.length ≤ (sharedPaths indices).length + 2 := by
  obtain ⟨_, valid, _⟩ := getHelperIndices_frontier built
  have accepted : rejectRelated indices = .ok () := by
    unfold getHelperIndices at built
    cases checked : rejectRelated indices with
    | error fault => simp [checked, Bind.bind, Except.bind] at built
    | ok checkedUnit => cases checkedUnit; rfl
  have claims : indices.Nodup := rejectRelated_nodup accepted
  have pigeon := (frontier_nodup built).length_le_of_subset
    (frontier_subset_children built uniform)
  simp only [List.length_append, children_length, List.length_singleton] at pigeon
  have split := length_filter_split (sharedPaths indices) (2 ^ depth)
  have high : indices.length
      ≤ ((sharedPaths indices).filter fun node => 2 ^ depth ≤ node).length := by
    refine claims.length_le_of_subset ?_
    intro claim claimed
    exact List.mem_filter.mpr ⟨mem_sharedPaths.mpr (claim_mem_paths valid claimed),
      by simpa using claim_lower valid uniform claimed⟩
  omega

/--
The shared ancestors split into a full top of the tree and one branch per claim below it.

The cut is free: above it every node of the tree is allowed.

Below the cut each level holds at most one ancestor per claim.
-/
theorem sharedPaths_length_le {indices : List Nat} {depth : Nat}
    (uniform : ∀ index ∈ indices, levelOf index = depth)
    (valid : ∀ index ∈ indices, 2 ≤ index) (cut : Nat) :
    (sharedPaths indices).length ≤ 2 ^ (cut + 1) - 2 + (depth - cut) * indices.length := by
  have flatLength : ((List.range (depth - cut)).flatMap
      fun step => indices.map fun claim => claim >>> step).length
      = (depth - cut) * indices.length := by
    simp [List.length_flatMap, sum_map_const]
  have covered : sharedPaths indices ⊆
      ((List.range (2 ^ (cut + 1) - 2)).map fun offset => offset + 2) ++
        (List.range (depth - cut)).flatMap fun step => indices.map fun claim => claim >>> step := by
    intro node member
    obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp (mem_sharedPaths.mp member)
    obtain ⟨step, inRange, reached⟩ := List.mem_map.mp stepMember
    have claimDepth : Nat.log2 claim = depth := uniform claim claimed
    have below : step < depth := claimDepth ▸ List.mem_range.mp inRange
    by_cases deep : step < depth - cut
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨step, List.mem_range.mpr deep,
        List.mem_map.mpr ⟨claim, claimed, reached⟩⟩)
    · have twoLe : 2 ≤ node := (claimPaths_bounds valid (mem_sharedPaths.mp member)).1
      have upper : claim < 2 ^ (depth + 1) := claimDepth ▸ Nat.lt_log2_self
      have splitUp : 2 ^ (depth + 1) = 2 ^ (depth - step + 1) * 2 ^ step := by
        rw [← Nat.pow_add, show depth - step + 1 + step = depth + 1 by omega]
      have nodeUpper : node < 2 ^ (depth - step + 1) := by
        rw [← reached, Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← splitUp]; exact upper)
      have grow : (2:Nat) ^ (depth - step + 1) ≤ 2 ^ (cut + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact List.mem_append_left _ (List.mem_map.mpr
        ⟨node - 2, List.mem_range.mpr (by omega), by omega⟩)
  simpa [flatLength] using (sharedPaths_nodup indices).length_le_of_subset covered

/--
A proof of several nodes at one depth carries no helper for the levels the claims share.

The claims cover the top of the tree between them, so those levels cost nothing.

Only the levels below the logarithm of the claim count cost one helper each.
-/
theorem getHelperIndices_length_le_shared {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    helpers.length ≤ indices.length * (depth - Nat.log2 indices.length) := by
  obtain ⟨nonempty, valid, _⟩ := getHelperIndices_frontier built
  have positive : 1 ≤ indices.length := List.length_pos_iff.mpr nonempty
  have children := getHelperIndices_length_add_le built uniform
  have shared := sharedPaths_length_le uniform valid (Nat.log2 indices.length)
  have reaches : 2 ^ Nat.log2 indices.length ≤ indices.length := Nat.log2_self_le (by omega)
  have double : (2:Nat) ^ (Nat.log2 indices.length + 1)
      = 2 * 2 ^ Nat.log2 indices.length := Nat.pow_succ'
  rw [Nat.mul_comm]
  omega

private theorem children_nodup {parents : List Nat} (distinct : parents.Nodup) :
    (parents.flatMap fun parent => [2 * parent, 2 * parent + 1]).Nodup := by
  induction parents with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨by simp, ih tail, ?_⟩
    intro child here other there
    obtain ⟨parent, member, pair⟩ := List.mem_flatMap.mp there
    have apart : parent ≠ head := fun same => fresh (same ▸ member)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at here pair
    omega

private theorem children_subset_frontier {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    (((sharedPaths indices).filter fun node => node < 2 ^ depth) ++ [1]).flatMap
        (fun parent => [2 * parent, 2 * parent + 1]) ⊆ helpers ++ sharedPaths indices := by
  obtain ⟨_, valid, _⟩ := getHelperIndices_frontier built
  intro child member
  obtain ⟨parent, above, pair⟩ := List.mem_flatMap.mp member
  have classified : (parent = 1 ∨ parent ∈ claimPaths indices) ∧ parent ∉ indices := by
    rcases List.mem_append.mp above with shared | root
    · obtain ⟨onPath, small⟩ := List.mem_filter.mp shared
      refine ⟨Or.inr (mem_sharedPaths.mp onPath), fun claimed => ?_⟩
      have := claim_lower valid uniform claimed
      simp only [decide_eq_true_eq] at small
      omega
    · simp only [List.mem_singleton] at root
      exact ⟨Or.inl root, fun claimed => by have := valid parent claimed; omega⟩
  obtain ⟨left, right⟩ := helperFrontier_children built classified.1 classified.2
  -- The child is one of the two, and each is a shared ancestor or a helper.
  simp only [List.mem_cons, List.not_mem_nil, or_false] at pair
  rcases pair with rfl | rfl <;> simp only [List.mem_append, mem_sharedPaths]
    <;> exact Or.symm ‹_›

/--
The shared ancestors outnumber the helpers by at most twice the claim count, less two.

Both children of a shared ancestor above the claimed level are shared ancestors or helpers.

That is what makes the two counts determine each other.
-/
theorem getHelperIndices_length_add_ge {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    (sharedPaths indices).length + 2 ≤ helpers.length + 2 * indices.length := by
  obtain ⟨_, valid, _⟩ := getHelperIndices_frontier built
  have parents : (((sharedPaths indices).filter fun node => node < 2 ^ depth) ++ [1]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(sharedPaths_nodup indices).filter _, by simp, ?_⟩
    intro node member root onRoot same
    simp only [List.mem_singleton] at onRoot
    have := (claimPaths_bounds valid (mem_sharedPaths.mp (List.mem_filter.mp member).1)).1
    omega
  have pigeon := (children_nodup parents).length_le_of_subset
    (children_subset_frontier built uniform)
  simp only [children_length, List.length_append, List.length_singleton] at pigeon
  have split := length_filter_split (sharedPaths indices) (2 ^ depth)
  have high : ((sharedPaths indices).filter fun node => 2 ^ depth ≤ node).length
      ≤ indices.length := by
    refine List.Nodup.length_le_of_subset ((sharedPaths_nodup indices).filter _) ?_
    intro node member
    obtain ⟨shared, big⟩ := List.mem_filter.mp member
    simp only [decide_eq_true_eq] at big
    obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp (mem_sharedPaths.mp shared)
    obtain ⟨step, _, reached⟩ := List.mem_map.mp stepMember
    by_cases bottom : step = 0
    · subst bottom
      simpa using reached ▸ claimed
    · have claimDepth : Nat.log2 claim = depth := uniform claim claimed
      have upper : claim < 2 ^ (depth + 1) := claimDepth ▸ Nat.lt_log2_self
      have even : (2:Nat) ^ (depth + 1) = 2 * 2 ^ depth := Nat.pow_succ'
      have climbed : claim >>> step ≤ claim >>> 1 := by
        rw [show step = 1 + (step - 1) by omega, Nat.shiftRight_add]
        exact shiftRight_le _ _
      rw [Nat.shiftRight_eq_div_pow] at climbed
      omega
  omega

/-- Bits set in a number, which is what repeated halving leaves behind. -/
private def digitSum : Nat → Nat
  | 0 => 0
  | value + 1 => (value + 1) % 2 + digitSum ((value + 1) / 2)
decreasing_by omega

/-- A number and all its halvings added together. -/
private def shiftSum : Nat → Nat → Nat
  | 0, _ => 0
  | levels + 1, value => value + shiftSum levels (value / 2)

private theorem digitSum_step (value : Nat) (positive : 0 < value) :
    digitSum value = value % 2 + digitSum (value / 2) := by
  obtain ⟨below, rfl⟩ : ∃ below, value = below + 1 := ⟨value - 1, by omega⟩
  rw [digitSum]

private theorem digitSum_le : ∀ levels value : Nat, value < 2 ^ levels → digitSum value ≤ levels
  | 0, value, small => by simp_all [digitSum]
  | levels + 1, value, small => by
    by_cases zero : value = 0
    · simp [zero, digitSum]
    · have half : value / 2 < 2 ^ levels := by rw [Nat.pow_succ] at small; omega
      have below := digitSum_le levels (value / 2) half
      rw [digitSum_step value (by omega)]
      omega

private theorem digitSum_le_pred :
    ∀ levels value : Nat, value + 2 ≤ 2 ^ (levels + 1) → digitSum value ≤ levels
  | 0, value, small => by simp_all [digitSum]
  | levels + 1, value, small => by
    by_cases zero : value = 0
    · simp [zero, digitSum]
    rw [digitSum_step value (by omega)]
    have grow : (2:Nat) ^ (levels + 2) = 2 * 2 ^ (levels + 1) := Nat.pow_succ'
    rcases Nat.mod_two_eq_zero_or_one value with even | odd
    · have half : value / 2 < 2 ^ (levels + 1) := by omega
      have below := digitSum_le (levels + 1) (value / 2) half
      omega
    · have half : value / 2 + 2 ≤ 2 ^ (levels + 1) := by omega
      have below := digitSum_le_pred levels (value / 2) half
      omega

private theorem shiftSum_zero (levels : Nat) : shiftSum levels 0 = 0 := by
  induction levels <;> simp_all [shiftSum]

private theorem shiftSum_digitSum :
    ∀ levels value : Nat, value < 2 ^ levels → shiftSum levels value + digitSum value = 2 * value
  | 0, value, small => by simp_all [digitSum, shiftSum]
  | levels + 1, value, small => by
    by_cases zero : value = 0
    · simp [zero, digitSum, shiftSum, shiftSum_zero]
    · have half : value / 2 < 2 ^ levels := by rw [Nat.pow_succ] at small; omega
      have below := shiftSum_digitSum levels (value / 2) half
      rw [digitSum_step value (by omega), shiftSum]
      omega

private theorem shiftSum_eq (levels value : Nat) :
    shiftSum levels value = ((List.range levels).map fun step => value >>> step).sum := by
  induction levels generalizing value with
  | zero => simp [shiftSum]
  | succ levels ih =>
    -- Halving first is one more shift on every later term.
    simp [shiftSum, ih, List.range_succ_eq_map, Function.comp_def, Nat.shiftRight_succ_inside]

private theorem sum_map_add (l : List Nat) (f g : Nat → Nat) :
    (l.map fun item => f item + g item).sum = (l.map f).sum + (l.map g).sum := by
  induction l <;> simp_all
  omega

private theorem sum_map_le {l : List Nat} {f g : Nat → Nat}
    (pointwise : ∀ item ∈ l, f item ≤ g item) : (l.map f).sum ≤ (l.map g).sum := by
  induction l <;> simp_all
  omega

private theorem shift_add_le (first last shift : Nat) (ordered : first ≤ last) :
    (last - first) >>> shift + first >>> shift ≤ last >>> shift := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  refine (Nat.le_div_iff_mul_le (Nat.two_pow_pos shift)).mpr ?_
  have spent := Nat.div_mul_le_self (last - first) (2 ^ shift)
  have kept := Nat.div_mul_le_self first (2 ^ shift)
  rw [Nat.add_mul]
  omega

private theorem nodup_flatMap_range {levels : Nat} {parts : Nat → List Nat} {tag mark : Nat → Nat}
    (inner : ∀ step, step < levels → (parts step).Nodup)
    (tagged : ∀ step, step < levels → ∀ node ∈ parts step, tag node = mark step)
    (marks : ∀ i, i < levels → ∀ j, j < levels → mark i = mark j → i = j) :
    ((List.range levels).flatMap parts).Nodup := by
  induction levels with
  | zero => simp
  | succ levels ih =>
    rw [List.range_succ, List.flatMap_append, List.nodup_append]
    refine ⟨ih (fun step below => inner step (by omega))
      (fun step below => tagged step (by omega))
      (fun i first j second => marks i (by omega) j (by omega)), ?_, ?_⟩
    · simpa using inner levels (by omega)
    · intro node member other last same
      obtain ⟨step, stepMember, inside⟩ := List.mem_flatMap.mp member
      have below := List.mem_range.mp stepMember
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at last
      have first := tagged step (by omega) node inside
      have second := tagged levels (by omega) other last
      rw [same, second] at first
      have := marks levels (by omega) step (by omega) first
      omega

private theorem shift_lower {value depth shift : Nat} (lower : 2 ^ depth ≤ value)
    (below : shift ≤ depth) : 2 ^ (depth - shift) ≤ value >>> shift := by
  rw [Nat.shiftRight_eq_div_pow]
  refine (Nat.le_div_iff_mul_le (Nat.two_pow_pos shift)).mpr ?_
  rwa [← Nat.pow_add, show depth - shift + shift = depth by omega]

private theorem shift_upper {value depth shift : Nat} (upper : value < 2 ^ (depth + 1))
    (below : shift ≤ depth) : value >>> shift < 2 ^ (depth - shift + 1) := by
  rw [Nat.shiftRight_eq_div_pow]
  refine Nat.div_lt_of_lt_mul ?_
  rwa [← Nat.pow_add, show shift + (depth - shift + 1) = depth + 1 by omega]

private theorem shift_monotone {small large shift : Nat} (ordered : small ≤ large) :
    small >>> shift ≤ large >>> shift := by
  simpa [Nat.shiftRight_eq_div_pow] using Nat.div_le_div_right ordered

private theorem run_mem_claimPaths {first count depth shift node : Nat}
    (positive : 0 < count) (lower : 2 ^ depth ≤ first)
    (upper : first + count ≤ 2 ^ (depth + 1)) (below : shift < depth)
    (bottom : first >>> shift ≤ node) (top : node ≤ (first + count - 1) >>> shift) :
    node ∈ claimPaths (List.range' first count) := by
  have positivePow : 0 < 2 ^ shift := Nat.two_pow_pos shift
  have mark : ∀ claim, first ≤ claim → claim < first + count → Nat.log2 claim = depth :=
    fun claim atLeast atMost => (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
  refine List.mem_flatMap.mpr ?_
  by_cases start : node = first >>> shift
  · exact ⟨first, List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩, List.mem_map.mpr
      ⟨shift, List.mem_range.mpr (by rw [mark first (Nat.le_refl _) (by omega)]; omega),
        start.symm⟩⟩
  · have same : first >>> shift = first / 2 ^ shift := Nat.shiftRight_eq_div_pow first shift
    have step : first / 2 ^ shift + 1 ≤ node := by omega
    have atLeast : first ≤ node * 2 ^ shift := by
      have grow : (first / 2 ^ shift + 1) * 2 ^ shift ≤ node * 2 ^ shift :=
        Nat.mul_le_mul_right _ step
      have room := Nat.lt_mul_div_succ first positivePow
      rw [Nat.mul_comm] at room
      omega
    have atMost : node * 2 ^ shift ≤ first + count - 1 :=
      (Nat.le_div_iff_mul_le positivePow).mp (by rw [← Nat.shiftRight_eq_div_pow]; exact top)
    have recovered : (node * 2 ^ shift) >>> shift = node := by
      rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel node positivePow]
    exact ⟨node * 2 ^ shift, List.mem_range'_1.mpr ⟨atLeast, by omega⟩, List.mem_map.mpr
      ⟨shift, List.mem_range.mpr (by rw [mark _ atLeast (by omega)]; omega), recovered⟩⟩

/--
A run of consecutive claims has one shared ancestor per level, and more where the run is wide.

The run halves as the levels rise.

The counts add up to twice the claim count, less the bits of the run's width.
-/
theorem sharedPaths_length_ge_run {first count depth : Nat}
    (positive : 0 < count) (lower : 2 ^ depth ≤ first)
    (upper : first + count ≤ 2 ^ (depth + 1)) :
    depth + 2 * count
      ≤ (sharedPaths (List.range' first count)).length + 2 + Nat.log2 count := by
  have double : (2:Nat) ^ (depth + 1) = 2 * 2 ^ depth := Nat.pow_succ'
  have lastUpper : first + count - 1 < 2 ^ (depth + 1) := by omega
  have ordered : first ≤ first + count - 1 := by omega
  have inner : ∀ shift, shift < depth → (List.range' (first >>> shift)
      ((first + count - 1) >>> shift - first >>> shift + 1)).Nodup :=
    fun _ _ => List.nodup_range'
  have tagged : ∀ shift, shift < depth → ∀ node ∈ List.range' (first >>> shift)
      ((first + count - 1) >>> shift - first >>> shift + 1), Nat.log2 node = depth - shift := by
    intro shift small node member
    obtain ⟨atLeast, atMost⟩ := List.mem_range'_1.mp member
    have bottom := shift_lower lower (Nat.le_of_lt small)
    have top := shift_upper lastUpper (Nat.le_of_lt small)
    have monotone := shift_monotone (shift := shift) ordered
    exact (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
  have distinct := nodup_flatMap_range (levels := depth)
    (parts := fun shift => List.range' (first >>> shift)
      ((first + count - 1) >>> shift - first >>> shift + 1))
    (tag := Nat.log2) (mark := fun shift => depth - shift) inner tagged
    (by intro i small j smaller same; omega)
  have covered : ((List.range depth).flatMap fun shift => List.range' (first >>> shift)
      ((first + count - 1) >>> shift - first >>> shift + 1))
      ⊆ sharedPaths (List.range' first count) := by
    intro node member
    obtain ⟨shift, stepMember, inside⟩ := List.mem_flatMap.mp member
    obtain ⟨atLeast, atMost⟩ := List.mem_range'_1.mp inside
    have monotone := shift_monotone (shift := shift) ordered
    exact mem_sharedPaths.mpr (run_mem_claimPaths positive lower upper
      (List.mem_range.mp stepMember) atLeast (by omega))
  have pigeon := distinct.length_le_of_subset covered
  simp only [List.length_flatMap, List.length_range'] at pigeon
  have terms : ∀ shift ∈ List.range depth, 1 + (count - 1) >>> shift
      ≤ (first + count - 1) >>> shift - first >>> shift + 1 := by
    intro shift _
    have climbed := shift_add_le first (first + count - 1) shift ordered
    rw [show first + count - 1 - first = count - 1 from by omega] at climbed
    omega
  have summed := sum_map_le terms
  have split : ((List.range depth).map fun shift => 1 + (count - 1) >>> shift).sum
      = depth + shiftSum depth (count - 1) := by
    rw [sum_map_add (List.range depth) (fun _ => 1) (fun shift => (count - 1) >>> shift),
      sum_map_const, List.length_range, shiftSum_eq]
    omega
  have digits : digitSum (count - 1) ≤ Nat.log2 count :=
    digitSum_le_pred (Nat.log2 count) (count - 1) (by have := Nat.lt_log2_self (n := count); omega)
  have whole : shiftSum depth (count - 1) + digitSum (count - 1) = 2 * (count - 1) :=
    shiftSum_digitSum depth (count - 1) (by omega)
  omega

/-- The helper count and the claim count together fix how many ancestors the claims have. -/
theorem getHelperIndices_length_add_eq {indices helpers : List Nat} {depth : Nat}
    (built : getHelperIndices indices = .ok helpers)
    (uniform : ∀ index ∈ indices, levelOf index = depth) :
    helpers.length + 2 * indices.length = (sharedPaths indices).length + 2 :=
  Nat.le_antisymm (getHelperIndices_length_add_le built uniform)
    (getHelperIndices_length_add_ge built uniform)

/--
A proof of consecutive nodes at one depth carries a helper for every unshared level.

The run shares a single branch above the levels its own length spans.

Each level of that branch costs one helper.
-/
theorem getHelperIndices_length_ge_run {first count depth : Nat} {helpers : List Nat}
    (built : getHelperIndices (List.range' first count) = .ok helpers)
    (positive : 0 < count) (lower : 2 ^ depth ≤ first)
    (upper : first + count ≤ 2 ^ (depth + 1)) :
    depth - Nat.log2 count ≤ helpers.length := by
  have uniform : ∀ index ∈ List.range' first count, levelOf index = depth := by
    intro index member
    obtain ⟨atLeast, atMost⟩ := List.mem_range'_1.mp member
    exact (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
  have children := getHelperIndices_length_add_ge built uniform
  have ancestors := sharedPaths_length_ge_run positive lower upper
  rw [List.length_range'] at children
  omega

end EthLib.Serialization.Ssz
