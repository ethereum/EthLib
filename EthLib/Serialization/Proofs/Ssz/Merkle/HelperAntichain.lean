module

public import EthLib.Serialization.Proofs.Ssz.Merkle.HelperUniqueness

/-! Supplied multiproof nodes form a cut: no supplied node hides another beneath it. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

private theorem rejectAncestors_excludes {indices ancestors : List Nat} {claim : Nat}
    (accepted : rejectAncestors indices claim ancestors = .ok ()) :
    ∀ ancestor ∈ ancestors, ancestor ∉ indices := by
  -- Every accepted ancestor position was absent from the requested claims.
  induction ancestors with
  | nil => simp
  | cons head rest ih =>
    by_cases present : head ∈ indices <;>
      simp_all [rejectAncestors, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem rejectClaimPaths_excludes {indices pending : List Nat}
    (accepted : rejectClaimPaths indices pending = .ok ()) :
    ∀ claim ∈ pending, ∃ path, getPathIndices claim = .ok path ∧
      ∀ ancestor ∈ path.drop 1, ancestor ∉ indices := by
  -- Validation excludes the strict ancestors of each requested claim before continuing to the next.
  induction pending with
  | nil => simp
  | cons head rest ih =>
    cases pathEq : getPathIndices head <;>
      simp [rejectClaimPaths, pathEq, Bind.bind, Except.bind] at accepted
    rename_i path
    cases checked : rejectAncestors indices head path.tail <;> simp [checked] at accepted
    intro claim member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨path, pathEq, rejectAncestors_excludes (by simpa using checked)⟩
    · exact ih accepted claim member

private theorem rejectRelated_paths {indices : List Nat}
    (accepted : rejectRelated indices = .ok ()) :
    rejectClaimPaths indices indices = .ok () := by
  -- An accepted request has already passed emptiness and duplicate checks before its paths are inspected.
  have nonempty := rejectRelated_nonempty accepted
  by_cases same : indices.eraseDups.length = indices.length <;>
    simp_all [rejectRelated, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A successful request excludes every strict ancestor of each claimed node. -/
theorem rejectRelated_strict_shift {indices : List Nat}
    (accepted : rejectRelated indices = .ok ()) {claim step : Nat}
    (claimed : claim ∈ indices) (positive : 0 < step) (below : step < Nat.log2 claim) :
    claim >>> step ∉ indices := by
  -- A positive shift below the branch depth names one of the excluded strict ancestors.
  obtain ⟨path, pathEq, excludes⟩ := rejectClaimPaths_excludes
    (rejectRelated_paths accepted) claim claimed
  cases measured : gindexLength claim <;>
    simp [getPathIndices, measured, Bind.bind, Except.bind, Pure.pure, Except.pure] at pathEq
  obtain ⟨rfl, _, _⟩ := gindexLength_ok measured
  subst path
  apply excludes
  rw [← List.map_drop]
  refine List.mem_map.mpr ⟨step, List.mem_drop_iff_getElem.mpr ⟨step - 1, by simp; omega, ?_⟩, rfl⟩
  simp only [List.getElem_range]
  omega

/-- A shifted node below the root was reached before exhausting its branch. -/
theorem shift_below_depth {claim step : Nat} (named : 1 ≤ claim)
    (below : 2 ≤ claim >>> step) : step < Nat.log2 claim := by
  -- After the leading bit reaches the root, further shifts can never reach a node below it.
  by_cases inside : step < Nat.log2 claim
  · exact inside
  have upper : (claim >>> Nat.log2 claim) >>> (step - Nat.log2 claim) ≤ 1 := by
    rw [shiftRight_depth named]
    exact shiftRight_le 1 _
  rw [← Nat.shiftRight_add, show Nat.log2 claim + (step - Nat.log2 claim) = step by omega] at upper
  omega

/-- The positions of the claims of a request that passes the checks form an antichain. -/
theorem rejectRelated_antichain {indices : List Nat} (accepted : rejectRelated indices = .ok ()) :
    ∀ a ∈ indices.map (gindexPosition (gindexHeight indices)),
      ∀ b ∈ indices.map (gindexPosition (gindexHeight indices)), a.IsAncestor b → a = b := by
  have valid := rejectRelated_valid accepted
  intro a ha b hb ab
  obtain ⟨ga, claimedA, rfl⟩ := List.mem_map.mp ha
  obtain ⟨gb, claimedB, rfl⟩ := List.mem_map.mp hb
  obtain ⟨k, hk⟩ := ab
  have twoA := valid ga claimedA
  have twoB := valid gb claimedB
  have deepA := log2_le_gindexHeight claimedA
  have deepB := log2_le_gindexHeight claimedB
  -- Climbing `k` levels from one claim lands on the other, which is `k` levels shallower.
  have levels := congrArg Cryptography.Merkle.Position.level hk
  simp only [gindexPosition, Cryptography.Merkle.Position.ancestor_level] at levels
  have depthA : 1 ≤ Nat.log2 ga := (Nat.le_log2 (by omega)).mpr twoA
  by_cases zero : k = 0
  · subst zero
    simpa using hk
  have short : k < Nat.log2 gb := by omega
  rw [gindexPosition_ancestor (by omega) deepB (by omega)] at hk
  -- So the first claim is a strict ancestor of the second, which the checks refuse.
  have shifted : 2 ≤ gb >>> k := path_shift_positive (by omega) short
  have same := congrArg (positionGindex (gindexHeight indices)) hk
  rw [positionGindex_gindexPosition (by omega) deepA,
    positionGindex_gindexPosition (by omega)
      (Nat.le_trans (levelOf_mono (by omega) (shiftRight_le gb k)) deepB)] at same
  exact absurd (same ▸ claimedA)
    (rejectRelated_strict_shift accepted claimedB (by omega) short)

/-- No supplied claim or helper is a strict ancestor of another supplied node. -/
theorem getHelperIndices_antichain {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    ∀ i ∈ indices ++ helpers, ∀ j ∈ indices ++ helpers, ∀ step,
      i >>> step = j → i = j := by
  obtain ⟨accepted, shape⟩ := getHelperIndices_ok built
  have valid := rejectRelated_valid accepted
  have inside := rejectRelated_inTree accepted
  -- Each supplied index is the index of a claim position or a Merkle helper, in the tree.
  have supplied : ∀ i ∈ indices ++ helpers,
      ∃ a ∈ indices.map (gindexPosition (gindexHeight indices)) ++
        Cryptography.Merkle.helpers (gindexHeight indices)
          (indices.map (gindexPosition (gindexHeight indices))),
      InTree (gindexHeight indices) a ∧ positionGindex (gindexHeight indices) a = i := by
    intro i member
    rcases List.mem_append.mp member with claimed | helper
    · refine ⟨_, List.mem_append_left _ (List.mem_map_of_mem claimed),
        inside _ (List.mem_map_of_mem claimed), ?_⟩
      exact positionGindex_gindexPosition (by have := valid i claimed; omega)
        (log2_le_gindexHeight claimed)
    · rw [shape] at helper
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp helper
      exact ⟨a, List.mem_append_right _ ha, Cryptography.Merkle.helpers_inside inside ha, rfl⟩
  intro i hi j hj step shifted
  obtain ⟨a, ha, aInside, rfl⟩ := supplied i hi
  obtain ⟨b, hb, bInside, rfl⟩ := supplied j hj
  obtain ⟨aNamed, aDepth⟩ := positionGindex_bounds aInside
  obtain ⟨bNamed, -⟩ := positionGindex_bounds bInside
  by_cases reach : a.level + step ≤ gindexHeight indices
  · -- The shift is the ancestor `step` levels up, which the antichain makes the node itself.
    rw [← positionGindex_ancestor aInside reach] at shifted
    have same := positionGindex_injective (inTree_ancestor aInside reach) bInside shifted
    have := Cryptography.Merkle.helpers_antichain (rejectRelated_antichain accepted) b hb a ha
      ⟨step, same.symm⟩
    rw [this]
  · -- Past the root, the shift is 0, which is no index.
    have small : positionGindex (gindexHeight indices) a < 2 ^ step := by
      have := Nat.lt_log2_self (n := positionGindex (gindexHeight indices) a)
      have low : a.level ≤ gindexHeight indices := aInside.level_le
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt small] at shifted
    omega

end EthLib.Serialization.Ssz
