import EthLib.Consensus.Proofs.Ssz.Merkle.HelperUniqueness

/-! Supplied multiproof nodes form a cut: no supplied node hides another beneath it. -/

namespace EthLib.Consensus.Ssz

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

private theorem sibling_strict_shift (index step : Nat) (positive : 0 < step) :
    gindexSibling index >>> step = index >>> step := by
  -- Siblings differ only in the lowest bit, which the first upward step discards.
  have distance : step - 1 + 1 = step := by omega
  rw [← distance, Nat.add_comm (step - 1) 1, Nat.shiftRight_add, Nat.shiftRight_add]
  have half := gindexSibling_half index
  simpa [Nat.shiftRight_eq_div_pow] using congrArg (fun n => n >>> (step - 1)) half

/-- No supplied claim or helper is a strict ancestor of another supplied node. -/
theorem getHelperIndices_antichain {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    ∀ i ∈ indices ++ helpers, ∀ j ∈ indices ++ helpers, ∀ step,
      i >>> step = j → i = j := by
  -- Every strict ancestor of a helper is also an ancestor of the claim that required that helper.
  obtain ⟨_, valid, frontier⟩ := getHelperIndices_frontier built
  have accepted : rejectRelated indices = .ok () := by
    unfold getHelperIndices at built
    cases checked : rejectRelated indices <;> simp [checked, Bind.bind, Except.bind] at built ⊢
  intro i supplied j target step shifted
  -- Zero upward steps preserve the supplied position itself.
  -- Every positive step must be excluded.
  by_cases zero : step = 0
  · simpa [zero] using shifted
  have positive : 0 < step := by omega
  -- Both claims and helpers lie below the root, so the target ancestor still has a positive branch depth.
  have jBelow : 2 ≤ j := by
    rcases List.mem_append.mp target with claim | helper
    · exact valid j claim
    · exact (helperFrontier_sibling built (Or.inr helper)).1
  -- Climbing from a helper discards its differing child bit and rejoins an original claim path.
  have origin : ∃ claim ∈ indices, ∃ distance, 0 < distance ∧ claim >>> distance = j := by
    rcases List.mem_append.mp supplied with claim | helper
    · exact ⟨i, claim, step, positive, shifted⟩
    · obtain ⟨mapped, _⟩ := (frontier i).mp helper
      obtain ⟨node, path, same⟩ := List.mem_map.mp mapped
      obtain ⟨claim, claimed, member⟩ := List.mem_flatMap.mp path
      obtain ⟨base, _, baseEq⟩ := List.mem_map.mp member
      refine ⟨claim, claimed, base + step, by omega, ?_⟩
      rw [Nat.shiftRight_add, baseEq, ← sibling_strict_shift node step positive, same]
      exact shifted
  obtain ⟨claim, claimed, distance, strict, reaches⟩ := origin
  have below := shift_below_depth (by have := valid claim claimed; omega)
    (show 2 ≤ claim >>> distance by omega)
  -- The target ancestor is therefore a reconstructible path node rather than a missing sibling.
  have onPath : j ∈ claimPaths indices := List.mem_flatMap.mpr
    ⟨claim, claimed, List.mem_map.mpr ⟨distance, List.mem_range.mpr below, reaches⟩⟩
  -- A claimed target violates ancestor rejection, while a helper target violates path exclusion.
  rcases List.mem_append.mp target with target | target
  · exact False.elim (rejectRelated_strict_shift accepted claimed strict below (reaches ▸ target))
  · exact False.elim (((frontier j).mp target).2 onPath)

end EthLib.Consensus.Ssz
