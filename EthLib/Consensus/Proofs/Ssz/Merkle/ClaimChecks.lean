import EthLib.Consensus.Proofs.Ssz.Merkle.HelperUniqueness

/-!
The index checks of a multiproof, read one claim at a time.

A path is walked by halving until the root, and a claim is refused when one of its strict ancestors is claimed too.
-/

namespace EthLib.Consensus.Ssz

/-- The level of an index halves away: one fewer level per halving, down to one. -/
theorem log2_half (index : Nat) (two : 2 ≤ index) : Nat.log2 (index / 2) + 1 = Nat.log2 index := by
  rw [Nat.log2_def index]
  -- The definition takes one halving step whenever the index is at least two.
  simp [two]

/-- An index of zero or one sits on level zero. -/
theorem log2_small (index : Nat) (small : index ≤ 1) : Nat.log2 index = 0 := by
  rw [Nat.log2_def index]
  -- The definition stops at once below two.
  simp [show ¬ 2 ≤ index by omega]

/-- An index of two or more has its level as its branch length. -/
theorem gindexLength_of_two {index : Nat} (two : 2 ≤ index) : gindexLength index = .ok (Nat.log2 index) := by
  -- Neither refusal applies: the index names a node, and that node is below the root.
  have half := log2_half index two
  simp only [gindexLength, gindexDepth, show ¬ index < 1 by omega, ite_false, bind, Except.bind]
  simp only [show (Nat.log2 index == 0) = false by simp; omega]
  rfl

/-- An index and its ancestors below the root, the deepest first. -/
def pathOf (index : Nat) : List Nat :=
  (List.range (Nat.log2 index)).map fun step => index >>> step

/-- Zero and the root have no path below the root. -/
theorem pathOf_small (index : Nat) (small : index ≤ 1) : pathOf index = [] := by
  -- Their level is zero, so the path has no step.
  simp [pathOf, log2_small index small]

/-- An index of two or more starts its path, and its parent's path follows. -/
theorem pathOf_cons (index : Nat) (two : 2 ≤ index) : pathOf index = index :: pathOf (index / 2) := by
  have half := log2_half index two
  rw [pathOf, ← half, List.range_succ_eq_map, List.map_cons, List.map_map, pathOf]
  -- One more shift is one halving first.
  congr 1
  apply List.map_congr_left
  intro step _
  simp only [Function.comp, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm]

/-- The paths of several claims, one after the other, are the claim paths. -/
theorem claimPaths_eq (indices : List Nat) : claimPaths indices = indices.flatMap pathOf := rfl

/-- A claim is refused for its strict ancestors exactly when one of them is claimed too. -/
theorem rejectAncestors_eq (indices : List Nat) (claim : Nat) :
    ∀ ancestors : List Nat, rejectAncestors indices claim ancestors =
      if ancestors.any (fun x => indices.contains x) then .error (.nestedIndex claim) else .ok ()
  | [] => rfl
  | x :: rest => by
    -- The first ancestor is checked, then the rest in order.
    rw [rejectAncestors]
    by_cases hx : x ∈ indices
    · simp [hx, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    · rw [rejectAncestors_eq indices claim rest]
      simp [hx]

/-- One claim: zero and the root are refused, then a claimed strict ancestor, then the rest are checked. -/
theorem rejectClaimPaths_cons (indices : List Nat) (claim : Nat) (rest : List Nat) :
    rejectClaimPaths indices (claim :: rest) =
      if claim = 0 then .error (.notAGindex 0) else if claim = 1 then .error .rootHasNoBranch
      else if (pathOf (claim / 2)).any (fun x => indices.contains x) then .error (.nestedIndex claim)
      else rejectClaimPaths indices rest := by
  by_cases zero : claim = 0
  · subst zero
    simp [rejectClaimPaths, getPathIndices, gindexLength, gindexDepth, bind, Except.bind]
  by_cases one : claim = 1
  · subst one
    simp [rejectClaimPaths, getPathIndices, gindexLength, gindexDepth, bind, Except.bind, log2_small 1]
  -- Past both refusals, the path is the claim followed by its strict ancestors.
  have two : 2 ≤ claim := by omega
  have path : getPathIndices claim = .ok (pathOf claim) := by
    simp [getPathIndices, gindexLength_of_two two, pathOf, bind, Except.bind, pure, Except.pure]
  simp only [rejectClaimPaths, path, zero, one, ite_false, bind, Except.bind, pathOf_cons claim two,
    List.drop_succ_cons, List.drop_zero, rejectAncestors_eq]
  by_cases a : ∃ x, x ∈ pathOf (claim / 2) ∧ x ∈ indices <;> simp [a]

/-- Claims checked in two runs are checked as one. -/
theorem rejectClaimPaths_append (indices : List Nat) :
    ∀ first second : List Nat, rejectClaimPaths indices (first ++ second) =
      (rejectClaimPaths indices first).bind fun _ => rejectClaimPaths indices second
  | [], _ => rfl
  | claim :: rest, second => by
    -- A refusal in the first run stops both sides, and otherwise the rest of the run continues.
    rw [List.cons_append, rejectClaimPaths_cons, rejectClaimPaths_cons]
    split
    · rfl
    split
    · rfl
    split
    · rfl
    exact rejectClaimPaths_append indices rest second

/-- A list keeps its length after removing duplicates exactly when it has none. -/
theorem eraseDups_length_iff (indices : List Nat) : indices.eraseDups.length = indices.length ↔ indices.Nodup := by
  constructor
  · intro same
    exact (eraseDups_sublist_nodup indices).1.eq_of_length same ▸ (eraseDups_sublist_nodup indices).2
  · intro nodup
    -- With no duplicates there is nothing to remove.
    have : indices.eraseDups = indices := by
      induction indices with
      | nil => rfl
      | cons head rest ih =>
        rw [List.eraseDups_cons]
        have fresh := (List.nodup_cons.mp nodup)
        rw [List.filter_eq_self.mpr (by intro x hx; simp; intro e; subst e; exact fresh.1 hx), ih fresh.2]
    rw [this]

/-- The index checks: no index, a repeated index, then each claim in order. -/
theorem rejectRelated_eq (indices : List Nat) :
    rejectRelated indices =
      if indices = [] then .error .emptyRequest else if ¬ indices.Nodup then .error .repeatedIndex
      else rejectClaimPaths indices indices := by
  by_cases empty : indices = []
  · subst empty; rfl
  -- Duplicates are detected by the length lost when they are removed.
  by_cases nodup : indices.Nodup
  · have : (indices.eraseDups.length != indices.length) = false := by
      simp [(eraseDups_length_iff indices).mpr nodup]
    simp [rejectRelated, empty, nodup, this]
  · have : (indices.eraseDups.length != indices.length) = true := by
      simp only [bne_iff_ne, ne_eq]; exact fun h => nodup ((eraseDups_length_iff indices).mp h)
    simp [rejectRelated, empty, nodup, this, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

end EthLib.Consensus.Ssz
