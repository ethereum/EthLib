import EthLib.Serialization.Proofs.Ssz.Merkle.HelperFrontier

/-! A multiproof assigns exactly one supplied node to each claimed or helper index. -/

namespace EthLib.Serialization.Ssz

/-- Removing duplicates keeps a sublist with no repeated entry. -/
theorem eraseDups_sublist_nodup (indices : List Nat) :
    List.Sublist indices.eraseDups indices ∧ indices.eraseDups.Nodup := by
  -- Keep the first occurrence and remove all equal later entries before recursing.
  cases indices with
  | nil => simp
  | cons head rest =>
    rw [List.eraseDups_cons]
    -- Removing later copies makes the retained head distinct from every recursively retained element.
    have filtered := eraseDups_sublist_nodup (rest.filter fun item => !item == head)
    exact ⟨.cons_cons _ (filtered.1.trans List.filter_sublist),
      List.nodup_cons.mpr ⟨by simp, filtered.2⟩⟩
termination_by indices.length
decreasing_by have := List.length_filter_le (fun item => !item == head) rest; simp_all; omega

/-- Duplicate-index rejection leaves each claim with exactly one supplied value. -/
theorem rejectRelated_nodup {indices : List Nat}
    (accepted : rejectRelated indices = .ok ()) : indices.Nodup := by
  -- An unchanged length after deduplication means no claim was repeated.
  by_cases same : indices.eraseDups.length = indices.length
  · exact (eraseDups_sublist_nodup indices).1.eq_of_length same ▸ (eraseDups_sublist_nodup indices).2
  · cases indices with
    | nil => simp at same
    | cons head rest =>
      simp only [List.length_cons] at same
      simp [rejectRelated, same, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- Sorting the deduplicated helper frontier preserves uniqueness. -/
theorem getHelperIndices_nodup {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) : helpers.Nodup := by
  -- Filtering and sorting preserve the uniqueness established by deduplication.
  unfold getHelperIndices at built
  cases accepted : rejectRelated indices <;> cases collected : collectPathIndices indices <;>
    simp [accepted, collected, Bind.bind, Except.bind, pure, Except.pure] at built
  subst helpers
  exact (List.mergeSort_perm _ _).symm.nodup ((eraseDups_sublist_nodup _).2.filter _)

/-- Claimed nodes and required helpers never assign two values to the same index. -/
theorem getHelperIndices_all_nodup {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) : (indices ++ helpers).Nodup := by
  -- Claims lie on their own paths, whereas helpers are explicitly excluded from every claim path.
  obtain ⟨_, valid, frontier⟩ := getHelperIndices_frontier built
  have claims : indices.Nodup := by
    unfold getHelperIndices at built
    cases accepted : rejectRelated indices with
    | error fault => simp [accepted, Bind.bind, Except.bind] at built
    | ok checked => cases checked; exact rejectRelated_nodup accepted
  -- Uniqueness of the combined frontier also requires the claim and helper sets to be disjoint.
  refine List.nodup_append.mpr ⟨claims, getHelperIndices_nodup built, ?_⟩
  rintro claim claimed _ supplied rfl
  exact (frontier claim |>.mp supplied).2 (claim_mem_paths valid claimed)

end EthLib.Serialization.Ssz
