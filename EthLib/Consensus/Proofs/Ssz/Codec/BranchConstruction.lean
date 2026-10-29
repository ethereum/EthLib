import EthLib.Consensus.Proofs.Ssz.Codec.WalkerClosure

/-! Readable nodes of a closed finite tree produce branches that reconstruct its root. -/

namespace EthLib.Consensus.Ssz

/-- Every finite upward walk can read its siblings and reconstruct its last ancestor. -/
theorem closed_branch_climb (read : Nat → Except Err Bytes) (closed : WalkerClosed read) :
    ∀ count index level node,
      1 ≤ index >>> (level + count) → read (index >>> level) = .ok node →
      ∃ proof root,
        (((List.range count).map fun step => gindexSibling (index >>> (level + step))).mapM read =
          .ok proof) ∧ read (index >>> (level + count)) = .ok root ∧
          climbBranch index level node proof = root := by
  -- Each readable child supplies a sibling and the parent used by the next step.
  intro count
  induction count with
  | zero =>
    intro index level node _ readable
    exact ⟨[], node, rfl, by simpa using readable, rfl⟩
  | succ count ih =>
    intro index level node reaches readable
    have onward : 1 ≤ index >>> (level + 1 + count) := by
      simpa only [Nat.add_assoc, Nat.add_comm count 1] using reaches
    -- A valid final ancestor implies every intermediate parent remains at or above the root.
    have above : 1 ≤ index >>> (level + 1) := by
      have small := shiftRight_le (index >>> (level + 1)) count
      rw [← Nat.shiftRight_add] at small
      exact Nat.le_trans onward small
    rw [shiftRight_succ] at above
    -- Closure supplies the next sibling and parent from the currently readable child.
    obtain ⟨parent, sibling, parentRead, siblingRead, parentEq⟩ :=
      closed (index >>> level) node (by omega) readable
    obtain ⟨proof, root, proofRead, rootRead, climbed⟩ :=
      ih index (level + 1) parent onward (by simpa only [shiftRight_succ] using parentRead)
    refine ⟨sibling :: proof, root, ?_, ?_, ?_⟩
    -- Advancing the climb level names exactly the suffix of the original sibling list.
    · simp only [Nat.add_assoc, Nat.add_comm 1] at proofRead
      simp [List.range_succ_eq_map, Function.comp_def, siblingRead, proofRead, Bind.bind,
        Except.bind, pure, Except.pure]
    · simpa only [Nat.add_assoc, Nat.add_comm count 1] using rootRead
    -- The current path bit chooses which side of the parent hash receives the supplied sibling.
    · subst parentEq
      rw [← climbed]
      rcases Nat.mod_two_eq_zero_or_one (index >>> level) with bit | bit <;>
        simp [climbBranch, gindexBit_parity, bit]

/-- A readable node of a closed tree has a complete branch reconstructing its root. -/
theorem closed_branch_rebuilds_root {read : Nat → Except Err Bytes} (closed : WalkerClosed read)
    {index : Nat} {indices : List Nat} {node : Bytes}
    (indexed : getBranchIndices index = .ok indices) (readable : read index = .ok node) :
    ∃ proof root, indices.mapM read = .ok proof ∧ read 1 = .ok root ∧
      calculateMerkleRootUnchecked node proof index = .ok root := by
  -- The generalized index fixes exactly how many parent steps reach position one.
  obtain ⟨shape, named, nonzero⟩ := getBranchIndices_eq indexed
  have reaches := shiftRight_depth named
  obtain ⟨proof, root, proofRead, rootRead, climbed⟩ :=
    closed_branch_climb read closed (Nat.log2 index) index 0 node
      (by simpa only [Nat.zero_add, reaches] using Nat.le_refl 1)
      (by simpa only [Nat.shiftRight_zero] using readable)
  simp only [Nat.zero_add, reaches] at rootRead
  simp only [Nat.zero_add] at proofRead
  -- Reading one sibling per ancestor preserves the exact branch length required by verification.
  have length : proof.length = Nat.log2 index := by
    have length_eq : ∀ (items : List Nat) (values : List Bytes),
        items.mapM read = .ok values → values.length = items.length := by
      intro items
      induction items with
      | nil => simp [pure, Except.pure]
      | cons head tail ih =>
        intro values built
        cases headRead : read head <;> cases tailRead : tail.mapM read <;>
          simp_all [List.mapM_cons, Bind.bind, Except.bind, pure, Except.pure]
        grind
    simpa only [List.length_map, List.length_range] using length_eq _ _ proofRead
  -- A valid non-root index exposes precisely the branch depth used by the reconstruction algorithm.
  have measured : gindexLength index = .ok (Nat.log2 index) := by
    simp [gindexLength, gindexDepth, show ¬index < 1 by omega, nonzero, Bind.bind, Except.bind]
  refine ⟨proof, root, by simpa only [shape] using proofRead, rootRead, ?_⟩
  simp [calculateMerkleRootUnchecked, measured, length, climbed, Bind.bind, Except.bind, Pure.pure, Except.pure]

end EthLib.Consensus.Ssz
