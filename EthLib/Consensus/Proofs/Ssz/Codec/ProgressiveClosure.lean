import EthLib.Consensus.Proofs.Ssz.Codec.WalkerClosure
import EthLib.Consensus.Proofs.Ssz.Codec.ProgressiveProofTree

/-! Progressive walks retain readable siblings and parents even when they enter nested values. -/

namespace EthLib.Consensus.Ssz

private theorem progressiveReading_parent_eq (chunks : Array Bytes) (index depth start level : Nat)
    (positive : 0 < depth)
    (interior : ProgressiveInterior chunks.size (index / 2) (depth - 1) start level) :
    progressiveReading chunks (index / 2) (depth - 1) start level =
      if index % 2 = 0 then
        combine (progressiveReading chunks index depth start level)
          (progressiveReading chunks (gindexSibling index) depth start level)
      else combine (progressiveReading chunks (gindexSibling index) depth start level)
        (progressiveReading chunks index depth start level) := by
  -- The current node and its sibling are the two ordered children of their shared parent.
  have equation := progressiveReading_split chunks (index / 2) (depth - 1) start level interior
  rw [show depth - 1 + 1 = depth by omega] at equation
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · obtain ⟨child, sibling⟩ := gindexSibling_even even
    rw [← sibling, ← child] at equation
    simpa only [ite_eq_left even] using equation
  · obtain ⟨child, sibling⟩ := gindexSibling_odd odd
    rw [← child, ← sibling] at equation
    simpa only [ite_eq_right (by omega : index % 2 ≠ 0)] using equation

/-- A successful progressive read has a sibling and parent whenever its nested values do. -/
theorem progressiveNode_closed (layout : MerkleLayout) (budget : Nat) (chunks : Array Bytes)
    (materialized : layoutChunksAt budget layout = .ok chunks)
    (children : ∀ slots, layout.leaves = .nested slots → ∀ child inner,
      some (child, inner) ∈ slots → child.nesting ≤ budget ∧ WalkerClosed (nodeRoot child inner))
    (index depth start level : Nat) (positive : 0 < depth)
    (node : Bytes) (read : progressiveNode budget layout index depth start (4 ^ level) = .ok node) :
    ∃ parent sibling,
      progressiveNode budget layout (index / 2) (depth - 1) start (4 ^ level) = .ok parent ∧
      progressiveNode budget layout (gindexSibling index) depth start (4 ^ level) = .ok sibling ∧
      parent = if index % 2 = 0 then combine node sibling else combine sibling node := by
  -- A left turn delegates to bounded closure, and a right turn repeats the spine argument.
  induction depth generalizing start level node with
  | zero => omega
  | succ depth ih =>
    have count := layoutChunksAt_size budget layout chunks materialized
    -- A successful nonterminal spine read implies the current segment actually exists.
    have occupied : start < layout.leaves.count := Nat.lt_of_not_ge fun past => by
      rw [progressiveNode_step, ite_eq_left past] at read
      cases read
    cases depth with
    | zero =>
      -- Immediately below a spine node, both sides are present even when the suffix is empty.
      have currentPosition : ProgressivePosition chunks.size index 1 start level :=
        ⟨by omega, by split <;> first | omega | trivial⟩
      have siblingPosition : ProgressivePosition chunks.size (gindexSibling index) 1 start level :=
        ⟨by omega, by split <;> first | omega | trivial⟩
      cases (progressiveNode_read materialized index 1 start level currentPosition).symm.trans read
      exact ⟨progressiveReading chunks (index / 2) 0 start level,
        progressiveReading chunks (gindexSibling index) 1 start level,
        progressiveNode_read materialized _ 0 start level trivial,
        progressiveNode_read materialized _ 1 start level siblingPosition,
        progressiveReading_parent_eq chunks index 1 start level (by omega)
          (show start < chunks.size by omega)⟩
    | succ depth =>
      -- Parent and sibling addresses preserve the current spine decision above their final turn.
      have parentTurn : gindexBit (index / 2) depth = gindexBit index (depth + 1) := by
        simp [gindexBit, Nat.testBit_add_one]
      have siblingTurn := gindexBit_sibling_high index (depth + 1) (by omega)
      rw [progressiveNode_step, ite_eq_right (by omega)] at read
      by_cases left : (!gindexBit index (depth + 1)) = true
      · rw [ite_eq_left left] at read
        -- The selected segment or remaining spine supplies the same ordered parent hash for all three reads.
        obtain ⟨parent, sibling, parentRead, siblingRead, equation⟩ :=
          boundedNode_closed layout budget chunks materialized children index (depth + 1)
            start (4 ^ level) (by omega) node read
        refine ⟨parent, sibling, ?_, ?_, equation⟩
        · simpa only [Nat.add_sub_cancel, progressiveNode_step, ite_eq_right (by omega : ¬start ≥ layout.leaves.count),
            parentTurn, ite_eq_left left] using parentRead
        · simpa only [progressiveNode_step, ite_eq_right (by omega : ¬start ≥ layout.leaves.count),
            siblingTurn, ite_eq_left left] using siblingRead
      · rw [ite_eq_right left, ← Nat.pow_succ] at read
        -- The selected segment or remaining spine supplies the same ordered parent hash for all three reads.
        obtain ⟨parent, sibling, parentRead, siblingRead, equation⟩ :=
          ih (start + 4 ^ level) (level + 1) (by omega) node read
        refine ⟨parent, sibling, ?_, ?_, equation⟩
        · simpa only [Nat.add_sub_cancel, progressiveNode_step, ite_eq_right (by omega : ¬start ≥ layout.leaves.count),
            parentTurn, ite_eq_right left, Nat.pow_succ] using parentRead
        · simpa only [progressiveNode_step, ite_eq_right (by omega : ¬start ≥ layout.leaves.count),
            siblingTurn, ite_eq_right left, Nat.pow_succ] using siblingRead

end EthLib.Consensus.Ssz
