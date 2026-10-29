import EthLib.Consensus.Proofs.Ssz.Merkle.HelperAntichain
import EthLib.Consensus.Proofs.Ssz.Merkle.MultiproofAcceptance

/-! A multiproof of one claim is the single-item proof of that claim. -/

namespace EthLib.Consensus.Ssz

/-- A list without repeats loses nothing when its duplicates are removed. -/
private theorem eraseDups_of_nodup : ∀ {nodes : List Nat}, nodes.Nodup → nodes.eraseDups = nodes
  | [], _ => rfl
  | head :: rest, unique => by
    -- The head occurs nowhere later, so removing its copies keeps the whole tail.
    obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
    rw [List.eraseDups_cons, List.filter_eq_self.mpr (by grind), eraseDups_of_nodup unique]

/-- A sibling is one more than an even node, or one less than an odd node. -/
private theorem gindexSibling_cases (index : Nat) :
    (index % 2 = 0 ∧ gindexSibling index = index + 1) ∨
      (index % 2 = 1 ∧ gindexSibling index = index - 1) := by
  rcases Nat.mod_two_eq_zero_or_one index with side | side
  · exact .inl ⟨side, by have := gindexSibling_even side; omega⟩
  · exact .inr ⟨side, by have := gindexSibling_odd side; omega⟩

/--
Two nodes on one path, one strictly above the other and both below the root.

The lower node is at least twice the higher one, which is what orders their siblings.
-/
private theorem branch_levels {index low high : Nat} (named : 1 ≤ index) (ordered : low < high)
    (below : high < Nat.log2 index) :
    2 ≤ index >>> high ∧ index >>> high ≤ index >>> low / 2 := by
  -- Climbing past the next level can only shrink the node further.
  have shrinks := shiftRight_le (index >>> (low + 1)) (high - (low + 1))
  rw [← Nat.shiftRight_add, show low + 1 + (high - (low + 1)) = high by omega,
    shiftRight_succ] at shrinks
  exact ⟨path_shift_positive named below, shrinks⟩

/--
With one claim, the helpers are its branch in the same order.

This is why the spec sorts helpers in decreasing order.
-/
theorem getHelperIndices_singleton (index : Nat) :
    getHelperIndices [index] = getBranchIndices index := by
  unfold getHelperIndices getBranchIndices
  cases measured : getPathIndices index with
  | error fault =>
    simp [rejectRelated, rejectClaimPaths, measured, List.eraseDups_cons, Bind.bind, Except.bind]
  | ok path =>
    -- The path is the index halved once per level, up to just below the root.
    obtain ⟨spelled, named⟩ : path = (List.range (Nat.log2 index)).map (index >>> ·) ∧ 1 ≤ index := by
      unfold getPathIndices at measured
      cases length : gindexLength index <;>
        simp [length, Bind.bind, Except.bind, pure, Except.pure] at measured
      exact ⟨by rw [← measured, (gindexLength_ok length).1], (gindexLength_ok length).2.1⟩
    -- Every node above the claim is smaller than it, so no ancestor repeats the claim.
    have ancestors : rejectAncestors [index] index path.tail = .ok () := by
      suffices fresh : index ∉ path.tail by
        generalize path.tail = later at fresh
        induction later <;> simp_all [rejectAncestors, eq_comm]
      rw [← List.drop_one, spelled, ← List.map_drop, List.mem_map]
      rintro ⟨step, member, same⟩
      obtain ⟨later, _, picked⟩ := List.mem_drop_iff_getElem.mp member
      simp only [List.getElem_range] at picked
      subst picked
      have shrinks := shiftRight_le (index >>> 1) later
      have half : index >>> 1 = index / 2 := by simp [Nat.shiftRight_eq_div_pow]
      rw [← Nat.shiftRight_add, same, half] at shrinks
      omega
    -- Lower siblings are larger, so the branch is already in decreasing order.
    have decreasing : (path.map gindexSibling).Pairwise (· > ·) := by
      rw [spelled, List.map_map, List.pairwise_map]
      refine List.pairwise_lt_range.imp_of_mem fun lowMember highMember ordered => ?_
      have levels := branch_levels named ordered (List.mem_range.mp highMember)
      have low := path_shift_positive named (List.mem_range.mp lowMember)
      grind [gindexSibling_cases]
    -- A sibling is never on the path, since it sits beside the path at its own level.
    have outside : ∀ node ∈ path.map gindexSibling, node ∉ path := by
      simp only [spelled, List.map_map, List.mem_map, List.mem_range]
      rintro _ ⟨step, below, rfl⟩ ⟨other, otherBelow, same⟩
      have levels := path_shift_positive named below
      rcases Nat.lt_trichotomy step other with ordered | rfl | ordered
      · have := branch_levels named ordered otherBelow
        grind [gindexSibling_cases]
      · grind [gindexSibling_cases]
      · have := branch_levels named ordered below
        grind [gindexSibling_cases]
    -- Validation passes, and sorting, filtering, and deduplication then change nothing.
    simp [rejectRelated, rejectClaimPaths, collectPathIndices, measured, ancestors,
      List.eraseDups_cons, Bind.bind, Except.bind, pure, Except.pure]
    rw [eraseDups_of_nodup (decreasing.imp Nat.ne_of_gt),
      List.filter_eq_self.mpr (fun node member => by simpa using outside node member),
      List.mergeSort_of_pairwise (decreasing.imp fun ordered => by simpa using Nat.le_of_lt ordered)]

/-- Climbing one more node adds one hash at the top of the climb. -/
private theorem climbBranch_append (index : Nat) : ∀ (level : Nat) (node last : Bytes)
    (siblings : List Bytes), climbBranch index level node (siblings ++ [last]) =
      if gindexBit index (level + siblings.length)
      then combine last (climbBranch index level node siblings)
      else combine (climbBranch index level node siblings) last
  | _, _, _, [] => by simp [climbBranch]
  | level, node, last, sibling :: rest => by
    simp only [List.cons_append, climbBranch, List.length_cons]
    rw [climbBranch_append index (level + 1)]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- With one claim, the multiproof fold rebuilds the root the single-item climb reaches. -/
theorem calculateMultiMerkleRootUnchecked_singleton {leaf root : Bytes} {proof : List Bytes}
    {index : Nat} (single : calculateMerkleRootUnchecked leaf proof index = .ok root) :
    calculateMultiMerkleRootUnchecked [leaf] proof [index] = .ok root := by
  -- The single-item check fixes the branch length and the root the climb reaches.
  unfold calculateMerkleRootUnchecked at single
  cases measured : gindexLength index with
  | error fault => simp [measured, Bind.bind, Except.bind] at single
  | ok depth =>
  obtain ⟨rfl, named, deep⟩ := gindexLength_ok measured
  simp only [measured, Bind.bind, Except.bind] at single
  split at single
  · simp [throw, throwThe, MonadExceptOf.throw] at single
  rename_i counted
  have count : proof.length = Nat.log2 index := by simpa using counted
  simp only [pure, Except.pure, Except.ok.injEq] at single
  -- The helpers are the branch, so the proof values line up with them one to one.
  let branch := (List.range (Nat.log2 index)).map fun step => gindexSibling (index >>> step)
  have built : getHelperIndices [index] = .ok branch := by
    simp [getHelperIndices_singleton, getBranchIndices, getPathIndices, measured, branch,
      List.map_map, Function.comp_def, Bind.bind, Except.bind, pure, Except.pure]
  obtain ⟨rebuiltRoot, rebuilt⟩ := calculateMultiMerkleRootUnchecked_complete (leaves := [leaf]) (proof := proof) built rfl
    (by simp [branch, count])
  obtain ⟨helpers, again, _, _, folded⟩ := calculateMultiMerkleRootUnchecked_shape rebuilt
  rw [built] at again
  cases again
  -- The fold computes the root of the tree cut at the supplied nodes.
  let nodes := [index].zip [leaf] ++ branch.zip proof
  have positions : nodes.map Prod.fst = [index] ++ branch := by
    simp [nodes, List.map_fst_zip, branch, count]
  have separated : ProofAntichain nodes := by
    simpa only [ProofAntichain, positions] using getHelperIndices_antichain built
  have unique : (nodes.map Prod.fst).Nodup := positions ▸ getHelperIndices_all_nodup built
  rw [rebuilt, foldToRoot_eq_proofTree separated unique folded, ← single]
  -- The tree is at least as tall as the claim is deep.
  have tall : Nat.log2 index ≤ multiproofHeight [index] branch :=
    member_le_foldl_max (List.mem_map_of_mem (f := levelOf) (by simp)) 0
  generalize multiproofHeight [index] branch = height at tall
  -- Each node on the path holds the climb so far, from the leaf up to the root.
  have climbs : ∀ step, step ≤ Nat.log2 index →
      (proofTree nodes (height - Nat.log2 index + step) (index >>> step)).root =
        climbBranch index 0 leaf (proof.take step) := by
    intro step
    induction step with
    | zero =>
      intro _
      simp [proofTree_supplied _ _ _ (by simp [nodes, nodeAt] : nodeAt nodes index = some leaf),
        CommitmentTree.root, climbBranch]
    | succ step ih =>
      intro below
      -- A path node above the claim is not supplied, since it would sit above the claim.
      have absent : nodeAt nodes (index >>> (step + 1)) = none := by
        cases found : nodeAt nodes (index >>> (step + 1)) with
        | none => rfl
        | some value =>
          have supplied : index >>> (step + 1) ∈ nodes.map Prod.fst :=
            List.mem_map.mpr ⟨_, nodeAt_member found, rfl⟩
          rw [positions] at supplied
          have same := getHelperIndices_antichain built index (by simp) _ supplied _ rfl
          have shrinks := shiftRight_le index step
          rw [shiftRight_succ] at same
          omega
      -- The sibling at this level is supplied, holding the proof value of this level.
      have sibling : nodeAt nodes (gindexSibling (index >>> step)) = some proof[step] := by
        apply nodeAt_of_unique unique
        apply List.mem_append_right
        exact List.mem_iff_getElem.mpr ⟨step, by simp [branch, count]; omega, by simp [branch]⟩
      rw [show height - Nat.log2 index + (step + 1) = height - Nat.log2 index + step + 1 by omega,
        List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, climbBranch_append,
        gindexBit_parity]
      rw [shiftRight_succ] at absent
      simp only [proofTree, absent, shiftRight_succ, List.length_take, count,
        Nat.min_eq_left (by omega : step ≤ Nat.log2 index), Nat.zero_add]
      -- The turn at this level says which child is on the path and which is the sibling.
      rcases gindexSibling_cases (index >>> step) with ⟨side, pair⟩ | ⟨side, pair⟩
      · rw [show 2 * (index >>> step / 2) = index >>> step by omega, ← pair,
          proofTree_supplied _ _ _ sibling]
        simp [CommitmentTree.root, ih (by omega), side]
      · have left : 2 * (index >>> step / 2) = gindexSibling (index >>> step) := by omega
        have right : gindexSibling (index >>> step) + 1 = index >>> step := by omega
        rw [left, right, proofTree_supplied _ _ _ sibling]
        simp [CommitmentTree.root, ih (by omega), side]
  have top := climbs (Nat.log2 index) (Nat.le_refl _)
  rw [shiftRight_depth named, Nat.sub_add_cancel tall, List.take_of_length_le (by omega)] at top
  rw [top]

/--
A valid single-item proof also passes the multi-item verifier, with the same verdict.

The leaf and the index each become a list of one, and the proof is passed as it is.
-/
theorem verifyMerkleMultiproof_singleton {leaf root : Bytes} {proof : List Bytes} {index : Nat}
    {verdict : Bool} (single : verifyMerkleProof leaf proof index root = .ok verdict) :
    verifyMerkleMultiproof [leaf] proof [index] root = .ok verdict := by
  -- Both verifiers rebuild the root, then run the same width checks before comparing it.
  unfold verifyMerkleProof calculateMerkleRoot at single
  cases rebuilt : calculateMerkleRootUnchecked leaf proof index <;> cases leafWidth : checkChunk leaf <;>
    cases proofWidths : checkChunks proof <;>
    simp [leafWidth, proofWidths, rebuilt, Bind.bind, Except.bind, pure,
      Except.pure] at single
  simp [verifyMerkleMultiproof, calculateMultiMerkleRoot, checkChunks, leafWidth, proofWidths,
    calculateMultiMerkleRootUnchecked_singleton rebuilt, single, Bind.bind, Except.bind, pure, Except.pure]

end EthLib.Consensus.Ssz
