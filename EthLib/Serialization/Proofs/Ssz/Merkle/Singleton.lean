module

public import EthLib.Serialization.Proofs.Ssz.Merkle.MultiproofAcceptance

/-! A multiproof of one claim is the single-item proof of that claim. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Cryptography.Merkle

/--
With one claim, the helpers are its branch in the same order.

This is why the helpers come in decreasing order.
-/
theorem getHelperIndices_singleton (index : Nat) :
    getHelperIndices [index] = getBranchIndices index := by
  unfold getHelperIndices claimPositions getBranchIndices
  cases measured : getPathIndices index with
  | error fault =>
    simp [rejectRelated, rejectClaimPaths, measured, List.eraseDups_cons, Bind.bind, Except.bind]
  | ok path =>
    -- The path is the index halved once per level, up to just below the root.
    obtain ⟨spelled, named⟩ : path = (List.range (Nat.log2 index)).map (index >>> ·) ∧
        1 ≤ index := by
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
    -- The checks pass, and the Merkle helpers of one node are the siblings of its path.
    have height : gindexHeight [index] = Nat.log2 index := by simp [gindexHeight, levelOf]
    have inside := gindexPosition_inTree named (Nat.le_of_eq height.symm)
    simp only [rejectRelated, rejectClaimPaths, measured, List.eraseDups_cons,
      Bind.bind, Except.bind, pure, Except.pure, List.isEmpty_cons, Bool.false_eq_true,
      ↓reduceIte, List.filter_nil, List.eraseDups_nil, List.length_cons, List.length_nil,
      bne_self_eq_false, List.map_cons, List.map_nil, height]
    rw [List.drop_one, ancestors]
    dsimp only
    rw [height] at inside
    rw [helpers_singleton inside, spelled, List.map_map, List.map_map]
    congr 1
    -- Each sibling on the path has the sibling index of the path index.
    have count : Nat.log2 index - (gindexPosition (Nat.log2 index) index).level = Nat.log2 index :=
      by simp [gindexPosition]
    simp only [pathTo, count, List.map_map]
    refine List.map_congr_left fun step below => ?_
    have top : (gindexPosition (Nat.log2 index) index).level + step ≤ Nat.log2 index := by
      simp [gindexPosition] at below ⊢; omega
    simp only [Function.comp_apply]
    rw [positionGindex_sibling (by simp [gindexPosition] at below ⊢; omega),
      positionGindex_ancestor inside top,
      positionGindex_gindexPosition named (Nat.le_refl _)]

/-- With one claim, the multiproof rebuilds the root the single-item climb reaches. -/
theorem calculateMultiMerkleRootUnchecked_singleton {leaf root : Bytes} {proof : List Bytes}
    {index : Nat} (single : calculateMerkleRootUnchecked leaf proof index = .ok root) :
    calculateMultiMerkleRootUnchecked [leaf] proof [index] = .ok root := by
  -- The single-item check fixes the branch length and the root the climb reaches.
  obtain ⟨count, climbed⟩ := calculateMerkleRootUnchecked_shape single
  have named : 1 ≤ index := by
    unfold calculateMerkleRootUnchecked at single
    cases measured : gindexLength index <;> simp [measured, Bind.bind, Except.bind] at single
    exact (gindexLength_ok measured).2.1
  -- The helpers are the branch, one per proof value.
  let branch := (List.range (Nat.log2 index)).map fun step => gindexSibling (index >>> step)
  have built : getHelperIndices [index] = .ok branch := by
    rw [getHelperIndices_singleton]
    have depth : Nat.log2 index ≠ 0 := by
      rw [← count]
      intro zero
      unfold calculateMerkleRootUnchecked at single
      cases measured : gindexLength index <;> simp [measured, Bind.bind, Except.bind] at single
      exact (gindexLength_ok measured).2.2 ((gindexLength_ok measured).1.trans (count ▸ zero))
    simp [getBranchIndices, getPathIndices, gindexLength, gindexDepth, show ¬index < 1 by omega,
      depth, Bind.bind, Except.bind, Pure.pure, Except.pure, List.map_map, Function.comp_def,
      branch]
  have height : gindexHeight [index] = Nat.log2 index := by simp [gindexHeight, levelOf]
  have inside := gindexPosition_inTree named (Nat.le_of_eq height.symm)
  have proofCount : proof.length = branch.length := by simp [branch, count]
  rw [calculateMultiMerkleRootUnchecked_eq built rfl proofCount,
    multiproofNodes_eq built rfl]
  -- The Merkle multiproof of one node climbs its path.
  have rebuilt := verify_singleton sszNodeHash inside leaf proof
    (by simp [gindexPosition, count, height])
  simp only [verify] at rebuilt
  simp only [height, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right,
    List.singleton_append] at rebuilt ⊢
  rw [rebuilt, ← climbed]
  have start : gindexPosition (Nat.log2 index) index = ⟨0, index - 2 ^ Nat.log2 index⟩ := by
    simp [gindexPosition]
  rw [start]
  -- The climb reads only the low bits of the index, where the index and its offset agree.
  refine congrArg Except.ok
    (climb_congr_index sszNodeHash (fun _ _ => rfl) proof 0 _ index leaf ?_)
  have := gindex_bounds named
  rw [count]
  exact (Nat.mod_eq_sub_mod this.1).symm

/--
A valid single-item proof also passes the multi-item verifier, with the same verdict.

The leaf and the index each become a list of one, and the proof is passed as it is.
-/
theorem verifyMerkleMultiproof_singleton {leaf root : Bytes} {proof : List Bytes} {index : Nat}
    {verdict : Bool} (single : verifyMerkleProof leaf proof index root = .ok verdict) :
    verifyMerkleMultiproof [leaf] proof [index] root = .ok verdict := by
  -- Both verifiers rebuild the root, then run the same width checks before comparing it.
  unfold verifyMerkleProof calculateMerkleRoot at single
  cases rebuilt : calculateMerkleRootUnchecked leaf proof index <;>
    cases leafWidth : checkChunk leaf <;>
    cases proofWidths : checkChunks proof <;>
    simp [leafWidth, proofWidths, rebuilt, Bind.bind, Except.bind, pure,
      Except.pure] at single
  simp [verifyMerkleMultiproof, calculateMultiMerkleRoot, checkChunks, leafWidth, proofWidths,
    calculateMultiMerkleRootUnchecked_singleton rebuilt, single, Bind.bind, Except.bind, pure,
    Except.pure]

end EthLib.Serialization.Ssz
