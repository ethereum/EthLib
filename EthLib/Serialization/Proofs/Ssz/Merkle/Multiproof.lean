module

public import EthLib.Serialization.Proofs.Ssz.Merkle.HelperAntichain
import EthLib.Base.Proofs.List

/-! An SSZ multiproof is the Merkle multiproof at the positions of its indices. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Cryptography.Merkle

/-- Every stored node agrees with the tree at its claimed position. -/
def NodesAgree (tree : Nat → Bytes) (nodes : List (Nat × Bytes)) : Prop :=
  -- Each stored pair must match the reference reading at its own index.
  ∀ index value, (index, value) ∈ nodes → value = tree index

/-- Parent equations needed within a finite tree, with no conditions below its leaves. -/
def ParentsAgree (tree : Nat → Bytes) (height : Nat) : Prop :=
  -- Only even children inside the finite height range need parent equations.
  ∀ index, 2 ≤ index → levelOf index ≤ height → index % 2 = 0 →
    combine (tree index) (tree (index + 1)) = tree (gindexParent index)

/-- Parent equations up to some height hold up to any lower height. -/
theorem ParentsAgree.mono {tree : Nat → Bytes} {low high : Nat} (parents : ParentsAgree tree high)
    (le : low ≤ high) : ParentsAgree tree low :=
  fun index two level even => parents index two (Nat.le_trans level le) even

/-- Reading any index sequence from a tree yields a node set agreeing with that tree. -/
theorem nodesAgree_zip_map (tree : Nat → Bytes) (indices : List Nat) :
    NodesAgree tree (indices.zip (indices.map tree)) := by
  -- Every pair consists of an index and precisely the value read at that index.
  induction indices with
  | nil => simp [NodesAgree]
  | cons index rest ih =>
    simp only [NodesAgree, List.map_cons, List.zip_cons_cons, List.mem_cons] at ih ⊢
    grind

/-- Two agreeing node sets can be supplied together without changing their meaning. -/
theorem NodesAgree.append {tree : Nat → Bytes} {left right : List (Nat × Bytes)}
    (leftAgree : NodesAgree tree left) (rightAgree : NodesAgree tree right) :
    NodesAgree tree (left ++ right) := by
  -- Each supplied pair originates in one of the two inputs.
  exact fun i value member => (List.mem_append.mp member).elim (leftAgree i value) (rightAgree i value)

/-- The nodes a multiproof gives, at their positions in the tree of the given height. -/
def multiproofNodes (height : Nat) (indices helpers : List Nat) (leaves proof : List Bytes) :
    List (Position × Bytes) :=
  ((indices ++ helpers).map (gindexPosition height)).zip (leaves ++ proof)

/-- Every claim and helper of a request that passes the checks is an index of the tree. -/
theorem getHelperIndices_valid {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    ∀ g ∈ indices ++ helpers, 1 ≤ g ∧ Nat.log2 g ≤ gindexHeight indices := by
  obtain ⟨accepted, shape⟩ := getHelperIndices_ok built
  intro g member
  rcases List.mem_append.mp member with claimed | helper
  · exact ⟨by have := rejectRelated_valid accepted g claimed; omega,
      log2_le_gindexHeight claimed⟩
  · -- A helper is the index of a node of the tree.
    rw [shape] at helper
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp helper
    obtain ⟨named, depth⟩ :=
      positionGindex_bounds (helpers_inside (rejectRelated_inTree accepted) hq)
    exact ⟨named, by omega⟩

/-- With the counts checked, the multiproof nodes are the opened nodes and the Merkle helpers.

So the SSZ verifier is the Merkle verifier at the positions of the indices. -/
theorem multiproofNodes_eq {indices helpers : List Nat} {leaves proof : List Bytes}
    (built : getHelperIndices indices = .ok helpers) (leafCount : leaves.length = indices.length) :
    multiproofNodes (gindexHeight indices) indices helpers leaves proof =
      (indices.map (gindexPosition (gindexHeight indices))).zip leaves ++
        (Cryptography.Merkle.helpers (gindexHeight indices)
          (indices.map (gindexPosition (gindexHeight indices)))).zip proof := by
  obtain ⟨accepted, shape⟩ := getHelperIndices_ok built
  -- The positions of the helper indices are the helpers themselves.
  have back : helpers.map (gindexPosition (gindexHeight indices)) =
      Cryptography.Merkle.helpers (gindexHeight indices)
        (indices.map (gindexPosition (gindexHeight indices))) := by
    rw [shape, List.map_map]
    refine (List.map_congr_left (g := id) fun q hq => ?_).trans (List.map_id _)
    exact gindexPosition_positionGindex (helpers_inside (rejectRelated_inTree accepted) hq)
  rw [multiproofNodes, List.map_append, List.zip_append (by simp [leafCount]), back]

/-- The SSZ multiproof root, read through the Merkle rebuild of its nodes. -/
theorem calculateMultiMerkleRootUnchecked_eq {indices helpers : List Nat}
    {leaves proof : List Bytes} (built : getHelperIndices indices = .ok helpers)
    (leafCount : leaves.length = indices.length) (proofCount : proof.length = helpers.length) :
    calculateMultiMerkleRootUnchecked leaves proof indices =
      match (rebuild sszNodeHash (multiproofNodes (gindexHeight indices) indices helpers leaves
          proof) (gindexHeight indices)).run with
      | some root => .ok root
      | none => .error .proofIncomplete := by
  obtain ⟨accepted, shape⟩ := getHelperIndices_ok built
  -- The checks pass, and the helper positions have as many entries as the helper indices.
  have count : proof.length = (Cryptography.Merkle.helpers (gindexHeight indices)
      (indices.map (gindexPosition (gindexHeight indices)))).length := by
    rw [proofCount, shape, List.length_map]
  rw [multiproofNodes_eq built leafCount]
  simp only [calculateMultiMerkleRootUnchecked, leafCount, claimPositions_ok accepted, count,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  split
  · next root rebuilt => rw [rebuilt]; rfl
  · next rebuilt => rw [rebuilt]; rfl

/-- A successful reconstruction checked the counts and the helpers, and is the Merkle rebuild. -/
theorem calculateMultiMerkleRootUnchecked_shape {leaves proof : List Bytes} {indices : List Nat}
    {root : Bytes} (built : calculateMultiMerkleRootUnchecked leaves proof indices = .ok root) :
    ∃ helpers, getHelperIndices indices = .ok helpers ∧ leaves.length = indices.length ∧
      proof.length = helpers.length ∧
      (rebuild sszNodeHash (multiproofNodes (gindexHeight indices) indices helpers leaves proof)
        (gindexHeight indices)).run = some root := by
  -- The leaf count is checked first.
  have leafCount : leaves.length = indices.length := by
    unfold calculateMultiMerkleRootUnchecked at built
    split at built
    · simp [throw, Bind.bind, Except.bind] at built
    · next count => simpa using count
  -- Then the request.
  have accepted : rejectRelated indices = .ok () := by
    cases accepted : rejectRelated indices with
    | error fault =>
      simp [calculateMultiMerkleRootUnchecked, claimPositions, accepted, leafCount, Bind.bind,
        Except.bind] at built
    | ok checked => rfl
  have helpers := getHelperIndices_of_rejectRelated accepted
  -- Then the proof count, against the helpers.
  have proofCount : proof.length = ((Cryptography.Merkle.helpers (gindexHeight indices)
      (indices.map (gindexPosition (gindexHeight indices)))).map
        (positionGindex (gindexHeight indices))).length := by
    rw [List.length_map]
    unfold calculateMultiMerkleRootUnchecked at built
    simp only [leafCount, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      claimPositions_ok accepted, Bind.bind, Except.bind] at built
    split at built
    · simp [throw] at built
    · next count => simpa using count
  refine ⟨_, helpers, leafCount, proofCount, ?_⟩
  rw [calculateMultiMerkleRootUnchecked_eq helpers leafCount proofCount] at built
  split at built
  · next root' rebuilt => cases built; exact rebuilt
  · cases built

/-- Correct counts and helper positions are sufficient for multiproof reconstruction to finish. -/
theorem calculateMultiMerkleRootUnchecked_complete {leaves proof : List Bytes}
    {indices helpers : List Nat} (built : getHelperIndices indices = .ok helpers)
    (leafCount : leaves.length = indices.length) (proofCount : proof.length = helpers.length) :
    ∃ root, calculateMultiMerkleRootUnchecked leaves proof indices = .ok root := by
  obtain ⟨accepted, shape⟩ := getHelperIndices_ok built
  -- The Merkle rebuild of a nonempty request in the tree always succeeds.
  obtain ⟨root, rebuilt⟩ := Option.isSome_iff_exists.mp
    (verify_isSome sszNodeHash (by simpa using rejectRelated_nonempty accepted)
      (rejectRelated_inTree accepted) (by simpa using leafCount)
      (by simpa [shape] using proofCount))
  refine ⟨root, ?_⟩
  rw [calculateMultiMerkleRootUnchecked_eq built leafCount proofCount,
    multiproofNodes_eq built leafCount]
  simp only [verify] at rebuilt
  simp [rebuilt]

/-- A successful reconstruction agrees with the finite tree supplying its nodes. -/
theorem calculateMultiMerkleRootUnchecked_agrees {tree : Nat → Bytes}
    {leaves proof : List Bytes} {indices helpers : List Nat}
    (helperIndices : getHelperIndices indices = .ok helpers)
    (leafValues : NodesAgree tree (indices.zip leaves))
    (proofValues : NodesAgree tree (helpers.zip proof))
    (parents : ParentsAgree tree
      (((indices.zip leaves ++ helpers.zip proof).map fun pair => levelOf pair.1).foldl max 0))
    {root : Bytes} (built : calculateMultiMerkleRootUnchecked leaves proof indices = .ok root) :
    root = tree 1 := by
  -- The counts were checked before the rebuild.
  obtain ⟨helpers', again, leafCount, proofCount, rebuilt⟩ :=
    calculateMultiMerkleRootUnchecked_shape built
  rw [helperIndices] at again
  cases again
  let H := gindexHeight indices
  have valid := getHelperIndices_valid helperIndices
  -- The tree is consistent up to the depth of the deepest claim.
  have tall : H ≤ ((indices.zip leaves ++ helpers.zip proof).map fun pair => levelOf pair.1).foldl
      max 0 := by
    apply Nat.le_trans (Nat.le_refl _)
    simp only [H, gindexHeight]
    have keys : (indices.zip leaves ++ helpers.zip proof).map Prod.fst = indices ++ helpers := by
      simp [List.map_fst_zip, leafCount, proofCount]
    have levels : ((indices.zip leaves ++ helpers.zip proof).map fun pair => levelOf pair.1) =
        (indices ++ helpers).map levelOf := by
      rw [← keys, List.map_map]
      rfl
    rw [levels, List.map_append, List.foldl_append]
    exact le_foldl_max _ _
  have consistent : Consistent sszNodeHash H (fun p => tree (positionGindex H p)) := by
    intro p low inside
    obtain ⟨named, depth⟩ := positionGindex_bounds inside
    obtain ⟨left, right⟩ := inTree_children inside low
    have top : p.level ≤ H := inside.level_le
    -- The parent equation at the even child gives the hash of the two children.
    have parent := (parents.mono tall) (2 * positionGindex H p) (by omega)
      (by rw [← positionGindex_left low top]; have := (positionGindex_bounds left).2; simp only
        [levelOf]; omega) (by omega)
    show tree (positionGindex H p) =
      combine (tree (positionGindex H p.left)) (tree (positionGindex H p.right))
    rw [positionGindex_left low top, positionGindex_right low top]
    simpa [gindexParent] using parent.symm
  -- Every node given is the tree's node at its position.
  have agree : ∀ e ∈ multiproofNodes H indices helpers leaves proof,
      tree (positionGindex H e.1) = e.2 := by
    intro e member
    simp only [multiproofNodes, List.zip_map_left] at member
    obtain ⟨⟨g, v⟩, pair, rfl⟩ := List.mem_map.mp member
    obtain ⟨named, deep⟩ := valid g (List.of_mem_zip pair).1
    rw [List.zip_append (by simp [leafCount])] at pair
    show tree (positionGindex H (gindexPosition H g)) = v
    rw [show positionGindex H (gindexPosition H g) = g from
      positionGindex_gindexPosition named deep]
    exact ((leafValues.append proofValues) g v pair).symm
  have same := rebuild_go_agrees sszNodeHash consistent agree rebuilt (Position.IsAncestor.refl _)
  simpa [H, positionGindex] using same

/-- An accepted multiproof names the root of the finite tree supplying its nodes. -/
theorem verifyMerkleMultiproof_agrees {tree : Nat → Bytes}
    {leaves proof : List Bytes} {indices helpers : List Nat}
    (helperIndices : getHelperIndices indices = .ok helpers)
    (leafValues : NodesAgree tree (indices.zip leaves))
    (proofValues : NodesAgree tree (helpers.zip proof))
    (parents : ParentsAgree tree
      (((indices.zip leaves ++ helpers.zip proof).map fun pair => levelOf pair.1).foldl max 0))
    {root : Bytes} (accepted : verifyMerkleMultiproof leaves proof indices root = .ok true) :
    root = tree 1 := by
  -- Width checks can reject a proof, but only reconstruction can accept its root.
  unfold verifyMerkleMultiproof calculateMultiMerkleRoot at accepted
  cases reconstructed : calculateMultiMerkleRootUnchecked leaves proof indices <;>
    cases leafWidths : checkChunks leaves <;> cases proofWidths : checkChunks proof <;>
    simp [leafWidths, proofWidths, reconstructed, Bind.bind, Except.bind, Pure.pure,
      Except.pure] at accepted
  subst root
  exact calculateMultiMerkleRootUnchecked_agrees helperIndices leafValues proofValues parents
    reconstructed

/-- Every valid multiproof read from a finite tree reconstructs that tree's root. -/
theorem multiproof_rebuilds_root {tree : Nat → Bytes} {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers)
    (parents : ParentsAgree tree
      ((((indices.zip (indices.map tree)) ++ helpers.zip (helpers.map tree)).map
        fun pair => levelOf pair.1).foldl max 0)) :
    calculateMultiMerkleRootUnchecked (indices.map tree) (helpers.map tree) indices =
      .ok (tree 1) := by
  -- Reconstruction succeeds, and what it returns agrees with the tree.
  obtain ⟨root, reconstructed⟩ := calculateMultiMerkleRootUnchecked_complete built
    (List.length_map ..) (List.length_map ..)
  have same := calculateMultiMerkleRootUnchecked_agrees built (nodesAgree_zip_map tree indices)
    (nodesAgree_zip_map tree helpers) parents reconstructed
  exact same ▸ reconstructed

/-- Reading only complete hash nodes passes the verifier's list-width check. -/
theorem checkChunks_map {tree : Nat → Bytes} {indices : List Nat}
    (widths : ∀ index ∈ indices, (tree index).size = bytesPerChunk) :
    checkChunks (indices.map tree) = .ok () := by
  -- Each node is checked independently before reconstruction begins.
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp_all [checkChunks, checkChunk_eq, Bind.bind, Except.bind]

/-- A multiproof read from a finite tree of 32-byte nodes is accepted by the public verifier. -/
theorem multiproof_verifies {tree : Nat → Bytes} {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers)
    (parents : ParentsAgree tree
      ((((indices.zip (indices.map tree)) ++ helpers.zip (helpers.map tree)).map
        fun pair => levelOf pair.1).foldl max 0))
    (widths : ∀ index ∈ indices ++ helpers, (tree index).size = bytesPerChunk) :
    verifyMerkleMultiproof (indices.map tree) (helpers.map tree) indices (tree 1) = .ok true := by
  -- Width checks admit the nodes, and full reconstruction produces the expected root.
  have leafWidths := checkChunks_map (fun i member => widths i (List.mem_append.mpr (Or.inl member)))
  have proofWidths := checkChunks_map (fun i member => widths i (List.mem_append.mpr (Or.inr member)))
  simp [verifyMerkleMultiproof, calculateMultiMerkleRoot, leafWidths, proofWidths,
    multiproof_rebuilds_root built parents, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Two sibling claims immediately below the root require no auxiliary nodes. -/
theorem calculateMultiMerkleRootUnchecked_two_children (left right : Bytes) :
    calculateMultiMerkleRootUnchecked [left, right] [] [2, 3] = .ok (combine left right) := by
  have helpers : getHelperIndices [2, 3] = .ok [] := by
    simp [getHelperIndices, claimPositions, rejectRelated, rejectClaimPaths, rejectAncestors,
      getPathIndices,
      gindexLength, gindexDepth, gindexHeight, levelOf, gindexPosition, Cryptography.Merkle.helpers,
      Cryptography.Merkle.helpers.go, Position.covers, Bind.bind, Except.bind, Pure.pure,
      Except.pure, List.range_succ, EthLib.Base.firstRepeated_cons]
  -- The tree holding the two children below the root.
  let tree : Nat → Bytes := fun n => if n = 2 then left else if n = 3 then right else
    combine left right
  have parents : ParentsAgree tree 1 := by
    intro index two level even
    have : index = 2 := by
      have := Nat.lt_log2_self (n := index)
      simp only [levelOf] at level
      have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_succ level)
      omega
    subst this
    simp [tree, gindexParent]
  obtain ⟨root, built⟩ := calculateMultiMerkleRootUnchecked_complete (leaves := [left, right])
    (proof := []) helpers rfl rfl
  have same := calculateMultiMerkleRootUnchecked_agrees (tree := tree) helpers
    (by
      intro index value member
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [tree])
    (by simp [NodesAgree])
    (by simpa using parents.mono (by decide)) built
  rw [built, same]
  simp [tree]

end EthLib.Serialization.Ssz
