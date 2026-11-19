module

public import EthLib.Serialization.Proofs.Ssz.Codec.NodeWidths
public import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain
public import EthLib.Serialization.Proofs.Ssz.Codec.WalkerLaws
public import EthLib.Serialization.Proofs.Ssz.Codec.BranchConstruction
public import EthLib.Serialization.Proofs.Ssz.Merkle.MultiproofAcceptance

/-! Multiproofs constructed from a value reconstruct its root without extending its leaf nodes. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- Each indexed node is a successful read of the value's finite tree. -/
def ReadNodes (read : Nat → Except Err Bytes) (nodes : List (Nat × Bytes)) : Prop :=
  ∀ index node, (index, node) ∈ nodes → read index = .ok node

/-- Reading a list preserves both its length and the value read at each paired index. -/
theorem mapM_readNodes {read : Nat → Except Err Bytes} {indices : List Nat} {values : List Bytes}
    (built : indices.mapM read = .ok values) :
    values.length = indices.length ∧ ReadNodes read (indices.zip values) := by
  -- Each successful head read contributes exactly one indexed output before the remaining reads.
  induction indices generalizing values with
  | nil => simp_all [Pure.pure, Except.pure, ReadNodes]
  | cons index rest ih =>
    cases first : read index <;> cases tail : rest.mapM read <;>
      simp [List.mapM_cons, first, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
    subst values
    obtain ⟨count, reads⟩ := ih tail
    simp only [ReadNodes, List.zip_cons_cons, List.mem_cons] at reads ⊢
    grind

/-- Valid helper positions and genuine node reads always reconstruct the same finite tree's root. -/
theorem closed_multiproof_rebuilds_root {read : Nat → Except Err Bytes} (closed : WalkerClosed read)
    {indices helpers : List Nat} {leaves proof : List Bytes}
    (indexed : getHelperIndices indices = .ok helpers)
    (leafReads : indices.mapM read = .ok leaves) (helperReads : helpers.mapM read = .ok proof) :
    ∃ root, calculateMultiMerkleRootUnchecked leaves proof indices = .ok root ∧ read 1 = .ok root := by
  obtain ⟨leafCount, leavesRead⟩ := mapM_readNodes leafReads
  obtain ⟨proofCount, proofRead⟩ := mapM_readNodes helperReads
  -- The reconstruction succeeds, as the Merkle rebuild of the nodes at their positions.
  obtain ⟨root, reconstructed⟩ := calculateMultiMerkleRootUnchecked_complete indexed leafCount proofCount
  refine ⟨root, reconstructed, ?_⟩
  obtain ⟨helpers', indexed', -, -, rebuilt⟩ :=
    calculateMultiMerkleRootUnchecked_shape reconstructed
  rw [indexed] at indexed'
  cases indexed'
  let H := gindexHeight indices
  have valid := getHelperIndices_valid indexed
  -- Every rebuilt node in the tree is the node the reader returns at its index.
  have reads := Cryptography.Merkle.rebuild_go_induction sszNodeHash
    (fun p v => InTree H p → read (positionGindex H p) = .ok v) (nodes :=
      multiproofNodes H indices helpers leaves proof) ?_ ?_ H 0 root rebuilt
    (Cryptography.Merkle.Position.IsAncestor.refl _)
  · simpa [H, positionGindex] using reads
  · -- A node given is read at its index.
    intro e member _
    rw [multiproofNodes, List.zip_map_left] at member
    obtain ⟨⟨g, v⟩, pair, rfl⟩ := List.mem_map.mp member
    obtain ⟨named, deep⟩ := valid g (List.of_mem_zip pair).1
    rw [List.zip_append (by simp [leafCount])] at pair
    show read (positionGindex H (gindexPosition H g)) = .ok v
    rw [show positionGindex H (gindexPosition H g) = g from
      positionGindex_gindexPosition named deep]
    exact (List.mem_append.mp pair).elim (leavesRead g v) (proofRead g v)
  · -- The reader closes the even child with its sibling into the parent.
    intro p a b low left right inside
    obtain ⟨leftInside, rightInside⟩ := inTree_children inside low
    have top : p.level ≤ H := inside.level_le
    have leftRead := left leftInside
    have rightRead := right rightInside
    rw [positionGindex_left low top] at leftRead
    rw [positionGindex_right low top] at rightRead
    have named := (positionGindex_bounds inside).1
    obtain ⟨parent, sibling, parentRead, siblingRead, equation⟩ :=
      closed _ a (by omega) leftRead
    obtain ⟨-, siblingIndex⟩ := gindexSibling_even (index := 2 * positionGindex H p) (by omega)
    rw [siblingIndex, show 2 * positionGindex H p / 2 = positionGindex H p by omega,
      rightRead] at siblingRead
    cases siblingRead
    rw [show 2 * positionGindex H p / 2 = positionGindex H p by omega] at parentRead
    rw [parentRead, equation]
    simp only [Nat.mul_mod_right, ↓reduceIte]
    rfl

/-- A multiproof built from any readable value nodes reconstructs the actual value root. -/
theorem buildMultiproof_rebuilds_value_root (shape : Desc) (value : Value) (root : Bytes)
    (rooted : hashTreeRoot shape value = .ok root) (indices helpers : List Nat)
    (indexed : getHelperIndices indices = .ok helpers) (leaves : List Bytes)
    (leafReads : indices.mapM (nodeRoot shape value) = .ok leaves)
    (proof : List Bytes) (built : buildMultiproof shape value indices = .ok proof) :
    calculateMultiMerkleRootUnchecked leaves proof indices = .ok root := by
  -- The finite value walker supplies the parent equations only at positions actually reconstructed.
  have helperReads : helpers.mapM (nodeRoot shape value) = .ok proof := by
    simpa only [buildMultiproof, indexed, Bind.bind, Except.bind] using built
  obtain ⟨result, reconstructed, rootRead⟩ := closed_multiproof_rebuilds_root
    (nodeRoot_closed shape value root rooted) indexed leafReads helperReads
  rw [nodeRoot_root, rooted] at rootRead
  cases rootRead
  exact reconstructed

/-- Every index in a successfully read list has a successful individual read. -/
theorem mapM_readable {read : Nat → Except Err Bytes} {indices : List Nat} {values : List Bytes}
    (built : indices.mapM read = .ok values) {index : Nat} (member : index ∈ indices) :
    ∃ node, read index = .ok node := by
  -- The paired output retains all input positions because successful reading preserves length.
  obtain ⟨count, reads⟩ := mapM_readNodes built
  have keys := List.map_fst_zip (by omega : indices.length ≤ values.length)
  rw [← keys] at member
  obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp member
  exact ⟨pair.2, same ▸ reads pair.1 pair.2 pairMember⟩

/-- A finite list of individually readable indices can be read as a complete list. -/
theorem mapM_readable_list (read : Nat → Except Err Bytes) :
    ∀ indices : List Nat, (∀ index ∈ indices, ∃ node, read index = .ok node) →
      ∃ values, indices.mapM read = .ok values := by
  -- Reading the head and the remaining list constructs the result in the same order.
  intro indices
  induction indices with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons index rest ih =>
    intro readable
    obtain ⟨node, head⟩ := readable index (by simp)
    obtain ⟨tail, tailRead⟩ := ih (fun i member => readable i (by simp [member]))
    exact ⟨node :: tail,
      by simp [List.mapM_cons, head, tailRead, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- Every helper needed by readable claims is readable in a tree closed under branches. -/
theorem closed_helper_reads {read : Nat → Except Err Bytes} (closed : WalkerClosed read)
    {indices helpers : List Nat} {leaves : List Bytes}
    (indexed : getHelperIndices indices = .ok helpers) (leafReads : indices.mapM read = .ok leaves) :
    ∃ proof, helpers.mapM read = .ok proof := by
  -- Every helper is a sibling along one of the claimed nodes' readable branches.
  obtain ⟨_, valid, shape⟩ := getHelperIndices_frontier indexed
  apply mapM_readable_list read helpers
  intro helper member
  -- Every necessary helper belongs to a claimed node’s finite sibling path.
  obtain ⟨siblingPath, _⟩ := (shape helper).mp member
  obtain ⟨ancestor, pathMember, siblingEq⟩ := List.mem_map.mp siblingPath
  obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp pathMember
  obtain ⟨step, below, ancestorEq⟩ := List.mem_map.mp stepMember
  -- The claim’s successful input read starts an upward branch whose siblings all remain readable.
  obtain ⟨leaf, leafRead⟩ := mapM_readable leafReads claimed
  have named : 1 ≤ claim := by have := valid claim claimed; omega
  obtain ⟨branch, root, branchRead, _, _⟩ :=
    closed_branch_climb read closed (Nat.log2 claim) claim 0 leaf
      (by simpa only [Nat.zero_add, shiftRight_depth named] using Nat.le_refl 1)
      (by simpa only [Nat.shiftRight_zero] using leafRead)
  simp only [Nat.zero_add] at branchRead
  apply mapM_readable branchRead
  exact List.mem_map.mpr ⟨step, below, (congrArg gindexSibling ancestorEq).trans siblingEq⟩

/-- Every valid request for readable value nodes builds a multiproof that reconstructs the value root. -/
theorem buildMultiproof_correct (shape : Desc) (value : Value) (root : Bytes)
    (rooted : hashTreeRoot shape value = .ok root) (indices helpers : List Nat)
    (indexed : getHelperIndices indices = .ok helpers) (leaves : List Bytes)
    (leafReads : indices.mapM (nodeRoot shape value) = .ok leaves) :
    ∃ proof, buildMultiproof shape value indices = .ok proof ∧
      calculateMultiMerkleRootUnchecked leaves proof indices = .ok root := by
  -- Branch closure provides all helpers, and reconstruction preserves their actual value reads.
  have closed := nodeRoot_closed shape value root rooted
  obtain ⟨proof, helperReads⟩ := closed_helper_reads closed indexed leafReads
  have built : buildMultiproof shape value indices = .ok proof := by
    simpa only [buildMultiproof, indexed, Bind.bind, Except.bind] using helperReads
  exact ⟨proof, built,
    buildMultiproof_rebuilds_value_root shape value root rooted indices helpers indexed leaves
      leafReads proof built⟩

private theorem value_reads_width (shape : Desc) (value : Value) (indices : List Nat)
    (nodes : List Bytes) (built : indices.mapM (nodeRoot shape value) = .ok nodes) :
    ∀ node ∈ nodes, node.size = bytesPerChunk := by
  -- Each returned node is paired with the successful value-tree read that produced it.
  obtain ⟨count, reads⟩ := mapM_readNodes built
  have outputs := List.map_snd_zip (by omega : nodes.length ≤ indices.length)
  intro node member
  rw [← outputs] at member
  obtain ⟨pair, paired, same⟩ := List.mem_map.mp member
  have width := nodeRoot_size shape value pair.1 pair.2 (reads pair.1 pair.2 paired)
  simpa only [same] using width

/-- Every valid request for readable value nodes builds a multiproof accepted against the value root. -/
theorem buildMultiproof_verifies (shape : Desc) (value : Value) (root : Bytes)
    (rooted : hashTreeRoot shape value = .ok root) (indices helpers : List Nat)
    (indexed : getHelperIndices indices = .ok helpers) (leaves : List Bytes)
    (leafReads : indices.mapM (nodeRoot shape value) = .ok leaves) :
    ∃ proof, buildMultiproof shape value indices = .ok proof ∧
      verifyMerkleMultiproof leaves proof indices root = .ok true := by
  -- Reconstruction gives the root equality, and every claimed or auxiliary node has full width.
  obtain ⟨proof, built, rebuilt⟩ :=
    buildMultiproof_correct shape value root rooted indices helpers indexed leaves leafReads
  have helperReads : helpers.mapM (nodeRoot shape value) = .ok proof := by
    simpa only [buildMultiproof, indexed, Bind.bind, Except.bind] using built
  -- Claimed leaves and generated helpers must separately satisfy the 32-byte node-width requirement.
  have leafWidths := (checkChunks_ok_iff leaves).mpr (value_reads_width shape value indices leaves leafReads)
  have proofWidths := (checkChunks_ok_iff proof).mpr (value_reads_width shape value helpers proof helperReads)
  refine ⟨proof, built, ?_⟩
  simp [verifyMerkleMultiproof, calculateMultiMerkleRoot, leafWidths, proofWidths, rebuilt, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- An admissible value has a root and an accepted multiproof for every valid readable request. -/
theorem buildMultiproof_fits_verifies (shape : Desc) (value : Value)
    (sound : shape.wellFormed = .ok ()) (fitted : Fits shape value)
    (indices helpers : List Nat) (indexed : getHelperIndices indices = .ok helpers)
    (leaves : List Bytes) (leafReads : indices.mapM (nodeRoot shape value) = .ok leaves) :
    ∃ root proof, hashTreeRoot shape value = .ok root ∧
      buildMultiproof shape value indices = .ok proof ∧
      verifyMerkleMultiproof leaves proof indices root = .ok true := by
  -- Admissibility supplies a complete root before the finite helper frontier is reconstructed.
  obtain ⟨root, rooted, _⟩ := hashTreeRoot_total shape value sound fitted
  obtain ⟨proof, built, verified⟩ :=
    buildMultiproof_verifies shape value root rooted indices helpers indexed leaves leafReads
  exact ⟨root, proof, rooted, built, verified⟩

end EthLib.Serialization.Ssz
