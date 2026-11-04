module

public import EthLib.Serialization.Ssz.Merkle.Branch
public import EthLib.Serialization.Proofs.Ssz.Merkle.Authentication
public import EthLib.Serialization.Proofs.Ssz.Merkle.Tree

/-!
# Proofs: Merkle branches by depth and index

A branch of depth `d` at index `i` is the branch of the generalized index `2^d + i`.

So the check by depth and index accepts exactly what the check by generalized index accepts.

Its binding then follows from the binding of that check.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A climb reads only the bits of the index at the levels it climbs. -/
theorem climbBranch_congr {index other : Nat} :
    ∀ {level : Nat} {node : Bytes} {branch : List Bytes},
    (∀ i < branch.length, gindexBit index (level + i) = gindexBit other (level + i)) →
    climbBranch index level node branch = climbBranch other level node branch
  | _, _, [], _ => rfl
  | level, node, sibling :: rest, bits => by
    have head := bits 0 (by simp)
    simp only [Nat.add_zero] at head
    rw [climbBranch_cons, climbBranch_cons, head]
    exact climbBranch_congr fun i below => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using bits (i + 1) (by simpa using below)

/-- The messages of a climb depend only on the bits of the index at the levels it climbs. -/
theorem branchMessages_congr {index other : Nat} :
    ∀ {level : Nat} {node : Bytes} {branch : List Bytes},
    (∀ i < branch.length, gindexBit index (level + i) = gindexBit other (level + i)) →
    branchMessages index level node branch = branchMessages other level node branch
  | _, _, [], _ => rfl
  | level, node, sibling :: rest, bits => by
    have head := bits 0 (by simp)
    simp only [Nat.add_zero] at head
    simp only [branchMessages, head]
    rw [branchMessages_congr fun i below => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using bits (i + 1) (by simpa using below)]

/-- Below bit `depth`, the generalized index `2^depth + i` has the bits of `i`. -/
theorem gindexBit_two_pow_add {depth i level : Nat} (below : level < depth) :
    gindexBit (2 ^ depth + i) level = gindexBit i level :=
  Nat.testBit_two_pow_add_gt below i

/-- Below bit `depth`, an index has the bits of its remainder modulo `2^depth`. -/
theorem gindexBit_mod_two_pow {depth i level : Nat} (below : level < depth) :
    gindexBit (i % 2 ^ depth) level = gindexBit i level := by
  simp [gindexBit, Nat.testBit_mod_two_pow, below]

/-- A branch is valid when it has `depth` nodes and climbs from the leaf to the root. -/
theorem isValidMerkleBranch_eq_true_iff {leaf root : Vector UInt8 32}
    {branch : List (Vector UInt8 32)} {depth index : Nat} :
    isValidMerkleBranch leaf branch depth index root = true ↔ branch.length = depth ∧
      climbBranch index 0 leaf.toArray (branch.map Vector.toArray) = root.toArray := by
  unfold isValidMerkleBranch computeMerkleBranchRoot
  by_cases count : branch.length = depth
  · subst count
    simp only [beq_self_eq_true, Nat.lt_irrefl, ↓reduceIte, List.take_length, Bool.true_and,
      true_and]
    cases chunked : toChunk (climbBranch index 0 leaf.toArray (branch.map Vector.toArray)) with
    | ok rebuilt =>
      rw [toChunk_ok_iff] at chunked
      simp [chunked, Vector.toArray_inj]
    | error fault =>
      -- A climb that reaches the root is one node wide, so it converts.
      simp only [Bool.false_eq_true, false_iff]
      intro reached
      rw [reached, (toChunk_ok_iff (chunk := root)).mpr rfl] at chunked
      cases chunked
  · simp [count, Ne.symm count]

/-- Only the remainder of the index modulo `2^depth` matters. -/
theorem isValidMerkleBranch_mod (leaf : Vector UInt8 32) (branch : List (Vector UInt8 32))
    (depth index : Nat) (root : Vector UInt8 32) :
    isValidMerkleBranch leaf branch depth (index % 2 ^ depth) root =
      isValidMerkleBranch leaf branch depth index root := by
  apply Bool.eq_iff_iff.mpr
  simp only [isValidMerkleBranch_eq_true_iff]
  constructor <;> rintro ⟨count, climbed⟩ <;> refine ⟨count, climbed ▸ climbBranch_congr ?_⟩ <;>
    intro i below <;> simp only [List.length_map, count] at below <;>
    simp [gindexBit_mod_two_pow below]

/-- The generalized index `2^depth + i` of an index below `2^depth` sits at that depth. -/
theorem gindexLength_two_pow_add {depth index : Nat} (positive : 0 < depth)
    (below : index < 2 ^ depth) : gindexLength (2 ^ depth + index) = .ok depth := by
  have depthIs : Nat.log2 (2 ^ depth + index) = depth :=
    (Nat.log2_eq_iff (by have := Nat.two_pow_pos depth; omega)).mpr
      ⟨by omega, by rw [Nat.pow_succ]; omega⟩
  simp [gindexLength, gindexDepth, depthIs, Nat.ne_of_gt positive, bind, Except.bind]

/--
Take a positive depth and an index below `2^depth`.

The valid branches are exactly those that verify at the generalized index `2^depth + index`.
-/
theorem isValidMerkleBranch_iff_verifyMerkleProof {leaf root : Vector UInt8 32}
    {branch : List (Vector UInt8 32)} {depth index : Nat} (positive : 0 < depth)
    (below : index < 2 ^ depth) :
    isValidMerkleBranch leaf branch depth index root = true ↔
      verifyMerkleProof leaf.toArray (branch.map Vector.toArray) (2 ^ depth + index)
        root.toArray = .ok true := by
  rw [isValidMerkleBranch_eq_true_iff, verifyMerkleProof_eq_true_iff]
  -- Every node of the branch is a vector, so every width check passes.
  simp only [calculateMerkleRootUnchecked, gindexLength_two_pow_add positive below, bind,
    Except.bind, List.length_map, Vector.size_toArray, true_and]
  by_cases count : branch.length = depth
  · -- The climb at the generalized index reads the same bits as the climb at the index.
    have same : climbBranch (2 ^ depth + index) 0 leaf.toArray (branch.map Vector.toArray) =
        climbBranch index 0 leaf.toArray (branch.map Vector.toArray) :=
      climbBranch_congr fun i lt => by
        simp only [List.length_map, count] at lt
        simpa using gindexBit_two_pow_add (i := index) (by omega : 0 + i < depth)
    simp [count, same, pure, Except.pure]
  · simp [count, throw, throwThe, MonadExceptOf.throw]

/--
Two valid branches at one depth, index and root open the same leaf, or expose a collision.

The collision is two distinct 64-byte messages, one hashed in each climb, with one SHA-256 hash.
-/
theorem isValidMerkleBranch_binding {leaf other root : Vector UInt8 32}
    {branch otherBranch : List (Vector UInt8 32)} {depth index : Nat}
    (first : isValidMerkleBranch leaf branch depth index root = true)
    (second : isValidMerkleBranch other otherBranch depth index root = true) :
    leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray (branch.map Vector.toArray),
      ∃ b ∈ branchMessages index 0 other.toArray (otherBranch.map Vector.toArray),
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  obtain ⟨count, climbed⟩ := isValidMerkleBranch_eq_true_iff.mp first
  obtain ⟨otherCount, otherClimbed⟩ := isValidMerkleBranch_eq_true_iff.mp second
  cases depth with
  | zero =>
    -- With no branch node, each leaf is the root.
    rw [List.length_eq_zero_iff] at count otherCount
    subst count otherCount
    exact .inl (Vector.toArray_inj.mp (climbed.trans otherClimbed.symm))
  | succ depth =>
    -- Both branches verify at the generalized index of the leaf.
    let gindex := 2 ^ (depth + 1) + index % 2 ^ (depth + 1)
    have reduced := Nat.mod_lt index (Nat.two_pow_pos (depth + 1))
    have verified := (isValidMerkleBranch_iff_verifyMerkleProof (Nat.succ_pos depth) reduced).mp
      ((isValidMerkleBranch_mod ..).trans first)
    have otherVerified :=
      (isValidMerkleBranch_iff_verifyMerkleProof (Nat.succ_pos depth) reduced).mp
        ((isValidMerkleBranch_mod ..).trans second)
    -- That index and the index have the same bits at every level a branch climbs.
    have bits : ∀ level < depth + 1, gindexBit gindex level = gindexBit index level :=
      fun level lt => (gindexBit_two_pow_add lt).trans (gindexBit_mod_two_pow lt)
    have messages : ∀ {node : Vector UInt8 32} {nodes : List (Vector UInt8 32)},
        nodes.length = depth + 1 → branchMessages gindex 0 node.toArray (nodes.map Vector.toArray)
          = branchMessages index 0 node.toArray (nodes.map Vector.toArray) :=
      fun counted => branchMessages_congr fun i lt => by
        simp only [List.length_map, counted] at lt
        simpa using bits i lt
    rcases verifyMerkleProof_binding verified otherVerified with same | collision
    · exact .inl (Vector.toArray_inj.mp same)
    · rw [messages count, messages otherCount] at collision
      exact .inr collision

/-- An index of at least two sits at a positive depth. -/
theorem log2_pos {gindex : Nat} (named : 2 ≤ gindex) : 0 < Nat.log2 gindex := by
  have upper := (gindexDepth_bounds (by omega : 1 ≤ gindex)).2
  rcases Nat.eq_zero_or_pos (Nat.log2 gindex) with zero | positive
  · rw [zero] at upper
    omega
  · exact positive

/-- A generalized index is its leading bit plus its index among the nodes of its level. -/
theorem two_pow_log2_add_mod {gindex : Nat} (named : 1 ≤ gindex) :
    2 ^ Nat.log2 gindex + gindex % 2 ^ Nat.log2 gindex = gindex := by
  obtain ⟨lower, upper⟩ := gindexDepth_bounds named
  rw [Nat.pow_succ] at upper
  rw [Nat.mod_eq_sub_mod lower, Nat.mod_eq_of_lt (by omega)]
  omega

/--
Take a generalized index of at least two.

The valid normalized branches are exactly those with zero front nodes and a rest that verifies.

The front holds the nodes beyond the depth of the index.
-/
theorem isValidNormalizedMerkleBranch_iff {leaf root : Vector UInt8 32}
    {branch : List (Vector UInt8 32)} {gindex : Nat} (named : 2 ≤ gindex) :
    isValidNormalizedMerkleBranch leaf branch gindex root = .ok true ↔
      (∀ node ∈ branch.take (branch.length - Nat.log2 gindex), node = Vector.replicate 32 0) ∧
      verifyMerkleProof leaf.toArray
        ((branch.drop (branch.length - Nat.log2 gindex)).map Vector.toArray) gindex
        root.toArray = .ok true := by
  have reduced := Nat.mod_lt gindex (Nat.two_pow_pos (Nat.log2 gindex))
  have depthIs : gindexDepth gindex = .ok (Nat.log2 gindex) := by
    simp [gindexDepth]
    omega
  simp only [isValidNormalizedMerkleBranch, getSubtreeIndex, gindexBelow, depthIs, bind,
    Except.bind, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq]
  rw [isValidMerkleBranch_iff_verifyMerkleProof (log2_pos named) reduced,
    two_pow_log2_add_mod (by omega)]

end EthLib.Serialization.Ssz
