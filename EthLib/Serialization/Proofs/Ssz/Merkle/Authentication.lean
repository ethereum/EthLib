import EthLib.Serialization.Proofs.Ssz.Merkle.Verify
import EthLib.Cryptography.Proofs.Hash.Sha256

/-! Conflicting branch openings expose a hash collision among the messages actually hashed. -/

namespace EthLib.Serialization.Ssz

/-- The compression inputs encountered while reconstructing one branch. -/
def branchMessages (index : Nat) : Nat → Bytes → List Bytes → List Bytes
  | _, _, [] => []
  | level, node, sibling :: rest =>
    -- The index determines the order of the two complete child nodes.
    let input := if gindexBit index level then sibling ++ node else node ++ sibling
    let parent := if gindexBit index level then combine sibling node else combine node sibling
    input :: branchMessages index (level + 1) parent rest

/-- Every parent digest is a complete SSZ node, regardless of the child inputs. -/
@[simp] theorem combine_size (left right : Bytes) : (combine left right).size = bytesPerChunk := by
  -- SHA-256 produces thirty-two bytes independently of the message contents.
  exact Cryptography.Hash.Sha256.hash_size (ByteArray.mk (left ++ right))

/-- A branch of complete nodes hashes only 64-byte messages. -/
theorem branchMessages_size (index level : Nat) (leaf : Bytes) (proof : List Bytes)
    (leafWidth : leaf.size = bytesPerChunk)
    (proofWidths : ∀ node ∈ proof, node.size = bytesPerChunk) :
    ∀ message ∈ branchMessages index level leaf proof, message.size = 2 * bytesPerChunk := by
  -- A valid leaf and sibling give 32 + 32 bytes, and their digest remains a valid next node.
  induction proof generalizing level leaf with
  | nil => simp [branchMessages]
  | cons sibling rest ih =>
    intro message member
    simp only [branchMessages, List.mem_cons] at member
    rcases member with here | later
    · subst message
      cases gindexBit index level <;> simp [leafWidth, proofWidths sibling List.mem_cons_self, Nat.two_mul]
    · apply ih (level + 1) _ _ (fun node member => proofWidths node (List.mem_cons_of_mem _ member))
        message later
      cases gindexBit index level <;> simp

/--
Two same-length branches with different leaves and the same root expose a SHA-256 collision.
The witnesses are messages hashed along the two actual branches, not arbitrary hash inputs.
-/
theorem climbBranch_binding (index : Nat) : ∀ level left leftProof right rightProof,
    left.size = bytesPerChunk → right.size = bytesPerChunk →
    (∀ node ∈ leftProof, node.size = bytesPerChunk) →
    (∀ node ∈ rightProof, node.size = bytesPerChunk) →
    leftProof.length = rightProof.length →
    climbBranch index level left leftProof = climbBranch index level right rightProof →
    left = right ∨ ∃ first ∈ branchMessages index level left leftProof,
      ∃ second ∈ branchMessages index level right rightProof,
        first ≠ second ∧ Cryptography.Hash.Sha256.hash (ByteArray.mk first) = Cryptography.Hash.Sha256.hash (ByteArray.mk second) := by
  intro level left leftProof
  induction leftProof generalizing level left with
  | nil =>
    intro right rightProof _ _ _ _ lengths same
    have empty : rightProof = [] := List.eq_nil_of_length_eq_zero lengths.symm
    subst rightProof
    exact .inl same
  | cons sibling rest ih =>
    intro right rightProof leftWidth rightWidth leftWidths rightWidths lengths same
    cases rightProof with
    | nil => simp at lengths
    | cons other others =>
      by_cases leaves : left = right
      · exact .inl leaves
      · let first := if gindexBit index level then sibling ++ left else left ++ sibling
        let second := if gindexBit index level then other ++ right else right ++ other
        let parent := if gindexBit index level then combine sibling left else combine left sibling
        let otherParent := if gindexBit index level then combine other right else combine right other
        -- Fixed child widths prevent distinct leaves from disappearing into a different concatenation boundary.
        have firstDifferent : first ≠ second := by
          intro equal
          cases direction : gindexBit index level with
          | false =>
            simp only [first, second, direction, Bool.false_eq_true, ite_false] at equal
            exact leaves (Array.append_inj equal (leftWidth.trans rightWidth.symm)).1
          | true =>
            simp only [first, second, direction, ite_true] at equal
            exact leaves (Array.append_inj equal
              ((leftWidths sibling List.mem_cons_self).trans
                (rightWidths other List.mem_cons_self).symm)).2
        -- The first shared parent of two distinct paths is precisely where a collision can be exhibited.
        by_cases joined : parent = otherParent
        · -- The first distinct pair already produces the same parent digest.
          refine .inr ⟨first, List.mem_cons_self, second, List.mem_cons_self, firstDifferent, ?_⟩
          apply ByteArray.ext
          cases direction : gindexBit index level <;>
            simpa [parent, otherParent, first, second, direction, combine] using joined
        · -- Otherwise any merger must occur later, between the two distinct parents.
          -- If the immediate parents differ, the common final root forces a merger farther up the branches.
          have next := ih (level + 1) parent otherParent others
            (by dsimp only [parent]; split <;> simp)
            (by dsimp only [otherParent]; split <;> simp)
            (fun node member => leftWidths node (List.mem_cons_of_mem _ member))
            (fun node member => rightWidths node (List.mem_cons_of_mem _ member))
            (by simpa using lengths) same
          obtain ⟨a, aIn, b, bIn, different, collision⟩ := next.resolve_left joined
          exact .inr ⟨a, List.mem_cons_of_mem _ aIn, b, List.mem_cons_of_mem _ bIn, different, collision⟩

/-- A branch passes width validation exactly when every supplied sibling is a full node. -/
theorem checkChunks_ok_iff (nodes : List Bytes) :
    checkChunks nodes = .ok () ↔ ∀ node ∈ nodes, node.size = bytesPerChunk := by
  -- Validation visits every sibling and succeeds precisely when each has width 32.
  induction nodes with
  | nil => simp [checkChunks]
  | cons node nodes ih =>
    by_cases width : node.size = bytesPerChunk <;>
      simp [checkChunks, checkChunk, width, Bind.bind, Except.bind, ih]

/-- Acceptance requires complete nodes and reconstruction of exactly the expected root. -/
theorem verifyMerkleProof_eq_true_iff (leaf : Bytes) (proof : List Bytes) (index : Nat) (root : Bytes) :
    verifyMerkleProof leaf proof index root = .ok true ↔
      leaf.size = bytesPerChunk ∧
      (∀ node ∈ proof, node.size = bytesPerChunk) ∧ calculateMerkleRootUnchecked leaf proof index = .ok root := by
  -- A successful answer requires all width checks and equality with the reconstructed root.
  simp only [verifyMerkleProof, calculateMerkleRoot, ← checkChunks_ok_iff]
  cases checkChunks proof <;> cases calculateMerkleRootUnchecked leaf proof index <;>
    by_cases leafWidth : leaf.size = bytesPerChunk <;>
    simp_all [checkChunk, Bind.bind, Except.bind, pure, Except.pure]

private theorem calculateMerkleRootUnchecked_shape {leaf root : Bytes} {proof : List Bytes} {index : Nat}
    (built : calculateMerkleRootUnchecked leaf proof index = .ok root) :
    proof.length = Nat.log2 index ∧ climbBranch index 0 leaf proof = root := by
  -- The validated index fixes the branch length before reconstruction can return a root.
  unfold calculateMerkleRootUnchecked at built
  cases measured : gindexLength index with
  | error fault => simp [measured, Bind.bind, Except.bind] at built
  | ok depth =>
    have depthIs := (gindexLength_ok measured).1
    simp only [measured, Bind.bind, Except.bind] at built
    split at built
    · simp at built
    · simp only [pure, Except.pure, Except.ok.injEq] at built
      exact ⟨by simp_all, built⟩

/--
Conflicting accepted openings at one index expose a collision in 64-byte SHA-256 messages.
No injectivity or collision-resistance axiom is assumed.
-/
theorem verifyMerkleProof_binding {left right root : Bytes} {leftProof rightProof : List Bytes}
    {index : Nat} (first : verifyMerkleProof left leftProof index root = .ok true)
    (second : verifyMerkleProof right rightProof index root = .ok true) :
    left = right ∨ ∃ a ∈ branchMessages index 0 left leftProof,
      ∃ b ∈ branchMessages index 0 right rightProof,
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  -- Acceptance supplies the widths and common branch depth required by collision extraction.
  obtain ⟨leftWidth, leftWidths, leftBuilt⟩ := (verifyMerkleProof_eq_true_iff ..).mp first
  obtain ⟨rightWidth, rightWidths, rightBuilt⟩ := (verifyMerkleProof_eq_true_iff ..).mp second
  -- A shared generalized index gives equal branch depths even when sibling bytes differ.
  obtain ⟨leftLength, leftRoot⟩ := calculateMerkleRootUnchecked_shape leftBuilt
  obtain ⟨rightLength, rightRoot⟩ := calculateMerkleRootUnchecked_shape rightBuilt
  -- Compare the two actual upward computations without assuming hash injectivity.
  have compared := climbBranch_binding index 0 left leftProof right rightProof leftWidth rightWidth
    leftWidths rightWidths (leftLength.trans rightLength.symm) (leftRoot.trans rightRoot.symm)
  exact compared.imp id fun ⟨a, aIn, b, bIn, different, collision⟩ => ⟨a, aIn, b, bIn,
    branchMessages_size index 0 left leftProof leftWidth leftWidths a aIn,
    branchMessages_size index 0 right rightProof rightWidth rightWidths b bIn, different, collision⟩

end EthLib.Serialization.Ssz
