module

public import EthLib.Serialization.Proofs.Ssz.Merkle.Verify
public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Cryptography.Proofs.Merkle.Binding

/-! Conflicting branch openings expose a SHA-256 collision between two 64-byte messages.

The collision sits at the lowest node where the two branches meet.

Each of the two messages is one its own branch hashes, not an arbitrary hash input. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- Every parent digest is a complete SSZ node, regardless of the child inputs. -/
@[simp] theorem combine_size (left right : Bytes) : (combine left right).size = bytesPerChunk := by
  -- SHA-256 produces thirty-two bytes independently of the message contents.
  exact Cryptography.Hash.Sha256.hash_size (ByteArray.mk (left ++ right))

/-- The messages a branch hashes, from its starting node up: each pair of nodes, concatenated. -/
def branchMessages (index level : Nat) (node : Bytes) (proof : List Bytes) : List Bytes :=
  (Cryptography.Merkle.climbPairs (fun _ _ => combine) level (index >>> level) node proof).map
    fun x => x.1 ++ x.2

/-- One step of the messages: the two nodes in the order the index bit gives, then the parent's. -/
theorem branchMessages_cons (index level : Nat) (node sibling : Bytes) (rest : List Bytes) :
    branchMessages index level node (sibling :: rest)
      = (if gindexBit index level then sibling ++ node else node ++ sibling) ::
          branchMessages index (level + 1)
            (if gindexBit index level then combine sibling node else combine node sibling)
            rest := by
  -- An even shifted index is a clear bit, which keeps the node on the left.
  unfold branchMessages
  simp only [Cryptography.Merkle.climbPairs, List.map_cons, ← Nat.shiftRight_succ]
  rcases Nat.mod_two_eq_zero_or_one (index >>> level) with h | h <;>
    simp [Cryptography.Merkle.ordered, gindexBit_parity, h] <;> rfl

/-- The SHA-256 collision two branches from one index run into, if any.

It is the two messages of the lowest node where the branches hash different pairs to one parent. -/
def findBranchCollision (index level : Nat) (left right : Bytes)
    (leftProof rightProof : List Bytes) : Option (Bytes × Bytes) :=
  (Cryptography.Merkle.findCollision (m := Id) (fun _ _ => combine) level (index >>> level) left
      right leftProof rightProof).run.map fun c => (c.x.1 ++ c.x.2, c.y.1 ++ c.y.2)

/-- One branch compared with itself gives no collision, so the search can fail. -/
theorem findBranchCollision_self (index level : Nat) (node : Bytes) (proof : List Bytes) :
    findBranchCollision index level node node proof proof = none := by
  unfold findBranchCollision
  rw [Cryptography.Merkle.findCollision_self]
  rfl

/-- Between branches of complete nodes, the search returns two different 64-byte messages.

They have one SHA-256 digest. -/
theorem findBranchCollision_valid {index level : Nat} {left right : Bytes}
    {leftProof rightProof : List Bytes} {a b : Bytes}
    (leftWidth : left.size = bytesPerChunk) (rightWidth : right.size = bytesPerChunk)
    (leftWidths : ∀ node ∈ leftProof, node.size = bytesPerChunk)
    (rightWidths : ∀ node ∈ rightProof, node.size = bytesPerChunk)
    (found : findBranchCollision index level left right leftProof rightProof = some (a, b)) :
    a.size = 2 * bytesPerChunk ∧ b.size = 2 * bytesPerChunk ∧ a ≠ b ∧
      Cryptography.Hash.Sha256.hash (ByteArray.mk a)
        = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  -- The two messages are those of a node collision.
  obtain ⟨c, hc, pair⟩ := Option.map_eq_some_iff.mp found
  cases pair
  obtain ⟨⟨different, joined⟩, -⟩ := Cryptography.Merkle.findCollision_valid _ _ _ _ _ _ _ c hc
  -- Every node the two climbs hash has 32 bytes, since a parent is a SHA-256 digest.
  obtain ⟨x1, x2, y1, y2⟩ := Cryptography.Merkle.findCollision_children _
    (fun node => node.size = bytesPerChunk) (fun _ _ _ _ => combine_size _ _)
    leftWidth rightWidth leftWidths rightWidths hc
  refine ⟨by simp [x1, x2, Nat.two_mul], by simp [y1, y2, Nat.two_mul],
    fun equal => different ?_, ?_⟩
  · -- Fixed child widths keep the boundary between the two children in place.
    obtain ⟨h1, h2⟩ := Array.append_inj equal (x1.trans y1.symm)
    exact Prod.ext h1 h2
  · -- The two pairs hash to one parent, which is the SHA-256 digest of their messages.
    exact ByteArray.ext joined

/-- Each message the search returns is one its own branch hashes. -/
theorem findBranchCollision_mem {index level : Nat} {left right : Bytes}
    {leftProof rightProof : List Bytes} {a b : Bytes}
    (found : findBranchCollision index level left right leftProof rightProof = some (a, b)) :
    a ∈ branchMessages index level left leftProof ∧
      b ∈ branchMessages index level right rightProof := by
  -- The two messages are those of a node collision, whose pairs the two climbs hash.
  obtain ⟨c, hc, pair⟩ := Option.map_eq_some_iff.mp found
  cases pair
  obtain ⟨hx, hy⟩ := Cryptography.Merkle.findCollision_mem_climbPairs _ hc
  exact ⟨List.mem_map_of_mem hx, List.mem_map_of_mem hy⟩

/-- Two same-length branches from one index with the same root start from one node.

Otherwise the search finds a collision. -/
theorem climbBranch_binding {index level : Nat} {left right : Bytes}
    {leftProof rightProof : List Bytes}
    (lengths : leftProof.length = rightProof.length)
    (same : climbBranch index level left leftProof = climbBranch index level right rightProof) :
    left = right ∨ (findBranchCollision index level left right leftProof rightProof).isSome := by
  rcases Cryptography.Merkle.climb_binding _ _ _ level (index >>> level) left right lengths same
    with ⟨leaves, -⟩ | found
  · exact .inl leaves
  · exact .inr (by simpa [findBranchCollision, Id.run] using found)

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

/-- A branch that rebuilds a root has the depth of its index, and climbs to that root. -/
theorem calculateMerkleRootUnchecked_shape {leaf root : Bytes} {proof : List Bytes} {index : Nat}
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

/-- Conflicting accepted openings at one index expose a collision of two 64-byte SHA-256 messages.

They are the messages the search returns, and each is one its own branch hashes.

No injectivity or collision-resistance axiom is assumed. -/
theorem verifyMerkleProof_binding {left right root : Bytes} {leftProof rightProof : List Bytes}
    {index : Nat} (first : verifyMerkleProof left leftProof index root = .ok true)
    (second : verifyMerkleProof right rightProof index root = .ok true) :
    left = right ∨
      ∃ a b, findBranchCollision index 0 left right leftProof rightProof = some (a, b) ∧
        a ∈ branchMessages index 0 left leftProof ∧ b ∈ branchMessages index 0 right rightProof ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a)
          = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  -- Acceptance supplies the widths and common branch depth required by collision extraction.
  obtain ⟨leftWidth, leftWidths, leftBuilt⟩ := (verifyMerkleProof_eq_true_iff ..).mp first
  obtain ⟨rightWidth, rightWidths, rightBuilt⟩ := (verifyMerkleProof_eq_true_iff ..).mp second
  -- A shared generalized index gives equal branch depths even when sibling bytes differ.
  obtain ⟨leftLength, leftRoot⟩ := calculateMerkleRootUnchecked_shape leftBuilt
  obtain ⟨rightLength, rightRoot⟩ := calculateMerkleRootUnchecked_shape rightBuilt
  -- Compare the two actual upward computations without assuming hash injectivity.
  rcases climbBranch_binding (leftLength.trans rightLength.symm)
      (leftRoot.trans rightRoot.symm) with
    leaves | found
  · exact .inl leaves
  · -- The search names the two messages: each is hashed along its own branch, and they collide.
    obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨aIn, bIn⟩ := findBranchCollision_mem hab
    exact .inr ⟨a, b, hab, aIn, bIn,
      findBranchCollision_valid leftWidth rightWidth leftWidths rightWidths hab⟩

end EthLib.Serialization.Ssz
