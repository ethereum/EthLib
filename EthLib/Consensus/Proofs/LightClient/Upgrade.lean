module

public import EthLib.Consensus.LightClient.Upgrade
public import EthLib.Consensus.Proofs.LightClient.Containers
public import EthLib.Consensus.Proofs.LightClient.FullNode
public import EthLib.Serialization.Proofs.Ssz.Type.ValueEquality

/-!
# Proofs: the upgrade of light client data to a later fork

An upgrade keeps the beacon header of a light client header.

So the upgrade of a store keeps its finalized and optimistic beacon headers, and their slots.

The Gloas header of a valid Electra header is valid too, under three conditions.

The header is not the empty one, and its slot comes before Gloas.

The configuration activates Capella no later than Deneb.

The new branch joins the proof of the block hash in the execution header to the old branch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The Gloas header of an Electra header keeps the beacon header. -/
theorem LightClientHeader.toGloas_beacon {config : Config} {post : Fork}
    {gloas : .glamsterdam ≤ post} {header : LightClientHeader preset .pectra}
    {upgraded : LightClientHeader preset post}
    (computed : header.toGloas config gloas = .ok upgraded) :
    upgraded.beacon = header.beacon := by
  unfold LightClientHeader.toGloas at computed
  split at computed
  · -- The empty header stays empty, and an Electra header equal to it has its beacon header.
    rename_i empty
    cases computed
    -- The SSZ value of a header starts with the fields of its beacon header.
    have values := beq_iff_eq.mp empty
    simp only [SszType.toValue, SszFields.toValues, Value.seq.injEq, List.cons.injEq] at values
    obtain ⟨⟨slot, proposer, parent, state, body, -⟩, -⟩ := values
    simp only [Value.uint.injEq, Value.bytes.injEq, UInt64.toNat_inj, Vector.toArray_inj]
      at slot proposer parent state body
    cases beacon : header.beacon
    simp_all [LightClientHeader.empty]
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)

/-- Nodes that convert to 32-byte vectors are the bytes of those vectors. -/
private theorem mapM_toChunk_eq_map :
    ∀ {nodes : List Bytes} {chunks : List Bytes32},
    nodes.mapM toChunk = .ok chunks → nodes = chunks.map Vector.toArray
  | [], chunks, built => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at built
    subst built
    rfl
  | node :: rest, chunks, built => by
    simp only [List.mapM_cons, Base.bind_ok_iff] at built
    obtain ⟨chunk, converted, tail, restBuilt, done⟩ := built
    simp only [pure, Except.pure, Except.ok.injEq] at done
    subst done
    have same : node = chunk.toArray := by
      unfold toChunk at converted
      split at converted
      · cases converted
        rfl
      · cases converted
    rw [List.map_cons, same, mapM_toChunk_eq_map restBuilt]

/-- A branch vector holds the list it was made from. -/
private theorem branchVector_toList {depth : Nat} {branch : List Bytes32}
    {vector : Vector Bytes32 depth} (made : branchVector depth branch = .ok vector) :
    vector.toList = branch := by
  unfold branchVector at made
  split at made
  · cases made
    simp
  · cases made

/-- An accepted branch is as long as the depth of its index. -/
private theorem verifyMerkleProof_length {leaf root : Bytes} {branch : List Bytes} {index : Nat}
    (verified : verifyMerkleProof leaf branch index root = .ok true) :
    branch.length = Nat.log2 index := by
  obtain ⟨-, -, built⟩ := (verifyMerkleProof_eq_true_iff ..).mp verified
  exact (calculateMerkleRootUnchecked_shape built).1

/-- A valid branch by depth and subtree index verifies at the generalized index. -/
private theorem verifyMerkleProof_of_isValidMerkleBranch {leaf root : Bytes32}
    {branch : List Bytes32} {gindex subtree : Nat} (named : 2 ≤ gindex)
    (indexed : getSubtreeIndex gindex = .ok subtree)
    (valid : isValidMerkleBranch leaf branch (Nat.log2 gindex) subtree root = true) :
    verifyMerkleProof leaf.toArray (branch.map Vector.toArray) gindex root.toArray = .ok true := by
  have depthIs : gindexDepth gindex = .ok (Nat.log2 gindex) := by
    simp [gindexDepth]
    omega
  simp only [getSubtreeIndex, depthIs, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    gindexBelow] at indexed
  subst indexed
  rw [isValidMerkleBranch_iff_verifyMerkleProof (log2_pos named)
    (Nat.mod_lt _ (Nat.two_pow_pos _)), two_pow_log2_add_mod (by omega)] at valid
  exact valid

/-- A branch that verifies at an index passes the normalized check there, with zeros in front. -/
private theorem isValidNormalizedMerkleBranch_of_verify {leaf root : Bytes32}
    {branch : List Bytes32} {gindex target : Nat} (named : 2 ≤ gindex)
    (verified : verifyMerkleProof leaf.toArray (branch.map Vector.toArray) gindex root.toArray =
      .ok true) :
    isValidNormalizedMerkleBranch leaf (normalizeMerkleBranch branch target) gindex root =
      .ok true := by
  have length := verifyMerkleProof_length verified
  rw [List.length_map] at length
  rw [isValidNormalizedMerkleBranch_normalize (by omega), isValidNormalizedMerkleBranch_iff named,
    length, Nat.sub_self, List.take_zero, List.drop_zero]
  exact ⟨by simp, verified⟩

/-- A container root from field roots that are untyped roots is the untyped root.

The roots of the fields must be those of their untyped values, one for each field type. -/
private theorem hashTreeRoot_of_fieldRoots {σ β : Type} [SszFields β] {names : List String}
    {fields : σ → β} {build : β → σ} (value : σ)
    (rootsAre : SszFields.roots (fields value) =
      ((SszFields.descs β).zip (SszFields.toValues (fields value))).mapM
        fun field => Serialization.Ssz.hashTreeRoot field.1 field.2)
    (paired : (SszFields.descs β).length = (SszFields.toValues (fields value)).length)
    {root : Bytes32}
    (rooted : @SszType.hashTreeRoot σ (SszType.container names fields build) value = .ok root) :
    Serialization.Ssz.hashTreeRoot (.container names (SszFields.descs β))
      (.seq (SszFields.toValues (fields value))) = .ok root.toArray := by
  simp only [SszType.hashTreeRoot, Base.bind_ok_iff] at rooted
  obtain ⟨node, built, chunked⟩ := rooted
  rw [toChunk_ok_iff] at chunked
  subst chunked
  simp only [SszType.root, Base.bind_ok_iff, rootsAre] at built
  obtain ⟨roots, fieldRoots, summary⟩ := built
  rw [← hashTreeRoot_container_roots paired fieldRoots]
  exact summary

/-- The typed root of a payload header of Capella or Electra is the root of its untyped value.

This holds at every preset. -/
private theorem ExecutionPayloadHeader.hashTreeRoot_untyped {payloadFork : Fork}
    (named : payloadFork = .shapella ∨ payloadFork = .pectra)
    (execution : ExecutionPayloadHeader preset payloadFork) {root : Bytes32}
    (rooted : SszType.hashTreeRoot execution = .ok root) :
    Serialization.Ssz.hashTreeRoot (SszType.desc (ExecutionPayloadHeader preset payloadFork))
      (SszType.toValue execution) = .ok root.toArray := by
  -- Every field type takes the root of its untyped value.
  have bytes : ∀ {n : Nat} (field : Vector UInt8 n),
      SszType.root field =
        Serialization.Ssz.hashTreeRoot (SszType.desc (Vector UInt8 n)) (SszType.toValue field) :=
    fun _ => rfl
  have list : ∀ {n : Nat} (field : SszList UInt8 n),
      SszType.root field =
        Serialization.Ssz.hashTreeRoot (SszType.desc (SszList UInt8 n)) (SszType.toValue field) :=
    fun _ => rfl
  have word : ∀ field : UInt64,
      SszType.root field =
        Serialization.Ssz.hashTreeRoot (SszType.desc UInt64) (SszType.toValue field) :=
    fun _ => rfl
  have wide : ∀ field : U256,
      SszType.root field =
        Serialization.Ssz.hashTreeRoot (SszType.desc U256) (SszType.toValue field) :=
    fun _ => rfl
  rcases named with rfl | rfl
  all_goals
    refine hashTreeRoot_of_fieldRoots execution ?_ rfl rooted
    simp +decide [SszFields.roots, SszFields.descs, SszFields.toValues, List.mapM_cons, bytes,
      list, word, wide]

/-- The proof of a node of a value, then a branch from the value's root, proves the node.

The node is read at an index of the value, and the second branch climbs from its root.

The joined branch passes the normalized check at the joined index, with zeros in front. -/
private theorem computeMerkleProof_append {α : Type} [SszType α] (value : α)
    {inner outer index target : Nat} {leaf root top : Bytes32} {proof rest : List Bytes32}
    (joined : gindexConcat outer inner = .ok index) (named : 2 ≤ inner) (deep : 2 ≤ index)
    (read : nodeRoot (SszType.desc α) (SszType.toValue value) inner = .ok leaf.toArray)
    (rooted : Serialization.Ssz.hashTreeRoot (SszType.desc α) (SszType.toValue value) =
      .ok root.toArray)
    (proved : computeMerkleProof value inner = .ok proof)
    (climbs : verifyMerkleProof root.toArray (rest.map Vector.toArray) outer top.toArray =
      .ok true) :
    isValidNormalizedMerkleBranch leaf (normalizeMerkleBranch (proof ++ rest) target) index top =
      .ok true := by
  obtain ⟨indices, indexed⟩ := getBranchIndices_ok named
  obtain ⟨nodes, built, verified⟩ := buildProof_verifies _ _ _ rooted inner _ read indices indexed
  -- The proof is the built branch, each node read back as a vector.
  have same : nodes = proof.map Vector.toArray := by
    simp only [computeMerkleProof, built, bind, Except.bind] at proved
    exact mapM_toChunk_eq_map proved
  subst same
  apply isValidNormalizedMerkleBranch_of_verify deep
  rw [List.map_append]
  exact verifyMerkleProof_append joined verified climbs

/-- The block hash of a payload header joins the payload in the body at the indices of the forks. -/
private theorem gindexConcat_payloadHeaderBlockHash :
    gindexConcat EXECUTION_PAYLOAD_GINDEX (payloadHeaderBlockHashGindex .pectra) =
        .ok EXECUTION_BLOCK_HASH_GINDEX_DENEB ∧
      gindexConcat EXECUTION_PAYLOAD_GINDEX (payloadHeaderBlockHashGindex .shapella) =
        .ok EXECUTION_BLOCK_HASH_GINDEX := by
  have deneb : Nat.log2 44 = 5 := by decide +kernel
  have capella : Nat.log2 28 = 4 := by decide +kernel
  simp +decide [gindexConcat, gindexDepth, payloadHeaderBlockHashGindex, EXECUTION_PAYLOAD_GINDEX,
    EXECUTION_BLOCK_HASH_GINDEX_DENEB, EXECUTION_BLOCK_HASH_GINDEX, deneb, capella, bind,
    Except.bind, pure, Except.pure]

/-- The Gloas header of a valid Electra header passes the header check too.

The Electra header is not the empty one, and its slot comes before Gloas.

The configuration activates Capella no later than Deneb.

The new branch proves the block hash inside the execution header, then climbs as the old one did.

A header of a slot before Capella keeps a zero block hash and a zero branch. -/
theorem LightClientHeader.isValidLightClientHeader_toGloas {config : Config} {post : Fork}
    {gloas : .glamsterdam ≤ post} {header : LightClientHeader preset .pectra}
    {upgraded : LightClientHeader preset post}
    (valid : isValidLightClientHeader config header = .ok true)
    (notEmpty : sameSszValue header (LightClientHeader.empty preset .pectra) = false)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH)
    (beforeGloas : computeEpochAtSlot preset header.beacon.slot < config.GLOAS_FORK_EPOCH)
    (computed : header.toGloas config gloas = .ok upgraded) :
    isValidLightClientHeader config upgraded = .ok true := by
  -- The upgrade keeps the beacon header, so both checks read the epoch of one slot.
  have beacon := LightClientHeader.toGloas_beacon computed
  unfold LightClientHeader.toGloas at computed
  simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at computed
  unfold isValidLightClientHeader getLcExecutionRoot at valid
  unfold isValidLightClientHeader
  simp only [LightClientError.requireFork,
    show Fork.altair ≤ post from Nat.le_trans (by decide) gloas,
    show Fork.altair ≤ Fork.pectra by decide, show ¬ Fork.glamsterdam ≤ Fork.pectra by decide,
    show Fork.shapella ≤ Fork.pectra by decide, show Fork.dencun ≤ Fork.pectra by decide,
    ↓reduceIte, ↓reduceDIte, beacon, true_and] at valid ⊢
  -- The new header takes the Gloas branch of the check, at a slot before Gloas.
  simp only [dite_eq_left_of_eq_true (eq_true gloas)]
  simp only [UInt64.not_le.mpr beforeGloas, ↓reduceIte] at ⊢
  by_cases deneb : config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot
  · -- From Deneb, the proof of the block hash comes from the full execution header.
    have capella := UInt64.le_trans ordered deneb
    simp only [deneb, UInt64.not_lt.mpr deneb, UInt64.not_lt.mpr capella, false_and,
      ↓reduceIte, Base.bind_ok_iff] at valid computed ⊢
    obtain ⟨-, -, root, ⟨-, -, rooted⟩, subtree, indexed, climbs⟩ := valid
    obtain ⟨proof, proved, branch, made, built⟩ := computed
    simp only [pure, Except.pure, Except.ok.injEq] at built climbs
    subst built
    refine ⟨(), trivial, LightClientError.liftRoot_ok.mpr ?_⟩
    rw [branchVector_toList made]
    exact computeMerkleProof_append _ gindexConcat_payloadHeaderBlockHash.1 (by decide)
      (by decide) (ExecutionPayloadHeader.nodeRoot_blockHash (by decide) (by decide) _)
      (ExecutionPayloadHeader.hashTreeRoot_untyped (.inr rfl) _
        (LightClientError.liftRoot_ok.mp rooted)) (LightClientError.liftRoot_ok.mp proved)
      (verifyMerkleProof_of_isValidMerkleBranch (by decide)
        (LightClientError.liftRoot_ok.mp indexed) climbs)
  by_cases capella : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot
  · -- Before Deneb, the proof of the block hash comes from the Capella execution header.
    simp only [deneb, capella, UInt64.not_lt.mpr capella, ↓reduceIte, Base.bind_ok_iff]
      at valid computed ⊢
    obtain ⟨-, -, valid⟩ := valid
    split at valid
    · simp [pure, Except.pure] at valid
    simp only [Base.bind_ok_iff] at valid
    obtain ⟨root, ⟨-, -, rooted⟩, subtree, indexed, climbs⟩ := valid
    obtain ⟨proof, proved, branch, made, built⟩ := computed
    simp only [pure, Except.pure, Except.ok.injEq] at built climbs
    subst built
    refine ⟨(), trivial, LightClientError.liftRoot_ok.mpr ?_⟩
    rw [branchVector_toList made]
    exact computeMerkleProof_append _ gindexConcat_payloadHeaderBlockHash.2 (by decide)
      (by decide) (ExecutionPayloadHeader.nodeRoot_blockHash (by decide) (by decide) _)
      (ExecutionPayloadHeader.hashTreeRoot_untyped (.inl rfl) _
        (LightClientError.liftRoot_ok.mp rooted)) (LightClientError.liftRoot_ok.mp proved)
      (verifyMerkleProof_of_isValidMerkleBranch (by decide)
        (LightClientError.liftRoot_ok.mp indexed) climbs)
  · -- Before Capella, the upgrade gives a zero block hash and a zero branch.
    simp only [deneb, capella, ↓reduceIte] at computed ⊢
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp [pure, Except.pure, bind, Except.bind]

/-- An upgraded header keeps the beacon header. -/
theorem LightClientHeader.upgrade_beacon {config : Config} {pre post : Fork}
    {later : pre ≤ post} {header : LightClientHeader preset pre}
    {upgraded : LightClientHeader preset post}
    (computed : header.upgrade config post later = .ok upgraded) :
    upgraded.beacon = header.beacon := by
  unfold LightClientHeader.upgrade at computed
  split at computed
  · cases computed
    rfl
  split at computed
  · exact (toGloas_beacon computed).trans rfl
  · cases computed
    rfl

/-- An upgraded store keeps its finalized and optimistic beacon headers.

So it keeps their slots, and the order between them. -/
theorem LightClientStore.upgrade_beacon {config : Config} {pre post : Fork}
    {later : pre ≤ post} {store : LightClientStore preset pre}
    {upgraded : LightClientStore preset post}
    (computed : store.upgrade config post later = .ok upgraded) :
    upgraded.finalizedHeader.beacon = store.finalizedHeader.beacon ∧
      upgraded.optimisticHeader.beacon = store.optimisticHeader.beacon := by
  unfold LightClientStore.upgrade at computed
  obtain ⟨finalized, finalizedOk, rest⟩ := Base.bind_ok_iff.mp computed
  obtain ⟨_, _, rest⟩ := Base.bind_ok_iff.mp rest
  obtain ⟨optimistic, optimisticOk, rest⟩ := Base.bind_ok_iff.mp rest
  cases rest
  exact ⟨LightClientHeader.upgrade_beacon finalizedOk,
    LightClientHeader.upgrade_beacon optimisticOk⟩

end EthLib.Consensus
