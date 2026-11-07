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

Before Gloas, an upgrade keeps a header valid when its slot needs no field that the header lacks.

A header of an earlier fork reaches Gloas through its Electra form, so it stays valid as well.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- An Electra header with the SSZ value of the empty one has the beacon header of the empty one. -/
private theorem beacon_of_same {header : LightClientHeader preset .pectra}
    (same : sameSszValue header (LightClientHeader.empty preset .pectra) = true) :
    header.beacon = (LightClientHeader.empty preset .pectra).beacon := by
  have values := beq_iff_eq.mp same
  simp only [SszType.toValue, SszFields.toValues, Value.seq.injEq, List.cons.injEq] at values
  obtain ⟨⟨slot, proposer, parent, state, body, -⟩, -⟩ := values
  simp only [Value.uint.injEq, Value.bytes.injEq, UInt64.toNat_inj, Vector.toArray_inj]
    at slot proposer parent state body
  cases beacon : header.beacon
  simp_all [LightClientHeader.empty]

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
    exact (beacon_of_same empty).symm
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

/-- A payload header with the empty SSZ value keeps it when upgraded.

Both forks are from Capella.

The fields that only the later fork has are zero, as in the empty header. -/
private theorem sameSszValue_upgrade_empty {pre post : Fork} (capella : .shapella ≤ pre)
    (postCapella : .shapella ≤ post) (header : ExecutionPayloadHeader preset pre)
    (same : sameSszValue header (ExecutionPayloadHeader.empty preset pre) = true) :
    sameSszValue (header.upgrade post) (ExecutionPayloadHeader.empty preset post) = true := by
  unfold sameSszValue at same ⊢
  rw [beq_iff_eq] at same ⊢
  by_cases deneb : Fork.dencun ≤ pre <;> by_cases postDeneb : Fork.dencun ≤ post <;>
  simp [SszType.toValue, SszFields.toValues, ExecutionPayloadHeader.upgrade,
    ExecutionPayloadHeader.empty, capella, postCapella, deneb, postDeneb] at same ⊢ <;>
  first | exact same | tauto

/-- Dropping an upgraded payload header to Capella gives the same header as dropping the old one.

Both forks are from Capella. -/
private theorem ExecutionPayloadHeader.toCapella_upgrade {pre post : Fork}
    (capella : .shapella ≤ pre) (postCapella : .shapella ≤ post)
    (execution : ExecutionPayloadHeader preset pre) :
    (execution.upgrade post).toCapella postCapella = execution.toCapella capella := by
  simp [ExecutionPayloadHeader.upgrade, ExecutionPayloadHeader.toCapella, capella]

/-- A payload header from Deneb keeps its root when upgraded to another fork from Deneb.

The two forks give it the same fields and the same field names. -/
private theorem ExecutionPayloadHeader.hashTreeRoot_upgrade {pre post : Fork}
    (deneb : .dencun ≤ pre) (postDeneb : .dencun ≤ post)
    (execution : ExecutionPayloadHeader preset pre) :
    SszType.hashTreeRoot (execution.upgrade post) = SszType.hashTreeRoot execution := by
  have capella : Fork.shapella ≤ pre := Nat.le_trans (by decide) deneb
  have postCapella : Fork.shapella ≤ post := Nat.le_trans (by decide) postDeneb
  simp [SszType.hashTreeRoot, SszType.root, SszFields.roots, ExecutionPayloadHeader.upgrade,
    ExecutionPayloadHeader.names, sinceNames, capella, deneb, postCapella, postDeneb]

/-- A vector cast to an equal length is all zero exactly when the vector is. -/
private theorem cast_beq_replicate {n m : Nat} (h : n = m) (v : Vector Bytes32 n) :
    (v.cast h == Vector.replicate m zeroBytes32) = (v == Vector.replicate n zeroBytes32) := by
  subst h
  rfl

/-- A vector cast to an equal length keeps its list. -/
private theorem cast_toList {n m : Nat} (h : n = m) (v : Vector Bytes32 n) :
    (v.cast h).toList = v.toList := by
  subst h
  rfl

/-- The execution root of an upgraded header is the root of the header.

The header is from Capella, and so is its upgrade.

A header of a slot from Deneb is from Deneb, and so is its upgrade. -/
private theorem root_upgradeFields {config : Config}
    {pre post : Fork} (capella : .shapella ≤ pre) (postCapella : .shapella ≤ post)
    (before : pre < .glamsterdam)
    (postBefore : post < .glamsterdam) {header : LightClientHeader preset pre}
    (denebSlot : .dencun ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH)
    (keepsDeneb : .dencun ≤ pre → .dencun ≤ post) :
    getLcExecutionRoot config (header.upgradeFields post before postBefore) =
      getLcExecutionRoot config header := by
  have early : ¬ Fork.glamsterdam ≤ pre := Nat.not_le_of_lt before
  have postEarly : ¬ Fork.glamsterdam ≤ post := Nat.not_le_of_lt postBefore
  have exec : ∀ h, (header.upgradeFields post before postBefore).execution h =
      (header.execution ⟨capella, before⟩).upgrade post := fun h => by
    simp [LightClientHeader.upgradeFields, capella]
  have beacon : (header.upgradeFields post before postBefore).beacon = header.beacon := rfl
  have altair : Fork.altair ≤ pre := Nat.le_trans (by decide) capella
  have postAltair : Fork.altair ≤ post := Nat.le_trans (by decide) postCapella
  unfold getLcExecutionRoot
  simp only [LightClientError.requireFork, altair, postAltair, beacon, early, postEarly, capella,
    postCapella, ↓reduceIte, ↓reduceDIte, exec]
  rcases denebSlot with deneb | deneb
  · have postDeneb := keepsDeneb deneb
    simp only [deneb, postDeneb, true_and,
      ExecutionPayloadHeader.hashTreeRoot_upgrade deneb postDeneb,
      ExecutionPayloadHeader.toCapella_upgrade capella postCapella]
  · have notDeneb := UInt64.not_le.mpr deneb
    simp only [notDeneb, and_false, ↓reduceIte,
      ExecutionPayloadHeader.toCapella_upgrade capella postCapella]

/-- Before Gloas, the header of another fork with the fields of a valid header is valid too.

That fork must be Altair or later.

It must keep the fields of Capella and of Deneb that the header has.

The slot of the header must not belong to a fork whose fields the header lacks.

So a header without the fields of Capella has a slot before Capella.

A header without the fields of Deneb has a slot before Deneb. -/
theorem LightClientHeader.isValidLightClientHeader_upgradeFields {config : Config}
    {pre post : Fork} (postAltair : .altair ≤ post)
    (keepsCapella : .shapella ≤ pre → .shapella ≤ post)
    (keepsDeneb : .dencun ≤ pre → .dencun ≤ post) (before : pre < .glamsterdam)
    (postBefore : post < .glamsterdam) {header : LightClientHeader preset pre}
    (valid : isValidLightClientHeader config header = .ok true)
    (capellaSlot : .shapella ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.CAPELLA_FORK_EPOCH)
    (denebSlot : .dencun ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH) :
    isValidLightClientHeader config (header.upgradeFields post before postBefore) = .ok true := by
  have beacon : (header.upgradeFields post before postBefore).beacon = header.beacon := rfl
  have early : ¬ Fork.glamsterdam ≤ pre := Nat.not_le_of_lt before
  have postEarly : ¬ Fork.glamsterdam ≤ post := Nat.not_le_of_lt postBefore
  by_cases altair : Fork.altair ≤ pre
  swap
  · simp [isValidLightClientHeader, LightClientError.requireFork, altair, bind, Except.bind]
      at valid
  by_cases capella : Fork.shapella ≤ pre
  · have postCapella := keepsCapella capella
    have exec : ∀ h, (header.upgradeFields post before postBefore).execution h =
        (header.execution ⟨capella, before⟩).upgrade post := fun h => by
      simp [LightClientHeader.upgradeFields, capella]
    have branch : ∀ h, ((header.upgradeFields post before postBefore).executionBranch h).toList =
        (header.executionBranch capella).toList := fun h => by
      simp only [LightClientHeader.upgradeFields, capella, ↓reduceDIte]
      exact cast_toList _ _
    have same : ∀ h, ((header.upgradeFields post before postBefore).executionBranch h ==
        Vector.replicate _ zeroBytes32) = (header.executionBranch capella ==
        Vector.replicate _ zeroBytes32) := fun h => by
      simp only [LightClientHeader.upgradeFields, capella, ↓reduceDIte]
      exact cast_beq_replicate _ _
    have root := root_upgradeFields (config := config) capella postCapella before postBefore
      (header := header) denebSlot keepsDeneb
    unfold isValidLightClientHeader at valid ⊢
    simp only [LightClientError.requireFork, altair, postAltair, early, postEarly, ↓reduceIte,
      ↓reduceDIte, beacon, capella, postCapella, exec, branch, same, root, bind, Except.bind]
        at valid ⊢
    by_cases pd : Fork.dencun ≤ pre
    · have pd' := keepsDeneb pd
      have blob : ∀ h, ((header.execution ⟨capella, before⟩).upgrade post).blobGasUsed h =
          (header.execution ⟨capella, before⟩).blobGasUsed pd := fun h => by
        simp [ExecutionPayloadHeader.upgrade, pd]
      have excess : ∀ h, ((header.execution ⟨capella, before⟩).upgrade post).excessBlobGas h =
          (header.execution ⟨capella, before⟩).excessBlobGas pd := fun h => by
        simp [ExecutionPayloadHeader.upgrade, pd]
      simp only [pd, pd', ↓reduceDIte, blob, excess] at valid ⊢
      by_cases c1 : computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH ∧
          ((header.execution ⟨capella, before⟩).blobGasUsed pd ≠ 0 ∨
            (header.execution ⟨capella, before⟩).excessBlobGas pd ≠ 0)
      · simp [c1, pure, Except.pure] at valid
      · simp only [c1, ↓reduceIte] at valid ⊢
        by_cases c2 : computeEpochAtSlot preset header.beacon.slot < config.CAPELLA_FORK_EPOCH
        · simp only [c2, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true]
            at valid ⊢
          obtain ⟨h1, h2⟩ := valid
          exact ⟨sameSszValue_upgrade_empty capella postCapella _ h1, h2⟩
        · simp only [c2, ↓reduceIte] at valid ⊢
          exact valid
    · simp only [pd, ↓reduceDIte] at valid
      have early := denebSlot.resolve_left pd
      by_cases pd' : Fork.dencun ≤ post
      · have blob : ∀ h, ((header.execution ⟨capella, before⟩).upgrade post).blobGasUsed h = 0 :=
          fun h => by simp [ExecutionPayloadHeader.upgrade, pd]
        have excess : ∀ h,
            ((header.execution ⟨capella, before⟩).upgrade post).excessBlobGas h = 0 :=
          fun h => by simp [ExecutionPayloadHeader.upgrade, pd]
        simp only [pd', ↓reduceDIte, blob, excess, ne_eq, not_true_eq_false, or_self, and_false,
          ↓reduceIte] at valid ⊢
        by_cases c2 : computeEpochAtSlot preset header.beacon.slot < config.CAPELLA_FORK_EPOCH
        · simp only [c2, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true]
            at valid ⊢
          obtain ⟨h1, h2⟩ := valid
          exact ⟨sameSszValue_upgrade_empty capella postCapella _ h1, h2⟩
        · simp only [c2, ↓reduceIte] at valid ⊢
          exact valid
      · simp only [pd', ↓reduceDIte] at ⊢
        by_cases c2 : computeEpochAtSlot preset header.beacon.slot < config.CAPELLA_FORK_EPOCH
        · simp only [c2, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true]
            at valid ⊢
          obtain ⟨h1, h2⟩ := valid
          exact ⟨sameSszValue_upgrade_empty capella postCapella _ h1, h2⟩
        · simp only [c2, ↓reduceIte] at valid ⊢
          exact valid
  · have exec : ∀ h, (header.upgradeFields post before postBefore).execution h =
        ExecutionPayloadHeader.empty preset post := fun h => by
      simp [LightClientHeader.upgradeFields, capella]
    have branch : ∀ h, (header.upgradeFields post before postBefore).executionBranch h =
        Vector.replicate _ zeroBytes32 := fun h => by
      simp [LightClientHeader.upgradeFields, capella]
    have slot := capellaSlot.resolve_left capella
    unfold isValidLightClientHeader at valid ⊢
    simp only [LightClientError.requireFork, altair, postAltair, early, postEarly, ↓reduceIte,
      ↓reduceDIte, beacon, capella] at valid ⊢
    simp [exec, branch, slot, ExecutionPayloadHeader.empty, sameSszValue, pure, Except.pure, bind,
      Except.bind]

/-- From Gloas, the upgrade of a valid header passes the header check too.

The header is not the empty one, and its slot comes before Gloas.

The slot must not belong to a fork whose fields the header lacks, as for an upgrade before Gloas.

The configuration activates Capella no later than Deneb. -/
theorem LightClientHeader.isValidLightClientHeader_upgrade {config : Config} {pre post : Fork}
    {later : pre ≤ post} (gloas : .glamsterdam ≤ post) {header : LightClientHeader preset pre}
    {upgraded : LightClientHeader preset post}
    (valid : isValidLightClientHeader config header = .ok true)
    (notEmpty : header.beacon ≠ (LightClientHeader.empty preset pre).beacon)
    (capellaSlot : .shapella ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.CAPELLA_FORK_EPOCH)
    (denebSlot : .dencun ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH)
    (beforeGloas : .glamsterdam ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.GLOAS_FORK_EPOCH)
    (computed : header.upgrade config post later = .ok upgraded) :
    isValidLightClientHeader config upgraded = .ok true := by
  unfold LightClientHeader.upgrade at computed
  by_cases preGloas : Fork.glamsterdam ≤ pre
  · simp only [preGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    have altair : Fork.altair ≤ pre := Nat.le_trans (by decide) preGloas
    have postAltair : Fork.altair ≤ post := Nat.le_trans (by decide) gloas
    unfold isValidLightClientHeader at valid ⊢
    simp only [LightClientError.requireFork, altair, postAltair, preGloas, gloas, ↓reduceIte,
      ↓reduceDIte, cast_toList] at valid ⊢
    exact valid
  · simp only [preGloas, gloas, ↓reduceDIte] at computed
    have preBefore : pre < .glamsterdam := Nat.lt_of_not_le preGloas
    have epoch := beforeGloas.resolve_left preGloas
    refine LightClientHeader.isValidLightClientHeader_toGloas (header := header.upgradeFields
      .pectra preBefore (by decide)) ?_ ?_ ordered epoch computed
    · exact LightClientHeader.isValidLightClientHeader_upgradeFields (by decide)
        (fun _ => by decide) (fun _ => by decide) preBefore (by decide) valid capellaSlot denebSlot
    · rw [Bool.eq_false_iff]
      intro same
      exact notEmpty (beacon_of_same same)

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
