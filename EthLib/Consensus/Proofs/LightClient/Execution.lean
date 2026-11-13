module

public import EthLib.Consensus.Proofs.LightClient.Authenticate
public import EthLib.Consensus.Proofs.LightClient.Upgrade

/-!
# Proofs: the execution branch of a light client header

From Capella a light client header carries the execution data of its block.

A valid header binds that data to any body whose root is its body root, or names a collision.

Before Gloas the data is the payload root at node 25, and from Gloas a block hash.

From Gloas, a header of a slot from Capella to Fulu climbs from that hash to its execution root.

From Deneb the binding reaches the blob gas fields of [EIP-4844].

Before Gloas, the fork of a header from Capella can be later than the fork of its block.

It then carries the upgrade of the payload header of that block.

The theorems take the lawful type of the body, at every preset whose sizes are nonzero.

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- From Capella to the forks before Gloas, the value of a payload holds its block hash at field 12.
-/
theorem ExecutionPayload.values_blockHash (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) (payload : ExecutionPayload preset fork) :
    ∃ values, SszType.toValue payload = .seq values ∧
      values[12]? = some (.bytes payload.blockHash.toArray) := by
  cases fork <;> first
    | exact absurd capella (by decide)
    | exact absurd beforeGloas (by decide)
    | exact ⟨_, rfl, rfl⟩

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- From Capella to the forks before Gloas, node 25 of a body is the root of its payload. -/
theorem BeaconBlockBody.nodeRoot_executionPayload (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) (body : BeaconBlockBody preset fork) {root : Bytes32}
    (rooted : SszType.hashTreeRoot
      (body.executionPayload ⟨Nat.le_trans (by decide) capella, beforeGloas⟩) = .ok root) :
    nodeRoot (SszType.desc (BeaconBlockBody preset fork)) (SszType.toValue body)
      EXECUTION_PAYLOAD_GINDEX = .ok root.toArray := by
  obtain ⟨fields, desc, -, chosen⟩ :=
    BeaconBlockBody.desc_executionPayload (preset := preset) capella beforeGloas
  obtain ⟨values, valued, picked⟩ :=
    BeaconBlockBody.values_executionPayload capella beforeGloas body
  have selected : PathSelects (SszType.desc (BeaconBlockBody preset fork))
      (SszType.toValue body) [.position 9] root.toArray := by
    have sound := LawfulSszType.wellFormed (α := BeaconBlockBody preset fork)
    have fits := LawfulSszType.fits body
    rw [desc] at sound fits ⊢
    rw [valued] at fits ⊢
    exact PathSelects.containerField sound fits chosen picked
      (.root (SszType.hashTreeRoot_ok_iff.mp rooted))
  exact selected.nodeRoot_eq (executionPayloadGindex_eq_of_lt capella beforeGloas)

/-- From Capella to the forks before Gloas, the block hash node of a body is the payload's hash.

The node is 412 at Capella, and 812 from Deneb. -/
theorem BeaconBlockBody.nodeRoot_executionBlockHash (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) (body : BeaconBlockBody preset fork) :
    nodeRoot (SszType.desc (BeaconBlockBody preset fork)) (SszType.toValue body)
      (if .dencun ≤ fork then EXECUTION_BLOCK_HASH_GINDEX_DENEB else EXECUTION_BLOCK_HASH_GINDEX) =
      .ok (body.executionPayload
        ⟨Nat.le_trans (by decide) capella, beforeGloas⟩).blockHash.toArray := by
  obtain ⟨fields, desc, -, chosen⟩ :=
    BeaconBlockBody.desc_executionPayload (preset := preset) capella beforeGloas
  obtain ⟨values, valued, picked⟩ :=
    BeaconBlockBody.values_executionPayload capella beforeGloas body
  obtain ⟨names, payloadFields, payloadDesc, -, hashChosen⟩ :=
    ExecutionPayload.desc_blockHash (preset := preset) capella beforeGloas
  set payload := body.executionPayload ⟨Nat.le_trans (by decide) capella, beforeGloas⟩
  obtain ⟨payloadValues, payloadValued, hashPicked⟩ :=
    ExecutionPayload.values_blockHash capella beforeGloas payload
  have inner : PathSelects (SszType.desc (ExecutionPayload preset fork)) (SszType.toValue payload)
      [.position 12] payload.blockHash.toArray := by
    have sound := LawfulSszType.wellFormed (α := ExecutionPayload preset fork)
    have fits := LawfulSszType.fits payload
    rw [payloadDesc] at sound fits ⊢
    rw [payloadValued] at fits ⊢
    exact PathSelects.containerField sound fits hashChosen hashPicked
      (.root (hashTreeRoot_chunk (by simp [bytesPerChunk])))
  have selected : PathSelects (SszType.desc (BeaconBlockBody preset fork))
      (SszType.toValue body) [.position 9, .position 12] payload.blockHash.toArray := by
    have sound := LawfulSszType.wellFormed (α := BeaconBlockBody preset fork)
    have fits := LawfulSszType.fits body
    rw [desc] at sound fits ⊢
    rw [valued] at fits ⊢
    exact PathSelects.containerField sound fits chosen picked inner
  exact selected.nodeRoot_eq (executionBlockHashGindex_eq_of_lt capella beforeGloas)

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Capella to the forks before Gloas, a valid header proves its execution root.

This holds for a slot from Capella.

The branch climbs from that root, at node 25, to the body root of the beacon header. -/
theorem isValidLightClientHeader_executionBranch {config : Config}
    (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot) :
    ∃ leaf, getLcExecutionRoot config header = .ok leaf ∧
      isValidMerkleBranch leaf (header.executionBranch capella).toList
        (Nat.log2 EXECUTION_PAYLOAD_GINDEX)
        (EXECUTION_PAYLOAD_GINDEX % 2 ^ Nat.log2 EXECUTION_PAYLOAD_GINDEX)
        header.beacon.bodyRoot = true := by
  have gloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) capella
  have below : getSubtreeIndex EXECUTION_PAYLOAD_GINDEX =
      .ok (EXECUTION_PAYLOAD_GINDEX % 2 ^ Nat.log2 EXECUTION_PAYLOAD_GINDEX) := by
    simp [getSubtreeIndex, gindexDepth, gindexBelow, EXECUTION_PAYLOAD_GINDEX, bind,
      Except.bind, pure, Except.pure]
  have late : ¬ computeEpochAtSlot preset header.beacon.slot < config.CAPELLA_FORK_EPOCH :=
    UInt64.not_lt.mpr started
  unfold isValidLightClientHeader at valid
  simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, capella, dite_false,
    dite_true, late, bind, Except.bind, pure, Except.pure, LightClientError.liftRoot,
    Except.mapError, below] at valid
  -- Past the check of the blob fields, the branch climbs from the execution root.
  cases root : getLcExecutionRoot config header with
  | error fault =>
    simp only [root] at valid
    split at valid <;> (try split at valid) <;> cases valid
  | ok leaf =>
    refine ⟨leaf, rfl, ?_⟩
    simp only [root] at valid
    split at valid
    · split at valid
      · cases valid
      · exact Except.ok.inj valid
    · exact Except.ok.inj valid

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Capella to the forks before Gloas, a valid header opens node 25 of its body.

Take any value whose root is the body root of the beacon header, at a slot from Capella.

Its node 25 is the execution root of the header.

Otherwise the search over the two climbs names a SHA-256 collision. -/
theorem isValidLightClientHeader_executionRoot_value {config : Config}
    (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    {α : Type} [SszType α] [LawfulSszType α] (value : α)
    (rooted : SszType.hashTreeRoot value = .ok header.beacon.bodyRoot) {node : Bytes32}
    (read : nodeRoot (SszType.desc α) (SszType.toValue value) EXECUTION_PAYLOAD_GINDEX =
      .ok node.toArray) :
    ∃ leaf, getLcExecutionRoot config header = .ok leaf ∧
      (leaf = node ∨ ∃ honest a b, computeMerkleProof value EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray node.toArray
            (((header.executionBranch capella).toList.drop
              ((header.executionBranch capella).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  obtain ⟨leaf, root, climbs⟩ := isValidLightClientHeader_executionBranch capella beforeGloas valid
    started
  exact ⟨leaf, root, isValidNormalizedMerkleBranch_value (by decide)
    (isValidNormalizedMerkleBranch_of_isValidMerkleBranch (by decide) climbs) value rooted read⟩

/-- A valid header from Capella to Fulu carries the root of the payload of its block.

Take a body of a fork from Capella to Fulu whose root is the body root of the beacon header.

At a slot from Capella, the execution root of the header is the root of the payload of the body.

Otherwise the search over the two climbs names a SHA-256 collision. -/
theorem isValidLightClientHeader_executionPayload {config : Config}
    (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    {bodyFork : Fork} (bodyCapella : .shapella ≤ bodyFork) (bodyBefore : bodyFork < .glamsterdam)
    (body : BeaconBlockBody preset bodyFork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot) :
    ∃ leaf payloadRoot, getLcExecutionRoot config header = .ok leaf ∧
      SszType.hashTreeRoot
        (body.executionPayload ⟨Nat.le_trans (by decide) bodyCapella, bodyBefore⟩) =
          .ok payloadRoot ∧
      (leaf = payloadRoot ∨ ∃ honest a b,
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch capella).toList.drop
              ((header.executionBranch capella).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  obtain ⟨payloadRoot, payloadRooted⟩ := SszType.hashTreeRoot_total
    (body.executionPayload ⟨Nat.le_trans (by decide) bodyCapella, bodyBefore⟩)
  obtain ⟨leaf, root, bound⟩ := isValidLightClientHeader_executionRoot_value capella beforeGloas
    valid started body rooted
    (BeaconBlockBody.nodeRoot_executionPayload bodyCapella bodyBefore body payloadRooted)
  exact ⟨leaf, payloadRoot, root, payloadRooted, bound⟩

/-! ## From Capella to Fulu: the fields of the execution header -/

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- Every count in a payload header fits the word mixed into its root.

The only count is the length of the extra data, below the 64-bit limit of the preset. -/
theorem ExecutionPayloadHeader.commitmentSized (header : ExecutionPayloadHeader preset fork) :
    CommitmentSized (SszType.desc (ExecutionPayloadHeader preset fork))
      (SszType.toValue header) := by
  have extra : header.extraData.data.size < 2 ^ 256 :=
    Nat.lt_of_le_of_lt header.extraData.bound
      (Nat.lt_trans preset.MAX_EXTRA_DATA_BYTES.toNat_lt (by decide))
  refine .container fun pair member => ?_
  by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
    simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues, capella, deneb]
      at member
  -- Each field is a fixed-size vector, an integer, or the extra data, which fits its word.
  all_goals
    repeat' rcases member with rfl | member
    all_goals first
      | exact .byteVector _ _
      | exact .uint _ _
      | exact .byteList extra

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The Capella header of a Capella header is that header. -/
theorem ExecutionPayloadHeader.toCapella_self (header : ExecutionPayloadHeader preset .shapella) :
    header.toCapella (Nat.le_refl _) = header := by
  cases header
  simp only [ExecutionPayloadHeader.toCapella]
  -- The fields of Deneb have no value at Capella, so only the withdrawals root remains.
  congr 1 <;> funext later <;> exact absurd later (by decide)

omit [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Capella to Fulu, the execution root of a header is the root of its execution header.

This holds at a slot from Capella, and from Deneb when the header is from Deneb. -/
theorem getLcExecutionRoot_execution {config : Config} (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) {header : LightClientHeader preset fork}
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (full : .dencun ≤ fork →
      config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot) :
    ∃ root, SszType.hashTreeRoot (header.execution ⟨capella, beforeGloas⟩) = .ok root ∧
      getLcExecutionRoot config header = .ok root := by
  have gloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) capella
  obtain ⟨root, rooted⟩ := SszType.hashTreeRoot_total (header.execution ⟨capella, beforeGloas⟩)
  refine ⟨root, rooted, ?_⟩
  unfold getLcExecutionRoot
  simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, dite_false, capella,
    dite_true, bind, Except.bind]
  by_cases deneb : Fork.dencun ≤ fork
  · simp [deneb, full deneb, LightClientError.liftRoot, Except.mapError, rooted]
  · -- Before Deneb the fork is Capella, whose header is its own Capella header.
    have capellaFork : fork = .shapella := by
      cases fork <;> first | rfl | exact absurd capella (by decide) | exact absurd deneb (by decide)
    subst capellaFork
    simp [deneb, started, LightClientError.liftRoot, Except.mapError,
      ExecutionPayloadHeader.toCapella_self, rooted]

/-- From Capella to Fulu, a valid header binds a header with its execution root to its block.

Take a body of a fork from Capella to Fulu whose root is the body root of the beacon header.

Take two payload headers of one fork.

The first has the execution root of the header, and the second the root of the body's one.

The two are then equal.

Otherwise one of two searches names a SHA-256 collision.

The first is over the climbs of the two branches to the body root.

The second is over the hash inputs of the roots of the two payload headers. -/
theorem isValidLightClientHeader_execution_binding {config : Config}
    (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    {bodyFork : Fork} (bodyCapella : .shapella ≤ bodyFork) (bodyBefore : bodyFork < .glamsterdam)
    (body : BeaconBlockBody preset bodyFork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot)
    {payloadHeader : ExecutionPayloadHeader preset bodyFork}
    (made : (body.executionPayload
      ⟨Nat.le_trans (by decide) bodyCapella, bodyBefore⟩).header = .ok payloadHeader)
    {viewFork : Fork} {left right : ExecutionPayloadHeader preset viewFork}
    (leftRooted : ∃ root, SszType.hashTreeRoot left = .ok root ∧
      getLcExecutionRoot config header = .ok root)
    (rightRooted : SszType.hashTreeRoot right = SszType.hashTreeRoot payloadHeader) :
    left = right ∨
      (∃ (leaf payloadRoot : Bytes32) (honest : List Bytes32) (a b : Array UInt8),
        getLcExecutionRoot config header = .ok leaf ∧
        SszType.hashTreeRoot payloadHeader = .ok payloadRoot ∧
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch capella).toList.drop
              ((header.executionBranch capella).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) ∨
      ∃ leftTree rightTree,
        valueTree (SszType.desc (ExecutionPayloadHeader preset viewFork))
          (SszType.toValue left) = .ok leftTree ∧
        valueTree (SszType.desc (ExecutionPayloadHeader preset viewFork))
          (SszType.toValue right) = .ok rightTree ∧
        ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
          x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  obtain ⟨leaf, payloadRoot, executionRoot, payloadRooted, bound⟩ :=
    isValidLightClientHeader_executionPayload capella beforeGloas valid started bodyCapella
      bodyBefore body rooted
  obtain ⟨root, leftRoot, sameRoot⟩ := leftRooted
  rw [sameRoot] at executionRoot
  cases executionRoot
  -- The header of the payload has the root of the payload.
  have payloadHeaderRooted : SszType.hashTreeRoot payloadHeader = .ok payloadRoot := by
    rw [ExecutionPayload.hashTreeRoot_header bodyBefore made, payloadRooted]
  rcases bound with same | ⟨honest, a, b, built, found, rest⟩
  · subst same
    rcases SszType.hashTreeRoot_binding (ExecutionPayloadHeader.commitmentSized _)
        (ExecutionPayloadHeader.commitmentSized _) leftRoot
        (rightRooted.trans payloadHeaderRooted) with equal | collision
    · exact .inl equal
    · exact .inr (.inr collision)
  · exact .inr (.inl ⟨leaf, payloadRoot, honest, a, b, sameRoot, payloadHeaderRooted, built,
      found, rest⟩)

/-- From Capella to Fulu, a valid header carries the execution header of its block, field by field.

Take a body of the fork of the header whose root is the body root of the beacon header.

At a slot from Capella, and from Deneb for a header from Deneb, it has the body's payload header.

Otherwise one of two searches names a SHA-256 collision.

The first is over the climbs of the two branches to the body root.

The second is over the hash inputs of the two roots of the execution headers. -/
theorem isValidLightClientHeader_execution_eq {config : Config}
    (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (full : .dencun ≤ fork →
      config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (body : BeaconBlockBody preset fork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot)
    {payloadHeader : ExecutionPayloadHeader preset fork}
    (made : (body.executionPayload
      ⟨Nat.le_trans (by decide) capella, beforeGloas⟩).header = .ok payloadHeader) :
    header.execution ⟨capella, beforeGloas⟩ = payloadHeader ∨
      (∃ (leaf payloadRoot : Bytes32) (honest : List Bytes32) (a b : Array UInt8),
        getLcExecutionRoot config header = .ok leaf ∧
        SszType.hashTreeRoot payloadHeader = .ok payloadRoot ∧
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch capella).toList.drop
              ((header.executionBranch capella).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) ∨
      ∃ leftTree rightTree,
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue (header.execution ⟨capella, beforeGloas⟩)) = .ok leftTree ∧
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue payloadHeader) = .ok rightTree ∧
        ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
          x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y :=
  isValidLightClientHeader_execution_binding capella beforeGloas valid started capella
    beforeGloas body rooted made (getLcExecutionRoot_execution capella beforeGloas started full)
    rfl

/-! ## From Deneb: the blob gas of the execution header -/

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The header of a payload keeps the blob gas used and the excess blob gas of the payload. -/
theorem ExecutionPayload.header_blobGas {payload : ExecutionPayload preset fork}
    {header : ExecutionPayloadHeader preset fork} (made : payload.header = .ok header) :
    header.blobGasUsed = payload.blobGasUsed ∧ header.excessBlobGas = payload.excessBlobGas := by
  unfold ExecutionPayload.header at made
  obtain ⟨_, -, rest⟩ := Base.bind_ok_iff.mp made
  dsimp only at rest
  split at rest
  · obtain ⟨_, -, rest⟩ := Base.bind_ok_iff.mp rest
    cases rest
    exact ⟨rfl, rfl⟩
  · cases rest
    exact ⟨rfl, rfl⟩

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Deneb to Fulu, a valid header of a slot before Deneb uses no blob gas.

Its execution header has zero blob gas used and zero excess blob gas, as the check requires. -/
theorem isValidLightClientHeader_blobGas_zero {config : Config}
    (deneb : .dencun ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (early : computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH) :
    (header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).blobGasUsed deneb = 0 ∧
      (header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).excessBlobGas deneb = 0 := by
  have gloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) deneb
  have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) deneb
  unfold isValidLightClientHeader at valid
  simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, dite_false, capella,
    dite_true, deneb, early, true_and, bind, Except.bind] at valid
  by_contra nonzero
  rw [not_and_or] at nonzero
  simp only [nonzero, ↓reduceIte, pure, Except.pure] at valid
  cases valid

/-- From Deneb to Fulu, a valid header carries the blob gas of the payload of its block.

Take a body of the fork of the header whose root is the body root, at a slot from Deneb.

The blob gas used and the excess blob gas of the header are those of the payload of the body.

Otherwise a search over the branches or the header roots names a SHA-256 collision.

The schedule must start Capella no later than Deneb. -/
theorem isValidLightClientHeader_blobGas {config : Config}
    (deneb : .dencun ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH)
    (body : BeaconBlockBody preset fork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot)
    {payloadHeader : ExecutionPayloadHeader preset fork}
    (made : (body.executionPayload
      ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).header = .ok payloadHeader) :
    ((header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).blobGasUsed deneb =
        (body.executionPayload ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).blobGasUsed deneb ∧
      (header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).excessBlobGas deneb =
        (body.executionPayload
          ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).excessBlobGas deneb) ∨
      (∃ (leaf payloadRoot : Bytes32) (honest : List Bytes32) (a b : Array UInt8),
        getLcExecutionRoot config header = .ok leaf ∧
        SszType.hashTreeRoot payloadHeader = .ok payloadRoot ∧
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.drop
              ((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) ∨
      ∃ leftTree rightTree,
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue (header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩)) =
            .ok leftTree ∧
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue payloadHeader) = .ok rightTree ∧
        ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
          x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  have capellaSlot : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot :=
    UInt64.le_trans ordered started
  rcases isValidLightClientHeader_execution_eq (Nat.le_trans (by decide) deneb) beforeGloas valid
      capellaSlot (fun _ => started) body rooted made with same | collision
  · obtain ⟨used, excess⟩ := ExecutionPayload.header_blobGas made
    left
    rw [same, used, excess]
    exact ⟨rfl, rfl⟩
  · exact .inr collision

/-! ## Before Gloas: a header of a later fork than its block

A store of a later fork upgrades a header of an earlier fork before it checks it.

The fields of the block's payload header carry over, and a field of a later fork is zero.
-/

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Deneb, a payload header with no blob gas is the upgrade of its Capella header. -/
theorem ExecutionPayloadHeader.eq_upgrade_toCapella (deneb : .dencun ≤ fork)
    (header : ExecutionPayloadHeader preset fork) (used : header.blobGasUsed deneb = 0)
    (excess : header.excessBlobGas deneb = 0) :
    header = (header.toCapella (Nat.le_trans (by decide) deneb)).upgrade fork := by
  cases header
  simp only [ExecutionPayloadHeader.toCapella, ExecutionPayloadHeader.upgrade]
  -- The withdrawals root carries over, and both blob gas fields are zero on each side.
  congr 1 <;> funext later <;>
    simp only [show ¬ Fork.dencun ≤ Fork.shapella by decide, ↓reduceDIte]
  · exact used
  · exact excess

omit [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Capella to Fulu, the execution root of a header is the root of its Capella form.

This holds at a slot from Capella and before Deneb.

The Capella form drops the two blob gas fields. -/
theorem getLcExecutionRoot_toCapella {config : Config} (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) {header : LightClientHeader preset fork}
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (early : computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH) :
    ∃ root, SszType.hashTreeRoot
        ((header.execution ⟨capella, beforeGloas⟩).toCapella capella) = .ok root ∧
      getLcExecutionRoot config header = .ok root := by
  have gloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) capella
  have notDeneb := UInt64.not_le.mpr early
  obtain ⟨root, rooted⟩ := SszType.hashTreeRoot_total
    ((header.execution ⟨capella, beforeGloas⟩).toCapella capella)
  refine ⟨root, rooted, ?_⟩
  unfold getLcExecutionRoot
  simp [LightClientError.requireFork, altair, gloas, capella, notDeneb, started, bind,
    Except.bind, LightClientError.liftRoot, Except.mapError, rooted]

/-- From Deneb to Fulu, a valid header of a Capella block carries its upgraded payload header.

Take a Capella body whose root is the body root of the beacon header.

At a slot from Capella and before Deneb, the header has the upgrade of the body's payload header.

So it has the fields of that payload header, and zero for both blob gas fields.

Otherwise one of two searches names a SHA-256 collision.

The first is over the climbs of the two branches to the body root.

The second is over the hash inputs of the roots of the two Capella headers. -/
theorem isValidLightClientHeader_execution_eq_upgrade_capella {config : Config}
    (deneb : .dencun ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (early : computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH)
    (body : BeaconBlockBody preset .shapella)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot)
    {payloadHeader : ExecutionPayloadHeader preset .shapella}
    (made : (body.executionPayload ⟨by decide, by decide⟩).header = .ok payloadHeader) :
    header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩ =
        payloadHeader.upgrade fork ∨
      (∃ (leaf payloadRoot : Bytes32) (honest : List Bytes32) (a b : Array UInt8),
        getLcExecutionRoot config header = .ok leaf ∧
        SszType.hashTreeRoot payloadHeader = .ok payloadRoot ∧
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.drop
              ((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) ∨
      ∃ leftTree rightTree,
        valueTree (SszType.desc (ExecutionPayloadHeader preset .shapella))
          (SszType.toValue ((header.execution ⟨Nat.le_trans (by decide) deneb,
            beforeGloas⟩).toCapella (Nat.le_trans (by decide) deneb))) = .ok leftTree ∧
        valueTree (SszType.desc (ExecutionPayloadHeader preset .shapella))
          (SszType.toValue payloadHeader) = .ok rightTree ∧
        ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
          x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) deneb
  rcases isValidLightClientHeader_execution_binding capella beforeGloas valid started
      (bodyFork := .shapella) (by decide) (by decide) body rooted made
      (getLcExecutionRoot_toCapella capella beforeGloas started early) rfl with
    equal | collision
  · -- The Capella headers agree, and a valid header of this slot uses no blob gas.
    obtain ⟨used, excess⟩ := isValidLightClientHeader_blobGas_zero deneb beforeGloas valid early
    left
    rw [← equal]
    exact ExecutionPayloadHeader.eq_upgrade_toCapella deneb _ used excess
  · exact .inr collision

/-- From Deneb to Fulu, a valid header of a block from Deneb carries its upgraded payload header.

Take a body of a fork from Deneb to Fulu whose root is the body root of the beacon header.

Its fork can be earlier or later than the fork of the header.

At a slot from Capella and from Deneb, the header has the upgrade of the body's payload header.

The two forks give a payload header the same fields, so the upgrade keeps every field.

Otherwise one of two searches names a SHA-256 collision.

The first is over the climbs of the two branches to the body root.

The second is over the hash inputs of the roots of the execution header and of that upgrade. -/
theorem isValidLightClientHeader_execution_eq_upgrade {config : Config}
    (deneb : .dencun ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (full : config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    {bodyFork : Fork} (bodyDeneb : .dencun ≤ bodyFork) (bodyBefore : bodyFork < .glamsterdam)
    (body : BeaconBlockBody preset bodyFork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot)
    {payloadHeader : ExecutionPayloadHeader preset bodyFork}
    (made : (body.executionPayload
      ⟨Nat.le_trans (by decide) bodyDeneb, bodyBefore⟩).header = .ok payloadHeader) :
    header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩ =
        payloadHeader.upgrade fork ∨
      (∃ (leaf payloadRoot : Bytes32) (honest : List Bytes32) (a b : Array UInt8),
        getLcExecutionRoot config header = .ok leaf ∧
        SszType.hashTreeRoot payloadHeader = .ok payloadRoot ∧
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.drop
              ((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) ∨
      ∃ leftTree rightTree,
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue (header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩)) =
            .ok leftTree ∧
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue (payloadHeader.upgrade fork)) = .ok rightTree ∧
        ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
          x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) deneb
  -- The upgrade of the payload header keeps its root.
  exact isValidLightClientHeader_execution_binding capella beforeGloas valid started
    (Nat.le_trans (by decide) bodyDeneb) bodyBefore body rooted made
    (getLcExecutionRoot_execution capella beforeGloas started (fun _ => full))
    (ExecutionPayloadHeader.hashTreeRoot_upgrade bodyDeneb deneb payloadHeader)

/-- From Deneb to Fulu, a valid header carries the blob gas of a block from Deneb to Fulu.

Take a body of a fork from Deneb to Fulu whose root is the body root, at a slot from Deneb.

The blob gas used and the excess blob gas of the header are those of the payload of the body.

Otherwise a search over the branches or the header roots names a SHA-256 collision.

The schedule must start Capella no later than Deneb. -/
theorem isValidLightClientHeader_blobGas_upgrade {config : Config}
    (deneb : .dencun ≤ fork) (beforeGloas : fork < .glamsterdam)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH)
    {bodyFork : Fork} (bodyDeneb : .dencun ≤ bodyFork) (bodyBefore : bodyFork < .glamsterdam)
    (body : BeaconBlockBody preset bodyFork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot)
    {payloadHeader : ExecutionPayloadHeader preset bodyFork}
    (made : (body.executionPayload
      ⟨Nat.le_trans (by decide) bodyDeneb, bodyBefore⟩).header = .ok payloadHeader) :
    ((header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).blobGasUsed deneb =
        (body.executionPayload
          ⟨Nat.le_trans (by decide) bodyDeneb, bodyBefore⟩).blobGasUsed bodyDeneb ∧
      (header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩).excessBlobGas deneb =
        (body.executionPayload
          ⟨Nat.le_trans (by decide) bodyDeneb, bodyBefore⟩).excessBlobGas bodyDeneb) ∨
      (∃ (leaf payloadRoot : Bytes32) (honest : List Bytes32) (a b : Array UInt8),
        getLcExecutionRoot config header = .ok leaf ∧
        SszType.hashTreeRoot payloadHeader = .ok payloadRoot ∧
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.drop
              ((header.executionBranch (Nat.le_trans (by decide) deneb)).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) ∨
      ∃ leftTree rightTree,
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue (header.execution ⟨Nat.le_trans (by decide) deneb, beforeGloas⟩)) =
            .ok leftTree ∧
        valueTree (SszType.desc (ExecutionPayloadHeader preset fork))
          (SszType.toValue (payloadHeader.upgrade fork)) = .ok rightTree ∧
        ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
          x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  rcases isValidLightClientHeader_execution_eq_upgrade deneb beforeGloas valid
      (UInt64.le_trans ordered started) started bodyDeneb bodyBefore body rooted made with
    same | collision
  · obtain ⟨used, excess⟩ := ExecutionPayload.header_blobGas made
    left
    rw [same, ← used, ← excess]
    simp [ExecutionPayloadHeader.upgrade, bodyDeneb]
  · exact .inr collision

/-- Before Gloas, the upgrade of a valid header carries the upgraded payload header of its block.

Take a valid header from Capella, and a body of its fork whose root is its body root.

The slot is from Capella, and from Deneb for a header from Deneb.

The upgrade of the header to a later fork then has the upgrade of the body's payload header.

So it has the fields of that payload header, and zero for each field that the block lacks.

Otherwise a search over the header before the upgrade names a SHA-256 collision.

The search is over the climbs of the two branches, or over the hash inputs of the header roots. -/
theorem LightClientHeader.isValidLightClientHeader_upgrade_execution {config : Config}
    {pre post : Fork} {later : pre ≤ post} (capella : .shapella ≤ pre)
    (postBefore : post < .glamsterdam)
    {header : LightClientHeader preset pre} {upgraded : LightClientHeader preset post}
    (valid : isValidLightClientHeader config header = .ok true)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (full : .dencun ≤ pre →
      config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    (body : BeaconBlockBody preset pre)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot)
    {payloadHeader : ExecutionPayloadHeader preset pre}
    (made : (body.executionPayload ⟨Nat.le_trans (by decide) capella,
      Nat.lt_of_le_of_lt later postBefore⟩).header = .ok payloadHeader)
    (computed : header.upgrade config post later = .ok upgraded) :
    upgraded.execution ⟨Nat.le_trans capella later, postBefore⟩ = payloadHeader.upgrade post ∨
      (∃ (leaf payloadRoot : Bytes32) (honest : List Bytes32) (a b : Array UInt8),
        getLcExecutionRoot config header = .ok leaf ∧
        SszType.hashTreeRoot payloadHeader = .ok payloadRoot ∧
        computeMerkleProof body EXECUTION_PAYLOAD_GINDEX = .ok honest ∧
        findBranchCollision EXECUTION_PAYLOAD_GINDEX 0 leaf.toArray payloadRoot.toArray
            (((header.executionBranch capella).toList.drop
              ((header.executionBranch capella).toList.length -
                Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) ∨
      ∃ leftTree rightTree,
        valueTree (SszType.desc (ExecutionPayloadHeader preset pre))
          (SszType.toValue (header.execution
            ⟨capella, Nat.lt_of_le_of_lt later postBefore⟩)) = .ok leftTree ∧
        valueTree (SszType.desc (ExecutionPayloadHeader preset pre))
          (SszType.toValue payloadHeader) = .ok rightTree ∧
        ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
          x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  rcases isValidLightClientHeader_execution_eq capella (Nat.lt_of_le_of_lt later postBefore) valid
      started full body rooted made with same | collision
  · left
    rw [LightClientHeader.upgrade_execution capella postBefore computed, same]
  · exact .inr collision

/-! ## From Gloas: the block hash -/

/-- From Gloas, node 2856 of a body is the parent block hash of its bid. -/
theorem BeaconBlockBody.nodeRoot_parentBlockHash (gloas : .glamsterdam ≤ fork)
    (body : BeaconBlockBody preset fork) :
    nodeRoot (SszType.desc (BeaconBlockBody preset fork)) (SszType.toValue body)
      EXECUTION_BLOCK_HASH_GINDEX_GLOAS =
      .ok (body.signedExecutionPayloadBid gloas).message.parentBlockHash.toArray := by
  set signed := body.signedExecutionPayloadBid gloas
  have bid : PathSelects (SszType.desc (ExecutionPayloadBid preset fork))
      (SszType.toValue signed.message) [.position 0] signed.message.parentBlockHash.toArray := by
    cases fork
    all_goals try exact absurd gloas (by decide)
    all_goals
      apply PathSelects.progressiveField
        (LawfulSszType.wellFormed (α := ExecutionPayloadBid preset _))
        (LawfulSszType.fits signed.message) (ordinal := 0) (child := SszType.desc Hash32)
        (inner := .bytes signed.message.parentBlockHash.toArray)
      · rfl
      · rfl
      · exact .root (hashTreeRoot_chunk (by simp [bytesPerChunk]))
  have bidSigned : PathSelects (SszType.desc (SignedExecutionPayloadBid preset fork))
      (SszType.toValue signed) [.position 0, .position 0]
      signed.message.parentBlockHash.toArray :=
    PathSelects.containerField
      (LawfulSszType.wellFormed (α := SignedExecutionPayloadBid preset fork))
      (LawfulSszType.fits signed) rfl rfl bid
  have selected : PathSelects (SszType.desc (BeaconBlockBody preset fork)) (SszType.toValue body)
      [.position (if .hegota ≤ fork then 8 else 10), .position 0, .position 0]
      signed.message.parentBlockHash.toArray := by
    cases fork
    all_goals try exact absurd gloas (by decide)
    all_goals
      apply PathSelects.progressiveField
        (LawfulSszType.wellFormed (α := type_of% body)) (LawfulSszType.fits body)
        (child := SszType.desc (SignedExecutionPayloadBid preset _))
        (inner := SszType.toValue signed)
      · rfl
      · rfl
      · exact bidSigned
  exact selected.nodeRoot_eq (executionBlockHashGindexGloas_eq_of_le gloas)

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Gloas, a valid header proves its block hash by the index of the fork of its slot.

The index is that of Gloas from Gloas, else that of Deneb from Deneb, else that of Capella.

The slot must be at least at one of these forks. -/
theorem isValidLightClientHeader_blockHashBranch {config : Config} (gloas : .glamsterdam ≤ fork)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (reached : config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot ∨
      config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot ∨
      config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot) :
    isValidNormalizedMerkleBranch (header.executionBlockHash gloas)
      (header.executionBranch (Nat.le_trans (by decide) gloas)).toList
      (if config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot then
        EXECUTION_BLOCK_HASH_GINDEX_GLOAS
      else if config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot then
        EXECUTION_BLOCK_HASH_GINDEX_DENEB
      else EXECUTION_BLOCK_HASH_GINDEX) header.beacon.bodyRoot = .ok true := by
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) gloas
  unfold isValidLightClientHeader at valid
  simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, dite_true, bind,
    Except.bind, LightClientError.liftRoot, Except.mapError] at valid
  split_ifs at valid ⊢ <;> first
    | (split at valid <;> simp_all)
    | (exfalso; simp_all)

/-- From Gloas, a valid header of a block from Gloas carries the parent block hash of its bid.

Take a body from Gloas whose root is the body root of the beacon header, at a slot from Gloas.

The block hash of the header is the parent block hash of the bid of the body.

Otherwise the search over the two climbs names a SHA-256 collision. -/
theorem isValidLightClientHeader_parentBlockHash {config : Config} (gloas : .glamsterdam ≤ fork)
    {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (gloasSlot : config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    {bodyFork : Fork} (bodyGloas : .glamsterdam ≤ bodyFork)
    (body : BeaconBlockBody preset bodyFork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot) :
    header.executionBlockHash gloas =
        (body.signedExecutionPayloadBid bodyGloas).message.parentBlockHash ∨
      ∃ honest a b, computeMerkleProof body EXECUTION_BLOCK_HASH_GINDEX_GLOAS = .ok honest ∧
        findBranchCollision EXECUTION_BLOCK_HASH_GINDEX_GLOAS 0
            (header.executionBlockHash gloas).toArray
            (body.signedExecutionPayloadBid bodyGloas).message.parentBlockHash.toArray
            (((header.executionBranch (Nat.le_trans (by decide) gloas)).toList.drop
              ((header.executionBranch (Nat.le_trans (by decide) gloas)).toList.length -
                Nat.log2 EXECUTION_BLOCK_HASH_GINDEX_GLOAS)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 EXECUTION_BLOCK_HASH_GINDEX_GLOAS)).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  have climbs := isValidLightClientHeader_blockHashBranch gloas valid (.inl gloasSlot)
  simp only [gloasSlot, ↓reduceIte] at climbs
  exact isValidNormalizedMerkleBranch_value (by decide) climbs body rooted
    (BeaconBlockBody.nodeRoot_parentBlockHash bodyGloas body)

/-- From Gloas, a valid header of a block from Capella to Fulu carries the hash of its payload.

Take a body from Capella to Fulu, from Deneb exactly when the slot is, whose root is the body root.

The block hash of the header is the block hash of the payload of the body.

Otherwise the search over the two climbs names a SHA-256 collision. -/
theorem isValidLightClientHeader_executionBlockHash {config : Config}
    (gloas : .glamsterdam ≤ fork) {header : LightClientHeader preset fork}
    (valid : isValidLightClientHeader config header = .ok true)
    (earlier : computeEpochAtSlot preset header.beacon.slot < config.GLOAS_FORK_EPOCH)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot)
    {bodyFork : Fork} (bodyCapella : .shapella ≤ bodyFork) (bodyBefore : bodyFork < .glamsterdam)
    (layout : config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot ↔
      .dencun ≤ bodyFork)
    (body : BeaconBlockBody preset bodyFork)
    (rooted : SszType.hashTreeRoot body = .ok header.beacon.bodyRoot) :
    header.executionBlockHash gloas =
        (body.executionPayload ⟨Nat.le_trans (by decide) bodyCapella, bodyBefore⟩).blockHash ∨
      ∃ honest a b, computeMerkleProof body
          (if .dencun ≤ bodyFork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
            else EXECUTION_BLOCK_HASH_GINDEX) = .ok honest ∧
        findBranchCollision
            (if .dencun ≤ bodyFork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
              else EXECUTION_BLOCK_HASH_GINDEX) 0
            (header.executionBlockHash gloas).toArray
            (body.executionPayload ⟨Nat.le_trans (by decide) bodyCapella,
              bodyBefore⟩).blockHash.toArray
            (((header.executionBranch (Nat.le_trans (by decide) gloas)).toList.drop
              ((header.executionBranch (Nat.le_trans (by decide) gloas)).toList.length -
                Nat.log2 (if .dencun ≤ bodyFork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
                  else EXECUTION_BLOCK_HASH_GINDEX))).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2
              (if .dencun ≤ bodyFork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
                else EXECUTION_BLOCK_HASH_GINDEX))).map Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  have climbs := isValidLightClientHeader_blockHashBranch gloas valid (.inr (.inr started))
  have notGloas : ¬ config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot :=
    UInt64.not_le.mpr earlier
  -- The index the client reads is the index of the payload of a body of the fork of the slot.
  have same : (if config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot then
      EXECUTION_BLOCK_HASH_GINDEX_DENEB else EXECUTION_BLOCK_HASH_GINDEX) =
      (if .dencun ≤ bodyFork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
        else EXECUTION_BLOCK_HASH_GINDEX) := by
    by_cases deneb : Fork.dencun ≤ bodyFork <;> simp [layout, deneb]
  simp only [notGloas, ↓reduceIte, same] at climbs
  exact isValidNormalizedMerkleBranch_value (by split <;> decide) climbs body rooted
    (BeaconBlockBody.nodeRoot_executionBlockHash bodyCapella bodyBefore body)

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The root that a Gloas header rebuilds for an execution header, for every slot, branch and fork.

At the genesis slot it is the root of the empty execution header of the given fork.

Otherwise the block hash climbs to it as field 12 of the execution header, by a slice of the branch.

The slice ends before the last 4 nodes, which climb from the payload at node 25 to the body root.

It has the 5 nodes before those when the given fork is from Deneb, and 4 nodes otherwise.

A branch too short for that slice gives an error. -/
theorem rebuildLcExecutionRoot_eq {slot : Slot} {blockHash : Hash32} {branch : List Bytes32}
    {payloadFork : Fork} :
    rebuildLcExecutionRoot (preset := preset) slot blockHash branch payloadFork =
      if slot = GENESIS_SLOT then
        LightClientError.liftRoot
          (SszType.hashTreeRoot (ExecutionPayloadHeader.empty preset payloadFork))
      else
        let depth := if .dencun ≤ payloadFork then 5 else 4
        LightClientError.liftRoot (computeMerkleBranchRoot blockHash
          (branch.extract (branch.length - (4 + depth)) (branch.length - 4)) depth 12) := by
  have payload : Nat.log2 EXECUTION_PAYLOAD_GINDEX = 4 := by decide +kernel
  have deneb : Nat.log2 44 = 5 := by decide +kernel
  have capella : Nat.log2 28 = 4 := by decide +kernel
  unfold rebuildLcExecutionRoot
  by_cases genesis : slot = GENESIS_SLOT
  · simp [genesis]
  · -- Both indices are 12 at their depth, and the two cuts of the branch make one slice.
    by_cases later : Fork.dencun ≤ payloadFork <;>
      simp [genesis, later, payload, deneb, capella, payloadHeaderBlockHashGindex,
        getSubtreeIndex, gindexDepth, gindexBelow, bind, Except.bind, pure, Except.pure,
        LightClientError.liftRoot, Except.mapError, List.drop_take] <;>
      congr 3

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- From Gloas, the execution root of a header is rebuilt for a slot before Gloas.

The slot must be from Capella or from Deneb, since the configuration does not order these forks.

The rebuilt execution header is that of Deneb for a slot from Deneb, and of Capella otherwise. -/
theorem getLcExecutionRoot_rebuild {config : Config} (gloas : .glamsterdam ≤ fork)
    {header : LightClientHeader preset fork}
    (earlier : computeEpochAtSlot preset header.beacon.slot < config.GLOAS_FORK_EPOCH)
    (started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot ∨
      config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot) :
    getLcExecutionRoot config header =
      rebuildLcExecutionRoot (preset := preset) header.beacon.slot (header.executionBlockHash gloas)
        (header.executionBranch (Nat.le_trans (by decide) gloas)).toList
        (if config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot then .dencun
          else .shapella) := by
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) gloas
  have notGloas : ¬ config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset header.beacon.slot :=
    UInt64.not_le.mpr earlier
  unfold getLcExecutionRoot
  simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, dite_true, notGloas, bind,
    Except.bind]
  split_ifs with deneb capella
  · rfl
  · rfl
  · exact absurd (started.resolve_right deneb) capella

/-! ## The headers that the client checks -/

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The header of a bootstrap that starts a store is valid. -/
theorem initializeLightClientStore_header_valid {config : Config} {trustedBlockRoot : Root}
    {bootstrap : LightClientBootstrap preset fork} {store : LightClientStore preset fork}
    (computed : initializeLightClientStore config trustedBlockRoot bootstrap = .ok store) :
    isValidLightClientHeader config bootstrap.header = .ok true := by
  unfold initializeLightClientStore at computed
  obtain ⟨_, -, rest⟩ := Base.bind_ok_iff.mp computed
  obtain ⟨verdict, valid, rest⟩ := Base.bind_ok_iff.mp rest
  obtain ⟨_, checked, -⟩ := Base.bind_ok_iff.mp rest
  obtain rfl := LightClientError.require_ok.mp checked
  exact valid

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The attested header of an accepted update is valid. -/
theorem validateLightClientUpdate_attestedHeader_valid {config : Config}
    {checks : SignatureChecks} {store : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ()) :
    isValidLightClientHeader config update.attestedHeader = .ok true := by
  unfold validateLightClientUpdate at accepted
  simp only [Base.bind_ok_iff, LightClientError.require_ok] at accepted
  obtain ⟨_, -, _, -, verdict, valid, _, checked, -⟩ := accepted
  subst checked
  exact valid

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The finalized header of an accepted update that proves finality is valid.

This holds after the genesis slot, where the header is not the zero header. -/
theorem validateLightClientUpdate_finalizedHeader_valid {config : Config}
    {checks : SignatureChecks} {store : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    (finality : update.isFinalityUpdate = true)
    (later : update.finalizedHeader.beacon.slot ≠ GENESIS_SLOT) :
    isValidLightClientHeader config update.finalizedHeader = .ok true := by
  have checked := (validateLightClientUpdate_proves accepted).2.1
  unfold validateFinality at checked
  simp only [finality, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at checked
  split at checked
  · contradiction
  obtain ⟨verdict, valid, rest⟩ := Base.bind_ok_iff.mp checked
  obtain ⟨_, required, -⟩ := Base.bind_ok_iff.mp rest
  obtain rfl := LightClientError.require_ok.mp required
  exact valid

end EthLib.Consensus
