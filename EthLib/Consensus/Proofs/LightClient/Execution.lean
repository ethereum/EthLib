module

public import EthLib.Consensus.Proofs.LightClient.Authenticate

/-!
# Proofs: the execution branch of a light client header

From Capella a light client header carries the execution data of its block.

A branch proves that data against the body root of the beacon header.

From Capella to Fulu the data is an execution payload header, and the branch reaches node 25.

That node of a body is the root of its execution payload.

From Gloas the data is a block hash, and the index depends on the fork of the slot.

For a slot from Gloas, node 2856 of the body is the parent block hash of its bid.

For an earlier slot, node 812 of a body from Deneb, or 412 of a Capella body, is its payload's hash.

Take a valid header and a body whose root is the body root of the header.

The header then carries the root or the hash of that body.

Otherwise the two climbs to the body root give a SHA-256 collision, which the theorems name.

The headers that the client checks are valid: the header of a bootstrap and the attested header.

So is the finalized header of an update that proves finality, after the genesis slot.

Each theorem holds at every preset.

The blob gas fields of the execution header come from [EIP-4844].

Each binding is a consequence of the SSZ trees of the types, not a further rule of the protocol.

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

Take a body of the fork of the slot, from Capella to Fulu, whose root is the body root.

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
