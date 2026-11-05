module

public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container
public import EthLib.Serialization.Proofs.Ssz.Merkle.Branch
public import EthLib.Serialization.Proofs.Ssz.Typed.Gindex
public import EthLib.Serialization.Proofs.Ssz.Codec.PathValues
public import EthLib.Serialization.Proofs.Ssz.Typed.ForkKind

/-!
# Proofs: the blob sidecars

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it.

Two sidecars whose branches verify for one blob of one block carry one commitment root.

Otherwise the two climbs to the body root hash two different messages to one SHA-256 output.

The depth of the inclusion proof, 17 for both presets, is the depth that the body type gives.

Every sidecar built from a block passes the inclusion check.

For both presets, a block gives one sidecar per blob.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

instance : NeZero Cryptography.Kzg.Constants.BYTES_PER_BLOB := ⟨by decide⟩

instance {preset : Preset} [NeZero preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat] :
    LawfulSszType (BlobSidecar preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BlobIdentifier := .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- Two sidecars that verify for one blob index and one body root have one commitment root.

Otherwise the two climbs hash two different messages to one SHA-256 output. -/
theorem verifyBlobSidecarInclusionProof_binding {preset : Preset} {fork : Fork}
    {first second : BlobSidecar preset} (sameIndex : first.index = second.index)
    (sameRoot :
      first.signedBlockHeader.message.bodyRoot = second.signedBlockHeader.message.bodyRoot)
    (firstValid : verifyBlobSidecarInclusionProof preset fork first = true)
    (secondValid : verifyBlobSidecarInclusionProof preset fork second = true) :
    ∃ leaf other index, SszType.hashTreeRoot first.kzgCommitment = .ok leaf ∧
      SszType.hashTreeRoot second.kzgCommitment = .ok other ∧
      (leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray
          (first.kzgCommitmentInclusionProof.toList.map Vector.toArray),
        ∃ b ∈ branchMessages index 0 other.toArray
          (second.kzgCommitmentInclusionProof.toList.map Vector.toArray),
          a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
          Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
            Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  unfold verifyBlobSidecarInclusionProof at firstValid secondValid
  rw [← sameIndex] at secondValid
  cases gindex : blobKzgCommitmentGindex preset fork first.index.toNat with
  | error fault => simp [gindex] at firstValid
  | ok g =>
    cases leafRoot : SszType.hashTreeRoot first.kzgCommitment with
    | error fault => simp [gindex, leafRoot] at firstValid
    | ok leaf =>
      cases otherRoot : SszType.hashTreeRoot second.kzgCommitment with
      | error fault => simp [gindex, otherRoot] at secondValid
      | ok other =>
        cases subtree : getSubtreeIndex g with
        | error fault => simp [gindex, leafRoot, subtree] at firstValid
        | ok index =>
          simp only [gindex, leafRoot, subtree] at firstValid
          simp only [gindex, otherRoot, subtree, ← sameRoot] at secondValid
          exact ⟨leaf, other, index, rfl, rfl, isValidMerkleBranch_binding firstValid secondValid⟩

section Inclusion

open Cryptography.Kzg

variable {preset : Preset} {fork : Fork}

/-- From Deneb to Fulu, the commitments are field 11 of a body of 12 or 13 fields. -/
private theorem body_desc (deneb : .dencun ≤ fork ∧ fork < .glamsterdam) :
    (BeaconBlockBody.names fork).idxOf "blob_kzg_commitments" = 11 ∧
      ∃ fields, SszType.desc (BeaconBlockBody preset fork) =
          .container (BeaconBlockBody.names fork) fields ∧
        (fields.length = 12 ∨ fields.length = 13) ∧
        fields[11]? = some (SszType.desc (BlobKZGCommitments preset fork)) := by
  obtain ⟨low, high⟩ := deneb
  cases fork <;>
    first
    | exact absurd low (by decide)
    | exact absurd high (by decide)
    | exact ⟨rfl, _, rfl, by first | exact .inl rfl | exact .inr rfl, rfl⟩

/-- From Deneb to Fulu, the commitments are field 11 of the value of a body. -/
private theorem body_values (deneb : .dencun ≤ fork ∧ fork < .glamsterdam)
    (body : BeaconBlockBody preset fork) :
    ∃ values, SszType.toValue body = .seq values ∧
      values[11]? = some (SszType.toValue (body.blobKzgCommitments deneb)) := by
  obtain ⟨low, high⟩ := deneb
  cases fork <;>
    first | exact absurd low (by decide) | exact absurd high (by decide) | exact ⟨_, rfl, rfl⟩

/-- Before Gloas, the commitments of a block form a list bounded by the preset. -/
private theorem commitments_desc (beforeGloas : fork < .glamsterdam) :
    SszType.desc (BlobKZGCommitments preset fork) =
      .list (SszType.desc KZGCommitment) preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat := by
  simp [SszType.desc, not_switch_of_lt beforeGloas]

/-- Field 11 of a container of 12 or 13 fields is leaf 11 of a tree of 16 leaves. -/
private theorem resolveStep_field_eleven {fields : List Desc} {names : List String} {field : Desc}
    (count : fields.length = 12 ∨ fields.length = 13) (chosen : fields[11]? = some field) :
    (Desc.container names fields).resolveStep (.position 11) = .ok (27, some field) := by
  have leaves : nextPow2 fields.length = 16 := by
    rcases count with count | count <;> rw [count] <;> simp [nextPow2, depthFor]
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.chunkCount, chosen, leaves,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Element `index` of a list of 32-byte composite elements is leaf `index` below the length. -/
private theorem getGeneralizedIndex_listElement {element : Desc} {limit index : Nat}
    (composite : element.isBasic = false) (inside : index < limit) :
    getGeneralizedIndex (.list element limit) [.position index] =
      .ok (2 * nextPow2 limit + index) := by
  have resolved : (Desc.list element limit).resolveStep (.position index) =
      .ok (2 * nextPow2 limit + index, some element) := by
    rw [resolveStep_list element limit index inside, Desc.itemLength_composite composite]
    have nodes : (limit * bytesPerChunk + bytesPerChunk - 1) / bytesPerChunk = limit := by
      unfold bytesPerChunk; omega
    have position : index * bytesPerChunk / bytesPerChunk = index := by
      unfold bytesPerChunk; omega
    rw [nodes, position, gindexConcat_mixed_leaf inside]
    rfl
  exact getGeneralizedIndex_step resolved (getGeneralizedIndex_nil element)
    (gindexConcat_root_right (by unfold nextPow2; have := Nat.two_pow_pos (depthFor limit); omega))

/-- From Deneb to Fulu, the generalized index of a commitment of a body.

The list is field 11 of 16 leaves, so node 27 of the body.

Below it, one level passes the length of the list.

The list has as many leaves as the least power of two at or above its limit. -/
theorem blobKzgCommitmentGindex_eq (deneb : .dencun ≤ fork ∧ fork < .glamsterdam) {index : Nat}
    (inside : index < preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) :
    blobKzgCommitmentGindex preset fork index =
      .ok (27 * (2 * nextPow2 preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) + index) := by
  obtain ⟨named, fields, desc, count, chosen⟩ := body_desc (preset := preset) deneb
  rw [commitments_desc deneb.2] at chosen
  unfold blobKzgCommitmentGindex SszType.getGeneralizedIndex
  rw [desc, named]
  refine getGeneralizedIndex_step (resolveStep_field_eleven count chosen)
    (getGeneralizedIndex_listElement rfl inside) ?_
  have wide := Nat.two_pow_pos (depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat)
  rw [gindexConcat_eq (by decide) (by unfold nextPow2; omega)]
  have room := le_two_pow_depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat
  have depth : Nat.log2 (2 * nextPow2 preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat + index) =
      depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat + 1 := by
    apply (Nat.log2_eq_iff (by unfold nextPow2; omega)).mpr
    simp only [nextPow2, Nat.pow_succ]
    constructor <;> omega
  rw [depth]
  congr 1
  simp only [nextPow2, Nat.pow_succ]
  omega

/-- Both presets allow 4096 commitments in a block, with proofs of depth 17. -/
private theorem named_limits (named : preset = .mainnet ∨ preset = .minimal) :
    preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat = 2 ^ 12 ∧
      preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat = 17 := by
  rcases named with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- The depth of the inclusion proof is the one the specification derives from the body type.

It is the depth of the commitment list in the body, plus one level for the length of the list.

Then it adds the base-2 logarithm of the most commitments, rounded up.

This holds from Deneb to the forks before Gloas, for both presets. -/
theorem kzgCommitmentInclusionProofDepth_eq (named : preset = .mainnet ∨ preset = .minimal)
    (deneb : .dencun ≤ fork ∧ fork < .glamsterdam) :
    ∃ gindex, SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
        [.position ((BeaconBlockBody.names fork).idxOf "blob_kzg_commitments")] = .ok gindex ∧
      preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat =
        Nat.log2 gindex + 1 + depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat := by
  obtain ⟨position, fields, desc, count, chosen⟩ := body_desc (preset := preset) deneb
  refine ⟨27, ?_, ?_⟩
  · unfold SszType.getGeneralizedIndex
    rw [desc, position]
    exact getGeneralizedIndex_step (resolveStep_field_eleven count chosen)
      (getGeneralizedIndex_nil _) (gindexConcat_root_right (by decide))
  · rw [named_limits named |>.1, named_limits named |>.2, depthFor_pow]
    decide

/-- From Deneb to Fulu, every commitment of a body sits at the depth of the inclusion proof.

This holds for every index below the most commitments of a block, for both presets. -/
theorem blobKzgCommitmentGindex_depth (named : preset = .mainnet ∨ preset = .minimal)
    (deneb : .dencun ≤ fork ∧ fork < .glamsterdam) {index : Nat}
    (inside : index < preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) :
    ∃ gindex, blobKzgCommitmentGindex preset fork index = .ok gindex ∧
      Nat.log2 gindex = preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat := by
  refine ⟨_, blobKzgCommitmentGindex_eq deneb inside, ?_⟩
  have room := le_two_pow_depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat
  have depth :
      Nat.log2 (27 * (2 * nextPow2 preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat) + index) =
        depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat + 5 := by
    apply (Nat.log2_eq_iff (by unfold nextPow2; omega)).mpr
    simp only [nextPow2, Nat.pow_succ]
    constructor <;> omega
  rw [depth, named_limits named |>.1, named_limits named |>.2, depthFor_pow]

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- The generic branch of commitment `index` of a body climbs from its root to that of the body. -/
private theorem inclusion_branch (deneb : .dencun ≤ fork ∧ fork < .glamsterdam)
    {body : BeaconBlockBody preset fork} {index : Nat} {commitment : KZGCommitment}
    (chosen : (body.blobKzgCommitments deneb).data[index]? = some commitment) :
    ∃ gindex leaf root nodes, blobKzgCommitmentGindex preset fork index = .ok gindex ∧
      SszType.hashTreeRoot commitment = .ok leaf ∧ SszType.hashTreeRoot body = .ok root ∧
      buildProof (SszType.desc (BeaconBlockBody preset fork)) (SszType.toValue body) gindex =
        .ok (nodes.map Vector.toArray) ∧
      isValidMerkleBranch leaf nodes (Nat.log2 gindex) (gindex % 2 ^ Nat.log2 gindex) root =
        true := by
  have inside : index < preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp (by simpa using chosen)).1
      ((body.blobKzgCommitments deneb).bound deneb.2)
  obtain ⟨position, fields, desc, count, field⟩ := body_desc (preset := preset) deneb
  obtain ⟨values, valued, commitments⟩ := body_values deneb body
  obtain ⟨leaf, rooted⟩ := SszType.hashTreeRoot_total commitment
  -- The commitment is the node that the path names in the tree of the body.
  have element : PathSelects (SszType.desc (BlobKZGCommitments preset fork))
      (SszType.toValue (body.blobKzgCommitments deneb)) [.position index] leaf.toArray := by
    have fits := LawfulSszType.fits (body.blobKzgCommitments deneb)
    rw [commitments_desc deneb.2] at fits ⊢
    exact PathSelects.listElement fits rfl (by simp [SszType.toValue, chosen])
      (PathSelects.root (SszType.hashTreeRoot_ok_iff.mp rooted))
  have selects : PathSelects (SszType.desc (BeaconBlockBody preset fork))
      (SszType.toValue body) [.position 11, .position index] leaf.toArray := by
    have sound := LawfulSszType.wellFormed (α := BeaconBlockBody preset fork)
    have fits := LawfulSszType.fits body
    rw [desc] at sound fits ⊢
    rw [valued] at fits ⊢
    exact PathSelects.containerField sound fits field commitments element
  obtain ⟨gindex, located, read⟩ := selects.reads
  have named : blobKzgCommitmentGindex preset fork index = .ok gindex := by
    unfold blobKzgCommitmentGindex SszType.getGeneralizedIndex
    rw [position]
    exact located
  have deep : 2 ≤ gindex := by
    rw [blobKzgCommitmentGindex_eq deneb inside] at named
    cases named
    unfold nextPow2
    have := Nat.two_pow_pos (depthFor preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat)
    omega
  obtain ⟨root, nodes, bodyRoot, proved, valid⟩ :=
    SszType.buildProof_isValidMerkleBranch body deep read
  exact ⟨gindex, leaf, root, nodes, named, rooted, bodyRoot, proved, valid⟩

/-- Nodes of 32 bytes convert back to the vectors they came from. -/
private theorem mapM_toChunk (nodes : List Bytes32) :
    (nodes.map Vector.toArray).mapM toChunk = .ok nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => exact Base.mapM_cons_ok.mpr ⟨node, rest, toChunk_ok_iff.mpr rfl, ih, rfl⟩

/-- A built inclusion proof climbs from its commitment to the root of the body.

The commitment is the one at the index, and the proof uses the depth and index at its level. -/
theorem blobKzgCommitmentInclusionProof_valid (deneb : .dencun ≤ fork ∧ fork < .glamsterdam)
    {body : BeaconBlockBody preset fork} {index : Nat} {commitment : KZGCommitment}
    (chosen : (body.blobKzgCommitments deneb).data[index]? = some commitment)
    {branch : Vector Bytes32 preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat}
    (built : blobKzgCommitmentInclusionProof body index = .ok branch) :
    ∃ gindex leaf root, blobKzgCommitmentGindex preset fork index = .ok gindex ∧
      SszType.hashTreeRoot commitment = .ok leaf ∧ SszType.hashTreeRoot body = .ok root ∧
      Nat.log2 gindex = preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat ∧
      isValidMerkleBranch leaf branch.toList preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat
        (gindex % 2 ^ Nat.log2 gindex) root = true := by
  obtain ⟨gindex, leaf, root, nodes, named, rooted, bodyRoot, proved, valid⟩ :=
    inclusion_branch deneb chosen
  -- The built proof is the branch that the generic construction gives.
  unfold blobKzgCommitmentInclusionProof at built
  simp only [named, proved, mapM_toChunk, bind, Except.bind] at built
  split at built
  · rename_i exact
    cases built
    have length : nodes.length = preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat := by
      simpa using exact
    have depth : Nat.log2 gindex = preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat := by
      have := (Bool.and_eq_true_iff.mp valid).1
      simp only [beq_iff_eq] at this
      omega
    refine ⟨gindex, leaf, root, named, rooted, bodyRoot, depth, ?_⟩
    have listed : (⟨nodes.toArray, exact⟩ : Vector Bytes32 _).toList = nodes := by simp
    rw [listed, ← depth]
    exact valid
  · cases built

/-- For both presets, the inclusion proof of every commitment of a body is built. -/
theorem blobKzgCommitmentInclusionProof_ok (named : preset = .mainnet ∨ preset = .minimal)
    (deneb : .dencun ≤ fork ∧ fork < .glamsterdam) {body : BeaconBlockBody preset fork}
    {index : Nat} {commitment : KZGCommitment}
    (chosen : (body.blobKzgCommitments deneb).data[index]? = some commitment) :
    ∃ branch, blobKzgCommitmentInclusionProof body index = .ok branch := by
  have inside : index < preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp (by simpa using chosen)).1
      ((body.blobKzgCommitments deneb).bound deneb.2)
  obtain ⟨gindex, _, _, nodes, located, _, _, proved, valid⟩ := inclusion_branch deneb chosen
  obtain ⟨other, located', depth⟩ := blobKzgCommitmentGindex_depth named deneb inside
  rw [located] at located'
  cases located'
  have length : nodes.length = preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat := by
    have := (Bool.and_eq_true_iff.mp valid).1
    simp only [beq_iff_eq] at this
    omega
  unfold blobKzgCommitmentInclusionProof
  simp only [located, proved, mapM_toChunk, bind, Except.bind]
  split
  · exact ⟨_, rfl⟩
  · rename_i short
    exact absurd (by simpa using length) short

/-- Every sidecar built from a signed block passes the inclusion check of its commitment.

This holds from Deneb to the forks before Gloas, for every preset. -/
theorem getBlobSidecars_verify (deneb : .dencun ≤ fork ∧ fork < .glamsterdam)
    {signed : SignedBeaconBlock preset fork} {blobs : List Blob} {proofs : List KZGProof}
    {sidecars : List (BlobSidecar preset)}
    (made : getBlobSidecars deneb signed blobs proofs = .ok sidecars) :
    ∀ sidecar ∈ sidecars, verifyBlobSidecarInclusionProof preset fork sidecar = true := by
  unfold getBlobSidecars at made
  obtain ⟨header, headed, mapped⟩ := Base.bind_ok_iff.mp made
  intro sidecar member
  obtain ⟨⟨blob, index⟩, _, step⟩ := Base.mapM_ok_mem mapped sidecar member
  cases chosen : (signed.message.body.blobKzgCommitments deneb).data[index]? with
  | none => simp [chosen, throw, throwThe, MonadExceptOf.throw] at step
  | some commitment =>
  cases proven : proofs[index]? with
  | none => simp [chosen, proven, throw, throwThe, MonadExceptOf.throw] at step
  | some proof =>
  cases built : blobKzgCommitmentInclusionProof signed.message.body index with
  | error fault => simp [chosen, proven, built, bind, Except.bind] at step
  | ok branch =>
  simp only [chosen, proven, built, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at step
  subst step
  obtain ⟨gindex, leaf, root, named, rooted, bodyRoot, depth, valid⟩ :=
    blobKzgCommitmentInclusionProof_valid deneb chosen built
  -- The header names the root of the body.
  unfold SignedBeaconBlock.signedHeader at headed
  simp only [bodyRoot, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at headed
  subst headed
  have small : index < 2 ^ 64 :=
    Nat.lt_trans (List.getElem?_eq_some_iff.mp (by simpa using chosen)).1
      (Nat.lt_of_le_of_lt ((signed.message.body.blobKzgCommitments deneb).bound deneb.2)
        (UInt64.toNat_lt _))
  have positive : 1 ≤ gindex := getGeneralizedIndex_positive _ _ _ named
  have below : getSubtreeIndex gindex = .ok (gindex % 2 ^ Nat.log2 gindex) := by
    simp [getSubtreeIndex, gindexDepth, gindexBelow, Nat.not_lt.mpr positive, bind,
      Except.bind, pure, Except.pure]
  unfold verifyBlobSidecarInclusionProof
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small, named, rooted, below]
  exact valid

/-- For both presets, a signed block gives one sidecar per blob.

The block must hold a commitment, and the list of proofs a proof, for each blob. -/
theorem getBlobSidecars_ok (named : preset = .mainnet ∨ preset = .minimal)
    (deneb : .dencun ≤ fork ∧ fork < .glamsterdam) {signed : SignedBeaconBlock preset fork}
    {blobs : List Blob} {proofs : List KZGProof}
    (enoughCommitments :
      blobs.length ≤ (signed.message.body.blobKzgCommitments deneb).data.size)
    (enoughProofs : blobs.length ≤ proofs.length) :
    ∃ sidecars, getBlobSidecars deneb signed blobs proofs = .ok sidecars ∧
      sidecars.length = blobs.length := by
  obtain ⟨root, rooted⟩ := SszType.hashTreeRoot_total signed.message.body
  have headed : signed.signedHeader = .ok ⟨⟨signed.message.slot, signed.message.proposerIndex,
      signed.message.parentRoot, signed.message.stateRoot, root⟩, signed.signature⟩ := by
    simp [SignedBeaconBlock.signedHeader, rooted, bind, Except.bind, pure, Except.pure]
  have mapped : ∀ {f : Blob × Nat → Except Err (BlobSidecar preset)},
      (∀ x ∈ blobs.zipIdx, ∃ y, f x = .ok y) →
      ∃ ys, blobs.zipIdx.mapM f = .ok ys ∧ ys.length = blobs.length := fun each => by
    obtain ⟨ys, made⟩ := Base.mapM_exists_ok each
    exact ⟨ys, made, by rw [Base.mapM_ok_length made, List.length_zipIdx]⟩
  unfold getBlobSidecars
  rw [headed]
  apply mapped
  rintro ⟨blob, index⟩ member
  have inside := (List.mem_zipIdx member).2.1
  simp only [Nat.zero_add] at inside
  have chosen : (signed.message.body.blobKzgCommitments deneb).data[index]? =
      some (signed.message.body.blobKzgCommitments deneb).data[index] :=
    Array.getElem?_eq_getElem (by omega)
  have proven : proofs[index]? = some proofs[index] := List.getElem?_eq_getElem (by omega)
  obtain ⟨branch, built⟩ := blobKzgCommitmentInclusionProof_ok named deneb chosen
  simp only [chosen, proven, built, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

end Inclusion

end EthLib.Consensus
