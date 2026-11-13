module

public import EthLib.Consensus.BeaconApi.Blocks
public import EthLib.Consensus.Proofs.BuilderApi
public import EthLib.Consensus.Proofs.Containers.Block

/-!
# Proofs: the block answers of the Beacon API

The header of a block, and its blinded form, have the root of the block.

So the root endpoint gives one root for the block, its header and its blinded block.

The blobs answer keeps blobs in the order of the block.

Each blob it gives has a commitment whose versioned hash is requested.

When each blob of the block commits to its commitment, so does each blob of the answer.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Kzg

variable {preset : Preset} {fork : Fork}

/-- The header of a signed block has the root of the block, and carries its signature. -/
theorem signedHeader_root {block : SignedBeaconBlock preset fork}
    {header : SignedBeaconBlockHeader} (computed : block.signedHeader = .ok header) :
    Serialization.Ssz.SszType.hashTreeRoot header.message = blockRoot block ∧
      header.signature = block.signature := by
  cases rooted : Serialization.Ssz.SszType.hashTreeRoot block.message.body with
  | error e => simp [SignedBeaconBlock.signedHeader, rooted, bind, Except.bind] at computed
  | ok bodyRoot =>
    simp [SignedBeaconBlock.signedHeader, rooted, bind, Except.bind, pure, Except.pure] at computed
    subst computed
    exact ⟨BeaconBlock.hashTreeRoot_header rooted, rfl⟩

/-- From Bellatrix to Fulu, a signed block always has a blinded form. -/
theorem blindedBlock_total (block : SignedBeaconBlock preset fork) (range : HasBuilderApi fork) :
    ∃ blinded, blindedBlock block range = .ok blinded := by
  obtain ⟨message, made⟩ := block.message.blind_total range
  exact ⟨⟨message, block.signature⟩,
    by simp [blindedBlock, made, bind, Except.bind, pure, Except.pure]⟩

/-- From Bellatrix to Fulu, the blinded block has the root of its block, and its signature.

It assumes that the logs bloom of the preset is not empty. -/
theorem blindedBlock_root [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {block : SignedBeaconBlock preset fork} {range : HasBuilderApi fork}
    {blinded : SignedBlindedBeaconBlock preset fork}
    (computed : blindedBlock block range = .ok blinded) :
    Serialization.Ssz.SszType.hashTreeRoot blinded.message = blockRoot block ∧
      blinded.signature = block.signature := by
  cases made : block.message.blind range with
  | error e => simp [blindedBlock, made, bind, Except.bind] at computed
  | ok body =>
    simp [blindedBlock, made, bind, Except.bind, pure, Except.pure] at computed
    subst computed
    exact ⟨by simpa [blockRoot] using BeaconBlock.hashTreeRoot_blind made, rfl⟩

/-- Before Bellatrix, the blinded block endpoint gives the block itself. -/
theorem blindedBlockResponse_before_bellatrix {block : SignedBeaconBlock preset fork}
    (early : fork < .bellatrix) : blindedBlockResponse block = blockResponse block := by
  have none : ¬ HasBuilderApi fork := fun range => absurd range.1 (Nat.not_le.2 early)
  simp [blindedBlockResponse, blockResponse, none, early]

/-- From Gloas, the blinded block endpoint gives the error with code 400. -/
theorem blindedBlockResponse_gloas {block : SignedBeaconBlock preset fork}
    (gloas : .glamsterdam ≤ fork) :
    blindedBlockResponse block =
      .error { code := 400, message := "Blocks from Gloas on do not have a blinded form" } := by
  have none : ¬ HasBuilderApi fork := fun range => absurd range.2 (Nat.not_lt.2 gloas)
  have late : ¬ fork < .bellatrix := Nat.not_lt.2
    (Nat.le_trans (by decide : Fork.bellatrix.ctorIdx ≤ Fork.glamsterdam.ctorIdx) gloas)
  simp [blindedBlockResponse, none, late]

/-- The first items of the kept pairs of a zip keep the order of the first list. -/
private theorem map_fst_filter_zip_sublist {α β : Type} (p : α × β → Bool) :
    ∀ (xs : List α) (ys : List β), (((xs.zip ys).filter p).map Prod.fst).Sublist xs
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    have rest := map_fst_filter_zip_sublist p xs ys
    by_cases keep : p (x, y) = true <;> simp [keep]
    · exact rest
    · exact rest.cons x

/-- The blobs of the answer keep the order of the blobs of the block. -/
theorem blockBlobs_sublist (blobs : List Blob) (commitments : List KZGCommitment)
    (hashes : Option (List VersionedHash)) :
    (blockBlobs blobs commitments hashes).Sublist blobs := by
  exact map_fst_filter_zip_sublist _ _ _

/-- Without hashes, the answer is every blob of the block. -/
theorem blockBlobs_none {blobs : List Blob} {commitments : List KZGCommitment}
    (paired : blobs.length = commitments.length) :
    blockBlobs blobs commitments none = blobs := by
  simp only [blockBlobs, Option.all_none]
  rw [List.filter_eq_self.2 (by simp)]
  exact List.map_fst_zip (Nat.le_of_eq paired)

/-- Each blob of the answer sits at the place of a commitment whose versioned hash is requested. -/
theorem blockBlobs_versionedHash {blobs : List Blob} {commitments : List KZGCommitment}
    {hashes : Option (List VersionedHash)} {blob : Blob}
    (mem : blob ∈ blockBlobs blobs commitments hashes) :
    ∃ (place : Nat) (commitment : KZGCommitment),
      blobs[place]? = some blob ∧ commitments[place]? = some commitment ∧
      ∀ requested ∈ hashes, kzgCommitmentToVersionedHash commitment ∈ requested := by
  simp only [blockBlobs, List.mem_map, List.mem_filter] at mem
  obtain ⟨⟨b, c⟩, ⟨zipped, kept⟩, rfl⟩ := mem
  obtain ⟨place, found⟩ := List.mem_iff_getElem?.1 zipped
  rw [List.getElem?_zip_eq_some] at found
  refine ⟨place, c, found.1, found.2, ?_⟩
  rintro requested rfl
  simpa using kept

/-- Each blob of the answer commits to a commitment of the block whose versioned hash is requested.

Each blob of the block must commit to the commitment at its place. -/
theorem blockBlobs_commitment {setup : TrustedSetup} {blobs : List Blob}
    {commitments : List KZGCommitment} {hashes : Option (List VersionedHash)}
    (committed : ∀ place (blobLt : place < blobs.length)
      (commitmentLt : place < commitments.length),
      blobToKzgCommitment setup blobs[place] = .ok commitments[place])
    {blob : Blob} (mem : blob ∈ blockBlobs blobs commitments hashes) :
    ∃ commitment ∈ commitments, blobToKzgCommitment setup blob = .ok commitment ∧
      ∀ requested ∈ hashes, kzgCommitmentToVersionedHash commitment ∈ requested := by
  obtain ⟨place, commitment, blobAt, commitmentAt, requested⟩ :=
    blockBlobs_versionedHash (hashes := hashes) mem
  obtain ⟨blobLt, blobEq⟩ := List.getElem?_eq_some_iff.1 blobAt
  obtain ⟨commitmentLt, commitmentEq⟩ := List.getElem?_eq_some_iff.1 commitmentAt
  refine ⟨commitment, List.mem_of_getElem? commitmentAt, ?_, requested⟩
  rw [← blobEq, ← commitmentEq]
  exact committed place blobLt commitmentLt

/-- Before Deneb, a block has no blob commitments. -/
theorem blockCommitments_before_deneb {block : BeaconBlock preset fork} (early : fork < .dencun) :
    blockCommitments block = [] := by
  have notGloas : ¬ .glamsterdam ≤ fork := fun late =>
    absurd (Nat.lt_of_lt_of_le early
      (Nat.le_trans (by decide : Fork.dencun.ctorIdx ≤ Fork.glamsterdam.ctorIdx) late))
      (Nat.lt_irrefl _)
  have notDeneb : ¬ .dencun ≤ fork := Nat.not_le.2 early
  simp [blockCommitments, notGloas, notDeneb]

/-- The blobs endpoint answers with the blobs of the commitments of the block. -/
theorem blobsOf_ok {block : SignedBeaconBlock preset fork} {blobs : List Blob}
    {hashes : Option (List VersionedHash)} {kept : List Blob}
    (computed : blobsOf block blobs hashes = .ok kept) :
    kept = blockBlobs blobs (blockCommitments block.message) hashes := by
  unfold blobsOf at computed
  simp only at computed
  split at computed <;> simp_all

end EthLib.Consensus.BeaconApi
