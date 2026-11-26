module

public import EthLib.Base.Proofs.List
public import EthLib.Consensus.BeaconApi.Blocks
public import EthLib.Consensus.Proofs.BuilderApi
public import EthLib.Consensus.Proofs.ForkChoice.Store
public import EthLib.Consensus.Proofs.Containers.Block

/-!
# Proofs: the block answers of the Beacon API

The header of a block, and its blinded form, have the root of the block.

So the root endpoint gives one root for the block, its header and its blinded block.

The blobs answer keeps blobs in the order of the block.

Each blob it gives has a commitment whose versioned hash is requested.

When each blob of the block commits to its commitment, so does each blob of the answer.

A known head is canonical, and a block that the store does not hold is not.

Each header of the headers answer matches the requested slot and parent root.

A columns answer holds exactly the requested sidecars that the node holds, in any order.

From Gloas, the envelope answer is the given envelope when its message matches the stored one.
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

/-- The answer for a list of hashes keeps the blobs of the block, each with its hash, in order. -/
theorem requestedBlobs_sublist (requested : List VersionedHash) (blobs : List Blob)
    (commitments : List KZGCommitment) :
    (requestedBlobs requested blobs commitments).Sublist (blobHashes blobs commitments) :=
  (Base.eraseDupsBy_sublist _ _).trans List.filter_sublist

/-- Each blob of the answer for a list of hashes is the first in the block with its hash. -/
theorem requestedBlobs_first {requested : List VersionedHash} {blobs : List Blob}
    {commitments : List KZGCommitment} {entry : Blob × VersionedHash}
    (mem : entry ∈ requestedBlobs requested blobs commitments) :
    ∃ front back, blobHashes blobs commitments = front ++ entry :: back ∧
      ∀ earlier ∈ front, earlier.2 ≠ entry.2 := by
  -- The entry is the first of its hash among the requested blobs.
  rw [requestedBlobs] at mem
  obtain ⟨front, back, split, first⟩ :=
    Base.eq_append_cons_of_mem_eraseDupsBy (fun e : Blob × VersionedHash => e.2) _ mem
  -- Its hash is requested.
  have asked := (List.mem_filter.1 (split ▸ List.mem_append_right front
    (List.mem_cons_self (a := entry) (l := back)))).2
  obtain ⟨front', back', whole, sorted⟩ := Base.eq_append_cons_of_filter split
  refine ⟨front', back', whole, fun earlier mem same => ?_⟩
  rcases sorted earlier mem with known | dropped
  · exact first earlier known same
  -- A blob before it that was not requested has another hash.
  · simp_all

/-- The hashes of the answer: the requested hashes of the commitments, once each, in block order. -/
theorem requestedBlobs_hashes {requested : List VersionedHash} {blobs : List Blob}
    {commitments : List KZGCommitment} (paired : blobs.length = commitments.length) :
    (requestedBlobs requested blobs commitments).map (·.2) =
      ((commitments.map kzgCommitmentToVersionedHash).filter requested.contains).eraseDups := by
  rw [requestedBlobs, Base.map_eraseDupsBy, blobHashes]
  conv_rhs => rw [← List.map_snd_zip (l₁ := blobs) (Nat.le_of_eq paired.symm), List.map_map]
  congr 1
  induction blobs.zip commitments with
  | nil => rfl
  | cons pair rest ih =>
    simp only [List.map_cons, List.filter_cons]
    split <;> simp_all

/-- No two blobs of the answer for a list of hashes have one versioned hash. -/
theorem requestedBlobs_nodup (requested : List VersionedHash) (blobs : List Blob)
    (commitments : List KZGCommitment) :
    ((requestedBlobs requested blobs commitments).map (·.2)).Nodup := by
  rw [requestedBlobs, Base.map_eraseDupsBy]
  exact Base.nodup_eraseDups _

/-- The blobs of the answer keep the order of the blobs of the block. -/
theorem blockBlobs_sublist (blobs : List Blob) (commitments : List KZGCommitment)
    (hashes : Option (List VersionedHash)) :
    (blockBlobs blobs commitments hashes).Sublist blobs := by
  -- The first items of the zip are a prefix of the blobs.
  have firsts : ((blobs.zip commitments).map Prod.fst).Sublist blobs := by
    rw [List.zip_eq_zip_take_min, List.map_fst_zip (by simp)]
    exact List.take_sublist _ _
  cases hashes with
  | none => exact firsts
  | some requested =>
    refine ((requestedBlobs_sublist requested blobs commitments).map Prod.fst).trans ?_
    simpa [blobHashes, List.map_map, Function.comp_def] using firsts

/-- Without hashes, the answer is every blob of the block. -/
theorem blockBlobs_none {blobs : List Blob} {commitments : List KZGCommitment}
    (paired : blobs.length = commitments.length) :
    blockBlobs blobs commitments none = blobs :=
  List.map_fst_zip (Nat.le_of_eq paired)

/-- Each blob of the answer sits at the place of a commitment whose versioned hash is requested. -/
theorem blockBlobs_versionedHash {blobs : List Blob} {commitments : List KZGCommitment}
    {hashes : Option (List VersionedHash)} {blob : Blob}
    (mem : blob ∈ blockBlobs blobs commitments hashes) :
    ∃ (place : Nat) (commitment : KZGCommitment),
      blobs[place]? = some blob ∧ commitments[place]? = some commitment ∧
      ∀ requested ∈ hashes, kzgCommitmentToVersionedHash commitment ∈ requested := by
  -- The blob comes with a commitment of the block, and with its hash if any was requested.
  obtain ⟨c, zipped, requestedHash⟩ : ∃ c, (blob, c) ∈ blobs.zip commitments ∧
      ∀ requested ∈ hashes, kzgCommitmentToVersionedHash c ∈ requested := by
    cases hashes with
    | none =>
      obtain ⟨⟨b, c⟩, zipped, rfl⟩ := List.mem_map.1 mem
      exact ⟨c, zipped, by simp⟩
    | some requested =>
      obtain ⟨⟨b, hash⟩, kept, rfl⟩ := List.mem_map.1 mem
      have filtered := (Base.eraseDupsBy_sublist _ _).subset kept
      simp only [blobHashes, List.mem_filter, List.mem_map, Prod.mk.injEq,
        List.contains_iff_mem] at filtered
      obtain ⟨⟨⟨b', c⟩, zipped, rfl, rfl⟩, asked⟩ := filtered
      exact ⟨c, zipped, by simpa using asked⟩
  obtain ⟨place, found⟩ := List.mem_iff_getElem?.1 zipped
  rw [List.getElem?_zip_eq_some] at found
  exact ⟨place, c, found.1, found.2, requestedHash⟩

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

/-- A known head is canonical: the ancestor of the head at its own slot is the head. -/
theorem isCanonical_head {config : Config} {store : Store preset fork} {head : Root}
    {block : BeaconBlock preset fork} (headIs : headRoot config store = some head)
    (found : store.blocks[head]? = some block) : isCanonical config store head = true := by
  have walk := Store.getAncestor_of_le (node := ⟨head, .pending⟩) found (UInt64.le_refl _)
  simp [isCanonical, found, headIs, blockAtSlot, walk, Except.toOption]

/-- A block that the store does not hold is not canonical. -/
theorem isCanonical_of_unknown {config : Config} {store : Store preset fork} {root : Root}
    (unknown : store.blocks[root]? = none) : isCanonical config store root = false := by
  simp [isCanonical, unknown]

/-- The answer for a signed header carries that header, and the root of its message. -/
theorem headerOf_ok {config : Config} {store : Store preset fork}
    {header : SignedBeaconBlockHeader} {response : HeaderResponse}
    (computed : headerOf config store header = .ok response) :
    response.header = header ∧
      Serialization.Ssz.SszType.hashTreeRoot header.message = .ok response.root ∧
      response.canonical = isCanonical config store response.root := by
  unfold headerOf at computed
  cases rooted : Serialization.Ssz.SszType.hashTreeRoot header.message with
  | error e => simp [rooted, Except.mapError, bind, Except.bind] at computed
  | ok root =>
    simp [rooted, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
    subst computed
    exact ⟨rfl, rfl, rfl⟩

/-- The header answer of a block has the root of the block. -/
theorem headerOf_blockRoot {config : Config} {store : Store preset fork}
    {block : SignedBeaconBlock preset fork} {header : SignedBeaconBlockHeader}
    {response : HeaderResponse} (signed : block.signedHeader = .ok header)
    (computed : headerOf config store header = .ok response) :
    blockRoot block = .ok response.root := by
  rw [← (signedHeader_root signed).1]
  exact (headerOf_ok computed).2.1

/-- The header answer of the head block says that the block is canonical. -/
theorem headers_canonical_head {config : Config} {store : Store preset fork} {head : Root}
    {block : BeaconBlock preset fork} (headIs : headRoot config store = some head)
    (found : store.blocks[head]? = some block) {header : SignedBeaconBlockHeader}
    {response : HeaderResponse} (computed : headerOf config store header = .ok response)
    (rootIs : response.root = head) : response.canonical = true := by
  rw [(headerOf_ok computed).2.2, rootIs]
  exact isCanonical_head headIs found

/-- Each selected header is one of the input, at the requested slot, with the requested parent. -/
theorem selectHeaders_mem {headers : List SignedBeaconBlockHeader} {slot : Option Slot}
    {parentRoot : Option Root} {header : SignedBeaconBlockHeader}
    (mem : header ∈ selectHeaders headers slot parentRoot) :
    header ∈ headers ∧ (∀ s ∈ slot, header.message.slot = s) ∧
      ∀ parent ∈ parentRoot, header.message.parentRoot = parent := by
  simp only [selectHeaders, List.mem_filter, Bool.and_eq_true] at mem
  obtain ⟨found, slotOk, parentOk⟩ := mem
  refine ⟨found, ?_, ?_⟩
  · rintro s rfl
    exact (by simpa using slotOk : s = header.message.slot).symm
  · rintro parent rfl
    exact (by simpa using parentOk : parent = header.message.parentRoot).symm

/-- Each entry of the headers answer is the answer for a held header that matches the filters. -/
theorem headersOf_mem {config : Config} {store : Store preset fork}
    {headers : List SignedBeaconBlockHeader} {slot : Option Slot} {parentRoot : Option Root}
    {answers : List HeaderResponse}
    (computed : headersOf config store headers slot parentRoot = .ok answers)
    {response : HeaderResponse} (mem : response ∈ answers) :
    ∃ header ∈ headers, headerOf config store header = .ok response ∧
      (∀ s ∈ slot, header.message.slot = s) ∧
      ∀ parent ∈ parentRoot, header.message.parentRoot = parent := by
  unfold headersOf at computed
  cases chosen : headersSlot config store slot parentRoot with
  | error e => simp [chosen, bind, Except.bind] at computed
  | ok slot' =>
    simp only [chosen, bind, Except.bind] at computed
    obtain ⟨header, selected, answered⟩ := mapM_ok_mem computed response mem
    obtain ⟨held, slotOk, parentOk⟩ := selectHeaders_mem selected
    refine ⟨header, held, answered, ?_, parentOk⟩
    rintro s rfl
    have kept : slot' = some s := by
      cases parentRoot <;> simpa [headersSlot] using chosen.symm
    exact slotOk s kept

/-- Without a slot and a parent root, the headers endpoint filters on the slot of the head. -/
theorem headersSlot_default {config : Config} {store : Store preset fork} {head : Root}
    {block : BeaconBlock preset fork} (headIs : headRoot config store = some head)
    (found : store.blocks[head]? = some block) :
    headersSlot config store none none = .ok (some block.slot) := by
  simp [headersSlot, headIs, found]

/-- The selected sidecars are the request, in the order of the input. -/
theorem selectColumns_isColumnsAnswer (sidecars : List (DataColumnSidecar preset fork))
    (indices : Option (List DataAvailability.ColumnIndex)) :
    IsColumnsAnswer sidecars indices (selectColumns sidecars indices) :=
  List.Perm.refl _

/-- Without indices, the selection is every sidecar. -/
theorem selectColumns_none (sidecars : List (DataColumnSidecar preset fork)) :
    selectColumns sidecars none = sidecars := by
  simp [selectColumns]

/-- A sidecar is in an answer exactly when the node holds it and its index is requested. -/
theorem IsColumnsAnswer.mem_iff {sidecars : List (DataColumnSidecar preset fork)}
    {indices : Option (List DataAvailability.ColumnIndex)}
    {answer : List (DataColumnSidecar preset fork)}
    (valid : IsColumnsAnswer sidecars indices answer) {sidecar : DataColumnSidecar preset fork} :
    sidecar ∈ answer ↔ sidecar ∈ sidecars ∧ ∀ requested ∈ indices, sidecar.index ∈ requested := by
  rw [List.Perm.mem_iff valid]
  simp only [selectColumns, List.mem_filter]
  cases indices <;> simp

/-- An empty list of indices requests no sidecar. -/
theorem selectColumns_some_nil (sidecars : List (DataColumnSidecar preset fork)) :
    selectColumns sidecars (some []) = [] := by
  simp [selectColumns]

/-- Before Fulu, the columns endpoint gives the error with code 400. -/
theorem columnsResponse_before_fulu {sidecars : List (DataColumnSidecar preset fork)}
    {indices : Option (List DataAvailability.ColumnIndex)} (early : fork < .fusaka) :
    columnsResponse sidecars indices = .error columnsBeforeFulu := by
  have notFulu : ¬ .fusaka ≤ fork := Nat.not_le.2 early
  unfold columnsResponse
  simp only [notFulu, ↓reduceIte]

/-- An envelope answer is the given envelope, whose message has the root of the stored one. -/
theorem payloadEnvelopeOf_ok {store : Store preset fork} {root : Root}
    {signed answer : SignedExecutionPayloadEnvelope preset fork}
    (computed : payloadEnvelopeOf store root signed = .ok answer) :
    answer = signed ∧ ∃ (gloas : .glamsterdam ≤ fork)
      (stored : ExecutionPayloadEnvelope preset fork) (held : Root),
        (store.payloads gloas)[root]? = some stored ∧
        Serialization.Ssz.SszType.hashTreeRoot stored = .ok held ∧
        Serialization.Ssz.SszType.hashTreeRoot signed.message = .ok held := by
  unfold payloadEnvelopeOf at computed
  split at computed
  · rename_i gloas
    split at computed
    · rename_i stored found
      split at computed
      · rename_i given held givenIs heldIs
        split at computed
        · rename_i same
          cases computed
          exact ⟨rfl, gloas, stored, held, found, heldIs, same ▸ givenIs⟩
        · cases computed
      · cases computed
    · cases computed
  · cases computed

/-- From Gloas, the envelope answer is the given envelope when the store holds its message.

The two messages must have the same root. -/
theorem payloadEnvelopeOf_of_stored {store : Store preset fork} {root : Root}
    {signed : SignedExecutionPayloadEnvelope preset fork} (gloas : .glamsterdam ≤ fork)
    {stored : ExecutionPayloadEnvelope preset fork} {held : Root}
    (found : (store.payloads gloas)[root]? = some stored)
    (storedRoot : Serialization.Ssz.SszType.hashTreeRoot stored = .ok held)
    (givenRoot : Serialization.Ssz.SszType.hashTreeRoot signed.message = .ok held) :
    payloadEnvelopeOf store root signed = .ok signed := by
  simp [payloadEnvelopeOf, gloas, found, storedRoot, givenRoot]

/-- Before Gloas, the envelope endpoint gives the error with code 404. -/
theorem payloadEnvelopeOf_before_gloas {store : Store preset fork} {root : Root}
    {signed : SignedExecutionPayloadEnvelope preset fork} (early : fork < .glamsterdam) :
    payloadEnvelopeOf store root signed = .error envelopeNotFound := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.2 early
  simp [payloadEnvelopeOf, notGloas]

/-- From Gloas, the blinded block endpoint has no SSZ body either: it gives the error with code 400.
-/
theorem blindedBlockSsz_gloas {block : SignedBeaconBlock preset fork}
    (gloas : .glamsterdam ≤ fork) :
    blindedBlockSsz block =
      .error { code := 400, message := "Blocks from Gloas on do not have a blinded form" } := by
  have none : ¬ HasBuilderApi fork := fun range => absurd range.2 (Nat.not_lt.2 gloas)
  have late : ¬ fork < .bellatrix := Nat.not_lt.2
    (Nat.le_trans (by decide : Fork.bellatrix.ctorIdx ≤ Fork.glamsterdam.ctorIdx) gloas)
  simp [blindedBlockSsz, none, late]

/-- An answer of the proposer's envelope endpoint is the cached envelope of the request.

The cache holds it for the slot of the request, and it names the block root of the request.

So a client never gets an envelope of another slot, or one committed to another block. -/
theorem cachedEnvelopeOf_ok {cache : Option (CachedEnvelope preset fork)} {slot : Slot}
    {root : Root} {envelope : ExecutionPayloadEnvelope preset fork}
    (answered : cachedEnvelopeOf cache slot root = .ok envelope) :
    .glamsterdam ≤ fork ∧ cache = some ⟨slot, envelope⟩ ∧ envelope.beaconBlockRoot = root := by
  unfold cachedEnvelopeOf at answered
  split at answered
  · rename_i gloas
    split at answered
    · rename_i cached
      split at answered
      · rename_i hit
        cases answered
        obtain ⟨sameSlot, sameRoot⟩ := hit
        cases cached
        simp_all
      · cases answered
    · cases answered
  · cases answered

/-- From Gloas, a cached envelope of the slot and the block root of the request is the answer. -/
theorem cachedEnvelopeOf_of_cached {slot : Slot} {root : Root}
    {envelope : ExecutionPayloadEnvelope preset fork} (gloas : .glamsterdam ≤ fork)
    (named : envelope.beaconBlockRoot = root) :
    cachedEnvelopeOf (some ⟨slot, envelope⟩) slot root = .ok envelope := by
  simp [cachedEnvelopeOf, gloas, named]

/-- Every other answer of the proposer's envelope endpoint is the error with code 404. -/
theorem cachedEnvelopeOf_error {cache : Option (CachedEnvelope preset fork)} {slot : Slot}
    {root : Root} {error : ErrorMessage}
    (failed : cachedEnvelopeOf cache slot root = .error error) :
    error = envelopeNotFound := by
  unfold cachedEnvelopeOf at failed
  split at failed
  · split at failed
    · split at failed <;> cases failed
      rfl
    · cases failed
      rfl
  · cases failed
    rfl

end EthLib.Consensus.BeaconApi
