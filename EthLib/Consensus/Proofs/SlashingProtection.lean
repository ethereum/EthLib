module

public import EthLib.Base.Except
public import EthLib.Consensus.SlashingProtection
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonHex
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws
public import Std.Data.TreeMap.Lemmas

/-!
# Proofs: slashing protection

A signer checks each message against its record, and then records it.

Such a signer signs a slashable pair only when two messages share a signing root.

The statement holds for any function that gives the signing root of a message.

Two votes that Casper FFG forbids together, among those signed, have equal signing roots.

So do two block headers of one slot.

The two headers of a valid proposer slashing, both signed, are different with one signing root.

Since slashable messages are different messages, each such pair is a collision of signing roots.

No signed vote is slashable with a vote of the starting file, as a record sees it.

A file may keep only the latest messages of a key, and drop the older ones.

Each block that a signer signs from it is after every older block.

So no valid proposer slashing pairs an older block with a signed block.

No vote that it signs is slashable with an older vote.

Each of these needs the file to keep one or more such messages of the key.

An import keeps only the greatest slot and epochs of each key.

After any sequence of imports, an accepted message meets every condition of each imported file.

An interchange file reads back as itself from the document that writes it.
-/

@[expose] public section

namespace EthLib.Consensus

open Lean Base Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork}

/-- Two errors with one code come from one constructor. -/
theorem SlashingProtectionError.code_injective (e₁ e₂ : SlashingProtectionError)
    (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code is one more than the index of its constructor.
  have back : ∀ e : SlashingProtectionError, e.code.toNat - 1 = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

/-! ## The conditions -/

/-- The second condition holds exactly when the slot is after the least one, or a repeat. -/
theorem checkBlockSlot_eq_ok_iff {blocks : List SignedBlockRecord} {slot : Slot}
    {signingRoot : Root} :
    checkBlockSlot blocks slot signingRoot = .ok () ↔
      ∀ minimum, minBlockSlot blocks = some minimum →
        minimum < slot ∨ isRepeatBlock blocks slot signingRoot = true := by
  unfold checkBlockSlot
  split <;> simp_all [ensure_ok_iff]

/-- The fourth condition holds exactly when the source epoch is at least the least one. -/
theorem checkSourceEpoch_eq_ok_iff {attestations : List SignedAttestationRecord}
    {sourceEpoch : Epoch} :
    checkSourceEpoch attestations sourceEpoch = .ok () ↔
      ∀ minimum, minSourceEpoch attestations = some minimum → minimum ≤ sourceEpoch := by
  unfold checkSourceEpoch
  split <;> simp_all [ensure_ok_iff]

/-- The fifth condition holds exactly when the target epoch is after the least one, or a repeat. -/
theorem checkTargetEpoch_eq_ok_iff {attestations : List SignedAttestationRecord}
    {sourceEpoch targetEpoch : Epoch} {signingRoot : Root} :
    checkTargetEpoch attestations sourceEpoch targetEpoch signingRoot = .ok () ↔
      ∀ minimum, minTargetEpoch attestations = some minimum →
        minimum < targetEpoch ∨
          isRepeatAttestation attestations sourceEpoch targetEpoch signingRoot = true := by
  unfold checkTargetEpoch
  split <;> simp_all [ensure_ok_iff]

/-- A block may be signed exactly when it meets the first two conditions.

No recorded block of its slot has another signing root, or none.

Its slot is after the least recorded slot, or some record has its slot and signing root. -/
theorem checkBlockSigning_eq_ok_iff {blocks : List SignedBlockRecord} {slot : Slot}
    {signingRoot : Root} :
    checkBlockSigning blocks slot signingRoot = .ok () ↔
      (∀ block ∈ blocks, block.conflictsWith slot signingRoot = false) ∧
      ∀ minimum, minBlockSlot blocks = some minimum →
        minimum < slot ∨ isRepeatBlock blocks slot signingRoot = true := by
  rw [checkBlockSigning, bind_unit_ok_iff, ensure_ok_iff, checkBlockSlot_eq_ok_iff]

/-- A vote may be signed exactly when it meets the last three conditions.

No recorded vote is slashable with it, as a record sees it.

Its source epoch is at least the least recorded one.

Its target epoch is after the least one, or some record has its epochs and signing root. -/
theorem checkAttestationSigning_eq_ok_iff {attestations : List SignedAttestationRecord}
    {sourceEpoch targetEpoch : Epoch} {signingRoot : Root} :
    checkAttestationSigning attestations sourceEpoch targetEpoch signingRoot = .ok () ↔
      (∀ attestation ∈ attestations,
        attestation.isSlashableWith sourceEpoch targetEpoch signingRoot = false) ∧
      (∀ minimum, minSourceEpoch attestations = some minimum → minimum ≤ sourceEpoch) ∧
      ∀ minimum, minTargetEpoch attestations = some minimum →
        minimum < targetEpoch ∨
          isRepeatAttestation attestations sourceEpoch targetEpoch signingRoot = true := by
  rw [checkAttestationSigning, bind_unit_ok_iff, ensure_ok_iff, bind_unit_ok_iff,
    checkSourceEpoch_eq_ok_iff, checkTargetEpoch_eq_ok_iff]

/-! ## Reading back the file -/

namespace Interchange

/-- A 64-bit integer that the file writes reads back as itself. -/
theorem readUInt64_uint64Json (path : String) (value : UInt64) :
    readUInt64 path (uint64Json value) = .ok value := by
  simp only [readUInt64, uint64Json, Serialization.Ssz.decimal, readString, bind, Except.bind]
  rw [Serialization.Ssz.readNat_str]
  simp [value.toNat_lt]

/-- Bytes that the file writes read back as themselves. -/
theorem readBytes_bytesJson (path : String) {size : Nat} (bytes : Vector UInt8 size) :
    readBytes path size (bytesJson bytes) = .ok bytes := by
  simp [readBytes, bytesJson, readString, bind, Except.bind, Serialization.Ssz.ofHex_toHex]

/-- The signing root of a record that the file writes reads back as itself.

A record without a root is written without the name, and reads back as having none. -/
theorem readSigningRoot_signingRootFields (path : String) (base : List (String × Json))
    (root : Option Root) (named : ∀ pair ∈ base, pair.1 ≠ "signing_root")
    (distinct : base.Pairwise fun a b => a.1 ≠ b.1) :
    readSigningRoot path (Json.mkObj (base ++ signingRootFields root)) = .ok root := by
  cases root with
  | none =>
    have absent := Serialization.Ssz.getObjVal?_mkObj_of_not_mem
      (pairs := base ++ signingRootFields none) (name := "signing_root") (by
        simp only [signingRootFields, List.append_nil, List.mem_map, not_exists, not_and]
        exact fun pair mem eq => named pair mem eq)
    simp [readSigningRoot, absent]
  | some root =>
    have found := Serialization.Ssz.getObjVal?_mkObj
      (pairs := base ++ signingRootFields (some root)) (name := "signing_root")
      (value := bytesJson root) (by
        simp only [signingRootFields, List.pairwise_append, distinct, List.mem_singleton,
          forall_eq, ne_eq, List.pairwise_singleton, true_and]
        exact fun a mem => named a mem) (by simp [signingRootFields])
    simp [readSigningRoot, found, readBytes_bytesJson, bind, Except.bind, pure, Except.pure]

/-- A block that the file writes reads back as itself. -/
theorem readBlock_blockJson (path : String) (block : SignedBlockRecord) :
    readBlock path (blockJson block) = .ok block := by
  have slot := Serialization.Ssz.getObjVal?_mkObj
    (pairs := [("slot", uint64Json block.slot)] ++ signingRootFields block.signingRoot)
    (name := "slot") (value := uint64Json block.slot)
    (by cases block.signingRoot <;> simp [signingRootFields]) (by simp)
  have root := readSigningRoot_signingRootFields path [("slot", uint64Json block.slot)]
    block.signingRoot (by simp) (by simp)
  simp only [readBlock, blockJson, field, slot, readUInt64_uint64Json, root, bind, Except.bind,
    pure, Except.pure]

/-- A vote that the file writes reads back as itself. -/
theorem readAttestation_attestationJson (path : String) (attestation : SignedAttestationRecord) :
    readAttestation path (attestationJson attestation) = .ok attestation := by
  have distinct : ∀ root : Option Root, ([("source_epoch", uint64Json attestation.sourceEpoch),
      ("target_epoch", uint64Json attestation.targetEpoch)] ++ signingRootFields root).Pairwise
        fun a b => a.1 ≠ b.1 := by
    intro root
    cases root <;> simp [signingRootFields]
  have source := Serialization.Ssz.getObjVal?_mkObj
    (pairs := [("source_epoch", uint64Json attestation.sourceEpoch),
      ("target_epoch", uint64Json attestation.targetEpoch)] ++
        signingRootFields attestation.signingRoot)
    (name := "source_epoch") (value := uint64Json attestation.sourceEpoch)
    (distinct _) (by simp)
  have target := Serialization.Ssz.getObjVal?_mkObj
    (pairs := [("source_epoch", uint64Json attestation.sourceEpoch),
      ("target_epoch", uint64Json attestation.targetEpoch)] ++
        signingRootFields attestation.signingRoot)
    (name := "target_epoch") (value := uint64Json attestation.targetEpoch)
    (distinct _) (by simp)
  have root := readSigningRoot_signingRootFields path
    [("source_epoch", uint64Json attestation.sourceEpoch),
      ("target_epoch", uint64Json attestation.targetEpoch)]
    attestation.signingRoot (by simp) (by simp)
  simp only [readAttestation, attestationJson, field, source, target, readUInt64_uint64Json, root,
    bind, Except.bind, pure, Except.pure]

/-- An array that the file writes, from elements that each read back, reads back as the list. -/
theorem readArray_arr {α : Type} (path : String)
    (read : String → Json → Except SlashingProtectionError α) (write : α → Json)
    (back : ∀ path x, read path (write x) = .ok x) (xs : List α) :
    readArray path read (.arr (xs.map write).toArray) = .ok xs := by
  unfold readArray
  -- Count the positions from any start, as the recursion on the list does.
  suffices ∀ n, (((xs.map write).zipIdx n).mapM fun (element, index) =>
      read s!"{path}[{index}]" element) = .ok xs from this 0
  intro n
  induction xs generalizing n with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.mapM_cons, back, ih, bind, Except.bind, pure,
      Except.pure]

/-- What one key signed, as the file writes it, reads back as itself. -/
theorem readEntry_entryJson (path : String) (entry : InterchangeEntry) :
    readEntry path (entryJson entry) = .ok entry := by
  have distinct : ([("pubkey", bytesJson entry.pubkey),
      ("signed_blocks", Json.arr (entry.signedBlocks.map blockJson).toArray),
      ("signed_attestations", Json.arr (entry.signedAttestations.map attestationJson).toArray)] :
        List (String × Json)).Pairwise fun a b => a.1 ≠ b.1 := by simp
  have pubkey := Serialization.Ssz.getObjVal?_mkObj distinct
    (name := "pubkey") (value := bytesJson entry.pubkey) (by simp)
  have blocks := Serialization.Ssz.getObjVal?_mkObj distinct (name := "signed_blocks")
    (value := Json.arr (entry.signedBlocks.map blockJson).toArray) (by simp)
  have attestations := Serialization.Ssz.getObjVal?_mkObj distinct (name := "signed_attestations")
    (value := Json.arr (entry.signedAttestations.map attestationJson).toArray) (by simp)
  simp only [readEntry, entryJson, field, pubkey, blocks, attestations, readBytes_bytesJson,
    readArray_arr _ readBlock blockJson readBlock_blockJson,
    readArray_arr _ readAttestation attestationJson readAttestation_attestationJson, bind,
    Except.bind, pure, Except.pure]

/-- An interchange file reads back as itself from the document that writes it. -/
theorem ofJson_toJson (interchange : Interchange) :
    ofJson interchange.toJson = .ok interchange := by
  have metadataDistinct : ([("interchange_format_version", Json.str INTERCHANGE_FORMAT_VERSION),
      ("genesis_validators_root", bytesJson interchange.genesisValidatorsRoot)] :
        List (String × Json)).Pairwise fun a b => a.1 ≠ b.1 := by simp
  have version := Serialization.Ssz.getObjVal?_mkObj metadataDistinct
    (name := "interchange_format_version") (value := Json.str INTERCHANGE_FORMAT_VERSION)
    (by simp)
  have root := Serialization.Ssz.getObjVal?_mkObj metadataDistinct
    (name := "genesis_validators_root") (value := bytesJson interchange.genesisValidatorsRoot)
    (by simp)
  have distinct : ([("metadata", Json.mkObj [
      ("interchange_format_version", Json.str INTERCHANGE_FORMAT_VERSION),
      ("genesis_validators_root", bytesJson interchange.genesisValidatorsRoot)]),
      ("data", Json.arr (interchange.data.map entryJson).toArray)] :
        List (String × Json)).Pairwise fun a b => a.1 ≠ b.1 := by simp
  have metadata := Serialization.Ssz.getObjVal?_mkObj distinct (name := "metadata")
    (value := Json.mkObj [
      ("interchange_format_version", Json.str INTERCHANGE_FORMAT_VERSION),
      ("genesis_validators_root", bytesJson interchange.genesisValidatorsRoot)]) (by simp)
  have data := Serialization.Ssz.getObjVal?_mkObj distinct (name := "data")
    (value := Json.arr (interchange.data.map entryJson).toArray) (by simp)
  simp only [ofJson, toJson, field, metadata, data, version, root, readString,
    readBytes_bytesJson, readArray_arr _ readEntry entryJson readEntry_entryJson,
    bind, Except.bind, pure, Except.pure]
  -- The version is the one of the format, and the rebuilt file is the file.
  simp

end Interchange

/-! ## Records -/

/-- Recording a vote of a key adds it after the votes of that key. -/
theorem attestationsOf_recordAttestation (interchange : Interchange) (pubkey : BLSPubkey)
    (sourceEpoch targetEpoch : Epoch) (signingRoot : Root) :
    (interchange.recordAttestation pubkey sourceEpoch targetEpoch signingRoot).attestationsOf
        pubkey =
      interchange.attestationsOf pubkey ++ [⟨sourceEpoch, targetEpoch, some signingRoot⟩] := by
  simp [Interchange.attestationsOf, Interchange.recordAttestation, List.filter_append]

/-- Recording a block of a key adds it after the blocks of that key. -/
theorem blocksOf_recordBlock (interchange : Interchange) (pubkey : BLSPubkey) (slot : Slot)
    (signingRoot : Root) :
    (interchange.recordBlock pubkey slot signingRoot).blocksOf pubkey =
      interchange.blocksOf pubkey ++ [⟨slot, some signingRoot⟩] := by
  simp [Interchange.blocksOf, Interchange.recordBlock, List.filter_append]

/-- A vote is a vote of a key exactly when an entry of that key holds it. -/
theorem mem_attestationsOf {interchange : Interchange} {pubkey : BLSPubkey}
    {attestation : SignedAttestationRecord} :
    attestation ∈ interchange.attestationsOf pubkey ↔
      ∃ entry ∈ interchange.data, entry.pubkey = pubkey ∧
        attestation ∈ entry.signedAttestations := by
  simp [Interchange.attestationsOf, and_assoc]

/-- A block is a block of a key exactly when an entry of that key holds it. -/
theorem mem_blocksOf {interchange : Interchange} {pubkey : BLSPubkey}
    {block : SignedBlockRecord} :
    block ∈ interchange.blocksOf pubkey ↔
      ∃ entry ∈ interchange.data, entry.pubkey = pubkey ∧ block ∈ entry.signedBlocks := by
  simp [Interchange.blocksOf, and_assoc]

/-! ## A signer's history -/

/-- A signer of votes: each vote of a key is checked against the record, then recorded.

A function gives the signing root of a vote, so the statements below hold for any one. -/
def signAttestations (signingRootOf : AttestationData → Root) (pubkey : BLSPubkey) :
    Interchange → List AttestationData → Except SlashingProtectionError Interchange
  | interchange, [] => .ok interchange
  | interchange, data :: rest => do
    interchange.checkAttestation pubkey data.source.epoch data.target.epoch (signingRootOf data)
    signAttestations signingRootOf pubkey
      (interchange.recordAttestation pubkey data.source.epoch data.target.epoch
        (signingRootOf data)) rest

/-- A signer of blocks: each block header of a key is checked against the record, then recorded.

A function gives the signing root of a header, so the statements below hold for any one. -/
def signBlocks (signingRootOf : BeaconBlockHeader → Root) (pubkey : BLSPubkey) :
    Interchange → List BeaconBlockHeader → Except SlashingProtectionError Interchange
  | interchange, [] => .ok interchange
  | interchange, header :: rest => do
    interchange.checkBlock pubkey header.slot (signingRootOf header)
    signBlocks signingRootOf pubkey
      (interchange.recordBlock pubkey header.slot (signingRootOf header)) rest

/-- Each vote that a signer signs passed its check against a record that holds its starting one. -/
theorem checked_of_signAttestations {signingRootOf : AttestationData → Root}
    {pubkey : BLSPubkey} {start finish : Interchange} {votes : List AttestationData}
    (signed : signAttestations signingRootOf pubkey start votes = .ok finish) :
    ∀ data ∈ votes, ∃ record : Interchange,
      (∀ attestation ∈ start.attestationsOf pubkey, attestation ∈ record.attestationsOf pubkey) ∧
      record.checkAttestation pubkey data.source.epoch data.target.epoch (signingRootOf data) =
        .ok () := by
  induction votes generalizing start with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨checked, later⟩ := bind_unit_ok_iff.mp signed
    intro data member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨start, fun _ kept => kept, checked⟩
    · obtain ⟨record, holds, check⟩ := ih later data member
      refine ⟨record, fun attestation kept => holds attestation ?_, check⟩
      rw [attestationsOf_recordAttestation]
      exact List.mem_append_left _ kept

/-- Each block that a signer signs passed its check against a record that holds its starting one. -/
theorem checked_of_signBlocks {signingRootOf : BeaconBlockHeader → Root} {pubkey : BLSPubkey}
    {start finish : Interchange} {headers : List BeaconBlockHeader}
    (signed : signBlocks signingRootOf pubkey start headers = .ok finish) :
    ∀ header ∈ headers, ∃ record : Interchange,
      (∀ block ∈ start.blocksOf pubkey, block ∈ record.blocksOf pubkey) ∧
      record.checkBlock pubkey header.slot (signingRootOf header) = .ok () := by
  induction headers generalizing start with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨checked, later⟩ := bind_unit_ok_iff.mp signed
    intro header member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨start, fun _ kept => kept, checked⟩
    · obtain ⟨record, holds, check⟩ := ih later header member
      refine ⟨record, fun block kept => holds block ?_, check⟩
      rw [blocksOf_recordBlock]
      exact List.mem_append_left _ kept

/-- Two votes slashable either way round have one signing root, if the record check passed.

The check compares the record of the earlier vote with the later vote. -/
theorem signingRoot_eq_of_isSlashableWith_eq_false {signingRootOf : AttestationData → Root}
    {earlier later : AttestationData}
    (passed : (⟨earlier.source.epoch, earlier.target.epoch, some (signingRootOf earlier)⟩ :
      SignedAttestationRecord).isSlashableWith later.source.epoch later.target.epoch
        (signingRootOf later) = false)
    (slashable : isSlashableAttestationData earlier later = true ∨
      isSlashableAttestationData later earlier = true) :
    signingRootOf earlier = signingRootOf later := by
  apply Classical.byContradiction
  intro distinct
  simp only [SignedAttestationRecord.isSlashableWith, Bool.or_eq_false_iff] at passed
  obtain ⟨⟨double, around⟩, inside⟩ := passed
  simp only [isSlashableAttestationData, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, decide_eq_true_eq] at slashable
  rcases slashable with (⟨_, same⟩ | ⟨below, above⟩) | (⟨_, same⟩ | ⟨below, above⟩)
  · simp [same, distinct] at double
  · simp [below, above] at inside
  · simp [same, distinct] at double
  · simp [below, above] at around

/-- Two signed votes that Casper FFG forbids together have the same signing root.

So such a pair is a collision of the signing root, since the two votes are different. -/
theorem signingRoot_eq_of_signAttestations {signingRootOf : AttestationData → Root}
    {pubkey : BLSPubkey} {start finish : Interchange} {votes : List AttestationData}
    (signed : signAttestations signingRootOf pubkey start votes = .ok finish)
    {data1 data2 : AttestationData} (member1 : data1 ∈ votes) (member2 : data2 ∈ votes)
    (slashable : isSlashableAttestationData data1 data2 = true) :
    signingRootOf data1 = signingRootOf data2 := by
  induction votes generalizing start with
  | nil => simp at member1
  | cons first rest ih =>
    obtain ⟨_, later⟩ := bind_unit_ok_iff.mp signed
    -- A later vote passed its check against a record that holds the first vote.
    have against : ∀ data ∈ rest,
        (⟨first.source.epoch, first.target.epoch, some (signingRootOf first)⟩ :
          SignedAttestationRecord).isSlashableWith data.source.epoch data.target.epoch
            (signingRootOf data) = false := by
      intro data member
      obtain ⟨record, holds, check⟩ := checked_of_signAttestations later data member
      have kept := holds _ (by
        rw [attestationsOf_recordAttestation]
        exact List.mem_append_right _ (List.mem_singleton_self _))
      exact (checkAttestationSigning_eq_ok_iff.mp check).1 _ kept
    rcases List.mem_cons.mp member1 with head1 | inRest1 <;>
      rcases List.mem_cons.mp member2 with head2 | inRest2
    · rw [head1, head2]
    · subst head1
      exact signingRoot_eq_of_isSlashableWith_eq_false (against data2 inRest2) (.inl slashable)
    · subst head2
      exact (signingRoot_eq_of_isSlashableWith_eq_false (against data1 inRest1)
        (.inr slashable)).symm
    · exact ih later inRest1 inRest2

/-- Each vote that a signer signs is not slashable with a vote of the file it started from.

The comparison is the one the record allows: by epochs, and by signing root for a double vote. -/
theorem isSlashableWith_eq_false_of_signAttestations {signingRootOf : AttestationData → Root}
    {pubkey : BLSPubkey} {start finish : Interchange} {votes : List AttestationData}
    (signed : signAttestations signingRootOf pubkey start votes = .ok finish)
    {attestation : SignedAttestationRecord} (imported : attestation ∈ start.attestationsOf pubkey)
    {data : AttestationData} (member : data ∈ votes) :
    attestation.isSlashableWith data.source.epoch data.target.epoch (signingRootOf data) =
      false := by
  obtain ⟨record, holds, check⟩ := checked_of_signAttestations signed data member
  exact (checkAttestationSigning_eq_ok_iff.mp check).1 _ (holds _ imported)

/-- Blocks that a signer signs from a record never share a slot with another signing root.

Two signed block headers of one slot have the same signing root. -/
theorem signingRoot_eq_of_signBlocks {signingRootOf : BeaconBlockHeader → Root}
    {pubkey : BLSPubkey} {start finish : Interchange} {headers : List BeaconBlockHeader}
    (signed : signBlocks signingRootOf pubkey start headers = .ok finish)
    {header1 header2 : BeaconBlockHeader} (member1 : header1 ∈ headers)
    (member2 : header2 ∈ headers) (sameSlot : header1.slot = header2.slot) :
    signingRootOf header1 = signingRootOf header2 := by
  induction headers generalizing start with
  | nil => simp at member1
  | cons first rest ih =>
    obtain ⟨_, later⟩ := bind_unit_ok_iff.mp signed
    -- A later block passed its check against a record that holds the first block.
    have against : ∀ header ∈ rest, header.slot = first.slot →
        signingRootOf first = signingRootOf header := by
      intro header member same
      obtain ⟨record, holds, check⟩ := checked_of_signBlocks later header member
      have kept := holds _ (by
        rw [blocksOf_recordBlock]
        exact List.mem_append_right _ (List.mem_singleton_self _))
      have passed := (checkBlockSigning_eq_ok_iff.mp check).1 _ kept
      simpa [SignedBlockRecord.conflictsWith, same] using passed
    rcases List.mem_cons.mp member1 with head1 | inRest1 <;>
      rcases List.mem_cons.mp member2 with head2 | inRest2
    · rw [head1, head2]
    · subst head1
      exact against header2 inRest2 sameSlot.symm
    · subst head2
      exact (against header1 inRest1 sameSlot).symm
    · exact ih later inRest1 inRest2

/-- If such a signer signed both headers of a valid proposer slashing, they differ and share a root.

So the pair is a collision of the signing root. -/
theorem signingRoot_eq_of_processProposerSlashing {signingRootOf : BeaconBlockHeader → Root}
    {pubkey : BLSPubkey} {start finish : Interchange} {headers : List BeaconBlockHeader}
    (signed : signBlocks signingRootOf pubkey start headers = .ok finish) {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (valid : processProposerSlashing config checks state slashing = .ok after)
    (member1 : slashing.signedHeader1.message ∈ headers)
    (member2 : slashing.signedHeader2.message ∈ headers) :
    slashing.signedHeader1.message ≠ slashing.signedHeader2.message ∧
      signingRootOf slashing.signedHeader1.message =
        signingRootOf slashing.signedHeader2.message := by
  obtain ⟨sameSlot, -, distinct, -⟩ := processProposerSlashing_checks valid
  exact ⟨distinct, signingRoot_eq_of_signBlocks signed member1 member2 sameSlot⟩

/-! ## A file that drops older messages -/

/-- The least value of a field over a list that is not empty is the field of one of its members. -/
private theorem exists_min?_map_eq {α : Type} {xs : List α} (field : α → UInt64)
    (nonempty : xs ≠ []) : ∃ x ∈ xs, (xs.map field).min? = some (field x) := by
  cases least : (xs.map field).min? with
  | none => simp_all
  | some value =>
    obtain ⟨x, member, rfl⟩ := List.mem_map.mp (List.min?_mem least)
    exact ⟨x, member, rfl⟩

/-- If each recorded block is after a slot, so is a block that passes the second condition.

The record holds one or more blocks. -/
theorem lt_slot_of_checkBlockSlot {blocks : List SignedBlockRecord} {old slot : Slot}
    {signingRoot : Root} (nonempty : blocks ≠ []) (older : ∀ block ∈ blocks, old < block.slot)
    (passed : checkBlockSlot blocks slot signingRoot = .ok ()) : old < slot := by
  obtain ⟨least, kept, isLeast⟩ := exists_min?_map_eq SignedBlockRecord.slot nonempty
  rcases checkBlockSlot_eq_ok_iff.mp passed _ isLeast with after | repeated
  · exact UInt64.lt_trans (older least kept) after
  · -- A repeat has the slot of a recorded block.
    obtain ⟨block, kept, same⟩ := List.any_eq_true.mp repeated
    simp only [Bool.and_eq_true, beq_iff_eq] at same
    exact same.1 ▸ older block kept

/-- If each recorded source is at least an epoch, so is a source that passes the fourth condition.

The record holds one or more votes. -/
theorem le_sourceEpoch_of_checkSourceEpoch {attestations : List SignedAttestationRecord}
    {old sourceEpoch : Epoch} (nonempty : attestations ≠ [])
    (older : ∀ attestation ∈ attestations, old ≤ attestation.sourceEpoch)
    (passed : checkSourceEpoch attestations sourceEpoch = .ok ()) : old ≤ sourceEpoch := by
  obtain ⟨least, kept, isLeast⟩ :=
    exists_min?_map_eq SignedAttestationRecord.sourceEpoch nonempty
  exact UInt64.le_trans (older least kept) (checkSourceEpoch_eq_ok_iff.mp passed _ isLeast)

/-- If each recorded target is after an epoch, so is a target that passes the fifth condition.

The record holds one or more votes. -/
theorem lt_targetEpoch_of_checkTargetEpoch {attestations : List SignedAttestationRecord}
    {old sourceEpoch targetEpoch : Epoch} {signingRoot : Root} (nonempty : attestations ≠ [])
    (older : ∀ attestation ∈ attestations, old < attestation.targetEpoch)
    (passed : checkTargetEpoch attestations sourceEpoch targetEpoch signingRoot = .ok ()) :
    old < targetEpoch := by
  obtain ⟨least, kept, isLeast⟩ :=
    exists_min?_map_eq SignedAttestationRecord.targetEpoch nonempty
  rcases checkTargetEpoch_eq_ok_iff.mp passed _ isLeast with after | repeated
  · exact UInt64.lt_trans (older least kept) after
  · -- A repeat has the target of a recorded vote.
    obtain ⟨attestation, kept, same⟩ := List.any_eq_true.mp repeated
    simp only [Bool.and_eq_true, beq_iff_eq] at same
    exact same.1.2 ▸ older attestation kept

/-- A vote is not slashable with a newer vote, in either order.

The newer vote has a source at least, and a target after, those of the older one. -/
theorem isSlashableAttestationData_eq_false_of_le_of_lt {old data : AttestationData}
    (source : old.source.epoch ≤ data.source.epoch)
    (target : old.target.epoch < data.target.epoch) :
    isSlashableAttestationData old data = false ∧ isSlashableAttestationData data old = false := by
  have notAbove : ¬data.source.epoch < old.source.epoch := UInt64.not_lt.mpr source
  have notBelow : ¬data.target.epoch < old.target.epoch :=
    UInt64.not_lt.mpr (UInt64.le_of_lt target)
  simp [isSlashableAttestationData, UInt64.ne_of_lt target, (UInt64.ne_of_lt target).symm,
    notAbove, notBelow]

/-- If each block of the starting file is after a slot, so is each block that a signer signs.

The file holds one or more blocks of the key. -/
theorem lt_slot_of_signBlocks {signingRootOf : BeaconBlockHeader → Root} {pubkey : BLSPubkey}
    {start finish : Interchange} {headers : List BeaconBlockHeader}
    (signed : signBlocks signingRootOf pubkey start headers = .ok finish)
    (nonempty : start.blocksOf pubkey ≠ []) {old : Slot}
    (older : ∀ block ∈ start.blocksOf pubkey, old < block.slot) {header : BeaconBlockHeader}
    (member : header ∈ headers) : old < header.slot := by
  induction headers generalizing start with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨checked, later⟩ := bind_unit_ok_iff.mp signed
    have after := lt_slot_of_checkBlockSlot nonempty older (bind_unit_ok_iff.mp checked).2
    rcases List.mem_cons.mp member with rfl | inRest
    · exact after
    · -- The block just signed is after the old slot too, so the grown record keeps the bound.
      refine ih later (by simp [blocksOf_recordBlock]) ?_ inRest
      intro block kept
      rw [blocksOf_recordBlock, List.mem_append, List.mem_singleton] at kept
      rcases kept with kept | rfl
      · exact older block kept
      · exact after

/-- No valid proposer slashing pairs a signed header with a header before each block of the file.

The file holds one or more blocks of the key.

The signed header may be the first or the second header of the slashing.

The two headers of a valid proposer slashing have one slot. -/
theorem processProposerSlashing_ne_ok_of_signBlocks {signingRootOf : BeaconBlockHeader → Root}
    {pubkey : BLSPubkey} {start finish : Interchange} {headers : List BeaconBlockHeader}
    (signed : signBlocks signingRootOf pubkey start headers = .ok finish)
    (nonempty : start.blocksOf pubkey ≠ []) {old : BeaconBlockHeader}
    (older : ∀ block ∈ start.blocksOf pubkey, old.slot < block.slot) {header : BeaconBlockHeader}
    (member : header ∈ headers) {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (pair : slashing.signedHeader1.message = old ∧ slashing.signedHeader2.message = header ∨
      slashing.signedHeader1.message = header ∧ slashing.signedHeader2.message = old) :
    processProposerSlashing config checks state slashing ≠ .ok after := by
  intro valid
  have sameSlot := (processProposerSlashing_checks valid).1
  have before := UInt64.ne_of_lt (lt_slot_of_signBlocks signed nonempty older member)
  rcases pair with ⟨first, second⟩ | ⟨first, second⟩
  · exact before (by rw [← first, ← second, sameSlot])
  · exact before (by rw [← first, ← second, sameSlot])

/-- No vote that a signer signs is slashable with a vote older than each vote of its starting file.

The file holds one or more votes of the key.

An older vote has a source at most, and a target before, those of each vote of the file. -/
theorem isSlashableAttestationData_eq_false_of_signAttestations
    {signingRootOf : AttestationData → Root} {pubkey : BLSPubkey} {start finish : Interchange}
    {votes : List AttestationData}
    (signed : signAttestations signingRootOf pubkey start votes = .ok finish)
    (nonempty : start.attestationsOf pubkey ≠ []) {old : AttestationData}
    (older : ∀ attestation ∈ start.attestationsOf pubkey,
      old.source.epoch ≤ attestation.sourceEpoch ∧ old.target.epoch < attestation.targetEpoch)
    {data : AttestationData} (member : data ∈ votes) :
    isSlashableAttestationData old data = false ∧ isSlashableAttestationData data old = false := by
  induction votes generalizing start with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨checked, later⟩ := bind_unit_ok_iff.mp signed
    obtain ⟨-, epochsChecked⟩ := bind_unit_ok_iff.mp checked
    obtain ⟨sourceChecked, targetChecked⟩ := bind_unit_ok_iff.mp epochsChecked
    have above := le_sourceEpoch_of_checkSourceEpoch nonempty
      (fun attestation kept => (older attestation kept).1) sourceChecked
    have after := lt_targetEpoch_of_checkTargetEpoch nonempty
      (fun attestation kept => (older attestation kept).2) targetChecked
    rcases List.mem_cons.mp member with rfl | inRest
    · exact isSlashableAttestationData_eq_false_of_le_of_lt above after
    · -- The vote just signed is newer than the old one too, so the grown record keeps the bound.
      refine ih later (by simp [attestationsOf_recordAttestation]) ?_ inRest
      intro attestation kept
      rw [attestationsOf_recordAttestation, List.mem_append, List.mem_singleton] at kept
      rcases kept with kept | rfl
      · exact older attestation kept
      · exact ⟨above, after⟩

/-! ## Imports with the minimal strategy -/

/-- A slot limit covers a slot when it exists and is at least that slot. -/
private abbrev CoversSlot (limit : Option Slot) (slot : Slot) : Prop :=
  ∃ maximum, limit = some maximum ∧ slot ≤ maximum

/-- Epoch limits cover a vote when they exist and are at least its source and its target. -/
private abbrev CoversEpochs (limits : Option (Epoch × Epoch))
    (attestation : SignedAttestationRecord) : Prop :=
  ∃ source target, limits = some (source, target) ∧
    attestation.sourceEpoch ≤ source ∧ attestation.targetEpoch ≤ target

/-- A property that every step of a fold keeps holds at its end. -/
private theorem foldl_keeps {α β : Type} {f : β → α → β} {P : β → Prop}
    (keep : ∀ b a, P b → P (f b a)) : ∀ (xs : List α) (b : β), P b → P (xs.foldl f b)
  | [], _, holds => holds
  | x :: xs, b, holds => foldl_keeps keep xs (f b x) (keep b x holds)

/-- A property that every step keeps, and that one step makes, holds at the end of a fold. -/
private theorem foldl_makes {α β : Type} {f : β → α → β} {P : β → Prop}
    (keep : ∀ b a, P b → P (f b a)) {x : α} (make : ∀ b, P (f b x)) :
    ∀ (xs : List α) (b : β), x ∈ xs → P (xs.foldl f b)
  | [], _, member => nomatch member
  | y :: xs, b, member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact foldl_keeps keep xs _ (make b)
    · exact foldl_makes keep make xs (f b y) member

/-- Raising a slot limit keeps every slot it covers, and covers the new block. -/
private theorem coversSlot_raiseSlotLimit {limit : Option Slot} {block : SignedBlockRecord} :
    (∀ slot, CoversSlot limit slot → CoversSlot (raiseSlotLimit limit block) slot) ∧
      CoversSlot (raiseSlotLimit limit block) block.slot := by
  cases limit with
  | none =>
    refine ⟨?_, block.slot, rfl, UInt64.le_refl _⟩
    rintro _ ⟨_, found, _⟩
    cases found
  | some maximum =>
    refine ⟨fun slot ⟨_, same, below⟩ => ?_, _, rfl, Std.right_le_max⟩
    cases same
    exact ⟨_, rfl, UInt64.le_trans below Std.left_le_max⟩

/-- Raising epoch limits keeps every vote they cover, and covers the new vote. -/
private theorem coversEpochs_raiseEpochLimits {limits : Option (Epoch × Epoch)}
    {attestation : SignedAttestationRecord} :
    (∀ old, CoversEpochs limits old → CoversEpochs (raiseEpochLimits limits attestation) old) ∧
      CoversEpochs (raiseEpochLimits limits attestation) attestation := by
  cases limits with
  | none =>
    refine ⟨?_, _, _, rfl, UInt64.le_refl _, UInt64.le_refl _⟩
    rintro _ ⟨_, _, found, _⟩
    cases found
  | some limits =>
    obtain ⟨source, target⟩ := limits
    refine ⟨fun old ⟨_, _, same, sourceBelow, targetBelow⟩ => ?_,
      _, _, rfl, Std.right_le_max, Std.right_le_max⟩
    cases same
    exact ⟨_, _, rfl, UInt64.le_trans sourceBelow Std.left_le_max,
      UInt64.le_trans targetBelow Std.left_le_max⟩

/-- The slot limit of a key in a map of limits, none when the key has none. -/
private def slotLimit (limits : Std.TreeMap BLSPubkey (Option Slot × Option (Epoch × Epoch)))
    (key : BLSPubkey) : Option Slot :=
  (limits.getD key (none, none)).1

/-- The epoch limits of a key in a map of limits, none when the key has none. -/
private def epochLimits (limits : Std.TreeMap BLSPubkey (Option Slot × Option (Epoch × Epoch)))
    (key : BLSPubkey) : Option (Epoch × Epoch) :=
  (limits.getD key (none, none)).2

/-- One more entry keeps each slot that the slot limit of a key covers. -/
private theorem coversSlot_insert {key : BLSPubkey} {slot : Slot}
    (limits : Std.TreeMap BLSPubkey (Option Slot × Option (Epoch × Epoch)))
    (entry : InterchangeEntry) (covered : CoversSlot (slotLimit limits key) slot) :
    CoversSlot (slotLimit (limits.insert entry.pubkey
      (entry.raiseLimits (limits.getD entry.pubkey (none, none)))) key) slot := by
  unfold slotLimit at covered ⊢
  rw [Std.TreeMap.getD_insert]
  split
  · rename_i same
    rw [Std.LawfulEqCmp.compare_eq_iff_eq.mp same]
    exact foldl_keeps (f := raiseSlotLimit) (P := fun limit => CoversSlot limit slot)
      (fun _ _ holds => coversSlot_raiseSlotLimit.1 _ holds) _ _ covered
  · exact covered

/-- One more entry keeps each vote that the epoch limits of a key cover. -/
private theorem coversEpochs_insert {key : BLSPubkey} {old : SignedAttestationRecord}
    (limits : Std.TreeMap BLSPubkey (Option Slot × Option (Epoch × Epoch)))
    (entry : InterchangeEntry) (covered : CoversEpochs (epochLimits limits key) old) :
    CoversEpochs (epochLimits (limits.insert entry.pubkey
      (entry.raiseLimits (limits.getD entry.pubkey (none, none)))) key) old := by
  unfold epochLimits at covered ⊢
  rw [Std.TreeMap.getD_insert]
  split
  · rename_i same
    rw [Std.LawfulEqCmp.compare_eq_iff_eq.mp same]
    exact foldl_keeps (f := raiseEpochLimits) (P := fun limits => CoversEpochs limits old)
      (fun _ _ holds => coversEpochs_raiseEpochLimits.1 _ holds) _ _ covered
  · exact covered

/-- The slot limit of a key covers each of its blocks. -/
private theorem coversSlot_limits {record : Interchange} {key : BLSPubkey}
    {old : SignedBlockRecord} (member : old ∈ record.blocksOf key) :
    CoversSlot (slotLimit record.limits key) old.slot := by
  obtain ⟨entry, kept, same, signed⟩ := mem_blocksOf.mp member
  subst same
  refine foldl_makes (P := fun limits => CoversSlot (slotLimit limits entry.pubkey) old.slot)
    (fun limits entry holds => coversSlot_insert limits entry holds)
    (fun limits => ?_) record.data ∅ kept
  unfold slotLimit
  rw [Std.TreeMap.getD_insert_self]
  exact foldl_makes (f := raiseSlotLimit) (P := fun limit => CoversSlot limit old.slot)
    (fun _ _ holds => coversSlot_raiseSlotLimit.1 _ holds)
    (fun _ => coversSlot_raiseSlotLimit.2) entry.signedBlocks _ signed

/-- The epoch limits of a key cover each of its votes. -/
private theorem coversEpochs_limits {record : Interchange} {key : BLSPubkey}
    {old : SignedAttestationRecord} (member : old ∈ record.attestationsOf key) :
    CoversEpochs (epochLimits record.limits key) old := by
  obtain ⟨entry, kept, same, signed⟩ := mem_attestationsOf.mp member
  subst same
  refine foldl_makes (P := fun limits => CoversEpochs (epochLimits limits entry.pubkey) old)
    (fun limits entry holds => coversEpochs_insert limits entry holds)
    (fun limits => ?_) record.data ∅ kept
  unfold epochLimits
  rw [Std.TreeMap.getD_insert_self]
  exact foldl_makes (f := raiseEpochLimits) (P := fun limits => CoversEpochs limits old)
    (fun _ _ holds => coversEpochs_raiseEpochLimits.1 _ holds)
    (fun _ => coversEpochs_raiseEpochLimits.2) entry.signedAttestations _ signed

/-- The blocks of a key after compaction are exactly its slot limit, without a root. -/
private theorem blocksOf_toMinimal {record : Interchange} {key : BLSPubkey} {maximum : Slot}
    (limit : slotLimit record.limits key = some maximum) :
    ∀ block, block ∈ record.toMinimal.blocksOf key ↔ block = ⟨maximum, none⟩ := by
  intro block
  rw [mem_blocksOf]
  unfold slotLimit at limit
  rw [Std.TreeMap.getD_eq_getD_getElem?] at limit
  cases found : record.limits[key]? with
  | none => simp [found] at limit
  | some value =>
    rw [found, Option.getD_some] at limit
    constructor
    · rintro ⟨entry, kept, same, member⟩
      obtain ⟨⟨k, v⟩, listed, rfl⟩ := List.mem_map.mp kept
      change k = key at same
      subst same
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some, found, Option.some.injEq] at listed
      subst listed
      simpa [limit] using member
    · rintro rfl
      refine ⟨_, List.mem_map.mpr ⟨(key, value),
        Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr found, rfl⟩, rfl, ?_⟩
      simp [limit]

/-- The votes of a key after compaction are exactly its epoch limits, without a root. -/
private theorem attestationsOf_toMinimal {record : Interchange} {key : BLSPubkey}
    {source target : Epoch} (limits : epochLimits record.limits key = some (source, target)) :
    ∀ attestation, attestation ∈ record.toMinimal.attestationsOf key ↔
      attestation = ⟨source, target, none⟩ := by
  intro attestation
  rw [mem_attestationsOf]
  unfold epochLimits at limits
  rw [Std.TreeMap.getD_eq_getD_getElem?] at limits
  cases found : record.limits[key]? with
  | none => simp [found] at limits
  | some value =>
    rw [found, Option.getD_some] at limits
    constructor
    · rintro ⟨entry, kept, same, member⟩
      obtain ⟨⟨k, v⟩, listed, rfl⟩ := List.mem_map.mp kept
      change k = key at same
      subst same
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some, found, Option.some.injEq] at listed
      subst listed
      simpa [limits] using member
    · rintro rfl
      refine ⟨_, List.mem_map.mpr ⟨(key, value),
        Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr found, rfl⟩, rfl, ?_⟩
      simp [limits]

/-- The least value of a field over a list where it is constant is that value. -/
private theorem minimum_of_constant {α : Type} {xs : List α} (field : α → UInt64)
    {value : UInt64} (present : ∃ x ∈ xs, field x = value)
    (same : ∀ x ∈ xs, field x = value) : (xs.map field).min? = some value := by
  apply List.min?_eq_some_iff.mpr
  refine ⟨List.mem_map.mpr present, ?_⟩
  intro y mapped
  obtain ⟨x, kept, rfl⟩ := List.mem_map.mp mapped
  rw [same x kept]
  exact UInt64.le_refl _

/-- After compaction, a block that passes the second condition is after every block of the key. -/
private theorem lt_slot_of_toMinimal {record : Interchange} {key : BLSPubkey}
    {slot : Slot} {root : Root} {old : SignedBlockRecord}
    (passed : checkBlockSlot (record.toMinimal.blocksOf key) slot root = .ok ())
    (member : old ∈ record.blocksOf key) : old.slot < slot := by
  obtain ⟨maximum, limit, bound⟩ := coversSlot_limits member
  have shape := blocksOf_toMinimal limit
  have minimum : minBlockSlot (record.toMinimal.blocksOf key) = some maximum :=
    minimum_of_constant SignedBlockRecord.slot ⟨_, (shape _).mpr rfl, rfl⟩
      (fun block member => by rw [(shape block).mp member])
  -- The limit has no signing root, so it cannot make an old block a permitted repeat.
  have repeated : isRepeatBlock (record.toMinimal.blocksOf key) slot root = false := by
    simp only [isRepeatBlock, List.any_eq_false]
    intro block member
    rw [(shape block).mp member]
    simp
  have after := checkBlockSlot_eq_ok_iff.mp passed maximum minimum
  simp only [repeated, Bool.false_eq_true, or_false] at after
  have bound := UInt64.le_iff_toNat_le.mp bound
  have after := UInt64.lt_iff_toNat_lt.mp after
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-- After compaction, a vote that passes the last two conditions is after every vote of the key.

Its source is at least, and its target after, those of each vote. -/
private theorem epochs_of_toMinimal {record : Interchange} {key : BLSPubkey}
    {source target : Epoch} {root : Root} {old : SignedAttestationRecord}
    (sourcePassed : checkSourceEpoch (record.toMinimal.attestationsOf key) source = .ok ())
    (targetPassed : checkTargetEpoch (record.toMinimal.attestationsOf key) source target root =
      .ok ()) (member : old ∈ record.attestationsOf key) :
    old.sourceEpoch ≤ source ∧ old.targetEpoch < target := by
  -- The source and target limits may come from different votes of the key.
  obtain ⟨maxSource, maxTarget, limits, sourceBound, targetBound⟩ := coversEpochs_limits member
  have shape := attestationsOf_toMinimal limits
  have present := (shape ⟨maxSource, maxTarget, none⟩).mpr rfl
  have leastSource : minSourceEpoch (record.toMinimal.attestationsOf key) = some maxSource :=
    minimum_of_constant SignedAttestationRecord.sourceEpoch ⟨_, present, rfl⟩
      (fun vote member => by rw [(shape vote).mp member])
  have leastTarget : minTargetEpoch (record.toMinimal.attestationsOf key) = some maxTarget :=
    minimum_of_constant SignedAttestationRecord.targetEpoch ⟨_, present, rfl⟩
      (fun vote member => by rw [(shape vote).mp member])
  have repeated : isRepeatAttestation (record.toMinimal.attestationsOf key)
      source target root = false := by
    simp only [isRepeatAttestation, List.any_eq_false]
    intro vote member
    rw [(shape vote).mp member]
    simp
  have sourceAfter := checkSourceEpoch_eq_ok_iff.mp sourcePassed maxSource leastSource
  have targetAfter := checkTargetEpoch_eq_ok_iff.mp targetPassed maxTarget leastTarget
  simp only [repeated, Bool.false_eq_true, or_false] at targetAfter
  refine ⟨UInt64.le_trans sourceBound sourceAfter, ?_⟩
  have bound := UInt64.le_iff_toNat_le.mp targetBound
  have after := UInt64.lt_iff_toNat_lt.mp targetAfter
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-- A block after every recorded block passes the second condition. -/
private theorem blockSlot_of_all_lt {blocks : List SignedBlockRecord} {slot : Slot}
    {root : Root} (after : ∀ block ∈ blocks, block.slot < slot) :
    checkBlockSlot blocks slot root = .ok () := by
  apply checkBlockSlot_eq_ok_iff.mpr
  intro minimum computed
  obtain ⟨block, member, rfl⟩ := List.mem_map.mp (List.min?_mem computed)
  exact Or.inl (after block member)

/-- A vote with a source at least every recorded source passes the fourth condition. -/
private theorem sourceEpoch_of_all_le {votes : List SignedAttestationRecord} {source : Epoch}
    (after : ∀ vote ∈ votes, vote.sourceEpoch ≤ source) :
    checkSourceEpoch votes source = .ok () := by
  apply checkSourceEpoch_eq_ok_iff.mpr
  intro minimum computed
  obtain ⟨vote, member, rfl⟩ := List.mem_map.mp (List.min?_mem computed)
  exact after vote member

/-- A vote with a target after every recorded target passes the fifth condition. -/
private theorem targetEpoch_of_all_lt {votes : List SignedAttestationRecord}
    {source target : Epoch} {root : Root} (after : ∀ vote ∈ votes, vote.targetEpoch < target) :
    checkTargetEpoch votes source target root = .ok () := by
  apply checkTargetEpoch_eq_ok_iff.mpr
  intro minimum computed
  obtain ⟨vote, member, rfl⟩ := List.mem_map.mp (List.min?_mem computed)
  exact Or.inl (after vote member)

/-- The record before one import, as the held file and the file one after the other. -/
private theorem blocksOf_append {held file : Interchange} {key : BLSPubkey} :
    ({held with data := held.data ++ file.data} : Interchange).blocksOf key =
      held.blocksOf key ++ file.blocksOf key := by
  simp [Interchange.blocksOf, List.filter_append]

/-- The votes before one import, as those of the held file and then those of the file. -/
private theorem attestationsOf_append {held file : Interchange} {key : BLSPubkey} :
    ({held with data := held.data ++ file.data} : Interchange).attestationsOf key =
      held.attestationsOf key ++ file.attestationsOf key := by
  simp [Interchange.attestationsOf, List.filter_append]

/-- After one import, an accepted block is after every block of the held file and the file.

So the block meets conditions 1 and 2 of the held record and of the file. -/
theorem lt_slot_of_importFile {held file : Interchange} {key : BLSPubkey} {slot : Slot}
    {root : Root} (passed : (held.importFile file).checkBlock key slot root = .ok ()) :
    ∀ old ∈ held.blocksOf key ++ file.blocksOf key, old.slot < slot := by
  intro old member
  rw [← blocksOf_append] at member
  exact lt_slot_of_toMinimal (bind_unit_ok_iff.mp passed).2 member

/-- After one import, an accepted vote has a source at least each source of the two files. -/
theorem le_sourceEpoch_of_importFile {held file : Interchange} {key : BLSPubkey}
    {source target : Epoch} {root : Root}
    (passed : (held.importFile file).checkAttestation key source target root = .ok ()) :
    ∀ old ∈ held.attestationsOf key ++ file.attestationsOf key, old.sourceEpoch ≤ source := by
  intro old member
  rw [← attestationsOf_append] at member
  have checks := (bind_unit_ok_iff.mp (bind_unit_ok_iff.mp passed).2)
  exact (epochs_of_toMinimal checks.1 checks.2 member).1

/-- After one import, an accepted vote has a target after each target of the two files. -/
theorem lt_targetEpoch_of_importFile {held file : Interchange} {key : BLSPubkey}
    {source target : Epoch} {root : Root}
    (passed : (held.importFile file).checkAttestation key source target root = .ok ()) :
    ∀ old ∈ held.attestationsOf key ++ file.attestationsOf key, old.targetEpoch < target := by
  intro old member
  rw [← attestationsOf_append] at member
  have checks := (bind_unit_ok_iff.mp (bind_unit_ok_iff.mp passed).2)
  exact (epochs_of_toMinimal checks.1 checks.2 member).2

/-- A block after every recorded block passes the first two conditions. -/
private theorem checkBlockSigning_of_all_lt {blocks : List SignedBlockRecord} {slot : Slot}
    {root : Root} (after : ∀ block ∈ blocks, block.slot < slot) :
    checkBlockSigning blocks slot root = .ok () := by
  refine checkBlockSigning_eq_ok_iff.mpr ⟨fun block member => ?_, ?_⟩
  · simp [SignedBlockRecord.conflictsWith, UInt64.ne_of_lt (after block member)]
  · exact checkBlockSlot_eq_ok_iff.mp (blockSlot_of_all_lt after)

/-- A vote with a source at least, and a target after, every recorded vote passes the last three.

No recorded vote has its target, and none surrounds it or is surrounded by it. -/
private theorem checkAttestationSigning_of_all {votes : List SignedAttestationRecord}
    {source target : Epoch} {root : Root} (above : ∀ vote ∈ votes, vote.sourceEpoch ≤ source)
    (after : ∀ vote ∈ votes, vote.targetEpoch < target) :
    checkAttestationSigning votes source target root = .ok () := by
  refine checkAttestationSigning_eq_ok_iff.mpr ⟨fun vote member => ?_,
    checkSourceEpoch_eq_ok_iff.mp (sourceEpoch_of_all_le above),
    checkTargetEpoch_eq_ok_iff.mp (targetEpoch_of_all_lt after)⟩
  have notAbove : ¬source < vote.sourceEpoch := UInt64.not_lt.mpr (above vote member)
  have notBelow : ¬target < vote.targetEpoch :=
    UInt64.not_lt.mpr (UInt64.le_of_lt (after vote member))
  simp [SignedAttestationRecord.isSlashableWith, UInt64.ne_of_lt (after vote member), notAbove,
    notBelow]

/-- After any sequence of imports, an accepted block meets conditions 1 and 2 of each input file.

The initial held file is included, and imported files may repeat or contain duplicate keys. -/
theorem checkBlockSigning_of_foldl_importFile {files : List Interchange} {held : Interchange}
    {key : BLSPubkey} {slot : Slot} {root : Root}
    (passed : (files.foldl Interchange.importFile held).checkBlock key slot root = .ok ()) :
    ∀ file ∈ held :: files, checkBlockSigning (file.blocksOf key) slot root = .ok () := by
  induction files generalizing held with
  | nil => simpa [Interchange.checkBlock] using passed
  | cons first rest ih =>
    have all := ih passed
    have current := lt_slot_of_importFile (all _ (List.mem_cons_self ..))
    intro file member
    rcases List.mem_cons.mp member with rfl | member
    · exact checkBlockSigning_of_all_lt fun old kept => current old (List.mem_append_left _ kept)
    rcases List.mem_cons.mp member with rfl | member
    · exact checkBlockSigning_of_all_lt fun old kept => current old (List.mem_append_right _ kept)
    · exact all file (List.mem_cons_of_mem _ member)

/-- After any sequence of imports, an accepted vote meets conditions 3, 4 and 5 of each input file.

The initial held file is included, and imported files may repeat or contain duplicate keys. -/
theorem checkAttestationSigning_of_foldl_importFile {files : List Interchange}
    {held : Interchange} {key : BLSPubkey} {source target : Epoch} {root : Root}
    (passed : (files.foldl Interchange.importFile held).checkAttestation key source target root =
      .ok ()) :
    ∀ file ∈ held :: files,
      checkAttestationSigning (file.attestationsOf key) source target root = .ok () := by
  induction files generalizing held with
  | nil => simpa [Interchange.checkAttestation] using passed
  | cons first rest ih =>
    have all := ih passed
    have above := le_sourceEpoch_of_importFile (all _ (List.mem_cons_self ..))
    have after := lt_targetEpoch_of_importFile (all _ (List.mem_cons_self ..))
    intro file member
    rcases List.mem_cons.mp member with rfl | member
    · exact checkAttestationSigning_of_all
        (fun old kept => above old (List.mem_append_left _ kept))
        (fun old kept => after old (List.mem_append_left _ kept))
    rcases List.mem_cons.mp member with rfl | member
    · exact checkAttestationSigning_of_all
        (fun old kept => above old (List.mem_append_right _ kept))
        (fun old kept => after old (List.mem_append_right _ kept))
    · exact all file (List.mem_cons_of_mem _ member)

end EthLib.Consensus
