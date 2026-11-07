module

public import EthLib.Base.Except
public import EthLib.Consensus.SlashingProtection
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonHex
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws

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

end EthLib.Consensus
