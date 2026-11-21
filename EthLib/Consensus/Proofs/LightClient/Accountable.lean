module

public import EthLib.Consensus.Proofs.LightClient.Authenticate

/-!
# Proofs: two updates that move the finalized header share a third of the committee

A light client moves its finalized header only when two thirds of the sync committee signed.

So two such updates, under one committee, have at least a third of its seats set in both.

Under the signature assumption, the keys of those seats signed the attested headers of both.

That is not a fault by itself: an honest member signs a new head at every slot.

Two such updates with one attested beacon header prove one finalized root.

Otherwise a search over the two finality branches names a SHA-256 collision.

A forced update moves the finalized header without two thirds, so these results leave it out.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- Two bit lists of one length have many bits set in both.

The two counts of set bits add up to at most the length plus the count of bits set in both. -/
theorem count_add_count_le_count_zipWith_and :
    ∀ first second : List Bool, first.length = second.length →
      first.count true + second.count true ≤
        first.length + (List.zipWith (· && ·) first second).count true
  | [], [], _ => by simp
  | [], _ :: _, same => absurd same (by simp)
  | _ :: _, [], same => absurd same (by simp)
  | a :: first, b :: second, same => by
    have rest := count_add_count_le_count_zipWith_and first second (by simpa using same)
    cases a <;> cases b <;> simp <;> omega

variable {preset : Preset} {fork : Fork}

/-- An update moves the finalized header exactly when two thirds of the committee signed it.

The finalized header of the update must also be newer than the one of the store. -/
theorem processLightClientUpdate_finalizedHeader_ne_iff {config : Config}
    {checks : SignatureChecks} {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    after.finalizedHeader ≠ store.finalizedHeader ↔
      preset.SYNC_COMMITTEE_SIZE.toNat * 2 ≤ update.syncAggregate.participants * 3 ∧
        store.finalizedHeader.beacon.slot < update.finalizedHeader.beacon.slot := by
  rw [processLightClientUpdate_finalizedHeader computed]
  split
  · rename_i moved
    refine ⟨fun _ => moved, fun _ same => ?_⟩
    have newer := moved.2
    rw [same] at newer
    exact UInt64.lt_irrefl _ newer
  · rename_i kept
    exact ⟨fun moved => absurd rfl moved, fun moved => absurd moved kept⟩

/-- An update that moves the finalized header proves a finalized root.

The finalized slot is above the slot of the store, so it is not the genesis slot.

An update without a finality branch carries the empty header, whose slot is the genesis slot. -/
theorem processLightClientUpdate_isFinalityUpdate {config : Config}
    {checks : SignatureChecks} {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after)
    (moved : after.finalizedHeader ≠ store.finalizedHeader) :
    update.isFinalityUpdate = true := by
  have newer := ((processLightClientUpdate_finalizedHeader_ne_iff computed).mp moved).2
  have checked := (validateLightClientUpdate_proves
    (processLightClientUpdate_eq_ok_iff.mp computed).1).2.1
  cases finality : update.isFinalityUpdate
  · -- Without a finality branch, the check holds the finalized header to the empty header.
    unfold validateFinality at checked
    simp only [finality, Bool.not_false, ↓reduceIte] at checked
    have empty := LightClientHeader.beacon_eq_of_sameSszValue
      (Base.ensure_ok_iff.mp checked)
    rw [empty] at newer
    exact (UInt64.not_lt_zero newer).elim
  · rfl

/-- Two updates that move the finalized header have a third of the committee set in both.

Each moves it only with two thirds of the seats, and the seats number the committee size.

This counts bits only, so it needs no signature assumption and no common committee. -/
theorem processLightClientUpdate_overlap {config : Config} {checks : SignatureChecks}
    {store₁ after₁ store₂ after₂ : LightClientStore preset fork}
    {update₁ update₂ : LightClientUpdate preset fork} {currentSlot₁ currentSlot₂ : Slot}
    {genesisValidatorsRoot : Root}
    (computed₁ : processLightClientUpdate config checks store₁ update₁ currentSlot₁
      genesisValidatorsRoot = .ok after₁)
    (moved₁ : after₁.finalizedHeader ≠ store₁.finalizedHeader)
    (computed₂ : processLightClientUpdate config checks store₂ update₂ currentSlot₂
      genesisValidatorsRoot = .ok after₂)
    (moved₂ : after₂.finalizedHeader ≠ store₂.finalizedHeader) :
    preset.SYNC_COMMITTEE_SIZE.toNat ≤
      3 * (List.zipWith (· && ·) update₁.syncAggregate.syncCommitteeBits.bits.toList
        update₂.syncAggregate.syncCommitteeBits.bits.toList).count true := by
  have first := ((processLightClientUpdate_finalizedHeader_ne_iff computed₁).mp moved₁).1
  have second := ((processLightClientUpdate_finalizedHeader_ne_iff computed₂).mp moved₂).1
  have shared := count_add_count_le_count_zipWith_and
    update₁.syncAggregate.syncCommitteeBits.bits.toList
    update₂.syncAggregate.syncCommitteeBits.bits.toList (by simp)
  unfold SyncAggregate.participants at first second
  simp only [Vector.length_toList] at shared
  omega

/-- The key of a seat whose bit is set is among the keys of the members that signed. -/
theorem SyncCommittee.mem_participantKeys (committee : SyncCommittee preset)
    (aggregate : SyncAggregate preset) (seat : Fin preset.SYNC_COMMITTEE_SIZE.toNat)
    (set : aggregate.syncCommitteeBits.bits[seat] = true) :
    committee.pubkeys[seat] ∈ committee.participantKeys aggregate := by
  unfold participantKeys
  rw [List.mem_toArray, List.mem_filterMap]
  refine ⟨(aggregate.syncCommitteeBits.bits[seat], committee.pubkeys[seat]), ?_, by simp [set]⟩
  rw [List.mem_iff_getElem]
  exact ⟨seat, by simp, by simp⟩

/-- Under the signature assumption, the key of each seat whose bit is set signed the update.

The seat is a seat of the committee that the store reads for the update.

The message is the signing root of the attested header. -/
theorem validateLightClientUpdate_signed_seat {config : Config} {checks : SignatureChecks}
    {store : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    {signed : Cryptography.Bls.BLSPubkey → ByteArray → Prop}
    (sound : checks.AggregateSoundOn
      (updateSignatureCall config store update genesisValidatorsRoot) signed)
    {signingRoot : Root}
    (rooted : syncCommitteeSigningRoot config update genesisValidatorsRoot = .ok signingRoot)
    (seat : Fin preset.SYNC_COMMITTEE_SIZE.toNat)
    (set : update.syncAggregate.syncCommitteeBits.bits[seat] = true) :
    signed (store.signatureCommittee update).pubkeys[seat] (packBytes signingRoot) := by
  obtain ⟨root, computedRoot, -, all⟩ := validateLightClientUpdate_signed accepted sound
  obtain rfl : root = signingRoot := Except.ok.inj (computedRoot.symm.trans rooted)
  exact all _ (SyncCommittee.mem_participantKeys _ _ seat set)

/-- Under one committee, the key of a seat set in two accepted updates signed both of them.

It signed the signing roots of both attested headers.

The committee is the one that each store reads for its update.

Each update needs the signature assumption on its own aggregate call. -/
theorem validateLightClientUpdate_overlap_signed {config : Config} {checks : SignatureChecks}
    {store₁ store₂ : LightClientStore preset fork}
    {update₁ update₂ : LightClientUpdate preset fork} {currentSlot₁ currentSlot₂ : Slot}
    {genesisValidatorsRoot : Root}
    (accepted₁ : validateLightClientUpdate config checks store₁ update₁ currentSlot₁
      genesisValidatorsRoot = .ok ())
    (accepted₂ : validateLightClientUpdate config checks store₂ update₂ currentSlot₂
      genesisValidatorsRoot = .ok ())
    (committee : store₁.signatureCommittee update₁ = store₂.signatureCommittee update₂)
    {signed : Cryptography.Bls.BLSPubkey → ByteArray → Prop}
    (sound₁ : checks.AggregateSoundOn
      (updateSignatureCall config store₁ update₁ genesisValidatorsRoot) signed)
    (sound₂ : checks.AggregateSoundOn
      (updateSignatureCall config store₂ update₂ genesisValidatorsRoot) signed)
    {signingRoot₁ signingRoot₂ : Root}
    (rooted₁ : syncCommitteeSigningRoot config update₁ genesisValidatorsRoot = .ok signingRoot₁)
    (rooted₂ : syncCommitteeSigningRoot config update₂ genesisValidatorsRoot = .ok signingRoot₂)
    (seat : Fin preset.SYNC_COMMITTEE_SIZE.toNat)
    (set₁ : update₁.syncAggregate.syncCommitteeBits.bits[seat] = true)
    (set₂ : update₂.syncAggregate.syncCommitteeBits.bits[seat] = true) :
    signed (store₁.signatureCommittee update₁).pubkeys[seat] (packBytes signingRoot₁) ∧
      signed (store₁.signatureCommittee update₁).pubkeys[seat] (packBytes signingRoot₂) := by
  refine ⟨validateLightClientUpdate_signed_seat accepted₁ sound₁ rooted₁ seat set₁, ?_⟩
  rw [committee]
  exact validateLightClientUpdate_signed_seat accepted₂ sound₂ rooted₂ seat set₂

/-- Two updates that move the finalized header from one attested beacon header agree on its root.

The root is that of the finalized beacon header, the finalized block root.

Both finality branches verify at one index against the state root of the attested header.

Otherwise the search over the two climbs names two 64-byte messages with one SHA-256 digest. -/
theorem processLightClientUpdate_finalized_agree {config : Config} {checks : SignatureChecks}
    {store₁ after₁ store₂ after₂ : LightClientStore preset fork}
    {update₁ update₂ : LightClientUpdate preset fork} {currentSlot₁ currentSlot₂ : Slot}
    {genesisValidatorsRoot : Root}
    (computed₁ : processLightClientUpdate config checks store₁ update₁ currentSlot₁
      genesisValidatorsRoot = .ok after₁)
    (moved₁ : after₁.finalizedHeader ≠ store₁.finalizedHeader)
    (computed₂ : processLightClientUpdate config checks store₂ update₂ currentSlot₂
      genesisValidatorsRoot = .ok after₂)
    (moved₂ : after₂.finalizedHeader ≠ store₂.finalizedHeader)
    (attested : update₁.attestedHeader.beacon = update₂.attestedHeader.beacon) :
    ∃ gindex root₁ root₂, finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
        update₁.attestedHeader.beacon.slot = .ok gindex ∧
      SszType.hashTreeRoot update₁.finalizedHeader.beacon = .ok root₁ ∧
      SszType.hashTreeRoot update₂.finalizedHeader.beacon = .ok root₂ ∧
      (root₁ = root₂ ∨ ∃ a b,
        findBranchCollision gindex 0 root₁.toArray root₂.toArray
            ((update₁.finalityBranch.toList.drop
              (update₁.finalityBranch.toList.length - Nat.log2 gindex)).map Vector.toArray)
            ((update₂.finalityBranch.toList.drop
              (update₂.finalityBranch.toList.length - Nat.log2 gindex)).map Vector.toArray) =
          some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  -- Each update proves its finalized root with its branch, at the index of the attested slot.
  have proves (store after : LightClientStore preset fork) (update : LightClientUpdate preset fork)
      (currentSlot : Slot)
      (computed : processLightClientUpdate config checks store update currentSlot
        genesisValidatorsRoot = .ok after)
      (moved : after.finalizedHeader ≠ store.finalizedHeader) :
      ∃ gindex root, finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
          update.attestedHeader.beacon.slot = .ok gindex ∧
        SszType.hashTreeRoot update.finalizedHeader.beacon = .ok root ∧
        isValidNormalizedMerkleBranch root update.finalityBranch.toList gindex
          update.attestedHeader.beacon.stateRoot = .ok true := by
    have newer := ((processLightClientUpdate_finalizedHeader_ne_iff computed).mp moved).2
    obtain ⟨gindex, root, indexed, named, valid⟩ := validateFinality_proves
      (validateLightClientUpdate_proves (processLightClientUpdate_eq_ok_iff.mp computed).1).2.1
      (processLightClientUpdate_isFinalityUpdate computed moved)
    -- The finalized slot is above the slot of the store, so it is not the genesis slot.
    rcases named with ⟨genesis, -⟩ | ⟨-, rooted⟩
    · rw [genesis] at newer
      exact (UInt64.not_lt_zero newer).elim
    · exact ⟨gindex, root, indexed, rooted, valid⟩
  obtain ⟨gindex, root₁, indexed₁, rooted₁, valid₁⟩ :=
    proves store₁ after₁ update₁ currentSlot₁ computed₁ moved₁
  obtain ⟨gindex₂, root₂, indexed₂, rooted₂, valid₂⟩ :=
    proves store₂ after₂ update₂ currentSlot₂ computed₂ moved₂
  rw [← attested, indexed₁, Except.ok.injEq] at indexed₂
  subst indexed₂
  rw [← attested] at valid₂
  exact ⟨gindex, root₁, root₂, indexed₁, rooted₁, rooted₂,
    isValidNormalizedMerkleBranch_binding (finalizedRootGindexAtSlot_named indexed₁) valid₁
      valid₂⟩

end EthLib.Consensus
