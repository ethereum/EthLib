module

public import EthLib.Consensus.Proofs.LightClient.Containers
public import EthLib.Consensus.Proofs.LightClient.FullNode
public import EthLib.Consensus.Proofs.LightClient.Sync

/-!
# Proofs: what an accepted light client update authenticates

An update carries a header that the sync committee signed, the attested header.

Its finality branch proves a finalized root against the state root of that header.

Its committee branch proves the next sync committee against the same state root.

A branch binds its leaf: take any value whose root is that state root.

Then the proved root is the root of the value's node at the index of the branch.

Otherwise the two climbs to the state root hash two different messages to one SHA-256 output.

In the state of the attested block, the two nodes are its finalized root and its next committee.

The signature needs an assumption, since EthLib proves no unforgeability of BLS here.

The assumption says that an aggregate signature verifies only if every signer signed the message.

Under it, every member whose bit is set signed the signing root of the attested header.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- A normalized branch that verifies against the root of a value opens the value's node.

The node is read at the index of the branch, and the branch that the full node builds proves it.

Otherwise the search over the two climbs names two different 64-byte messages with one hash. -/
theorem isValidNormalizedMerkleBranch_value {α : Type} [SszType α] [LawfulSszType α]
    {leaf node root : Bytes32} {branch : List Bytes32} {gindex : Nat} (named : 2 ≤ gindex)
    (valid : isValidNormalizedMerkleBranch leaf branch gindex root = .ok true) (value : α)
    (rooted : SszType.hashTreeRoot value = .ok root)
    (read : nodeRoot (SszType.desc α) (SszType.toValue value) gindex = .ok node.toArray) :
    leaf = node ∨ ∃ honest a b, computeMerkleProof value gindex = .ok honest ∧
      findBranchCollision gindex 0 leaf.toArray node.toArray
          ((branch.drop (branch.length - Nat.log2 gindex)).map Vector.toArray)
          ((honest.drop (honest.length - Nat.log2 gindex)).map Vector.toArray) =
        some (a, b) ∧
      a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
      Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
        Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  obtain ⟨valueRoot, honest, valueRooted, built, honestValid⟩ :=
    computeMerkleProof_isValidNormalizedMerkleBranch value named read
  obtain rfl : valueRoot = root := Except.ok.inj (valueRooted.symm.trans rooted)
  rcases isValidNormalizedMerkleBranch_binding named valid honestValid with same | collision
  · exact .inl same
  · obtain ⟨a, b, rest⟩ := collision
    exact .inr ⟨honest, a, b, built, rest⟩

variable {preset : Preset} {fork : Fork}

/-- An accepted finality check of an update that proves finality verifies its finality branch.

The leaf is the root of the finalized beacon header, or zero at the genesis slot.

The index is the index of the finalized root in the state at the attested slot. -/
theorem validateFinality_proves {config : Config} {update : LightClientUpdate preset fork}
    (accepted : validateFinality config update = .ok ())
    (finality : update.isFinalityUpdate = true) :
    ∃ gindex leaf, finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
        update.attestedHeader.beacon.slot = .ok gindex ∧
      (update.finalizedHeader.beacon.slot = GENESIS_SLOT ∧ leaf = zeroBytes32 ∨
        update.finalizedHeader.beacon.slot ≠ GENESIS_SLOT ∧
          SszType.hashTreeRoot update.finalizedHeader.beacon = .ok leaf) ∧
      isValidNormalizedMerkleBranch leaf update.finalityBranch.toList gindex
        update.attestedHeader.beacon.stateRoot = .ok true := by
  unfold validateFinality at accepted
  simp only [finality, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at accepted
  split at accepted
  · rename_i genesis
    obtain ⟨_, -, rest⟩ := Base.bind_ok_iff.mp accepted
    obtain ⟨_, zero, rest⟩ := Base.bind_ok_iff.mp rest
    cases zero
    obtain ⟨gindex, indexed, rest⟩ := Base.bind_ok_iff.mp rest
    obtain ⟨verdict, checked, rest⟩ := Base.bind_ok_iff.mp rest
    obtain rfl := LightClientError.require_ok.mp rest
    exact ⟨gindex, _, indexed, .inl ⟨genesis, rfl⟩, LightClientError.liftRoot_ok.mp checked⟩
  · rename_i later
    obtain ⟨_, -, rest⟩ := Base.bind_ok_iff.mp accepted
    obtain ⟨_, -, rest⟩ := Base.bind_ok_iff.mp rest
    obtain ⟨leaf, rooted, rest⟩ := Base.bind_ok_iff.mp rest
    obtain ⟨gindex, indexed, rest⟩ := Base.bind_ok_iff.mp rest
    obtain ⟨verdict, checked, rest⟩ := Base.bind_ok_iff.mp rest
    obtain rfl := LightClientError.require_ok.mp rest
    exact ⟨gindex, leaf, indexed, .inr ⟨later, LightClientError.liftRoot_ok.mp rooted⟩,
      LightClientError.liftRoot_ok.mp checked⟩

/-- An accepted committee branch verifies the root of the next committee of an update.

The index is the index of the next committee in the state at the attested slot. -/
theorem validateNextSyncCommitteeBranch_proves {config : Config}
    {update : LightClientUpdate preset fork}
    (accepted : validateNextSyncCommitteeBranch config update = .ok ()) :
    ∃ gindex leaf, nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
        update.attestedHeader.beacon.slot = .ok gindex ∧
      SszType.hashTreeRoot update.nextSyncCommittee = .ok leaf ∧
      isValidNormalizedMerkleBranch leaf update.nextSyncCommitteeBranch.toList gindex
        update.attestedHeader.beacon.stateRoot = .ok true := by
  unfold validateNextSyncCommitteeBranch at accepted
  obtain ⟨leaf, rooted, rest⟩ := Base.bind_ok_iff.mp accepted
  obtain ⟨gindex, indexed, rest⟩ := Base.bind_ok_iff.mp rest
  obtain ⟨verdict, checked, rest⟩ := Base.bind_ok_iff.mp rest
  obtain rfl := LightClientError.require_ok.mp rest
  exact ⟨gindex, leaf, indexed, LightClientError.liftRoot_ok.mp rooted,
    LightClientError.liftRoot_ok.mp checked⟩

/-- The index of the finalized root at a slot names a node below the root. -/
theorem finalizedRootGindexAtSlot_named {config : Config} {slot : Slot} {gindex : Nat}
    (indexed : finalizedRootGindexAtSlot (preset := preset) (fork := fork) config slot =
      .ok gindex) : 2 ≤ gindex := by
  unfold finalizedRootGindexAtSlot at indexed
  cases forked : stateForkAtSlot (preset := preset) (fork := fork) config slot with
  | error => simp [forked, Functor.map, Except.map] at indexed
  | ok state =>
    simp only [forked, Functor.map, Except.map, Except.ok.injEq] at indexed
    subst indexed
    unfold finalizedRootGindex
    split <;> (try split) <;> decide

/-- The index of the next committee at a slot names a node below the root. -/
theorem nextSyncCommitteeGindexAtSlot_named {config : Config} {slot : Slot} {gindex : Nat}
    (indexed : nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config slot =
      .ok gindex) : 2 ≤ gindex := by
  unfold nextSyncCommitteeGindexAtSlot at indexed
  cases forked : stateForkAtSlot (preset := preset) (fork := fork) config slot with
  | error => simp [forked, Functor.map, Except.map] at indexed
  | ok state =>
    simp only [forked, Functor.map, Except.map, Except.ok.injEq] at indexed
    subst indexed
    unfold nextSyncCommitteeGindex
    split <;> (try split) <;> decide

/-- What an accepted update proves, before any assumption on the signature.

At least the minimum of bits of the aggregate are set.

The signature check accepts the keys of those members on the signing root of the attested header.

The finality check passes, and so does the branch of a next committee that the update carries.

An update without a committee branch carries the zero committee. -/
theorem validateLightClientUpdate_proves {config : Config} {checks : SignatureChecks}
    {store : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ()) :
    preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat ≤ update.syncAggregate.participants ∧
      validateFinality config update = .ok () ∧
      (update.isSyncCommitteeUpdate = true →
        validateNextSyncCommitteeBranch config update = .ok ()) ∧
      (update.isSyncCommitteeUpdate = false →
        update.nextSyncCommittee = SyncCommittee.empty preset) ∧
      ∃ signingRoot, syncCommitteeSigningRoot config update genesisValidatorsRoot =
          .ok signingRoot ∧
        checks.fastAggregateVerify
          (((store.signatureCommittee update).participantKeys update.syncAggregate).map packBytes)
          (packBytes signingRoot) (packBytes update.syncAggregate.syncCommitteeSignature) =
          true := by
  unfold validateLightClientUpdate at accepted
  simp only [Base.bind_ok_iff, LightClientError.require_ok] at accepted
  obtain ⟨_, -, _, participants, _, -, _, -, _, -, rest⟩ := accepted
  refine ⟨participants, ?_⟩
  -- Split on the three conditions of the branches, then read each chain of checks.
  cases known : store.isNextSyncCommitteeKnown <;>
    cases committee : update.isSyncCommitteeUpdate <;>
    simp only [known, committee, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      and_false, and_true, Base.bind_ok_iff, LightClientError.require_ok] at rest
  · obtain ⟨_, -, _, -, ⟨⟩, finality, _, empty, root, rooted, verified⟩ := rest
    exact ⟨finality, nofun, fun _ => empty, root, rooted, verified⟩
  · obtain ⟨_, -, _, -, ⟨⟩, finality, ⟨⟩, branch, root, rooted, verified⟩ := rest
    exact ⟨finality, fun _ => branch, nofun, root, rooted, verified⟩
  · obtain ⟨_, -, _, -, ⟨⟩, finality, _, empty, root, rooted, verified⟩ := rest
    exact ⟨finality, nofun, fun _ => empty, root, rooted, verified⟩
  · obtain ⟨_, -, _, -, ⟨⟩, finality, rest⟩ := rest
    -- A next committee that the store knows must also match; the branch check follows.
    split at rest <;> simp only [Base.bind_ok_iff, LightClientError.require_ok] at rest
    · obtain ⟨_, -, ⟨⟩, branch, root, rooted, verified⟩ := rest
      exact ⟨finality, fun _ => branch, nofun, root, rooted, verified⟩
    · obtain ⟨⟨⟩, branch, root, rooted, verified⟩ := rest
      exact ⟨finality, fun _ => branch, nofun, root, rooted, verified⟩

/-- The finalized root of an accepted update is a node of the attested state.

Take any value whose root is the attested state root, such as the beacon state of that block.

Its node at the index of the finality branch is the leaf that the update proves.

Otherwise the search over the two climbs names a SHA-256 collision.

The leaf is the root of the finalized beacon header, or zero at the genesis slot. -/
theorem validateLightClientUpdate_finalized {config : Config} {checks : SignatureChecks}
    {store : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    (finality : update.isFinalityUpdate = true) {α : Type} [SszType α] [LawfulSszType α]
    (state : α) (rooted : SszType.hashTreeRoot state = .ok update.attestedHeader.beacon.stateRoot) :
    ∃ gindex leaf, finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
        update.attestedHeader.beacon.slot = .ok gindex ∧
      (update.finalizedHeader.beacon.slot = GENESIS_SLOT ∧ leaf = zeroBytes32 ∨
        update.finalizedHeader.beacon.slot ≠ GENESIS_SLOT ∧
          SszType.hashTreeRoot update.finalizedHeader.beacon = .ok leaf) ∧
      ∀ node : Bytes32,
        nodeRoot (SszType.desc α) (SszType.toValue state) gindex = .ok node.toArray →
      leaf = node ∨ ∃ honest a b, computeMerkleProof state gindex = .ok honest ∧
        findBranchCollision gindex 0 leaf.toArray node.toArray
            ((update.finalityBranch.toList.drop
              (update.finalityBranch.toList.length - Nat.log2 gindex)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 gindex)).map Vector.toArray) =
          some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  obtain ⟨gindex, leaf, indexed, named, valid⟩ :=
    validateFinality_proves (validateLightClientUpdate_proves accepted).2.1 finality
  exact ⟨gindex, leaf, indexed, named, fun node read =>
    isValidNormalizedMerkleBranch_value (finalizedRootGindexAtSlot_named indexed) valid state
      rooted read⟩

/-- The next committee root of an accepted update is a node of the attested state.

This holds for an update that carries a committee branch.

Take any value whose root is the attested state root, such as the beacon state of that block.

Its node at the index of the committee branch is the root of the committee of the update.

Otherwise the search over the two climbs names a SHA-256 collision. -/
theorem validateLightClientUpdate_nextSyncCommittee {config : Config}
    {checks : SignatureChecks} {store : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    (committee : update.isSyncCommitteeUpdate = true) {α : Type} [SszType α] [LawfulSszType α]
    (state : α) (rooted : SszType.hashTreeRoot state = .ok update.attestedHeader.beacon.stateRoot) :
    ∃ gindex leaf, nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
        update.attestedHeader.beacon.slot = .ok gindex ∧
      SszType.hashTreeRoot update.nextSyncCommittee = .ok leaf ∧
      ∀ node : Bytes32,
        nodeRoot (SszType.desc α) (SszType.toValue state) gindex = .ok node.toArray →
      leaf = node ∨ ∃ honest a b, computeMerkleProof state gindex = .ok honest ∧
        findBranchCollision gindex 0 leaf.toArray node.toArray
            ((update.nextSyncCommitteeBranch.toList.drop
              (update.nextSyncCommitteeBranch.toList.length - Nat.log2 gindex)).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 gindex)).map Vector.toArray) =
          some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  obtain ⟨gindex, leaf, indexed, committeeRoot, valid⟩ :=
    validateNextSyncCommitteeBranch_proves
      ((validateLightClientUpdate_proves accepted).2.2.1 committee)
  exact ⟨gindex, leaf, indexed, committeeRoot, fun node read =>
    isValidNormalizedMerkleBranch_value (nextSyncCommitteeGindexAtSlot_named indexed) valid state
      rooted read⟩

/-- The finalized root of an accepted update is the finalized root of the attested beacon state.

Take a beacon state of a fork from Altair whose root is the attested state root.

At the attested slot, the client must read the finalized root at the index of that fork.

The proved root is the root of the finalized beacon header, or zero at the genesis slot.

It is the root in the finalized checkpoint of the state, or the search names a SHA-256 collision. -/
theorem validateLightClientUpdate_finalizedCheckpoint {config : Config}
    {checks : SignatureChecks} {store : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    (finality : update.isFinalityUpdate = true) {stateFork : Fork}
    [LawfulSszType (BeaconState preset stateFork)] (altair : .altair ≤ stateFork)
    (state : BeaconState preset stateFork)
    (rooted : SszType.hashTreeRoot state = .ok update.attestedHeader.beacon.stateRoot)
    (layout : finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
      update.attestedHeader.beacon.slot = .ok (finalizedRootGindex stateFork)) :
    ∃ leaf node,
      (update.finalizedHeader.beacon.slot = GENESIS_SLOT ∧ leaf = zeroBytes32 ∨
        update.finalizedHeader.beacon.slot ≠ GENESIS_SLOT ∧
          SszType.hashTreeRoot update.finalizedHeader.beacon = .ok leaf) ∧
      SszType.hashTreeRoot state.finalizedCheckpoint.root = .ok node ∧
      (leaf = node ∨ ∃ honest a b,
        computeMerkleProof state (finalizedRootGindex stateFork) = .ok honest ∧
        findBranchCollision (finalizedRootGindex stateFork) 0 leaf.toArray node.toArray
            ((update.finalityBranch.toList.drop (update.finalityBranch.toList.length -
              Nat.log2 (finalizedRootGindex stateFork))).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 (finalizedRootGindex stateFork))).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  obtain ⟨gindex, leaf, indexed, named, bound⟩ :=
    validateLightClientUpdate_finalized accepted finality state rooted
  rw [layout, Except.ok.injEq] at indexed
  subst indexed
  obtain ⟨node, nodeRooted⟩ := SszType.hashTreeRoot_total state.finalizedCheckpoint.root
  exact ⟨leaf, node, named, nodeRooted,
    bound node (BeaconState.nodeRoot_finalizedCheckpoint_root altair state nodeRooted)⟩

/-- The committee of an accepted update is the next sync committee of the attested beacon state.

This holds for an update that carries a committee branch.

Take a beacon state of a fork from Altair whose root is the attested state root.

At the attested slot, the client must read the committee at the index of that fork.

The root of the committee of the update is the root of the next committee of the state.

Otherwise the search names a SHA-256 collision. -/
theorem validateLightClientUpdate_nextSyncCommittee_state {config : Config}
    {checks : SignatureChecks} {store : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    (committee : update.isSyncCommitteeUpdate = true) {stateFork : Fork}
    [LawfulSszType (BeaconState preset stateFork)] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (altair : .altair ≤ stateFork) (state : BeaconState preset stateFork)
    (rooted : SszType.hashTreeRoot state = .ok update.attestedHeader.beacon.stateRoot)
    (layout : nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
      update.attestedHeader.beacon.slot = .ok (nextSyncCommitteeGindex stateFork)) :
    ∃ leaf node, SszType.hashTreeRoot update.nextSyncCommittee = .ok leaf ∧
      SszType.hashTreeRoot (state.nextSyncCommittee altair) = .ok node ∧
      (leaf = node ∨ ∃ honest a b,
        computeMerkleProof state (nextSyncCommitteeGindex stateFork) = .ok honest ∧
        findBranchCollision (nextSyncCommitteeGindex stateFork) 0 leaf.toArray node.toArray
            ((update.nextSyncCommitteeBranch.toList.drop
              (update.nextSyncCommitteeBranch.toList.length -
                Nat.log2 (nextSyncCommitteeGindex stateFork))).map Vector.toArray)
            ((honest.drop (honest.length - Nat.log2 (nextSyncCommitteeGindex stateFork))).map
              Vector.toArray) = some (a, b) ∧
        a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
          Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  obtain ⟨gindex, leaf, indexed, committeeRooted, bound⟩ :=
    validateLightClientUpdate_nextSyncCommittee accepted committee state rooted
  rw [layout, Except.ok.injEq] at indexed
  subst indexed
  obtain ⟨node, nodeRooted⟩ := SszType.hashTreeRoot_total (state.nextSyncCommittee altair)
  exact ⟨leaf, node, committeeRooted, nodeRooted,
    bound node (BeaconState.nodeRoot_nextSyncCommittee altair state nodeRooted)⟩

/-- The assumption on an aggregate signature check: it accepts only messages that all keys signed.

The relation says which messages the holder of each key signed.

BLS with proofs of possession is meant to give this, except with negligible probability.

EthLib does not prove that, so the theorems below take it as a hypothesis. -/
def SignatureChecks.AggregateSound (checks : SignatureChecks)
    (signed : ByteArray → ByteArray → Prop) : Prop :=
  ∀ keys message signature, checks.fastAggregateVerify keys message signature = true →
    ∀ key ∈ keys, signed key message

/-- The assumption has content: the checks that accept every signature do not meet it.

Here no key signed any message, and the checks still accept a signature by one key. -/
theorem SignatureChecks.not_aggregateSound_acceptAll :
    ¬SignatureChecks.acceptAll.AggregateSound fun _ _ => False :=
  fun sound => sound #[.empty] .empty .empty rfl .empty (by simp)

/-- Keys whose bit is set number as many as the set bits, when there is a key for each bit. -/
theorem length_filterMap_zip_bits {β : Type} :
    ∀ (bits : List Bool) (keys : List β), bits.length ≤ keys.length →
      ((bits.zip keys).filterMap fun (bit, key) => if bit then some key else none).length =
        bits.count true
  | [], _, _ => rfl
  | _ :: _, [], short => absurd short (by simp)
  | bit :: bits, key :: keys, enough => by
    have rest := length_filterMap_zip_bits bits keys (by simpa using enough)
    cases bit
    · simp [rest]
    · simp [rest]

/-- Keys whose bit is set keep their order, so they form a sublist of the keys. -/
theorem filterMap_zip_bits_sublist {β : Type} :
    ∀ (bits : List Bool) (keys : List β),
      ((bits.zip keys).filterMap fun (bit, key) => if bit then some key else none).Sublist keys
  | [], keys => by simp
  | _ :: _, [] => by simp
  | bit :: bits, key :: keys => by
    have rest := filterMap_zip_bits_sublist bits keys
    cases bit
    · simpa [List.filterMap_cons] using rest.cons key
    · simpa [List.filterMap_cons] using rest.cons_cons key

/-- The keys of a committee whose bit is set number as many as the members that signed. -/
theorem SyncCommittee.size_participantKeys (committee : SyncCommittee preset)
    (aggregate : SyncAggregate preset) :
    (committee.participantKeys aggregate).size = aggregate.participants := by
  unfold participantKeys SyncAggregate.participants
  simp only [List.size_toArray]
  exact length_filterMap_zip_bits _ _ (by simp)

/-- What the signature of an accepted update authenticates, under the assumption on it.

The update names the committee of the store for its signature period.

At least the minimum of its members signed the signing root of the attested header. -/
theorem validateLightClientUpdate_signed {config : Config} {checks : SignatureChecks}
    {store : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    {signed : ByteArray → ByteArray → Prop} (sound : checks.AggregateSound signed) :
    ∃ signingRoot, syncCommitteeSigningRoot config update genesisValidatorsRoot =
        .ok signingRoot ∧
      preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat ≤
        ((store.signatureCommittee update).participantKeys update.syncAggregate).size ∧
      ∀ key ∈ (store.signatureCommittee update).participantKeys update.syncAggregate,
        signed (packBytes key) (packBytes signingRoot) := by
  obtain ⟨participants, -, -, -, signingRoot, rooted, verified⟩ :=
    validateLightClientUpdate_proves accepted
  refine ⟨signingRoot, rooted, by rw [SyncCommittee.size_participantKeys]; exact participants,
    fun key member => sound _ _ _ verified _ (Array.mem_map_of_mem member)⟩

/-- An accepted update was signed by a member outside any set that holds fewer committee seats.

Take a set of keys, such as those that may sign anything.

Suppose it holds fewer seats of the signing committee than there are signers.

Under the assumption on aggregate signatures, a signer outside the set signed the signing root.

That root is the signing root of the attested header. -/
theorem validateLightClientUpdate_signed_outside {config : Config} {checks : SignatureChecks}
    {store : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ())
    {signed : ByteArray → ByteArray → Prop} (sound : checks.AggregateSound signed)
    (excluded : Cryptography.Bls.BLSPubkey → Bool)
    (few : (store.signatureCommittee update).pubkeys.toList.countP excluded <
      update.syncAggregate.participants) :
    ∃ signingRoot, syncCommitteeSigningRoot config update genesisValidatorsRoot =
        .ok signingRoot ∧
      ∃ key ∈ (store.signatureCommittee update).participantKeys update.syncAggregate,
        excluded key = false ∧ signed (packBytes key) (packBytes signingRoot) := by
  obtain ⟨signingRoot, rooted, -, all⟩ := validateLightClientUpdate_signed accepted sound
  refine ⟨signingRoot, rooted, ?_⟩
  -- The signers are seats of the committee, so the set holds fewer of them than there are.
  have seats := (filterMap_zip_bits_sublist update.syncAggregate.syncCommitteeBits.bits.toList
    (store.signatureCommittee update).pubkeys.toList).countP_le (p := excluded)
  have count := SyncCommittee.size_participantKeys (store.signatureCommittee update)
    update.syncAggregate
  unfold SyncCommittee.participantKeys at count all ⊢
  simp only [List.size_toArray, List.mem_toArray] at count all ⊢
  generalize ((update.syncAggregate.syncCommitteeBits.bits.toList.zip
    (store.signatureCommittee update).pubkeys.toList).filterMap
      fun (bit, key) => if bit then some key else none) = signers at seats count all ⊢
  -- If every signer were in the set, the set would hold every signer.
  refine Classical.byContradiction fun none => absurd few (Nat.not_lt.mpr ?_)
  have inside : ∀ key ∈ signers, excluded key = true := fun key member => by
    cases outside : excluded key
    · exact absurd ⟨key, member, outside, all key member⟩ none
    · rfl
  rw [← count, ← List.countP_eq_length.mpr inside]
  exact seats

end EthLib.Consensus
