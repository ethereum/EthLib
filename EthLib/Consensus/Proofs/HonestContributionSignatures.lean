module

public import EthLib.Consensus.Proofs.HonestAggregation
public import EthLib.Consensus.Proofs.Gossip.SyncCommittee
public import EthLib.Consensus.Proofs.HonestValidator
public import EthLib.Cryptography.Proofs.Bls.AggregatePerm

/-!
# Proofs: honest sync contributions pass their signature check

The contribution counts one signature per participating seat, in the order read by gossip.

A key that holds several seats contributes its signature once for each of those seats.

Repeated messages for a key do not add signatures: each seat takes the first matching message.

The selected secret keys must not sum to zero.

A contribution and proof that its aggregator makes and signs passes both of its signature checks.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A subcommittee slice has one key for each of its seats. -/
private theorem syncSubcommitteePubkeys_length {committee : SyncCommittee preset}
    {subcommitteeIndex : UInt64} (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT) :
    (syncSubcommitteePubkeys committee subcommitteeIndex.toNat).length =
      syncSubcommitteeSize preset := by
  have below : subcommitteeIndex.toNat < Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT := by
    simpa [SYNC_COMMITTEE_SUBNET_COUNT, Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT,
      UInt64.lt_iff_toNat_lt] using inRange
  have room : (subcommitteeIndex.toNat + 1) * syncSubcommitteeSize preset ≤
      preset.SYNC_COMMITTEE_SIZE.toNat :=
    calc (subcommitteeIndex.toNat + 1) * syncSubcommitteeSize preset
        ≤ Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT * syncSubcommitteeSize preset :=
          Nat.mul_le_mul_right _ below
      _ ≤ preset.SYNC_COMMITTEE_SIZE.toNat := Nat.mul_div_le _ _
  rw [Nat.succ_mul] at room
  simp only [syncSubcommitteePubkeys, List.length_take, List.length_drop, Vector.length_toList]
  omega

/-- Reading the seats in order gives the subcommittee slice. -/
private theorem syncSubcommitteePubkeys_eq_map {committee : SyncCommittee preset}
    {subcommitteeIndex : UInt64} (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT) :
    syncSubcommitteePubkeys committee subcommitteeIndex.toNat =
      (List.finRange (syncSubcommitteeSize preset)).map
        (syncSubcommitteeKey committee subcommitteeIndex inRange) := by
  apply List.ext_getElem
  · simp [syncSubcommitteePubkeys_length inRange]
  · intro index left right
    simp [syncSubcommitteeKey, List.getElem_map, List.getElem_finRange]

/-- The first input message for each participating seat, with its registry key. -/
private def contributionEntries (keyed : List (BLSPubkey × SyncCommitteeMessage))
    (pubkeys : List BLSPubkey) : List (BLSPubkey × SyncCommitteeMessage) :=
  pubkeys.filterMap fun pubkey => keyed.find? (·.1 = pubkey)

/-- The selected entries have exactly the keys picked by the bits, with multiplicity. -/
private theorem contributionEntries_keys (keyed : List (BLSPubkey × SyncCommitteeMessage))
    (pubkeys : List BLSPubkey) :
    (contributionEntries keyed pubkeys).map Prod.fst =
      (pubkeys.zip (pubkeys.map fun pubkey => keyed.any (·.1 = pubkey))).filterMap
        (fun (pubkey, bit) => if bit then some pubkey else none) := by
  induction pubkeys with
  | nil => rfl
  | cons pubkey pubkeys ih =>
    have foundSome := List.isSome_find? (xs := keyed) (f := fun entry => decide (entry.1 = pubkey))
    cases found : keyed.find? (·.1 = pubkey) with
    | none =>
      have absent : keyed.any (·.1 = pubkey) = false := by simpa [found] using foundSome.symm
      simpa [contributionEntries, found, absent] using ih
    | some entry =>
      have present : keyed.any (·.1 = pubkey) = true := by simpa [found] using foundSome.symm
      have same : entry.1 = pubkey := by simpa using List.find?_some found
      simpa [contributionEntries, found, present, same] using congrArg (pubkey :: ·) ih

/-- Every entry selected for a seat came from the registry lookup. -/
private theorem mem_keyed_of_mem_contributionEntries
    {keyed : List (BLSPubkey × SyncCommitteeMessage)} {pubkeys : List BLSPubkey}
    {entry : BLSPubkey × SyncCommitteeMessage}
    (member : entry ∈ contributionEntries keyed pubkeys) : entry ∈ keyed := by
  obtain ⟨pubkey, _, found⟩ := List.mem_filterMap.mp member
  exact List.mem_of_find?_eq_some found

/-- Mapping the selected entries is the same as selecting their images. -/
private theorem map_selected {α β : Type} (entries : List (α × Bool)) (f : α → β) :
    (entries.filterMap (fun (value, bit) => if bit then some value else none)).map f =
      entries.filterMap (fun (value, bit) => if bit then some (f value) else none) := by
  rw [List.map_filterMap]
  congr 1
  funext entry
  rcases entry with ⟨value, bit⟩
  cases bit <;> rfl

/-- Selected registry messages verify under their keys in seat order. -/
private theorem contributionEntries_verify
    (keyed : List (BLSPubkey × SyncCommitteeMessage)) (pubkeys : List BLSPubkey)
    (secret : BLSPubkey → Signatures.SecretKey) (message : ByteArray)
    (honest : ∀ entry ∈ keyed,
      entry.1 = Signatures.skToPk (secret entry.1) ∧
        Signatures.sign (secret entry.1) message = .ok entry.2.signature)
    {signature : BLSSignature}
    (aggregated : Signatures.aggregate
      ((contributionEntries keyed pubkeys).map fun entry =>
        Base.packBytes entry.2.signature).toArray =
        .ok signature)
    (nonzero : (((contributionEntries keyed pubkeys).map fun entry => secret entry.1).map
      (·.val)).sum ≠ 0) :
    Signatures.fastAggregateVerify
      (((contributionEntries keyed pubkeys).map Prod.fst).map Base.packBytes).toArray message
      (Base.packBytes signature) = true := by
  have signed : List.Forall₂ (fun key sig => Signatures.sign key message = .ok sig)
      ((contributionEntries keyed pubkeys).map fun entry => secret entry.1)
      ((contributionEntries keyed pubkeys).map fun entry => entry.2.signature) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro entry member
    exact (honest entry (mem_keyed_of_mem_contributionEntries member)).2
  have nonempty : (contributionEntries keyed pubkeys).map (fun entry => secret entry.1) ≠ [] := by
    intro empty
    simp [empty] at nonzero
  have verifies := Signatures.fastAggregateVerify_aggregate_of_forall₂ signed nonempty nonzero
    (by simpa [List.map_map, Signatures.sigBytes, Base.packBytes, Function.comp_def]
      using aggregated)
  have keys : (((contributionEntries keyed pubkeys).map fun entry => secret entry.1).map
      Signatures.pkBytes) =
      ((contributionEntries keyed pubkeys).map Prod.fst).map Base.packBytes := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro entry member
    exact congrArg Base.packBytes
      (honest entry (mem_keyed_of_mem_contributionEntries member)).1.symm
  simpa only [keys, Signatures.sigBytes, Base.packBytes] using verifies

/-- A contribution of honest messages passes the signature check of its topic.

Each message on the block root at the state's slot signs the signing root.

It signs with the secret key behind the registered public key of its validator.

The selected secret keys, counted once per set seat, must not sum to zero.

The check reads the same subcommittee keys as the construction. -/
theorem isValidContributionSignature_constructSyncCommitteeContribution
    {config : Config} {state : BeaconState preset fork} {committee : SyncCommittee preset}
    {blockRoot : Root} {subcommitteeIndex : UInt64} {messages : List SyncCommitteeMessage}
    {contribution : SyncCommitteeContribution preset} {domain : Domain} {signingRoot : Root}
    (secret : BLSPubkey → Signatures.SecretKey)
    (built : constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex
      messages = .ok contribution)
    (domained : getDomain config state DOMAIN_SYNC_COMMITTEE
      (some (computeEpochAtSlot preset state.slot)) = .ok domain)
    (rooted : computeSigningRoot blockRoot domain = .ok signingRoot)
    (honest : ∀ message ∈ messages, message.slot = state.slot →
      message.beaconBlockRoot = blockRoot → ∀ validator,
      getValidator state message.validatorIndex = .ok validator →
        validator.pubkey = Signatures.skToPk (secret validator.pubkey) ∧
          Signatures.sign (secret validator.pubkey) (Base.packBytes signingRoot) =
            .ok message.signature)
    (nonzero : ((((syncSubcommitteePubkeys committee subcommitteeIndex.toNat).zip
        contribution.aggregationBits.bits.toList).filterMap
        (fun (pubkey, bit) => if bit then some (secret pubkey) else none)).map (·.val)).sum ≠ 0) :
    isValidContributionSignature config .bls state
      (syncSubcommitteePubkeys committee subcommitteeIndex.toNat) contribution = .ok true := by
  unfold constructSyncCommitteeContribution at built
  split at built
  · rename_i inRange
    dsimp only at built
    split at built
    · simp [throw, throwThe, MonadExceptOf.throw] at built
    obtain ⟨keyed, keyedOk, built⟩ := bind_ok_iff.mp built
    split at built
    · simp [throw, throwThe, MonadExceptOf.throw] at built
    obtain ⟨signature, aggregated, built⟩ := bind_ok_iff.mp built
    simp only [pure, Except.pure, Except.ok.injEq] at built
    subst built
    let pubkeys := syncSubcommitteePubkeys committee subcommitteeIndex.toNat
    have pubkeysEq := syncSubcommitteePubkeys_eq_map (committee := committee) inRange
    have bitsEq :
        (Vector.ofFn fun seat : Fin (syncSubcommitteeSize preset) =>
          keyed.any (·.1 = syncSubcommitteeKey committee subcommitteeIndex inRange seat)).toList =
        pubkeys.map (fun pubkey => keyed.any (·.1 = pubkey)) := by
      rw [show pubkeys = _ from pubkeysEq]
      simp [Vector.toList_ofFn, List.finRange, List.map_ofFn, Function.comp_def]
    have entriesHonest : ∀ entry ∈ keyed,
        entry.1 = Signatures.skToPk (secret entry.1) ∧
          Signatures.sign (secret entry.1) (Base.packBytes signingRoot) =
            .ok entry.2.signature := by
      rintro ⟨pubkey, message⟩ member
      obtain ⟨original, originalMember, read⟩ := mapM_ok_mem keyedOk _ member
      obtain ⟨validator, found, read⟩ := bind_ok_iff.mp read
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      have sameMessage := List.mem_filter.mp originalMember
      exact honest original sameMessage.1 (of_decide_eq_true sameMessage.2).1
        (of_decide_eq_true sameMessage.2).2 validator (mapError_ok_iff.mp found)
    have aggregated' : Signatures.aggregate
        ((contributionEntries keyed pubkeys).map fun entry =>
          Base.packBytes entry.2.signature).toArray = .ok signature := by
      rw [mapError_ok_iff] at aggregated
      simpa only [contributionEntries, pubkeys, pubkeysEq, List.map_filterMap,
        List.filterMap_map, Function.comp_def] using aggregated
    have selected :
        (contributionEntries keyed pubkeys).map (fun entry => secret entry.1) =
        (pubkeys.zip (pubkeys.map fun pubkey => keyed.any (·.1 = pubkey))).filterMap
          (fun (pubkey, bit) => if bit then some (secret pubkey) else none) := by
      calc
        _ = ((contributionEntries keyed pubkeys).map Prod.fst).map secret := by
          simp [List.map_map]
        _ = _ := by rw [contributionEntries_keys, map_selected]
    have nonzero' : (((contributionEntries keyed pubkeys).map fun entry => secret entry.1).map
        (·.val)).sum ≠ 0 := by
      rw [selected]
      simpa only [bitsEq] using nonzero
    have verifies := contributionEntries_verify keyed pubkeys secret (Base.packBytes signingRoot)
      entriesHonest aggregated' nonzero'
    have participants :
        (pubkeys.zip (pubkeys.map fun pubkey => keyed.any (·.1 = pubkey))).filterMap
          (fun entry => if entry.2 then some (Base.packBytes entry.1) else none) =
        ((contributionEntries keyed pubkeys).map Prod.fst).map Base.packBytes := by
      have projection :
          (fun entry : BLSPubkey × Bool =>
            if entry.2 then some (Base.packBytes entry.1) else none) =
          (fun (pubkey, bit) => if bit then some (Base.packBytes pubkey) else none) := by
        funext entry
        cases entry
        rfl
      rw [projection]
      rw [← map_selected, ← contributionEntries_keys]
    simp only [isValidContributionSignature, domained, rooted, Except.mapError, bind,
      Except.bind, pure, Except.pure]
    apply congrArg (Except.ok (ε := ForkChoiceError))
    unfold syncAggregateVerify
    dsimp only [pubkeys] at participants verifies bitsEq
    simp only [bitsEq, participants, SignatureChecks.bls, verifies, Bool.or_true]
  · simp [throw, throwThe, MonadExceptOf.throw] at built

/-- A nonzero sum over selected keys needs at least one set bit. -/
private theorem any_of_nonzero_selected (pubkeys : List BLSPubkey) (bits : List Bool)
    (secret : BLSPubkey → Signatures.SecretKey)
    (nonzero : (((pubkeys.zip bits).filterMap
      (fun (pubkey, bit) => if bit then some (secret pubkey) else none)).map (·.val)).sum ≠ 0) :
    bits.any id = true := by
  have nonempty : (pubkeys.zip bits).filterMap
      (fun (pubkey, bit) => if bit then some (secret pubkey) else none) ≠ [] := by
    intro empty
    simp [empty] at nonzero
  obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨⟨pubkey, bit⟩, seated, chosen⟩ := List.mem_filterMap.mp member
  have set : bit = true := by cases bit <;> simp_all
  exact List.any_eq_true.mpr ⟨bit, (List.of_mem_zip seated).2, set⟩

/-- An honest contribution passes its aggregate-signature gate on the contribution topic.

The topic accepts it exactly when the remaining checks pass.

The clock, head state, committee and aggregator signature computations must succeed.

The subnet range and the nonempty participation checks pass with no further hypothesis. -/
theorem validateContributionAndProof_eq_accept_of_construct
    {config : Config} {state : BeaconState preset fork} {committee : SyncCommittee preset}
    {blockRoot : Root} {subcommitteeIndex : UInt64} {messages : List SyncCommitteeMessage}
    {signed : SignedContributionAndProof preset} {domain : Domain} {signingRoot : Root}
    {seen : Seen} {store : Store preset fork} {altair : .altair ≤ fork}
    {currentTimeMs : UInt64} {current selected signedByAggregator : Bool} {aggregator : Validator}
    (secret : BLSPubkey → Signatures.SecretKey)
    (built : constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex
      messages = .ok signed.message.contribution)
    (domained : getDomain config state DOMAIN_SYNC_COMMITTEE
      (some (computeEpochAtSlot preset state.slot)) = .ok domain)
    (rooted : computeSigningRoot blockRoot domain = .ok signingRoot)
    (honest : ∀ message ∈ messages, message.slot = state.slot →
      message.beaconBlockRoot = blockRoot → ∀ validator,
      getValidator state message.validatorIndex = .ok validator →
        validator.pubkey = Signatures.skToPk (secret validator.pubkey) ∧
          Signatures.sign (secret validator.pubkey) (Base.packBytes signingRoot) =
            .ok message.signature)
    (nonzero : ((((syncSubcommitteePubkeys committee subcommitteeIndex.toNat).zip
        signed.message.contribution.aggregationBits.bits.toList).filterMap
        (fun (pubkey, bit) => if bit then some (secret pubkey) else none)).map (·.val)).sum ≠ 0)
    (clock : store.isCurrentSlot config signed.message.contribution.slot currentTimeMs =
      .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (members : getSyncSubcommitteePubkeys state altair
      signed.message.contribution.subcommitteeIndex =
        .ok (syncSubcommitteePubkeys committee subcommitteeIndex.toNat))
    (selection : isValidSignatureAtSlot config .bls state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
      signed.message.contribution.slot
      (SyncAggregatorSelectionData.mk signed.message.contribution.slot
        signed.message.contribution.subcommitteeIndex)
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (bySigner : isValidSignatureAtSlot config .bls state DOMAIN_CONTRIBUTION_AND_PROOF
      signed.message.contribution.slot signed.message aggregator.pubkey signed.signature =
        .ok signedByAggregator) :
    validateContributionAndProof config .bls seen store altair signed currentTimeMs = .ok .accept ↔
      isNonStrictSuperset (seen.contributionBits
          (signed.message.contribution.slot, signed.message.contribution.beaconBlockRoot,
            signed.message.contribution.subcommitteeIndex))
          signed.message.contribution.aggregationBits.bits.toList = false ∧
        (signed.message.contribution.slot, signed.message.aggregatorIndex,
          signed.message.contribution.subcommitteeIndex) ∉ seen.syncContributionAggregatorKeys ∧
        current = true ∧ isSyncCommitteeAggregator preset signed.message.selectionProof = true ∧
        aggregator.pubkey ∈ syncSubcommitteePubkeys committee subcommitteeIndex.toNat ∧
        selected = true ∧ signedByAggregator = true := by
  have participants := isValidContributionSignature_constructSyncCommitteeContribution
    secret built domained rooted honest nonzero
  obtain ⟨inRange, _, _, sameIndex, _⟩ := constructSyncCommitteeContribution_spec built
  have inside : signed.message.contribution.subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT :=
    sameIndex ▸ inRange
  have bitsSet := any_of_nonzero_selected
    (syncSubcommitteePubkeys committee subcommitteeIndex.toNat)
    signed.message.contribution.aggregationBits.bits.toList secret nonzero
  rw [validateContributionAndProof_eq_accept clock head found members selection bySigner
    participants]
  simp only [inside, bitsSet, and_true, true_and]

/-- An honest contribution and proof is accepted on its topic exactly when the other checks pass.

The aggregator makes it from the contribution and signs it.

It uses the secret key behind its registered public key.

It signs with the head state of the receiver.

Its selection proof and its signature then pass their checks with no further hypothesis.

The clock, head state, domain, signing root and committee computations must succeed. -/
theorem validateContributionAndProof_eq_accept_of_getContributionAndProof
    {config : Config} {state : BeaconState preset fork} {committee : SyncCommittee preset}
    {blockRoot : Root} {subcommitteeIndex : UInt64} {messages : List SyncCommitteeMessage}
    {signed : SignedContributionAndProof preset} {domain : Domain} {signingRoot : Root}
    {seen : Seen} {store : Store preset fork} {altair : .altair ≤ fork}
    {currentTimeMs : UInt64} {current : Bool} {aggregator : Validator}
    {key : Signatures.SecretKey} (secret : BLSPubkey → Signatures.SecretKey)
    (built : constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex
      messages = .ok signed.message.contribution)
    (domained : getDomain config state DOMAIN_SYNC_COMMITTEE
      (some (computeEpochAtSlot preset state.slot)) = .ok domain)
    (rooted : computeSigningRoot blockRoot domain = .ok signingRoot)
    (honest : ∀ message ∈ messages, message.slot = state.slot →
      message.beaconBlockRoot = blockRoot → ∀ validator,
      getValidator state message.validatorIndex = .ok validator →
        validator.pubkey = Signatures.skToPk (secret validator.pubkey) ∧
          Signatures.sign (secret validator.pubkey) (Base.packBytes signingRoot) =
            .ok message.signature)
    (nonzero : ((((syncSubcommitteePubkeys committee subcommitteeIndex.toNat).zip
        signed.message.contribution.aggregationBits.bits.toList).filterMap
        (fun (pubkey, bit) => if bit then some (secret pubkey) else none)).map (·.val)).sum ≠ 0)
    (clock : store.isCurrentSlot config signed.message.contribution.slot currentTimeMs =
      .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (owned : aggregator.pubkey = Signatures.skToPk key)
    (members : getSyncSubcommitteePubkeys state altair
      signed.message.contribution.subcommitteeIndex =
        .ok (syncSubcommitteePubkeys committee subcommitteeIndex.toNat))
    (made : getContributionAndProof config state signed.message.aggregatorIndex
      signed.message.contribution key = .ok signed.message)
    (signedBy : getContributionAndProofSignature config state signed.message key =
      .ok signed.signature) :
    validateContributionAndProof config .bls seen store altair signed currentTimeMs = .ok .accept ↔
      isNonStrictSuperset (seen.contributionBits
          (signed.message.contribution.slot, signed.message.contribution.beaconBlockRoot,
            signed.message.contribution.subcommitteeIndex))
          signed.message.contribution.aggregationBits.bits.toList = false ∧
        (signed.message.contribution.slot, signed.message.aggregatorIndex,
          signed.message.contribution.subcommitteeIndex) ∉ seen.syncContributionAggregatorKeys ∧
        current = true ∧ isSyncCommitteeAggregator preset signed.message.selectionProof = true ∧
        aggregator.pubkey ∈ syncSubcommitteePubkeys committee subcommitteeIndex.toNat := by
  have selection := (getContributionAndProof_spec made).2.2
  have bySigner := isValidSignatureAtSlot_getContributionAndProofSignature signedBy
  rw [← owned] at selection bySigner
  rw [validateContributionAndProof_eq_accept_of_construct secret built domained rooted honest
    nonzero clock head found members selection bySigner]
  simp only [and_true]

end EthLib.Consensus
