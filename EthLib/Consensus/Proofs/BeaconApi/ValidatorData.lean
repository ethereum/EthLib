module

public import EthLib.Consensus.BeaconApi.ValidatorData
public import EthLib.Consensus.Proofs.HonestAggregateSignatures
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the data that the Beacon API hands a validator

The attestation data votes for the head of the store, at the requested slot.

For a store in Electra or Fulu its index is 0.

An aggregate has the requested data root, slot and committee, and joins the messages that match.

An aggregate of distinct honest signers passes the check of an indexed attestation.

It needs each signer's key in the registry, and secret keys that do not sum to zero.

A bit of a contribution is set exactly when the key of that seat signed a matching message.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-! ## Attestation data -/

/-- The state taken to a slot is at that slot. -/
theorem stateAtSlot_slot {config : Config} {state after : BeaconState preset fork} {slot : Slot}
    (computed : stateAtSlot config state slot = .ok after) : after.slot = slot := by
  unfold stateAtSlot at computed
  split_ifs at computed with below same
  · simp [Except.ok.injEq] at computed; subst computed; exact same.symm
  · obtain ⟨_, advanced⟩ := processSlots_slot (mapError_ok_iff.mp computed)
    exact advanced

/-- A produced attestation data comes from the head state taken to the slot. -/
private theorem produceAttestationData_spec {config : Config} {store : Store preset fork}
    {optimistic : OptimisticStore preset fork} {slot : Slot} {committeeIndex : CommitteeIndex}
    {data : AttestationData}
    (produced : produceAttestationData config store optimistic slot committeeIndex = .ok data) :
    ∃ (head : ForkChoiceNode) (blockSlot : Slot) (state : BeaconState preset fork),
      store.getHead config = .ok head ∧
      isExecutionOptimistic optimistic head.root = false ∧
      getAttestationData state head.root blockSlot committeeIndex head.payloadStatus =
        .ok data ∧ state.slot = slot := by
  unfold produceAttestationData at produced
  simp only [bind_ok_iff] at produced
  obtain ⟨head, got, produced⟩ := produced
  cases hb : store.blocks[head.root]? with
  | none => simp [hb] at produced
  | some block =>
    cases hs : store.blockStates[head.root]? with
    | none => simp [hb, hs] at produced
    | some headState =>
      simp only [hb, hs, bind_ok_iff, checkVerified] at produced
      obtain ⟨_, checked, current, _, produced⟩ := produced
      by_cases late : current < slot
      · simp [late, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at produced
      simp only [late, ite_false, bind_ok_iff] at produced
      obtain ⟨state, atSlot, built⟩ := produced
      refine ⟨head, block.slot, state, mapError_ok_iff.mp got, ?_, mapError_ok_iff.mp built,
        stateAtSlot_slot atSlot⟩
      cases h : isExecutionOptimistic optimistic head.root <;> simp [h] at checked ⊢

/-- The attestation data names the head of the store, at the requested slot.

The payload of the head block is verified. -/
theorem produceAttestationData_head {config : Config} {store : Store preset fork}
    {optimistic : OptimisticStore preset fork} {slot : Slot} {committeeIndex : CommitteeIndex}
    {data : AttestationData}
    (produced : produceAttestationData config store optimistic slot committeeIndex = .ok data) :
    ∃ head, store.getHead config = .ok head ∧ data.beaconBlockRoot = head.root ∧
      isExecutionOptimistic optimistic head.root = false ∧ data.slot = slot := by
  obtain ⟨head, blockSlot, state, got, verified, made, same⟩ := produceAttestationData_spec produced
  obtain ⟨-, -, slotOf, rootOf, -⟩ := getAttestationData_eq_ok_iff.mp made
  exact ⟨head, got, rootOf, verified, by rw [slotOf, same]⟩

/-- For a store in Electra or Fulu, the index of the attestation data is 0.

The store holds one fork, so a slot of a later fork is answered under the rule of the store. -/
theorem produceAttestationData_index {config : Config} {store : Store preset fork}
    {optimistic : OptimisticStore preset fork} {slot : Slot} {committeeIndex : CommitteeIndex}
    {data : AttestationData} (electra : .pectra ≤ fork) (beforeGloas : fork < .glamsterdam)
    (produced : produceAttestationData config store optimistic slot committeeIndex = .ok data) :
    data.index = 0 := by
  obtain ⟨_, _, _, _, _, made, _⟩ := produceAttestationData_spec produced
  obtain ⟨indexed, _⟩ := getAttestationData_eq_ok_iff.mp made
  rw [attestationDataIndex_of_pectra_of_lt_glamsterdam electra beforeGloas] at indexed
  exact (Except.ok.inj indexed).symm

/-- The payload attestation data names the block of its slot on the chain of the head.

It holds the slot and the two flags given. -/
theorem producePayloadAttestationData_block {config : Config} {store : Store preset fork}
    {slot : Slot} {payloadPresent blobDataAvailable : Bool} {data : PayloadAttestationData}
    (produced : producePayloadAttestationData config store slot payloadPresent blobDataAvailable =
      .ok (some data)) :
    ∃ head, headRoot config store = some head ∧
      blockAtSlot store head slot = some data.beaconBlockRoot ∧ data.slot = slot ∧
      data.payloadPresent = payloadPresent ∧ data.blobDataAvailable = blobDataAvailable := by
  unfold producePayloadAttestationData at produced
  by_cases gloas : .glamsterdam ≤ fork
  swap
  · simp [gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at produced
  cases hr : headRoot config store with
  | none => simp [gloas, hr] at produced
  | some head =>
    cases hb : blockAtSlot store head slot with
    | none => simp [gloas, hr, hb, pure, Except.pure] at produced
    | some root =>
      simp [gloas, hr, hb, pure, Except.pure] at produced
      subst produced
      exact ⟨head, rfl, hb, rfl, rfl, rfl⟩

/-! ## Aggregates -/

/-- Before Electra, a built aggregate comes from the first matching attestation. -/
private theorem aggregateAttestation_lt {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (before : fork < .pectra)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    ∃ first, attestations.find? (matchesRequest · dataRoot slot committeeIndex) = some first ∧
      isExecutionOptimistic optimistic first.data.beaconBlockRoot = false ∧
      constructAggregate state before first.data attestations = .ok aggregate := by
  unfold aggregateAttestation at built
  simp only [before, ↓reduceDIte] at built
  cases found : attestations.find? (matchesRequest · dataRoot slot committeeIndex) with
  | none => simp [found] at built
  | some first =>
    rw [found] at built
    simp only [bind_ok_iff, checkVerified] at built
    obtain ⟨_, checked, built⟩ := built
    refine ⟨first, rfl, ?_, mapError_ok_iff.mp built⟩
    cases h : isExecutionOptimistic optimistic first.data.beaconBlockRoot <;>
      simp [h] at checked ⊢

/-- From Electra, a built aggregate comes from the first matching single attestation. -/
private theorem aggregateAttestation_ge {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (electra : .pectra ≤ fork)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    ∃ first, singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) = some first ∧
      isExecutionOptimistic optimistic first.data.beaconBlockRoot = false ∧
      constructAggregateOfSingleAttestations state first.data committeeIndex singles =
        .ok aggregate := by
  unfold aggregateAttestation at built
  have notBefore : ¬ fork < .pectra := fun h => Nat.not_le_of_lt h electra
  simp only [notBefore, ↓reduceDIte] at built
  cases found : singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) with
  | none => simp [found] at built
  | some first =>
    rw [found] at built
    simp only [bind_ok_iff, checkVerified] at built
    obtain ⟨_, checked, built⟩ := built
    refine ⟨first, rfl, ?_, mapError_ok_iff.mp built⟩
    cases h : isExecutionOptimistic optimistic first.data.beaconBlockRoot <;>
      simp [h] at checked ⊢

/-- An aggregate has the requested data root and slot, and its block is verified. -/
theorem aggregateAttestation_matching {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    hasRoot aggregate.data dataRoot = true ∧ aggregate.data.slot = slot ∧
      isExecutionOptimistic optimistic aggregate.data.beaconBlockRoot = false := by
  by_cases before : fork < .pectra
  · obtain ⟨first, found, verified, made⟩ := aggregateAttestation_lt before built
    have matched := List.find?_some found
    obtain ⟨_, _, _, _, _, sameData, _⟩ := constructAggregate_spec made
    simp only [matchesRequest, Bool.and_eq_true, beq_iff_eq] at matched
    rw [sameData]
    exact ⟨matched.1.1, matched.1.2, verified⟩
  · obtain ⟨first, found, verified, made⟩ :=
      aggregateAttestation_ge (Nat.not_lt.mp before) built
    have matched := List.find?_some found
    obtain ⟨_, _, _, _, _, sameData, _, _⟩ :=
      constructAggregateOfSingleAttestations_spec made
    simp only [singleMatchesRequest, Bool.and_eq_true, beq_iff_eq] at matched
    rw [sameData]
    exact ⟨matched.1.1, matched.1.2, verified⟩

/-- Before Electra, an aggregate is the honest aggregate of the attestations with its data.

That data has the requested committee index. -/
theorem aggregateAttestation_construct_of_lt_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (before : fork < .pectra)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    aggregate.data.index = committeeIndex ∧
      constructAggregate state before aggregate.data attestations = .ok aggregate := by
  obtain ⟨first, found, _, made⟩ := aggregateAttestation_lt before built
  have matched := List.find?_some found
  obtain ⟨_, _, _, _, _, sameData, _⟩ := constructAggregate_spec made
  simp only [matchesRequest, Bool.and_eq_true, beq_iff_eq] at matched
  rw [sameData]
  exact ⟨matched.2, made⟩

/-- From Electra, an aggregate is the honest aggregate of the single attestations with its data. -/
theorem aggregateAttestation_construct_of_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (electra : .pectra ≤ fork)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    constructAggregateOfSingleAttestations state aggregate.data committeeIndex singles =
      .ok aggregate := by
  obtain ⟨first, _, _, made⟩ := aggregateAttestation_ge electra built
  obtain ⟨_, _, _, _, _, sameData, _, _⟩ := constructAggregateOfSingleAttestations_spec made
  rw [sameData]
  exact made

/-- Before Electra, an aggregate sets a bit exactly when an attestation with its data sets it.

The aggregate and each such attestation have one bit for each member of the committee. -/
theorem aggregateAttestation_bits_of_lt_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (before : fork < .pectra)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    ∃ committee, getBeaconCommittee state aggregate.data.slot committeeIndex = .ok committee ∧
      (∀ attestation ∈ attestations, attestation.data = aggregate.data →
        attestation.aggregationBits.bits.size = committee.size) ∧
      aggregate.aggregationBits.bits.size = committee.size ∧
      ∀ seat < committee.size, aggregate.aggregationBits.bits.getD seat false = true ↔
        ∃ attestation ∈ attestations, attestation.data = aggregate.data ∧
          attestation.aggregationBits.bits.getD seat false = true := by
  obtain ⟨sameIndex, made⟩ := aggregateAttestation_construct_of_lt_electra before built
  obtain ⟨committee, got, _, sizes, bits, _, _⟩ := constructAggregate_spec made
  rw [sameIndex] at got
  refine ⟨committee, got,
    fun a ha h => sizes a (List.mem_filter.2 ⟨ha, by simpa using h⟩),
    by simp [bits], fun seat below => ?_⟩
  simp [bits, below, Array.getD_eq_getD_getElem?]

/-- From Electra, the attesters of an aggregate are those of the matching single attestations.

A single attestation matches when it has the data of the aggregate and the requested committee. -/
theorem aggregateAttestation_attesters_of_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (electra : .pectra ≤ fork)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    ∃ indices, getAttestingIndices state aggregate = .ok indices ∧
      ∀ validatorIndex, validatorIndex ∈ indices ↔
        ∃ single ∈ singles, single.data = aggregate.data ∧
          single.committeeIndex = committeeIndex ∧ single.attesterIndex = validatorIndex := by
  exact mem_getAttestingIndices_constructAggregateOfSingleAttestations electra
    (aggregateAttestation_construct_of_electra electra built)

/-- From Electra, the committee bits of an aggregate mark the requested committee alone. -/
theorem aggregateAttestation_committeeBits_of_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {aggregate : Attestation preset fork}
    (electra : .pectra ≤ fork)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate) :
    getCommitteeIndices (aggregate.committeeBits electra) = [committeeIndex] :=
  getCommitteeIndices_constructAggregateOfSingleAttestations electra
    (aggregateAttestation_construct_of_electra electra built)

/-- Before Electra, an aggregate of distinct honest attesters passes its indexed check.

The registry must hold each signer's public key, and their secret keys must not sum to zero. -/
theorem aggregateAttestation_valid_of_lt_electra {config : Config}
    {state : BeaconState preset fork} {optimistic : OptimisticStore preset fork}
    {attestations : List (Attestation preset fork)} {singles : List SingleAttestation}
    {dataRoot : Root} {slot : Slot} {committeeIndex : CommitteeIndex}
    {aggregate : Attestation preset fork} {signers : List ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} (before : fork < .pectra)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate)
    (honest : List.Forall₂ (fun index attestation =>
      constructAttestation config state before aggregate.data index (key index) = .ok attestation)
        signers (attestations.filter (·.data = aggregate.data)))
    (distinct : signers.Nodup)
    (registered : ∀ index ∈ signers, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : ((signers.map key).map (·.val)).sum ≠ 0) :
    ∃ indexed, getIndexedAttestation state aggregate = .ok indexed ∧
      isValidIndexedAttestation config .bls state indexed = .ok true := by
  exact isValidIndexedAttestation_constructAggregate honest distinct registered sum
    (aggregateAttestation_construct_of_lt_electra before built).2

/-- From Electra, an aggregate of distinct honest single attesters passes its indexed check.

The registry must hold each signer's public key, and their secret keys must not sum to zero.

From Gloas, the number of signers must fit the bound of the check. -/
theorem aggregateAttestation_valid_of_electra {config : Config}
    {state : BeaconState preset fork} {optimistic : OptimisticStore preset fork}
    {attestations : List (Attestation preset fork)} {singles : List SingleAttestation}
    {dataRoot : Root} {slot : Slot} {committeeIndex : CommitteeIndex}
    {aggregate : Attestation preset fork} {signers : List ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} (electra : .pectra ≤ fork)
    (built : aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .ok aggregate)
    (honest : List.Forall₂ (fun index single =>
      constructSingleAttestation config state aggregate.data committeeIndex index (key index) =
        .ok single)
        signers (singles.filter fun single =>
          single.data = aggregate.data ∧ single.committeeIndex = committeeIndex))
    (distinct : signers.Nodup)
    (registered : ∀ index ∈ signers, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : ((signers.map key).map (·.val)).sum ≠ 0)
    (bounded : .glamsterdam ≤ fork → signers.length ≤ maxAttesters preset fork) :
    ∃ indexed, getIndexedAttestation state aggregate = .ok indexed ∧
      isValidIndexedAttestation config .bls state indexed = .ok true := by
  exact isValidIndexedAttestation_constructAggregateOfSingleAttestations electra honest distinct
    registered sum bounded (aggregateAttestation_construct_of_electra electra built)

/-! ## Sync committee contributions -/

/-- From Altair, a bit of a contribution is set exactly when a member of that seat sent a message.

The message must be of the requested slot and root, from a validator with the key of the seat.

The seat is one of the sync committee of the next slot, and the root is verified. -/
theorem produceSyncCommitteeContribution_bits {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {optimistic : OptimisticStore preset fork}
    {messages : List SyncCommitteeMessage} {slot : Slot} {subcommitteeIndex : UInt64}
    {root : Root} {contribution : SyncCommitteeContribution preset}
    (produced : produceSyncCommitteeContribution state altair optimistic messages slot
      subcommitteeIndex root = .ok contribution) :
    ∃ committee, syncCommitteeAtNextSlot state altair = .ok committee ∧
      ∃ inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT,
        isExecutionOptimistic optimistic root = false ∧
        contribution.slot = slot ∧ contribution.beaconBlockRoot = root ∧
        contribution.subcommitteeIndex = subcommitteeIndex ∧
        ∀ seat : Fin (syncSubcommitteeSize preset),
          contribution.aggregationBits.bits[seat.val] = true ↔
          ∃ message ∈ messages, message.slot = slot ∧ message.beaconBlockRoot = root ∧
            ∃ validator, getValidator state message.validatorIndex = .ok validator ∧
              validator.pubkey = syncSubcommitteeKey committee subcommitteeIndex inRange seat := by
  unfold produceSyncCommitteeContribution at produced
  by_cases same : slot = state.slot
  swap
  · simp [same, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at produced
  subst same
  by_cases inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT
  swap
  · simp [inRange, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at produced
  simp only [inRange, ite_true, bind_ok_iff, checkVerified] at produced
  obtain ⟨_, checked, committee, got, built⟩ := produced
  refine ⟨committee, mapError_ok_iff.mp got, inRange, ?_⟩
  cases built' : constructSyncCommitteeContribution state committee root subcommitteeIndex
    (messages.filter (inSubcommittee state (syncSubcommitteePubkeys committee
      subcommitteeIndex.toNat))) with
  | error fault => cases fault <;> simp [built', throw, throwThe, MonadExceptOf.throw] at built
  | ok c =>
    simp [built', pure, Except.pure] at built
    subst built
    obtain ⟨_, h1, h2, h3, h4⟩ := constructSyncCommitteeContribution_spec built'
    refine ⟨?_, h1, h2, h3, fun seat => (h4 seat).trans ⟨fun ⟨m, hm, rest⟩ => ?_, ?_⟩⟩
    · cases h : isExecutionOptimistic optimistic root <;> simp [h] at checked ⊢
    · exact ⟨m, (List.mem_filter.mp hm).1, rest⟩
    · rintro ⟨m, hm, hslot, hroot, validator, got, key⟩
      refine ⟨m, List.mem_filter.mpr ⟨hm, ?_⟩, hslot, hroot, validator, got, key⟩
      simp only [inSubcommittee, got, List.contains_iff_mem]
      rw [key]
      exact List.getElem_mem _

end EthLib.Consensus.BeaconApi
