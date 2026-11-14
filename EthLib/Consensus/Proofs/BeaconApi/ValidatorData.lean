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

Each refusal of an aggregate or a contribution with a code other than 500 is stated with its cause.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-! ## Errors -/

/-- After the check of a block, an answer refuses with a code in two cases only.

It refuses an optimistic block with code 503.

For a verified block, it refuses with a code exactly when the rest of the answer does. -/
theorem checkVerified_bind_error_iff {α : Type} {optimistic : OptimisticStore preset fork}
    {root : Root} {rest : Unit → Except ErrorMessage α} {code : Nat} :
    (∃ error, (checkVerified optimistic root >>= rest) = .error error ∧ error.code = code) ↔
      isExecutionOptimistic optimistic root = true ∧ code = 503 ∨
        isExecutionOptimistic optimistic root = false ∧
          ∃ error, rest () = .error error ∧ error.code = code := by
  unfold checkVerified
  cases isExecutionOptimistic optimistic root <;>
    simp [optimisticBlock, bind, Except.bind, eq_comm]

/-- A failed construction refuses with a code other than 500 only for an index out of range.

That refusal has code 400.

It needs a code other than 500, the code of an internal error. -/
private theorem mapError_constructionError_iff {β : Type} {built : Except ValidatorDutyError β}
    {code : Nat} (notInternal : code ≠ 500) :
    (∃ error, built.mapError constructionError = .error error ∧ error.code = code) ↔
      code = 400 ∧ ∃ index limit, built = .error (.indexOutOfRange index limit) := by
  constructor
  · rintro ⟨error, failed, rfl⟩
    obtain ⟨fault, rfl, rfl⟩ := mapError_eq_error_iff.mp failed
    cases fault <;> simp_all [constructionError, internalError]
  · rintro ⟨rfl, index, limit, rfl⟩
    exact ⟨_, rfl, rfl⟩

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

/-- Before Electra, the construction of an aggregate never fails for an index out of range. -/
private theorem constructAggregate_ne_indexOutOfRange {state : BeaconState preset fork}
    {before : fork < .pectra} {data : AttestationData}
    {attestations : List (Attestation preset fork)} {index limit : UInt64} :
    constructAggregate state before data attestations ≠ .error (.indexOutOfRange index limit) := by
  intro failed
  unfold constructAggregate at failed
  split at failed
  · simp [throw, throwThe, MonadExceptOf.throw] at failed
  rcases bind_eq_error failed with failed | ⟨committee, -, failed⟩
  · obtain ⟨_, -, mapped⟩ := mapError_eq_error_iff.mp failed
    cases mapped
  split at failed
  · simp [throw, throwThe, MonadExceptOf.throw] at failed
  dsimp only at failed
  rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
  · obtain ⟨_, -, mapped⟩ := mapError_eq_error_iff.mp failed
    cases mapped
  · simp [pure, Except.pure] at failed

/-- An aggregate of single attestations fails for an index out of range in one case only.

That case is a committee index not below the most committees a slot can have. -/
private theorem constructAggregateOfSingleAttestations_indexOutOfRange_iff
    {state : BeaconState preset fork} {data : AttestationData} {committeeIndex : CommitteeIndex}
    {singles : List SingleAttestation} :
    (∃ index limit, constructAggregateOfSingleAttestations state data committeeIndex singles =
      .error (.indexOutOfRange index limit)) ↔
      preset.MAX_COMMITTEES_PER_SLOT ≤ committeeIndex := by
  unfold constructAggregateOfSingleAttestations
  by_cases inside : committeeIndex < preset.MAX_COMMITTEES_PER_SLOT
  swap
  · simp [inside, throw, throwThe, MonadExceptOf.throw]
    exact UInt64.not_lt.mp inside
  simp only [inside, dite_true]
  refine ⟨fun ⟨index, limit, failed⟩ => ?_,
    fun outside => absurd inside (UInt64.not_lt.mpr outside)⟩
  split at failed
  · simp [throw, throwThe, MonadExceptOf.throw] at failed
  rcases bind_eq_error failed with failed | ⟨committee, -, failed⟩
  · obtain ⟨_, -, mapped⟩ := mapError_eq_error_iff.mp failed
    cases mapped
  split at failed
  · simp [throw, throwThe, MonadExceptOf.throw] at failed
  split at failed
  · rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
    · obtain ⟨_, -, mapped⟩ := mapError_eq_error_iff.mp failed
      cases mapped
    · simp [pure, Except.pure] at failed
  · simp [throw, throwThe, MonadExceptOf.throw] at failed

/-- Before Electra, the aggregate answer refuses with a code other than 500 in two cases only.

It refuses with code 404 when no attestation matches the data root, slot and committee.

It refuses with code 503 when the block of the first match is optimistic.

It needs a fork before Electra, and a code other than 500, the code of an internal error. -/
theorem aggregateAttestation_error_iff_of_lt_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {code : Nat} (before : fork < .pectra)
    (notInternal : code ≠ 500) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = code) ↔
      code = 404 ∧ (¬∃ attestation ∈ attestations, hasRoot attestation.data dataRoot = true ∧
        attestation.data.slot = slot ∧ attestation.data.index = committeeIndex) ∨
      ∃ first, attestations.find? (matchesRequest · dataRoot slot committeeIndex) = some first ∧
        isExecutionOptimistic optimistic first.data.beaconBlockRoot = true ∧ code = 503 := by
  unfold aggregateAttestation
  simp only [before, ↓reduceDIte]
  have unmatched : (¬∃ attestation ∈ attestations, hasRoot attestation.data dataRoot = true ∧
      attestation.data.slot = slot ∧ attestation.data.index = committeeIndex) ↔
      attestations.find? (matchesRequest · dataRoot slot committeeIndex) = none := by
    simp [List.find?_eq_none, matchesRequest]
  rw [unmatched]
  cases attestations.find? (matchesRequest · dataRoot slot committeeIndex) with
  | none => simp [noMatch, @eq_comm _ 404 code]
  | some first =>
    simp only [checkVerified_bind_error_iff, mapError_constructionError_iff notInternal,
      constructAggregate_ne_indexOutOfRange]
    simp

/-- From Electra, the aggregate answer refuses with a code other than 500 in three cases only.

It refuses with code 404 when no single attestation matches the data root, slot and committee.

It refuses with code 503 when the block of the first match is optimistic.

When that block is verified, it refuses with code 400 for a committee index out of range.

That index is not below the most committees a slot can have.

A lower index never gives code 400, even when the epoch has fewer committees.

It needs a fork from Electra, and a code other than 500, the code of an internal error. -/
theorem aggregateAttestation_error_iff_of_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {code : Nat} (electra : .pectra ≤ fork)
    (notInternal : code ≠ 500) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = code) ↔
      code = 404 ∧ (¬∃ single ∈ singles, hasRoot single.data dataRoot = true ∧
        single.data.slot = slot ∧ single.committeeIndex = committeeIndex) ∨
      ∃ first, singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) = some first ∧
        (isExecutionOptimistic optimistic first.data.beaconBlockRoot = true ∧ code = 503 ∨
          isExecutionOptimistic optimistic first.data.beaconBlockRoot = false ∧ code = 400 ∧
            preset.MAX_COMMITTEES_PER_SLOT ≤ committeeIndex) := by
  unfold aggregateAttestation
  have notBefore : ¬ fork < .pectra := fun h => Nat.not_le_of_lt h electra
  simp only [notBefore, ↓reduceDIte]
  have unmatched : (¬∃ single ∈ singles, hasRoot single.data dataRoot = true ∧
      single.data.slot = slot ∧ single.committeeIndex = committeeIndex) ↔
      singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) = none := by
    simp [List.find?_eq_none, singleMatchesRequest]
  rw [unmatched]
  cases singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) with
  | none => simp [noMatch, @eq_comm _ 404 code]
  | some first =>
    simp only [checkVerified_bind_error_iff, mapError_constructionError_iff notInternal,
      constructAggregateOfSingleAttestations_indexOutOfRange_iff]
    simp

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

/-- A contribution fails for want of messages in one case only.

That case is no message of the slot of the state on the root.

It never fails for an index out of range.

It needs a subcommittee index that names a subnet. -/
private theorem constructSyncCommitteeContribution_noMessages_iff
    {state : BeaconState preset fork}
    {committee : SyncCommittee preset} {blockRoot : Root} {subcommitteeIndex : UInt64}
    {messages : List SyncCommitteeMessage}
    (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT) :
    (constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex messages =
      .error .noMessages ↔
        ∀ message ∈ messages, message.slot = state.slot → message.beaconBlockRoot ≠ blockRoot) ∧
      ∀ index limit, constructSyncCommitteeContribution state committee blockRoot
        subcommitteeIndex messages ≠ .error (.indexOutOfRange index limit) := by
  by_cases empty : (messages.filter fun message =>
      message.slot = state.slot ∧ message.beaconBlockRoot = blockRoot).isEmpty
  · have failed : constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex
        messages = .error .noMessages := by
      simp only [constructSyncCommitteeContribution, inRange, dite_true, empty, ite_true]
      rfl
    rw [failed]
    refine ⟨iff_of_true rfl ?_, fun _ _ => by simp⟩
    simpa [List.filter_eq_nil_iff] using empty
  have never : ∀ fault, constructSyncCommitteeContribution state committee blockRoot
      subcommitteeIndex messages = .error fault →
        fault ≠ .noMessages ∧ ∀ index limit, fault ≠ .indexOutOfRange index limit := by
    intro fault failed
    simp only [constructSyncCommitteeContribution, inRange, dite_true, empty,
      Bool.false_eq_true, ite_false] at failed
    rcases bind_eq_error failed with failed | ⟨keyed, -, failed⟩
    · obtain ⟨_, _, failed, -⟩ := mapM_error failed
      rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
      · obtain ⟨_, -, rfl⟩ := mapError_eq_error_iff.mp failed
        simp
      · simp [pure, Except.pure] at failed
    split at failed
    · simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq] at failed
      subst failed
      simp
    rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
    · obtain ⟨_, -, rfl⟩ := mapError_eq_error_iff.mp failed
      simp
    · simp [pure, Except.pure] at failed
  have present : ¬∀ message ∈ messages, message.slot = state.slot →
      message.beaconBlockRoot ≠ blockRoot := by
    simpa [List.filter_eq_nil_iff] using empty
  exact ⟨iff_of_false (fun failed => (never _ failed).1 rfl) present,
    fun index limit failed => (never _ failed).2 index limit rfl⟩

/-- From Altair, the contribution answer refuses with a code other than 500 in three cases only.

It refuses with code 400 when the slot is not that of the state, or the index names no subnet.

Else it refuses with code 503 when the root is optimistic.

Else it refuses with code 404 when no message of the slot on the root comes from a member.

A member is a known validator with a key of the subcommittee.

That refusal also needs the sync committee of the next slot to have a value.

It needs a code other than 500, the code of an internal error. -/
theorem produceSyncCommitteeContribution_error_iff {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {optimistic : OptimisticStore preset fork}
    {messages : List SyncCommitteeMessage} {slot : Slot} {subcommitteeIndex : UInt64}
    {root : Root} {code : Nat} (notInternal : code ≠ 500) :
    (∃ error, produceSyncCommitteeContribution state altair optimistic messages slot
      subcommitteeIndex root = .error error ∧ error.code = code) ↔
      code = 400 ∧ (slot ≠ state.slot ∨ SYNC_COMMITTEE_SUBNET_COUNT ≤ subcommitteeIndex) ∨
        slot = state.slot ∧ subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT ∧
          (isExecutionOptimistic optimistic root = true ∧ code = 503 ∨
            isExecutionOptimistic optimistic root = false ∧ code = 404 ∧
              ∃ committee, syncCommitteeAtNextSlot state altair = .ok committee ∧
                ¬∃ message ∈ messages, message.slot = slot ∧ message.beaconBlockRoot = root ∧
                  ∃ validator, getValidator state message.validatorIndex = .ok validator ∧
                    validator.pubkey ∈
                      syncSubcommitteePubkeys committee subcommitteeIndex.toNat) := by
  unfold produceSyncCommitteeContribution
  by_cases same : slot = state.slot
  swap
  · simp [same, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, @eq_comm _ 400 code]
  subst same
  by_cases inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT
  swap
  · simp [inRange, UInt64.not_lt.mp inRange, constructionError, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind, @eq_comm _ 400 code]
  have notAbove := UInt64.not_le.mpr inRange
  simp only [inRange, notAbove, ↓reduceIte, ne_eq, not_true_eq_false, or_self, and_false,
    false_or, true_and]
  rw [checkVerified_bind_error_iff]
  cases isExecutionOptimistic optimistic root
  swap
  · simp
  simp only [Bool.false_eq_true, false_and, false_or, true_and]
  cases got : syncCommitteeAtNextSlot state altair with
  | error fault =>
    simp [Except.mapError, internalError, bind, Except.bind, notInternal, @eq_comm _ 500 code]
  | ok committee =>
    simp only [Except.mapError, bind, Except.bind, Except.ok.injEq, exists_eq_left']
    obtain ⟨noMessages, noIndex⟩ := constructSyncCommitteeContribution_noMessages_iff
      (state := state) (committee := committee) (blockRoot := root)
      (messages := messages.filter (inSubcommittee state (syncSubcommitteePubkeys committee
        subcommitteeIndex.toNat))) inRange
    have keyed : ∀ message, inSubcommittee state (syncSubcommitteePubkeys committee
        subcommitteeIndex.toNat) message = true ↔
        ∃ validator, getValidator state message.validatorIndex = .ok validator ∧
          validator.pubkey ∈ syncSubcommitteePubkeys committee subcommitteeIndex.toNat := by
      intro message
      unfold inSubcommittee
      cases getValidator state message.validatorIndex <;> simp
    have convert : (¬∃ message ∈ messages, message.slot = state.slot ∧
        message.beaconBlockRoot = root ∧
          ∃ validator, getValidator state message.validatorIndex = .ok validator ∧
            validator.pubkey ∈ syncSubcommitteePubkeys committee subcommitteeIndex.toNat) ↔
        constructSyncCommitteeContribution state committee root subcommitteeIndex
          (messages.filter (inSubcommittee state (syncSubcommitteePubkeys committee
            subcommitteeIndex.toNat))) = .error .noMessages := by
      rw [noMessages]
      simp only [List.mem_filter, keyed]
      constructor
      · rintro absent message ⟨member, validator, found, key⟩ sameSlot sameRoot
        exact absent ⟨message, member, sameSlot, sameRoot, validator, found, key⟩
      · rintro absent ⟨message, member, sameSlot, sameRoot, validator, found, key⟩
        exact absent message ⟨member, validator, found, key⟩ sameSlot sameRoot
    rw [convert]
    cases built : constructSyncCommitteeContribution state committee root subcommitteeIndex
        (messages.filter (inSubcommittee state (syncSubcommitteePubkeys committee
          subcommitteeIndex.toNat))) with
    | ok contribution => simp [pure, Except.pure]
    | error fault =>
      cases fault
      case indexOutOfRange index limit => exact absurd built (noIndex index limit)
      all_goals simp [throw, throwThe, MonadExceptOf.throw, noMatch, constructionError,
        internalError, notInternal, @eq_comm _ 404 code, @eq_comm _ 500 code]

/-! ## Responses -/

/-- Writing the value of an answer as JSON fails only with code 500. -/
theorem apiJsonOr500_error_code {α : Type} [Serialization.Ssz.SszType α] [ApiSpelling α] {x : α}
    {error : ErrorMessage} (failed : apiJsonOr500 x = .error error) : error.code = 500 := by
  unfold apiJsonOr500 at failed
  cases json : toApiJson x with
  | error fault =>
    simp only [json, Except.mapError, Except.error.injEq] at failed
    rw [← failed]
    rfl
  | ok _ => simp [json, Except.mapError] at failed

/-- Writing the value of an answer as JSON adds no refusal with a code other than 500.

It needs a code other than 500, the code of an internal error. -/
private theorem apiJsonOr500_bind_error_iff {α β : Type} [Serialization.Ssz.SszType α]
    [ApiSpelling α]
    {answer : Except ErrorMessage α} {wrap : Lean.Json → β} {code : Nat}
    (notInternal : code ≠ 500) :
    (∃ error, (do return wrap (← apiJsonOr500 (← answer))) = .error error ∧ error.code = code) ↔
      ∃ error, answer = .error error ∧ error.code = code := by
  cases answer with
  | error fault => simp [bind, Except.bind]
  | ok value =>
    simp only [bind, Except.bind]
    cases json : apiJsonOr500 value with
    | error fault => simp [apiJsonOr500_error_code json, notInternal, @eq_comm _ 500 code]
    | ok _ => simp [pure, Except.pure]

/-- The aggregate response refuses with a code exactly when the answer does.

It needs a code other than 500, the code of an internal error. -/
theorem aggregateAttestationResponse_error_iff {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {code : Nat} (notInternal : code ≠ 500) :
    (∃ error, aggregateAttestationResponse state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = code) ↔
      ∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
        committeeIndex = .error error ∧ error.code = code := by
  unfold aggregateAttestationResponse versioned
  exact apiJsonOr500_bind_error_iff notInternal

/-- From Altair, the contribution response refuses with a code exactly when the answer does.

It needs a code other than 500, the code of an internal error. -/
theorem syncCommitteeContributionResponse_error_iff {state : BeaconState preset fork}
    (altair : .altair ≤ fork) {optimistic : OptimisticStore preset fork}
    {messages : List SyncCommitteeMessage} {slot : Slot} {subcommitteeIndex : UInt64}
    {root : Root} {code : Nat} (notInternal : code ≠ 500) :
    (∃ error, syncCommitteeContributionResponse state optimistic messages slot
      subcommitteeIndex root = .error error ∧ error.code = code) ↔
      ∃ error, produceSyncCommitteeContribution state altair optimistic messages slot
        subcommitteeIndex root = .error error ∧ error.code = code := by
  rw [syncCommitteeContributionResponse, dite_eq_left altair]
  exact apiJsonOr500_bind_error_iff notInternal

/-- Before Altair, the contribution response is the error with code 400 that names Altair.

It needs a fork before Altair. -/
theorem syncCommitteeContributionResponse_of_lt_altair {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {messages : List SyncCommitteeMessage}
    {slot : Slot} {subcommitteeIndex : UInt64} {root : Root} (early : fork < .altair) :
    syncCommitteeContributionResponse state optimistic messages slot subcommitteeIndex root =
      .error (beforeFork "sync committee contribution" .altair) := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le.2 early
  simp [syncCommitteeContributionResponse, notAltair]

end EthLib.Consensus.BeaconApi
