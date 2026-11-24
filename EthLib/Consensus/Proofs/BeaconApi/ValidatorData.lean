module

public import EthLib.Consensus.BeaconApi.ValidatorData
public import EthLib.Consensus.Proofs.HonestAggregateSignatures
public import EthLib.Consensus.Proofs.Transition.StateTransition
public import EthLib.Consensus.Proofs.BeaconApi.Responses
import EthLib.Consensus.Proofs.BeaconApi.Encoding
import EthLib.Consensus.Proofs.Containers.Attestation
import EthLib.Consensus.Proofs.Containers.Builder
import EthLib.Consensus.Proofs.Containers.SyncCommittee
import EthLib.Consensus.Proofs.ForkChoice.Head

/-!
# Proofs: the data that the Beacon API hands a validator

What the attestation data, payload attestation data, aggregate and contribution answers hold.

When each answer and its response refuse, and with which code.
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

/-- A failed construction refuses with code 500 for every fault but an index out of range. -/
private theorem mapError_constructionError_internal_iff {β : Type}
    {built : Except ValidatorDutyError β} :
    (∃ error, built.mapError constructionError = .error error ∧ error.code = 500) ↔
      ∃ fault, built = .error fault ∧ ∀ index limit, fault ≠ .indexOutOfRange index limit := by
  constructor
  · rintro ⟨error, failed, code⟩
    obtain ⟨fault, rfl, rfl⟩ := mapError_eq_error_iff.mp failed
    refine ⟨fault, rfl, fun index limit same => ?_⟩
    subst same
    simp [constructionError] at code
  · rintro ⟨fault, rfl, inRange⟩
    refine ⟨_, rfl, ?_⟩
    cases fault
    case indexOutOfRange index limit => exact absurd rfl (inRange index limit)
    all_goals simp [constructionError, internalError]

/-! ## Attestation data -/

/-- The state taken to a slot is at that slot. -/
theorem stateAtSlot_slot {config : Config} {state after : BeaconState preset fork} {slot : Slot}
    (computed : stateAtSlot config state slot = .ok after) : after.slot = slot := by
  unfold stateAtSlot at computed
  split_ifs at computed with below same
  · simp [Except.ok.injEq] at computed; subst computed; exact same.symm
  · obtain ⟨_, advanced⟩ := processSlots_slot (mapError_ok_iff.mp computed)
    exact advanced

/-- Taking a state to a slot gets code 500 exactly when the empty slots up to that slot fail.

For that refusal, the slot must be after the slot of the state. -/
theorem stateAtSlot_internal_iff {config : Config} {state : BeaconState preset fork}
    {slot : Slot} :
    (∃ error, stateAtSlot config state slot = .error error ∧ error.code = 500) ↔
      state.slot < slot ∧ ∃ fault, processSlots config .bls state slot = .error fault := by
  unfold stateAtSlot
  by_cases below : slot < state.slot
  · simp [below, slotBeforeHead, UInt64.not_lt.mpr (UInt64.le_of_lt below)]
  by_cases same : slot = state.slot
  · simp [same]
  have after : state.slot < slot :=
    UInt64.lt_of_le_of_ne (UInt64.not_lt.mp below) (Ne.symm same)
  simp only [below, same, after, ite_false, true_and]
  cases processSlots config .bls state slot <;> simp [Except.mapError, internalError]

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

/-- Computing the index in attestation data never fails.

From Gloas, the payload status must not be pending. -/
private theorem attestationDataIndex_ok_exists {slot headSlot : Slot}
    {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus}
    (settled : .glamsterdam ≤ fork → payloadStatus ≠ .pending) :
    ∃ index, attestationDataIndex fork slot headSlot committeeIndex payloadStatus = .ok index := by
  unfold attestationDataIndex
  split_ifs with gloas <;> cases payloadStatus <;> simp_all

/-- Building attestation data never fails for an index out of range. -/
private theorem getAttestationData_ne_indexOutOfRange {state : BeaconState preset fork}
    {headRoot : Root} {headSlot : Slot} {committeeIndex : CommitteeIndex}
    {payloadStatus : PayloadStatus} {index limit : UInt64} :
    getAttestationData state headRoot headSlot committeeIndex payloadStatus ≠
      .error (.indexOutOfRange index limit) := by
  intro failed
  unfold getAttestationData at failed
  rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
  · unfold attestationDataIndex at failed
    split_ifs at failed
    cases payloadStatus <;> simp at failed
  rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
  · unfold getEpochBoundaryBlockRoot at failed
    rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
    · obtain ⟨_, -, mapped⟩ := mapError_eq_error_iff.mp failed
      cases mapped
    split at failed
    · simp [pure, Except.pure] at failed
    · obtain ⟨_, -, mapped⟩ := mapError_eq_error_iff.mp failed
      cases mapped
  · simp [pure, Except.pure] at failed

/-- Building attestation data gets code 500 exactly when the root of its target fails.

From Gloas, the payload status must not be pending. -/
private theorem getAttestationData_internal_iff {state : BeaconState preset fork}
    {headRoot : Root} {headSlot : Slot} {committeeIndex : CommitteeIndex}
    {payloadStatus : PayloadStatus} (settled : .glamsterdam ≤ fork → payloadStatus ≠ .pending) :
    (∃ error, (getAttestationData state headRoot headSlot committeeIndex payloadStatus).mapError
      constructionError = .error error ∧ error.code = 500) ↔
      ∃ fault, getEpochBoundaryBlockRoot state headRoot = .error fault := by
  have anyFault : (∃ fault, getAttestationData state headRoot headSlot committeeIndex
      payloadStatus = .error fault ∧ ∀ index limit, fault ≠ .indexOutOfRange index limit) ↔
      ∃ fault, getAttestationData state headRoot headSlot committeeIndex payloadStatus =
        .error fault :=
    ⟨fun ⟨fault, failed, _⟩ => ⟨fault, failed⟩, fun ⟨fault, failed⟩ => ⟨fault, failed,
      fun _ _ same => getAttestationData_ne_indexOutOfRange (same ▸ failed)⟩⟩
  rw [mapError_constructionError_internal_iff, anyFault]
  obtain ⟨index, indexed⟩ := attestationDataIndex_ok_exists (slot := state.slot)
    (headSlot := headSlot) (committeeIndex := committeeIndex) settled
  unfold getAttestationData
  rw [indexed]
  cases getEpochBoundaryBlockRoot state headRoot <;> simp [bind, Except.bind, pure, Except.pure]

/-- Once the checks before a step pass, the answer gets code 500 exactly when that step fails.

The answer is the attestation data at the head of the store. -/
theorem produceAttestationData_internal_iff {config : Config} {store : Store preset fork}
    {optimistic : OptimisticStore preset fork} {slot : Slot} {committeeIndex : CommitteeIndex} :
    (∃ error, produceAttestationData config store optimistic slot committeeIndex =
      .error error ∧ error.code = 500) ↔
      -- The first steps find the head of the store, then the block and the state of that head.
      (∃ fault, store.getHead config = .error fault) ∨
      ∃ head, store.getHead config = .ok head ∧
        (store.blocks[head.root]? = none ∨ store.blockStates[head.root]? = none ∨
          ∃ block headState, store.blocks[head.root]? = some block ∧
            store.blockStates[head.root]? = some headState ∧
            -- The next step reads the current slot of the store, and needs a verified head block.
            isExecutionOptimistic optimistic head.root = false ∧
            ((∃ fault, store.getCurrentSlot config = .error fault) ∨
              -- The later steps also need a requested slot not after the current slot.
              ∃ current, store.getCurrentSlot config = .ok current ∧ slot ≤ current ∧
                -- The step of the empty slots takes the head state up to the requested slot.
                --
                -- That step needs a requested slot after the slot of the head state.
                ((headState.slot < slot ∧
                    ∃ fault, processSlots config .bls headState slot = .error fault) ∨
                  -- The last step takes the root of the target.
                  --
                  -- It needs a requested slot not before the slot of the head state.
                  ∃ state, stateAtSlot config headState slot = .ok state ∧
                    ∃ fault, getEpochBoundaryBlockRoot state head.root = .error fault))) := by
  unfold produceAttestationData
  cases got : store.getHead config with
  | error fault => simp [Except.mapError, internalError, bind, Except.bind]
  | ok head =>
    simp only [Except.mapError, bind, Except.bind, reduceCtorEq, exists_false, false_or,
      Except.ok.injEq, exists_eq_left']
    cases store.blocks[head.root]? with
    | none => simp [internalError]
    | some block =>
      cases store.blockStates[head.root]? with
      | none => simp [internalError]
      | some headState =>
        simp only [reduceCtorEq, false_or, Option.some.injEq, exists_and_left, exists_eq_left']
        unfold checkVerified
        cases isExecutionOptimistic optimistic head.root with
        | true => simp [optimisticBlock]
        | false =>
          simp only [Bool.false_eq_true, ite_false, true_and]
          cases store.getCurrentSlot config with
          | error fault => simp [internalError]
          | ok current =>
            simp only [reduceCtorEq, exists_false, false_or, Except.ok.injEq, exists_eq_left']
            by_cases late : current < slot
            · simp [late, UInt64.not_le.mpr late, throw, throwThe, MonadExceptOf.throw]
            have notLate : slot ≤ current := UInt64.not_lt.mp late
            simp only [late, ite_false, notLate, true_and]
            cases atSlot : stateAtSlot config headState slot with
            | error fault =>
              have internal := stateAtSlot_internal_iff (config := config) (state := headState)
                (slot := slot)
              rw [atSlot] at internal
              simp only [reduceCtorEq, false_and, exists_false, or_false, Except.error.injEq,
                exists_eq_left'] at internal ⊢
              exact internal
            | ok state =>
              have notInternal : ¬ (headState.slot < slot ∧
                  ∃ fault, processSlots config .bls headState slot = .error fault) := by
                intro failed
                obtain ⟨_, refused, -⟩ := stateAtSlot_internal_iff.mpr failed
                rw [atSlot] at refused
                cases refused
              simp only [notInternal, Except.ok.injEq, exists_eq_left', false_or]
              -- Computing the index of the data never fails.
              --
              -- That holds since from Gloas the head is never a pending node.
              simpa only [Except.mapError] using
                getAttestationData_internal_iff fun gloas => Store.getHead_ne_pending gloas got

/-- The payload attestation data answer gets code 500 exactly when the store has no head.

For that refusal, the fork must be from Gloas. -/
theorem producePayloadAttestationData_internal_iff {config : Config}
    {store : Store preset fork} {slot : Slot} {payloadPresent blobDataAvailable : Bool} :
    (∃ error, producePayloadAttestationData config store slot payloadPresent blobDataAvailable =
      .error error ∧ error.code = 500) ↔
      .glamsterdam ≤ fork ∧ ∃ fault, store.getHead config = .error fault := by
  unfold producePayloadAttestationData headRoot
  by_cases gloas : .glamsterdam ≤ fork
  swap
  · simp [gloas, beforeFork, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  cases store.getHead config with
  | error fault => simp [gloas, internalError, Except.toOption]
  | ok head => simp [gloas, Except.toOption, pure, Except.pure]

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

It needs a code other than 500, the code of an internal error. -/
theorem aggregateAttestation_error_iff_of_lt_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {code : Nat} (before : fork < .pectra)
    (notInternal : code ≠ 500) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = code) ↔
      -- Code 404 when no attestation matches the data root, slot and committee.
      code = 404 ∧ (¬∃ attestation ∈ attestations, hasRoot attestation.data dataRoot = true ∧
        attestation.data.slot = slot ∧ attestation.data.index = committeeIndex) ∨
      -- Code 503 when the block of the first match is optimistic.
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

It needs a code other than 500, the code of an internal error. -/
theorem aggregateAttestation_error_iff_of_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {code : Nat} (electra : .pectra ≤ fork)
    (notInternal : code ≠ 500) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = code) ↔
      -- Code 404 when no single attestation matches the data root, slot and committee.
      code = 404 ∧ (¬∃ single ∈ singles, hasRoot single.data dataRoot = true ∧
        single.data.slot = slot ∧ single.committeeIndex = committeeIndex) ∨
      ∃ first, singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) = some first ∧
        -- Code 503 when the block of the first match is optimistic.
        (isExecutionOptimistic optimistic first.data.beaconBlockRoot = true ∧ code = 503 ∨
          -- When that block is verified, code 400 for a committee index out of range.
          --
          -- That index is not below the most committees a slot can have.
          --
          -- A lower index never gives code 400, even when the epoch has fewer committees.
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

/-- Before Electra, the aggregate answer refuses with code 500 exactly when its construction fails.

The construction joins the attestations with the data of the first match.

That refusal also needs a match whose block is verified. -/
theorem aggregateAttestation_internal_iff_of_lt_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} (before : fork < .pectra) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = 500) ↔
      ∃ first, attestations.find? (matchesRequest · dataRoot slot committeeIndex) = some first ∧
        isExecutionOptimistic optimistic first.data.beaconBlockRoot = false ∧
        ∃ fault, constructAggregate state before first.data attestations = .error fault := by
  unfold aggregateAttestation
  simp only [before, ↓reduceDIte]
  cases attestations.find? (matchesRequest · dataRoot slot committeeIndex) with
  | none => simp [noMatch]
  | some first =>
    have anyFault : (∃ fault, constructAggregate state before first.data attestations =
        .error fault ∧ ∀ index limit, fault ≠ .indexOutOfRange index limit) ↔
        ∃ fault, constructAggregate state before first.data attestations = .error fault :=
      ⟨fun ⟨fault, failed, _⟩ => ⟨fault, failed⟩, fun ⟨fault, failed⟩ => ⟨fault, failed,
        fun _ _ same => constructAggregate_ne_indexOutOfRange (same ▸ failed)⟩⟩
    simp only [checkVerified_bind_error_iff, mapError_constructionError_internal_iff, anyFault]
    simp

/-- From Electra, the aggregate answer refuses with code 500 exactly when its construction fails.

The construction joins the single attestations of the committee with the data of the first match.

That refusal also needs a match whose block is verified. -/
theorem aggregateAttestation_internal_iff_of_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} (electra : .pectra ≤ fork) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = 500) ↔
      ∃ first, singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) = some first ∧
        isExecutionOptimistic optimistic first.data.beaconBlockRoot = false ∧
        -- It also needs a committee index below the most committees a slot can have.
        committeeIndex < preset.MAX_COMMITTEES_PER_SLOT ∧
        ∃ fault, constructAggregateOfSingleAttestations state first.data committeeIndex singles =
          .error fault := by
  unfold aggregateAttestation
  have notBefore : ¬ fork < .pectra := fun h => Nat.not_le_of_lt h electra
  simp only [notBefore, ↓reduceDIte]
  cases singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) with
  | none => simp [noMatch]
  | some first =>
    have outside := constructAggregateOfSingleAttestations_indexOutOfRange_iff (state := state)
      (data := first.data) (committeeIndex := committeeIndex) (singles := singles)
    have inRangeFault : (∃ fault, constructAggregateOfSingleAttestations state first.data
        committeeIndex singles = .error fault ∧
          ∀ index limit, fault ≠ .indexOutOfRange index limit) ↔
        committeeIndex < preset.MAX_COMMITTEES_PER_SLOT ∧
          ∃ fault, constructAggregateOfSingleAttestations state first.data committeeIndex
            singles = .error fault := by
      constructor
      · rintro ⟨fault, failed, inRange⟩
        refine ⟨UInt64.not_le.mp fun above => ?_, fault, failed⟩
        obtain ⟨index, limit, failedIndex⟩ := outside.mpr above
        exact inRange index limit (Except.error.inj (failed.symm.trans failedIndex))
      · rintro ⟨inside, fault, failed⟩
        exact ⟨fault, failed, fun index limit same => UInt64.not_le.mpr inside
          (outside.mp ⟨index, limit, same ▸ failed⟩)⟩
    simp only [checkVerified_bind_error_iff, mapError_constructionError_internal_iff,
      inRangeFault]
    simp

/-- The first match is among the attestations with its data, which the construction joins. -/
theorem mem_filter_data_of_find?_matchesRequest
    {attestations : List (Attestation preset fork)} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} {first : Attestation preset fork}
    (found : attestations.find? (matchesRequest · dataRoot slot committeeIndex) = some first) :
    first ∈ attestations.filter (·.data = first.data) :=
  List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, by simp⟩

/-- The first match is among the single attestations of the committee with its data.

The construction from Electra joins exactly those. -/
theorem mem_filter_data_committee_of_find?_singleMatchesRequest {singles : List SingleAttestation}
    {dataRoot : Root} {slot : Slot} {committeeIndex : CommitteeIndex} {first : SingleAttestation}
    (found : singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) = some first) :
    first ∈ singles.filter (fun single =>
      single.data = first.data ∧ single.committeeIndex = committeeIndex) := by
  have matched := List.find?_some found
  simp only [singleMatchesRequest, Bool.and_eq_true, beq_iff_eq] at matched
  exact List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, by simp [matched.2]⟩

/-- Before Electra, code 500 of the aggregate answer comes exactly when one of three faults occurs.

That refusal also needs a first match whose block is verified.

The committee has no value, or an attestation with the data of that match has bits of another size.

The third is that the signature of such an attestation does not decode. -/
theorem aggregateAttestation_internal_iff_faults_of_lt_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} (before : fork < .pectra) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = 500) ↔
      ∃ first, attestations.find? (matchesRequest · dataRoot slot committeeIndex) = some first ∧
        isExecutionOptimistic optimistic first.data.beaconBlockRoot = false ∧
        -- The committee of the requested slot and index has no value.
        ((∃ error, getBeaconCommittee state slot committeeIndex = .error error) ∨
          ∃ committee, getBeaconCommittee state slot committeeIndex = .ok committee ∧
            -- An attestation with the data of the first match has bits of another size.
            ((∃ attestation ∈ attestations.filter (·.data = first.data),
                attestation.aggregationBits.bits.size ≠ committee.size) ∨
              -- The signature of such an attestation does not decode.
              ∃ attestation ∈ attestations.filter (·.data = first.data),
                ∃ error, G2.uncompress attestation.signature = .error error)) := by
  rw [aggregateAttestation_internal_iff_of_lt_electra before]
  refine exists_congr fun first => and_congr_right fun found => and_congr_right fun _ => ?_
  -- The first match has the requested slot and index.
  have matched := List.find?_some found
  simp only [matchesRequest, Bool.and_eq_true, beq_iff_eq] at matched
  rw [exists_constructAggregate_eq_error_iff, matched.1.2, matched.2, getAggregateSignature,
    Signatures.exists_aggregate_map_eq_error_iff
      (mem_filter_data_of_find?_matchesRequest found)]

/-- From Electra, code 500 of the aggregate answer comes exactly when one of four faults occurs.

That refusal also needs a verified first match, and an index below the most committees of a slot.

The committee has no value, an attester is outside it, or before Gloas it is too large.

The fourth is that the signature of a joined single attestation does not decode. -/
theorem aggregateAttestation_internal_iff_faults_of_electra {state : BeaconState preset fork}
    {optimistic : OptimisticStore preset fork} {attestations : List (Attestation preset fork)}
    {singles : List SingleAttestation} {dataRoot : Root} {slot : Slot}
    {committeeIndex : CommitteeIndex} (electra : .pectra ≤ fork) :
    (∃ error, aggregateAttestation state optimistic attestations singles dataRoot slot
      committeeIndex = .error error ∧ error.code = 500) ↔
      ∃ first, singles.find? (singleMatchesRequest · dataRoot slot committeeIndex) = some first ∧
        isExecutionOptimistic optimistic first.data.beaconBlockRoot = false ∧
        -- It also needs a committee index below the most committees a slot can have.
        committeeIndex < preset.MAX_COMMITTEES_PER_SLOT ∧
        -- The committee of the requested slot and index has no value.
        ((∃ error, getBeaconCommittee state slot committeeIndex = .error error) ∨
          ∃ committee, getBeaconCommittee state slot committeeIndex = .ok committee ∧
            -- A single attestation of the committee with that data has an attester outside it.
            ((∃ single ∈ singles.filter (fun single =>
                single.data = first.data ∧ single.committeeIndex = committeeIndex),
                single.attesterIndex ∉ committee) ∨
              -- Before Gloas, the committee has more members than the limit of an attestation.
              (fork < .glamsterdam ∧ maxAttesters preset fork < committee.size) ∨
              -- The signature of such a single attestation does not decode.
              ∃ single ∈ singles.filter (fun single =>
                single.data = first.data ∧ single.committeeIndex = committeeIndex),
                ∃ error, G2.uncompress single.signature = .error error)) := by
  rw [aggregateAttestation_internal_iff_of_electra electra]
  refine exists_congr fun first => and_congr_right fun found => and_congr_right fun _ =>
    and_congr_right fun inside => ?_
  -- The first match has the requested slot.
  have matched := List.find?_some found
  simp only [singleMatchesRequest, Bool.and_eq_true, beq_iff_eq] at matched
  rw [exists_constructAggregateOfSingleAttestations_eq_error_iff, matched.1.2,
    Signatures.exists_aggregate_map_eq_error_iff
      (mem_filter_data_committee_of_find?_singleMatchesRequest found)]
  -- An index in range is not a fault.
  simp only [UInt64.not_le.mpr inside, false_or]

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

It needs a subcommittee index that names a subnet. -/
private theorem constructSyncCommitteeContribution_noMessages_iff
    {state : BeaconState preset fork}
    {committee : SyncCommittee preset} {blockRoot : Root} {subcommitteeIndex : UInt64}
    {messages : List SyncCommitteeMessage}
    (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT) :
    (constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex messages =
      .error (.noMessages state.slot blockRoot) ↔
        -- That case is no message of the slot of the state on the root.
        ∀ message ∈ messages, message.slot = state.slot → message.beaconBlockRoot ≠ blockRoot) ∧
      (∀ slot root, constructSyncCommitteeContribution state committee blockRoot
        subcommitteeIndex messages = .error (.noMessages slot root) →
          slot = state.slot ∧ root = blockRoot) ∧
      -- It never fails for an index out of range.
      ∀ index limit, constructSyncCommitteeContribution state committee blockRoot
        subcommitteeIndex messages ≠ .error (.indexOutOfRange index limit) := by
  by_cases empty : (messages.filter fun message =>
      message.slot = state.slot ∧ message.beaconBlockRoot = blockRoot).isEmpty
  · have failed : constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex
        messages = .error (.noMessages state.slot blockRoot) := by
      simp only [constructSyncCommitteeContribution, inRange, dite_true, empty, ite_true]
      rfl
    rw [failed]
    refine ⟨iff_of_true rfl ?_, fun _ _ same => ?_, fun _ _ => by simp⟩
    · simpa [List.filter_eq_nil_iff] using empty
    · simp only [Except.error.injEq, ValidatorDutyError.noMessages.injEq] at same
      exact ⟨same.1.symm, same.2.symm⟩
  have never : ∀ fault, constructSyncCommitteeContribution state committee blockRoot
      subcommitteeIndex messages = .error fault →
        (∀ slot root, fault ≠ .noMessages slot root) ∧
          ∀ index limit, fault ≠ .indexOutOfRange index limit := by
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
  exact ⟨iff_of_false (fun failed => (never _ failed).1 _ _ rfl) present,
    fun slot root failed => absurd rfl ((never _ failed).1 slot root),
    fun index limit failed => (never _ failed).2 index limit rfl⟩

/-- A contribution of members fails only for want of messages, or on a signature.

A member is a known validator with a key of the subcommittee.

It needs a subcommittee index that names a subnet. -/
private theorem constructSyncCommitteeContribution_members_error
    {state : BeaconState preset fork} {committee : SyncCommittee preset} {blockRoot : Root}
    {subcommitteeIndex : UInt64} {messages : List SyncCommitteeMessage}
    {fault : ValidatorDutyError} (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT)
    (failed : constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex
      (messages.filter (inSubcommittee state
        (syncSubcommitteePubkeys committee subcommitteeIndex.toNat))) = .error fault) :
    fault = .noMessages state.slot blockRoot ∨ ∃ error, fault = .bls error := by
  -- Each message that passes the filter comes from a known validator whose key holds a seat.
  have seated : ∀ message ∈ messages.filter (inSubcommittee state
      (syncSubcommitteePubkeys committee subcommitteeIndex.toNat)), ∃ validator,
        getValidator state message.validatorIndex = .ok validator ∧
          ∃ seat, syncSubcommitteeKey committee subcommitteeIndex inRange seat =
            validator.pubkey := by
    intro message member
    have inside := (List.mem_filter.mp member).2
    unfold inSubcommittee at inside
    cases found : getValidator state message.validatorIndex with
    | error _ => simp [found] at inside
    | ok validator =>
      simp only [found, List.contains_iff_mem] at inside
      obtain ⟨position, below, keyAt⟩ := List.getElem_of_mem inside
      exact ⟨validator, rfl, ⟨position, Nat.lt_of_lt_of_le below (List.length_take_le _ _)⟩,
        keyAt⟩
  unfold constructSyncCommitteeContribution at failed
  simp only [inRange, dite_true] at failed
  split at failed
  · simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq] at failed
    exact .inl failed.symm
  rcases bind_eq_error failed with failed | ⟨keyed, keyedOk, failed⟩
  · obtain ⟨message, member, step⟩ := exists_mem_of_mapM_error failed
    obtain ⟨validator, found, -⟩ := seated message (List.mem_filter.mp member).1
    simp [found, Except.mapError, bind, Except.bind, pure, Except.pure] at step
  split at failed
  -- No message is outside the subcommittee, since its key holds a seat.
  · rename_i key other found
    obtain ⟨message, member, step⟩ := mapM_ok_mem keyedOk _ (List.mem_of_find?_eq_some found)
    obtain ⟨validator, read, step⟩ := bind_ok_iff.mp step
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at step
    obtain ⟨rfl, -⟩ := step
    obtain ⟨known, knownOk, seat, keyAt⟩ := seated message (List.mem_filter.mp member).1
    rw [mapError_ok_iff, knownOk, Except.ok.injEq] at read
    subst read
    have unseated := List.find?_some found
    simp at unseated
    exact absurd keyAt (unseated seat)
  rcases bind_eq_error failed with failed | ⟨_, -, failed⟩
  · obtain ⟨error, -, rfl⟩ := mapError_eq_error_iff.mp failed
    exact .inr ⟨error, rfl⟩
  · simp [pure, Except.pure] at failed

/-- From Altair, the contribution answer refuses with a code other than 500 in three cases only.

It needs a code other than 500, the code of an internal error. -/
theorem produceSyncCommitteeContribution_error_iff {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {optimistic : OptimisticStore preset fork}
    {messages : List SyncCommitteeMessage} {slot : Slot} {subcommitteeIndex : UInt64}
    {root : Root} {code : Nat} (notInternal : code ≠ 500) :
    (∃ error, produceSyncCommitteeContribution state altair optimistic messages slot
      subcommitteeIndex root = .error error ∧ error.code = code) ↔
      -- Code 400 when the slot is not that of the state, or the index names no subnet.
      code = 400 ∧ (slot ≠ state.slot ∨ SYNC_COMMITTEE_SUBNET_COUNT ≤ subcommitteeIndex) ∨
        slot = state.slot ∧ subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT ∧
          -- Else code 503 when the root is optimistic.
          (isExecutionOptimistic optimistic root = true ∧ code = 503 ∨
            -- Else code 404 when no message of the slot on the root comes from a member.
            --
            -- A member is a known validator with a key of the subcommittee.
            --
            -- That refusal also needs the sync committee of the next slot to have a value.
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
    obtain ⟨noMessages, sameFields, noIndex⟩ := constructSyncCommitteeContribution_noMessages_iff
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
            subcommitteeIndex.toNat))) = .error (.noMessages state.slot root) := by
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
      case noMessages slot blockRoot =>
        obtain ⟨rfl, rfl⟩ := sameFields slot blockRoot built
        simp [throw, throwThe, MonadExceptOf.throw, noMatch, @eq_comm _ 404 code]
      all_goals simp [throw, throwThe, MonadExceptOf.throw, constructionError,
        internalError, notInternal, @eq_comm _ 500 code]

/-- From Altair, the contribution answer refuses with code 500 in two cases only. -/
theorem produceSyncCommitteeContribution_internal_iff {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {optimistic : OptimisticStore preset fork}
    {messages : List SyncCommitteeMessage} {slot : Slot} {subcommitteeIndex : UInt64}
    {root : Root} :
    (∃ error, produceSyncCommitteeContribution state altair optimistic messages slot
      subcommitteeIndex root = .error error ∧ error.code = 500) ↔
      -- Both refusals need a request at the slot of the state, and a root whose block is verified.
      --
      -- They also need an index that names a subnet.
      slot = state.slot ∧ subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT ∧
        isExecutionOptimistic optimistic root = false ∧
        -- Code 500 when the sync committee of the next slot has no value.
        --
        -- That happens only at the largest 64-bit slot, whose next slot overflows.
        ((∃ fault, syncCommitteeAtNextSlot state altair = .error fault) ∨
          -- Else code 500 when the construction of the contribution fails on a signature.
          ∃ committee, syncCommitteeAtNextSlot state altair = .ok committee ∧ ∃ fault,
            constructSyncCommitteeContribution state committee root subcommitteeIndex
              (messages.filter (inSubcommittee state
                (syncSubcommitteePubkeys committee subcommitteeIndex.toNat))) =
              .error (.bls fault)) := by
  unfold produceSyncCommitteeContribution
  by_cases same : slot = state.slot
  swap
  · simp [same, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  subst same
  by_cases inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT
  swap
  · simp [inRange, constructionError, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  simp only [inRange, ↓reduceIte, true_and]
  rw [checkVerified_bind_error_iff]
  cases isExecutionOptimistic optimistic root
  swap
  · simp
  simp only [Bool.false_eq_true, false_and, false_or, true_and]
  cases got : syncCommitteeAtNextSlot state altair with
  | error fault => simp [Except.mapError, internalError, bind, Except.bind]
  | ok committee =>
    simp only [Except.mapError, bind, Except.bind, Except.ok.injEq, exists_eq_left',
      reduceCtorEq, exists_false, false_or]
    cases built : constructSyncCommitteeContribution state committee root subcommitteeIndex
        (messages.filter (inSubcommittee state (syncSubcommitteePubkeys committee
          subcommitteeIndex.toNat))) with
    | ok contribution => simp [pure, Except.pure]
    | error fault =>
      rcases constructSyncCommitteeContribution_members_error inRange built with
        rfl | ⟨error, rfl⟩
      · simp [throw, throwThe, MonadExceptOf.throw, noMatch]
      · simp [throw, throwThe, MonadExceptOf.throw, constructionError, internalError]

/-! ## Responses -/

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

/-- The attestation data response refuses exactly when the answer does, with the same error. -/
theorem attestationDataResponse_eq_error_iff {config : Config} {store : Store preset fork}
    {optimistic : OptimisticStore preset fork} {slot : Slot} {committeeIndex : CommitteeIndex}
    {error : ErrorMessage} :
    attestationDataResponse config store optimistic slot committeeIndex = .error error ↔
      produceAttestationData config store optimistic slot committeeIndex = .error error := by
  unfold attestationDataResponse
  exact apiJsonOr500_bind_eq_error_iff fun data _ => toApiJson_total data

/-- The payload attestation data response refuses exactly when the answer does, with its error. -/
theorem payloadAttestationDataResponse_eq_error_iff {config : Config} {store : Store preset fork}
    {slot : Slot} {payloadPresent blobDataAvailable : Bool} {error : ErrorMessage} :
    payloadAttestationDataResponse config store slot payloadPresent blobDataAvailable =
        .error error ↔
      producePayloadAttestationData config store slot payloadPresent blobDataAvailable =
        .error error := by
  unfold payloadAttestationDataResponse
  cases answer : producePayloadAttestationData config store slot payloadPresent blobDataAvailable
    with
  | error fault => simp [bind, Except.bind]
  | ok data =>
    cases data with
    | none => simp [bind, Except.bind, pure, Except.pure]
    | some data =>
      obtain ⟨document, wrote⟩ := toApiJson_total data
      simp [versioned, apiJsonOr500, wrote, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The aggregate response refuses exactly when the answer does, with the same error.

It needs a preset with at least one committee per slot. -/
theorem aggregateAttestationResponse_eq_error_iff [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    {state : BeaconState preset fork} {optimistic : OptimisticStore preset fork}
    {attestations : List (Attestation preset fork)} {singles : List SingleAttestation}
    {dataRoot : Root} {slot : Slot} {committeeIndex : CommitteeIndex} {error : ErrorMessage} :
    aggregateAttestationResponse state optimistic attestations singles dataRoot slot
        committeeIndex = .error error ↔
      aggregateAttestation state optimistic attestations singles dataRoot slot committeeIndex =
        .error error := by
  unfold aggregateAttestationResponse
  exact versioned_eq_error_iff fun aggregate _ => toApiJson_total aggregate

/-- From Altair, the contribution response refuses exactly when the answer does, with its error.

It needs a preset whose sync subcommittees are not empty. -/
theorem syncCommitteeContributionResponse_eq_error_iff [NeZero (syncSubcommitteeSize preset)]
    {state : BeaconState preset fork} (altair : .altair ≤ fork)
    {optimistic : OptimisticStore preset fork} {messages : List SyncCommitteeMessage}
    {slot : Slot} {subcommitteeIndex : UInt64} {root : Root} {error : ErrorMessage} :
    syncCommitteeContributionResponse state optimistic messages slot subcommitteeIndex root =
        .error error ↔
      produceSyncCommitteeContribution state altair optimistic messages slot subcommitteeIndex
        root = .error error := by
  rw [syncCommitteeContributionResponse, dite_eq_left altair]
  exact apiJsonOr500_bind_eq_error_iff fun contribution _ => toApiJson_total contribution

end EthLib.Consensus.BeaconApi
