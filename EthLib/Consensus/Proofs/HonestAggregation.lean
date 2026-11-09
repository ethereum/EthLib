module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Gossip.Attestation
public import EthLib.Consensus.HonestAggregation
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Time
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect
import EthLib.Base.Proofs.Forall2

/-!
# Proofs: the votes of an honest attester and their aggregates

Attestation data votes for the head block, and its source is the current justified checkpoint.

Its target epoch is the current epoch, which is the epoch of its slot.

Its target root is the root that the state records for the first slot of that epoch.

At that first slot itself, it is the root of the head block.

Its index follows the rule of its fork, which from Electra passes the check of the index of a vote.

It has a value unless, from Gloas, a head block of an earlier slot has a pending payload status.

That holds when the length of an epoch is positive and at most the number of recorded roots.

The slot of the state plus that number must also fit in 64 bits.

Honest signatures on one message aggregate to a signature that verifies.

The keys must not sum to zero, and the signature verifies under the keys in the order of the votes.

Before Electra, the attestation of a validator shows that one validator as its only attester.

The attesters of an aggregate are then the attesters of its attestations with the same data.

From Electra, they are the attesters of the single attestations with the same data and committee.

Its committee bits name that one committee.

The contribution of a sync subcommittee sets the bit of each seat whose key signed a message.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-! ## Attestation data -/

/-- The first slot of the epoch of a slot is that slot when the length of an epoch divides it. -/
theorem div_mul_eq_self_iff {slot length : UInt64} :
    slot / length * length = slot ↔ slot % length = 0 := by
  -- The product is at most the slot, so it does not wrap around.
  have product : (slot / length * length).toNat = slot.toNat / length.toNat * length.toNat := by
    rw [UInt64.toNat_mul, UInt64.toNat_div,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) slot.toNat_lt)]
  rw [← UInt64.toNat_inj, product, ← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.toNat_zero]
  constructor
  · intro whole
    have split := Nat.mod_add_div slot.toNat length.toNat
    rw [Nat.mul_comm, whole] at split
    omega
  · intro divides
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divides)

/-- The root of the block at the start of the epoch.

At a slot that the length of an epoch divides, it is the root of the head block.

At any other slot, it is the root that the state records for the first slot of the epoch. -/
theorem getEpochBoundaryBlockRoot_eq_ok_iff {state : BeaconState preset fork}
    {headRoot root : Root} :
    getEpochBoundaryBlockRoot state headRoot = .ok root ↔
      (state.slot % preset.SLOTS_PER_EPOCH = 0 ∧ root = headRoot) ∨
        (state.slot % preset.SLOTS_PER_EPOCH ≠ 0 ∧
          getBlockRoot state (getCurrentEpoch state) = .ok root) := by
  unfold getEpochBoundaryBlockRoot
  dsimp only
  rw [getCurrentEpoch, computeStartSlotAtEpoch_computeEpochAtSlot]
  simp only [Except.mapError, bind, Except.bind, div_mul_eq_self_iff]
  by_cases first : state.slot % preset.SLOTS_PER_EPOCH = 0
  · simp [first, pure, Except.pure, eq_comm]
  · simp only [first, ↓reduceIte, false_and, false_or]
    cases getBlockRoot state (computeEpochAtSlot preset state.slot) <;> simp [first]

/-- The root of the block at the start of the epoch has a value.

The length of an epoch must be positive and at most the number of recorded roots.

The slot of the state plus the number of recorded roots must fit in 64 bits. -/
theorem getEpochBoundaryBlockRoot_ok {state : BeaconState preset fork} {headRoot : Root}
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (covered : preset.SLOTS_PER_EPOCH ≤ preset.SLOTS_PER_HISTORICAL_ROOT)
    (fits : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64) :
    ∃ root, getEpochBoundaryBlockRoot state headRoot = .ok root := by
  by_cases first : state.slot % preset.SLOTS_PER_EPOCH = 0
  · exact ⟨headRoot, getEpochBoundaryBlockRoot_eq_ok_iff.mpr (.inl ⟨first, rfl⟩)⟩
  -- The first slot of the epoch is before the slot of the state, by less than an epoch.
  have start := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) state.slot
  obtain ⟨atMost, within⟩ := computeStartSlotAtEpoch_le_lt positive start
  have before : (state.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat <
      state.slot.toNat := by
    refine Nat.lt_of_le_of_ne atMost fun same => first ?_
    exact div_mul_eq_self_iff.mp (UInt64.toNat_inj.mp same)
  have covered := UInt64.le_iff_toNat_le.mp covered
  have nonzero : preset.SLOTS_PER_HISTORICAL_ROOT ≠ 0 := by
    intro zero
    have := UInt64.lt_iff_toNat_lt.mp positive
    simp [zero] at covered
    omega
  -- The first slot plus the number of recorded roots fits in 64 bits, and reaches the slot.
  have sum : (state.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH +
      preset.SLOTS_PER_HISTORICAL_ROOT).toNat =
        (state.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat +
          preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have lastOk := addChecked_ok_iff.mpr ⟨by omega, sum⟩
  have lower := UInt64.lt_iff_toNat_lt.mpr before
  have upper : state.slot ≤ state.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH +
      preset.SLOTS_PER_HISTORICAL_ROOT := UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨root, rooted⟩ : ∃ root, getBlockRoot state (getCurrentEpoch state) = .ok root := by
    unfold getBlockRoot getBlockRootAtSlot
    simp only [getCurrentEpoch, start, liftArith, Except.mapError, bind, Except.bind, lastOk,
      lower, upper, ↓reduceIte]
    simp [readCircular, nonzero]
  exact ⟨root, getEpochBoundaryBlockRoot_eq_ok_iff.mpr (.inr ⟨first, rooted⟩)⟩

/-- The index in attestation data before Electra is the index of the committee. -/
theorem attestationDataIndex_of_lt_pectra {slot headSlot : Slot}
    {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus} (before : fork < .pectra) :
    attestationDataIndex fork slot headSlot committeeIndex payloadStatus = .ok committeeIndex := by
  have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : ¬ .glamsterdam ≤ fork := fun gloas => notElectra (Nat.le_trans (by decide) gloas)
  simp [attestationDataIndex, notGloas, notElectra]

/-- The index in attestation data from Electra and before Gloas is zero. -/
theorem attestationDataIndex_of_pectra_of_lt_glamsterdam {slot headSlot : Slot}
    {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus} (electra : .pectra ≤ fork)
    (before : fork < .glamsterdam) :
    attestationDataIndex fork slot headSlot committeeIndex payloadStatus = .ok 0 := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [attestationDataIndex, notGloas, electra]

/-- From Gloas, the index in attestation data whose head block is of its slot is zero. -/
theorem attestationDataIndex_of_glamsterdam_of_eq {slot headSlot : Slot}
    {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus} (gloas : .glamsterdam ≤ fork)
    (same : headSlot = slot) :
    attestationDataIndex fork slot headSlot committeeIndex payloadStatus = .ok 0 := by
  simp [attestationDataIndex, gloas, same]

/-- From Gloas, the index for a head block of an earlier slot is the status of its payload.

It is 0 for an empty payload and 1 for a full one, and a pending status fails. -/
theorem attestationDataIndex_of_glamsterdam_of_ne {slot headSlot : Slot}
    {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus} (gloas : .glamsterdam ≤ fork)
    (earlier : headSlot ≠ slot) :
    attestationDataIndex fork slot headSlot committeeIndex payloadStatus =
      match payloadStatus with
      | .empty => .ok 0
      | .full => .ok 1
      | .pending => .error .pendingPayloadStatus := by
  cases payloadStatus <;> simp [attestationDataIndex, gloas, earlier]

/-- From Electra, the index in attestation data passes the check of the index of a vote. -/
theorem isValidDataIndex_of_attestationDataIndex {slot headSlot : Slot}
    {committeeIndex index : CommitteeIndex} {payloadStatus : PayloadStatus}
    (electra : .pectra ≤ fork)
    (indexed : attestationDataIndex fork slot headSlot committeeIndex payloadStatus = .ok index) :
    isValidDataIndex fork index = true := by
  unfold attestationDataIndex at indexed
  unfold isValidDataIndex
  by_cases gloas : Fork.glamsterdam ≤ fork
  · simp only [gloas, ↓reduceIte] at indexed ⊢
    split at indexed
    · cases indexed
      decide
    · split at indexed <;> cases indexed <;> decide
  · simp only [gloas, electra, ↓reduceIte, Except.ok.injEq] at indexed ⊢
    simp [← indexed]

/-- From Electra, the index in attestation data whose head block is of its slot is zero. -/
theorem eq_zero_of_attestationDataIndex_of_eq {slot headSlot : Slot}
    {committeeIndex index : CommitteeIndex} {payloadStatus : PayloadStatus}
    (electra : .pectra ≤ fork)
    (indexed : attestationDataIndex fork slot headSlot committeeIndex payloadStatus = .ok index)
    (same : headSlot = slot) : index = 0 := by
  subst same
  unfold attestationDataIndex at indexed
  by_cases gloas : Fork.glamsterdam ≤ fork <;>
    simp [gloas, electra] at indexed <;> exact indexed.symm

/-- The attestation data of an attester, from what it is built of.

Its index and the root of its target are those of their rules.

Its slot is the slot of the state, and it votes for the head block.

Its source is the current justified checkpoint, and its target epoch is the current epoch. -/
theorem getAttestationData_eq_ok_iff {state : BeaconState preset fork} {headRoot : Root}
    {headSlot : Slot} {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus}
    {data : AttestationData} :
    getAttestationData state headRoot headSlot committeeIndex payloadStatus = .ok data ↔
      attestationDataIndex fork state.slot headSlot committeeIndex payloadStatus =
          .ok data.index ∧
        getEpochBoundaryBlockRoot state headRoot = .ok data.target.root ∧
        data.slot = state.slot ∧ data.beaconBlockRoot = headRoot ∧
        data.source = state.currentJustifiedCheckpoint ∧
        data.target.epoch = getCurrentEpoch state := by
  unfold getAttestationData
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨index, indexed, root, rooted, rfl⟩
    exact ⟨indexed, rooted, rfl, rfl, rfl, rfl⟩
  · rintro ⟨indexed, rooted, slot, block, source, epoch⟩
    refine ⟨_, indexed, _, rooted, ?_⟩
    rcases data with ⟨_, _, _, _, ⟨_, _⟩⟩
    simp_all

/-- The target epoch of attestation data is the epoch of its slot, as processing checks. -/
theorem target_epoch_eq_of_getAttestationData {state : BeaconState preset fork}
    {headRoot : Root} {headSlot : Slot} {committeeIndex : CommitteeIndex}
    {payloadStatus : PayloadStatus} {data : AttestationData}
    (made : getAttestationData state headRoot headSlot committeeIndex payloadStatus = .ok data) :
    data.target.epoch = computeEpochAtSlot preset data.slot := by
  obtain ⟨-, -, slot, -, -, epoch⟩ := getAttestationData_eq_ok_iff.mp made
  rw [epoch, slot, getCurrentEpoch]

/-- The attestation data of an attester has a value, unless its index fails.

The index fails only from Gloas, for a head block of an earlier slot with a pending status.

The length of an epoch must be positive and at most the number of recorded roots.

The slot of the state plus the number of recorded roots must fit in 64 bits. -/
theorem exists_getAttestationData_eq_ok_iff {state : BeaconState preset fork} {headRoot : Root}
    {headSlot : Slot} {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus}
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (covered : preset.SLOTS_PER_EPOCH ≤ preset.SLOTS_PER_HISTORICAL_ROOT)
    (fits : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64) :
    (∃ data, getAttestationData state headRoot headSlot committeeIndex payloadStatus = .ok data) ↔
      ¬ (.glamsterdam ≤ fork ∧ headSlot ≠ state.slot ∧ payloadStatus = .pending) := by
  obtain ⟨root, rooted⟩ := getEpochBoundaryBlockRoot_ok (headRoot := headRoot) positive covered fits
  simp only [getAttestationData, bind_ok_iff, rooted, pure, Except.pure, Except.ok.injEq]
  unfold attestationDataIndex
  split
  · rename_i gloas
    split
    · rename_i same
      simp [same]
    · rename_i earlier
      cases payloadStatus <;> simp [gloas, earlier]
  · rename_i notGloas
    split <;> simp [notGloas]

/-! ## Signatures -/

/-- Keys that signed a message, one for each attestation, give the signatures of those. -/
theorem mapM_sign_eq_of_forall₂ {attestations : List (Attestation preset fork)}
    {keys : List Signatures.SecretKey} {message : ByteArray}
    (signed : List.Forall₂ (fun attestation key =>
      Signatures.sign key message = .ok attestation.signature) attestations keys) :
    keys.mapM (fun key => Signatures.sign key message) =
      .ok (attestations.map (·.signature)) :=
  mapM_ok_of_forall₂ (List.forall₂_map_right_iff.mpr signed.flip)

/-- Honest signatures of attestations on one message aggregate to a signature that verifies.

Each attestation carries the signature of the message by its key, in the order of the keys.

The keys must not sum to zero. -/
theorem fastAggregateVerify_getAggregateSignature
    {attestations : List (Attestation preset fork)} {keys : List Signatures.SecretKey}
    {message : ByteArray}
    (signed : List.Forall₂ (fun attestation key =>
      Signatures.sign key message = .ok attestation.signature) attestations keys)
    (nonempty : keys ≠ []) (sum : (keys.map (·.val)).sum ≠ 0) :
    ∃ signature, getAggregateSignature attestations = .ok signature ∧
      Signatures.fastAggregateVerify (keys.map Signatures.pkBytes).toArray message
        (Signatures.sigBytes signature) = true := by
  obtain ⟨signatures, signs, signature, aggregated, verifies⟩ :=
    Signatures.fastAggregateVerify_aggregate keys nonempty sum message
  -- Signing is a function, so the signatures of the keys are those of the attestations.
  rw [mapM_sign_eq_of_forall₂ signed, Except.ok.injEq] at signs
  subst signs
  refine ⟨signature, ?_, verifies⟩
  simpa [getAggregateSignature, List.map_map, Function.comp_def, Base.packBytes] using aggregated

/-! ## Attesters -/

/-- The attesters of a committee are its members whose bit is set, from the offset. -/
theorem mem_committeeAttesters_iff {bits : Array Bool} {offset : Nat}
    {committee : Array ValidatorIndex} {attesters : List ValidatorIndex}
    (computed : committeeAttesters bits offset committee = .ok attesters)
    {validatorIndex : ValidatorIndex} :
    validatorIndex ∈ attesters ↔ ∃ (seat : Nat) (inside : seat < committee.size),
      committee[seat] = validatorIndex ∧ bits.getD (offset + seat) false = true := by
  unfold committeeAttesters at computed
  split at computed
  · cases computed
  cases computed
  simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    List.mem_zipIdx_iff_getElem?, Prod.exists]
  constructor
  · rintro ⟨member, seat, found, set, rfl⟩
    obtain ⟨inside, read⟩ := List.getElem?_eq_some_iff.mp found
    exact ⟨seat, by simpa using inside, by simpa using read, set⟩
  · rintro ⟨seat, inside, rfl, set⟩
    exact ⟨_, seat, by simp [inside], set, rfl⟩

/-- The attesters of a committee have a value when the bits have the size of the committee. -/
theorem committeeAttesters_ok {bits : Array Bool} {committee : Array ValidatorIndex}
    (sized : bits.size = committee.size) :
    ∃ attesters, committeeAttesters bits 0 committee = .ok attesters := by
  unfold committeeAttesters
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  exact ⟨_, rfl⟩

/-- A strictly increasing list whose only member is an index is that index alone. -/
theorem eq_singleton_of_pairwise_lt {indices : List ValidatorIndex} {only : ValidatorIndex}
    (increasing : indices.Pairwise (· < ·)) (members : ∀ index, index ∈ indices ↔ index = only) :
    indices = [only] := by
  match indices, increasing with
  | [], _ => exact absurd ((members only).mpr rfl) List.not_mem_nil
  | [first], _ => rw [(members first).mp List.mem_cons_self]
  | first :: second :: _, increasing =>
    have below := List.rel_of_pairwise_cons increasing List.mem_cons_self
    rw [(members first).mp List.mem_cons_self,
      (members second).mp (List.mem_cons_of_mem _ List.mem_cons_self)] at below
    exact absurd below (UInt64.lt_irrefl _)

/-- The member of an array at the first position of a value that it holds is that value. -/
theorem getElem_idxOf {committee : Array ValidatorIndex} {validatorIndex : ValidatorIndex}
    (inside : committee.idxOf validatorIndex < committee.size) :
    committee[committee.idxOf validatorIndex] = validatorIndex := by
  rcases committee with ⟨members⟩
  simp

/-! ## The attestation of a validator -/

/-- Before Electra, the attestation of a validator, from what it is built of.

Its committee holds the validator, and its bits set only the first seat of the validator.

It holds the data, and the signature of the data. -/
theorem constructAttestation_spec {config : Config} {state : BeaconState preset fork}
    {before : fork < .pectra} {data : AttestationData} {validatorIndex : ValidatorIndex}
    {key : Signatures.SecretKey} {attestation : Attestation preset fork}
    (built : constructAttestation config state before data validatorIndex key = .ok attestation) :
    ∃ committee, getBeaconCommittee state data.slot data.index = .ok committee ∧
      committee.idxOf validatorIndex < committee.size ∧
      attestation.aggregationBits.bits =
        Array.ofFn (fun seat : Fin committee.size =>
          decide (seat.val = committee.idxOf validatorIndex)) ∧
      attestation.data = data ∧
      getAttestationSignature config state data key = .ok attestation.signature := by
  unfold constructAttestation at built
  obtain ⟨committee, committeeOk, built⟩ := bind_ok_iff.mp built
  rw [mapError_ok_iff] at committeeOk
  dsimp only at built
  split at built
  · rename_i seated
    split at built
    · obtain ⟨signature, signed, built⟩ := bind_ok_iff.mp built
      simp only [pure, Except.pure, Except.ok.injEq] at built
      subst built
      exact ⟨committee, committeeOk, seated, rfl, rfl, signed⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at built
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at built

/-- Before Electra, the attestation of a validator shows it as its only attester. -/
theorem getAttestingIndices_constructAttestation {config : Config}
    {state : BeaconState preset fork} {before : fork < .pectra} {data : AttestationData}
    {validatorIndex : ValidatorIndex} {key : Signatures.SecretKey}
    {attestation : Attestation preset fork}
    (built : constructAttestation config state before data validatorIndex key = .ok attestation) :
    getAttestingIndices state attestation = .ok [validatorIndex] := by
  obtain ⟨committee, committeeOk, seated, bits, sameData, -⟩ := constructAttestation_spec built
  obtain ⟨attesters, attestersOk⟩ :=
    committeeAttesters_ok (bits := attestation.aggregationBits.bits) (committee := committee)
      (by simp [bits])
  unfold getAttestingIndices
  dsimp only
  split
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  simp only [sameData, committeeOk, attestersOk, bind, Except.bind, pure, Except.pure]
  congr 1
  refine eq_singleton_of_pairwise_lt (sortedSet_sorted _) fun index => ?_
  rw [mem_sortedSet, mem_committeeAttesters_iff attestersOk, bits]
  constructor
  · rintro ⟨seat, inside, rfl, set⟩
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, inside, ↓reduceDIte,
      Option.getD_some, decide_eq_true_eq, Nat.zero_add] at set
    subst set
    exact getElem_idxOf seated
  · rintro rfl
    exact ⟨_, seated, getElem_idxOf seated, by simp [seated]⟩

/-- Before Electra, the attestation of a validator on its attestation data.

The data names the committee of the slot of the state at the index given.

That committee holds the validator.

The attestation shows that validator as its only attester. -/
theorem getAttestingIndices_constructAttestation_getAttestationData {config : Config}
    {state : BeaconState preset fork} {before : fork < .pectra} {headRoot : Root}
    {headSlot : Slot} {committeeIndex : CommitteeIndex} {payloadStatus : PayloadStatus}
    {data : AttestationData} {validatorIndex : ValidatorIndex} {key : Signatures.SecretKey}
    {attestation : Attestation preset fork}
    (made : getAttestationData state headRoot headSlot committeeIndex payloadStatus = .ok data)
    (built : constructAttestation config state before data validatorIndex key = .ok attestation) :
    attestation.data = data ∧
      (∃ committee, getBeaconCommittee state state.slot committeeIndex = .ok committee ∧
        validatorIndex ∈ committee) ∧
      getAttestingIndices state attestation = .ok [validatorIndex] := by
  obtain ⟨indexed, -, slot, -⟩ := getAttestationData_eq_ok_iff.mp made
  rw [attestationDataIndex_of_lt_pectra before, Except.ok.injEq] at indexed
  obtain ⟨committee, committeeOk, seated, -, sameData, -⟩ := constructAttestation_spec built
  refine ⟨sameData, ⟨committee, ?_, ?_⟩, getAttestingIndices_constructAttestation built⟩
  · rwa [slot, ← indexed] at committeeOk
  · rw [← getElem_idxOf seated]
    exact Array.getElem_mem seated

/-- Before Electra, the attesters of an attestation whose bits have the size of its committee.

They are the members of the committee whose bit is set, as a set. -/
theorem mem_getAttestingIndices_of_lt_electra {state : BeaconState preset fork}
    (before : fork < .pectra) {attestation : Attestation preset fork}
    {committee : Array ValidatorIndex}
    (committeeOk :
      getBeaconCommittee state attestation.data.slot attestation.data.index = .ok committee)
    (sized : attestation.aggregationBits.bits.size = committee.size) :
    ∃ indices, getAttestingIndices state attestation = .ok indices ∧
      ∀ validatorIndex, validatorIndex ∈ indices ↔ ∃ (seat : Nat) (inside : seat < committee.size),
        committee[seat] = validatorIndex ∧
          attestation.aggregationBits.bits.getD seat false = true := by
  obtain ⟨attesters, attestersOk⟩ := committeeAttesters_ok sized
  refine ⟨sortedSet attesters, ?_, fun validatorIndex => ?_⟩
  · unfold getAttestingIndices
    dsimp only
    split
    · exact absurd ‹_› (Nat.not_le_of_lt before)
    simp only [committeeOk, attestersOk, bind, Except.bind, pure, Except.pure]
  · rw [mem_sortedSet, mem_committeeAttesters_iff attestersOk]
    simp only [Nat.zero_add]

/-! ## The aggregate of attestations -/

/-- Before Electra, the aggregate of attestations, from what it is built of.

The attestations with the data are not none, and each has one bit for each member of the committee.

A bit of the aggregate is set when the bit of some attestation with the data is.

It holds the data, and the aggregate of the signatures of those attestations. -/
theorem constructAggregate_spec {state : BeaconState preset fork} {before : fork < .pectra}
    {data : AttestationData} {attestations : List (Attestation preset fork)}
    {aggregate : Attestation preset fork}
    (built : constructAggregate state before data attestations = .ok aggregate) :
    ∃ committee, getBeaconCommittee state data.slot data.index = .ok committee ∧
      attestations.filter (·.data = data) ≠ [] ∧
      (∀ attestation ∈ attestations.filter (·.data = data),
        attestation.aggregationBits.bits.size = committee.size) ∧
      aggregate.aggregationBits.bits = Array.ofFn (fun seat : Fin committee.size =>
        (attestations.filter (·.data = data)).any (·.aggregationBits.bits.getD seat.val false)) ∧
      aggregate.data = data ∧
      getAggregateSignature (attestations.filter (·.data = data)) = .ok aggregate.signature := by
  unfold constructAggregate at built
  split at built
  · simp [throw, throwThe, MonadExceptOf.throw] at built
  rename_i first rest joined
  obtain ⟨committee, committeeOk, built⟩ := bind_ok_iff.mp built
  rw [mapError_ok_iff] at committeeOk
  split at built
  · simp [throw, throwThe, MonadExceptOf.throw] at built
  rename_i found
  obtain ⟨signature, signed, built⟩ := bind_ok_iff.mp built
  simp only [pure, Except.pure, Except.ok.injEq] at built
  subst built
  rw [mapError_ok_iff] at signed
  refine ⟨committee, committeeOk, by simp [joined], fun attestation member => ?_, by simp [joined],
    rfl, by rw [joined]; exact signed⟩
  rw [joined] at member
  have sized := List.find?_eq_none.mp found attestation member
  simpa using sized

/-- Before Electra, the attesters of an aggregate are those of its attestations with the data.

Each such attestation has attesters, and a validator attests the aggregate when it attests one. -/
theorem mem_getAttestingIndices_constructAggregate {state : BeaconState preset fork}
    {before : fork < .pectra} {data : AttestationData}
    {attestations : List (Attestation preset fork)} {aggregate : Attestation preset fork}
    (built : constructAggregate state before data attestations = .ok aggregate) :
    ∃ indices, getAttestingIndices state aggregate = .ok indices ∧
      ∀ validatorIndex, validatorIndex ∈ indices ↔
        ∃ attestation ∈ attestations, attestation.data = data ∧
          ∃ attesters, getAttestingIndices state attestation = .ok attesters ∧
            validatorIndex ∈ attesters := by
  obtain ⟨committee, committeeOk, -, sized, bits, sameData, -⟩ := constructAggregate_spec built
  -- Every attestation with the data reads the committee of the aggregate.
  have read : ∀ attestation : Attestation preset fork, attestation.data = data →
      getBeaconCommittee state attestation.data.slot attestation.data.index = .ok committee :=
    fun attestation same => same ▸ committeeOk
  obtain ⟨indices, indicesOk, members⟩ := mem_getAttestingIndices_of_lt_electra before
    (read aggregate sameData) (by simp [bits])
  refine ⟨indices, indicesOk, fun validatorIndex => ?_⟩
  rw [members]
  constructor
  · rintro ⟨seat, inside, rfl, set⟩
    simp only [bits, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, inside, ↓reduceDIte,
      Option.getD_some, List.any_eq_true, List.mem_filter, decide_eq_true_eq] at set
    obtain ⟨attestation, ⟨member, same⟩, setHere⟩ := set
    obtain ⟨attesters, attestersOk, attestersMembers⟩ := mem_getAttestingIndices_of_lt_electra
      before (read attestation same) (sized attestation (by simp [member, same]))
    exact ⟨attestation, member, same, attesters, attestersOk,
      (attestersMembers _).mpr ⟨seat, inside, rfl, by simpa using setHere⟩⟩
  · rintro ⟨attestation, member, same, attesters, attestersOk, attesting⟩
    obtain ⟨attesters', attestersOk', attestersMembers⟩ := mem_getAttestingIndices_of_lt_electra
      before (read attestation same) (sized attestation (by simp [member, same]))
    rw [attestersOk, Except.ok.injEq] at attestersOk'
    subst attestersOk'
    obtain ⟨seat, inside, rfl, setHere⟩ := (attestersMembers _).mp attesting
    refine ⟨seat, inside, rfl, ?_⟩
    simp only [bits, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, inside, ↓reduceDIte,
      Option.getD_some, List.any_eq_true, List.mem_filter, decide_eq_true_eq]
    exact ⟨attestation, ⟨member, same⟩, by simpa using setHere⟩

/-! ## The aggregate of single attestations -/

/-- Bits that are all unset mark no index, wherever their indices start. -/
theorem filterMap_zipIdx_eq_nil {bits : List Bool} (unset : ∀ bit ∈ bits, bit = false)
    (start : Nat) :
    (bits.zipIdx start).filterMap
      (fun (bit, index) => if bit then some index.toUInt64 else none) = [] := by
  induction bits generalizing start with
  | nil => rfl
  | cons bit rest ih =>
    rw [List.zipIdx_cons, List.filterMap_cons, unset bit List.mem_cons_self]
    exact ih (fun other member => unset other (List.mem_cons_of_mem _ member)) _

/-- Bits that set only one position mark the index of that position alone. -/
theorem filterMap_zipIdx_eq_singleton {bits : List Bool} {start position : Nat}
    (inside : position < bits.length)
    (only : ∀ (index : Nat) (below : index < bits.length), bits[index] = true ↔ index = position) :
    (bits.zipIdx start).filterMap
      (fun (bit, index) => if bit then some index.toUInt64 else none) =
        [(start + position).toUInt64] := by
  induction bits generalizing start position with
  | nil => simp at inside
  | cons bit rest ih =>
    rw [List.zipIdx_cons, List.filterMap_cons]
    cases position with
    | zero =>
      have head : bit = true := by
        have first := (only 0 (by simp)).mpr rfl
        rwa [List.getElem_cons_zero] at first
      subst head
      simp only [↓reduceIte, Nat.add_zero]
      rw [filterMap_zipIdx_eq_nil]
      intro other member
      obtain ⟨index, below, rfl⟩ := List.getElem_of_mem member
      have later := only (index + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at later
      simpa using later
    | succ position =>
      have head : bit = false := by
        have first := only 0 (by simp)
        rw [List.getElem_cons_zero] at first
        simpa using first
      subst head
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih (by simpa using inside) fun index below => by
        have later := only (index + 1) (by simp; omega)
        rwa [List.getElem_cons_succ, Nat.add_right_cancel_iff] at later]
      congr 2
      omega

/-- The committee bits that mark only an index below their size name that index alone. -/
theorem getCommitteeIndices_ofFn {count committeeIndex : UInt64} (inside : committeeIndex < count) :
    getCommitteeIndices (⟨Vector.ofFn fun index : Fin count.toNat =>
      index.val.toUInt64 == committeeIndex⟩ : Bitvector count.toNat) = [committeeIndex] := by
  have below := UInt64.lt_iff_toNat_lt.mp inside
  unfold getCommitteeIndices
  rw [filterMap_zipIdx_eq_singleton (position := committeeIndex.toNat) (by simpa using below)]
  · simp
  · intro index within
    have small : index < 2 ^ 64 := Nat.lt_trans (by simpa using within) count.toNat_lt
    simp only [Vector.toList_ofFn, List.getElem_ofFn, beq_iff_eq]
    constructor
    · intro same
      have read := congrArg UInt64.toNat same
      simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt small] at read
      exact read
    · rintro rfl
      simp

/-- From Electra, the aggregate of single attestations, from what it is built of.

The index is below the number of committees of a slot.

The committee holds the attester of each single attestation with the data and the committee index.

A bit of the aggregate is set at each seat whose member is the attester of one of them.

The committee bits mark the index alone, and the aggregate holds the data and their signature. -/
theorem constructAggregateOfSingleAttestations_spec {state : BeaconState preset fork}
    {data : AttestationData} {committeeIndex : CommitteeIndex} {singles : List SingleAttestation}
    {aggregate : Attestation preset fork}
    (built : constructAggregateOfSingleAttestations state data committeeIndex singles =
      .ok aggregate) :
    committeeIndex < preset.MAX_COMMITTEES_PER_SLOT ∧
    ∃ committee, getBeaconCommittee state data.slot committeeIndex = .ok committee ∧
      (∀ single ∈ singles.filter (fun single =>
          single.data = data ∧ single.committeeIndex = committeeIndex),
        single.attesterIndex ∈ committee) ∧
      aggregate.aggregationBits.bits = Array.ofFn (fun seat : Fin committee.size =>
        (singles.filter (fun single =>
          single.data = data ∧ single.committeeIndex = committeeIndex)).any
            (·.attesterIndex = committee[seat])) ∧
      aggregate.data = data ∧
      (∀ electra, aggregate.committeeBits electra =
        ⟨Vector.ofFn fun index : Fin preset.MAX_COMMITTEES_PER_SLOT.toNat =>
          index.val.toUInt64 == committeeIndex⟩) ∧
      Signatures.aggregate ((singles.filter (fun single =>
          single.data = data ∧ single.committeeIndex = committeeIndex)).map
            fun single => Base.packBytes single.signature).toArray =
        .ok aggregate.signature := by
  unfold constructAggregateOfSingleAttestations at built
  split at built
  · rename_i inside
    dsimp only at built
    split at built
    · simp [throw, throwThe, MonadExceptOf.throw] at built
    obtain ⟨committee, committeeOk, built⟩ := bind_ok_iff.mp built
    rw [mapError_ok_iff] at committeeOk
    split at built
    · simp [throw, throwThe, MonadExceptOf.throw] at built
    rename_i found
    split at built
    · obtain ⟨signature, signed, built⟩ := bind_ok_iff.mp built
      simp only [pure, Except.pure, Except.ok.injEq] at built
      subst built
      rw [mapError_ok_iff] at signed
      refine ⟨inside, committee, committeeOk, fun single member => ?_, rfl, rfl, fun _ => rfl,
        signed⟩
      have seated := List.find?_eq_none.mp found single member
      simpa using seated
    · simp [throw, throwThe, MonadExceptOf.throw] at built
  · simp [throw, throwThe, MonadExceptOf.throw] at built

/-- From Electra, the committee bits of the aggregate of single attestations name its committee. -/
theorem getCommitteeIndices_constructAggregateOfSingleAttestations
    {state : BeaconState preset fork} {data : AttestationData} {committeeIndex : CommitteeIndex}
    {singles : List SingleAttestation} {aggregate : Attestation preset fork}
    (electra : .pectra ≤ fork)
    (built : constructAggregateOfSingleAttestations state data committeeIndex singles =
      .ok aggregate) :
    getCommitteeIndices (aggregate.committeeBits electra) = [committeeIndex] := by
  obtain ⟨inside, -, -, -, -, -, committeeBits, -⟩ :=
    constructAggregateOfSingleAttestations_spec built
  rw [committeeBits electra]
  exact getCommitteeIndices_ofFn inside

/-- From Electra, the attesters of the aggregate of single attestations are their attesters.

They are the attesters of the single attestations with the data and the committee index. -/
theorem mem_getAttestingIndices_constructAggregateOfSingleAttestations
    {state : BeaconState preset fork} {data : AttestationData} {committeeIndex : CommitteeIndex}
    {singles : List SingleAttestation} {aggregate : Attestation preset fork}
    (electra : .pectra ≤ fork)
    (built : constructAggregateOfSingleAttestations state data committeeIndex singles =
      .ok aggregate) :
    ∃ indices, getAttestingIndices state aggregate = .ok indices ∧
      ∀ validatorIndex, validatorIndex ∈ indices ↔
        ∃ single ∈ singles, single.data = data ∧ single.committeeIndex = committeeIndex ∧
          single.attesterIndex = validatorIndex := by
  obtain ⟨-, committee, committeeOk, seated, bits, sameData, -, -⟩ :=
    constructAggregateOfSingleAttestations_spec built
  obtain ⟨attesters, attestersOk⟩ :=
    committeeAttesters_ok (bits := aggregate.aggregationBits.bits) (committee := committee)
      (by simp [bits])
  refine ⟨sortedSet attesters, ?_, fun validatorIndex => ?_⟩
  · unfold getAttestingIndices
    dsimp only
    split
    · rw [getCommitteeIndices_constructAggregateOfSingleAttestations electra built]
      simp only [committeesAttesters, sameData, committeeOk, attestersOk, bind, Except.bind, pure,
        Except.pure, List.append_nil]
    · exact absurd electra ‹_›
  · rw [mem_sortedSet, mem_committeeAttesters_iff attestersOk]
    constructor
    · rintro ⟨seat, inside, rfl, set⟩
      simp only [bits, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, Nat.zero_add, inside,
        ↓reduceDIte, Option.getD_some, List.any_eq_true, List.mem_filter, decide_eq_true_eq]
        at set
      obtain ⟨single, ⟨member, sameSingle, sameIndex⟩, attester⟩ := set
      exact ⟨single, member, sameSingle, sameIndex, attester⟩
    · rintro ⟨single, member, sameSingle, sameIndex, rfl⟩
      obtain ⟨seat, inside, found⟩ :=
        Array.mem_iff_getElem.mp (seated single (by simp [member, sameSingle, sameIndex]))
      refine ⟨seat, inside, found, ?_⟩
      simp only [bits, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, Nat.zero_add, inside,
        ↓reduceDIte, Option.getD_some, List.any_eq_true, List.mem_filter, decide_eq_true_eq]
      exact ⟨single, ⟨member, sameSingle, sameIndex⟩, found.symm⟩

/-! ## Sync committee contributions -/

/-- From Altair, the contribution of a subcommittee, from what it is built of.

Its subcommittee index is below the number of subnets.

It holds the slot of the state and the root.

A bit is set at each seat whose key is that of the validator of a message of that slot and root. -/
theorem constructSyncCommitteeContribution_spec {state : BeaconState preset fork}
    {committee : SyncCommittee preset} {blockRoot : Root} {subcommitteeIndex : UInt64}
    {messages : List SyncCommitteeMessage} {contribution : SyncCommitteeContribution preset}
    (built : constructSyncCommitteeContribution state committee blockRoot subcommitteeIndex
      messages = .ok contribution) :
    ∃ inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT,
      contribution.slot = state.slot ∧ contribution.beaconBlockRoot = blockRoot ∧
      contribution.subcommitteeIndex = subcommitteeIndex ∧
      ∀ seat : Fin (syncSubcommitteeSize preset),
        contribution.aggregationBits.bits[seat.val] = true ↔
        ∃ message ∈ messages, message.slot = state.slot ∧ message.beaconBlockRoot = blockRoot ∧
          ∃ validator, getValidator state message.validatorIndex = .ok validator ∧
            validator.pubkey = syncSubcommitteeKey committee subcommitteeIndex inRange seat := by
  unfold constructSyncCommitteeContribution at built
  split at built
  · rename_i inRange
    dsimp only at built
    split at built
    · simp [throw, throwThe, MonadExceptOf.throw] at built
    obtain ⟨keyed, keyedOk, built⟩ := bind_ok_iff.mp built
    split at built
    · simp [throw, throwThe, MonadExceptOf.throw] at built
    obtain ⟨signature, -, built⟩ := bind_ok_iff.mp built
    simp only [pure, Except.pure, Except.ok.injEq] at built
    subst built
    refine ⟨inRange, rfl, rfl, rfl, fun seat => ?_⟩
    simp only [Vector.getElem_ofFn, List.any_eq_true, decide_eq_true_eq, Prod.exists]
    constructor
    · rintro ⟨key, message, member, isSeat⟩
      obtain ⟨message', member', step⟩ := mapM_ok_mem keyedOk _ member
      obtain ⟨validator, validatorOk, step⟩ := bind_ok_iff.mp step
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at step
      obtain ⟨owned, rfl⟩ := step
      simp only [List.mem_filter, decide_eq_true_eq] at member'
      exact ⟨message', member'.1, member'.2.1, member'.2.2, validator,
        mapError_ok_iff.mp validatorOk, owned.trans isSeat⟩
    · rintro ⟨message, member, sameSlot, sameRoot, validator, validatorOk, owned⟩
      obtain ⟨entry, entryMember, step⟩ :=
        exists_mem_of_mapM_ok keyedOk (List.mem_filter.mpr ⟨member, by simp [sameSlot, sameRoot]⟩)
      simp only [validatorOk, Except.mapError, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at step
      subst step
      exact ⟨validator.pubkey, message, entryMember, owned⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at built

end EthLib.Consensus
