module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Time

/-!
# Proofs: slots, epochs and times

The first slot of an epoch lies in that epoch, and every slot lies after its epoch's first slot.

The slots of an epoch exist exactly when its first slot plus its length fits in 64 bits.

The slot at the start time of a slot is that slot, in milliseconds and in seconds.

Each conversion fails exactly when its result leaves the 64-bit range.

A part of a slot grows with its basis points and stays below the slot.

From Gloas, the attestation, the payload and the payload attestation fall due in that order.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {config : Config} {preset : Preset}

/-- The first slot of an epoch exists exactly when it fits in 64 bits. -/
theorem computeStartSlotAtEpoch_ok_iff {epoch : Epoch} {slot : Slot} :
    computeStartSlotAtEpoch preset epoch = .ok slot ↔
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 ∧
        slot.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
  mulChecked_ok_iff

/-- The epoch of the first slot of an epoch is that epoch. -/
theorem computeEpochAtSlot_computeStartSlotAtEpoch {epoch : Epoch} {slot : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (start : computeStartSlotAtEpoch preset epoch = .ok slot) :
    computeEpochAtSlot preset slot = epoch := by
  obtain ⟨-, value⟩ := computeStartSlotAtEpoch_ok_iff.mp start
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := UInt64.lt_iff_toNat_lt.mp positive
  rw [computeEpochAtSlot, ← UInt64.toNat_inj, UInt64.toNat_div, value,
    Nat.mul_div_cancel _ positive]

/-- The epoch of a slot has a first slot: the slot rounded down to a multiple of the epoch. -/
theorem computeStartSlotAtEpoch_computeEpochAtSlot (slot : Slot) :
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) =
      .ok (slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH) := by
  have fits : (slot / preset.SLOTS_PER_EPOCH).toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    rw [UInt64.toNat_div]
    exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) slot.toNat_lt
  refine computeStartSlotAtEpoch_ok_iff.mpr ⟨fits, ?_⟩
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt fits]
  rfl

/-- A slot lies in the epoch that starts at most one epoch's slots before it. -/
theorem computeStartSlotAtEpoch_le_lt {slot start : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    (first : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok start) :
    start.toNat ≤ slot.toNat ∧ slot.toNat < start.toNat + preset.SLOTS_PER_EPOCH.toNat := by
  obtain ⟨-, value⟩ := computeStartSlotAtEpoch_ok_iff.mp first
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := UInt64.lt_iff_toNat_lt.mp positive
  rw [value, computeEpochAtSlot, UInt64.toNat_div]
  constructor
  · exact Nat.div_mul_le_self _ _
  · have := Nat.lt_div_mul_add (a := slot.toNat) positive
    exact this

/-- The epoch of an activation or an exit exists exactly when it fits in 64 bits.

It is then one epoch, then the seed lookahead, after the given epoch. -/
theorem computeActivationExitEpoch_ok_iff {epoch result : Epoch} :
    computeActivationExitEpoch preset epoch = .ok result ↔
      epoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat < 2 ^ 64 ∧
        result.toNat = epoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat := by
  unfold computeActivationExitEpoch
  cases next : addChecked epoch 1 with
  | error fault =>
    have : ¬ epoch.toNat + 1 < 2 ^ 64 := by
      intro fits
      unfold addChecked at next
      simp [fits] at next
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and]
    omega
  | ok after =>
    obtain ⟨-, value⟩ := addChecked_ok_iff.mp next
    simp only [bind, Except.bind, addChecked_ok_iff, value, UInt64.toNat_one]

/-- The start time of a slot, in milliseconds, maps back to the slot. -/
theorem computeSlotAtTimeMs_computeTimeAtSlotMs {genesisTimeMs timeMs : UInt64} {slot : Slot}
    (positive : 0 < config.SLOT_DURATION_MS)
    (start : computeTimeAtSlotMs config genesisTimeMs slot = .ok timeMs) :
    computeSlotAtTimeMs config genesisTimeMs timeMs = .ok slot := by
  unfold computeTimeAtSlotMs at start
  cases product : mulChecked slot config.SLOT_DURATION_MS with
  | error fault => simp [product, bind, Except.bind] at start
  | ok offset =>
    simp only [product, bind, Except.bind] at start
    obtain ⟨-, offsetValue⟩ := mulChecked_ok_iff.mp product
    obtain ⟨-, timeValue⟩ := addChecked_ok_iff.mp start
    have positive : 0 < config.SLOT_DURATION_MS.toNat := UInt64.lt_iff_toNat_lt.mp positive
    have elapsed : subChecked timeMs genesisTimeMs = .ok offset :=
      subChecked_ok_iff.mpr ⟨by omega, by omega⟩
    have quotient : divChecked offset config.SLOT_DURATION_MS = .ok slot := by
      refine divChecked_ok_iff.mpr ⟨by intro zero; simp [zero] at positive, ?_⟩
      rw [offsetValue, Nat.mul_div_cancel _ positive]
    simp only [computeSlotAtTimeMs, elapsed, quotient, bind, Except.bind]

/-- A whole number of seconds that fits keeps its value, in milliseconds.

It fits when it is at most the largest 64-bit integer divided by 1000. -/
theorem toNat_secondsToMilliseconds {seconds : UInt64} (fits : seconds ≤ UINT64_MAX / 1000) :
    (secondsToMilliseconds seconds).toNat = seconds.toNat * 1000 := by
  have max : UINT64_MAX.toNat = 2 ^ 64 - 1 := by decide
  have thousand : (1000 : UInt64).toNat = 1000 := rfl
  have fits' : seconds.toNat ≤ (2 ^ 64 - 1) / 1000 := by
    have := UInt64.le_iff_toNat_le.mp fits
    rwa [UInt64.toNat_div, max, thousand] at this
  have notLt : ¬ UINT64_MAX / 1000 < seconds := UInt64.not_lt.mpr fits
  simp only [secondsToMilliseconds, notLt, ↓reduceIte]
  rw [UInt64.toNat_mul, thousand]
  exact Nat.mod_eq_of_lt (by omega)

/-- The start time of a slot, in seconds, maps back to the slot.

A slot lasts a positive whole number of seconds.

A shorter slot can share its second with the next one.

For example, with slots of 500 milliseconds, slots 2 and 3 start in the same second.

The time of genesis must also fit in milliseconds.

A time that saturates is not the time of genesis. -/
theorem computeSlotAtTime_computeTimeAtSlot {genesisTime time : UInt64} {slot : Slot}
    (positive : 0 < config.SLOT_DURATION_MS) (whole : config.SLOT_DURATION_MS % 1000 = 0)
    (genesis : genesisTime ≤ UINT64_MAX / 1000)
    (start : computeTimeAtSlot config genesisTime slot = .ok time) :
    computeSlotAtTime config genesisTime time = .ok slot := by
  have genesisMs := toNat_secondsToMilliseconds genesis
  have max : UINT64_MAX.toNat = 2 ^ 64 - 1 := by decide
  have thousand : (1000 : UInt64).toNat = 1000 := rfl
  have positive : 0 < config.SLOT_DURATION_MS.toNat := UInt64.lt_iff_toNat_lt.mp positive
  -- The slot lasts `1000 * k` milliseconds, that is `k` seconds.
  obtain ⟨k, hk⟩ : ∃ k, config.SLOT_DURATION_MS.toNat = 1000 * k := by
    refine ⟨config.SLOT_DURATION_MS.toNat / 1000, ?_⟩
    have := congrArg UInt64.toNat whole
    rw [UInt64.toNat_mod, thousand] at this
    simp only [UInt64.toNat_zero] at this
    omega
  unfold computeTimeAtSlot at start
  cases started : computeTimeAtSlotMs config (secondsToMilliseconds genesisTime) slot with
  | error fault => simp [started, bind, Except.bind] at start
  | ok timeMs =>
    simp only [started, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at start
    unfold computeTimeAtSlotMs at started
    cases product : mulChecked slot config.SLOT_DURATION_MS with
    | error fault => simp [product, bind, Except.bind] at started
    | ok offset =>
      simp only [product, bind, Except.bind] at started
      obtain ⟨-, offsetValue⟩ := mulChecked_ok_iff.mp product
      obtain ⟨fitsMs, timeValue⟩ := addChecked_ok_iff.mp started
      rw [genesisMs] at fitsMs timeValue
      rw [hk] at offsetValue
      have regroup : slot.toNat * (1000 * k) = 1000 * (slot.toNat * k) := by
        rw [Nat.mul_left_comm]
      -- The time in seconds is the genesis time plus `k` seconds for each slot.
      have timeNat : time.toNat = genesisTime.toNat + slot.toNat * k := by
        rw [← start, millisecondsToSeconds, UInt64.toNat_div, thousand]
        omega
      have timeLe : time ≤ UINT64_MAX / 1000 := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [UInt64.toNat_div, max, thousand]
        omega
      have timeMsValue := toNat_secondsToMilliseconds timeLe
      have elapsed : subChecked (secondsToMilliseconds time) (secondsToMilliseconds genesisTime) =
          .ok offset :=
        subChecked_ok_iff.mpr ⟨by omega, by omega⟩
      have quotient : divChecked offset config.SLOT_DURATION_MS = .ok slot := by
        refine divChecked_ok_iff.mpr ⟨by intro zero; simp [zero] at positive, ?_⟩
        rw [offsetValue, hk, Nat.mul_div_cancel _ (by omega : 0 < 1000 * k)]
      simp only [computeSlotAtTime, computeSlotAtTimeMs, elapsed, quotient, bind, Except.bind]

/-- A part of a slot exists exactly when the product of its basis points and the slot fits in
64 bits.

It is then that product divided by the basis points of a whole. -/
theorem getSlotComponentDurationMs_ok_iff {basisPoints duration : UInt64} :
    getSlotComponentDurationMs config basisPoints = .ok duration ↔
      basisPoints.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 ∧
        duration.toNat = basisPoints.toNat * config.SLOT_DURATION_MS.toNat / 10000 := by
  unfold getSlotComponentDurationMs
  cases product : mulChecked basisPoints config.SLOT_DURATION_MS with
  | error fault =>
    have : ¬ basisPoints.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 := by
      intro fits
      unfold mulChecked at product
      simp [fits] at product
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and]
    omega
  | ok value =>
    obtain ⟨fits, value⟩ := mulChecked_ok_iff.mp product
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, fits, true_and]
    rw [← UInt64.toNat_inj, UInt64.toNat_div, value]
    exact ⟨Eq.symm, Eq.symm⟩

/-- More basis points give at least as long a part of the slot. -/
theorem getSlotComponentDurationMs_mono {small large shorter longer : UInt64}
    (le : small ≤ large)
    (first : getSlotComponentDurationMs config small = .ok shorter)
    (second : getSlotComponentDurationMs config large = .ok longer) : shorter ≤ longer := by
  obtain ⟨-, shorter⟩ := getSlotComponentDurationMs_ok_iff.mp first
  obtain ⟨-, longer⟩ := getSlotComponentDurationMs_ok_iff.mp second
  rw [UInt64.le_iff_toNat_le, shorter, longer]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp le))

/-- A part below the whole of a nonempty slot ends before the slot does. -/
theorem getSlotComponentDurationMs_lt {basisPoints duration : UInt64}
    (part : basisPoints < BASIS_POINTS) (positive : 0 < config.SLOT_DURATION_MS)
    (ok : getSlotComponentDurationMs config basisPoints = .ok duration) :
    duration < config.SLOT_DURATION_MS := by
  obtain ⟨-, value⟩ := getSlotComponentDurationMs_ok_iff.mp ok
  have part : basisPoints.toNat < 10000 := UInt64.lt_iff_toNat_lt.mp part
  have positive : 0 < config.SLOT_DURATION_MS.toNat := UInt64.lt_iff_toNat_lt.mp positive
  rw [UInt64.lt_iff_toNat_lt, value, Nat.div_lt_iff_lt_mul (by decide)]
  have := Nat.mul_lt_mul_of_pos_right part positive
  rwa [Nat.mul_comm 10000] at this

/-- Before Gloas, an attestation is due at the part that the configuration gives before Gloas. -/
theorem getAttestationDueMs_of_lt {fork : Fork} (before : fork < .glamsterdam) :
    getAttestationDueMs config fork =
      getSlotComponentDurationMs config config.ATTESTATION_DUE_BPS := by
  have later : ¬ fork ≥ .glamsterdam := Nat.not_le_of_lt before
  simp only [getAttestationDueMs, later, ↓reduceIte]

/-- Before Gloas, an aggregate is due at the part that the configuration gives before Gloas. -/
theorem getAggregateDueMs_of_lt {fork : Fork} (before : fork < .glamsterdam) :
    getAggregateDueMs config fork =
      getSlotComponentDurationMs config config.AGGREGATE_DUE_BPS := by
  have later : ¬ fork ≥ .glamsterdam := Nat.not_le_of_lt before
  simp only [getAggregateDueMs, later, ↓reduceIte]

/-- Before Gloas, a sync committee message is due at the part given before Gloas. -/
theorem getSyncMessageDueMs_of_lt {fork : Fork} (before : fork < .glamsterdam) :
    getSyncMessageDueMs config fork =
      getSlotComponentDurationMs config config.SYNC_MESSAGE_DUE_BPS := by
  have later : ¬ fork ≥ .glamsterdam := Nat.not_le_of_lt before
  simp only [getSyncMessageDueMs, later, ↓reduceIte]

/-- Before Gloas, a sync committee contribution is due at the part given before Gloas. -/
theorem getContributionDueMs_of_lt {fork : Fork} (before : fork < .glamsterdam) :
    getContributionDueMs config fork =
      getSlotComponentDurationMs config config.CONTRIBUTION_DUE_BPS := by
  have later : ¬ fork ≥ .glamsterdam := Nat.not_le_of_lt before
  simp only [getContributionDueMs, later, ↓reduceIte]

/-- From Gloas, the attestation, the payload and the payload attestation fall due in that order,
within the slot.

The configuration orders their basis points below a whole, and its slot is nonempty. -/
theorem gloas_deadlines_ordered {fork : Fork} {attestation payload payloadAttestation : UInt64}
    (gloas : fork ≥ .glamsterdam)
    (first : config.ATTESTATION_DUE_BPS_GLOAS ≤ config.PAYLOAD_DUE_BPS)
    (second : config.PAYLOAD_DUE_BPS ≤ config.PAYLOAD_ATTESTATION_DUE_BPS)
    (part : config.PAYLOAD_ATTESTATION_DUE_BPS < BASIS_POINTS)
    (positive : 0 < config.SLOT_DURATION_MS)
    (attestationOk : getAttestationDueMs config fork = .ok attestation)
    (payloadOk : getPayloadDueMs config = .ok payload)
    (payloadAttestationOk : getPayloadAttestationDueMs config = .ok payloadAttestation) :
    attestation ≤ payload ∧ payload ≤ payloadAttestation ∧
      payloadAttestation < config.SLOT_DURATION_MS := by
  simp only [getAttestationDueMs, gloas, ↓reduceIte] at attestationOk
  exact ⟨getSlotComponentDurationMs_mono first attestationOk payloadOk,
    getSlotComponentDurationMs_mono second payloadOk payloadAttestationOk,
    getSlotComponentDurationMs_lt part positive payloadAttestationOk⟩

/-- A part of the slot exists when a larger part does not overflow. -/
theorem getSlotComponentDurationMs_ok_of_le {small large : UInt64} (le : small ≤ large)
    (fits : large.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64) :
    ∃ duration, getSlotComponentDurationMs config small = .ok duration := by
  have le : small.toNat ≤ large.toNat := UInt64.le_iff_toNat_le.mp le
  have fits' : small.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ le) fits
  refine ⟨UInt64.ofNat (small.toNat * config.SLOT_DURATION_MS.toNat / 10000), ?_⟩
  refine getSlotComponentDurationMs_ok_iff.mpr ⟨fits', ?_⟩
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) fits')]

/-- On mainnet and on the minimal configuration, from Gloas, the attestation, the payload and the
payload attestation fall due in that order, within the slot. -/
theorem gloas_deadlines_ordered_of_named {fork : Fork} (gloas : fork ≥ .glamsterdam)
    (named : config = .mainnet ∨ config = .minimal) :
    ∃ attestation payload payloadAttestation,
      getAttestationDueMs config fork = .ok attestation ∧
      getPayloadDueMs config = .ok payload ∧
      getPayloadAttestationDueMs config = .ok payloadAttestation ∧
      attestation ≤ payload ∧ payload ≤ payloadAttestation ∧
      payloadAttestation < config.SLOT_DURATION_MS := by
  have values : config.ATTESTATION_DUE_BPS_GLOAS ≤ config.PAYLOAD_DUE_BPS ∧
      config.PAYLOAD_DUE_BPS ≤ config.PAYLOAD_ATTESTATION_DUE_BPS ∧
      config.PAYLOAD_ATTESTATION_DUE_BPS < BASIS_POINTS ∧ 0 < config.SLOT_DURATION_MS ∧
      config.PAYLOAD_ATTESTATION_DUE_BPS.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 := by
    rcases named with rfl | rfl <;> decide
  obtain ⟨first, second, part, positive, fits⟩ := values
  obtain ⟨payloadAttestation, payloadAttestationOk⟩ :=
    getSlotComponentDurationMs_ok_of_le (UInt64.le_refl _) fits
  obtain ⟨payload, payloadOk⟩ := getSlotComponentDurationMs_ok_of_le second fits
  obtain ⟨attestation, attestationOk⟩ :=
    getSlotComponentDurationMs_ok_of_le (UInt64.le_trans first second) fits
  have attestationOk : getAttestationDueMs config fork = .ok attestation := by
    simp only [getAttestationDueMs, gloas, ↓reduceIte, attestationOk]
  exact ⟨attestation, payload, payloadAttestation, attestationOk, payloadOk, payloadAttestationOk,
    gloas_deadlines_ordered gloas first second part positive attestationOk payloadOk
      payloadAttestationOk⟩

/-! ## The slots of an epoch -/

/-- The slots of an epoch are its first slot plus each offset below the length of an epoch.

The sum of the first slot and that length is below `2^64`. -/
theorem epochSlots_eq_ok_iff {epoch : Epoch} {slots : List Slot} :
    epochSlots preset epoch = .ok slots ↔
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 ∧
        slots = (List.range preset.SLOTS_PER_EPOCH.toNat).map fun offset =>
          epoch * preset.SLOTS_PER_EPOCH + offset.toUInt64 := by
  unfold epochSlots computeStartSlotAtEpoch mulChecked addChecked
  by_cases mul : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64
  · have product : (epoch * preset.SLOTS_PER_EPOCH).toNat =
        epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt mul]
    by_cases add : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat <
        2 ^ 64
    · simp only [mul, product, add, ite_true, bind, Except.bind, pure,
        Except.pure, Except.ok.injEq, true_and, eq_comm]
    · simp only [mul, product, add, ite_true, ite_false, bind, Except.bind,
        false_and, reduceCtorEq]
  · have add : ¬epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat <
        2 ^ 64 := by omega
    simp only [mul, add, ite_false, bind, Except.bind, false_and, reduceCtorEq]

/-- An epoch whose first slot plus the length of an epoch reaches `2^64` has no slots.

The guides compute that sum as a 64-bit integer, which overflows there. -/
theorem epochSlots_eq_error {epoch : Epoch}
    (big : 2 ^ 64 ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat) :
    epochSlots preset epoch = .error .overflow := by
  unfold epochSlots computeStartSlotAtEpoch mulChecked addChecked
  by_cases mul : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64
  · have product : (epoch * preset.SLOTS_PER_EPOCH).toNat =
        epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt mul]
    have add : ¬epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat <
        2 ^ 64 := Nat.not_lt.mpr big
    simp only [mul, product, add, ite_true, ite_false, bind, Except.bind]
  · simp only [mul, ite_false, bind, Except.bind]

/-- The slot at an offset below the length of an epoch, as a number. -/
theorem toNat_epochSlot {epoch : Epoch}
    (fits : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    {offset : Nat} (offsetLt : offset < preset.SLOTS_PER_EPOCH.toNat) :
    (epoch * preset.SLOTS_PER_EPOCH + offset.toUInt64).toNat =
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + offset := by
  have offsetSmall : offset < 2 ^ 64 :=
    Nat.lt_of_lt_of_le offsetLt (Nat.le_of_lt preset.SLOTS_PER_EPOCH.toNat_lt)
  have productSmall : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt productSmall]
  exact Nat.mod_eq_of_lt (by omega)

/-- Each slot of an epoch has that epoch. -/
theorem mem_epochSlots {epoch : Epoch} {slots : List Slot} (h : epochSlots preset epoch = .ok slots)
    {slot : Slot} (mem : slot ∈ slots) : computeEpochAtSlot preset slot = epoch := by
  obtain ⟨fits, rfl⟩ := epochSlots_eq_ok_iff.mp h
  simp only [List.mem_map, List.mem_range] at mem
  obtain ⟨offset, offsetLt, rfl⟩ := mem
  -- The slot is the first slot of the epoch plus an offset below the length of an epoch.
  have lengthPos : 0 < preset.SLOTS_PER_EPOCH.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) offsetLt
  apply UInt64.toNat_inj.mp
  simp only [computeEpochAtSlot, UInt64.toNat_div, toNat_epochSlot fits offsetLt]
  rw [Nat.mul_comm, Nat.mul_add_div lengthPos, Nat.div_eq_of_lt offsetLt, Nat.add_zero]

/-- Each slot of an epoch is among its slots, when an epoch has at least one slot. -/
theorem mem_epochSlots_of_epoch {epoch : Epoch} {slots : List Slot}
    (positive : preset.SLOTS_PER_EPOCH ≠ 0) (h : epochSlots preset epoch = .ok slots)
    {slot : Slot} (slotEpoch : computeEpochAtSlot preset slot = epoch) : slot ∈ slots := by
  obtain ⟨fits, rfl⟩ := epochSlots_eq_ok_iff.mp h
  have lengthPos : 0 < preset.SLOTS_PER_EPOCH.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have epochNat := congrArg UInt64.toNat slotEpoch
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
  -- The slot is the first slot of the epoch plus its place in the epoch.
  have split := Nat.div_add_mod slot.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [epochNat] at split
  have offsetLt := Nat.mod_lt slot.toNat lengthPos
  simp only [List.mem_map, List.mem_range]
  refine ⟨slot.toNat % preset.SLOTS_PER_EPOCH.toNat, offsetLt, ?_⟩
  apply UInt64.toNat_inj.mp
  rw [toNat_epochSlot fits offsetLt, Nat.mul_comm, split]

/-- The slots of an epoch strictly increase. -/
theorem epochSlots_pairwise {epoch : Epoch} {slots : List Slot}
    (h : epochSlots preset epoch = .ok slots) : slots.Pairwise (· < ·) := by
  obtain ⟨fits, rfl⟩ := epochSlots_eq_ok_iff.mp h
  rw [List.pairwise_map]
  refine (List.Pairwise.and_mem.mp List.pairwise_lt_range).imp fun ⟨first, second, lt⟩ => ?_
  rw [UInt64.lt_iff_toNat_lt, toNat_epochSlot fits (List.mem_range.mp first),
    toNat_epochSlot fits (List.mem_range.mp second)]
  omega

/-- The slots of an epoch, from its first slot, when that slot is known.

The first slot plus the length of an epoch is then below `2^64`. -/
theorem epochSlots_eq_ok_of_start {epoch : Epoch} {start : Slot} {slots : List Slot}
    (first : computeStartSlotAtEpoch preset epoch = .ok start)
    (h : epochSlots preset epoch = .ok slots) :
    start.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 ∧
      slots = (List.range preset.SLOTS_PER_EPOCH.toNat).map fun k => start + k.toUInt64 := by
  unfold epochSlots at h
  rw [first] at h
  cases sum : addChecked start preset.SLOTS_PER_EPOCH with
  | error e => simp [sum, bind, Except.bind] at h
  | ok v =>
    simp only [sum, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨(addChecked_ok_iff.mp sum).1, h.symm⟩

end EthLib.Consensus
