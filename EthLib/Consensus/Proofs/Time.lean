module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Time

/-!
# Proofs: slots, epochs and times

The first slot of an epoch lies in that epoch, and every slot lies after its epoch's first slot.

The slot at the start time of a slot is that slot.

Each conversion fails exactly when its result leaves the 64-bit range.
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

end EthLib.Consensus
