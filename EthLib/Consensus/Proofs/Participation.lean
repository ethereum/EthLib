module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Participation

/-!
# Proofs: participation flags

A flag that is added is set, at any index.

Each validator that participates with a flag in an epoch is active then and not slashed.

Its flag is set in the participation of that epoch.

An attestation earns flags only when its source is the justified checkpoint of its target epoch.

Its flags are the source, target and head flags, each at most once and in that order.

From Gloas a vote for the block of its own slot matches its payload exactly when its index is zero.

A vote for an earlier block matches when its index is the availability bit of the parent slot.

A head flag from Gloas needs a matching payload vote.

From Altair, a base reward is the base reward per increment, once for each whole increment.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- A flag that is added is set. -/
theorem hasFlag_addFlag (flags : ParticipationFlags) (flagIndex : UInt64) :
    hasFlag (addFlag flags flagIndex) flagIndex = true := by
  simp only [hasFlag, addFlag, beq_iff_eq]
  apply UInt8.toBitVec_inj.mp
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or]
  ext k
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases (flagBit flagIndex).toBitVec[k] <;> simp

/-- Each validator that participates with a flag in a recent epoch is active then and not slashed.

Its flag is set in the participation of that epoch. -/
theorem mem_getUnslashedParticipatingIndices {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {flagIndex : UInt64} {epoch : Epoch} {result : List ValidatorIndex}
    (computed : getUnslashedParticipatingIndices state altair flagIndex epoch = .ok result) :
    ∀ index ∈ result, index ∈ getActiveValidatorIndices state epoch ∧
      (∃ validator, getValidator state index = .ok validator ∧ validator.slashed = false) ∧
      ∃ flags,
        (if epoch = getCurrentEpoch state then (state.currentEpochParticipation altair).data
          else (state.previousEpochParticipation altair).data)[index.toNat]? = some flags ∧
        hasFlag flags flagIndex = true := by
  unfold getUnslashedParticipatingIndices at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨activeIndices, checked, read, readOk, rfl⟩ := computed
    have same : activeIndices = getActiveValidatorIndices state epoch := by
      unfold getActiveValidatorIndicesChecked at checked
      split at checked
      · exact (Except.ok.inj checked).symm
      · cases checked
    subst activeIndices
    intro index member
    simp only [List.mem_map, List.mem_filter] at member
    obtain ⟨⟨same, kept⟩, ⟨found, keptTrue⟩, rfl⟩ := member
    obtain ⟨candidate, active, step⟩ := mapM_ok_mem readOk _ found
    split at step
    · rename_i flags read
      simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at step
      obtain ⟨validator, validatorOk, rfl, rfl⟩ := step
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at keptTrue
      exact ⟨active, ⟨validator, validatorOk, keptTrue.2⟩, flags, read, keptTrue.1⟩
    · cases step
  · cases computed

/-- An attestation earns flags only when its source is the justified checkpoint it should vote for.

It is the current one for a target in the current epoch, and the previous one otherwise.

Its flags are the source, target and head flags, each at most once and in that order. -/
theorem getAttestationParticipationFlagIndices_spec {state : BeaconState preset fork}
    {data : AttestationData} {inclusionDelay : UInt64} {parentSlot : Slot} {flags : List UInt64}
    (computed :
      getAttestationParticipationFlagIndices state data inclusionDelay parentSlot = .ok flags) :
    data.source = (if data.target.epoch = getCurrentEpoch state then
        state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint) ∧
      flags.Sublist
        [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX] := by
  unfold getAttestationParticipationFlagIndices at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  by_cases matching : data.source = (if data.target.epoch = getCurrentEpoch state then
      state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true matching)] at computed
    cases computed
    refine ⟨matching, ?_⟩
    show List.Sublist _
      ([TIMELY_SOURCE_FLAG_INDEX] ++ [TIMELY_TARGET_FLAG_INDEX] ++ [TIMELY_HEAD_FLAG_INDEX])
    have single : ∀ (condition : Prop) [Decidable condition] (flag : UInt64),
        List.Sublist (if condition then [flag] else []) [flag] := by
      intro condition _ flag
      split <;> simp
    exact ((single _ _).append (single _ _)).append (single _ _)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false matching)] at computed
    cases computed

/-- From Gloas, a vote for the block of its own slot matches its payload when its index is zero.

Any other index is an error. -/
theorem payloadMatches_of_sameSlot {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {data : AttestationData} {parentSlot : Slot}
    (same : isAttestationSameSlot state data = .ok true) :
    payloadMatches state gloas data parentSlot =
      if data.index = 0 then .ok true else .error (.sameSlotIndexNotZero data.index) := by
  unfold payloadMatches
  simp only [same, bind, Except.bind, ↓reduceIte]
  split <;> rfl

/-- From Gloas, a vote for an earlier block matches its payload when its index is the bit.

The bit is the availability of the payload at the parent slot. -/
theorem payloadMatches_of_not_sameSlot {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {data : AttestationData} {parentSlot : Slot} {available : Bool}
    (notSame : isAttestationSameSlot state data = .ok false)
    (bit : (state.executionPayloadAvailability gloas).bits[
      (parentSlot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat]? = some available) :
    payloadMatches state gloas data parentSlot =
      .ok (data.index == if available then 1 else 0) := by
  unfold payloadMatches
  simp only [notSame, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, bit]
  rfl

/-- From Gloas, an attestation earns the head flag only when its payload vote matches. -/
theorem payloadMatches_of_head {state : BeaconState preset fork} (gloas : .glamsterdam ≤ fork)
    {data : AttestationData} {inclusionDelay : UInt64} {parentSlot : Slot} {flags : List UInt64}
    (computed :
      getAttestationParticipationFlagIndices state data inclusionDelay parentSlot = .ok flags)
    (head : TIMELY_HEAD_FLAG_INDEX ∈ flags) :
    payloadMatches state gloas data parentSlot = .ok true := by
  unfold getAttestationParticipationFlagIndices at computed
  simp only [gloas, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨_, _, payload, payloadOk, _, _, computed⟩ := computed
  by_cases matching : data.source = (if data.target.epoch = getCurrentEpoch state then
      state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true matching)] at computed
    cases computed
    simp only [List.mem_append] at head
    rcases head with (source | target) | head
    · split at source <;> simp_all [TIMELY_SOURCE_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX]
    · split at target <;> simp_all [TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX]
    · cases payload
      · simp at head
      · exact payloadOk
  · rw [ite_eq_right_of_eq_false _ _ (eq_false matching)] at computed
    cases computed

/-- From Altair, the base reward of a validator is the base reward per increment.

It counts once for each whole increment of the effective balance of the validator. -/
theorem getBaseReward_eq_mul_of_altair {state : BeaconState preset fork}
    (altair : .altair ≤ fork) {total perIncrement base : Gwei} {index : ValidatorIndex}
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement)
    (computed : getBaseReward state total index = .ok base) :
    ∃ validator, state.validators.data[index.toNat]? = some validator ∧
      base.toNat = validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        perIncrement.toNat := by
  simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff, per, Except.ok.injEq,
    exists_eq_left', liftArith, mapError_ok_iff, mulChecked_ok_iff] at computed
  obtain ⟨validator, found, -, product⟩ := computed
  refine ⟨validator, ?_, by rw [product, UInt64.toNat_div]⟩
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact read
  · cases found

end EthLib.Consensus
