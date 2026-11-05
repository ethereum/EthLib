module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Participation

/-!
# Proofs: participation flags

A flag that is added is set, at any index.

Each validator that participates with a flag in an epoch is active then and not slashed.

Its flag is set in the participation of that epoch.

An attestation earns flags only when its source is the justified checkpoint of its target epoch.

Its flags are the source, target and head flags, each at most once and in that order.
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
    obtain ⟨read, readOk, rfl⟩ := computed
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
    {data : AttestationData} {inclusionDelay : UInt64} {flags : List UInt64}
    (computed : getAttestationParticipationFlagIndices state data inclusionDelay = .ok flags) :
    data.source = (if data.target.epoch = getCurrentEpoch state then
        state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint) ∧
      flags.Sublist
        [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX] := by
  unfold getAttestationParticipationFlagIndices at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
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

end EthLib.Consensus
