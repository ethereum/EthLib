module

public import EthLib.Consensus.Proofs.Participation
public import EthLib.Consensus.Proofs.Transition.Operations

/-!
# Proofs: where a timely target flag comes from, in one attestation

From Altair the state keeps one byte of flags for each validator, in each of two epochs.

They are the current and the previous epoch.

Justification adds the stake of the unslashed validators whose byte holds the timely target flag.

An attestation sets that flag only for its attesters, and only for a vote of the right link.

Its data then has the justified checkpoint of its target epoch as source.

Its target epoch is the current or the previous one.

Its target root is the root of the block at the first slot of that epoch.

The attester is in the indexed attestation, whose aggregate signature passed the checks of the step.

With the BLS checks, the aggregate signature verifies under keys that include the attester's.

Reading that as its signature assumes that no one forges a BLS aggregate.

No other position gains the target flag, and the other epoch gains none.

This is the step of one attestation toward the invariant that justification counts only such votes.

Gasper §4.4, Definition 4.5, justifies a checkpoint by the stake of the votes for one link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- From Altair: the flags of the current epoch when asked for it, else of the previous epoch. -/
def recentParticipation (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (current : Bool) : EpochParticipation preset fork :=
  if current then state.currentEpochParticipation altair
  else state.previousEpochParticipation altair

/-- From Altair: the byte at a position of a list of flags holds the timely target flag. -/
def TargetFlagAt (participation : EpochParticipation preset fork) (position : Nat) : Prop :=
  ∃ flags, participation.data[position]? = some flags ∧
    hasFlag flags TIMELY_TARGET_FLAG_INDEX = true

/-- Setting a flag other than the target flag never sets the target flag. -/
private theorem hasFlag_addFlag_target (flags : ParticipationFlags) (flag : Fin 3)
    (set : hasFlag (addFlag flags flag.val.toUInt64) TIMELY_TARGET_FLAG_INDEX = true) :
    hasFlag flags TIMELY_TARGET_FLAG_INDEX = true ∨
      flag.val.toUInt64 = TIMELY_TARGET_FLAG_INDEX := by
  have other : ∀ bit : ParticipationFlags, bit &&& flagBit TIMELY_TARGET_FLAG_INDEX = 0 →
      hasFlag (flags ||| bit) TIMELY_TARGET_FLAG_INDEX =
        hasFlag flags TIMELY_TARGET_FLAG_INDEX := by
    intro bit clear
    have cleared := congrArg UInt8.toBitVec clear
    simp only [hasFlag]
    congr 1
    apply UInt8.toBitVec_inj.mp
    simp only [UInt8.toBitVec_and, UInt8.toBitVec_or] at cleared ⊢
    rw [BitVec.and_or_distrib_right, cleared]
    simp
  match flag with
  | ⟨1, _⟩ => exact .inr rfl
  | ⟨0, _⟩ => exact .inl (by rw [← other (flagBit (0 : Nat).toUInt64) (by decide)]; exact set)
  | ⟨2, _⟩ => exact .inl (by rw [← other (flagBit (2 : Nat).toUInt64) (by decide)]; exact set)

/-- The flags that an attestation earns hold the timely target flag only in one case.

Its target root is the root of the block at the first slot of its target epoch. -/
theorem getAttestationParticipationFlagIndices_targetRoot {data : AttestationData}
    {inclusionDelay : UInt64} {parentSlot : Slot} {earned : List UInt64}
    (computed :
      getAttestationParticipationFlagIndices state data inclusionDelay parentSlot = .ok earned)
    (target : TIMELY_TARGET_FLAG_INDEX ∈ earned) :
    getBlockRoot state data.target.epoch = .ok data.target.root := by
  unfold getAttestationParticipationFlagIndices at computed
  simp only [bind_ok_iff] at computed
  generalize (if data.target.epoch = getCurrentEpoch state then state.currentJustifiedCheckpoint
    else state.previousJustifiedCheckpoint) = justified at computed
  obtain ⟨root, rootOk, _, _, _, _, final⟩ := computed
  split at final
  · simp only [pure, Except.pure, Except.ok.injEq] at final
    subst final
    rw [rootOk]
    simp [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX] at target
    rw [target.1.2]
  · cases final

/-- One flag of one attester sets the target flag only if it was set or the step earns it. -/
private theorem addFlagReward_target {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {flags flags' : ParticipationFlags} {numerator numerator' : Gwei}
    {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    (computed :
      addFlagReward state total earned index (flags, numerator) flag = .ok (flags', numerator'))
    (set : hasFlag flags' TIMELY_TARGET_FLAG_INDEX = true) :
    hasFlag flags TIMELY_TARGET_FLAG_INDEX = true ∨ TIMELY_TARGET_FLAG_INDEX ∈ earned := by
  unfold addFlagReward at computed
  dsimp only at computed
  split at computed
  · rename_i chosen
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    rcases hasFlag_addFlag_target flags flag set with old | same
    · exact .inl old
    · exact .inr (same ▸ chosen.1)
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, _⟩ := computed
    exact .inl set

/-- One attester keeps the size, and sets the target flag only at its own position if earned. -/
private theorem addAttesterFlags_target {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {participation updated : EpochParticipation preset fork}
    {numerator numerator' : Gwei}
    (computed :
      addAttesterFlags state total earned (participation, numerator) index =
        .ok (updated, numerator')) :
    updated.data.size = participation.data.size ∧
      ∀ position, TargetFlagAt updated position →
        TargetFlagAt participation position ∨
          TIMELY_TARGET_FLAG_INDEX ∈ earned ∧ index.toNat = position := by
  unfold addAttesterFlags at computed
  dsimp only at computed
  split at computed
  · rename_i inside
    simp only [bind_ok_iff] at computed
    obtain ⟨⟨flags, _⟩, fold, final⟩ := computed
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, _⟩ := final
    have byte : hasFlag flags TIMELY_TARGET_FLAG_INDEX = true →
        hasFlag participation.data[index.toNat] TIMELY_TARGET_FLAG_INDEX = true ∨
          TIMELY_TARGET_FLAG_INDEX ∈ earned :=
      foldlM_ok_invariant
        (fun step => hasFlag step.1 TIMELY_TARGET_FLAG_INDEX = true →
          hasFlag participation.data[index.toNat] TIMELY_TARGET_FLAG_INDEX = true ∨
            TIMELY_TARGET_FLAG_INDEX ∈ earned)
        (fun ⟨_, _⟩ _ ⟨_, _⟩ holds step set =>
          (addFlagReward_target step set).elim holds .inr)
        .inl fold
    refine ⟨by simp, fun position ⟨value, found, set⟩ => ?_⟩
    rw [Array.getElem?_set] at found
    split at found
    · rename_i same
      cases found
      rcases byte set with old | chosen
      · exact .inl ⟨_, by rw [← same]; exact Array.getElem?_eq_getElem inside, old⟩
      · exact .inr ⟨chosen, same⟩
    · exact .inl ⟨value, found, set⟩
  · cases computed

/-- Adding flags of the three kinds sets the target flag only if it was set or is among them. -/
theorem hasFlag_foldl_addFlag_target :
    ∀ (flags : List UInt64) (old : ParticipationFlags),
      flags.Sublist [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX] →
      hasFlag (flags.foldl addFlag old) TIMELY_TARGET_FLAG_INDEX = true →
      hasFlag old TIMELY_TARGET_FLAG_INDEX = true ∨ TIMELY_TARGET_FLAG_INDEX ∈ flags
  | [], _, _, set => .inl set
  | flag :: rest, old, kinds, set => by
    have known : flag ∈ [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX,
        TIMELY_HEAD_FLAG_INDEX] := kinds.subset List.mem_cons_self
    rcases hasFlag_foldl_addFlag_target rest (addFlag old flag)
        ((List.sublist_cons_self flag rest).trans kinds) set with middle | later
    · simp only [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX, TIMELY_HEAD_FLAG_INDEX,
        List.mem_cons, List.not_mem_nil, or_false] at known
      rcases known with rfl | rfl | rfl
      · exact (hasFlag_addFlag_target old ⟨0, by decide⟩ middle).imp id (absurd · (by decide))
      · exact .inr List.mem_cons_self
      · exact (hasFlag_addFlag_target old ⟨2, by decide⟩ middle).imp id (absurd · (by decide))
    · exact .inr (List.mem_cons_of_mem flag later)

/-- A fold whose steps each set a target flag only at the position of their index, if earned.

After it, a target flag was there before, or is at the position of an index of the list.

The fold may carry more than the flags, which a projection reads. -/
theorem foldlM_targetFlag {σ : Type} {earned : Prop} {flagsOf : σ → EpochParticipation preset fork}
    {step : σ → ValidatorIndex → Except TransitionError σ}
    (each : ∀ carried index updated, step carried index = .ok updated →
      ∀ position, TargetFlagAt (flagsOf updated) position →
        TargetFlagAt (flagsOf carried) position ∨ earned ∧ index.toNat = position) :
    ∀ (indices : List ValidatorIndex) (start finish : σ),
      indices.foldlM step start = .ok finish → ∀ position, TargetFlagAt (flagsOf finish) position →
        TargetFlagAt (flagsOf start) position ∨ earned ∧ ∃ index ∈ indices, index.toNat = position
  | [], start, finish, computed, position, flagged => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .inl flagged
  | first :: rest, start, finish, computed, position, flagged => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, middleOk, computed⟩ := computed
    rcases foldlM_targetFlag each rest middle finish computed position flagged with
      old | ⟨chosen, index, member, place⟩
    · rcases each start first middle middleOk position old with older | ⟨chosen, place⟩
      · exact .inl older
      · exact .inr ⟨chosen, first, List.mem_cons_self, place⟩
    · exact .inr ⟨chosen, index, List.mem_cons_of_mem first member, place⟩

/-- From Altair, setting the flags of attesters keeps the size of the list of flags.

A position gains the timely target flag only if the earned flags hold it.

That position is then the position of one of the attesters. -/
theorem foldlM_addAttesterFlags_target {total : Gwei} {earned : List UInt64}
    {attesters : List ValidatorIndex} {participation updated : EpochParticipation preset fork}
    {numerator numerator' : Gwei}
    (computed : attesters.foldlM (addAttesterFlags state total earned) (participation, numerator) =
      .ok (updated, numerator')) :
    updated.data.size = participation.data.size ∧
      ∀ position, TargetFlagAt updated position →
        TargetFlagAt participation position ∨
          TIMELY_TARGET_FLAG_INDEX ∈ earned ∧
            ∃ attester ∈ attesters, attester.toNat = position := by
  refine ⟨foldlM_ok_invariant
      (fun (carried : EpochParticipation preset fork × Gwei) =>
        carried.1.data.size = participation.data.size)
      (fun ⟨_, _⟩ _ ⟨_, _⟩ holds ok => (addAttesterFlags_target ok).1.trans holds) rfl computed,
    fun position flagged => ?_⟩
  exact foldlM_targetFlag (flagsOf := Prod.fst)
    (fun ⟨_, _⟩ _ ⟨_, _⟩ ok => (addAttesterFlags_target ok).2) attesters _ _ computed position
    flagged

/-- From Altair, a target flag that an attestation sets comes from a vote that passed the checks.

With the BLS checks, that vote carries a valid aggregate signature.

The flag is at a position of the flags of the current epoch, or else of the previous one.

Either it was there before, or the attestation set it, and then five facts hold.

The indexed attestation exists, and its aggregate signature passes the checks of the step.

It holds the data of the attestation, and an attester at that position.

The target epoch is the epoch of those flags.

The source is the justified checkpoint that the state holds for that epoch.

The target root is the root of the block at the first slot of that epoch. -/
theorem processAttestationAltair_targetFlag {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after)
    (current : Bool) (position : Nat)
    (flagged : TargetFlagAt (recentParticipation after altair current) position) :
    TargetFlagAt (recentParticipation state altair current) position ∨
      ∃ indexed, getIndexedAttestation state attestation = .ok indexed ∧
        isValidIndexedAttestation config checks state indexed = .ok true ∧
        indexed.data = attestation.data ∧
        (∃ attester ∈ indexed.attestingIndices.data, attester.toNat = position) ∧
        attestation.data.target.epoch =
          (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
        attestation.data.source =
          (if current then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint) ∧
        getBlockRoot state attestation.data.target.epoch = .ok attestation.data.target.root := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, recent, _, _, _, _, _, _, _, _, _, _, earned, earnedOk, indexed, indexedOk,
    valid, validOk, _, checked, _, _, attesters, attestersOk, ⟨updated, _⟩, fold, _, _,
    raised, raisedOk, final⟩ := computed
  have kept :
      recentParticipation after altair current = recentParticipation raised altair current := by
    split at final
    · rw [recordPaymentWeight_eq final]
      rfl
    · cases final
      rfl
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  simp only [BeaconState.putBalance, recentParticipation] at kept
  unfold recentParticipation at flagged
  rw [kept] at flagged
  rw [ensure_ok_iff] at checked recent
  subst checked
  obtain ⟨indexed', indexedOk', indices, dataEq, -⟩ :=
    getIndexedAttestation_of_getAttestingIndices attestersOk
  rw [indexedOk] at indexedOk'
  cases indexedOk'
  have members : ∀ attester ∈ attesters, attester ∈ indexed.attestingIndices.data :=
    fun _ member => by
      rw [indices]
      exact List.mem_toArray.mpr member
  obtain ⟨source, -⟩ := getAttestationParticipationFlagIndices_spec earnedOk
  generalize chosen : (attestation.data.target.epoch == getCurrentEpoch state) = same
    at fold flagged
  have moved := (foldlM_addAttesterFlags_target fold).2 position
  cases same <;> cases current
  · rcases moved (by simpa [setEpochParticipation] using flagged) with
      old | ⟨target, attester, member, place⟩
    · exact .inl (by simpa [recentParticipation] using old)
    have root := getAttestationParticipationFlagIndices_targetRoot earnedOk target
    have other : attestation.data.target.epoch ≠ getCurrentEpoch state := ne_of_beq_false chosen
    refine .inr ⟨indexed, indexedOk, validOk, dataEq, ⟨attester, members _ member, place⟩,
      recent.resolve_right other, ?_, root⟩
    simpa [other] using source
  · exact .inl (by simpa [setEpochParticipation, recentParticipation] using flagged)
  · exact .inl (by simpa [setEpochParticipation, recentParticipation] using flagged)
  · rcases moved (by simpa [setEpochParticipation] using flagged) with
      old | ⟨target, attester, member, place⟩
    · exact .inl (by simpa [recentParticipation] using old)
    have root := getAttestationParticipationFlagIndices_targetRoot earnedOk target
    have here : attestation.data.target.epoch = getCurrentEpoch state := beq_iff_eq.mp chosen
    refine .inr ⟨indexed, indexedOk, validOk, dataEq, ⟨attester, members _ member, place⟩,
      here, ?_, root⟩
    simpa [here] using source

end EthLib.Consensus
