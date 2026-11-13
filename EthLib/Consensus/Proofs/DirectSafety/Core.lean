module

public import EthLib.Consensus.Proofs.DirectSafety.Conflict

/-!
# Support of the voters of a quorum call

Previous-epoch voters may have exited the current active set, so the support includes them.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The keys of the unslashed validators active at the current or at the previous epoch. -/
noncomputable def recentKeys {fork : Fork} (s : BeaconState preset fork) :
    Finset BLSPubkey := by
  classical
  exact (activeKeys s ∪ keysAt s (getActiveValidatorIndices s (getPreviousEpoch s))).filter
    (¬ SlashedAt s ·)

/-- The keys of the unslashed validators active at the current epoch. -/
noncomputable def unslashedKeys {fork : Fork} (s : BeaconState preset fork) :
    Finset BLSPubkey := by
  classical
  exact (activeKeys s).filter (¬ SlashedAt s ·)

-- With distinct keys, the key of an unslashed validator names no slashed validator.
private theorem not_slashedAt {fork : Fork} {state : BeaconState preset fork}
    (unique : PubkeysDistinct state) {v : Validator} (member : v ∈ state.validators.data.toList)
    (unslashed : v.slashed = false) : ¬ SlashedAt state v.pubkey := by
  rintro ⟨u, inside, key, slashed⟩
  have same : u = v := List.inj_on_of_nodup_map unique inside member key
  rw [same, unslashed] at slashed
  cases slashed

/-- The keys counted for a link are recent at the state that counts them.

Both participation flags and pending votes select unslashed validators active at the target epoch.

Only the pending votes of the state and distinct keys are inputs. -/
private theorem counted_recent {fork : Fork} {state : BeaconState preset fork}
    {votes : Set (ValidatorIndex × AttestationData)} (pending : PendingVoted votes state)
    (unique : PubkeysDistinct state)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch state) (current : Bool) (target : Checkpoint)
    (targetEpoch : target.epoch =
      if current then getCurrentEpoch state else getPreviousEpoch state)
    {indices : List ValidatorIndex} (counted : targetIndices state target.epoch = .ok indices) :
    keysAt state indices ⊆ recentKeys state := by
  classical
  have facts : ∀ i ∈ indices, i ∈ getActiveValidatorIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      ∃ v, getValidator state i = .ok v ∧ v.slashed = false := by
    intro i member
    rw [targetEpoch] at counted
    rcases targetIndices_ok counted with ⟨_, counted⟩ | ⟨before, _, matching, counted⟩
    · exact ⟨(mem_getUnslashedParticipatingIndices counted i member).1,
        (mem_getUnslashedParticipatingIndices counted i member).2.1⟩
    · -- A count is after the two epochs where equal justified fields are required.
      have notEarly : JustifiedEarly state := by
        intro small
        have smallNat := UInt64.le_iff_toNat_le.mp small
        have laterNat := UInt64.lt_iff_toNat_lt.mp later
        omega
      refine ⟨(PendingVoted.attester before pending notEarly current matching counted member).1,
        ?_⟩
      -- Before Altair the attesters are filtered to the unslashed ones.
      simp only [getUnslashedAttestingIndices, bind_ok_iff, unslashedAmong] at counted
      obtain ⟨_, _, filtered⟩ := counted
      have passes := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passes
      obtain ⟨v, found, fresh⟩ := passes
      exact ⟨v, found, by simpa using fresh⟩
  intro key member
  simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at member
  obtain ⟨i, member, found⟩ := member
  obtain ⟨active, v, validator, fresh⟩ := facts i member
  have at_ := getValidator_eq_ok_iff.mp validator
  rw [at_, Option.map_some, Option.some.injEq] at found
  subst found
  have present : v.pubkey ∈ keysAt state (getActiveValidatorIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state)) := by
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i, active, by simp [at_]⟩
  refine Finset.mem_filter.mpr ⟨?_, not_slashedAt unique
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? at_)) fresh⟩
  cases current
  · exact Finset.mem_union_right _ (by simpa using present)
  · exact Finset.mem_union_left _ (by simpa [activeKeys] using present)

/-- The keys that a justification test of the run counts are recent at the state of the test.

They are unslashed and active at its current or its previous epoch.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem quorum_voters_recent {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    (call : QuorumCall run) :
    call.voters ⊆ recentKeys call.cached :=
  counted_recent (cached_participation run parameters genesis call.toEpochCall).1
    (call.toEpochCall.pubkeysDistinct genesis)
    call.later call.current call.target call.targetEpoch call.counted

/-- The keys that a quorum counts are recent at the state of its test.

The quorum is a quorum call of the run, or the test of one justification step at its last state.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem view_voters_recent {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    {view : TerminalView a} (call : ViewQuorum run view) :
    call.voters ⊆ recentKeys call.state.state := by
  cases call with
  | inl c => exact quorum_voters_recent run parameters genesis c
  | inr c =>
    -- The step counts at the last state, whose pending votes are those of the whole run.
    exact counted_recent (inherited_participation run .nil parameters genesis).1
      (run.pubkeysDistinct genesis) c.later c.current c.target c.targetEpoch c.counted

end EthLib.Consensus.DirectSafety
