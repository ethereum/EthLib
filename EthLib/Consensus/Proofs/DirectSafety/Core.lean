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

/-- The keys of the validators active at the current or at the previous epoch of the state. -/
noncomputable def recentKeys {fork : Fork} (s : BeaconState preset fork) : Finset BLSPubkey :=
  activeKeys s ∪ keysAt s (getActiveValidatorIndices s (getPreviousEpoch s))

/-- The keys counted for a link are recent at the state that counts them.

Both participation flags and pending votes select validators active at the target epoch.

Only the pending votes of the state are an input. -/
private theorem counted_recent {fork : Fork} {state : BeaconState preset fork}
    {votes : Set (ValidatorIndex × AttestationData)} (pending : PendingVoted votes state)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch state) (current : Bool) (target : Checkpoint)
    (targetEpoch : target.epoch =
      if current then getCurrentEpoch state else getPreviousEpoch state)
    {indices : List ValidatorIndex} (counted : targetIndices state target.epoch = .ok indices) :
    keysAt state indices ⊆ recentKeys state := by
  classical
  have active : ∀ i ∈ indices, i ∈ getActiveValidatorIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state) := by
    intro i member
    rw [targetEpoch] at counted
    rcases targetIndices_ok counted with ⟨_, counted⟩ | ⟨before, _, matching, counted⟩
    · exact (mem_getUnslashedParticipatingIndices counted i member).1
    · -- A count is after the two epochs where equal justified fields are required.
      have notEarly : JustifiedEarly state := by
        intro small
        have smallNat := UInt64.le_iff_toNat_le.mp small
        have laterNat := UInt64.lt_iff_toNat_lt.mp later
        omega
      exact (PendingVoted.attester before pending notEarly current matching counted member).1
  intro key member
  simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at member
  obtain ⟨i, member, found⟩ := member
  have present : key ∈ keysAt state (getActiveValidatorIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state)) := by
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i, active i member, found⟩
  cases current
  · exact Finset.mem_union_right _ (by simpa using present)
  · exact Finset.mem_union_left _ (by simpa [activeKeys] using present)

/-- The keys that a justification test of the run counts are recent at the state of the test.

They are active at its current or its previous epoch.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem quorum_voters_recent {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : QuorumCall run) :
    call.voters ⊆ recentKeys call.cached :=
  counted_recent (cached_participation run parameters genesis call.toEpochCall).1
    call.later call.current call.target call.targetEpoch call.counted

/-- The keys that a quorum counts are recent at the state of its test.

The quorum is a quorum call of the run, or the test of one justification step at its last state.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem view_voters_recent {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    {view : TerminalView a} (call : ViewQuorum run view) :
    call.voters ⊆ recentKeys call.state.state := by
  cases call with
  | inl c => exact quorum_voters_recent run parameters genesis c
  | inr c =>
    -- The step counts at the last state, whose pending votes are those of the whole run.
    exact counted_recent (inherited_participation run .nil parameters genesis).1 c.later
      c.current c.target c.targetEpoch c.counted

end EthLib.Consensus.DirectSafety
