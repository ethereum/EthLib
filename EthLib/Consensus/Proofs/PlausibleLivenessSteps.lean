module

public import EthLib.Consensus.Proofs.LivenessBlock
public import EthLib.Consensus.Proofs.LivenessVotes
public import EthLib.Consensus.Proofs.SlotCommitteeStake
import EthLib.Base.Proofs.MapM
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.PayloadInputs
import EthLib.Consensus.Proofs.Transition.RootLinks
import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the steps of plausible liveness on the beacon chain

Plausible liveness joins runs of slot steps and honest continuations through two epochs.

These are the facts that the joins need.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Models DirectSafety DirectSafety.Apriori

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The latest block header -/

/-- A block step leaves the latest block header at the slot of the state it reaches. -/
private theorem headerSlot_of_applySignedBlock {fork : Fork}
    {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (ok : applySignedBlock config checks engine before signed true = .ok after) :
    after.latestBlockHeader.slot = after.slot := by
  have processed := (applySignedBlock_ok ok).2.1
  obtain ⟨atSlot, -, -⟩ := processBlock_parentRoot processed
  obtain ⟨_, -, header⟩ := latestBlockHeader_processBlock processed
  rw [header, (frame_processBlock processed).slot, ← atSlot]

/-- A slot step keeps the slot of the latest block header and moves the slot on by one. -/
theorem headerSlot_of_advanceSlotAcross {forked after : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks forked = .ok after) :
    after.state.latestBlockHeader.slot = forked.state.latestBlockHeader.slot ∧
      after.state.slot.toNat = forked.state.slot.toNat + 1 := by
  obtain ⟨moved, -, -, _, -, header⟩ := advanceSlotAcross_cases ok
  refine ⟨?_, moved⟩
  rw [header]
  split <;> rfl

/-- The latest block header of a state reached from a genesis state is at its slot or before.

Each slot step keeps the header and moves the slot on, and each block puts the header at it. -/
theorem headerSlot_le_of_run {g x : ForkedBeaconState preset} (genesis : Genesis config checks g)
    (run : Run config checks g x) : x.state.latestBlockHeader.slot ≤ x.state.slot := by
  induction run with
  | nil =>
    rw [(genesis_header genesis).1]
    exact UInt64.zero_le
  | snoc _ step ih =>
    cases step with
    | slot ok =>
      obtain ⟨header, moved⟩ := headerSlot_of_advanceSlotAcross ok
      rw [header, UInt64.le_iff_toNat_le, moved]
      have := UInt64.le_iff_toNat_le.mp ih
      omega
    | block engine signed due ok =>
      rw [headerSlot_of_applySignedBlock ok]
      exact UInt64.le_refl _

/-! ## No upgrade due -/

/-- After a step, a state with a slot after its latest block header has no upgrade due. -/
theorem Step.notDue_of_fresh {before after : ForkedBeaconState preset}
    (step : Step config checks before after)
    (fresh : after.state.latestBlockHeader.slot < after.state.slot) :
    upgradeDue config after = false := by
  cases step with
  -- A slot step runs the upgrades.
  | slot ok =>
    obtain ⟨_, _, upgraded⟩ := bind_ok_iff.mp ok
    exact processUpgrades_upgradeDue upgraded
  -- A block would have put the header at the slot.
  --
  -- So the step is a slot step.
  | block engine signed due ok =>
    rw [headerSlot_of_applySignedBlock ok] at fresh
    exact absurd fresh (UInt64.lt_irrefl _)

/-- At the end of a run, a state with a slot after its latest block header has no upgrade due.

The first state must have no upgrade due, in case the run is empty. -/
theorem Run.notDue_of_fresh {first last : ForkedBeaconState preset}
    (run : Run config checks first last) (start : upgradeDue config first = false)
    (fresh : last.state.latestBlockHeader.slot < last.state.slot) :
    upgradeDue config last = false := by
  cases run with
  | nil => exact start
  | snoc _ step => exact step.notDue_of_fresh fresh

/-- A run that changes the epoch has no upgrade due at its end.

Its last state must have a slot after its latest block header. -/
theorem Run.notDue_of_moved {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (moved : getCurrentEpoch first.state ≠ getCurrentEpoch last.state)
    (fresh : last.state.latestBlockHeader.slot < last.state.slot) :
    upgradeDue config last = false := by
  cases run with
  | nil => exact absurd rfl moved
  | snoc _ step => exact step.notDue_of_fresh fresh

/-! ## Joining runs -/

/-- Each step of a run without blocks is a slot step, so it has each property of slot steps. -/
theorem Run.slotStep_of_blockCount {first last : ForkedBeaconState preset}
    (property : ∀ {before after : ForkedBeaconState preset}, Step config checks before after → Prop)
    (slot : ∀ {before after : ForkedBeaconState preset}
      (ok : advanceSlotAcross config checks before = .ok after), property (.slot ok))
    (run : Run config checks first last) (none : run.blockCount = 0)
    {before after : ForkedBeaconState preset} {step : Step config checks before after}
    (member : run.Contains step) : property step := by
  induction run with
  | nil => cases member
  | snoc pre next ih =>
    cases next with
    | slot ok =>
      cases member with
      | last => exact slot ok
      | earlier member => exact ih none member
    | block => simp [Run.blockCount] at none

/-- A run without blocks is honest. -/
theorem Run.honest_of_blockCount {first last : ForkedBeaconState preset}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (run : Run config checks first last) (none : run.blockCount = 0) :
    run.Honest config honest key :=
  fun _ member => run.slotStep_of_blockCount (fun step => step.Honest config honest key)
    (fun _ => by simp only [Step.Honest]) none member

/-- A run without blocks applies blocks only at the proposals. -/
theorem Run.blocksAt_of_blockCount {first last : ForkedBeaconState preset} {proposals : Set Slot}
    (run : Run config checks first last) (none : run.blockCount = 0) :
    run.BlocksAt proposals :=
  fun _ member => run.slotStep_of_blockCount (fun step => step.BlockAt proposals)
    (fun _ => by simp only [Step.BlockAt]) none member

/-- A vote of a run followed by a slot step is a vote of the run. -/
theorem Run.mem_votes_of_snocSlot {first middle last : ForkedBeaconState preset}
    {run : Run config checks first middle} {ok : advanceSlotAcross config checks middle = .ok last}
    {vote : ValidatorIndex × AttestationData} (member : vote ∈ (run.snoc (.slot ok)).votes) :
    vote ∈ run.votes := by
  obtain ⟨before, after, step, contained, voted⟩ := member
  cases contained with
  | last => exact absurd voted (Set.notMem_empty _)
  | earlier contained => exact ⟨before, after, step, contained, voted⟩

/-- A vote of a run without blocks followed by a run is a vote of the second run. -/
theorem Run.mem_votes_of_append {first middle last : ForkedBeaconState preset}
    {pre : Run config checks first middle} {tail : Run config checks middle last}
    (none : pre.blockCount = 0) {vote : ValidatorIndex × AttestationData}
    (member : vote ∈ (pre.append tail).votes) : vote ∈ tail.votes := by
  obtain ⟨before, after, step, contained, voted⟩ := member
  rcases (Run.contains_append pre tail step).mp contained with inPre | inTail
  -- A run without blocks casts no vote, so joining it in front keeps the votes of the rest.
  · rw [pre.slotStep_of_blockCount (fun step => step.votes = ∅) (fun _ => rfl) none inPre]
      at voted
    exact absurd voted (Set.notMem_empty _)
  · exact ⟨before, after, step, inTail, voted⟩

/-! ## Activity and slashing along a run -/

/-- Along a run from `x`, the epochs up to two after that of `x` keep their activity.

So an honest validator active at `x` in each such epoch is active in the epoch of a later state.

That epoch must be at most two after that of `x`, and the seed lookahead must reach two epochs. -/
theorem active_of_run {x w : ForkedBeaconState preset} {honest : Finset ValidatorIndex}
    (lookahead : 2 ≤ preset.MAX_SEED_LOOKAHEAD.toNat) (run : Run config checks x w)
    (high : (getCurrentEpoch w.state).toNat ≤ (getCurrentEpoch x.state).toNat + 2)
    (active : ∀ i ∈ honest, ∀ epoch : Epoch,
      epoch.toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
      (getCurrentEpoch x.state).toNat ≤ epoch.toNat →
        i ∈ getActiveValidatorIndices x.state epoch) :
    getCurrentEpoch w.state ≤ activityFixedEpoch x.state ∧
      ∀ i ∈ honest, i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state) := by
  have fixed : getCurrentEpoch w.state ≤ activityFixedEpoch x.state := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := (getCurrentEpoch w.state).toNat_lt
    omega
  refine ⟨fixed, fun i member => ?_⟩
  rw [(activeKept_of_chainSteps run.chainSteps).getActiveValidatorIndices_eq fixed]
  exact active i member _ high
    (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps run.chainSteps))

/-- After an honest run, a validator active at its end and unslashed at its start is unslashed. -/
theorem unslashed_of_honestRun {x w : ForkedBeaconState preset} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {run : Run config checks x w}
    (honestRun : run.Honest config honest key) {i : ValidatorIndex} {epoch : Epoch}
    (active : i ∈ getActiveValidatorIndices w.state epoch)
    (unslashed : (x.state.validators.data[i.toNat]?).map (·.slashed) = some false) :
    (w.state.validators.data[i.toNat]?).map (·.slashed) = some false := by
  have inside := lt_size_of_mem_getActiveValidatorIndices active
  rw [Array.getElem?_eq_getElem inside]
  cases flag : w.state.validators.data[i.toNat].slashed with
  | false => simp [flag]
  | true =>
    have back := honestRun.slashed_of_slashed i.toNat
      (by rw [Array.getElem?_eq_getElem inside]; simp [flag])
    rw [unslashed] at back
    cases back

/-! ## The justification test at the end of an epoch -/

/-- At the last slot of a later epoch, the honest validators outside that slot count.

They also hold two thirds of the active stake.

An honest run from `x` reaches the state, at most two epochs after that of `x`, before Gloas.

The votes of the other slots of its epoch are gathered, and the committees of its slot have values.

The margin of the honest stake without one slot holds at `x` for the epoch of the state. -/
theorem exists_counted_quorum {g x z : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x z)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (roots : preset.RootsReachPreviousEpoch)
    (lookahead : 2 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (guard : aprioriGuardAt config x ((getCurrentEpoch x.state).toNat + 1))
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (honestTail : tail.Honest config honest key)
    (active : ∀ i ∈ honest, ∀ epoch : Epoch,
      epoch.toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
      (getCurrentEpoch x.state).toNat ≤ epoch.toNat →
        i ∈ getActiveValidatorIndices x.state epoch)
    (unslashed : ∀ i ∈ honest,
      (x.state.validators.data[i.toNat]?).map (·.slashed) = some false)
    (margin : ∀ epoch : Epoch, (getCurrentEpoch x.state).toNat < epoch.toNat →
      epoch.toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
      ∀ excluded ⊆ (getActiveValidatorIndices x.state epoch).toFinset,
        excluded.card ≤ (getActiveValidatorIndices x.state epoch).length /
          preset.SLOTS_PER_EPOCH.toNat + 1 →
        2 * stake (fun i => balanceAt x.state i.toNat)
            (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset +
          stakeMargin config x ((getCurrentEpoch x.state).toNat + 1) ≤
        3 * stake (fun i => balanceAt x.state i.toNat) (honest \ excluded))
    (altair : .altair ≤ z.fork) (beforeGloas : z.fork < .glamsterdam)
    (low : (getCurrentEpoch x.state).toNat < (getCurrentEpoch z.state).toNat)
    (high : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch x.state).toNat + 2)
    (last : (z.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (shuffleRoom : (getActiveValidatorIndices z.state (getCurrentEpoch z.state)).length *
      ((getCommitteeCountPerSlot z.state (getCurrentEpoch z.state)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    (committees : ∃ committees : List (Array ValidatorIndex), (List.range
        (getCommitteeCountPerSlot z.state (getCurrentEpoch z.state)).toNat).mapM
      (fun position => getBeaconCommittee z.state z.state.slot position.toUInt64) =
        .ok committees)
    (gathered : VotesGathered honest z.state) :
    ∃ counted : Finset ValidatorIndex,
      (∀ indices, targetIndices z.state (getCurrentEpoch z.state) = .ok indices →
        counted ⊆ indices.toFinset) ∧
      2 * stake (fun index => balanceAt z.state index.toNat)
          (getActiveValidatorIndices z.state (getCurrentEpoch z.state)).toFinset ≤
        3 * stake (fun index => balanceAt z.state index.toNat) counted := by
  obtain ⟨list, listOk⟩ := committees
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := roots.twoSlots
    omega
  obtain ⟨fixed, activeZ⟩ := active_of_run lookahead tail high active
  have unslashedZ : ∀ i ∈ honest,
      (z.state.validators.data[i.toNat]?).map (·.slashed) = some false :=
    fun i member => unslashed_of_honestRun honestTail (activeZ i member) (unslashed i member)
  refine ⟨honest \ (list.flatMap Array.toList).toFinset,
    targetIndices_of_votesGathered altair last shuffleRoom gathered activeZ unslashedZ
      listOk, ?_⟩
  exact quorum_without_slot_of_stakeMargin shared tail genesis parameters caps aligned
    roots.twoSlots beforeGloas (by omega) guard activeZ unslashedZ
    (fun i member => active i member _ (by omega) (Nat.le_refl _))
    (fun i _ slashed => honestTail.slashed_of_slashed i.toNat slashed) fixed listOk
    (margin _ low high)

end EthLib.Consensus
