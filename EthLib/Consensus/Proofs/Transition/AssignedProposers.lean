module

public import EthLib.Consensus.Proofs.Proposers
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.ProposerLookahead
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# Proofs: along a run, each proposer of the lookahead names an assigned validator

From Fulu the state keeps the proposers of the current epoch and the next `MIN_SEED_LOOKAHEAD` ones.

Each was drawn active in its epoch, so its activation epoch is assigned.

No later step clears an assigned activation epoch.

So from Fulu, the proposer of each state of a run from genesis is a validator of the registry.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- From Fulu, each entry of the lookahead names a validator of the registry.

That validator has an assigned activation epoch.

Before Fulu the state has no lookahead, and the property holds. -/
def AssignedProposers {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ fulu : .fusaka ≤ f, ∀ i ∈ (s.proposerLookahead fulu).toList,
    ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH

/-- Each proposer of an epoch names a validator with an assigned activation epoch. -/
theorem getBeaconProposerIndices_assigned {f : Fork} {s : BeaconState preset f} {epoch : Epoch}
    {proposers : Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat}
    (ok : getBeaconProposerIndices s epoch = .ok proposers) :
    ∀ i ∈ proposers.toList,
      ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  intro i member
  obtain ⟨v, found, active⟩ := getBeaconProposerIndices_active ok i member
  exact ⟨v, found, Internal.assigned_of_active active⟩

/-- Proposers stay assigned from one state to another that keeps the lifecycle of the registry.

The two states may be of different forks. -/
theorem AssignedProposers.transfer {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (held : AssignedProposers s) (life : RegistryLifecycle s t)
    -- From Fulu, the lookahead of the second state is a lookahead of the first.
    (back : ∀ late : .fusaka ≤ g, ∃ early : .fusaka ≤ f,
      t.proposerLookahead late = s.proposerLookahead early) : AssignedProposers t := by
  intro late i member
  obtain ⟨early, same⟩ := back late
  rw [same] at member
  obtain ⟨v, found, assigned⟩ := held early i member
  obtain ⟨w, read, kept⟩ := life.validators i.toNat v found
  exact ⟨w, read, (kept.activationEpoch assigned) ▸ assigned⟩

/-- Each entry of a drawn lookahead names a validator with an assigned activation epoch. -/
theorem initializeProposerLookahead_assigned {f : Fork} {s : BeaconState preset f}
    {lookahead : Vector ValidatorIndex
      ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)}
    (ok : initializeProposerLookahead s = .ok lookahead) :
    ∀ i ∈ lookahead.toList,
      ∃ v, s.validators.data[i.toNat]? = some v ∧ v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  intro i member
  obtain ⟨k, inside, rfl⟩ := List.getElem_of_mem member
  obtain ⟨_, _, -, computed, drawn⟩ :=
    initializeProposerLookahead_drawn ok k (by simpa using inside)
  exact getBeaconProposerIndices_assigned computed _ (by simpa using drawn)

/-- A successful update of the lookahead keeps each of its proposers assigned. -/
theorem AssignedProposers.refresh {f : Fork} {s t : BeaconState preset f}
    {fulu : .fusaka ≤ f} (held : AssignedProposers s)
    (ok : processProposerLookahead s fulu = .ok t) : AssignedProposers t := by
  obtain ⟨epoch, _, rest⟩ := bind_ok_iff.mp ok
  obtain ⟨last, drawn, final⟩ := bind_ok_iff.mp rest
  cases final
  intro _ i member
  obtain ⟨j, inside, rfl⟩ := List.getElem_of_mem member
  simp only [Vector.getElem_toList, Vector.getElem_ofFn]
  split
  · exact held fulu _ (by simp)
  · exact getBeaconProposerIndices_assigned drawn _ (by simp)

private theorem assignedProposers_processEpoch {fork : Fork} {s t : BeaconState preset fork}
    (held : AssignedProposers s) (ok : processEpoch config checks s = .ok t) :
    AssignedProposers t := by
  by_cases fulu : .fusaka ≤ fork
  · obtain ⟨m, looked, -, mLook, draw, validators, lookEq, -⟩ :=
      processEpoch_lookahead_cut fulu ok
    -- The state before the draw has the lookahead of the start and the registry of the end.
    have before : AssignedProposers m := held.transfer
      ((registryLifecycle_processEpoch ok).trans (.of_data validators.symm))
      (fun late => ⟨late, congrFun mLook late⟩)
    -- The draw is the lookahead stage, which keeps the validators.
    have edge : EpochStage.Edge config checks .proposerLookahead m looked := by
      simp only [EpochStage.Edge, fulu, ↓reduceDIte]
      exact draw
    have same := edge.validators_eq ⟨nofun, nofun, nofun⟩
    exact (before.refresh draw).transfer (.of_data (by rw [validators, same]))
      (fun late => ⟨late, congrFun lookEq late⟩)
  · exact fun later => absurd later fulu

private theorem assignedProposers_advanceSlot {fork : Fork} {s t : BeaconState preset fork}
    (held : AssignedProposers s) (ok : advanceSlot config checks s = .ok t) :
    AssignedProposers t := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have cachedHeld : AssignedProposers cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact held.transfer (.of_data rfl) (fun late => ⟨late, rfl⟩)
  have epochedHeld : AssignedProposers epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact assignedProposers_processEpoch cachedHeld epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ cachedHeld
  exact epochedHeld.transfer (.of_data rfl) (fun late => ⟨late, rfl⟩)

private theorem assignedProposers_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (held : AssignedProposers pre.state) (ok : upgradeNext config checks pre = .ok post) :
    AssignedProposers post.val.state := by
  by_cases early : .fusaka ≤ pre.fork
  -- From Fulu the upgrades to Gloas and to Heze copy the lookahead.
  · exact held.transfer (registryLifecycle_upgradeNext ok)
      (fun _ => ⟨early, upgradeNext_proposerLookahead ok early⟩)
  -- The upgrade to Fulu draws the lookahead from its registry.
  · intro late i member
    obtain ⟨fork, state⟩ := pre
    cases fork <;>
      simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
        throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
    case pectra =>
      obtain ⟨_, upgraded, rfl⟩ := ok
      simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at upgraded
      obtain ⟨lookahead, drawn, rfl⟩ := upgraded
      exact initializeProposerLookahead_assigned drawn i member
    all_goals first
      | exact (early (by dsimp only; decide)).elim
      | (obtain ⟨_, _, rfl⟩ := ok; exact absurd late (by dsimp only; decide))

private theorem assignedProposers_chainStep {x y : ForkedBeaconState preset}
    (step : ChainStep config checks x y) (held : AssignedProposers x.state) :
    AssignedProposers y.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    exact processUpgrades_induction (config := config) (checks := checks)
      (forked := ⟨x.fork, advanced⟩) (property := fun u => AssignedProposers u.state)
      (fun before stepOk => assignedProposers_upgradeNext before stepOk)
      (assignedProposers_advanceSlot held advancedOk) upgraded
  | block engine signed validated ok =>
    exact held.transfer (RegistryLifecycle.chainStep (.block engine signed validated ok))
      (fun late => ⟨late, congrFun (processBlock_proposerLookahead (applySignedBlock_ok ok).2.1)
        late⟩)

/-- Along a run from a genesis of deposits, each proposer of the lookahead is assigned.

From Fulu it names a validator of the registry with an assigned activation epoch. -/
theorem Run.assignedProposers {g x : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (run : Run config checks g x) :
    AssignedProposers x.state := by
  induction run with
  | nil =>
    -- Genesis is before Fulu, so it has no lookahead.
    obtain ⟨_, _, _, before, initialized⟩ := genesis
    exact fun fulu => (Nat.not_le_of_lt before (Nat.le_trans (by decide) fulu)).elim
  | snoc pre step ih => exact assignedProposers_chainStep step.chainStep ih

/-- A proposer read from a state that holds the property names an assigned validator.

Before Fulu the proposer is drawn from the active validators, so it is assigned too. -/
theorem AssignedProposers.selected {f : Fork} {s : BeaconState preset f}
    (held : AssignedProposers s) {proposer : ValidatorIndex}
    (ok : getBeaconProposerIndex s = .ok proposer) :
    ∃ v, s.validators.data[proposer.toNat]? = some v ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  unfold getBeaconProposerIndex at ok
  split at ok
  · -- From Fulu the proposer is an entry of the lookahead.
    rename_i fulu
    split at ok
    · cases ok
    · cases ok
      exact held fulu _ (by apply List.getElem_mem)
  · -- Before Fulu the proposer is drawn from the active validators of the epoch.
    obtain ⟨seed, _, rest⟩ := bind_ok_iff.mp ok
    obtain ⟨active, checked, drawn⟩ := bind_ok_iff.mp rest
    obtain ⟨v, found, live⟩ :=
      (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp
        (List.mem_toArray.mp (mem_of_computeProposerIndex drawn))
    exact ⟨v, found, Internal.assigned_of_active live⟩

/-- From Fulu, a state that a run reaches from genesis has a proposer for its slot.

That proposer is a validator of the registry.

An epoch of the preset must have at least one slot. -/
theorem Run.getBeaconProposerIndex_ok {g x : ForkedBeaconState preset}
    (nonzero : preset.SLOTS_PER_EPOCH ≠ 0) (genesis : Genesis config checks g)
    (run : Run config checks g x) (fulu : .fusaka ≤ x.fork) :
    ∃ proposer, getBeaconProposerIndex x.state = .ok proposer ∧
      proposer.toNat < x.state.validators.data.size := by
  -- From Fulu the proposer is an entry of the lookahead, so the read succeeds.
  have read : ∃ proposer, getBeaconProposerIndex x.state = .ok proposer := by
    unfold getBeaconProposerIndex
    simp only [fulu, nonzero, ↓reduceDIte]
    exact ⟨_, rfl⟩
  obtain ⟨proposer, read⟩ := read
  -- Each entry of the lookahead names a validator of the registry.
  obtain ⟨_, found, -⟩ := (run.assignedProposers genesis).selected read
  exact ⟨proposer, read, (Array.getElem?_eq_some_iff.mp found).1⟩

end EthLib.Consensus
