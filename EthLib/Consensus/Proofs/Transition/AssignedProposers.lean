module

public import EthLib.Consensus.Proofs.Transition.ValidatorStep
import EthLib.Consensus.Proofs.Transition.ProposerLookahead
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# Proofs: along a run, each proposer of the lookahead names an assigned validator

From Fulu the state keeps the proposers of this epoch and of the next `MIN_SEED_LOOKAHEAD` epochs.

Each was drawn active in the epoch it was drawn for, so its activation epoch is assigned.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

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
    exact (refreshed_proposers before draw).transfer (.of_data (by rw [validators, same]))
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
      exact initialized_proposers drawn i member
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
    obtain ⟨_, _, _, initialized⟩ := genesis
    have before := (initializeBeaconStateFromEth1_ok initialized).1
    exact fun fulu => (Nat.not_le_of_lt before (Nat.le_trans (by decide) fulu)).elim
  | snoc pre step ih => exact assignedProposers_chainStep step.chainStep ih

end EthLib.Consensus
