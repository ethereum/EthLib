module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Upgrade
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Totality.ShapeBlock

/-!
# Preservation of the deposit carry

Blocks and the epoch operations other than pending deposits keep the carry.

The Electra upgrade initializes it to zero, and later upgrades before Gloas keep it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}
  {s t : BeaconState preset fork}

private abbrev Kept (s t : BeaconState preset fork) : Prop :=
  t.depositBalanceToConsume = s.depositBalanceToConsume

private theorem kept_fold {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x t, step s x = .ok t → Kept s t) {items : List α}
    (ok : items.foldlM step s = .ok t) : Kept s t :=
  foldlM_ok_invariant (Kept s) (fun _ _ _ before ok => (kept _ _ _ ok).trans before) rfl ok

private theorem kept_setValidatorAt {index : Nat} {v : Validator}
    (ok : s.setValidatorAt index v = .ok t) : Kept s t := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

private theorem kept_setValidator {index : ValidatorIndex} {v : Validator}
    (ok : s.setValidator index v = .ok t) : Kept s t :=
  kept_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem kept_setBalance {index : ValidatorIndex} {balance : Gwei}
    (ok : s.setBalance index balance = .ok t) : Kept s t := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  rfl

private theorem kept_increase {index : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s index amount = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  exact kept_setBalance set

private theorem kept_decrease {index : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s index amount = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  exact kept_setBalance set

private theorem kept_exitQueue {amount : Gwei} {epoch : Epoch}
    (ok : exitQueue config s amount = .ok (t, epoch)) : Kept s t := by
  unfold exitQueue at ok
  split at ok
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := ok
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, rfl, _⟩ := ok
    rfl

private theorem kept_exit {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) : Kept s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · rfl
  · exact (kept_setValidator set).trans (kept_exitQueue queue)

/-- The epoch steps keep the deposit balance to consume. -/
theorem depositCarryLaws : EpochStepLaws (fork := fork) (preset := preset)
    fun s t => t.depositBalanceToConsume = s.depositBalanceToConsume where
  refl _ := rfl
  trans one two := two.trans one
  setValidatorAt set _ _ _ _ _ := kept_setValidatorAt set
  increaseBalance := kept_increase
  decreaseBalance := kept_decrease
  initiateValidatorExit := kept_exit
  eth1DataVotes _ _ := rfl
  inactivityScores _ _ := rfl
  slashings _ _ := rfl
  randaoMixes _ _ := rfl
  historicalRoots _ _ := rfl
  historicalSummaries _ _ := rfl
  participationRecords _ := rfl
  pendingConsolidations _ _ := rfl
  syncCommittees _ _ _ := rfl
  proposerLookahead _ _ := rfl
  ptcWindow _ _ := rfl

/-- Every epoch stage other than the pending deposits keeps the deposit balance to consume. -/
theorem EpochStage.Edge.depositCarry {stage : EpochStage}
    (edge : EpochStage.Edge config checks stage s t) (other : stage ≠ .pendingDeposits) :
    t.depositBalanceToConsume = s.depositBalanceToConsume := by
  by_cases ordinary : stage ≠ .justification ∧ stage ≠ .payments ∧ stage ≠ .participation ∧
      stage ≠ .pendingDeposits
  · exact depositCarryLaws.epochEdge ordinary (EpochStage.action_cases.mpr edge)
  -- The laws leave out justification, the payments and the rotation of the flags.
  cases stage
  case justification | payments | participation =>
    exact (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.1
  case pendingDeposits => exact absurd rfl other
  all_goals exact absurd ⟨nofun, nofun, nofun, nofun⟩ ordinary

private theorem kept_excess {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : Kept s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    have same := kept_setBalance set
    exact same
  · cases ok; rfl

private theorem depositCarry_upgradeToElectra {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    t.depositBalanceToConsume (by decide) = 0 := by
  simp only [upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := ok
  have one := kept_fold (fun _ _ _ ok => by
    simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
    exact (kept_setValidator validator).trans (kept_setBalance balance)) queued
  have two := kept_fold (fun _ _ _ ok => by
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · exact kept_excess (liftAccessor_ok.mp ok)
      · cases ok; rfl
    · cases ok; rfl) compounded
  exact congrFun (two.trans one) (by decide)

private theorem kept_upgradeNext {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) :
    (if h : .pectra ≤ t.val.fork then (t.val.state.depositBalanceToConsume h).toNat else 0) =
      (if h : .pectra ≤ s.fork then (s.state.depositBalanceToConsume h).toNat else 0) := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, _, rfl⟩ := ok
    rfl
  · subst ok; rfl
  · subst ok; rfl
  · subst ok; rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [show Fork.pectra ≤ .pectra from by decide, ↓reduceDIte]
    rw [depositCarry_upgradeToElectra upgraded]
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    rfl
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

theorem depositCarry_processUpgrades {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam) :
    (if h : .pectra ≤ t.fork then (t.state.depositBalanceToConsume h).toNat else 0) =
      (if h : .pectra ≤ s.fork then (s.state.depositBalanceToConsume h).toNat else 0) :=
  processUpgrades_induction (property := fun u => u.fork < .glamsterdam →
      (if h : .pectra ≤ u.fork then (u.state.depositBalanceToConsume h).toNat else 0) =
        (if h : .pectra ≤ s.fork then (s.state.depositBalanceToConsume h).toNat else 0))
    (fun {_ post} held nextOk later =>
      (kept_upgradeNext nextOk later).trans (held (Nat.lt_trans post.property later)))
    (fun _ => rfl) ok early

/-- A block keeps the deposit carry.

This holds at every fork. -/
theorem depositCarry_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} (_early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume :=
  (processBlock_blockKept ok).depositCarry

end EthLib.Consensus
