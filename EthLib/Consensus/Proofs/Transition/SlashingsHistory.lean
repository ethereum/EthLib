module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
import EthLib.Consensus.Proofs.Transition.EpochParticipation

/-!
# Proofs: the epoch stages that keep the slashed balances and the history

Every epoch stage keeps the slashed balances, the historical roots and the historical summaries.

The two exceptions are the slashings reset and the history update.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}

/-- An epoch stage keeps three fields, unless it is the slashings reset or the history update.

The fields are the slashed balances, the historical roots and the historical summaries. -/
theorem EpochStage.Edge.slashingsHistory {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t)
    (other : stage ≠ .slashingsReset ∧ stage ≠ .history) :
    t.slashings = s.slashings ∧ t.historicalRoots = s.historicalRoots ∧
      t.historicalSummaries = s.historicalSummaries := by
  cases stage <;> simp only [EpochStage.Edge] at edge
  case slashingsReset | history => simp at other
  case justification =>
    rw [processJustificationAndFinalization_eq edge]
    exact ⟨rfl, rfl, rfl⟩
  case inactivity =>
    split at edge
    · rw [processInactivityUpdates_frame edge]
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case rewards =>
    rw [processRewardsAndPenalties_frame edge]
    exact ⟨rfl, rfl, rfl⟩
  case registry =>
    obtain ⟨slashings, -, -, -, roots, summaries, -⟩ := processRegistryUpdates_fields edge
    exact ⟨slashings, roots, summaries⟩
  case slashings =>
    rw [processSlashings_frame edge]
    exact ⟨rfl, rfl, rfl⟩
  case eth1Reset =>
    split at edge
    · rw [processEth1DataReset_frame edge]
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case pendingDeposits =>
    split at edge
    · exact processPendingDeposits_history edge
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case pendingConsolidations =>
    split at edge
    · obtain ⟨-, -, -, -, -, -, summaries, slashings, roots⟩ :=
        processPendingConsolidations_fields edge
      exact ⟨slashings, roots, summaries⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case payments =>
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case effectiveBalances =>
    rw [processEffectiveBalanceUpdates_frame edge]
    exact ⟨rfl, rfl, rfl⟩
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    exact ⟨rfl, rfl, rfl⟩
  case participation =>
    split at edge
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
    · unfold processParticipationRecordUpdates at edge
      split at edge
      · cases edge
      simp only [pure, Except.pure, Except.ok.injEq] at edge
      subst edge
      exact ⟨rfl, rfl, rfl⟩
  case syncCommittees =>
    split at edge
    · unfold processSyncCommitteeUpdates at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case ptcWindow =>
    split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩

end EthLib.Consensus
