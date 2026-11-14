module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
public import EthLib.Consensus.Proofs.Transition.EpochDecomposition
public import EthLib.Consensus.Proofs.Transition.Totality.Inactivity
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits

/-!
# Proofs: the bounds that one epoch keeps

A run of slots carries bounds on the state from one epoch to the next.

From Altair, one epoch keeps every inactivity score within a bound plus the score bias.

The update of the scores adds at most the bias, and the other steps keep the scores.

A validator that a deposit adds starts at a score of zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- Every score of a state is at most a bound. -/
private def ScoresAtMost (altair : .altair ≤ fork) (bound : Nat) (state : BeaconState preset fork) :
    Prop :=
  ∀ score ∈ (state.inactivityScores altair).data, score.toNat ≤ bound

/-- A step that keeps the scores keeps their bound. -/
private theorem ScoresAtMost.of_eq {altair : .altair ≤ fork} {bound : Nat}
    (same : after.inactivityScores = state.inactivityScores)
    (scored : ScoresAtMost altair bound state) : ScoresAtMost altair bound after := by
  unfold ScoresAtMost
  rw [same]
  exact scored

/-- A new validator in the registry has a score of zero, which keeps the bound. -/
private theorem ScoresAtMost.of_addValidator {altair : .altair ≤ fork} {bound : Nat}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey credentials amount = .ok after)
    (scored : ScoresAtMost altair bound state) : ScoresAtMost altair bound after := by
  unfold addValidatorToRegistry at computed
  simp only [altair, ↓reduceDIte, addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, scoresOk, rfl⟩ := computed
  intro score member
  obtain ⟨i, _, rfl⟩ := Array.mem_iff_getElem.mp member
  have found := setOrAppendList_getElem? scoresOk i
  rw [Array.getElem?_eq_getElem ‹_›] at found
  split at found
  · rw [Option.some.injEq] at found
    rw [found]
    exact Nat.zero_le _
  · exact scored _ (Array.mem_iff_getElem?.mpr ⟨i, found.symm⟩)

/-- A pending deposit keeps the bound on the scores. -/
private theorem ScoresAtMost.of_applyPendingDeposit {altair : .altair ≤ fork} {bound : Nat}
    {config : Config} {checks : SignatureChecks} {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (scored : ScoresAtMost altair bound state) : ScoresAtMost altair bound after := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact scored
  · obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    exact scored
  · exact scored.of_addValidator added

/-- From Altair, a step after the update of the scores keeps their bound. -/
private theorem ScoresAtMost.of_action {altair : .altair ≤ fork} {bound : Nat}
    {config : Config} {checks : SignatureChecks} {stage : EpochStage}
    (member : stage ∈ [.rewards, .registry, .slashings, .eth1Reset, .pendingDeposits,
      .pendingConsolidations, .payments, .effectiveBalances])
    (computed : action config checks stage state = .ok after)
    (scored : ScoresAtMost altair bound state) : ScoresAtMost altair bound after := by
  have edge := action_cases.mp computed
  cases stage <;> simp only [Edge] at edge <;> try (simp at member; done)
  case rewards => exact scored.of_eq (by rw [processRewardsAndPenalties_frame edge])
  case registry => exact scored.of_eq (processRegistryUpdates_fields edge).2.2.2.1
  case slashings => exact scored.of_eq (by rw [processSlashings_frame edge])
  case eth1Reset =>
    split at edge
    · exact scored.of_eq (by rw [processEth1DataReset_frame edge])
    · subst edge
      exact scored
  case pendingDeposits =>
    split at edge
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ :=
        processPendingDeposits_applied edge
      have kept := foldlM_ok_invariant (g := applyPendingDeposit config checks)
        (ScoresAtMost altair bound) (fun _ _ _ prior step => prior.of_applyPendingDeposit step)
        scored folded
      exact kept.of_eq rfl
    · subst edge
      exact scored
  case pendingConsolidations =>
    split at edge
    · exact scored.of_eq (processPendingConsolidations_fields edge).2.2.2.1
    · subst edge
      exact scored
  case payments =>
    split at edge
    · exact scored.of_eq (by rw [processBuilderPendingPayments_eq edge])
    · subst edge
      exact scored
  case effectiveBalances => exact scored.of_eq (by rw [processEffectiveBalanceUpdates_frame edge])

/-- From Altair, one epoch keeps every inactivity score within a bound plus the score bias.

Take a bound on every score before the epoch.

After it, every score is at most that bound plus the bias. -/
theorem processEpoch_scoreBound {config : Config} {checks : SignatureChecks}
    (altair : .altair ≤ fork) {bound : Nat}
    (scored : ∀ score ∈ (state.inactivityScores altair).data, score.toNat ≤ bound)
    (computed : processEpoch config checks state = .ok after) :
    ∀ score ∈ (after.inactivityScores altair).data,
      score.toNat ≤ bound + config.INACTIVITY_SCORE_BIAS.toNat := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity] ++ ([.rewards, .registry, .slashings,
    .eth1Reset, .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances] ++
    [.slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow])) _ _ at trace
  obtain ⟨middle, head, rest⟩ := append_iff.mp trace
  obtain ⟨settled, middleTrace, last⟩ := append_iff.mp rest
  rcases head with _ | ⟨justified, _ | ⟨updated, _ | _⟩⟩
  have edge := action_cases.mp updated
  simp only [Edge, altair, ↓reduceDIte] at edge
  have justifiedScores := processJustificationAndFinalization_inactivityScores
    (action_cases.mp justified)
  have bounded : ScoresAtMost altair (bound + config.INACTIVITY_SCORE_BIAS.toNat) middle :=
    processInactivityUpdates_scoreBound edge fun score member => by
      rw [justifiedScores] at member
      exact scored score member
  have carried := middleTrace.transport
    (fun first second => ScoresAtMost altair (bound + config.INACTIVITY_SCORE_BIAS.toNat) first →
      ScoresAtMost altair (bound + config.INACTIVITY_SCORE_BIAS.toNat) second)
    (fun _ => id) (fun one two held => two (one held))
    (fun _ member _ _ ok held => held.of_action member ok) bounded
  exact ScoresAtMost.of_eq (sameBalancesRegistryScores_tail altair last).2.2 carried

end EthLib.Consensus
