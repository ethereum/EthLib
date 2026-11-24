module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
public import EthLib.Consensus.Proofs.Transition.DepositCarry
public import EthLib.Consensus.Proofs.Transition.EpochDecomposition
public import EthLib.Consensus.Proofs.Transition.Totality.Inactivity
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
public import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Consensus.Proofs.Transition.Slot
import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoadBlock
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.SlashingsHistory

/-!
# Proofs: the bounds that one epoch keeps

A run of slots carries bounds on the state from one epoch to the next.

One epoch keeps four bounds:

- From Altair, every inactivity score stays within a bound plus the score bias.
- The sum of the slashed balances never rises, since one epoch only resets one entry.
- One epoch adds at most one historical root, and from Capella at most one historical summary.
- From Electra, the churn carried for deposits grows by at most the cap of the deposit churn.

After one epoch, the effective balances sum to at most 4/3 of the balances on mainnet.

That needs a state that keeps the invariant.

Only the pending deposits grow the registry, by at most their cap at each epoch start.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

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
  -- The update of the scores adds at most the bias.
  have bounded : ScoresAtMost altair (bound + config.INACTIVITY_SCORE_BIAS.toNat) middle :=
    processInactivityUpdates_scoreBound edge fun score member => by
      rw [justifiedScores] at member
      exact scored score member
  -- The other steps keep the scores, and a validator that a deposit adds starts at zero.
  have carried := middleTrace.transport
    (fun first second => ScoresAtMost altair (bound + config.INACTIVITY_SCORE_BIAS.toNat) first →
      ScoresAtMost altair (bound + config.INACTIVITY_SCORE_BIAS.toNat) second)
    (fun _ => id) (fun one two held => two (one held))
    (fun _ member _ _ ok held => held.of_action member ok) bounded
  exact ScoresAtMost.of_eq (sameBalancesRegistryScores_tail altair last).2.2 carried

/-- Writing a zero into a list never raises the sum of its entries. -/
private theorem sum_set_zero_le (values : List Nat) (position : Nat) :
    (values.set position 0).sum ≤ values.sum := by
  induction values generalizing position with
  | nil => simp
  | cons head tail ih =>
    cases position with
    | zero => simp
    | succ position =>
      simp only [List.set_cons_succ, List.sum_cons]
      have := ih position
      omega

/-- The slashings reset never raises the slashed balance sum and keeps the historical records. -/
private theorem slashingsReset_facts {config : Config} {checks : SignatureChecks}
    (computed : action config checks .slashingsReset state = .ok after) :
    slashedBalanceSum after ≤ slashedBalanceSum state ∧
      after.historicalRoots = state.historicalRoots ∧
      after.historicalSummaries = state.historicalSummaries := by
  obtain ⟨_, slashings, _, written, rfl⟩ := processSlashingsReset_eq (action_cases.mp computed)
  refine ⟨?_, rfl, rfl⟩
  unfold slashedBalanceSum
  unfold writeCircularRooted at written
  split at written
  · cases written
  · cases written
    simp only [Serialization.Ssz.RootedVector.elements_set, Vector.toList_set, List.map_set]
    -- The reset sets one entry to zero, so the sum does not rise.
    exact sum_set_zero_le _ _

/-- The history update keeps the slashed balances, and adds at most one entry to each list. -/
private theorem history_facts {config : Config} {checks : SignatureChecks}
    (computed : action config checks .history state = .ok after) :
    after.slashings = state.slashings ∧
      after.historicalRoots.data.size ≤ state.historicalRoots.data.size + 1 ∧
      ∀ capella : .shapella ≤ fork, (after.historicalSummaries capella).data.size ≤
        (state.historicalSummaries capella).data.size + 1 := by
  have edge := action_cases.mp computed
  simp only [Edge] at edge
  split at edge
  · obtain ⟨_, kept⟩ := processHistoricalSummariesUpdate_eq edge
    split at kept
    · obtain ⟨_, _, _, _, pushed, same⟩ := kept
      rw [← same]
      refine ⟨rfl, Nat.le_succ_of_le (Nat.le_refl _), fun capella => ?_⟩
      rw [pushed]
      simp
    · subst kept
      exact ⟨rfl, Nat.le_succ_of_le (Nat.le_refl _), fun _ => Nat.le_succ_of_le (Nat.le_refl _)⟩
  · obtain ⟨_, kept⟩ := processHistoricalRootsUpdate_eq (Nat.lt_of_not_le (by assumption)) edge
    split at kept
    · obtain ⟨_, _, pushed, same⟩ := kept
      rw [← same]
      refine ⟨rfl, ?_, fun _ => Nat.le_succ_of_le (Nat.le_refl _)⟩
      rw [pushed]
      simp
    · subst kept
      exact ⟨rfl, Nat.le_succ_of_le (Nat.le_refl _), fun _ => Nat.le_succ_of_le (Nat.le_refl _)⟩

/-- The history update splits an epoch into the steps before it, itself, and the steps after it.

The steps before never raise the slashed balance sum and keep the historical records.

The steps after keep the slashed balances and the historical records. -/
private theorem history_cut {config : Config} {checks : SignatureChecks}
    (computed : processEpoch config checks state = .ok after) :
    ∃ before mid, action config checks .history before = .ok mid ∧
      slashedBalanceSum before ≤ slashedBalanceSum state ∧
      before.historicalRoots = state.historicalRoots ∧
      before.historicalSummaries = state.historicalSummaries ∧
      after.slashings = mid.slashings ∧ after.historicalRoots = mid.historicalRoots ∧
      after.historicalSummaries = mid.historicalSummaries := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
    .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances, .slashingsReset,
    .randaoReset] ++ (.history :: [.participation, .syncCommittees, .proposerLookahead,
    .ptcWindow])) _ _ at trace
  obtain ⟨before, head, rest⟩ := append_iff.mp trace
  cases rest with
  | cons historyOk tail =>
    obtain ⟨summed, roots, summaries⟩ := head.transport
      (fun (first second : BeaconState preset fork) =>
        slashedBalanceSum second ≤ slashedBalanceSum first ∧
          second.historicalRoots = first.historicalRoots ∧
          second.historicalSummaries = first.historicalSummaries)
      (fun _ => ⟨Nat.le_refl _, rfl, rfl⟩)
      (fun one two => ⟨Nat.le_trans two.1 one.1, two.2.1.trans one.2.1, two.2.2.trans one.2.2⟩)
      fun stage member _ _ ok => by
        by_cases reset : stage = .slashingsReset
        · subst reset
          exact slashingsReset_facts ok
        · obtain ⟨slashings, roots, summaries⟩ := (action_cases.mp ok).slashingsHistory
            ⟨reset, by rintro rfl; simp at member⟩
          refine ⟨?_, roots, summaries⟩
          unfold slashedBalanceSum
          rw [slashings]
    obtain ⟨slashings, roots', summaries'⟩ := tail.transport
      (fun (first second : BeaconState preset fork) => second.slashings = first.slashings ∧
        second.historicalRoots = first.historicalRoots ∧
        second.historicalSummaries = first.historicalSummaries)
      (fun _ => ⟨rfl, rfl, rfl⟩)
      (fun one two => ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.trans one.2.2⟩)
      fun stage member _ _ ok => (action_cases.mp ok).slashingsHistory
        ⟨by rintro rfl; simp at member, by rintro rfl; simp at member⟩
    exact ⟨before, _, historyOk, summed, roots, summaries, slashings, roots', summaries'⟩

/-- One epoch never raises the sum of the slashed balances.

It only writes a zero into the entry of the next epoch. -/
theorem processEpoch_slashedBalanceSum_le {config : Config} {checks : SignatureChecks}
    (computed : processEpoch config checks state = .ok after) :
    slashedBalanceSum after ≤ slashedBalanceSum state := by
  obtain ⟨_, _, historyOk, summed, -, -, slashings, -, -⟩ := history_cut computed
  obtain ⟨kept, -, -⟩ := history_facts historyOk
  unfold slashedBalanceSum at summed ⊢
  rwa [slashings, kept]

/-- One epoch adds at most one root to the list of historical roots. -/
theorem processEpoch_historicalRoots_size_le {config : Config} {checks : SignatureChecks}
    (computed : processEpoch config checks state = .ok after) :
    after.historicalRoots.data.size ≤ state.historicalRoots.data.size + 1 := by
  obtain ⟨_, _, historyOk, -, roots, -, -, roots', -⟩ := history_cut computed
  obtain ⟨-, bound, -⟩ := history_facts historyOk
  rwa [roots', ← roots]

/-- From Capella, one epoch adds at most one entry to the historical summaries. -/
theorem processEpoch_historicalSummaries_size_le {config : Config} {checks : SignatureChecks}
    (capella : .shapella ≤ fork) (computed : processEpoch config checks state = .ok after) :
    (after.historicalSummaries capella).data.size ≤
      (state.historicalSummaries capella).data.size + 1 := by
  obtain ⟨_, _, historyOk, -, -, summaries, -, -, summaries'⟩ := history_cut computed
  obtain ⟨-, -, bound⟩ := history_facts historyOk
  rw [summaries', ← summaries]
  exact bound capella

/-- From Electra, one epoch raises the churn carried for deposits by at most the cap of its fork.

The deposits use the churn of the epoch plus the churn carried.

They carry what is left only when they reach the churn; otherwise they carry nothing. -/
theorem processEpoch_depositBalanceToConsume_le {config : Config} {checks : SignatureChecks}
    (electra : .pectra ≤ fork) (computed : processEpoch config checks state = .ok after) :
    (after.depositBalanceToConsume electra).toNat ≤
      (state.depositBalanceToConsume electra).toNat + depositChurnCap config fork := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ (.pendingDeposits :: [.pendingConsolidations, .payments, .effectiveBalances,
    .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow])) _ _ at trace
  obtain ⟨before, head, rest⟩ := append_iff.mp trace
  cases rest with
  | cons depositsOk tail =>
    have first := head.transport (fun (first second : BeaconState preset fork) =>
        second.depositBalanceToConsume = first.depositBalanceToConsume)
      (fun _ => rfl) (fun one two => Eq.trans two one) fun stage member _ _ ok =>
      (action_cases.mp ok).depositCarry (by rintro rfl; simp at member)
    have third := tail.transport (fun (first second : BeaconState preset fork) =>
        second.depositBalanceToConsume = first.depositBalanceToConsume)
      (fun _ => rfl) (fun one two => Eq.trans two one) fun stage member _ _ ok =>
      (action_cases.mp ok).depositCarry (by rintro rfl; simp at member)
    have edge := action_cases.mp depositsOk
    simp only [Edge, electra, ↓reduceDIte] at edge
    have bound := processPendingDeposits_depositBalanceToConsume_le edge
    rw [third]
    rw [first] at bound
    exact bound

/-- A step that keeps the balances matching the registry and the effective balances whole. -/
private def BalancesAligned (state after : BeaconState preset fork) : Prop :=
  (BalancesMatch state → BalancesMatch after) ∧
    (MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state →
      EffectiveBalancesAligned after)

/-- A state relates to itself. -/
private theorem BalancesAligned.refl (state : BeaconState preset fork) :
    BalancesAligned state state :=
  ⟨id, fun _ => id⟩

/-- Two related steps in a row are related. -/
private theorem BalancesAligned.trans {first second third : BeaconState preset fork}
    (one : BalancesAligned first second) (two : BalancesAligned second third) :
    BalancesAligned first third :=
  ⟨two.1 ∘ one.1, fun maxAligned => two.2 maxAligned ∘ one.2 maxAligned⟩

/-- A frame keeps the balances matching and the effective balances whole. -/
private theorem BalancesAligned.of_frame (frame : Frame state after) :
    BalancesAligned state after :=
  ⟨frame.balancesMatch, frame.aligned⟩

/-- The steps of an epoch before the update of the effective balances keep two facts.

The balances match the registry, and the effective balances stay whole. -/
private theorem BalancesAligned.of_action {config : Config} {checks : SignatureChecks}
    {stage : EpochStage}
    (member : stage ∈ [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
      .pendingDeposits, .pendingConsolidations, .payments])
    (computed : action config checks stage state = .ok after) : BalancesAligned state after := by
  have edge := action_cases.mp computed
  by_cases justification : stage = .justification
  · subst justification
    simp only [Edge] at edge
    rw [processJustificationAndFinalization_eq edge]
    exact ⟨id, fun _ => id⟩
  by_cases deposits : stage = .pendingDeposits
  · subst deposits
    simp only [Edge] at edge
    split at edge
    · exact .of_frame (mutatorEpochFrameLaws.processPendingDeposits edge).toEpochFrame.toFrame
    · subst edge
      exact .refl _
  by_cases payments : stage = .payments
  · subst payments
    simp only [Edge] at edge
    split at edge
    · exact .of_frame (frame_processBuilderPendingPayments edge).toEpochFrame.toFrame
    · subst edge
      exact .refl _
  exact .of_frame (mutatorEpochFrameLaws.toEpochStepLaws.epochEdge
    ⟨justification, payments, by rintro rfl; simp at member, deposits⟩ computed
    ).toEpochFrame.toFrame

/-- After one epoch, the effective balances sum to at most a fixed factor of the balances.

The factor is the hysteresis quotient divided by that quotient less the downward multiplier.

It says something only when the downward multiplier is below the quotient.

On mainnet it is 4/3. -/
theorem processEpoch_effectiveBalanceSum_le {config : Config} {checks : SignatureChecks}
    -- The state must satisfy the state invariant.
    --
    -- The largest effective balances must be whole increments.
    (holds : Invariant state) (maxAligned : MaxEffectiveBalancesAligned preset)
    (computed : processEpoch config checks state = .ok after) :
    effectiveBalanceSum after *
        (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
      balanceSum after * preset.HYSTERESIS_QUOTIENT.toNat := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
    .pendingDeposits, .pendingConsolidations, .payments] ++ (.effectiveBalances ::
    [.slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow])) _ _ at trace
  obtain ⟨before, head, rest⟩ := append_iff.mp trace
  cases rest with
  | cons updatedOk tail =>
    have prior := head.transport BalancesAligned (fun _ => BalancesAligned.refl _)
      (fun one two => one.trans two) fun _ member _ _ ok => .of_action member ok
    have kept := tail.transport (fun (first second : BeaconState preset fork) =>
        second.validators = first.validators ∧ second.balances = first.balances)
      (fun _ => ⟨rfl, rfl⟩)
      (fun one two => ⟨Eq.trans two.1 one.1, Eq.trans two.2 one.2⟩) fun stage member _ _ ok => by
      obtain ⟨validators, balances, -⟩ := (action_cases.mp ok).records
        ⟨by rintro rfl; simp at member, by rintro rfl; simp at member,
          by rintro rfl; simp at member, by rintro rfl; simp at member,
          by rintro rfl; simp at member, by rintro rfl; simp at member⟩
      exact ⟨validators, balances⟩
    have bound := processEffectiveBalanceUpdates_effectiveBalanceSum_le
      (prior.1 holds.balancesMatch) (prior.2 maxAligned (holds.aligned maxAligned))
      (action_cases.mp updatedOk)
    unfold effectiveBalanceSum balanceSum at bound ⊢
    rw [kept.1, kept.2]
    exact bound

/-! ## The registry grows only by pending deposits at epoch starts -/

section RegistryGrowth

variable {config : Config} {checks : SignatureChecks}

/-- The pending deposits of an epoch add at most `MAX_PENDING_DEPOSITS_PER_EPOCH` validators. -/
private theorem processPendingDeposits_validators_size_le {fork : Base.Fork}
    {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks s electra = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  -- Applied deposits form a sublist of the bounded prefix read by this pass.
  obtain ⟨read, rest, applied, postponed, next, pending, carried,
    _, _, cap, subset, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  have growth := foldlM_validators_size_le
    (fun _ _ _ h => (applyPendingDeposit_validators_size_le_and_mem h).1) folded
  have count := subset.length_le
  dsimp only
  omega

/-- An epoch adds at most `MAX_PENDING_DEPOSITS_PER_EPOCH` validators, at every fork. -/
private theorem processEpoch_validators_size_le {fork : Base.Fork} {s t : BeaconState preset fork}
    (ok : processEpoch config checks s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  have trace := processEpoch_trace ok
  change EpochTrace _ ([.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ (.pendingDeposits :: .pendingConsolidations :: EpochStage.middleStages ++
      EpochStage.tailStages)) _ _ at trace
  obtain ⟨reset, head, rest⟩ := EpochTrace.append_iff.mp trace
  cases rest
  rename_i deposited depositedOk rest
  -- Every stage other than the pending deposits keeps the size of the registry.
  have same {ks : List EpochStage} {a b : BeaconState preset fork}
      (trace : EpochTrace (EpochStage.action config checks) ks a b)
      (without : EpochStage.pendingDeposits ∉ ks) :
      b.validators.data.size = a.validators.data.size := by
    refine trace.transport
      (fun a b : BeaconState preset fork => b.validators.data.size = a.validators.data.size)
      (fun _ => rfl) (fun one two => two.trans one) ?_
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    cases k
    case registry => exact (sameSizes_processRegistryUpdates edge).1
    case effectiveBalances => exact (sameSizes_processEffectiveBalanceUpdates edge).1
    case pendingDeposits => exact absurd member without
    all_goals exact congrArg (·.data.size) (edge.validators_eq ⟨nofun, nofun, nofun⟩)
  have before := same head (by simp)
  have after := same rest (by simp [EpochStage.middleStages, EpochStage.tailStages])
  have edge := EpochStage.action_cases.mp depositedOk
  have middle : deposited.validators.data.size ≤ reset.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits_validators_size_le edge
    · subst edge
      omega
  omega

/-- One slot adds at most `MAX_PENDING_DEPOSITS_PER_EPOCH` validators for each epoch it starts. -/
theorem advanceSlot_validators_size_le {fork : Base.Fork} {s t : BeaconState preset fork}
    (ok : advanceSlot config checks s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
        ((getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  obtain ⟨next, cached, epoched, nextOk, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cacheEq⟩ := processSlot_ok cachedOk
  have cacheSize : cached.validators.data.size = s.validators.data.size := by rw [cacheEq]
  have cacheSlot := processSlot_slot cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    -- Charge the pending-deposit cap only when this slot crosses an epoch boundary.
    have epochs := nextSlot_epoch_of_boundary nextOk boundary
    have growth := processEpoch_validators_size_le epochedOk
    have diff : (getCurrentEpoch { epoched with slot := next }).toNat -
        (getCurrentEpoch s).toNat = 1 := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      dsimp only
      omega
    rw [diff, one_mul]
    dsimp only
    omega
  · cases epochedOk
    dsimp only
    omega

/-- Slots add at most one epoch of pending deposits to the registry for each epoch they cross. -/
theorem advanceSlots_validators_size_le :
    ∀ (count : ℕ) {s t : BeaconState preset fork}, advanceSlots config checks count s = .ok t →
      (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat ∧
        t.validators.data.size ≤ s.validators.data.size +
          ((getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat) *
            preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
  | 0, s, t, ok => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    simp
  | count + 1, s, t, ok => by
    simp only [advanceSlots, bind_ok_iff] at ok
    obtain ⟨next, step, rest⟩ := ok
    have slotEq := advanceSlot_slot step
    have grow := advanceSlot_validators_size_le step
    obtain ⟨later, growRest⟩ := advanceSlots_validators_size_le count rest
    have earlier : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch next).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotEq]
      exact Nat.div_le_div_right (Nat.le_succ _)
    refine ⟨earlier.trans later, ?_⟩
    have split : (getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat =
        ((getCurrentEpoch t).toNat - (getCurrentEpoch next).toNat) +
          ((getCurrentEpoch next).toNat - (getCurrentEpoch s).toNat) := by omega
    rw [split, Nat.add_mul]
    omega

/-- Processing slots adds at most one epoch of pending deposits for each epoch it crosses. -/
theorem processSlots_validators_size_le {s t : BeaconState preset fork} {slot : Slot}
    (ok : processSlots config checks s slot = .ok t) :
    (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat ∧
      t.validators.data.size ≤ s.validators.data.size +
        ((getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  unfold processSlots at ok
  simp only [bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨_, _, advanced⟩ := ok
  exact advanceSlots_validators_size_le _ advanced

/-- From Gloas, a block adds no validator, so its transition adds only what its slots add. -/
theorem stateTransition_validators_size_le (gloas : .glamsterdam ≤ fork)
    {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (ok : stateTransition config checks engine s signed validateResult = .ok t) :
    (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat ∧
      t.validators.data.size ≤ s.validators.data.size +
        ((getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok ok
  obtain ⟨later, grow⟩ := processSlots_validators_size_le slotsOk
  have block := processBlock_validators_size_le blockOk
  have none : blockDepositCount signed.message.body = 0 := by
    unfold blockDepositCount
    exact dite_eq_right_of_eq_false (eq_false (Nat.not_lt_of_le gloas))
  have sameEpoch : getCurrentEpoch t = getCurrentEpoch advanced := by
    simp only [getCurrentEpoch, processBlock_slot blockOk]
  rw [sameEpoch]
  exact ⟨later, by omega⟩

end RegistryGrowth

end EthLib.Consensus
