module

public import EthLib.Consensus.Proofs.Transition.EpochDecomposition
public import EthLib.Consensus.Proofs.Transition.Totality.Bound
public import EthLib.Consensus.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.BuilderPayments
import EthLib.Consensus.Proofs.Transition.EpochJustification
import EthLib.Consensus.Proofs.Transition.EpochParticipation
import EthLib.Consensus.Proofs.Transition.EpochRewards
import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# Proofs: the shape of the state that a run of slots keeps

The totality theorems of the epoch steps read lists indexed by the registry.

They assume that each such list has one entry for each validator.

From Electra they also assume each effective balance at most the largest one of its validator.

Before Electra they assume a bound that this one implies.

From Electra, they assume that each queued consolidation names two validators of the registry.

One epoch keeps these facts, and so does one slot and a run of slots within a fork.

So do the upgrades, when the caps of the preset grow at Electra.

A deposit appends one entry to each list.

The rotation of the flags writes a fresh list of the registry size.

The update of the effective balances caps each one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The facts on the shape of a state that the epoch steps assume.

The balances, the flags and the scores have one entry for each validator.

Each effective balance is within its cap.

From Electra, each queued consolidation is inside the registry. -/
structure Shaped (state : BeaconState preset fork) : Prop where
  balancesMatch : BalancesMatch state
  participationMatches : ParticipationMatches state
  inactivityScoresMatch : InactivityScoresMatch state
  capped : EffectiveBalancesCapped state
  inside : ConsolidationsInside state

/-- The facts of the shape other than the caps, which each stage of an epoch keeps. -/
private structure Sized (state : BeaconState preset fork) : Prop where
  balancesMatch : BalancesMatch state
  participationMatches : ParticipationMatches state
  inactivityScoresMatch : InactivityScoresMatch state
  inside : ConsolidationsInside state

/-- A state of the right shape has the facts other than the caps. -/
private theorem Shaped.sized {s : BeaconState preset fork} (shaped : Shaped s) : Sized s :=
  ⟨shaped.balancesMatch, shaped.participationMatches, shaped.inactivityScoresMatch, shaped.inside⟩

/-- The facts other than the caps and the caps give the shape. -/
private theorem Sized.shaped {s : BeaconState preset fork} (sized : Sized s)
    (capped : EffectiveBalancesCapped s) : Shaped s :=
  ⟨sized.balancesMatch, sized.participationMatches, sized.inactivityScoresMatch, capped,
    sized.inside⟩

/-- A step that keeps the registry, the queue of consolidations and the sizes keeps the facts. -/
private theorem Sized.of_kept {s t : BeaconState preset fork} (sized : Sized s)
    (validators : t.validators = s.validators)
    (balances : BalancesMatch s → BalancesMatch t)
    (participation : ParticipationMatches s → ParticipationMatches t)
    (scores : InactivityScoresMatch s → InactivityScoresMatch t)
    (consolidations : t.pendingConsolidations = s.pendingConsolidations) : Sized t := by
  refine ⟨balances sized.balancesMatch, participation sized.participationMatches,
    scores sized.inactivityScoresMatch, ?_⟩
  unfold ConsolidationsInside
  rw [validators, consolidations]
  exact sized.inside

/-- A step that keeps every list that the facts read keeps the facts. -/
private theorem Sized.of_eq {s t : BeaconState preset fork} (sized : Sized s)
    (validators : t.validators = s.validators := by rfl)
    (balances : t.balances = s.balances := by rfl)
    (previous : t.previousEpochParticipation = s.previousEpochParticipation := by rfl)
    (current : t.currentEpochParticipation = s.currentEpochParticipation := by rfl)
    (scores : t.inactivityScores = s.inactivityScores := by rfl)
    (consolidations : t.pendingConsolidations = s.pendingConsolidations := by rfl) :
    Sized t :=
  sized.of_kept validators
    (fun matched => by unfold BalancesMatch; rw [validators, balances]; exact matched)
    (fun sized altair => by rw [validators, previous, current]; exact sized altair)
    (fun scored altair => by rw [validators, scores]; exact scored altair) consolidations

/-- One stage of the epoch keeps the facts other than the caps. -/
private theorem Sized.of_action {stage : EpochStage} {s t : BeaconState preset fork}
    (computed : action config checks stage s = .ok t) (shaped : Sized s) : Sized t := by
  have edge := action_cases.mp computed
  cases stage <;> simp only [Edge] at edge
  case justification =>
    rw [processJustificationAndFinalization_eq edge]
    exact shaped.of_eq
  case inactivity =>
    split at edge
    · have sizes := processInactivityUpdates_sizes edge
      rw [processInactivityUpdates_frame edge]
      refine shaped.of_kept rfl id id (fun scored altair => ?_) rfl
      rw [← scored altair]
      exact sizes.2
    · subst edge
      exact shaped
  case rewards =>
    have matched := (mutatorEpochFrameLaws.toEpochStepLaws.epochEdge (stage := .rewards)
      ⟨nofun, nofun, nofun, nofun⟩ computed).toEpochFrame.toFrame.balancesMatch
    rw [processRewardsAndPenalties_frame edge] at matched ⊢
    exact shaped.of_kept rfl matched id id rfl
  case registry =>
    have sizes := sameSizes_processRegistryUpdates edge
    obtain ⟨-, consolidations⟩ := processRegistryUpdates_kept edge
    obtain ⟨-, previous, current, scores, -⟩ := processRegistryUpdates_fields edge
    have balances := processRegistryUpdates_balances edge
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold BalancesMatch
      rw [balances, sizes.1]
      exact shaped.balancesMatch
    · intro altair
      rw [previous, current, sizes.1]
      exact shaped.participationMatches altair
    · intro altair
      rw [scores, sizes.1]
      exact shaped.inactivityScoresMatch altair
    · intro electra
      rw [consolidations, sizes.1]
      exact shaped.inside electra
  case slashings =>
    have matched := (mutatorEpochFrameLaws.toEpochStepLaws.epochEdge (stage := .slashings)
      ⟨nofun, nofun, nofun, nofun⟩ computed).toEpochFrame.toFrame.balancesMatch
    rw [processSlashings_frame edge] at matched ⊢
    exact shaped.of_kept rfl matched id id rfl
  case eth1Reset =>
    split at edge
    · rw [processEth1DataReset_frame edge]
      exact shaped.of_eq
    · subst edge
      exact shaped
  case pendingDeposits =>
    split at edge
    · have frame := frame_processPendingDeposits edge
      have flags := processPendingDeposits_matches edge shaped.participationMatches
        shaped.inactivityScoresMatch
      refine ⟨balancesMatch_processPendingDeposits edge shaped.balancesMatch, flags.1, flags.2, ?_⟩
      intro electra consolidation member
      rw [processPendingDeposits_pendingConsolidations edge] at member
      have held := shaped.inside electra consolidation member
      exact ⟨Nat.lt_of_lt_of_le held.1 frame.registryGrows,
        Nat.lt_of_lt_of_le held.2 frame.registryGrows⟩
    · subst edge
      exact shaped
  case pendingConsolidations =>
    split at edge
    · have matched := (mutatorEpochFrameLaws.toEpochStepLaws.epochEdge
        (stage := .pendingConsolidations) ⟨nofun, nofun, nofun, nofun⟩
          computed).toEpochFrame.toFrame.balancesMatch
          shaped.balancesMatch
      obtain ⟨validators, previous, current, scores, -⟩ := processPendingConsolidations_fields edge
      obtain ⟨_, -, -, queue⟩ := processPendingConsolidations_pass edge
      refine ⟨matched, ?_, ?_, ?_⟩
      · intro altair
        rw [previous, current, validators]
        exact shaped.participationMatches altair
      · intro altair
        rw [scores, validators]
        exact shaped.inactivityScoresMatch altair
      · intro electra' consolidation member
        rw [validators]
        have listed : consolidation ∈ (t.pendingConsolidations electra').data.toList :=
          Array.mem_toList_iff.mpr member
        rw [queue] at listed
        exact shaped.inside electra' consolidation
          (Array.mem_toList_iff.mp (List.mem_of_mem_drop listed))
    · subst edge
      exact shaped
  case payments =>
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
      exact shaped.of_eq
    · subst edge
      exact shaped
  case effectiveBalances =>
    have sizes := sameSizes_processEffectiveBalanceUpdates edge
    have frame := processEffectiveBalanceUpdates_frame edge
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold BalancesMatch
      rw [sizes.1, sizes.2]
      exact shaped.balancesMatch
    · intro altair
      rw [frame, sizes.1]
      exact shaped.participationMatches altair
    · intro altair
      rw [frame, sizes.1]
      exact shaped.inactivityScoresMatch altair
    · intro electra
      rw [frame, sizes.1]
      exact shaped.inside electra
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    exact shaped.of_eq
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    exact shaped.of_eq
  case history =>
    split at edge
    · unfold processHistoricalSummariesUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact shaped.of_eq
    · unfold processHistoricalRootsUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact shaped.of_eq
  case participation =>
    split at edge
    · rename_i altair
      subst edge
      refine ⟨shaped.balancesMatch, fun _ => ⟨?_, ?_⟩, shaped.inactivityScoresMatch,
        shaped.inside⟩
      · exact (shaped.participationMatches altair).2
      · simp [processParticipationFlagUpdates]
    · rename_i early
      obtain ⟨u, computed, _, _, restored⟩ :=
        processParticipationRecordUpdates_eq (state := s) (Nat.lt_of_not_le early)
      obtain rfl := Except.ok.inj (computed.symm.trans edge)
      exact shaped.of_kept (congrArg (·.validators) restored)
        (fun _ => by unfold BalancesMatch; rw [← restored] at shaped; exact shaped.balancesMatch)
        (fun _ altair => absurd altair early) (fun _ altair => absurd altair early)
        (congrArg (·.pendingConsolidations) restored)
  case syncCommittees =>
    split at edge
    · unfold processSyncCommitteeUpdates at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact shaped.of_eq
    · subst edge
      exact shaped
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact shaped.of_eq
    · subst edge
      exact shaped
  case ptcWindow =>
    split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact shaped.of_eq
    · subst edge
      exact shaped

/-- One epoch keeps the facts of the shape other than the caps. -/
private theorem processEpoch_sized (computed : processEpoch config checks state = .ok after)
    (sized : Sized state) : Sized after :=
  (processEpoch_trace computed).transport (fun s t => Sized s → Sized t) (fun _ => id)
    (fun one two held => two (one held)) (fun _ _ _ _ ok held => held.of_action ok) sized

/-- One epoch keeps the shape of the state. -/
theorem processEpoch_shaped (computed : processEpoch config checks state = .ok after)
    (shaped : Shaped state) : Shaped after :=
  (processEpoch_sized computed shaped.sized).shaped (processEpoch_capped computed shaped.capped)

/-- One slot keeps the shape of the state. -/
theorem advanceSlot_shaped (computed : advanceSlot config checks state = .ok after)
    (shaped : Shaped state) : Shaped after := by
  have capped := advanceSlot_capped computed shaped.capped
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have epochedSized : Sized epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch_sized epochedOk shaped.sized.of_eq
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact shaped.sized.of_eq
  exact epochedSized.of_eq.shaped capped

/-- A run of slots within one fork keeps the shape of the state. -/
theorem advanceSlots_shaped {count : Nat}
    (computed : advanceSlots config checks count state = .ok after)
    (shaped : Shaped state) : Shaped after := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ shaped
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact ih rest (advanceSlot_shaped nextOk shaped)

/-- An upgrade from a fork at or after Altair keeps the shape.

It must carry the registry, the flags and the scores.

Each queued consolidation after it must be one queued before it. -/
private theorem Shaped.of_carried {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (shaped : Shaped s) (capped : EffectiveBalancesCapped t)
    (matched : BalancesMatch t) (altair : .altair ≤ f) (forward : f ≤ h)
    (validators : t.validators.data.size = s.validators.data.size)
    (previous : (t.previousEpochParticipation (Nat.le_trans altair forward)).data =
      (s.previousEpochParticipation altair).data)
    (current : (t.currentEpochParticipation (Nat.le_trans altair forward)).data =
      (s.currentEpochParticipation altair).data)
    (scores : (t.inactivityScores (Nat.le_trans altair forward)).data =
      (s.inactivityScores altair).data)
    (consolidations : ∀ (electra : .pectra ≤ h), ∀ c ∈ (t.pendingConsolidations electra).data,
      ∃ early : .pectra ≤ f, c ∈ (s.pendingConsolidations early).data) : Shaped t := by
  refine ⟨matched, fun _ => ⟨?_, ?_⟩, fun _ => ?_, capped, fun electra c member => ?_⟩
  · rw [validators, ← (shaped.participationMatches altair).1]
    exact congrArg Array.size previous
  · rw [validators, ← (shaped.participationMatches altair).2]
    exact congrArg Array.size current
  · rw [validators, ← shaped.inactivityScoresMatch altair]
    exact congrArg Array.size scores
  · obtain ⟨early, found⟩ := consolidations electra c member
    rw [validators]
    exact shaped.inside early c found

/-- A step of the upgrade to Electra keeps the size of the registry and four lists.

These are both lists of flags, the scores and the queue of consolidations. -/
private def QueueKept (s t : BeaconState preset fork) : Prop :=
  t.validators.data.size = s.validators.data.size ∧
    t.previousEpochParticipation = s.previousEpochParticipation ∧
    t.currentEpochParticipation = s.currentEpochParticipation ∧
    t.inactivityScores = s.inactivityScores ∧ t.pendingConsolidations = s.pendingConsolidations

private theorem QueueKept.trans {s t u : BeaconState preset fork} (one : QueueKept s t)
    (two : QueueKept t u) : QueueKept s u :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.trans one.2.2.2.2⟩

private theorem QueueKept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x t, step s x = .ok t → QueueKept s t) {items : List α}
    {s t : BeaconState preset fork} (computed : items.foldlM step s = .ok t) : QueueKept s t :=
  foldlM_ok_invariant (QueueKept s) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    ⟨rfl, rfl, rfl, rfl, rfl⟩ computed

private theorem QueueKept.queuePreActivation {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation s electra index = .ok t) : QueueKept s t := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨_, rfl⟩ := setValidator_ok set₂
  exact ⟨(sameSizes_putValidator _ _ _).1, rfl, rfl, rfl, rfl⟩

private theorem QueueKept.queueCompoundingExcess {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess s electra index = .ok t) : QueueKept s t := by
  unfold Consensus.queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok set
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · cases queued
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · cases computed
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases computed
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The upgrade to the next fork keeps the shape of the state.

The caps of the preset are assumed in order.

The largest balance before Electra must be at most the least one from Electra.

That one must be at most the largest one for compounding credentials. -/
theorem upgradeNext_shaped {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (computed : upgradeNext config checks pre = .ok post) (shaped : Shaped pre.state) :
    Shaped post.val.state := by
  have capped := upgradeNext_capped activation compounding computed shaped.capped
  have matched := (upgradeFrame_upgradeNext computed).balancesMatch shaped.balancesMatch
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    dsimp only at shaped capped matched ⊢
    obtain ⟨validators, -, previous, current, scores, -⟩ := upgradeToAltair_spec upgraded
    refine ⟨matched, fun _ => ⟨?_, ?_⟩, fun _ => ?_, capped, fun electra => absurd electra ?_⟩
    · rw [validators]; exact previous
    · rw [validators]; exact current
    · rw [validators]; exact scores
    · decide
  case altair | bellatrix | shapella =>
    subst computed
    dsimp only at shaped capped matched ⊢
    refine shaped.of_carried capped matched (by decide) (by decide) ?_ ?_ ?_ ?_
      (fun electra => absurd electra (by decide)) <;>
      simp [carryFields, carryList, carryRooted] <;> rw [dite_eq_left (by decide)]
  · obtain ⟨_, upgraded, rfl⟩ := computed
    dsimp only at shaped capped matched ⊢
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    obtain ⟨size, previous, current, scores, consolidations⟩ :=
      (QueueKept.foldlM (fun _ _ _ ok => QueueKept.queuePreActivation ok) queued).trans
        (QueueKept.foldlM (fun _ _ _ ok => QueueKept.queueCompoundingExcess ok) compounded)
    clear queued compounded
    refine shaped.of_carried capped matched (by decide) (by decide) ?_ ?_ ?_ ?_ ?_
    · rw [size]; simp [carryFields, carryRooted]
    · rw [previous]; simp [carryFields, carryList]; rw [dite_eq_left (by decide)]
    · rw [current]; simp [carryFields, carryList]; rw [dite_eq_left (by decide)]
    · rw [scores]; simp [carryFields, carryList]; rw [dite_eq_left (by decide)]
    · intro electra c member
      rw [consolidations] at member
      have early : ¬Fork.pectra ≤ Fork.dencun := by decide
      simp [carryFields, early] at member
  · obtain ⟨_, upgraded, rfl⟩ := computed
    dsimp only at shaped capped matched ⊢
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    have altair : Fork.altair ≤ Fork.pectra := by decide
    have electra : Fork.pectra ≤ Fork.pectra := by decide
    refine shaped.of_carried capped matched altair (by decide) ?_ ?_ ?_ ?_
      (fun _ c member => ⟨electra, ?_⟩) <;> clear capped matched
    · simp [carryFields, carryRooted]
    · simp [carryFields, carryList, altair]
    · simp [carryFields, carryList, altair]
    · simp [carryFields, carryList, altair]
    · simpa [carryFields, carryList, electra] using member
  · obtain ⟨_, upgraded, rfl⟩ := computed
    dsimp only at shaped capped matched ⊢
    unfold upgradeToGloas at upgraded
    obtain ⟨root, -, rest⟩ := bind_ok_iff.mp upgraded
    obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨builders, pending, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    obtain ⟨validators, -, -, -, consolidations, -⟩ :=
      upgradeFields_lists (config := config) state root
    exact shaped.of_carried capped matched (by decide) (by decide)
      (congrArg Array.size validators) rfl rfl rfl
      (fun _ c member => ⟨by decide, consolidations ▸ member⟩)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    dsimp only at shaped capped matched ⊢
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact shaped.of_carried capped matched (by decide) (by decide) rfl rfl rfl rfl
      (fun _ c member => ⟨by decide, member⟩)

/-- The upgrades due at a slot keep the shape of the state, under the same conditions. -/
theorem processUpgrades_shaped {forked upgraded : ForkedBeaconState preset}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (computed : processUpgrades config checks forked = .ok upgraded)
    (shaped : Shaped forked.state) : Shaped upgraded.state :=
  processUpgrades_induction (property := fun forked => Shaped forked.state)
    (fun held ok => upgradeNext_shaped activation compounding ok held) shaped computed

end EthLib.Consensus
