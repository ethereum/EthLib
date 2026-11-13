module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised

/-!
# Funding across an epoch

From Electra, the epoch passes conserve the funded stake and the deposit balance to consume.

The exceptions are one epoch of activation and exit churn and the credits recorded by the replay.

The epoch is cut on the shared schedule: the replay covers the stages before the payments.

Before Gloas the payments are the identity.

The stages after the effective-balance update keep the funding.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem funding_kept_prefix {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (credit : Nat)
    (size : t.validators.data.size = s.validators.data.size)
    (life : RegistryLifecycle s t) (slot : t.slot = s.slot)
    (queue : t.pendingConsolidations = s.pendingConsolidations)
    (effective : ∀ i, i < s.validators.data.size →
      effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i)
    (balances : (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤ credit) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + credit := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  have bound := funding_potential_change
    (s.pendingConsolidations electra).data.toList
    (s.pendingConsolidations electra).data.toList
    (fun i => actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)
    size life (by rw [epoch]) (fun _ h => Or.inl h) (fun i => ?_)
  · rw [← queue, funding_potential_eq t electra] at bound
    rw [queue, funding_potential_eq s electra] at bound
    omega
  · by_cases inside : i < s.validators.data.size
    · rw [effective i inside]; omega
    · have outside : s.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
      have outsideT : t.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
      simp only [effectiveAt, outside, outsideT, Option.map_none, Option.getD_none,
        Nat.zero_max]
      omega

private def FundingOrdinary (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source ≠ .deposits ∧ e.source ≠ .consolidations

private theorem funding_ordinary_record {fork : Fork} {pre post : BalanceReplay preset fork}
    {source : BalanceSource} {limits action}
    (initial : FundingOrdinary pre.2) (ordinary : source ≠ .deposits ∧ source ≠ .consolidations)
    (ok : recordBalance source limits action pre = .ok post) : FundingOrdinary post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, _, _, rfl⟩ := ok
  intro e member
  rcases List.mem_append.mp member with old | new
  · exact initial e old
  · obtain rfl := List.mem_singleton.mp new
    exact ordinary

private theorem funding_ordinary_deltas {fork : Fork} (source : BalanceSource)
    (ordinary : source ≠ .deposits ∧ source ≠ .consolidations) (deltas : Array Gwei × Array Gwei)
    {pre post : BalanceReplay preset fork} (initial : FundingOrdinary pre.2)
    (ok : replayDeltas source deltas pre = .ok post) : FundingOrdinary post.2 := by
  apply foldlM_ok_invariant (fun p => FundingOrdinary p.2) _ initial ok
  intro pre i post initial ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, rewarded, rewardOk, penaltyOk⟩ := ok
  exact funding_ordinary_record
    (funding_ordinary_record initial (by decide) rewardOk) ordinary penaltyOk

private theorem funding_ordinary_rewards {fork : Fork} {pre post : BalanceReplay preset fork}
    (initial : FundingOrdinary pre.2)
    (ok : replayRewards (config := config) pre = .ok post) : FundingOrdinary post.2 := by
  unfold replayRewards at ok
  split at ok
  · cases ok; exact initial
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, folded, last⟩ := bind_ok_iff.mp ok
      exact funding_ordinary_deltas _ (by decide) _
        (foldlM_ok_invariant (fun p => FundingOrdinary p.2)
          (fun _ _ _ h ok => funding_ordinary_deltas _ (by decide) _ h ok) initial folded) last
    · simp only [bind_ok_iff] at ok
      obtain ⟨rewards, _, rewarded, rewardOk, middle, folded, last⟩ := ok
      exact funding_ordinary_deltas _ (by decide) _
        (foldlM_ok_invariant (fun p => FundingOrdinary p.2)
          (fun _ _ _ h ok => funding_ordinary_deltas _ (by decide) _ h ok)
          (funding_ordinary_deltas _ (by decide) _ initial rewardOk) folded) last

private theorem funding_rewards {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processRewardsAndPenalties config s = .ok t)
    {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (s, []) = .ok (t, events)) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + (events.map fundingCredit).sum := by
  have coverage := coverage_rewards (coverage_refl ⟨fork, s⟩) replayed
  have bounded := replayRewards_bounded (by simp [EventsBounded]) replayed
  have ordinary := funding_ordinary_rewards (by simp [FundingOrdinary]) replayed
  have balanceBound : (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤
      (events.map fundingCredit).sum := by
    calc
      _ ≤ ∑ i ∈ Finset.range s.validators.data.size,
          (events.map fun e => coverageDelta false e.before e.after i).sum :=
        Finset.sum_le_sum (fun i _ => coverage false i)
      _ ≤ (events.map fun e => e.credits).sum :=
        coverage_sum_events events _ false
      _ ≤ (events.map fundingCredit).sum := by
        have pointwise : ∀ e ∈ events, e.credits ≤ fundingCredit e := by
          intro e member
          have bound := (bounded e member).1
          have ord := ordinary e member
          cases source : e.source <;> simp_all [fundingCredit]
        clear coverage bounded ordinary replayed
        induction events with
        | nil => simp
        | cons e rest ih =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add (pointwise e (by simp))
            (ih (fun e h => pointwise e (by simp [h])))
  have registry : t.validators = s.validators := by
    rw [processRewardsAndPenalties_frame ok]
  exact funding_kept_prefix electra _ (congrArg (·.data.size) registry)
    (.of_data (congrArg (·.data) registry)) (frame_processRewardsAndPenalties ok).slot
    (by rw [processRewardsAndPenalties_frame ok])
    (fun i _ => by simp only [effectiveAt, registry]) balanceBound

private theorem funding_same {fork : Fork} {s t : BeaconState preset fork}
    (registry : t.validators = s.validators) (balances : t.balances = s.balances)
    (slot : t.slot = s.slot) (queue : t.pendingConsolidations = s.pendingConsolidations) :
    fundedStake ⟨fork, t⟩ = fundedStake ⟨fork, s⟩ := by
  simp only [fundedStake, effectiveAt, actualBalanceAt, registry, balances,
    getCurrentEpoch, slot, queue]
  rfl

private theorem funding_registry {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processRegistryUpdates config s = .ok t)
    (queue : t.pendingConsolidations = s.pendingConsolidations) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  have bound := funding_kept_prefix electra 0 (sameSizes_processRegistryUpdates ok).1
    (registryLifecycle_processRegistryUpdates ok) (frame_processRegistryUpdates ok).slot
    queue (effectiveKept_registry ok)
    (by simp only [actualBalanceAt, processRegistryUpdates_balances ok, Nat.sub_self, Finset.sum_const_zero]
        exact Nat.le_refl _)
  simpa using bound

private theorem funding_slashings {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processSlashings s = .ok t) : fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  obtain ⟨_, _, credits, _⟩ := delayed_slashing_bounds s t (s.validators.bound early) ok
  have registry := processSlashings_validators ok
  have bound := funding_kept_prefix electra 0 (sameSizes_processSlashings ok).1
    (.of_data (congrArg (·.data) registry)) (frame_processSlashings ok).slot
    (by obtain ⟨_, same⟩ := processSlashings_eq ok; rw [same])
    (fun i _ => by simp only [effectiveAt, registry]) ?_
  · simpa using bound
  · have covered := coverage_event_sum
      (⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ : BalanceEvent preset)
      s.validators.data.size false
    change (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤ balanceCredits s t at covered
    omega

/-- A stage that keeps the validators, the balances, the slot and the queue keeps the funding. -/
private theorem funding_stage {fork : Fork} {k : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks k s t)
    (other : k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
      k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances) :
    fundedStake ⟨fork, t⟩ = fundedStake ⟨fork, s⟩ :=
  have kept := edge.records other
  funding_same kept.1 kept.2.1 kept.2.2.2.2 kept.2.2.1

/-- The stages before the payments, from Electra.

The replay events are the rewards, the slashings, the pending deposits and the consolidations.

The stages before pending deposits change the funding by at most the credits they record.

The pending deposits and consolidations then change it by at most the churn. -/
private theorem funding_before {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s) (pending : PendingConsolidationInvariant config s)
    (ok : epochBeforePayments config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events)) :
    fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ ≤
      fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, altair, before,
    rewardEvents, limit, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
    depositedOk, consolidatedOk, resetMatch, rewardReplay, equal⟩ :=
    funding_epoch_site electra early ok replayed matched
  have justifiedEdge : EpochStage.Edge config checks .justification s justified := justifiedOk
  have scoredEdge : EpochStage.Edge config checks .inactivity justified scored := by
    simp only [EpochStage.Edge, altair, ↓reduceDIte]; exact scoredOk
  have rewardedEdge : EpochStage.Edge config checks .rewards scored rewarded := rewardedOk
  have registeredEdge : EpochStage.Edge config checks .registry rewarded registered :=
    registeredOk
  have slashedEdge : EpochStage.Edge config checks .slashings registered slashed := slashedOk
  have resetEdge : EpochStage.Edge config checks .eth1Reset slashed reset := by
    simp only [EpochStage.Edge, before, ↓reduceDIte]; exact resetOk
  -- Justification, inactivity and the eth1 reset keep the funding, as epoch stages.
  have justifiedFunding := funding_stage justifiedEdge ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have scoredFunding := funding_stage scoredEdge ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have rewardFunding := funding_rewards electra rewardedOk rewardReplay
  have registryFunding :=
    funding_registry electra registeredOk (registeredEdge.samePendingQueue nofun)
  have slashFunding := funding_slashings electra early slashedOk
  have resetFunding := funding_stage resetEdge ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have resetOrder : ExitsOrdered reset :=
    (frame_processEth1DataReset resetOk).exitsOrdered <|
    (frame_processSlashings slashedOk).exitsOrdered <|
    (frame_processRegistryUpdates registeredOk).exitsOrdered <|
    (frame_processRewardsAndPenalties rewardedOk).exitsOrdered <|
    (frame_processInactivityUpdates scoredOk).exitsOrdered <|
    (by simpa only [ExitsOrdered, (processJustificationAndFinalization_keeps
      justifiedOk).2.2.2.2.2.1] using ordered)
  have resetActivation := resetEdge.activationExitOrder <| slashedEdge.activationExitOrder <|
    registeredEdge.activationExitOrder <| rewardedEdge.activationExitOrder <|
    scoredEdge.activationExitOrder <| justifiedEdge.activationExitOrder activation
  have resetPending := resetEdge.pendingConsolidationInvariant <|
    slashedEdge.pendingConsolidationInvariant <| registeredEdge.pendingConsolidationInvariant <|
    rewardedEdge.pendingConsolidationInvariant <| scoredEdge.pendingConsolidationInvariant <|
    justifiedEdge.pendingConsolidationInvariant pending
  have pendingOk : processPendingBalances config checks reset = .ok t := by
    simp only [processPendingBalances, electra, ↓reduceDIte, bind_ok_iff]
    exact ⟨deposited, depositedOk, consolidatedOk⟩
  obtain ⟨deposited', depositedOk', _, pendingFunding⟩ :=
    funding_pending_balances electra early delay resetMatch resetOrder resetActivation
      resetPending pendingOk
  rw [Except.ok.inj (depositedOk'.symm.trans depositedOk)] at pendingFunding
  have carry : reset.depositBalanceToConsume = s.depositBalanceToConsume := by
    exact depositCarry_beforePending justifiedOk scoredOk rewardedOk registeredOk slashedOk
      resetOk
  rw [equal, List.map_append, List.map_append, List.map_append,
    List.sum_append, List.sum_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fundingCredit,
    Nat.add_zero, funding_carry, electra, ↓reduceDIte]
  have withdrawn : withdrawnConsolidationCredit
      ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, consumedDeposits reset deposited electra, 0⟩ =
      withdrawnConsolidationCredit ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, 0, 0⟩ := rfl
  rw [withdrawn]
  rw [carry] at pendingFunding
  omega

/-- The stages after the effective-balance update keep the funding and the deposit carry. -/
private theorem funding_late {fork : Fork} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks)
      [.slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow] s t) :
    fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ =
      fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ := by
  let Same (a b : BeaconState preset fork) : Prop :=
    fundedStake ⟨fork, b⟩ = fundedStake ⟨fork, a⟩ ∧
      b.depositBalanceToConsume = a.depositBalanceToConsume
  have same : Same s t := by
    refine trace.transport Same (fun _ => ⟨rfl, rfl⟩)
      (fun one two => ⟨two.1.trans one.1, two.2.trans one.2⟩) ?_
    intro k member a b computed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    -- Each late stage keeps the fields that the funding and the deposit carry read.
    have kept := (EpochStage.action_cases.mp computed).records
      (by rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩)
    exact ⟨funding_same kept.1 kept.2.1 kept.2.2.2.2 kept.2.2.1, kept.2.2.2.1⟩
  simp only [funding_carry, same.1, same.2]

/-- The epoch passes conserve funding apart from churn and the recorded external credits.

The epoch is cut after the stages before the payments, whose replay is unique.

Before Gloas the payments are the identity. -/
theorem funding_epoch {fork : Fork} {s t middle : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s)
    (pending : PendingConsolidationInvariant config s)
    (ok : processEpoch config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events)) :
    fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ ≤
      fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have trace := processEpoch_trace ok
  change EpochTrace _ ((EpochStage.prefixStages ++ [.payments, .effectiveBalances]) ++
    [.slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
      .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨updated, head, tail⟩ := EpochTrace.append_iff.mp trace
  obtain ⟨before, prefixTrace, rest⟩ := EpochTrace.append_iff.mp head
  cases rest
  rename_i paid paidOk rest
  cases rest
  rename_i updatedOk rest
  cases rest
  have paidEdge := EpochStage.action_cases.mp paidOk
  simp only [EpochStage.Edge, gloas, ↓reduceDIte] at paidEdge
  subst paidEdge
  have updatedEdge := EpochStage.action_cases.mp updatedOk
  have beforeOk : epochBeforePayments config checks s = .ok before :=
    (epochBeforePayments_eq_run config checks s).trans (EpochTrace.run_ok_iff.mpr prefixTrace)
  -- The replay of the stages before the payments is unique, so it ends at `before`.
  obtain ⟨recorded, recordedOk⟩ := epochBalanceReplay_before beforeOk
  obtain rfl := (Prod.mk.inj (Except.ok.inj (recordedOk.symm.trans replayed))).1
  have bound := funding_before electra early delay matched ordered activation pending
    beforeOk events replayed
  have late := funding_late tail
  have queue := updatedEdge.samePendingQueue nofun
  have effective := funding_effective_updates
    (before.pendingConsolidations electra).data.toList updatedEdge
  rw [← queue, funding_potential_eq updated electra] at effective
  rw [queue, funding_potential_eq before electra] at effective
  have carry := updatedEdge.depositCarry nofun
  simp only [funding_carry, electra, ↓reduceDIte, carry] at late bound ⊢
  omega

end

end EthLib.Consensus.DirectSafety
