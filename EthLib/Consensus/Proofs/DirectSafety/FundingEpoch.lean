module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Funding across an epoch

Before Gloas, the epoch passes conserve the funded stake and the deposit balance to consume.

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
    (credit : Nat)
    (size : t.validators.data.size = s.validators.data.size)
    (life : RegistryLifecycle s t) (slot : t.slot = s.slot)
    (queue : t.pendingConsolidations = s.pendingConsolidations)
    (effective : ∀ i, i < s.validators.data.size →
      effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i)
    (balances : (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤ credit) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + credit := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  have sources : fundingSources t = fundingSources s := by
    unfold fundingSources
    rw [queue]
  have bound := fundingPotential_change (fundingSources t) (fundingSources s)
    (fun i => actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)
    size life (by rw [epoch]) (fun _ h => Or.inl (sources ▸ h)) (fun i => ?_)
  · rw [fundingPotential_eq, fundingPotential_eq] at bound
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

private theorem funding_ordinary_rewards {fork : Fork} {pre post : BalanceReplay preset fork}
    (initial : FundingOrdinary pre.2)
    (ok : replayRewards (config := config) pre = .ok post) : FundingOrdinary post.2 :=
  replayRewards_induction (fun pre => FundingOrdinary pre.2)
    (fun prior ok => funding_ordinary_record prior (by decide) ok)
    (fun penalty prior ok => funding_ordinary_record prior
      (by rcases penalty with rfl | rfl <;> decide) ok) initial ok

/-- The recorded reward credits bound the sum of positive balance changes. -/
theorem funding_rewards_balance {fork : Fork} {s t : BeaconState preset fork}
    {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (s, []) = .ok (t, events)) :
    (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤
      (events.map fundingCredit).sum := by
  have coverage := coverage_rewards (pre := (s, [])) (coverage_refl ⟨fork, s⟩) replayed
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
  exact balanceBound

private theorem funding_rewards {fork : Fork} {s t : BeaconState preset fork}
    (ok : processRewardsAndPenalties config s = .ok t)
    {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (s, []) = .ok (t, events)) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + (events.map fundingCredit).sum := by
  have registry : t.validators = s.validators := by
    rw [processRewardsAndPenalties_frame ok]
  exact funding_kept_prefix _ (congrArg (·.data.size) registry)
    (.of_data (congrArg (·.data) registry)) (frame_processRewardsAndPenalties ok).slot
    (by rw [processRewardsAndPenalties_frame ok])
    (fun i _ => by simp only [effectiveAt, registry]) (funding_rewards_balance replayed)

private theorem funding_same {fork : Fork} {s t : BeaconState preset fork}
    (registry : t.validators = s.validators) (balances : t.balances = s.balances)
    (slot : t.slot = s.slot) (queue : t.pendingConsolidations = s.pendingConsolidations) :
    fundedStake ⟨fork, t⟩ = fundedStake ⟨fork, s⟩ := by
  simp only [fundedStake, effectiveAt, actualBalanceAt, registry, balances,
    getCurrentEpoch, slot, queue]
  rfl

private theorem funding_registry {fork : Fork} {s t : BeaconState preset fork}
    (ok : processRegistryUpdates config s = .ok t) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  have bound := funding_kept_prefix 0 (sameSizes_processRegistryUpdates ok).1
    (registryLifecycle_processRegistryUpdates ok) (frame_processRegistryUpdates ok).slot
    (processRegistryUpdates_kept ok).2 (effectiveKept_registry ok)
    (by simp only [actualBalanceAt, processRegistryUpdates_balances ok, Nat.sub_self,
          Finset.sum_const_zero]
        exact Nat.le_refl _)
  simpa using bound

private theorem funding_slashings {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam)
    (ok : processSlashings s = .ok t) : fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  obtain ⟨_, _, credits, _⟩ := delayed_slashing_bounds s t (s.validators.bound early) ok
  have registry : t.validators = s.validators := by rw [processSlashings_frame ok]
  have bound := funding_kept_prefix 0 (sameSizes_processSlashings ok).1
    (.of_data (congrArg (·.data) registry)) (frame_processSlashings ok).slot
    (by rw [processSlashings_frame ok])
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

/-- The stages before the payments, before Gloas.

The replay events are the rewards and the slashings.

From Electra they also include the pending deposits and the consolidations.

The stages before pending deposits change the funding by at most the credits they record.

From Electra the pending deposits and consolidations then change it by at most the churn. -/
theorem funding_before_of {fork : Fork} {s t : BeaconState preset fork}
    (potential : BeaconState preset fork → Nat)
    (ordinary : ∀ {k a b}, EpochStage.Edge config checks k a b →
      k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
        k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances → potential b = potential a)
    (rewards : ∀ {a b events}, processRewardsAndPenalties config a = .ok b →
      replayRewards (config := config) (a, []) = .ok (b, events) →
      potential b ≤ potential a + (events.map fundingCredit).sum)
    (registry : ∀ {a b}, a.slot = s.slot → processRegistryUpdates config a = .ok b →
      potential b ≤ potential a)
    (slashings : ∀ {a b}, processSlashings a = .ok b → potential b ≤ potential a)
    (pendingBound : ∀ {a b} (electra : .pectra ≤ fork), a.slot = s.slot →
      s.validators.data.size ≤ a.validators.data.size → BalancesMatch a → ExitsOrdered a →
      ActivationExitOrder a → PendingConsolidationInvariant config a →
      processPendingBalances config checks a = .ok b →
      ∃ deposited, processPendingDeposits config checks a electra = .ok deposited ∧
        processPendingConsolidations deposited electra = .ok b ∧
        potential b + (b.depositBalanceToConsume electra).toNat ≤
          potential a + (a.depositBalanceToConsume electra).toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
            withdrawnConsolidationCredit ⟨.deposits, ⟨fork, a⟩, ⟨fork, deposited⟩, 0, 0⟩)
    (early : fork < .glamsterdam)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s) (pending : PendingConsolidationInvariant config s)
    (ok : epochBeforePayments config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events)) :
    potential t + fundingCarry ⟨fork, t⟩ ≤
      potential s + fundingCarry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  obtain ⟨reset, deposited, ⟨⟨justified, scored, rewarded, registered, slashed, justifiedOk,
    scoredOk, rewardedOk, registeredOk, slashedOk, resetOk⟩, rewardEvents, limit, rewardReplay, _⟩,
    depositedOk, consolidatedOk, equal⟩ := funding_epoch_site ok replayed
  have stages : EpochPrefix config checks s reset :=
    ⟨_, _, _, _, _, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk⟩
  have trace := stages.trace
  -- Justification, inactivity and the eth1 reset keep the funding, as epoch stages.
  have justifiedFunding := ordinary justifiedOk ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have scoredFunding := ordinary scoredOk ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have rewardFunding := rewards rewardedOk rewardReplay
  have scoredSlot : scored.slot = s.slot :=
    (scoredOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2.trans
      (justifiedOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2
  have registryFunding := registry ((frame_processRewardsAndPenalties rewardedOk).slot.trans
    scoredSlot) registeredOk
  have slashFunding := slashings slashedOk
  have resetFunding := ordinary resetOk ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  rw [equal]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, fundingCredit, Nat.add_zero]
  by_cases electra : .pectra ≤ fork
  · have kept {P : BeaconState preset fork → Prop}
        (step : ∀ {k : EpochStage} {a b : BeaconState preset fork},
          EpochStage.Edge config checks k a b → P a → P b) (start : P s) : P reset :=
      trace.transport (fun a b => P a → P b) (fun _ => id) (fun one two => two ∘ one)
        (fun _ _ _ _ computed => step (EpochStage.action_cases.mp computed)) start
    have resetActivation := kept (fun edge => edge.activationExitOrder) activation
    have resetPending := kept (fun edge => edge.pendingConsolidationInvariant) pending
    -- After justification, the stages up to the eth1 reset are mutator frames.
    obtain ⟨carry, frame, resetMatch⟩ := funding_epoch_prefix electra early
      ⟨_, _, _, _, _, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk⟩ matched
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at depositedOk consolidatedOk
    have resetOrder : ExitsOrdered reset := frame.exitsOrdered <| by
      simpa only [ExitsOrdered, (processJustificationAndFinalization_keeps
        justifiedOk).2.2.2.2.2.1] using ordered
    have pendingOk : processPendingBalances config checks reset = .ok t := by
      simp only [processPendingBalances, electra, ↓reduceDIte, bind_ok_iff]
      exact ⟨deposited, depositedOk, consolidatedOk⟩
    have justifiedSize : s.validators.data.size ≤ justified.validators.data.size := by
      rw [(sameSizes_processJustificationAndFinalization justifiedOk).1]
    have resetSlot : reset.slot = s.slot := frame.slot.trans
      (justifiedOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2
    obtain ⟨deposited', depositedOk', _, pendingFunding⟩ := pendingBound electra resetSlot
      (justifiedSize.trans frame.registryGrows) resetMatch resetOrder resetActivation
      resetPending pendingOk
    rw [Except.ok.inj (depositedOk'.symm.trans depositedOk), carry] at pendingFunding
    simp only [electra, ↓reduceDIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fundingCredit, fundingCarry, ↓reduceIte, Nat.add_zero]
    have withdrawn : withdrawnConsolidationCredit
        ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, consumedDeposits reset deposited electra,
          0⟩ =
        withdrawnConsolidationCredit ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, 0, 0⟩ := rfl
    rw [withdrawn]
    omega
  · -- Before Electra the pending stages are absent and nothing is carried.
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at depositedOk consolidatedOk
    subst depositedOk consolidatedOk
    simp only [electra, ↓reduceDIte, List.map_nil, List.sum_nil, fundingCarry]
    omega

private theorem funding_before {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s) (pending : PendingConsolidationInvariant config s)
    (ok : epochBeforePayments config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events)) :
    fundedStake ⟨fork, t⟩ + fundingCarry ⟨fork, t⟩ ≤
      fundedStake ⟨fork, s⟩ + fundingCarry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum :=
  funding_before_of (fun a => fundedStake ⟨fork, a⟩) funding_stage
    (fun ok replayed => funding_rewards ok replayed)
    (fun _ ok => funding_registry ok) (fun ok => funding_slashings early ok)
    (fun electra _ _ matched ordered activation pending ok =>
      funding_pending_balances electra early delay matched ordered activation pending ok)
    early matched ordered activation pending ok events replayed

/-- The stages after the effective-balance update keep the funding and the deposit carry. -/
private theorem funding_late_of {fork : Fork} {s t : BeaconState preset fork}
    (potential : BeaconState preset fork → Nat)
    (ordinary : ∀ {k a b}, EpochStage.Edge config checks k a b →
      k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
        k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances → potential b = potential a)
    (trace : EpochTrace (EpochStage.action config checks)
      [.slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow] s t) :
    potential t + fundingCarry ⟨fork, t⟩ =
      potential s + fundingCarry ⟨fork, s⟩ := by
  let Same (a b : BeaconState preset fork) : Prop :=
    potential b = potential a ∧
      b.depositBalanceToConsume = a.depositBalanceToConsume
  have same : Same s t := by
    refine trace.transport Same (fun _ => ⟨rfl, rfl⟩)
      (fun one two => ⟨two.1.trans one.1, two.2.trans one.2⟩) ?_
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    have other : k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
        k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances := by
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    exact ⟨ordinary edge other, (edge.records other).2.2.2.1⟩
  simp only [fundingCarry, same.1, same.2]

/-- Stage bounds on a potential give an epoch bound including carry and recorded credits. -/
theorem funding_epoch_of {fork : Fork} {s t middle : BeaconState preset fork}
    (potential : BeaconState preset fork → Nat)
    (ordinary : ∀ {k a b}, EpochStage.Edge config checks k a b →
      k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
        k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances → potential b = potential a)
    (beforeBound : ∀ {b} events, epochBeforePayments config checks s = .ok b →
      epochBalanceReplay (config := config) (checks := checks) s = .ok (b, events) →
      potential b + fundingCarry ⟨fork, b⟩ ≤ potential s + fundingCarry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + (events.map fundingCredit).sum)
    (effectiveBound : ∀ {a b}, BalancesMatch a →
      processEffectiveBalanceUpdates a = .ok b → potential b ≤ potential a)
    (early : fork < .glamsterdam)
    (matched : BalancesMatch s)
    (ok : processEpoch config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events)) :
    potential t + fundingCarry ⟨fork, t⟩ ≤
      potential s + fundingCarry ⟨fork, s⟩ +
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
  have bound := beforeBound events beforeOk replayed
  have late := funding_late_of potential ordinary tail
  have beforeMatch : BalancesMatch before :=
    prefixTrace.transport (fun a b => BalancesMatch a → BalancesMatch b)
      (fun _ => id) (fun one two => two ∘ one) (by
        intro k _ a b computed
        have edge := EpochStage.action_cases.mp computed
        by_cases justification : k = .justification
        · subst k
          obtain ⟨validators, balances, _⟩ :=
            edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          simpa only [BalancesMatch, validators, balances] using (id : BalancesMatch a → _)
        · exact edge.balancesMatch_of_not_justification justification) matched
  have effective := effectiveBound beforeMatch updatedEdge
  have carry := updatedEdge.depositCarry nofun
  simp only [fundingCarry, carry] at late bound ⊢
  omega

/-- The epoch passes conserve funding apart from churn and the recorded external credits.

The epoch is cut after the stages before the payments, whose replay is unique.

Before Gloas the payments are the identity. -/
theorem funding_epoch {fork : Fork} {s t middle : BeaconState preset fork}
    (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s)
    (pending : PendingConsolidationInvariant config s)
    (ok : processEpoch config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events)) :
    fundedStake ⟨fork, t⟩ + fundingCarry ⟨fork, t⟩ ≤
      fundedStake ⟨fork, s⟩ + fundingCarry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  apply funding_epoch_of (fun a => fundedStake ⟨fork, a⟩) funding_stage
    (fun events ok replayed =>
      funding_before early delay matched ordered activation pending ok events replayed)
    (fun {a b} _ updatedEdge => ?_) early matched ok events replayed
  have sources : fundingSources b = fundingSources a := by
    unfold fundingSources
    rw [show b.pendingConsolidations = a.pendingConsolidations from
      (show EpochStage.Edge config checks .effectiveBalances a b from updatedEdge).samePendingQueue
          nofun]
  rw [← fundingPotential_eq, ← fundingPotential_eq, sources]
  exact funding_effective_updates (fundingSources a) updatedEdge

end

end EthLib.Consensus.DirectSafety
