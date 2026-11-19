module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Issuance

/-!
# The inputs of a branch drift

A branch runs from the reference state to a later state.

This module bounds what a branch reads: its deposits, inactivity scores and departures.

It also bounds the count of active keys before Electra and the participating balance of a pass.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-! ## The events of an epoch replay

The stages of an epoch after the rewards record slashing, deposit and consolidation events only.

Only the pending-deposit stage records a deposit event, and it records at most one.
-/

/-- The stages of an epoch after the rewards append only slashing, deposit and consolidation events.

Only the pending-deposit stage appends a deposit event, and it appends at most one. -/
private theorem epochReplayAction_sources {f : Fork} {k : EpochStage}
    (later : k ∈ [EpochStage.registry, .slashings, .eth1Reset, .pendingDeposits,
      .pendingConsolidations]) {pre post : BalanceReplay preset f}
    (ok : epochReplayAction (config := config) (checks := checks) k pre = .ok post) :
    ∃ added, post.2 = pre.2 ++ added ∧ (∀ e ∈ added,
      e.source = .slashings ∨ e.source = .deposits ∨ e.source = .consolidations) ∧
      (added.filter fun e => e.source = .deposits).length ≤ 1 ∧
      (k ≠ .pendingDeposits → (added.filter fun e => e.source = .deposits).length = 0) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at later
  rcases later with rfl | rfl | rfl | rfl | rfl <;> simp only [epochReplayAction] at ok
  · simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact ⟨[], by simp, by simp, by simp, fun _ => by simp⟩
  · simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact ⟨_, rfl, by simp, (List.length_filter_le _ _).trans (by simp), fun _ => by simp⟩
  all_goals
    split at ok
    · simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, rfl⟩ := ok
      first
        | exact ⟨_, rfl, by simp, (List.length_filter_le _ _).trans (by simp),
            fun h => by first | exact absurd rfl h | simp⟩
        | exact ⟨[], by simp, by simp, by simp, fun _ => by simp⟩
    · cases ok
      exact ⟨[], by simp, by simp, by simp, fun _ => by simp⟩

/-- The replay of an epoch, from Altair, runs justification and inactivity, then the rewards.

Its events are those of the rewards pass, replayed from the state after the score update.

They are followed by slashing, deposit and consolidation events only.

The rewards pass records reward, penalty and inactivity events only.

The later stages record at most one deposit event. -/
private theorem epochReplay_events_core {f : Fork} (altair : .altair ≤ f)
    {cached : BeaconState preset f} {post : BalanceReplay preset f}
    (trace : EpochTrace (epochReplayAction (config := config) (checks := checks))
      EpochStage.prefixStages (cached, []) post) :
    ∃ just pass rewarded later, EpochStage.Edge config checks .justification cached just ∧
      EpochStage.Edge config checks .inactivity just pass ∧
      replayRewards (config := config) (pass, []) = .ok rewarded ∧
      post.2 = rewarded.2 ++ later ∧
      (∀ e ∈ later, e.source = .slashings ∨ e.source = .deposits ∨ e.source = .consolidations) ∧
      (∀ e ∈ rewarded.2, e.source = .rewards ∨ e.source = .penalties ∨ e.source = .inactivity) ∧
      (later.filter fun e => e.source = .deposits).length ≤ 1 := by
  simp only [EpochStage.prefixStages] at trace
  cases trace with | cons one trace =>
  cases trace with | cons two trace =>
  cases trace with | cons three trace =>
  cases trace with | cons four trace =>
  cases trace with | cons five trace =>
  cases trace with | cons six trace =>
  cases trace with | cons seven trace =>
  cases trace with | cons eight trace =>
  cases trace
  simp only [epochReplayAction, carryBalance, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at one
  obtain ⟨just, justOk, rfl⟩ := one
  simp only [epochReplayAction, altair, ↓reduceDIte, carryBalance, bind_ok_iff, pure,
    Except.pure, Except.ok.injEq] at two
  obtain ⟨pass, passOk, rfl⟩ := two
  simp only [epochReplayAction] at three
  -- The rewards record rewards and penalties only.
  have sources := replayRewards_induction (fun pre => ∀ e ∈ pre.2,
      e.source = .rewards ∨ e.source = .penalties ∨ e.source = .inactivity)
    (fun held ok => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | new
      · exact held e old
      · obtain rfl := List.mem_singleton.mp new
        exact .inl rfl)
    (fun penalty held ok => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | new
      · exact held e old
      · obtain rfl := List.mem_singleton.mp new
        exact .inr penalty)
    (by simp) three
  obtain ⟨a4, e4, s4, c4⟩ := epochReplayAction_sources (by simp) four
  obtain ⟨a5, e5, s5, c5⟩ := epochReplayAction_sources (by simp) five
  obtain ⟨a6, e6, s6, c6⟩ := epochReplayAction_sources (by simp) six
  obtain ⟨a7, e7, s7, c7⟩ := epochReplayAction_sources (by simp) seven
  obtain ⟨a8, e8, s8, c8⟩ := epochReplayAction_sources (by simp) eight
  refine ⟨just, pass, _, a4 ++ a5 ++ a6 ++ a7 ++ a8, justOk,
    by simp only [EpochStage.Edge, altair, ↓reduceDIte]; exact passOk, three,
    by rw [e8, e7, e6, e5, e4]; simp only [List.append_assoc], ?_, sources, ?_⟩
  · intro e member
    simp only [List.mem_append] at member
    rcases member with (((m | m) | m) | m) | m
    exacts [s4 e m, s5 e m, s6 e m, s7 e m, s8 e m]
  · simp only [List.filter_append, List.length_append]
    have z4 := c4.2 nofun
    have z5 := c5.2 nofun
    have z6 := c6.2 nofun
    have z8 := c8.2 nofun
    have o7 := c7.1
    omega

/-- The replay of an epoch, from Altair, runs justification and inactivity, then the rewards.

Its events are those of the rewards pass, replayed from the state after the score update.

They are followed by slashing, deposit and consolidation events only.

The rewards pass records reward, penalty and inactivity events only. -/
theorem epochReplay_events {f : Fork} (altair : .altair ≤ f)
    {cached : BeaconState preset f} {post : BalanceReplay preset f}
    (trace : EpochTrace (epochReplayAction (config := config) (checks := checks))
      EpochStage.prefixStages (cached, []) post) :
    ∃ just pass rewarded later, EpochStage.Edge config checks .justification cached just ∧
      EpochStage.Edge config checks .inactivity just pass ∧
      replayRewards (config := config) (pass, []) = .ok rewarded ∧
      post.2 = rewarded.2 ++ later ∧
      (∀ e ∈ later, e.source = .slashings ∨ e.source = .deposits ∨ e.source = .consolidations) ∧
      ∀ e ∈ rewarded.2, e.source = .rewards ∨ e.source = .penalties ∨ e.source = .inactivity := by
  obtain ⟨just, pass, rewarded, later, justOk, passOk, replayed, split, laterSources,
    rewardSources, -⟩ := epochReplay_events_core altair trace
  exact ⟨just, pass, rewarded, later, justOk, passOk, replayed, split, laterSources,
    rewardSources⟩

/-- The replay of an epoch, from Altair, records at most one deposit event.

Only the pending-deposit stage records one, and the rewards pass records none. -/
private theorem epochReplay_deposit_count {f : Fork} (altair : .altair ≤ f)
    {cached : BeaconState preset f} {post : BalanceReplay preset f}
    (trace : EpochTrace (epochReplayAction (config := config) (checks := checks))
      EpochStage.prefixStages (cached, []) post) :
    (post.2.filter fun e => e.source = .deposits).length ≤ 1 := by
  obtain ⟨_, _, rewarded, later, _, _, _, split, _, rewardSources, count⟩ :=
    epochReplay_events_core altair trace
  have none : (rewarded.2.filter fun e => e.source = .deposits).length = 0 :=
    List.length_eq_zero_iff.mpr (List.filter_eq_nil_iff.mpr fun e member => by
      rcases rewardSources e member with s | s | s <;> simp [s])
  rw [split, List.filter_append, List.length_append]
  omega

/-! ## No deposit credit to a withdrawable consolidation source

The withdrawn-source credit of an event is what a deposit event credits to pending sources.

It counts only the sources that can already withdraw at the current epoch.

On a run from genesis it is zero at every deposit event.

From Electra, a block deposit only queues a pending deposit, so its event credits nothing.

The pass of the pending deposits starts at a state of the epoch replay.

The stages before it keep the pending consolidations ordered, with the current epoch as bound.

So every pending source there withdraws after the current epoch, slashed or not.
-/

/-- The credit to withdrawable pending sources is part of the credits of the event. -/
private theorem withdrawnConsolidationCredit_le_credits (event : BalanceEvent preset) :
    withdrawnConsolidationCredit event ≤ event.credits := by
  unfold withdrawnConsolidationCredit BalanceEvent.credits
  split
  · rename_i electra
    rw [funding_sum_zipIdx event.before.state.validators.data.toList (fun v i =>
      if decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch event.before.state).toNat) &&
          (event.before.state.pendingConsolidations electra).data.any
            (fun c => c.sourceIndex.toNat == i) then
        actualBalanceAt event.after i - actualBalanceAt event.before i else 0)]
    let credit := fun i => actualBalanceAt event.after i - actualBalanceAt event.before i
    -- A position past the balances after the event credits nothing.
    have outside : ∀ i ∈ Finset.range event.before.state.validators.data.toList.length,
        credit i ≠ 0 → i < event.after.state.balances.data.size := by
      intro i _ positive
      by_contra past
      apply positive
      simp [credit, actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt past)]
    calc _ ≤ ∑ i ∈ Finset.range event.before.state.validators.data.toList.length, credit i :=
          Finset.sum_le_sum fun i _ => by
            cases event.before.state.validators.data.toList[i]? with
            | none => exact Nat.zero_le _
            | some v =>
              simp only [Option.map_some, Option.getD_some]
              split
              · exact Nat.le_refl _
              · exact Nat.zero_le _
      _ = ∑ i ∈ (Finset.range event.before.state.validators.data.toList.length).filter
            (· < event.after.state.balances.data.size), credit i :=
          (Finset.sum_filter_of_ne outside).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset fun i member => by
          simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
          exact member.2
  · exact Nat.zero_le _

/-- An event that starts at an ordered state credits no withdrawable pending source.

Every pending source there withdraws after the current epoch. -/
private theorem withdrawnConsolidationCredit_eq_zero_of_ordered {s t : BeaconState preset fork}
    {source : BalanceSource} {credit debit : Nat}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s) :
    withdrawnConsolidationCredit ⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ = 0 := by
  unfold withdrawnConsolidationCredit
  split
  · rename_i electra
    obtain ⟨-, sources⟩ := holds.2 electra
    refine List.sum_eq_zero fun x mem => ?_
    obtain ⟨⟨v, i⟩, member, rfl⟩ := List.mem_map.mp mem
    have read : s.validators.data[i]? = some v := by
      simpa using List.mem_zipIdx_iff_getElem?.mp member
    dsimp only
    split
    · rename_i due
      simp only [Bool.and_eq_true, decide_eq_true_eq, ← Array.any_toList, List.any_eq_true,
        beq_iff_eq] at due
      obtain ⟨withdrawable, c, mem, index⟩ := due
      obtain ⟨-, -, late⟩ := sources c mem v (by rw [index]; exact read)
      omega
    · rfl
  · rfl

/-- The deposit events of an ordered state's epoch replay credit no withdrawable pending source.

Each stage keeps the order at the current epoch, so the deposit event starts at an ordered state.

A deposit event of the replay is the pending-deposit pass at a state with matching sizes. -/
private theorem epochBalanceReplay_deposits {checks : SignatureChecks}
    {s : BeaconState preset fork} {post : BalanceReplay preset fork}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    (∀ e ∈ post.2, e.source = .deposits → withdrawnConsolidationCredit e = 0) ∧
    (BalancesMatch s → ExitsOrdered s → ∀ e ∈ post.2, e.source = .deposits →
      ∃ (electra : .pectra ≤ fork) (u v : BeaconState preset fork),
        BalancesMatch u ∧ ExitsOrdered u ∧ RegistryLifecycle u post.1 ∧
          processPendingDeposits config checks u electra = .ok v ∧
          e.before = ⟨fork, u⟩ ∧ e.after = ⟨fork, v⟩) := by
  let Settled (pre : BalanceReplay preset fork) : Prop :=
    PendingConsolidationsOrdered config (getCurrentEpoch pre.1).toNat pre.1 ∧
      (∀ e ∈ pre.2, e.source = .deposits → withdrawnConsolidationCredit e = 0) ∧
      (BalancesMatch s → ExitsOrdered s → BalancesMatch pre.1 ∧ ExitsOrdered pre.1 ∧
        ∀ e ∈ pre.2, e.source = .deposits →
          ∃ (electra : .pectra ≤ fork) (u v : BeaconState preset fork),
            BalancesMatch u ∧ ExitsOrdered u ∧ RegistryLifecycle u pre.1 ∧
              processPendingDeposits config checks u electra = .ok v ∧
              e.before = ⟨fork, u⟩ ∧ e.after = ⟨fork, v⟩)
  -- A stage moves the state along its edge and records events that are not deposits.
  have moved {k : EpochStage} {pre : BalanceReplay preset fork} {u : BeaconState preset fork}
      (added : List (BalanceEvent preset)) (held : Settled pre)
      (edge : EpochStage.Edge config checks k pre.1 u)
      (keeps : BalancesMatch pre.1 → BalancesMatch u)
      (ord : ExitsOrdered pre.1 → ExitsOrdered u)
      (quiet : ∀ e ∈ added, e.source ≠ .deposits) : Settled (u, pre.2 ++ added) := by
    refine ⟨edge.pendingConsolidationsOrdered held.1, fun e mem deposit => ?_,
      fun matched ordered => ?_⟩
    · rcases List.mem_append.mp mem with mem | mem
      · exact held.2.1 e mem deposit
      · exact absurd deposit (quiet e mem)
    · obtain ⟨before, beforeOrd, sites⟩ := held.2.2 matched ordered
      refine ⟨keeps before, ord beforeOrd, fun e mem deposit => ?_⟩
      rcases List.mem_append.mp mem with mem | mem
      · obtain ⟨electra, a, b, ma, oa, la, rest⟩ := sites e mem deposit
        exact ⟨electra, a, b, ma, oa, la.trans edge.registryLifecycle, rest⟩
      · exact absurd deposit (quiet e mem)
  -- A carried stage moves the state along its edge and records nothing.
  have carried {k : EpochStage} {action : BeaconState preset fork → Except TransitionError _}
      {pre next : BalanceReplay preset fork} (held : Settled pre)
      (edge : ∀ {u}, action pre.1 = .ok u → EpochStage.Edge config checks k pre.1 u)
      (keeps : ∀ {u}, action pre.1 = .ok u → BalancesMatch pre.1 → BalancesMatch u)
      (ord : ∀ {u}, action pre.1 = .ok u → ExitsOrdered pre.1 → ExitsOrdered u)
      (step : carryBalance action pre = .ok next) : Settled next := by
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨u, computed, rfl⟩ := step
    have settled := moved [] held (edge computed) (keeps computed) (ord computed)
      (fun _ mem => by cases mem)
    rwa [List.append_nil] at settled
  have done : Settled post := by
    refine (epochBalanceReplay_trace ok).transport (fun a b => Settled a → Settled b)
      (fun _ => id) (fun one two => two ∘ one) ?_
      ⟨holds, fun _ mem => (by cases mem),
        fun matched ordered => ⟨matched, ordered, fun _ mem => (by cases mem)⟩⟩
    intro k member pre next step held
    cases k <;> simp only [epochReplayAction] at step
    case justification =>
      exact carried (k := .justification) held id
        (fun ok => balancesMatch_of_sameSizes (sameSizes_processJustificationAndFinalization ok))
        (fun ok o => by
          simpa only [ExitsOrdered, (processJustificationAndFinalization_keeps ok).2.2.2.2.2.1]
            using o)
        step
    case registry =>
      exact carried (k := .registry) held id
        (fun ok => (frame_processRegistryUpdates ok).balancesMatch)
        (fun ok o => (frame_processRegistryUpdates ok).exitsOrdered o) step
    case inactivity =>
      split at step
      · rename_i present
        exact carried (k := .inactivity) held (fun computed => by
          simp only [EpochStage.Edge, present, ↓reduceDIte]
          exact computed) (fun ok => (frame_processInactivityUpdates ok).balancesMatch)
          (fun ok o => (frame_processInactivityUpdates ok).exitsOrdered o) step
      · cases step
        exact held
    case eth1Reset =>
      split at step
      · rename_i present
        exact carried (k := .eth1Reset) held (fun computed => by
          simp only [EpochStage.Edge, present, ↓reduceDIte]
          exact computed) (fun ok => (frame_processEth1DataReset ok).balancesMatch)
          (fun ok o => (frame_processEth1DataReset ok).exitsOrdered o) step
      · cases step
        exact held
    case rewards =>
      refine replayRewards_induction Settled (fun held ok => ?_) (fun penalty held ok => ?_)
        held step
      · simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at ok
        obtain ⟨_, _, u, raised, rfl⟩ := ok
        have sizes := sameSizes_increaseBalance raised
        obtain ⟨_, set⟩ := increaseBalance_ok raised
        obtain ⟨_, rfl⟩ := setBalance_ok set
        refine ⟨held.1, fun e mem deposit => ?_, fun matched ordered => ?_⟩
        · rcases List.mem_append.mp mem with mem | mem
          · exact held.2.1 e mem deposit
          · rw [List.mem_singleton.mp mem] at deposit
            cases deposit
        · obtain ⟨before, beforeOrd, sites⟩ := held.2.2 matched ordered
          refine ⟨balancesMatch_of_sameSizes sizes before, beforeOrd, fun e mem deposit => ?_⟩
          rcases List.mem_append.mp mem with mem | mem
          · obtain ⟨electra, a, b, ma, oa, la, rest⟩ := sites e mem deposit
            exact ⟨electra, a, b, ma, oa, la.trans (.of_data rfl), rest⟩
          · rw [List.mem_singleton.mp mem] at deposit
            cases deposit
      · simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at ok
        obtain ⟨_, _, u, lowered, rfl⟩ := ok
        have sizes := sameSizes_decreaseBalance lowered
        obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp lowered
        refine ⟨held.1, fun e mem deposit => ?_, fun matched ordered => ?_⟩
        · rcases List.mem_append.mp mem with mem | mem
          · exact held.2.1 e mem deposit
          · rw [List.mem_singleton.mp mem] at deposit
            rcases penalty with rfl | rfl <;> cases deposit
        · obtain ⟨before, beforeOrd, sites⟩ := held.2.2 matched ordered
          refine ⟨balancesMatch_of_sameSizes sizes before, beforeOrd, fun e mem deposit => ?_⟩
          rcases List.mem_append.mp mem with mem | mem
          · obtain ⟨electra, a, b, ma, oa, la, rest⟩ := sites e mem deposit
            exact ⟨electra, a, b, ma, oa, la.trans (.of_data rfl), rest⟩
          · rw [List.mem_singleton.mp mem] at deposit
            rcases penalty with rfl | rfl <;> cases deposit
    case slashings =>
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨_, _, u, slashed, rfl⟩ := step
      exact moved (k := .slashings) _ held slashed
        (fun matched => (frame_processSlashings slashed).balancesMatch matched)
        (fun o => (frame_processSlashings slashed).exitsOrdered o) (by simp)
    case pendingDeposits =>
      split at step
      · rename_i electra
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨u, deposited, rfl⟩ := step
        have edge : EpochStage.Edge config checks .pendingDeposits pre.1 u := by
          simp only [EpochStage.Edge, electra, ↓reduceDIte]
          exact deposited
        refine ⟨edge.pendingConsolidationsOrdered held.1, fun e mem deposit => ?_,
          fun matched ordered => ?_⟩
        · rcases List.mem_append.mp mem with mem | mem
          · exact held.2.1 e mem deposit
          · rw [List.mem_singleton.mp mem]
            exact withdrawnConsolidationCredit_eq_zero_of_ordered held.1
        · obtain ⟨before, beforeOrd, sites⟩ := held.2.2 matched ordered
          refine ⟨(frame_processPendingDeposits deposited).balancesMatch before,
            (frame_processPendingDeposits deposited).exitsOrdered beforeOrd,
            fun e mem deposit => ?_⟩
          rcases List.mem_append.mp mem with mem | mem
          · obtain ⟨electra, a, b, ma, oa, la, rest⟩ := sites e mem deposit
            exact ⟨electra, a, b, ma, oa, la.trans edge.registryLifecycle, rest⟩
          · rw [List.mem_singleton.mp mem]
            exact ⟨electra, pre.1, u, before, beforeOrd, edge.registryLifecycle, deposited,
              rfl, rfl⟩
      · cases step
        exact held
    case pendingConsolidations =>
      split at step
      · rename_i electra
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨u, consolidated, rfl⟩ := step
        exact moved (k := .pendingConsolidations) _ held
          (by simp only [EpochStage.Edge, electra, ↓reduceDIte]; exact consolidated)
          (fun matched => (frame_processPendingConsolidations consolidated).balancesMatch matched)
          (fun o => (frame_processPendingConsolidations consolidated).exitsOrdered o) (by simp)
      · cases step
        exact held
    all_goals simp [EpochStage.prefixStages] at member
  exact ⟨done.2.1, fun matched ordered => (done.2.2 matched ordered).2.2⟩

/-- The epoch replay of an ordered state credits no withdrawable pending source.

Each stage keeps the order at the current epoch, so the deposit event starts at an ordered state. -/
private theorem epochBalanceReplay_withdrawnConsolidationCredit {checks : SignatureChecks}
    {s : BeaconState preset fork} {post : BalanceReplay preset fork}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    ∀ e ∈ post.2, e.source = .deposits → withdrawnConsolidationCredit e = 0 :=
  (epochBalanceReplay_deposits holds ok).1

/-- The deposit events of one step before Gloas credit no withdrawable pending source.

A block deposit has no credit limit from Electra, and its credits are within that limit.

A slot runs the epoch replay from an ordered state, and its upgrades record no deposit.

A deposit event of a slot is the pending-deposit pass at an ordered state with matching sizes.

The registry of that state keeps its assigned epochs to the end of the slot. -/
private theorem stepBalanceEvents_deposits {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (step : Step config checks x y)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events) :
    (EventsBounded events →
      ∀ e ∈ events, e.source = .deposits → withdrawnConsolidationCredit e = 0) ∧
    ∀ (across : advanceSlotAcross config checks x = .ok y), step = Step.slot across →
      (∀ e ∈ events, e.source = .deposits →
        ∃ (electra : .pectra ≤ x.fork) (u v : BeaconState preset x.fork),
          BalancesMatch u ∧ ExitsOrdered u ∧ RegistryLifecycle u y.state ∧
            processPendingDeposits config checks u electra = .ok v ∧
            e.before = ⟨x.fork, u⟩ ∧ e.after = ⟨x.fork, v⟩) ∧
      ((∃ e ∈ events, e.source = .deposits) →
        (getCurrentEpoch y.state).toNat = (getCurrentEpoch x.state).toNat + 1) ∧
      (events.filter fun e => e.source = .deposits).length ≤ 1 := by
  have sourceEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | block engine signed due blockOk =>
    have quiet := funding_block_events sourceEarly engine signed.message
      (Step.balanceEvents_block sourceEarly ok)
    refine ⟨fun bounded e mem deposit => ?_, fun across same => by cases same⟩
    by_cases electra : .pectra ≤ e.before.fork
    · have zero := quiet e mem deposit electra
      have within := (bounded e mem).1
      have part := withdrawnConsolidationCredit_le_credits e
      omega
    · rw [withdrawnConsolidationCredit, dite_eq_right electra]
  | slot across =>
    -- The slot replays the epoch only at its last slot, then records the upgrade crossings.
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp across
    have steps := advanceOk
    simp only [advanceSlot, bind_ok_iff] at steps
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochedOk, advancedEq⟩ := steps
    obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
    have crossed : ∀ e ∈ crossings, e.source ≠ .deposits := fun e mem deposit =>
      absurd ((upgradeBalanceReplay_crossing crossingOk e mem).symm.trans deposit) (by decide)
    obtain ⟨last, epochedOk⟩ | ⟨last, rfl⟩ := epochIfLast_cases epochedOk
    · obtain ⟨middle, updated, epochEvents, replayOk, updateOk, updatedValidators, -⟩ :=
        epochBalanceReplay_result cached epoched sourceEarly epochedOk
      rw [Step.balanceEvents_epoch_slot across cachedOk nextOk last replayOk advanceOk
        crossingOk] at ok
      cases ok
      have matched : BalancesMatch cached :=
        (frame_processSlot cachedOk).balancesMatch
          (run_justified_separated shared genesis).1.balancesMatch
      have exitsOrd : ExitsOrdered cached :=
        (frame_processSlot cachedOk).exitsOrdered
          (run_justified_separated shared genesis).1.exitsOrdered
      have toEnd : RegistryLifecycle middle y.state := by
        simp only [pure, Except.pure, Except.ok.injEq] at advancedEq
        have epochedKept : RegistryLifecycle updated epoched :=
          .of_data (congrArg (·.data) updatedValidators.symm)
        have advancedKept : RegistryLifecycle epoched advanced := by
          rw [← advancedEq]
          exact .of_data rfl
        have upgraded := processUpgrades_induction
          (property := fun post => RegistryLifecycle advanced post.state)
          (fun before ok => before.trans (registryLifecycle_upgradeNext ok)) (.refl advanced)
          upgrades
        exact (EpochStage.Edge.registryLifecycle (config := config) (checks := checks)
          (k := .effectiveBalances) updateOk).trans
          (epochedKept.trans (advancedKept.trans upgraded))
      have ordered : PendingConsolidationsOrdered config (getCurrentEpoch cached).toNat
          cached := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
        exact shared.pendingConsolidationsOrdered genesis sourceEarly delay
      refine ⟨fun _ e mem deposit => ?_,
        fun across' same => ⟨fun e mem deposit => ?_, fun _ => ?_, ?_⟩⟩
      · rcases List.mem_append.mp mem with mem | mem
        · exact (epochBalanceReplay_deposits ordered replayOk).1 e mem deposit
        · exact absurd deposit (crossed e mem)
      · rcases List.mem_append.mp mem with mem | mem
        · obtain ⟨electra, a, b, ma, oa, la, rest⟩ :=
            (epochBalanceReplay_deposits ordered replayOk).2 matched exitsOrd e mem deposit
          exact ⟨electra, a, b, ma, oa, la.trans toEnd, rest⟩
        · exact absurd deposit (crossed e mem)
      · -- The epoch replay runs at the last slot of an epoch, which the slot then leaves.
        have remainder : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
          simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat last
        have nextVal : next.toNat = x.state.slot.toNat + 1 := by
          simp only [liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff,
            UInt64.toNat_one] at nextOk
          exact nextOk.2
        have divides := Nat.dvd_of_mod_eq_zero remainder
        rw [nextVal] at divides
        have slotEq := processUpgrades_slot upgrades
        simp only [pure, Except.pure, Except.ok.injEq] at advancedEq
        have advancedSlot : advanced.slot = next := by
          rw [← advancedEq]
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotEq, advancedSlot, nextVal]
        exact Nat.succ_div_of_dvd divides
      · -- Only the pending-deposit stage records a deposit, so an epoch replay records one at most.
        have none : (crossings.filter fun e => e.source = .deposits).length = 0 :=
          List.length_eq_zero_iff.mpr (List.filter_eq_nil_iff.mpr fun e mem => by
            simpa using crossed e mem)
        rw [List.filter_append, List.length_append, none, Nat.add_zero]
        by_cases any : ∃ e ∈ epochEvents, e.source = .deposits
        · obtain ⟨e, mem, deposit⟩ := any
          obtain ⟨electra, -⟩ := (epochBalanceReplay_deposits ordered replayOk).2 matched exitsOrd
            e mem deposit
          exact epochReplay_deposit_count (Nat.le_trans (by decide) electra)
            (epochBalanceReplay_trace replayOk)
        · have none : (epochEvents.filter fun e => e.source = .deposits).length = 0 :=
            List.length_eq_zero_iff.mpr (List.filter_eq_nil_iff.mpr fun e mem => by
              simpa using fun deposit => any ⟨e, mem, deposit⟩)
          omega
    · have replayed : (Step.slot across).balanceEvents = .ok ([] ++ crossings) := by
        simp only [Step.balanceEvents, cachedOk, nextOk, last, ↓reduceIte, advanceOk,
          crossingOk, bind, Except.bind, pure, Except.pure]
      rw [replayed] at ok
      cases ok
      exact ⟨fun _ e mem deposit => absurd deposit (crossed e (by simpa using mem)),
        fun across' same => ⟨fun e mem deposit => absurd deposit (crossed e (by simpa using mem)),
          fun ⟨e, mem, deposit⟩ => absurd deposit (crossed e (by simpa using mem)),
          by
            rw [List.nil_append]
            exact Nat.le_trans (Nat.le_of_eq (List.length_eq_zero_iff.mpr
              (List.filter_eq_nil_iff.mpr fun e mem => by simpa using crossed e mem)))
              (Nat.zero_le _)⟩⟩

/-- The deposit events of one step before Gloas credit no withdrawable pending source.

A block deposit has no credit limit from Electra, and its credits are within that limit.

A slot runs the epoch replay from an ordered state, and its upgrades record no deposit. -/
private theorem stepBalanceEvents_withdrawnConsolidationCredit {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (step : Step config checks x y)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events)
    (bounded : EventsBounded events) :
    ∀ e ∈ events, e.source = .deposits → withdrawnConsolidationCredit e = 0 :=
  (stepBalanceEvents_deposits shared genesis step early delay ok).1 bounded

/-- A slot step records at most one deposit event, a pending-deposit pass at an epoch's end.

The pass starts at an ordered state, whose registry keeps its assigned epochs to the slot's end. -/
theorem Step.slot_deposit_site {checks : SignatureChecks} {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (across : advanceSlotAcross config checks x = .ok y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (ok : (Step.slot across).balanceEvents = .ok events) :
    (∀ e ∈ events, e.source = .deposits →
      ∃ (electra : .pectra ≤ x.fork) (u v : BeaconState preset x.fork),
        BalancesMatch u ∧ ExitsOrdered u ∧ RegistryLifecycle u y.state ∧
          processPendingDeposits config checks u electra = .ok v ∧
          e.before = ⟨x.fork, u⟩ ∧ e.after = ⟨x.fork, v⟩) ∧
    ((∃ e ∈ events, e.source = .deposits) →
      (getCurrentEpoch y.state).toNat = (getCurrentEpoch x.state).toNat + 1) ∧
    (events.filter fun e => e.source = .deposits).length ≤ 1 :=
  (stepBalanceEvents_deposits shared genesis (Step.slot across) early delay ok).2 across rfl

/-- Lemma WC: on a run from genesis, no deposit event credits a withdrawable pending source.

Every pending consolidation source of a reachable state withdraws after the current epoch.

The epoch pass of the pending deposits starts at such a state, and block deposits credit nothing.

It covers the deposit events, the only ones whose funding credit reads this credit. -/
theorem _root_.EthLib.Consensus.Run.withdrawnConsolidationCredit_eq_zero
    {checks : SignatureChecks} {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {high : Nat} {events : List (BalanceEvent preset)}
    (ok : tail.balanceEvents high = .ok events) :
    ∀ e ∈ events,
      (e.source = .deposits → withdrawnConsolidationCredit e = 0) ∧
      (0 < e.creditLimit → e.source = .rewards ∨ e.source = .sync ∨
        e.source = .slashings ∨ e.source = .deposits ∨ e.source = .consolidations) ∧
      x.fork ≤ e.before.fork := by
  -- Every event of the run is within its own limits.
  obtain ⟨recorded, recordedOk, bounded⟩ :=
    Run.balanceEvents_bounded shared tail genesis early high
  rw [ok] at recordedOk
  cases recordedOk
  have key : ∀ {z : ForkedBeaconState preset} (part : Run config checks x z),
      z.fork < .glamsterdam → ∀ {found : List (BalanceEvent preset)},
        part.balanceEvents high = .ok found → EventsBounded found →
          ∀ e ∈ found,
            (e.source = .deposits → withdrawnConsolidationCredit e = 0) ∧
            (0 < e.creditLimit → e.source = .rewards ∨ e.source = .sync ∨
              e.source = .slashings ∨ e.source = .deposits ∨
                e.source = .consolidations) ∧ x.fork ≤ e.before.fork := by
    intro z part
    induction part with
    | nil =>
      intro _ found ok _
      simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact fun _ mem => by cases mem
    | snoc pre step ih =>
      intro early found ok bounded
      simp only [Run.balanceEvents, bind_ok_iff] at ok
      obtain ⟨prior, priorOk, rest⟩ := ok
      have before := Nat.lt_of_le_of_lt step.chainStep.fork_le early
      split at rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        intro e mem
        rcases List.mem_append.mp mem with mem | mem
        · exact ih before priorOk (fun e member => bounded e (List.mem_append_left _ member))
            e mem
        · have sites := step.balanceEvents_credit_sources early
            (run_justified_separated (shared.append pre) genesis).1 addedOk e mem
          exact ⟨stepBalanceEvents_withdrawnConsolidationCredit (shared.append pre) genesis step
            early delay addedOk (fun e member => bounded e (List.mem_append_right _ member)) e mem,
            sites.2, Nat.le_trans (fork_le_of_chainSteps pre.chainSteps) sites.1⟩
      · cases rest
        exact ih before priorOk bounded
  exact key tail early ok bounded

/-! ## The a priori branch drift

The drift `f` of a branch is a function of numbers read at its reference state `x`.

These numbers are the observables below, and the window `H` with the epochs `H1` before Electra.

`f` itself reads only those numbers and the constants of the preset and the configuration.

Its index `t` runs over the epochs `0` to `H + 1` of the window.

"Before the fork" means `t < H1`.
-/

theorem countPath_monotone (config : Config) (start : Nat) :
    Monotone (activeCountPath config start) :=
  monotone_nat_of_le_succ fun _ => Nat.le_add_right _ _

/-! ## The observables of a reference state

Each observable is a number read at the reference state `x` of a branch.

It is a parameter of the drift, not a premise.
-/

/-! ## The inactivity scores of a branch

From Altair, the score of a key rises by at most the score bias at each update.

Every other step keeps the scores at the positions that exist before it.

So a key of the registry at `x` has a score of at most `sigma + bias * t` after `t` updates.

`sigma` is the start score, at least each score at `x`.
-/

/-- From Altair, the score of a state at each position `i` below `n` is at most `bound i`. -/
private def ScoresBelowAt (n : Nat) (bound : Nat → Nat) (s : ForkedBeaconState preset) : Prop :=
  ∀ altair : .altair ≤ s.fork, ∀ i < n, ∀ score : UInt64,
    (s.state.inactivityScores altair).data[i]? = some score → score.toNat ≤ bound i

/-- A step that keeps the scores below `n` keeps their bound. -/
private theorem ScoresBelowAt.of_kept {f : Fork} {s t : BeaconState preset f} {n : Nat}
    {bound : Nat → Nat}
    (kept : ∀ i < n, ScoreKept i s t) (below : ScoresBelowAt n bound ⟨f, s⟩) :
    ScoresBelowAt n bound ⟨f, t⟩ := fun altair i member score found =>
  below altair i member score (by rw [← kept i member altair]; exact found)

/-- An update of the scores raises each one by at most the score bias. -/
private theorem ScoresBelowAt.inactivity {f : Fork} {s t : BeaconState preset f} {n : Nat}
    {bound : Nat → Nat}
    (altair : .altair ≤ f) (computed : processInactivityUpdates config s altair = .ok t)
    (below : ScoresBelowAt n bound ⟨f, s⟩) :
    ScoresBelowAt n (fun i => bound i + config.INACTIVITY_SCORE_BIAS.toNat) ⟨f, t⟩ := by
  intro _ i member score found
  obtain ⟨old, olds, raised⟩ := processInactivityUpdates_score_le computed found
  have := below altair i member old olds
  dsimp only
  omega

/-- Justification keeps the scores, and the update after it raises each by the bias at most. -/
private theorem ScoresBelowAt.pass {f : Fork} {s cached just pass : BeaconState preset f}
    {n : Nat} {bound : Nat → Nat} (altair : .altair ≤ f) (below : ScoresBelowAt n bound ⟨f, s⟩)
    (cachedOk : processSlot s = .ok cached)
    (justified : processJustificationAndFinalization cached = .ok just)
    (scored : processInactivityUpdates config just altair = .ok pass) :
    ScoresBelowAt n (fun i => bound i + config.INACTIVITY_SCORE_BIAS.toNat) ⟨f, pass⟩ := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  refine ScoresBelowAt.inactivity altair scored (ScoresBelowAt.of_kept (fun i _ =>
    ScoreKept.of_scores (processJustificationAndFinalization_inactivityScores justified) i) ?_)
  exact ScoresBelowAt.of_kept (fun i _ => ScoreKept.of_scores rfl i) below

/-- An upgrade before Gloas from Altair keeps the scores, unless it is the upgrade to Electra. -/
private theorem upgradeNext_scores {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) (altair : .altair ≤ pre.fork)
    (early : post.val.fork < .glamsterdam) (era : .pectra ≤ pre.fork ∨ post.val.fork < .pectra)
    (later : .altair ≤ post.val.fork) :
    (post.val.state.inactivityScores later).data = (pre.state.inactivityScores altair).data := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp [carryFields, carryList, altair]
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    simp [carryFields, carryList, altair]
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    dsimp only at era
    exact absurd era (by decide)
  case fusaka | glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    dsimp only at early
    exact absurd early (by decide)
  all_goals
    dsimp only at altair
    first
    | exact absurd altair (by decide)
    | (simp only [upgradeNext] at computed; cases computed)

/-- The upgrades of a slot step keep the bound of the scores below `n`, before Gloas. -/
private theorem ScoresBelowAt.upgrades {s t : ForkedBeaconState preset} {n : Nat}
    {bound : Nat → Nat}
    (computed : processUpgrades config checks s = .ok t) (altair : .altair ≤ s.fork)
    (early : t.fork < .glamsterdam) (era : .pectra ≤ s.fork ∨ t.fork < .pectra)
    (below : ScoresBelowAt n bound s) : ScoresBelowAt n bound t := by
  refine (processUpgrades_induction (property := fun u => u.fork < .glamsterdam →
      (.pectra ≤ s.fork ∨ u.fork < .pectra) → s.fork ≤ u.fork ∧ ScoresBelowAt n bound u)
    (fun {pre post} held stepOk postEarly postEra => ?_)
    (fun _ _ => ⟨Nat.le_refl _, below⟩) computed early era).2
  have rising := post.property
  obtain ⟨low, preBelow⟩ := held (Nat.lt_trans rising postEarly)
    (postEra.imp id fun before => Nat.lt_trans rising before)
  refine ⟨Nat.le_trans low (Nat.le_of_lt rising), fun later i member score found => ?_⟩
  have same := upgradeNext_scores stepOk (Nat.le_trans altair low) postEarly
    (postEra.imp (fun electra => Nat.le_trans electra low) id) later
  rw [same] at found
  exact preBelow (Nat.le_trans altair low) i member score found

/-- A step from Altair keeps the bound of the scores below `n`, or raises it by the bias.

It needs no premise on the registry: a validator that the step adds takes the score zero.

It raises the bound only when the step ends an epoch, and so moves the epoch on by one. -/
private theorem ScoresBelowAt.step_all {m l : ForkedBeaconState preset}
    (step : Step config checks m l)
    {n : Nat} {bound : Nat → Nat} (altair : .altair ≤ m.fork)
    (early : l.fork < .glamsterdam) (era : .pectra ≤ m.fork ∨ l.fork < .pectra)
    (below : ScoresBelowAt n bound m) :
    ScoresBelowAt n (fun i => bound i + config.INACTIVITY_SCORE_BIAS.toNat *
      ((getCurrentEpoch l.state).toNat - (getCurrentEpoch m.state).toNat)) l := by
  cases step with
  | @block f before after engine signed due ok =>
    -- A block keeps its slot and the scores of the registry before it.
    have processed := (applySignedBlock_ok ok).2.1
    have same : getCurrentEpoch after = getCurrentEpoch before := by
      simp only [getCurrentEpoch, (frame_processBlock processed).slot]
    show ScoresBelowAt n (fun i => bound i + config.INACTIVITY_SCORE_BIAS.toNat *
      ((getCurrentEpoch after).toNat - (getCurrentEpoch before).toNat)) ⟨_, after⟩
    simp only [same, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    intro later i member score found
    rcases (scoresKept_processBlock processed).2 later i score found with old | zero
    · exact below later i member score old
    · simp [zero]
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advanceOk
    have lSlot : l.state.slot = next := processUpgrades_slot upgrades
    have lEpoch : (getCurrentEpoch l.state).toNat =
        next.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [getCurrentEpoch_toNat, lSlot]
    refine ScoresBelowAt.upgrades upgrades altair early era ?_
    rw [lEpoch, getCurrentEpoch_toNat]
    obtain ⟨last, epochedOk⟩ | ⟨within, rfl⟩ := epochIfLast_cases epochedOk
    · -- The last slot of an epoch updates the scores once, and moves the epoch on by one.
      rw [nextSlot_epoch_of_boundary sum last, Nat.add_sub_cancel_left, Nat.mul_one]
      have epochRun : processEpochAltair config checks cached altair = .ok epoched := by
        unfold processEpoch at epochedOk
        simpa only [altair, ↓reduceDIte] using epochedOk
      intro later i member score found
      obtain ⟨just, pass, justified, scored, -, kept⟩ := scoresKept_processEpochAltair epochRun
      rcases kept i score found with old | zero
      · exact ScoresBelowAt.pass altair below cachedOk justified scored later i member score old
      · simp [zero]
    · -- Another slot keeps the epoch and the scores.
      simp only [nextSlot_epoch_of_inside sum within, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      exact ScoresBelowAt.of_kept (fun i _ => ScoreKept.of_scores rfl i) below

/-- On a branch from `x` from Altair, each score below `n` follows its start bound plus `bias * t`.

It needs no premise on the registry at `x`: a validator that the branch adds takes the score zero.

`t` is the number of epochs from `x`, so the number of updates of the scores so far. -/
private theorem scoresBelowAt_run_all {x y : ForkedBeaconState preset}
    (tail : Run config checks x y)
    (altair : .altair ≤ x.fork) (early : y.fork < .glamsterdam)
    (era : .pectra ≤ x.fork ∨ y.fork < .pectra) {n : Nat} {start : Nat → Nat}
    (initial : ScoresBelowAt n start x) :
    ScoresBelowAt n (fun i => start i + config.INACTIVITY_SCORE_BIAS.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat)) y := by
  induction tail with
  | nil =>
    intro altair' i member score found
    simpa using initial altair' i member score found
  | @snoc m l pre step ih =>
    have mEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have forks := fork_le_of_chainSteps pre.chainSteps
    have before := ih mEarly
      (era.imp id fun later => Nat.lt_of_le_of_lt step.chainStep.fork_le later)
    have moved := ScoresBelowAt.step_all step (Nat.le_trans altair forks) early
      (era.imp (fun electra => Nat.le_trans electra forks) id) before
    have first := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have second := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    intro later i member score found
    have bound := moved later i member score found
    dsimp only at bound ⊢
    have epochs : (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat +
        ((getCurrentEpoch l.state).toNat - (getCurrentEpoch m.state).toNat) =
          (getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat := by omega
    rw [Nat.add_assoc, ← Nat.mul_add, epochs] at bound
    exact bound

/-- From Altair, each score of a state at a position below `n` is at most `bound`. -/
def ScoresBelow (n bound : Nat) (s : ForkedBeaconState preset) : Prop :=
  ∀ altair : .altair ≤ s.fork, ∀ i < n, ∀ score : UInt64,
    (s.state.inactivityScores altair).data[i]? = some score → score.toNat ≤ bound

/-- An update of the scores raises each one by at most the score bias. -/
theorem ScoresBelow.inactivity {f : Fork} {s t : BeaconState preset f} {n bound : Nat}
    (altair : .altair ≤ f) (computed : processInactivityUpdates config s altair = .ok t)
    (below : ScoresBelow n bound ⟨f, s⟩) :
    ScoresBelow n (bound + config.INACTIVITY_SCORE_BIAS.toNat) ⟨f, t⟩ :=
  ScoresBelowAt.inactivity (bound := fun _ => bound) altair computed below

/-- Justification keeps the scores, and the update after it raises each by the bias at most. -/
private theorem ScoresBelow.pass {f : Fork} {s cached just pass : BeaconState preset f}
    {n bound : Nat} (altair : .altair ≤ f) (below : ScoresBelow n bound ⟨f, s⟩)
    (cachedOk : processSlot s = .ok cached)
    (justified : processJustificationAndFinalization cached = .ok just)
    (scored : processInactivityUpdates config just altair = .ok pass) :
    ScoresBelow n (bound + config.INACTIVITY_SCORE_BIAS.toNat) ⟨f, pass⟩ :=
  ScoresBelowAt.pass (bound := fun _ => bound) altair below cachedOk justified scored

/-- A step from Altair keeps the bound of the scores below `n`, or raises it by the bias.

It raises it only when it ends an epoch, and so moves the epoch on by one. -/
theorem ScoresBelow.step {m l : ForkedBeaconState preset} (step : Step config checks m l)
    {n bound : Nat} (altair : .altair ≤ m.fork) (inside : n ≤ m.state.validators.data.size)
    (early : l.fork < .glamsterdam) (era : .pectra ≤ m.fork ∨ l.fork < .pectra)
    (below : ScoresBelow n bound m) :
    ScoresBelow n (bound + config.INACTIVITY_SCORE_BIAS.toNat *
      ((getCurrentEpoch l.state).toNat - (getCurrentEpoch m.state).toNat)) l :=
  have _ := inside
  ScoresBelowAt.step_all (bound := fun _ => bound) step altair early era below

/-- From Altair, each score of a state is at most the start score that the floor reads. -/
private theorem scoresBelowAt_start (x : ForkedBeaconState preset) (altair : .altair ≤ x.fork)
    (n : Nat) : ScoresBelowAt n (fun _ => startInactivityScore config x) x := by
  intro _ i _ score found
  have member := le_foldr_max (List.mem_map_of_mem (f := UInt64.toNat)
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)))
  unfold startInactivityScore
  simp only [altair, ↓reduceDIte]
  exact member.trans (Nat.le_max_left _ _)

/-- On a branch from `x` from Altair, each score of a state is small, new positions too.

It holds for every position of the state, also those that the branch adds.

The score is at most `sigma + bias * t`, with `sigma` the start score that the floor reads.

`t` is the number of epochs from `x`, so the number of updates of the scores so far. -/
theorem runScores_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (altair : .altair ≤ x.fork) (early : y.fork < .glamsterdam)
    (era : .pectra ≤ x.fork ∨ y.fork < .pectra) (later : .altair ≤ y.fork) {i : Nat}
    {score : UInt64} (found : (y.state.inactivityScores later).data[i]? = some score) :
    score.toNat ≤ startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat *
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) :=
  scoresBelowAt_run_all (start := fun _ => startInactivityScore config x) tail altair early era
    (scoresBelowAt_start x altair (i + 1)) later i (Nat.lt_succ_self i) score found

/-- A key's score on a branch from Altair is at most its start score plus a bias per epoch. -/
theorem runScore_le_start {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (altair : .altair ≤ x.fork) (early : y.fork < .glamsterdam)
    (era : .pectra ≤ x.fork ∨ y.fork < .pectra) (later : .altair ≤ y.fork) {i : Nat}
    {score : UInt64} (found : (y.state.inactivityScores later).data[i]? = some score) :
    score.toNat ≤ (((x.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 +
      config.INACTIVITY_SCORE_BIAS.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) := by
  let start : Nat → Nat := fun j => if j = i then
    (((x.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0
    else startInactivityScore config x
  have initial : ScoresBelowAt (i + 1) start x := by
    intro altair' j below score' read
    by_cases same : j = i
    · subst same
      simp [start, read]
    · simpa [start, same] using scoresBelowAt_start x altair' (i + 1) altair' j below score' read
  have bound := scoresBelowAt_run_all tail altair early era initial later i (Nat.lt_succ_self i)
    score found
  simpa [start] using bound

/-- After the update of pass `s`, each inactivity score of the registry at `x` is small.

The pass ends epoch `s` of a branch from `x` from Altair, in the slot step from its last state `z`.

The score is at most `sigma + bias * (s + 1)`, with `sigma` the start score that `f` reads. -/
theorem referenceScores_le {x z : ForkedBeaconState preset} (head : Run config checks x z)
    (altair : .altair ≤ x.fork) (early : z.fork < .glamsterdam)
    (era : .pectra ≤ x.fork ∨ z.fork < .pectra)
    {cached just pass : BeaconState preset z.fork} (cachedOk : processSlot z.state = .ok cached)
    (justified : EpochStage.Edge config checks .justification cached just)
    (scored : EpochStage.Edge config checks .inactivity just pass)
    {i : Nat} (inside : i < x.state.validators.data.size) (later : .altair ≤ z.fork)
    {score : UInt64} (found : (pass.inactivityScores later).data[i]? = some score) :
    score.toNat ≤ startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat *
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat + 1) := by
  have scoredOk : processInactivityUpdates config just later = .ok pass := by
    simpa only [EpochStage.Edge, later, ↓reduceDIte] using scored
  have bound := ScoresBelow.pass (n := x.state.validators.data.size) later
    (fun later' _ _ _ found' => runScores_le head altair early era later' found') cachedOk
    justified scoredOk later i inside score found
  rwa [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

/-! ## The departures of a branch

The departures that a branch charges in its window fit the budget `Dnew` of the drift.

This is the window bound of the departure charges, with the counts and rates of the drift.

Two facts of the window are hypotheses here, since the ceiling of the active stake gives them.

Before the fork each step of the window starts with at most `A_{H+1}` active validators.

From Electra each step of the window starts with a consolidation churn of at most `Cc`.
-/

/-- A tail splits after its last step that starts by epoch `bound`.

The second part starts after `bound`, so it charges only exits after `bound`.

When the second part has a step, its start is after `bound` too. -/
theorem window_cut {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (bound : Nat) :
    ∃ (m : ForkedBeaconState preset) (cut : Run config checks x m) (rest : Run config checks m y),
      tail = cut.append rest ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), cut.Contains step →
        (getCurrentEpoch u.state).toNat ≤ bound) ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), rest.Contains step →
        bound < (getCurrentEpoch u.state).toNat) ∧
      (∀ charge ∈ rest.departureCharges, bound < charge.epoch) ∧
      (bound < (getCurrentEpoch m.state).toNat ∨
        ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
          ¬ rest.Contains step) := by
  induction tail with
  | nil => exact ⟨x, .nil, .nil, rfl, fun _ member => (by cases member),
      fun _ member => (by cases member),
      fun _ member => by simp [Run.departureCharges] at member,
      .inr fun _ member => by cases member⟩
  | @snoc b c pre step ih =>
    obtain ⟨m, cut, rest, rfl, inside, outside, later, start⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
    by_cases within : (getCurrentEpoch b.state).toNat ≤ bound
    · -- The tail so far starts by `bound` at its end, so its second part is empty.
      cases rest with
      | nil =>
        refine ⟨c, cut.snoc step, .nil, rfl, fun later member => ?_,
          fun _ member => (by cases member),
          fun _ member => by simp [Run.departureCharges] at member,
          .inr fun _ member => by cases member⟩
        cases member with
        | last => exact within
        | earlier member => exact inside later member
      | snoc rest last =>
        have after := outside last (.last _ _)
        have ordered := UInt64.le_iff_toNat_le.mp last.chainStep.currentEpoch_le
        omega
    · refine ⟨m, cut, rest.snoc step, rfl, inside, fun later member => ?_,
        fun charge member => ?_, ?_⟩
      · cases member with
        | last => omega
        | earlier member => exact outside later member
      · rcases List.mem_append.mp member with old | latest
        · exact later charge old
        · have lower := departureCharges_epoch_ge step early charge latest
          omega
      · -- Without an earlier step, the second part starts where this step starts.
        rcases start with after | empty
        · exact .inl after
        · cases rest with
          | nil => exact .inl (by omega)
          | snoc rest last => exact absurd (.last _ _) (empty last)

/-- The departures that a branch charges in its window fit the budget `Dnew`.

The window runs from the current epoch of `x` to `high + 1`.

A branch from Electra is charged its queue carry and the Electra churn from each queue end.

A branch before Electra ends before the fork epoch, so it is charged only the count churn. -/
theorem departures_le_budget {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high : Nat) (guard : aprioriGuardAt config x high)
    (counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat ≤ high + 1 → u.fork < .pectra →
        activeCount u.state ≤
          activeCountPath config (referenceCount x + scheduledActivationCount x)
              (driftHorizon x high + 1))
    (rates : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat ≤ high + 1 → .pectra ≤ u.fork →
        ∀ rate : Gwei, getConsolidationChurnLimit config u.state = .ok rate →
        rate.toNat ≤ consolidationChurn preset config
          (stakeCeiling preset config (referenceCount x) (scheduledActivationCount x)
                (unassignedPreStake x)
            (fundingCarry x) (exitedSlashableCount x) (fundedStake x + previousOnlyStake x)
            (driftHorizon x high) (preElectraEpochs config x high) (driftHorizon x high + 1))) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      departureBudget preset config (referenceCount x) (scheduledActivationCount x)
          (unassignedPreStake x)
        (fundingCarry x) (exitedSlashableCount x) (fundedStake x + previousOnlyStake x)
        (queueCarry x high)
        (exitQueueStart x - (getCurrentEpoch x.state).toNat)
        (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
        (driftHorizon x high) (preElectraEpochs config x high) := by
  -- D-Q reads only the steps of the window, and the steps after it charge later exits.
  obtain ⟨m, cut, rest, rfl, inside, -, later, -⟩ := window_cut tail early (high + 1)
  have cutEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have bound := departure_charges_le_window_from shared cut genesis caps cutEarly high _ _
    (fun step member => counted step ((Run.contains_append _ _ _).mpr (.inl member))
      (inside step member))
    (fun step member => rates step ((Run.contains_append _ _ _).mpr (.inl member))
      (inside step member))
  have after : ((rest.departureCharges.filter fun c => c.epoch ≤ high + 1).map
      (·.amount)).sum = 0 := by
    rw [List.filter_eq_nil_iff.mpr fun c member => by
      simpa using later c member]
    rfl
  rw [Run.departureCharges_append, List.filter_append, List.map_append, List.sum_append, after,
    Nat.add_zero]
  obtain ⟨-, -, minimum, -, -, -, -, -, -, -, -, -, -, crossing⟩ := guard
  -- The written-out carry of D-Q is the carry of the queues.
  change _ ≤ queueCarry x high + _ + _ + _ at bound
  simp only [departureBudget]
  generalize activeCountPath config (referenceCount x + scheduledActivationCount x)
      (driftHorizon x high + 1) = A
    at bound ⊢
  generalize consolidationChurn preset config (stakeCeiling preset config (referenceCount x)
    (scheduledActivationCount x) (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
    (fundedStake x + previousOnlyStake x) (driftHorizon x high) (preElectraEpochs config x high)
    (driftHorizon x high + 1)) = Cc at bound ⊢
  have horizon : driftHorizon x high = high + 2 - (getCurrentEpoch x.state).toNat := rfl
  rw [horizon] at crossing ⊢
  by_cases electra : .pectra ≤ x.fork
  · -- From Electra the count term is off, and each churn counts from its queue end on.
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
    simp only [zero, lt_self_iff_false, ↓reduceIte, notBefore, Nat.mul_zero,
      Nat.add_zero] at bound ⊢
    have from_ (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat
        (max start config.ELECTRA_FORK_EPOCH.toNat) ≤
          high + 2 - (getCurrentEpoch x.state).toNat + 2 -
            (start - (getCurrentEpoch x.state).toNat) := by omega
    have exitTerm := Nat.mul_le_mul_right
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (from_ (exitQueueStart x))
    have consolidationTerm := Nat.mul_le_mul_right Cc (from_ (consolidationQueueStart x))
    omega
  · -- Before Electra the no-crossing clause puts the fork epoch after the window.
    have before : x.fork < .pectra := Nat.lt_of_not_ge electra
    have positive : 0 < preElectraEpochs config x high := by
      simp only [preElectraEpochs, before, ↓reduceIte, driftHorizon]
      split_ifs <;> omega
    have ends : high + 2 - (getCurrentEpoch x.state).toNat + 2 ≤ preElectraEpochs config x high :=
      crossing.resolve_left (Nat.ne_of_gt positive)
    have late : ¬ config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1 := by
      simp only [preElectraEpochs, before, ↓reduceIte, driftHorizon] at ends
      split_ifs at ends <;> omega
    have starts : exitQueueStart x = (getCurrentEpoch x.state).toNat := by
      simp [exitQueueStart, electra]
    -- A positive minimum churn makes the floor of one in the count churn redundant.
    have floor : max 1 (cohortCap config A) = cohortCap config A :=
      Nat.max_eq_right (Nat.le_trans minimum (Nat.le_max_left _ _))
    have rate := Nat.mul_le_mul_left (cohortCap config A)
      (UInt64.le_iff_toNat_le.mp caps.activation)
    have empty (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat
        (max start config.ELECTRA_FORK_EPOCH.toNat) = 0 := by omega
    simp only [before, ↓reduceIte, starts, Nat.max_self, Nat.add_zero, positive, floor,
      Nat.sub_self, empty, Nat.zero_mul] at bound ⊢
    have horizon := Nat.mul_le_mul
      (show high + 2 - (getCurrentEpoch x.state).toNat ≤
        high + 2 - (getCurrentEpoch x.state).toNat + 2 - 0 by omega)
      (show cohortCap config A * preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat * cohortCap config A by
        rw [Nat.mul_comm preset.MIN_ACTIVATION_BALANCE.toNat]; exact rate)
    omega

/-! ## The count path before Electra -/

/-- The active validators at `x` are at most its active keys, since registry keys are distinct. -/
theorem activeCount_le_refCount {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) : activeCount x.state ≤ referenceCount x := by
  have within := x.state.validators.bound early
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member => by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have nodup : (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).Nodup :=
    (getActiveValidatorIndices_sorted within _).imp fun {a b} less (same : a = b) => by
      subst same; exact UInt64.lt_irrefl _ less
  rw [activeCount, referenceCount, activeKeys, Finset.card_eq_sum_ones,
    keys_sum x.state _ (shared.pubkeysDistinct genesis) inside fun _ => 1,
    ← List.toFinset_card_of_nodup nodup, Finset.card_eq_sum_ones]
  exact (Finset.sum_congr rfl fun i member => by
    simp [Array.getElem?_eq_getElem (inside i (List.mem_toFinset.mp member))]).ge

/-- Before Electra, the validators given an activation epoch in the window follow `A_t`.

They are counted at the end `z` of a run from `x`, without those already exited at `x`.

`A_t` is the count path from the active and scheduled validators at `x`, after `t` epochs. -/
theorem windowActivations_le_countPath {g x z : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x z) (early : z.fork < .pectra) :
    ((Finset.range z.state.validators.data.size).filter fun i =>
      (z.state.validators.data[i]?).any (·.activationEpoch != FAR_FUTURE_EPOCH) &&
        (x.state.validators.data[i]?).all fun w => w.activationEpoch == FAR_FUTURE_EPOCH ||
          decide (getCurrentEpoch x.state < w.exitEpoch)).card ≤
      activeCountPath config (referenceCount x + scheduledActivationCount x)
        ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) :=
  windowActivations_le tail early _ (Nat.add_le_add_right (activeCount_le_refCount shared genesis
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) (Nat.lt_trans early (by decide))))
    _) fun _ => Nat.le_refl _

/-! ## The ceiling of the funding -/

/-- The funding at a state `y` of a branch from `v` is at most its start bound plus the churn.

The funding is the funded stake plus the deposit carry, and `start` bounds it at `v`.

Each epoch from `v` to `y` adds its deposit churn, and the replay adds its funding credits.

From an Electra `x`, `v` is `x` and `start` is the funded stake plus the deposit carry at `x`. -/
theorem funding_le_ceiling {g v y : ForkedBeaconState preset}
    (shared : Run config checks g v) (tail : Run config checks v y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    {start : Nat} (funded : fundedStake v + fundingCarry v ≤ start) :
    fundedStake y + fundingCarry y ≤
      start + ((getCurrentEpoch y.state).toNat - (getCurrentEpoch v.state).toNat) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have bound := funding_run_bound (fun s => fundedStake s + fundingCarry s) (fun _ => 0)
    fundingCredit tail early high endEpoch events replayed (fun pre step early added ok => by
      simpa using funding_step_of_run (shared.append pre) genesis step early delay added ok)
  rw [show ∀ l : List (BalanceEvent preset), (l.map fun _ => 0).sum = 0 by simp,
    Nat.add_zero] at bound
  omega

/-! ## The participating balance of a rewards pass

The rewards pass at the end of epoch `t` reads the participants of epoch `t - 1`.

Each is active at `t - 1`, and its effective balance has not changed since an earlier state `u`.

So their balance is at most the effective stake at `u` of the keys active at `t - 1`.

For `t >= 1`, `u` is the output of the epoch transition that ends `t - 1`.

Its current epoch is still `t - 1`, so its funded stake counts every such key.

For `t = 0`, `u` is the start `x` of the branch.

The keys active at the epoch before `x` but not at `x` are then counted by their stake at `x`.
-/

/-- The participants of the previous epoch weigh at most the stake at `u` of its active keys.

The pass must keep the activity of `u` at that epoch, and its effective balances. -/
private theorem participating_le_reference {f h : Fork} {u : BeaconState preset f}
    {pass : BeaconState preset h} (early : f < .glamsterdam) (altair : .altair ≤ h)
    (active : ActiveKept (getPreviousEpoch pass) u pass)
    (effective : ∀ i, i < u.validators.data.size →
      effectiveAt ⟨h, pass⟩ i = effectiveAt ⟨f, u⟩ i)
    {flag : UInt64} {participating : List ValidatorIndex} {balance : Gwei}
    (flagged : getUnslashedParticipatingIndices pass altair flag (getPreviousEpoch pass) =
      .ok participating)
    (weighed : getTotalBalance pass participating = .ok balance) :
    balance.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (getActiveValidatorIndices u (getPreviousEpoch pass)).toFinset,
        effectiveAt ⟨f, u⟩ i.toNat) := by
  obtain ⟨-, -, total⟩ := getTotalBalance_ok_iff_stake.mp weighed
  rw [total]
  refine max_le_max_left _ ?_
  have same := active.getActiveValidatorIndices_eq (UInt64.le_refl _)
  -- Each participant is active at `u`, so it is inside the registry of `u`.
  have among (i : ValidatorIndex) (member : i ∈ participating.toFinset) :
      i ∈ (getActiveValidatorIndices u (getPreviousEpoch pass)).toFinset := by
    have chosen := (mem_getUnslashedParticipatingIndices flagged i
      (List.mem_toFinset.mp member)).1
    rw [same] at chosen
    exact List.mem_toFinset.mpr chosen
  calc Models.stake (fun i => balanceAt pass i.toNat) participating.toFinset
      = ∑ i ∈ participating.toFinset, effectiveAt ⟨f, u⟩ i.toNat := by
        refine Finset.sum_congr rfl fun i member => ?_
        obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (u.validators.bound early)).mp
          (List.mem_toFinset.mp (among i member))
        exact effective i.toNat (Array.getElem?_eq_some_iff.mp found).1
    _ ≤ _ := Finset.sum_le_sum_of_subset among

/-- The effective balances of the active validators of a state sum to at most its funded stake.

The keys of the registry must be distinct. -/
theorem activeEffective_le_funded (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) (unique : PubkeysDistinct x.state) :
    ∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset,
      effectiveAt x i.toNat ≤ fundedStake x := by
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member => by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (x.state.validators.bound early)).mp
      member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have bound := funding_active_le x early unique
  rw [activeKeys, keys_weight _ _ unique inside] at bound
  exact bound

/-- A run inside one epoch, then the stages of the next slot up to the rewards pass.

They keep the activity of the start `r`, its effective balances and its current epoch. -/
theorem pass_kept_of_effective {r s : ForkedBeaconState preset}
    (inner : Run config checks r s) (effective : EffectiveKept r.state s.state)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    {cached just pass : BeaconState preset s.fork} (cachedOk : processSlot s.state = .ok cached)
    (justified : EpochStage.Edge config checks .justification cached just)
    (scored : EpochStage.Edge config checks .inactivity just pass) :
    ActiveKept (activityFixedEpoch r.state) r.state pass ∧
      (∀ i, i < r.state.validators.data.size →
        effectiveAt ⟨s.fork, pass⟩ i = effectiveAt r i) ∧
      getCurrentEpoch pass = getCurrentEpoch r.state ∧
      pass.validators = s.state.validators ∧ pass.slot = s.state.slot := by
  -- The stages before the rewards keep the validators and the slot.
  have one := justified.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have two := scored.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have validators : pass.validators = s.state.validators := two.1.trans one.1
  have slot : pass.slot = s.state.slot := two.2.2.2.2.trans one.2.2.2.2
  refine ⟨(activeKept_of_chainSteps inner.chainSteps).trans fun _ _ _ => by
      simp only [isActiveAt, validators], fun i inside => ?_, ?_⟩
  · rw [← effective i inside]
    simp only [effectiveAt, validators]
  · exact ⟨by simpa only [getCurrentEpoch, slot] using same, validators, slot⟩

/-- The Electra same-epoch run supplies the effective evidence for the pass frame. -/
theorem pass_kept {r s : ForkedBeaconState preset} (inner : Run config checks r s)
    (_electra : .pectra ≤ r.fork) (early : s.fork < .glamsterdam)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    {cached just pass : BeaconState preset s.fork} (cachedOk : processSlot s.state = .ok cached)
    (justified : EpochStage.Edge config checks .justification cached just)
    (scored : EpochStage.Edge config checks .inactivity just pass) :
    ActiveKept (activityFixedEpoch r.state) r.state pass ∧
      (∀ i, i < r.state.validators.data.size →
        effectiveAt ⟨s.fork, pass⟩ i = effectiveAt r i) ∧
      getCurrentEpoch pass = getCurrentEpoch r.state := by
  obtain ⟨active, effective, epoch, _, _⟩ := pass_kept_of_effective inner
    (run_same_epoch_effective inner early same) same cachedOk justified scored
  exact ⟨active, effective, epoch⟩

/-- After an epoch boundary, the keys active at the previous epoch weigh at most the funding.

That is the funding at the last state `z` before the boundary, one epoch of churn and the credits.

The credits are the funding credits of the slot from `z`, whose epoch transition ends that epoch.

They are counted at the output `e` of that transition, whose current epoch is still the old one. -/
theorem previousStake_le_ceiling {g z w : ForkedBeaconState preset}
    (shared : Run config checks g z) (genesis : Genesis (config := config) (checks := checks) g)
    (boundary : advanceSlotAcross config checks z = .ok w)
    (crossing : getCurrentEpoch z.state < getCurrentEpoch w.state)
    (electra : .pectra ≤ z.fork) (wEarly : w.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot boundary).balanceEvents = .ok events) :
    ∑ i ∈ (getActiveValidatorIndices w.state (getPreviousEpoch w.state)).toFinset,
        effectiveAt w i.toNat ≤
      fundedStake z + fundingCarry z + config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have zEarly : z.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot boundary).chainStep.fork_le wEarly
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp boundary
  have advanceCopy := advanceOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cachedZ, cachedZOk, e, epochOk, advancedEq⟩ := advanceCopy
  have sum := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  simp only [UInt64.toNat_one] at sum
  have wSlot : w.state.slot = next := by rw [processUpgrades_slot upgrades, ← advancedEq]
  have registry : w.state.validators.data = e.validators.data := by
    rw [processUpgrades_validators_of_electra (s := ⟨z.fork, advanced⟩) electra wEarly upgrades,
      ← advancedEq]
  obtain ⟨_, _, _, _, cachedZEq⟩ := processSlot_ok cachedZOk
  -- The slot from `z` ends epoch `t - 1`, so it runs the epoch transition.
  have last : next % preset.SLOTS_PER_EPOCH = 0 := by
    by_contra inside
    have epochs := nextSlot_epoch_of_inside sum inside
    have later := UInt64.lt_iff_toNat_lt.mp crossing
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, wSlot] at later
    omega
  have epochs := nextSlot_epoch_of_boundary sum last
  simp only [epochIfLast, last, ↓reduceIte] at epochOk
  obtain ⟨_, justifiedZ, frame⟩ := processEpoch_frame epochOk
  have eSlot : e.slot = z.state.slot := by
    rw [frame.slot, (EpochStage.Edge.records (config := config) (checks := checks)
      (stage := .justification) justifiedZ ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2,
      cachedZEq]
  -- The previous epoch of `w` is the current epoch of `e`, which has the registry of `w`.
  have previous : getPreviousEpoch w.state = getCurrentEpoch e := by
    apply UInt64.toNat_inj.mp
    have wPrevious := getPreviousEpoch_toNat w.state
    have wValue := getCurrentEpoch_toNat w.state
    have eValue := getCurrentEpoch_toNat e
    rw [wSlot] at wValue
    rw [eSlot] at eValue
    omega
  have sameKeys : getActiveValidatorIndices w.state (getCurrentEpoch e) =
      getActiveValidatorIndices e (getCurrentEpoch e) :=
    (show ActiveKept (getCurrentEpoch e) e w.state from fun _ _ _ => by
      simp only [isActiveAt, registry]).getActiveValidatorIndices_eq (UInt64.le_refl _)
  have unique : PubkeysDistinct e := by
    have distinct := (shared.snoc (.slot boundary)).pubkeysDistinct genesis
    unfold PubkeysDistinct validatorKeys at distinct ⊢
    rwa [registry] at distinct
  have weights : ∀ i, effectiveAt w i = effectiveAt ⟨z.fork, e⟩ i := fun i => by
    simp only [effectiveAt, registry]
  rw [previous, sameKeys]
  simp only [weights]
  have active : ∑ i ∈ (getActiveValidatorIndices e (getCurrentEpoch e)).toFinset,
      effectiveAt ⟨z.fork, e⟩ i.toNat ≤ fundedStake ⟨z.fork, e⟩ :=
    activeEffective_le_funded ⟨z.fork, e⟩ zEarly unique
  -- The epoch transition raises the funding by one epoch of churn and its credits.
  have holds := (run_justified_separated shared genesis).1
  obtain ⟨middle, -, epochEvents, epochReplay, -⟩ :=
    epochBalanceReplay_result cachedZ e zEarly epochOk
  have funded := funding_epoch zEarly delay
    ((frame_processSlot cachedZOk).balancesMatch holds.balancesMatch)
    ((frame_processSlot cachedZOk).exitsOrdered holds.exitsOrdered)
    (by rw [cachedZEq]; exact shared.activationExitOrder genesis)
    (by rw [cachedZEq]; exact fun witness =>
      shared.pendingConsolidation_invariant genesis zEarly witness (by omega))
    epochOk epochEvents epochReplay
  obtain ⟨crossings, crossingOk, _⟩ := upgradeBalanceReplay_bounded upgrades
  have split := Step.balanceEvents_epoch_slot boundary cachedZOk nextOk last epochReplay
    advanceOk crossingOk
  obtain rfl := Except.ok.inj (replayed.symm.trans split)
  have startFunded : fundedStake ⟨z.fork, cachedZ⟩ = fundedStake z := by rw [cachedZEq]; rfl
  have startCarry : fundingCarry ⟨z.fork, cachedZ⟩ = fundingCarry z := by rw [cachedZEq]; rfl
  rw [startFunded, startCarry] at funded
  rw [List.map_append, List.sum_append]
  omega

/-- At the rewards pass after a run inside one epoch, each flag's participants weigh at most a sum.

It is the effective stake at the start `r` of the run of the keys active at its previous epoch.

The pass follows the stages of the next slot from `s` before the rewards. -/
theorem participating_le_previous {r s : ForkedBeaconState preset}
    (inner : Run config checks r s) (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    (electra : .pectra ≤ r.fork) (early : s.fork < .glamsterdam)
    {cached just pass : BeaconState preset s.fork} (cachedOk : processSlot s.state = .ok cached)
    (justified : EpochStage.Edge config checks .justification cached just)
    (scored : EpochStage.Edge config checks .inactivity just pass) (altair : .altair ≤ s.fork)
    {flag : UInt64} {participating : List ValidatorIndex} {balance : Gwei}
    (flagged : getUnslashedParticipatingIndices pass altair flag (getPreviousEpoch pass) =
      .ok participating)
    (weighed : getTotalBalance pass participating = .ok balance) :
    balance.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
        effectiveAt r i.toNat) := by
  have rEarly : r.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  obtain ⟨activeKept, effectiveKept, passEpoch⟩ := pass_kept inner electra early same cachedOk
    justified scored
  have previous : getPreviousEpoch pass = getPreviousEpoch r.state := by
    apply UInt64.toNat_inj.mp
    rw [getPreviousEpoch_toNat, getPreviousEpoch_toNat, passEpoch]
  have kept : ActiveKept (getPreviousEpoch pass) r.state pass :=
    activeKept.mono (UInt64.le_trans (passEpoch ▸ getPreviousEpoch_le pass)
      (getCurrentEpoch_le_activityFixedEpoch _))
  have bound := participating_le_reference rEarly altair kept effectiveKept flagged weighed
  rw [previous] at bound
  exact bound

/-- At the start `x` of a branch, the keys active at the previous epoch weigh at most a sum.

It is the funded stake of `x` and the stake at `x` of the keys active only at the epoch before.

The keys of the registry must be distinct. -/
theorem previousStake_le_start (x : ForkedBeaconState preset)
    (xEarly : x.fork < .glamsterdam) (unique : PubkeysDistinct x.state) :
    ∑ i ∈ (getActiveValidatorIndices x.state (getPreviousEpoch x.state)).toFinset,
      effectiveAt x i.toNat ≤ fundedStake x + previousOnlyStake x := by
  have within := x.state.validators.bound xEarly
  -- Split the keys of the previous epoch by whether they are still active at `x`.
  set current := (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset
  set before := (getActiveValidatorIndices x.state (getPreviousEpoch x.state)).toFinset
  rw [← Finset.sum_filter_add_sum_filter_not before (· ∈ current)]
  have stillActive : ∑ i ∈ before.filter (· ∈ current), effectiveAt x i.toNat ≤
      ∑ i ∈ current, effectiveAt x i.toNat :=
    Finset.sum_le_sum_of_subset fun i member => (Finset.mem_filter.mp member).2
  have funded : ∑ i ∈ current, effectiveAt x i.toNat ≤ fundedStake x :=
    activeEffective_le_funded x xEarly unique
  -- The others are the keys active only at the previous epoch.
  have leaving : ∑ i ∈ before.filter (· ∉ current), effectiveAt x i.toNat ≤
      previousOnlyStake x := by
    let weight (v : Validator) : Nat :=
      if isActiveValidator v (getPreviousEpoch x.state) &&
          !isActiveValidator v (getCurrentEpoch x.state) then v.effectiveBalance.toNat else 0
    have sum := funding_sum_zipIdx x.state.validators.data.toList fun v _ => weight v
    have shape : (x.state.validators.data.toList.zipIdx.map fun (v, _) => weight v) =
        x.state.validators.data.toList.map weight := by
      have first := congrArg (List.map weight)
        (List.zipIdx_map_fst 0 x.state.validators.data.toList)
      rw [List.map_map] at first
      rw [← first]
      exact List.map_congr_left fun ⟨_, _⟩ _ => rfl
    rw [shape] at sum
    unfold previousOnlyStake
    change _ ≤ (x.state.validators.data.toList.map weight).sum
    rw [sum]
    simp only [Array.length_toList, Array.getElem?_toList]
    apply Finset.sum_le_sum_of_injOn (fun i => i.toNat)
    · intro i _ j _ eq
      exact UInt64.toNat_inj.mp eq
    · intro i member
      obtain ⟨j, chosen, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp
        (List.mem_toFinset.mp (Finset.mem_filter.mp chosen).1)
      exact Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1
    · intro i member
      obtain ⟨inPrevious, notCurrent⟩ := Finset.mem_filter.mp member
      obtain ⟨v, found, activePrevious⟩ := (mem_getActiveValidatorIndices within).mp
        (List.mem_toFinset.mp inPrevious)
      have inactive : isActiveValidator v (getCurrentEpoch x.state) = false := by
        by_contra activeNow
        exact notCurrent (List.mem_toFinset.mpr ((mem_getActiveValidatorIndices within).mpr
          ⟨v, found, by simpa using activeNow⟩))
      simp [weight, found, effectiveAt, activePrevious, inactive]
    · intro _ _ _
      exact Nat.zero_le _
  omega

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
