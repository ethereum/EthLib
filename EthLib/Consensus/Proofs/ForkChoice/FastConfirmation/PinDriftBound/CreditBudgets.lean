module

import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import Mathlib.Data.Nat.ModEq
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
import Mathlib.Algebra.Order.Floor.Div
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.BalanceBounds

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

namespace Internal

/-- The low bound of an existing key is covered by its exit charge and its sync debits. -/
private theorem existing_low_le_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    -- The key is activated at the finalized state, charged on the run, and exits by C.
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    (pinTerms config pulled anc fin).lowEB v.toNat ≤
      -- The charge is its effective balance at the exit call.
      Internal.exitQ tailC v.toNat + (events.map (Internal.syncDebit v.toNat)).sum := by
  -- The bound reads the floor of its balance from the finalized state.
  --
  -- The lower bound accounts separately for penalties and due partial withdrawals.
  --
  -- The hysteresis is covered by the activation balance.
  have bound := Internal.existing_low_explicit h fromFin tailC replayed v epochLe val initial
    charged
  have drop : (pinTerms config pulled anc fin).drop v.toNat =
      ((pinTerms config pulled anc fin).leakAt
          (balanceAt fin v.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              (withdrawalMaxEffectiveBalance preset fork val).toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [Internal.drop_of_found config pulled anc fin initial, Internal.base0_of_found config pulled
      anc fin initial]
    rfl
  rw [Internal.lowEB_unfold, drop]
  exact bound

/-- The new-key floor equals the minimum departure charge plus the sync-debit allowance. -/
private theorem exitFloor_add_slack (h : Setting config checks g split fin pulled anc counted V) :
    (pinTerms config pulled anc fin).exitFloor + (pinTerms config pulled anc fin).newKeySlack =
      (pinTerms config pulled anc fin).newKeyFloor := by
  have newKey := h.facts.newKey fork
  have size := h.facts.incrementSize
  have floorEq : (pinTerms config pulled anc fin).newKeyFloor =
      2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat := rfl
  have exitEq : (pinTerms config pulled anc fin).exitFloor =
      max 1 (min (config.EJECTION_BALANCE.toNat - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
        (pinTerms config pulled anc fin).newKeyFloor) := rfl
  have slack : (pinTerms config pulled anc fin).newKeySlack =
      (pinTerms config pulled anc fin).newKeyFloor -
        (pinTerms config pulled anc fin).exitFloor := rfl
  omega

/-- A key that is not yet activated at the finalized state and has a small charge loses seats. -/
private theorem pending_key_claim (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    -- A charge below the minimum implies sync debits above the allowance for a new key.
    (small : Internal.exitQ tailC v.toNat < (pinTerms config pulled anc fin).exitFloor)
    -- The key is missing at the finalized state, or its activation there is unassigned.
    (fresh : fin.validators.data[v.toNat]? = none ∨
      ∃ w, fin.validators.data[v.toNat]? = some w ∧ w.activationEpoch = FAR_FUTURE_EPOCH) :
    (pinTerms config pulled anc fin).newKeySlack < (events.map (Internal.syncDebit v.toNat)).sum :=
      by
  -- The key activates on the run from the finalized state.
  --
  -- So it keeps at least the new-key balance floor less its sync debits.
  --
  -- It has no partial withdrawals queued, since a request needs an active key.
  --
  -- The charge splits C's run at the step that exits the key.
  --
  -- The key is activated there, by `charge_activated`.
  --
  -- The key is active at that state, so the floor of a new key reads its effective balance.
  --
  -- That balance is the charge, and the floor adds the key's sync debits and partial payments.
  --
  -- The partial payments are none, since no queued entry names the key at the finalized state.
  --
  -- An entry queued later is not due in the window.
  classical
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨c, cMember, cIndex⟩ := charged
  obtain ⟨a, b, pre, step, post, split', vv, w, found, foundB, unset, set, activated, amount,
    epoch⟩ := Internal.charge_activated (x := ⟨fork, split⟩) electra tailC c
    (tailC.departure_charge_site c cMember)
  rw [cIndex] at found foundB
  -- the charge counts, so `exitQ` is its amount
  have exitQEq : Internal.exitQ tailC v.toNat = c.amount := by
    rcases Internal.exitQ_cases tailC v.toNat with ⟨none, -⟩ | ⟨d, dMember, dIndex, -, dQ⟩
    · exact absurd (epochLe c cMember cIndex) (none c cMember cIndex)
    · rw [dQ, Internal.charge_unique tailC dMember cMember (dIndex.trans cIndex.symm)]
  -- the run from the finalized state to the exit step, and its events, a prefix of the replay
  have shape : fromFin.append ((pre.snoc step).append post) =
      (fromFin.append pre).append ((Run.nil.snoc step).append post) := by
    rw [pre.snoc_append_eq, Run.append_assoc]
  rw [← split', shape] at replayed
  obtain ⟨prior, priorOk, isPrefix⟩ := Run.balanceEvents_prefix (fromFin.append pre)
    ((Run.nil.snoc step).append post) (getCurrentEpoch pulled).toNat events replayed
  have aEpoch : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch counted).toNat :=
    UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
  have aInside : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := h.near
    omega
  have aEarly : a.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
      h.early
  have finite : (getCurrentEpoch a.state).toNat < FAR_FUTURE_EPOCH.toNat := by
    have ne := getCurrentEpoch_ne_farFuture h.twoSlots a.state
    have := (getCurrentEpoch a.state).toNat_lt
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have : (getCurrentEpoch a.state).toNat ≠ FAR_FUTURE_EPOCH.toNat := fun eq =>
      ne (UInt64.toNat_inj.mp eq)
    omega
  have active : isActiveAt a.state (getCurrentEpoch a.state) v.toNat = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨vv, found, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨activated, by rw [unset]; exact UInt64.lt_iff_toNat_lt.mpr finite⟩
  have pending : ∀ u, fin.validators.data[v.toNat]? = some u →
      (getCurrentEpoch (⟨fork, fin⟩ : ForkedBeaconState preset).state).toNat + 1 <
        u.activationEpoch.toNat := by
    intro u foundFin
    rcases fresh with none | ⟨u', foundFin', far⟩
    · rw [none] at foundFin
      cases foundFin
    · obtain rfl := Option.some.inj (foundFin.symm.trans foundFin')
      rw [far]
      exact getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
  have floor := Internal.Run.new_key_effective_floor toFin h.genesis h.parameters h.caps h.aligned
    h.twoSlots electra h.fulu (getCurrentEpoch pulled).toNat h.guard (fromFin.append pre) aEarly
    aInside h.window (Internal.Setting.delay h) h.bands h.facts v.toNat pending active priorOk
  -- no queued partial withdrawal names the key at the finalized state, which has no activation
  have genesisPartials : Internal.AssignedPartials g.state := by
    obtain ⟨_, _, _, initialized⟩ := h.genesis
    have before := (initializeBeaconStateFromEth1_ok initialized).1
    intro fork
    exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) fork)).elim
  have finPartials : Internal.AssignedPartials fin :=
    (Internal.CapStep.run toFin h.caps.activation h.caps.compounding).2.1 h.early genesisPartials
  have noEntry : ((((fin.pendingPartialWithdrawals electra).data.toList.filter
      fun entry => decide (entry.validatorIndex = v)).filter
        (fun entry => entry.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
          (·.amount.toNat)).sum = 0 := by
    have none : (fin.pendingPartialWithdrawals electra).data.toList.filter
        (fun entry => decide (entry.validatorIndex = v)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro entry member same
      obtain ⟨u, foundU, assignedU⟩ := finPartials electra entry member
      rw [of_decide_eq_true same] at foundU
      rcases fresh with absent | ⟨u', foundU', far⟩
      · rw [absent] at foundU
        cases foundU
      · obtain rfl := Option.some.inj (foundU.symm.trans foundU')
        exact assignedU far
    rw [none]
    rfl
  have debits := Internal.Run.partialDebit_le (fromFin.append pre) electra aEarly
    (getCurrentEpoch pulled).toNat ((getCurrentEpoch pulled).toNat + 1) aInside
    (Internal.window_short h) v priorOk
  have toUInt : v.toNat.toUInt64 = v := by simp
  have partials : (prior.map (DirectSafety.Apriori.Internal.floorPartialDebit
      v.toNat.toUInt64)).sum = 0 := by
    rw [toUInt]
    exact Nat.le_zero.mp (noEntry ▸ debits)
  have order := exitFloor_add_slack h
  have floorEq : (pinTerms config pulled anc fin).newKeyFloor =
      2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat := rfl
  rw [Internal.parameters_of_fusaka h.fulu h.early] at floorEq
  have effective : effectiveAt a v.toNat = c.amount := by
    simp only [effectiveAt, found, Option.map_some, Option.getD_some]
    exact amount.symm
  have prefixSum : (prior.map (Internal.syncDebit v.toNat)).sum ≤ (events.map (Internal.syncDebit
    v.toNat)).sum := by
    obtain ⟨rest, rfl⟩ := isPrefix
    simp only [List.map_append, List.sum_append]
    omega
  omega

/-- A previous-only key not exiting at the call, with a small charge, is low or loses seats. -/
private theorem small_charge_claim (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    -- The debits are those of the replay of the run from the finalized state to C's state.
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (activatedBy : ∀ c, counted.validators.data[v.toNat]? = some c →
      c.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    -- A small charge is below the minimum used to count departures.
    (small : Internal.exitQ tailC v.toNat < (pinTerms config pulled anc fin).exitFloor) :
    -- The key is then a low key, or its sync debits from finality exceed the new-key allowance.
    (pinTerms config pulled anc fin).lowB v.toNat = true ∨
      (pinTerms config pulled anc fin).newKeySlack < (events.map (Internal.syncDebit v.toNat)).sum
        := by
  -- A key that is not activated at the finalized state can lose committee seats.
  --
  -- For an activated key, R reads the assigned activation and an epoch before withdrawal.
  --
  -- Its departure charge and debits cover the lower bound.
  classical
  by_cases fresh : fin.validators.data[v.toNat]? = none ∨
      ∃ w, fin.validators.data[v.toNat]? = some w ∧ w.activationEpoch = FAR_FUTURE_EPOCH
  · exact .inr (pending_key_claim h fromFin tailC replayed v epochLe charged small fresh)
  obtain ⟨absent, notFar⟩ := not_or.mp fresh
  obtain ⟨w, found⟩ := Option.ne_none_iff_exists'.mp absent
  have activated : w.activationEpoch ≠ FAR_FUTURE_EPOCH := fun far => notFar ⟨w, found, far⟩
  by_cases rich : (pinTerms config pulled anc fin).newKeySlack <
      (events.map (Internal.syncDebit v.toNat)).sum
  · exact .inr rich
  refine .inl (Internal.lowB_intro config pulled anc fin
    (Internal.activated_key_at_pulled h tailC v activatedBy charged found activated) ?_)
  have floor := existing_low_le_charge h fromFin tailC replayed v epochLe w found charged
  have order := exitFloor_add_slack h
  omega

/-- The total active balance at each step of a run from the finalized state is bounded.

It is at most three halves of the pulled total.

The run ends at most one epoch after the pulled epoch.

The guard bounds the active balance at each step. -/
theorem step_band_of_guard (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (r : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {pulledTotal : Gwei} (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      r.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat := by
  intro u w step member T read
  obtain ⟨pre, post, _, _, _⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have wEarly : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have wEpoch : (getCurrentEpoch w.state).toNat ≤ (getCurrentEpoch e).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  exact (total_band_of_setting h (pre.snoc step) wEarly (by omega) read pulledOk).2

/-- The sync debits of any keys over a run from the finalized block fit the window's envelope.

The run ends within one epoch of R's, and its events are read at R's epoch.

The seats of the window debit at most its slots' envelopes, one for each epoch to the run's end. -/
theorem syncDebits_window_le (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : run.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, (events.map (Internal.syncDebit v.toNat)).sum ≤
      ((getCurrentEpoch e).toNat + 1 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      run.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat :=
    Internal.step_band_of_guard h run within pulledOk
  have debits := (Internal.Run.syncDebits_le run h.fulu h.early (getCurrentEpoch pulled).toNat
    replayed pulledTotal.toNat band (S.image fun v : ValidatorIndex => v.toNat)).1
  rw [Finset.sum_image fun _ _ _ _ same => UInt64.toNat_inj.mp same] at debits
  rwa [pulledOk]

/-- The seat count bounds how many keys can exceed the new-key sync-debit allowance. -/
private theorem card_seat_keys_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (B : Finset ValidatorIndex)
    (seats : ∀ v ∈ B, (pinTerms config pulled anc fin).newKeySlack <
      (events.map (Internal.syncDebit v.toNat)).sum) :
    B.card ≤ (pinTerms config pulled anc fin).newKeySeats := by
  -- Take the sync debits of any keys over the run from the finalized state to C's state.
  --
  -- They fit one envelope.
  --
  -- The envelope is for each seat and slot of the window.
  --
  -- A key over the slack has at least one more than the slack.
  --
  -- So the keys number at most the debits over the slack.
  classical
  have debits := Internal.syncDebits_window_le h (fromFin.append tailC) h.near replayed B
  have each : B.card * ((pinTerms config pulled anc fin).newKeySlack + 1) ≤
      ∑ v ∈ B, (events.map (Internal.syncDebit v.toNat)).sum := by
    have := Finset.card_nsmul_le_sum B
      (fun v : ValidatorIndex => (events.map (Internal.syncDebit v.toNat)).sum)
      ((pinTerms config pulled anc fin).newKeySlack + 1) fun v member => seats v member
    simpa [smul_eq_mul] using this
  have seatsEq : (pinTerms config pulled anc fin).newKeySeats =
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat /
            max 1 (pinTerms config pulled anc fin).newKeySlack := rfl
  rw [seatsEq, Nat.le_div_iff_mul_le (lt_max_of_lt_left Nat.one_pos)]
  have epochs : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by have := h.near; omega
  have window := Nat.mul_le_mul_right
    (PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat)
    (Nat.mul_le_mul_right preset.SYNC_COMMITTEE_SIZE.toNat
      (Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochs))
  have unit : max 1 (pinTerms config pulled anc fin).newKeySlack ≤
      (pinTerms config pulled anc fin).newKeySlack + 1 := by omega
  calc B.card * max 1 (pinTerms config pulled anc fin).newKeySlack
      ≤ B.card * ((pinTerms config pulled anc fin).newKeySlack + 1) := Nat.mul_le_mul_left _ unit
    _ ≤ _ := each
    _ ≤ _ := debits
    _ ≤ _ := by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using window

/-- The keys that C's branch charges are few, if each is activated by R's epoch and exits by C. -/
theorem charged_count_of (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (S : Finset ValidatorIndex)
    -- A key is charged if the run has a departure charge at its position.
    (keys : ∀ v ∈ S, (∀ c, counted.validators.data[v.toNat]? = some c →
        c.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat) ∧
      (∀ c ∈ tailC.departureCharges, c.index = v.toNat →
        c.epoch ≤ (getCurrentEpoch counted).toNat) ∧
      ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    -- The queue count bounds the number of charged keys.
    --
    -- Those are the keys with a large charge, the low keys and the keys that lose seats.
    S.card ≤ (pinTerms config pulled anc fin).queueKeys := by
  -- Large charges spend at least the minimum departure charge per key.
  --
  -- Small charges can be counted without reading R's exit flag.
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨events, replayed⟩ := (fromFin.append tailC).balanceEvents_ok h.early
    (getCurrentEpoch pulled).toNat
  have big := Internal.card_big_charges_le h tailC S
  set small := S.filter fun v => ¬ (pinTerms config pulled anc fin).exitFloor ≤
    Internal.exitQ tailC v.toNat with hSmall
  have claim : ∀ v ∈ small, (pinTerms config pulled anc fin).lowB v.toNat = true ∨
      (pinTerms config pulled anc fin).newKeySlack < (events.map (Internal.syncDebit v.toNat)).sum
        := by
    intro v member
    obtain ⟨inS, notBig⟩ := Finset.mem_filter.mp member
    obtain ⟨activatedBy, epochLe, charged⟩ := keys v inS
    exact small_charge_claim h fromFin tailC replayed v activatedBy epochLe charged
      (Nat.lt_of_not_ge notBig)
  have seats := card_seat_keys_le h fromFin tailC replayed
    (small.filter fun v => ¬ (pinTerms config pulled anc fin).lowB v.toNat = true) (by
      intro v member
      obtain ⟨inSmall, notLow⟩ := Finset.mem_filter.mp member
      exact (claim v inSmall).resolve_left notLow)
  have lows : (small.filter fun v => (pinTerms config pulled anc fin).lowB v.toNat = true).card ≤
      (pinTerms config pulled anc fin).lowKeys := by
    rw [Internal.lowKeys_eq]
    have count := voters_sum_le (voters := small.filter fun v =>
        (pinTerms config pulled anc fin).lowB v.toNat = true)
      (positions := (pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).lowB i = true) (fun _ => 1) (fun v member => by
      have low := (Finset.mem_filter.mp member).2
      obtain ⟨w, found⟩ := Internal.lowB_found config pulled anc fin low
      exact Internal.mem_positions_filter config pulled anc fin found low)
    simpa using count
  have coverSmall : small ⊆
      (small.filter fun v => (pinTerms config pulled anc fin).lowB v.toNat = true) ∪
        (small.filter fun v => ¬ (pinTerms config pulled anc fin).lowB v.toNat = true) := by
    intro v member
    by_cases low : (pinTerms config pulled anc fin).lowB v.toNat = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨member, low⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨member, low⟩)
  have coverS : S ⊆ (S.filter fun v => (pinTerms config pulled anc fin).exitFloor ≤
      Internal.exitQ tailC v.toNat) ∪ small := by
    intro v member
    by_cases large : (pinTerms config pulled anc fin).exitFloor ≤ Internal.exitQ tailC v.toNat
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨member, large⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨member, large⟩)
  have splitS := (Finset.card_le_card coverS).trans (Finset.card_union_le _ _)
  have splitSmall := (Finset.card_le_card coverSmall).trans (Finset.card_union_le _ _)
  rw [Internal.queueKeys_unfold]
  omega

/-- The previous-only keys that C's branch charges are few.

Each is activated by R's epoch, since it is active in the epoch before C's. -/
private theorem charged_count (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    ((previousOnlyKeys counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
        v.toNat).card ≤
      (pinTerms config pulled anc fin).queueKeys := by
  refine Internal.charged_count_of h tailC _ fun v member => ?_
  obtain ⟨inK5, charged⟩ := Finset.mem_filter.mp member
  refine ⟨fun c foundC => ?_, charge_epoch_le_of_previousOnlyKeys h tailC inK5, charged⟩
  obtain ⟨u, foundU, activeBefore, -⟩ := previousOnlyKeys_previous_only h inK5
  obtain rfl : u = c := Option.some.inj (foundU.symm.trans foundC)
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeBefore
  have low := UInt64.le_iff_toNat_le.mp activeBefore.1
  have previous := getPreviousEpoch_toNat counted
  have near := h.near
  omega

/-- Each credited previous-only key counts at weight three and needs two extra rounding bands.

The bound separates scheduled exits seen by R from exits that start on C's branch. -/
theorem budget_exitingBands (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    2 * (∑ v ∈ (previousOnlyKeys counted V), Internal.bandC tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).exitingBands :=
  Internal.two_bands_le_exitingBands config pulled anc fin counted V tailC highC
    (fun _ member flag _ => previousOnlyKeys_charged h tailC member flag) (charged_count h tailC)

/-- The queue budget covers the rise after departure charges on C's branch.

It covers keys counted in C's quorum but inactive at C and outside the voter set. -/
theorem budget_queueRise (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    3 * (∑ v ∈ (previousOnlyKeys counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        Internal.riseQ tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).queueRise := by
  classical
  rw [Internal.queueRise_unfold]
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  have later := UInt64.le_iff_toNat_le.mp h.later
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · simp only [tight, ↓reduceIte]
    have tightLe : (pinTerms config pulled anc fin).depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat :=
      of_decide_eq_true tight
    have depthEq : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    rw [depthEq] at tightLe
    have none : ∀ v ∈ (previousOnlyKeys counted V).filter
        (fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat),
        Internal.riseQ tailC highC v.toNat = 0 := by
      intro v member
      apply Internal.riseQ_eq_zero
      intro c charged same
      have inside := charge_epoch_le_of_previousOnlyKeys h tailC (Finset.mem_filter.mp member).1 c
        charged same
      have far : (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
        DirectSafety.Run.departureCharges_epoch_ge_start tailC electra h.early c charged
      omega
    rw [Finset.sum_eq_zero none]
    simp
  · simp only [tight, Bool.false_eq_true, ↓reduceIte]
    have sumEq := Finset.sum_filter_ne_zero
      (s := (previousOnlyKeys counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
          v.toNat)
      (f := fun v : ValidatorIndex => Internal.riseQ tailC highC v.toNat)
    have each := Finset.sum_le_card_nsmul
      (((previousOnlyKeys counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
        v.toNat).filter
          fun v => Internal.riseQ tailC highC v.toNat ≠ 0)
      (fun v : ValidatorIndex => Internal.riseQ tailC highC v.toNat)
      (preset.upwardBand + (pinTerms config pulled anc fin).depth *
        (pinTerms config pulled anc fin).gainRateMax)
      fun v _ => Internal.riseQ_le h tailC highC v.toNat
    have count := (Finset.card_le_card (Finset.filter_subset
      (fun v : ValidatorIndex => Internal.riseQ tailC highC v.toNat ≠ 0)
      ((previousOnlyKeys counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
        v.toNat))).trans
      (charged_count h tailC)
    rw [smul_eq_mul] at each
    rw [← sumEq]
    calc _ ≤ 3 * ((((previousOnlyKeys counted V).filter fun v =>
            ∃ c ∈ tailC.departureCharges, c.index = v.toNat).filter
          fun v => Internal.riseQ tailC highC v.toNat ≠ 0).card *
        (preset.upwardBand + (pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).gainRateMax)) := Nat.mul_le_mul_left _ each
      _ ≤ _ := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ count)

/-- The scheduled-exit budget covers the rise of previous-only keys whose exit R can see.

The sum over previous-only keys takes only those without a departure charge on C's run. -/
theorem budget_exitingRise (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (∑ v ∈ (previousOnlyKeys counted V) with ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat =
        true,
        (pinTerms config pulled anc fin).rise v.toNat) ≤
      (pinTerms config pulled anc fin).exitingRise := by
  classical
  have exitingRise : (pinTerms config pulled anc fin).exitingRise =
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).exitingB i = true,
        (pinTerms config pulled anc fin).rise i := by
    simp only [pinTerms, decide_eq_true_eq]
  have apart : Disjoint
      ((previousOnlyKeys counted V).filter fun v => ¬ ∃ c ∈ tailC.departureCharges, c.index =
          v.toNat)
      ((joinedKeys pulled counted).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = true) := by
    refine Finset.disjoint_left.mpr fun v first second => ?_
    have active := (Finset.mem_filter.mp (Finset.mem_filter.mp second).1).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp first).1).2.1 active
  rw [← Finset.sum_union apart, exitingRise]
  refine voters_sum_le (pinTerms config pulled anc fin).rise fun v selected => ?_
  have exiting : (pinTerms config pulled anc fin).exitingB v.toNat = true := by
    rcases Finset.mem_union.mp selected with chosen | chosen
    · exact previousOnlyKeys_exiting_of_not_charged h tailC (Finset.mem_filter.mp chosen).1
        (Finset.mem_filter.mp chosen).2
    · exact (Finset.mem_filter.mp chosen).2
  have found : ∃ w, pulled.validators.data[v.toNat]? = some w := by
    obtain ⟨-, -, read⟩ := (by simpa only [pinTerms, decide_eq_true_eq] using exiting :
      _ ∧ _ ∧ ((pulled.validators.data[v.toNat]?).map fun w =>
        decide (w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).getD false = true)
    exact Internal.validator_of_flag (.inr read)
  obtain ⟨w, found⟩ := found
  exact Internal.mem_positions_filter config pulled anc fin found exiting

/-- The credits of a set of keys in one event are at most the event's credit limit. -/
theorem sum_keyCredit_le_creditLimit (S : Finset ValidatorIndex) (e : BalanceEvent preset)
    (bounded : e.credits ≤ e.creditLimit) : ∑ v ∈ S, Internal.keyCredit v.toNat e ≤ e.creditLimit :=
      by
  refine Nat.le_trans ?_ bounded
  unfold Internal.keyCredit
  have inj : Set.InjOn (fun v : ValidatorIndex => v.toNat) S := fun a _ b _ same =>
    UInt64.toNat_inj.mp same
  rw [← Finset.sum_image (f := fun i => actualBalanceAt e.after i - actualBalanceAt e.before i)
    inj]
  exact Internal.keys_credits_le _ e

/-- The block credits of one epoch, against the pin's rate on the pulled total.

The rewards of the epoch are at most `54 / 448` of the rate on each active set.

Each active set is at most the total, which is within three halves of the pulled total. -/
private theorem propN_arith {inc c pi pq a b total T : ℕ} (incPos : 0 < inc)
    (credits : c * 448 ≤ 54 * pi * (a + b)) (prev : pi * a ≤ pq * (total / inc))
    (curr : pi * b ≤ pq * (total / inc)) (band : 2 * total ≤ 3 * T) :
    c * 896 ≤ 324 * (pq * (T / inc)) + 216 * pq := by
  have h1 := Nat.div_mul_le_self total inc
  have h2 := Nat.lt_mul_div_succ T incPos
  have K2 : 2 * (total / inc) ≤ 3 * (T / inc) + 2 := by
    have : 2 * (total / inc) * inc < (3 * (T / inc) + 3) * inc := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  have e : c * 448 ≤ 54 * (2 * (pq * (total / inc))) := by
    calc c * 448 ≤ 54 * pi * (a + b) := credits
      _ = 54 * (pi * a + pi * b) := by ring
      _ ≤ _ := by omega
  calc c * 896 = 2 * (c * 448) := by ring
    _ ≤ 2 * (54 * (2 * (pq * (total / inc)))) := by omega
    _ = 108 * (pq * (2 * (total / inc))) := by ring
    _ ≤ 108 * (pq * (3 * (T / inc) + 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ K2)
    _ = 324 * (pq * (T / inc)) + 216 * pq := by ring

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The reward rate and the total at the start of a run in `fin`'s epoch or later are bounded.

The state is reached from `fin`, or it precedes `fin` in its epoch and reads what `fin` reads. -/
private theorem start_rates (h : Setting config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork}
    (within : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, m⟩) ∨
      ∃ _ : Run config checks ⟨fork, m⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch m)
    {pq : Gwei} (pqOk : getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq)
    {T : Gwei} (pulledOk : getTotalActiveBalance pulled = .ok T)
    {total perIncrement : Gwei} (totalOk : getTotalActiveBalance m = .ok total)
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    perIncrement.toNat * ((∑ i ∈ (getActiveValidatorIndices m (getPreviousEpoch m)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      pq.toNat * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
    perIncrement.toNat * ((∑ i ∈ (getActiveValidatorIndices m (getCurrentEpoch m)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      pq.toNat * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
    2 * total.toNat ≤ 3 * T.toNat := by
  rcases link with toMne | ⟨back, same⟩
  · obtain ⟨toM⟩ := toMne
    exact ⟨Internal.rate_of_guard h toM within (Or.inl rfl) pqOk total perIncrement totalOk per,
      Internal.rate_of_guard h toM within (Or.inr rfl) pqOk total perIncrement totalOk per,
      (total_band_of_setting h toM h.early within totalOk pulledOk).2⟩
  · have current := activeStake_eq_of_same_epoch back h.early same (getCurrentEpoch m)
      (UInt64.le_refl _)
    have previous := activeStake_eq_of_same_epoch back h.early same (getPreviousEpoch m)
      (getPreviousEpoch_le _)
    have previousSame : getPreviousEpoch fin = getPreviousEpoch m := by
      simp only [getPreviousEpoch, same]
    obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
    change total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (getActiveValidatorIndices m (getCurrentEpoch m)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) at value
    obtain ⟨atFin, atFinOk, atFinValue⟩ := totalActive_exists (s := fin) h.early (by
      rw [same, current]
      exact Nat.lt_of_le_of_lt (by rw [value]; exact le_max_right _ _) total.toNat_lt)
    simp only [same] at atFinValue
    have amounts : atFin = total := UInt64.toNat_inj.mp (by rw [atFinValue, current, value])
    subst amounts
    have inside : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
      rw [same]
      exact within
    have first := Internal.rate_of_guard h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩)
      inside
      (Or.inl rfl) pqOk atFin perIncrement atFinOk per
    have second := Internal.rate_of_guard h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩)
      inside
      (Or.inr rfl) pqOk atFin perIncrement atFinOk per
    refine ⟨?_, ?_, (total_band_of_setting h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩)
      h.early inside atFinOk pulledOk).2⟩
    · rw [previousSame, previous] at first
      exact first
    · rw [same, current] at second
      exact second

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The proposer credits of a set of keys over a run inside one epoch of C's branch are bounded.

The bound is the pin's rate on the pulled total, with `896` times the credits on the left.

The block steps of the run credit at most `54 / 448` of the rate on the active increments.

A run with no reads of the rate credits nothing. -/
private theorem propN_epoch_le (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) (S : Finset ValidatorIndex) {T : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok T) {m : BeaconState preset fork}
    (toM : Run config checks g ⟨fork, m⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, m⟩) ∨
      ∃ _ : Run config checks ⟨fork, m⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch m)
    {u : ForkedBeaconState preset}
    (inner : Run config checks ⟨fork, m⟩ u) (rest : Run config checks u ⟨fork, counted⟩)
    (same : getCurrentEpoch u.state = getCurrentEpoch m) :
    (∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      inner)) * 896 ≤
      324 * ((pinTerms config pulled anc fin).perIncrement *
        (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have uFork : u.fork = fork := Internal.fork_eq_of_run inner rest (Nat.le_refl _)
  have uEarly : u.fork < .glamsterdam := by rw [uFork]; exact h.early
  have within : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (inner.append rest).chainSteps)) h.near
  obtain ⟨events, replayed, bounded⟩ :=
    Run.balanceEvents_bounded toM inner h.genesis uEarly highC
  have scan : ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false)
    v.toNat highC
      inner) ≤ sourceCredits .rewards events := by
    have := Internal.creditScan_sum_le S UInt64.toNat (fun s => decide (s = .rewards)) (fun _ =>
      false) highC
      (fun e => e.creditLimit) inner replayed fun e member _ =>
        Internal.sum_keyCredit_le_creditLimit S e (bounded e member).1
    simpa [sourceCredits] using this
  obtain ⟨reads, data⟩ := epoch_credits_data inner (by exact electra) uEarly same highC replayed
  rcases reads with ⟨total, perIncrement, totalOk, per⟩ | ⟨quiet, -⟩
  swap
  · rw [quiet] at scan
    simp [Nat.le_zero.mp scan]
  obtain ⟨credits, -⟩ := data total perIncrement totalOk per
  obtain ⟨pq, pqOk⟩ := Internal.quarter_base_ok h.facts per ((getTotalActiveBalance
    pulled).toOption.getD 0)
  obtain ⟨prev, curr, band⟩ := start_rates h within link pqOk pulledOk totalOk per
  have rate : (pinTerms config pulled anc fin).perIncrement = pq.toNat := by
    show ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat = pq.toNat
    rw [pqOk]
    rfl
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  rw [rate]
  exact Nat.le_trans (Nat.mul_le_mul_right 896 scan)
    (propN_arith incPos credits prev curr band)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The proposer credits of a set of keys over a one-epoch segment of C's branch are bounded. -/
private theorem propN_segment_le (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) (S : Finset ValidatorIndex) {T : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok T) {s0 : BeaconState preset fork}
    {m n : ForkedBeaconState preset} (toS : Run config checks g ⟨fork, s0⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, s0⟩) ∨
      ∃ _ : Run config checks ⟨fork, s0⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch s0)
    -- The segment may follow a run `head` of its own epoch, whose credits it adds to.
    (head : Run config checks ⟨fork, s0⟩ m) (mid : Run config checks m n)
    (rest : Run config checks n ⟨fork, counted⟩)
    (sameStart : getCurrentEpoch m.state = getCurrentEpoch s0)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state) :
    ((∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      head)) + ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false)
        v.toNat
        highC mid)) * 896 ≤
      -- The bound is the pin's rate on the pulled total, with `896` times the credits on the left.
      324 * ((pinTerms config pulled anc fin).perIncrement *
        (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement := by
  -- The slot that ends the segment adds no block credit.
  --
  -- So the segment fits as its run before that slot does.
  have mFork : m.fork = fork := Internal.fork_eq_of_run head (mid.append rest) (Nat.le_refl _)
  obtain ⟨mf, ms⟩ := m
  obtain rfl : mf = fork := mFork
  rcases DirectSafety.Apriori.Internal.segment_slot_cases mid starts with same |
    ⟨u, inner, boundary, rfl, uEpoch, -⟩
  · have whole := propN_epoch_le h highC S pulledOk toS link (head.append mid) rest
      (same.trans sameStart)
    simp only [Internal.creditScan_append, Finset.sum_add_distrib] at whole
    exact whole
  · have whole := propN_epoch_le h highC S pulledOk toS link (head.append inner)
      ((Run.nil.snoc (Step.slot boundary)).append rest) (uEpoch.trans sameStart)
    simp only [Internal.creditScan_append, Finset.sum_add_distrib] at whole
    refine Nat.le_trans (Nat.mul_le_mul_right 896 (Nat.add_le_add_left
      (Finset.sum_le_sum fun v _ => ?_) _)) whole
    rw [Internal.creditScan_snoc]
    split <;> simp [Internal.stepCredit]

/-- The whole increments of aligned stakes are at most those of larger stakes on a larger set. -/
private theorem stake_le_base {α : Type} {inc pq : ℕ} {P : Finset ℕ} {f : ℕ → ℕ} {A : Finset α}
    {g : α → ℕ} (e : ℕ → ℕ) (incPos : 0 < inc) (inj : Set.InjOn g A)
    (inside : ∀ a ∈ A, g a ∈ P) (le : ∀ a ∈ A, e (g a) ≤ f (g a)) (dvd : ∀ j, inc ∣ e j) :
    pq * ((∑ a ∈ A, e (g a)) / inc) ≤ ∑ j ∈ P, f j / inc * pq := by
  rw [← Finset.sum_image (f := e) inj]
  have exact : ∑ j ∈ A.image g, e j = inc * ∑ j ∈ A.image g, e j / inc := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (Nat.mul_div_cancel' (dvd j)).symm
  rw [exact, Nat.mul_div_cancel_left _ incPos, Finset.mul_sum]
  refine Nat.le_trans (Finset.sum_le_sum fun j member => ?_)
    (Finset.sum_le_sum_of_subset (f := fun j => f j / inc * pq) fun j member => ?_)
  · obtain ⟨a, inA, rfl⟩ := Finset.mem_image.mp member
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (le a inA))
  · obtain ⟨a, inA, rfl⟩ := Finset.mem_image.mp member
    exact inside a inA

/-- The epoch bound of the pin's rate on the pulled total is at most the proposer credit.

The proposer base pays the bound, with an allowance at the rate for one extra increment. -/
private theorem credit_arith {inc pi E T P A : ℕ} (incPos : 0 < inc) (hT : T = max inc E)
    (hP : pi * (E / inc) ≤ P) (hA : 1 ≤ A) :
    (324 * (pi * (T / inc)) + 216 * pi) / 896 ≤ P + A * pi := by
  have one : T / inc ≤ E / inc + 1 := by
    rw [hT]
    rcases le_total inc E with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h, Nat.div_self incPos]; exact Nat.le_add_left _ _
  have mul : pi * (T / inc) ≤ pi * (E / inc) + pi := by
    calc pi * (T / inc) ≤ pi * (E / inc + 1) := Nat.mul_le_mul_left _ one
      _ = _ := by ring
  have A1 : pi ≤ A * pi := Nat.le_mul_of_pos_left _ hA
  refine Nat.div_le_of_le_mul ?_
  nlinarith

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- C's proposer credits to any set of keys, with the sync part of the bound, are bounded. -/
theorem proposer_rewards_le (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
      ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch b)
    -- The credits start at a state `b` of the split's epoch.
    --
    -- So they include the run `pre` from `b`.
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (S : Finset ValidatorIndex) :
    (∑ v ∈ S, Internal.propN (pre.append tailC) highC v.toNat) +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer ≤
      -- The bound is the proposer credit of each epoch of the window.
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit := by
  -- The credits of each epoch are cut over the blocks, and the split's epoch is cut once from `b`.
  --
  -- So the flag rewards of its epoch pass are not read.
  obtain ⟨T, pulledOk⟩ := h.pulledTotal
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  obtain ⟨B, hB⟩ : ∃ B, B = (324 * ((pinTerms config pulled anc fin).perIncrement *
      (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement) / 896 := ⟨_, rfl⟩
  -- the credits of `pre` are those of one epoch run, so they fit one epoch's bound
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards))
    (fun _ => false) v.toNat highC pre) := ⟨_, rfl⟩
  have first : P ≤ B := by
    have one := propN_segment_le h highC S pulledOk toB link pre
      (Run.nil : Run config checks ⟨fork, split⟩ ⟨fork, split⟩) tailC sameEpoch
      (fun step member => by cases member)
    rw [hB, hP]
    refine (Nat.le_div_iff_mul_le (by norm_num)).mpr (Nat.le_trans ?_ one)
    simp only [Internal.creditScan_nil, Finset.sum_const_zero, Nat.add_zero]
    exact Nat.le_refl _
  have cut := run_cuts_of_additive tailC h.early (fun _ => True)
    (fun r => ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false)
      v.toNat highC
      r)) (fun i => if i = 0 then B - P else B)
    (fun pre post _ => by simp only [Internal.creditScan_append, Finset.sum_add_distrib])
    (fun _ _ _ _ => trivial)
    (fun {m n} toM mid rest starts _ => by
      obtain ⟨mf, ms⟩ := m
      obtain rfl : fork = mf := (Internal.fork_eq_of_run toM (mid.append rest) (Nat.le_refl _)).symm
      by_cases e : getCurrentEpoch ms = getCurrentEpoch split
      · -- the segment is in the split's epoch, so it adds to the credits of `pre`
        have index : ix (⟨fork, split⟩ : ForkedBeaconState preset) ⟨fork, ms⟩ = 0 := by
          simp only [ix, e]
          omega
        simp only [index, ↓reduceIte]
        have one := propN_segment_le h highC S pulledOk toB link (pre.append toM) mid rest
          (by simpa only [sameEpoch] using e) starts
        have again : P ≤ ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ =>
          false)
            v.toNat highC (pre.append toM)) := by
          rw [hP]
          exact Finset.sum_le_sum fun v _ => by
            rw [Internal.creditScan_append]
            exact Nat.le_add_right _ _
        have bound : P + ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ =>
          false)
            v.toNat highC mid) ≤ B := by
          rw [hB]
          exact (Nat.le_div_iff_mul_le (by norm_num)).mpr
            (Nat.le_trans (Nat.mul_le_mul_right 896 (Nat.add_le_add_right again _)) one)
        omega
      · have later : getCurrentEpoch split < getCurrentEpoch ms :=
          UInt64.lt_of_le_of_ne (currentEpoch_le_of_chainSteps toM.chainSteps) (Ne.symm e)
        have index : ix (⟨fork, split⟩ : ForkedBeaconState preset) ⟨fork, ms⟩ ≠ 0 := by
          have := UInt64.lt_iff_toNat_lt.mp later
          simp only [ix]
          omega
        simp only [index, ↓reduceIte]
        rw [hB]
        have one := propN_segment_le h highC S pulledOk ((toFin.append fromFin).append toM)
          (Or.inl ⟨fromFin.append toM⟩) (Run.nil : Run config checks ⟨fork, ms⟩ ⟨fork, ms⟩) mid
          rest rfl starts
        simp only [Internal.creditScan_nil, Finset.sum_const_zero, Nat.zero_add] at one
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr one)
    (ix ⟨fork, split⟩ ⟨fork, counted⟩ + 1) (fun step member => steps_before_end tailC step member)
  have total : ∀ t : ℕ, ((List.range (t + 1)).map
      (fun i => if i = 0 then B - P else B)).sum + P ≤ (t + 1) * B := by
    intro t
    induction t with
    | zero => simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        ↓reduceIte, Nat.add_zero, Nat.zero_add]; omega
    | succ t ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.succ_ne_zero t, ↓reduceIte] at ih ⊢
      have : (t + 1 + 1) * B = (t + 1) * B + B := by ring
      omega
  have joined : ∑ v ∈ S, Internal.propN (pre.append tailC) highC v.toNat =
      P + ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat
        highC
        tailC) := by
    rw [hP, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Internal.creditScan_append _ _ _ _ pre tailC
  have depth : ix ⟨fork, split⟩ ⟨fork, counted⟩ + 1 ≤ (pinTerms config pulled anc fin).depth := by
    have fin' := UInt64.le_iff_toNat_le.mp h.finalized
    have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have near := h.near
    show _ ≤ (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat
    simp only [ix]
    omega
  have credit : B + (pinTerms config pulled anc fin).syncProposer ≤
      (pinTerms config pulled anc fin).proposerCredit := by
    obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok pulledOk)
    rw [hB]
    simp only [pinTerms]
    refine Nat.add_le_add_right (credit_arith incPos value ?_ ?_) _
    · refine stake_le_base (g := UInt64.toNat) (fun j => balanceAt pulled j) incPos
        (fun a _ b _ same => UInt64.toNat_inj.mp same) (fun a member => ?_)
        (fun a _ => Nat.le_trans (Nat.le_add_right _ _) (le_max_left _ _)) fun j =>
          Nat.dvd_of_mod_eq_zero (FloorTrace.effective_aligned
            (toFin.append (fromFin.append toPulled)) h.genesis h.aligned j)
      obtain ⟨w, found, active⟩ := (mem_getActiveValidatorIndices
        (pulled.validators.bound h.early)).mp (List.mem_toFinset.mp member)
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
      have exit := UInt64.lt_iff_toNat_lt.mp active.2
      have fin' := UInt64.le_iff_toNat_le.mp h.finalized
      have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
      exact Internal.mem_positions_filter config pulled anc fin found (by simp [found]; omega)
    · have slots := h.twoSlots
      have two : 2 ≤ (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := by
        have := UInt64.le_iff_toNat_le.mp h.finalized
        have := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
        omega
      -- The first of the credited keys' slots is one of the terms of `attesterExcess`.
      iterate 4 refine Nat.le_trans ?_ (Nat.le_add_right _ _)
      refine Nat.le_trans ?_ (Nat.le_add_left _ _)
      iterate 3 refine Nat.le_trans ?_ (Nat.le_add_right _ _)
      exact Nat.le_trans (by decide) (Nat.mul_le_mul two slots)
  calc _ ≤ (ix ⟨fork, split⟩ ⟨fork, counted⟩ + 1) * B +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer :=
      Nat.add_le_add_right (by
        rw [joined]
        have := total (ix ⟨fork, split⟩ ⟨fork, counted⟩)
        omega) _
    _ ≤ (pinTerms config pulled anc fin).depth * B +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ depth) _
    _ ≤ _ := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ credit

/-- The sources of the due entries of X's queue that name a target in `T`. -/
def dueList (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : List Validator :=
  (((X.pendingConsolidations electra).data.toList.filter fun c =>
      decide (c.targetIndex ∈ T)).filterMap fun c =>
    X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
      !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)

/-- Counting the due entries gives the consolidation queue's contribution. -/
theorem dueAt_eq (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : Internal.dueAt X high T = (Internal.dueList X electra high
      T).length := by
  unfold Internal.dueAt Internal.dueList
  simp only [electra, ↓reduceDIte]

/-- The caps of the due entries of two disjoint sets of targets add up. -/
private theorem dueList_sum_union (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (disjoint : Disjoint A B) (f : Validator → ℕ) :
    ((Internal.dueList X electra high (A ∪ B)).map f).sum =
      ((Internal.dueList X electra high A).map f).sum + ((Internal.dueList X electra high B).map
        f).sum := by
  -- Each entry adds the value of its source when the source passes the test, else nothing.
  have perEntry : ∀ (M : List PendingConsolidation)
      (look : PendingConsolidation → Option Validator) (ok : Validator → Bool),
      (((M.filterMap look).filter ok).map f).sum =
        (M.map fun c => (((look c).filter ok).map f).getD 0).sum := by
    intro M look ok
    induction M with
    | nil => rfl
    | cons c M ih =>
      cases found : look c with
      | none => simp [found, ih]
      | some w => by_cases keep : ok w = true <;> simp [found, keep, ih, Option.filter]
  unfold Internal.dueList
  rw [perEntry, perEntry, perEntry]
  have := Internal.sum_filter_or (X.pendingConsolidations electra).data.toList
    (fun c => decide (c.targetIndex ∈ A)) (fun c => decide (c.targetIndex ∈ B))
    (by
      rintro c ⟨ha, hb⟩
      simp only [decide_eq_true_eq] at ha hb
      exact Finset.disjoint_left.mp disjoint ha hb)
    (fun c => ((((X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
      !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map f).getD 0))
  simpa [Finset.mem_union, Bool.decide_or] using this

/-- The due entries of two disjoint sets of targets number as many as those of their union. -/
private theorem dueList_length_union (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (disjoint : Disjoint A B) :
    (Internal.dueList X electra high (A ∪ B)).length =
      (Internal.dueList X electra high A).length + (Internal.dueList X electra high B).length := by
  have := dueList_sum_union X electra high disjoint (fun _ => 1)
  simpa using this

/-- A later horizon keeps at least the stake of an earlier one. -/
theorem dueList_sum_mono (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    {high high' : ℕ} (later : high ≤ high') (T : Finset ValidatorIndex) (f : Validator → ℕ) :
    ((Internal.dueList X electra high T).map f).sum ≤ ((Internal.dueList X electra high' T).map
      f).sum := by
  unfold Internal.dueList
  have sub : List.Sublist
      ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter
        (fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)))
      ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter
        (fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high' + 1))) := by
    refine List.monotone_filter_right _ fun b hb => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    exact ⟨hb.1, by omega⟩
  exact (sub.map f).sum_le_sum fun _ _ => Nat.zero_le _

/-- A later horizon keeps at least the entries of an earlier one. -/
private theorem dueList_length_mono (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    {high high' : ℕ} (later : high ≤ high') (T : Finset ValidatorIndex) :
    (Internal.dueList X electra high T).length ≤ (Internal.dueList X electra high' T).length := by
  simpa using Internal.dueList_sum_mono X electra later T fun _ => 1

/-- More targets keep at least the entries of fewer. -/
private theorem dueList_length_subset (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (sub : A ⊆ B) :
    (Internal.dueList X electra high A).length ≤ (Internal.dueList X electra high B).length := by
  unfold Internal.dueList
  refine (((List.monotone_filter_right _ fun c hc => ?_).filterMap _).filter _).length_le
  simp only [decide_eq_true_eq] at hc ⊢
  exact sub hc

/-- The due entries of any targets have at most the stake of all entries read at that horizon. -/
theorem dueList_sum_le_all (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) (T : Finset ValidatorIndex) (f : Validator → ℕ) :
    ((Internal.dueList X electra high T).map f).sum ≤
      ((((((X.pendingConsolidations electra).data.toList.filterMap fun c =>
        X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map f)).sum) := by
  unfold Internal.dueList
  refine (List.Sublist.map f ?_).sum_le_sum fun _ _ => Nat.zero_le _
  exact (List.filter_sublist.filterMap _).filter _

/-- A whistleblower's share of an amount is at most the amount.

The quotient is at least thirty, so a share of `33/300` of the amount, rounded up, fits. -/
theorem wShare_le (facts : PinPresetFacts preset) (x : ℕ) : Internal.wShare preset fork x ≤ x := by
  have quotient := facts.whistleblower fork
  unfold Internal.wShare
  generalize (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = W at *
  have pos : 0 < 10 * W := by omega
  refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul pos).mpr ?_)
  have big : 33 * x ≤ 10 * W * x := Nat.mul_le_mul_right _ (by omega)
  have two : (x + 1) * (10 * W) = 10 * W * x + 10 * W := by ring
  show 33 * x + 10 * W - 1 < (x + 1) * (10 * W)
  omega

/-- The due entries of a set of targets are those of its keys.

Each entry names one target. -/
private theorem dueAt_sum (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : ∑ v ∈ T, Internal.dueAt X high {v} = Internal.dueAt X high T := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Internal.dueAt_eq X electra high]
    simp [Internal.dueList]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Internal.dueAt_eq X electra high, Internal.dueAt_eq X electra
      high,
      Internal.dueAt_eq X electra high, show insert a s = {a} ∪ s from rfl,
      dueList_length_union X electra high (Finset.disjoint_singleton_left.mpr ha)]

/-- The band of a key is its upward band for each due entry that names it, and these add over keys.

The due entries of a set of targets are the due entries of its keys. -/
theorem bandX_sum (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) :
    ∑ v ∈ T, Internal.bandX X high v.toNat = preset.upwardBand * Internal.dueAt X high T := by
  classical
  have single (v : ValidatorIndex) :
      Internal.bandX X high v.toNat = preset.upwardBand * Internal.dueAt X high {v} := by
    simp [Internal.bandX]
  simp only [single]
  rw [← Finset.mul_sum, dueAt_sum X electra high T]

/-- No key is in two of the staying, the previous-only and the joined keys and `V`. -/
theorem classes_disjoint (h : Setting config checks g split fin pulled anc counted V) :
    Disjoint (stayingKeys pulled counted V) (previousOnlyKeys counted V) ∧
    Disjoint (stayingKeys pulled counted V) (joinedKeys pulled counted) ∧
    Disjoint (previousOnlyKeys counted V) (joinedKeys pulled counted) ∧
    Disjoint V (stayingKeys pulled counted V) ∧ Disjoint V (previousOnlyKeys counted V) ∧
    Disjoint V (joinedKeys pulled counted) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine Finset.disjoint_left.mpr fun v a b => ?_
  · simp only [stayingKeys, previousOnlyKeys, Finset.mem_filter] at a b
    exact b.2.1 a.1
  · simp only [stayingKeys, joinedKeys, Finset.mem_filter] at a b
    exact b.2.2 a.2.1
  · simp only [previousOnlyKeys, joinedKeys, Finset.mem_filter] at a b
    exact a.2.1 b.1
  · simp only [stayingKeys, Finset.mem_filter] at b
    exact b.2.2.2 a
  · simp only [previousOnlyKeys, Finset.mem_filter] at b
    exact b.2.2 a
  · simp only [joinedKeys, Finset.mem_filter] at b
    exact b.2.2 (h.voting v a).1

/-- A staying, previous-only or joined key is in C's quorum. -/
theorem classes_mem_countedQuorum {v : ValidatorIndex}
    (member : v ∈ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled
        counted)
      : v ∈ countedQuorum counted := by
  simp only [Finset.mem_union] at member
  rcases member with (h4 | h5) | h6
  · simp only [stayingKeys, Finset.mem_filter] at h4
    exact h4.2.2.1
  · simp only [previousOnlyKeys, Finset.mem_filter] at h5
    exact h5.1
  · simp only [joinedKeys, Finset.mem_filter] at h6
    exact h6.2.1

/-- A staying, previous-only or joined key is in C's quorum.

So it is unslashed at C. -/
theorem classes_unslashed {v : ValidatorIndex}
    (member : v ∈ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled
        counted)
      :
    slashedFlagAt counted v.toNat ≠ some true := by
  have inQ := classes_mem_countedQuorum member
  intro slashed
  simp only [countedQuorum, quorumVoters, Finset.mem_filter] at inQ
  have unslashed := inQ.2
  unfold slashedFlagAt at slashed
  rw [slashed] at unslashed
  simp at unslashed

/-- The keys slashed at C and not at the split are in no class of C's quorum, and not in `V`. -/
theorem newlySlashed_disjoint (h : Setting config checks g split fin pulled anc counted V) :
    Disjoint (stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted)
      (newlySlashed pulled counted split) ∧
    Disjoint V (newlySlashed pulled counted split) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hk hs
    simp only [newlySlashed, Finset.mem_filter] at hs
    exact Internal.classes_unslashed hk hs.2.1
  · rw [Finset.disjoint_left]
    intro v hv hs
    simp only [newlySlashed, Finset.mem_filter] at hs
    have unslashed := (h.voting v hv).2
    rw [hs.2.1] at unslashed
    simp at unslashed

/-- The keys created after the split's registry and slashed at C are in no other class.

They are slashed at C, so they are not in C's quorum or in `V`.

They are absent at the split, so they are not newly slashed keys. -/
theorem createdSlashed_disjoint (h : Setting config checks g split fin pulled anc counted V) :
    Disjoint (stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted
        ∪
      newlySlashed pulled counted split)
      (createdSlashed counted split) ∧ Disjoint V (createdSlashed counted split) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hk hc
    simp only [createdSlashed, Finset.mem_filter] at hc
    rcases Finset.mem_union.mp hk with quorum | created
    · exact Internal.classes_unslashed quorum hc.2.2
    · simp only [newlySlashed, Finset.mem_filter] at created
      have absent : slashedFlagAt split v.toNat = none := by
        simp only [slashedFlagAt, Option.map_eq_none_iff]
        exact Array.getElem?_eq_none hc.2.1
      rw [absent] at created
      cases created.2.2
  · rw [Finset.disjoint_left]
    intro v hv hc
    simp only [createdSlashed, Finset.mem_filter] at hc
    have unslashed := (h.voting v hv).2
    rw [hc.2.2] at unslashed
    simp at unslashed

/-- A key that a run credits.

A block step credits it, or a pending-deposit pass does. -/
def creditedKey {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) : Bool :=
  decide (0 < Internal.grossScan v.toNat high tail +
    (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat high tail))

/-- The gain budget counts one unit per credited-key slot and two more per exiting key.

The same holds for each queue key.

The slots are at least the proposers, the seats and the deposit recipients of the window.

They also hold the seat units of R's branch and the shared segment. -/
theorem creditUnits_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
    ∃ N : ℕ, (pinTerms config pulled anc fin).creditUnits =
        (N + 2 * (((pinTerms config pulled anc fin).positions.filter fun i =>
          (pinTerms config pulled anc fin).exitingB i = true).card +
            (pinTerms config pulled anc fin).queueKeys)) *
          (pinTerms config pulled anc fin).unitGain ∧
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
            ((pinTerms config pulled anc fin).depthFin /
              max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2)) *
          preset.SYNC_COMMITTEE_SIZE.toNat ≤ N := by
  dsimp only [pinTerms]
  simp only [decide_eq_true_eq]
  exact ⟨_, rfl, by omega⟩

/-- The keys that a sync aggregate debits on the shared segment or R's branch fit the seat units.

The seat units are the seats of the committees of the periods that the two runs touch. -/
theorem debit_keys_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high : ℕ)
    {events eventsF : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents high = .ok eventsF) (A B : Finset ValidatorIndex)
    (debitsF : ∀ v ∈ A, 0 < Internal.syncD eventsF v.toNat) (debitsR : ∀ v ∈ B, 0 < Internal.syncD
      events v.toNat) :
    (A ∪ B).card ≤ ((pinTerms config pulled anc fin).depth /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((pinTerms config pulled anc fin).depthFin /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2)) *
      preset.SYNC_COMMITTEE_SIZE.toNat := by
  classical
  obtain ⟨eventsC, replayedC⟩ := tailC.balanceEvents_ok h.early high
  have inj : Function.Injective fun v : ValidatorIndex => v.toNat := fun a b same =>
    UInt64.toNat_inj.mp same
  have union := Internal.seat_union_card h fromFin tail tailC high high replayed replayedF replayedC
    (Nat.le_trans (by decide) h.fulu) (A.image fun v => v.toNat) (B.image fun v => v.toNat)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      have := debitsF v hv
      simp only [Internal.syncD, List.map_append, List.sum_append] at this ⊢
      omega)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact debitsR v hv)
  rw [← Finset.image_union, Finset.card_image_of_injective _ inj] at union
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have periods := Nat.add_div_le_div_add_div_add_one
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) (getCurrentEpoch fin).toNat
    (max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
  have shift : ((getCurrentEpoch pulled).toNat + 1) /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat ≤ ((getCurrentEpoch pulled).toNat + 2) /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := Nat.div_le_div_right (by omega)
  rw [Nat.sub_add_cancel (by omega)] at periods
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have depthFinEq : (pinTerms config pulled anc fin).depthFin =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := rfl
  refine union.trans ?_
  have nonneg := Nat.zero_le (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) /
    max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
  rw [depthEq, depthFinEq, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The credited keys of a set fit the credited-key slots of the window.

The slots are the proposers, the seats and the deposit recipients of the window.

The count uses the slots of the epochs on C's run. -/
theorem credited_slots_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (T : Finset ValidatorIndex) (inside : ∀ v ∈ T, v.toNat < counted.validators.data.size) :
    (T.filter fun v => Internal.creditedKey tailC highC v = true).card ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  have fit : (T.filter fun v => Internal.creditedKey tailC highC v = true).card ≤
      ((Finset.range counted.validators.data.size).filter fun i =>
        0 < Internal.grossScan i highC tailC +
          (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC
            tailC)).card := by
    refine Finset.card_le_card_of_injOn (fun v : ValidatorIndex => v.toNat) (fun v hv => ?_)
      (fun a _ b _ same => UInt64.toNat_inj.mp same)
    obtain ⟨member, flag⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (inside v member), of_decide_eq_true flag⟩
  have credited := Internal.credited_keys_le h tailC highC
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  -- The slots of the run's epochs are at most those of the window.
  have near := h.near
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have monotone := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
  simp only at monotone
  have wide : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat + 1 ≤
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := by omega
  have periods := Nat.add_div_le_div_add_div_add_one
    ((getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat)
    (getCurrentEpoch split).toNat (max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
  rw [Nat.sub_add_cancel monotone] at periods
  have periodsLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    (show (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat by omega)
  have monotoneLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) monotone
  have first := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) wide
  have second := Nat.mul_le_mul_left preset.SYNC_COMMITTEE_SIZE.toNat
    (show (getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 ≤
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2 by omega)
  have bound : ((getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat + 1) *
      (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
        preset.SYNC_COMMITTEE_SIZE.toNat *
          ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
              1) ≤
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) *
          preset.SLOTS_PER_EPOCH.toNat +
        (((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat :=
    (Nat.add_le_add first second).trans_eq (by ring)
  rw [depthEq]
  omega

/-- The credited keys of the classes and of the slashed keys fit the window's credited-key slots.

The classes are the staying, the previous-only and the joined keys.

The slashed keys are the newly slashed and the created slashed keys.
-/
theorem credited_classes_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    ((stayingKeys pulled counted V).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((previousOnlyKeys counted V).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((joinedKeys pulled counted).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((newlySlashed pulled counted split).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((createdSlashed counted split).filter fun v =>
        Internal.creditedKey tailC highC v = true).card ≤
    -- The slots are the proposers, the seats and the deposit recipients of the window.
    (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
      ((pinTerms config pulled anc fin).depth /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
          preset.SYNC_COMMITTEE_SIZE.toNat +
      (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  -- A credited created slashed key is a credited key of C's run, in C's registry, like the others.
  classical
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  obtain ⟨dSC, -⟩ := newlySlashed_disjoint h
  obtain ⟨dCS, -⟩ := createdSlashed_disjoint h
  set C4 := (stayingKeys pulled counted V).filter fun v => Internal.creditedKey tailC highC v = true
  set C5 := (previousOnlyKeys counted V).filter fun v => Internal.creditedKey tailC highC v = true
  set C6 := (joinedKeys pulled counted).filter fun v => Internal.creditedKey tailC highC v = true
  set Csc := (newlySlashed pulled counted split).filter fun v =>
    Internal.creditedKey tailC highC v = true
  set Ccs := (createdSlashed counted split).filter fun v =>
    Internal.creditedKey tailC highC v = true
  -- The five classes are apart, and each key of them is in C's registry.
  have apart : Disjoint (C4 ∪ C6) C5 :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_filter_filter d45,
      (Finset.disjoint_filter_filter d56).symm⟩
  have apartSC : Disjoint (C4 ∪ C6 ∪ C5) Csc :=
    Finset.disjoint_of_subset_left (u := stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪
      joinedKeys pulled counted)
      (fun v hv => by
        simp only [C4, C5, C6, Finset.mem_union, Finset.mem_filter] at hv
        simp only [Finset.mem_union]
        tauto)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dSC)
  have apartCS : Disjoint (C4 ∪ C6 ∪ C5 ∪ Csc) Ccs :=
    Finset.disjoint_of_subset_left (u := stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪
      joinedKeys pulled counted ∪
      newlySlashed pulled counted split)
      (fun v hv => by
        simp only [C4, C5, C6, Csc, Finset.mem_union, Finset.mem_filter] at hv
        simp only [Finset.mem_union]
        tauto)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dCS)
  have card5 : (C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs).card =
      C4.card + C6.card + C5.card + Csc.card + Ccs.card := by
    rw [Finset.card_union_of_disjoint apartCS, Finset.card_union_of_disjoint apartSC,
      Finset.card_union_of_disjoint apart,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter d46)]
  have inCounted : ∀ v ∈ stayingKeys pulled counted V ∪ joinedKeys pulled counted ∪ previousOnlyKeys
    counted V,
      v.toNat < counted.validators.data.size := by
    intro v hv
    simp only [Finset.mem_union] at hv
    rcases hv with (h4 | h6) | h5
    · obtain ⟨w, found, -⟩ := Internal.active_of_activeVoters h.early (Finset.mem_filter.mp h4).1
      exact (Array.getElem?_eq_some_iff.mp found).1
    · obtain ⟨w, found, -⟩ := Internal.active_of_activeVoters h.early (Finset.mem_filter.mp h6).1
      exact (Array.getElem?_eq_some_iff.mp found).1
    · have listed := (Finset.mem_filter.mp h5).1
      simp only [countedQuorum, quorumVoters, Finset.mem_filter, List.mem_toFinset,
        List.mem_append] at listed
      rcases listed.1 with now | before
      · exact lt_size_of_mem_getActiveValidatorIndices now
      · exact lt_size_of_mem_getActiveValidatorIndices before
  have flagIn : ∀ v : ValidatorIndex, slashedFlagAt counted v.toNat = some true →
      v.toNat < counted.validators.data.size := by
    intro v flag
    simp only [slashedFlagAt, Option.map_eq_some_iff] at flag
    obtain ⟨w, found, -⟩ := flag
    exact (Array.getElem?_eq_some_iff.mp found).1
  have inSC : ∀ v ∈ newlySlashed pulled counted split, v.toNat < counted.validators.data.size :=
    fun v hv => flagIn v (Finset.mem_filter.mp hv).2.1
  have inCS : ∀ v ∈ createdSlashed counted split, v.toNat < counted.validators.data.size :=
    fun v hv => flagIn v (Finset.mem_filter.mp hv).2.2
  have flags : ∀ v ∈ C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs, Internal.creditedKey tailC highC v = true := by
    intro v member
    simp only [C4, C5, C6, Csc, Ccs, Finset.mem_union, Finset.mem_filter] at member
    tauto
  have inside : ∀ v ∈ C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs, v.toNat < counted.validators.data.size := by
    intro v member
    have classed : v ∈ stayingKeys pulled counted V ∪ joinedKeys pulled counted ∪ previousOnlyKeys
      counted V ∨
        v ∈ newlySlashed pulled counted split ∨ v ∈ createdSlashed counted split := by
      simp only [C4, C5, C6, Csc, Ccs, Finset.mem_union, Finset.mem_filter] at member ⊢
      tauto
    rcases classed with held | held | held
    · exact inCounted v held
    · exact inSC v held
    · exact inCS v held
  have slots := Internal.credited_slots_le h tailC highC _ inside
  rw [Finset.filter_true_of_mem flags, card5] at slots
  omega

/-- The rounding slacks of a set of keys are the upward band for each credited key. -/
theorem band_sum {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (S : Finset ValidatorIndex) :
    ∑ v ∈ S, Internal.bandC tail high v.toNat =
      preset.upwardBand * (S.filter fun v => Internal.creditedKey tail high v = true).card := by
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Internal.bandC Internal.creditedKey
  by_cases credited : 0 < Internal.grossScan v.toNat high tail +
    (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat high tail) <;>
    simp [credited]

/-- The credits that a scan reads for a key are at most the credits of its source's events.

The sources of the scan, block and slot, are those that `p` selects. -/
theorem scan_le_events (blockP slotP : BalanceSource → Bool) (p : BalanceSource → Prop)
    [DecidablePred p] (selects : ∀ s, (blockP s = true ∨ slotP s = true) ↔ p s)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high : ℕ)
    (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (Internal.creditScan blockP slotP v.toNat high tail) ≤
      ((events.filter fun e => p e.source).map (Internal.keyCredit v.toNat)).sum := by
  have scan := Internal.creditScan_sum_le {v} UInt64.toNat blockP slotP high (Internal.keyCredit
    v.toNat) tail
    replayed fun e _ _ => by simp
  simp only [Finset.sum_singleton] at scan
  refine scan.trans (le_of_eq ?_)
  simp only [selects]
  rw [List.sum_map_ite (fun e : BalanceEvent preset => p e.source) (Internal.keyCredit v.toNat)
    (fun _ => 0)]
  simp

/-- The credits of a key on C's branch are its proposer credits and deposits, up to consolidations.

The consolidations are those of the replayed events. -/
theorem credit_parts_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    Internal.credC tail high v.toNat ≤ Internal.credN tail high v.toNat + Internal.consAmt events
      v.toNat ∧
    Internal.propC tail high v.toNat ≤ Internal.propN tail high v.toNat + Internal.consAmt events
      v.toNat := by
  have cons := Internal.scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp) tail high v
    replayed
  have c := Internal.credC_split tail high v.toNat
  have p := Internal.propC_split tail high v.toNat
  exact ⟨by unfold Internal.consAmt; omega, by unfold Internal.consAmt; omega⟩

/-- C's proposer credits to inactive counted keys outside the voter set count at weight three. -/
theorem budget_exitingCredits (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
      ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch b)
    -- This run starts at the split's epoch, so its credits are proposer credits only.
    --
    -- Consolidations and deposits credit at epoch processing, so none falls inside `pre`.
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    -- The bound uses a factor of ten to account for compounding and rounding the extra exit charge.
    --
    -- The compounding of the credits, an exact tenth of the keys' total, is in the bound.
    10 * (2 * ((∑ v ∈ (previousOnlyKeys counted V), Internal.propN pre highC v.toNat) +
        ∑ v ∈ (previousOnlyKeys counted V), Internal.propC tailC highC v.toNat)) +
      -- The reserve also accounts separately for two more bands per credited key in this group.
      2 * ((∑ v ∈ (previousOnlyKeys counted V), Internal.propN pre highC v.toNat) +
        ∑ v ∈ (previousOnlyKeys counted V), Internal.propN tailC highC v.toNat) +
        -- The reserve accounts separately for the proposer's sync rewards.
        22 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).exitingCredits +
        -- The bound adds the amounts transferred by consolidation.
        20 * (∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat) := by
  -- The proposer credits fit the pin's per-epoch bound, and their consolidation part is `consAmt`.
  have rewards := Internal.proposer_rewards_le h toB link pre sameEpoch tailC highC
      (previousOnlyKeys
    counted V)
  simp only [Internal.propN_append, Finset.sum_add_distrib] at rewards
  have parts : ∑ v ∈ (previousOnlyKeys counted V), Internal.propC tailC highC v.toNat ≤
      ∑ v ∈ (previousOnlyKeys counted V), Internal.propN tailC highC v.toNat +
        ∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => (Internal.credit_parts_le tailC highC v replayedC).2
  have exiting : (pinTerms config pulled anc fin).exitingCredits =
      (22 * ((pinTerms config pulled anc fin).depth *
        (pinTerms config pulled anc fin).proposerCredit) + 9) / 10 := rfl
  rw [exiting]
  omega

/-- The credit budget includes proposer rewards, queued deposits and credited-key slots.

The separate deposit queue budget counts that queue at weight three. -/
private theorem credits_budget (config : Config) (pulled anc fin : BeaconState preset fork) :
    ∃ carry churn wb ck : ℕ, (pinTerms config pulled anc fin).queueDep = 3 * (churn + carry) ∧
      (pinTerms config pulled anc fin).credits =
        (11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).proposerCredit + carry + churn + wb) + 9) / 10 +
          ck * preset.upwardBand ∧
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤
        ck := by
  dsimp only [pinTerms]
  exact ⟨_, _, _, _, rfl, rfl, Nat.le_add_right _ _⟩

/-- The deposits of the classes fit the deposit queue at weight three.

The keys slashed at C, newly slashed or created slashed, count the deposits of some events.

These are the events that do not hold them slashed.

The classes of C's quorum are apart from them. -/
private theorem deposits_union_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ stayingKeys pulled counted V ∪ joinedKeys pulled counted,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
          tailC)) +
      (∑ v ∈ newlySlashed pulled counted split ∪ createdSlashed counted split, Internal.depPre
          eventsC
        v.toNat)) ≤
      (pinTerms config pulled anc fin).queueDep := by
  have quorum : stayingKeys pulled counted V ∪ joinedKeys pulled counted ⊆
      stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted := fun v
        member => by
    simp only [Finset.mem_union] at member ⊢
    tauto
  refine Internal.deposits_active_le h tailC highC endEpochC replayedC _ _ ?_ (fun v member => ?_)
    fun v member => ?_
  · rw [Finset.disjoint_union_right]
    exact ⟨Finset.disjoint_of_subset_left quorum (newlySlashed_disjoint h).1,
      Finset.disjoint_of_subset_left (fun v m => Finset.mem_union_left _ (quorum m))
        (createdSlashed_disjoint h).1⟩
  · have countedActive : v ∈ countedActiveVoters counted := by
      rcases Finset.mem_union.mp member with m | m
      · exact (Finset.mem_filter.mp m).1
      · exact (Finset.mem_filter.mp m).1
    obtain ⟨w, found, active⟩ := Internal.active_of_activeVoters h.early countedActive
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
    exact ⟨w, found, active.2⟩
  · have flag : slashedFlagAt counted v.toNat = some true := by
      rcases Finset.mem_union.mp member with m | m
      · exact (Finset.mem_filter.mp m).2.1
      · exact (Finset.mem_filter.mp m).2.2
    simpa [slashedFlagAt, Option.map_eq_some_iff] using flag

/-- The credits bound, from the proposer rewards, the deposits and the classes' credited keys. -/
private theorem budget_credits_of (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    -- The proposer budget covers the five classes' proposer rewards and the sync proposer share.
    (rewards : (∑ v ∈ stayingKeys pulled counted V, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ previousOnlyKeys counted V, Internal.propN pre highC v.toNat) +
      (∑ v ∈ previousOnlyKeys counted V, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ joinedKeys pulled counted, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split, Internal.propN pre highC v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ createdSlashed counted split, Internal.propN tailC highC v.toNat) +
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer ≤
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit)
    -- This compares the deposits of the classes with the deposit queue, at weight three.
    --
    -- The deposits of a key slashed at C count only those before its slashing, in its share.
    (deposits : 3 * ((∑ v ∈ stayingKeys pulled counted V ∪ joinedKeys pulled counted,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
          tailC)) +
      (∑ v ∈ newlySlashed pulled counted split ∪ createdSlashed counted split,
        Internal.depPre eventsC v.toNat)) ≤
      (pinTerms config pulled anc fin).queueDep)
    -- This compares the credited keys of the classes with the credited-key slots.
    (cards :
      ((stayingKeys pulled counted V).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((previousOnlyKeys counted V).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((joinedKeys pulled counted).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((newlySlashed pulled counted split).filter fun v =>
        Internal.creditedKey tailC highC v = true).card +
      ((createdSlashed counted split).filter fun v =>
        Internal.creditedKey tailC highC v = true).card ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) :
    10 * ((∑ v ∈ (stayingKeys pulled counted V), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (previousOnlyKeys counted V), Internal.propN pre highC v.toNat) +
      (∑ v ∈ (previousOnlyKeys counted V), Internal.propC tailC highC v.toNat) +
      (∑ v ∈ (stayingKeys pulled counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (previousOnlyKeys counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ newlySlashed pulled counted split, Internal.propN tailC
        highC v.toNat) +
        ∑ v ∈ newlySlashed pulled counted split, Internal.depPre eventsC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split, Internal.propN pre highC
        v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split, Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ createdSlashed counted split, Internal.propN tailC highC
        v.toNat) +
        ∑ v ∈ createdSlashed counted split, Internal.depPre eventsC v.toNat) +
      (∑ v ∈ createdSlashed counted split, Internal.bandC tailC highC v.toNat)) +
      ((∑ v ∈ (stayingKeys pulled counted V), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (joinedKeys pulled counted), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (previousOnlyKeys counted V), Internal.propN pre highC v.toNat) +
        (∑ v ∈ (previousOnlyKeys counted V), Internal.propN tailC highC v.toNat)) +
        11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        10 * ((∑ v ∈ (stayingKeys pulled counted V), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (joinedKeys pulled counted), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat)) := by
  -- The reserve charges consolidation transfers and sync rewards separately.
  classical
  obtain ⟨carry, churn, wb, ck, queue, credits, slots⟩ := credits_budget config pulled anc fin
  obtain ⟨-, d46, -, -, -, -⟩ := Internal.classes_disjoint h
  have dSCCS : Disjoint (newlySlashed pulled counted split) (createdSlashed counted split) :=
    Finset.disjoint_of_subset_left Finset.subset_union_right (createdSlashed_disjoint h).1
  have parts (S : Finset ValidatorIndex) := fun v (_ : v ∈ S) => Internal.credit_parts_le tailC
    highC v
    replayedC
  have sumLe (S : Finset ValidatorIndex) (f g : ValidatorIndex → ℕ)
      (le : ∀ v ∈ S, f v ≤ g v) : ∑ v ∈ S, f v ≤ ∑ v ∈ S, g v := Finset.sum_le_sum le
  have c4 := sumLe (stayingKeys pulled counted V) _ (fun v => Internal.credN tailC highC v.toNat +
    Internal.consAmt eventsC v.toNat) fun v m => (parts _ v m).1
  have c6 := sumLe (joinedKeys pulled counted) _ (fun v => Internal.credN tailC highC v.toNat +
    Internal.consAmt eventsC v.toNat) fun v m => (parts _ v m).1
  have c5 := sumLe (previousOnlyKeys counted V) _ (fun v => Internal.propN tailC highC v.toNat +
    Internal.consAmt eventsC v.toNat) fun v m => (parts _ v m).2
  simp only [Finset.sum_add_distrib] at c4 c6 c5
  have e4 : ∑ v ∈ stayingKeys pulled counted V, Internal.credN tailC highC v.toNat =
      (∑ v ∈ stayingKeys pulled counted V, Internal.propN tailC highC v.toNat) + ∑ v ∈ stayingKeys
        pulled counted V,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
          := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Internal.credN_split tailC highC v.toNat
  have e6 : ∑ v ∈ joinedKeys pulled counted, Internal.credN tailC highC v.toNat =
      (∑ v ∈ joinedKeys pulled counted, Internal.propN tailC highC v.toNat) + ∑ v ∈ joinedKeys
        pulled counted,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
          := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Internal.credN_split tailC highC v.toNat
  rw [Finset.sum_union d46, Finset.sum_union dSCCS] at deposits
  have w1 := Internal.wShare_le (fork := fork) h.facts ((∑ v ∈ newlySlashed pulled counted split,
    Internal.propN tailC highC v.toNat) + ∑ v ∈ newlySlashed pulled counted split, Internal.depPre
      eventsC v.toNat)
  have w3 := Internal.wShare_le (fork := fork) h.facts (∑ v ∈ newlySlashed pulled counted split,
    Internal.propN pre highC v.toNat)
  have w2 := Internal.wShare_le (fork := fork) h.facts ((∑ v ∈ createdSlashed counted split,
    Internal.propN tailC highC v.toNat) + ∑ v ∈ createdSlashed counted split, Internal.depPre
        eventsC
      v.toNat)
  have bands : (∑ v ∈ stayingKeys pulled counted V, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ previousOnlyKeys counted V, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ joinedKeys pulled counted, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ createdSlashed counted split, Internal.bandC tailC highC v.toNat) ≤ ck *
          preset.upwardBand
        := by
    simp only [Internal.band_sum, ← Nat.mul_add]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (cards.trans slots)
  omega

/-- C's non-attestation credits to keys counted once. -/
theorem budget_credits (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
      ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch b)
    -- A previous-only key also reads the proposer credits of `pre`.
    --
    -- That run leads to the split from the start of its epoch.
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    -- The bound uses a factor of ten to account for compounding and rounding the credit charge.
    --
    -- The compounding of the credits, an exact tenth of the keys' total, is in the bound.
    10 * ((∑ v ∈ (stayingKeys pulled counted V), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (previousOnlyKeys counted V), Internal.propN pre highC v.toNat) +
      (∑ v ∈ (previousOnlyKeys counted V), Internal.propC tailC highC v.toNat) +
      -- Each credited staying or previous-only key uses one rounding slot.
      (∑ v ∈ (stayingKeys pulled counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (previousOnlyKeys counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ newlySlashed pulled counted split, Internal.propN tailC
        highC v.toNat) +
        ∑ v ∈ newlySlashed pulled counted split, Internal.depPre eventsC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split, Internal.propN pre highC
        v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split, Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ createdSlashed counted split, Internal.propN tailC highC
        v.toNat) +
        ∑ v ∈ createdSlashed counted split, Internal.depPre eventsC v.toNat) +
      (∑ v ∈ createdSlashed counted split, Internal.bandC tailC highC v.toNat)) +
      ((∑ v ∈ (stayingKeys pulled counted V), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (joinedKeys pulled counted), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (previousOnlyKeys counted V), Internal.propN pre highC v.toNat) +
        (∑ v ∈ (previousOnlyKeys counted V), Internal.propN tailC highC v.toNat)) +
        -- The proposer's sync rewards belong to the sync budget instead.
        11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        -- The reserve also charges consolidation transfers separately.
        10 * ((∑ v ∈ (stayingKeys pulled counted V), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (joinedKeys pulled counted), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat)) :=
  budget_credits_of h pre tailC highC replayedC
    (by
      obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
      have := Internal.proposer_rewards_le h toB link pre sameEpoch tailC highC
        (stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪
        joinedKeys pulled counted ∪ newlySlashed pulled counted split ∪ createdSlashed counted
            split)
      simp only [Internal.propN_append, Finset.sum_add_distrib] at this
      simp only [Finset.sum_union (createdSlashed_disjoint h).1, Finset.sum_union
          (newlySlashed_disjoint
        h).1,
        Finset.sum_union (Finset.disjoint_union_left.mpr ⟨d46, d56⟩),
        Finset.sum_union d45] at this
      omega)
    (deposits_union_le h tailC highC endEpochC replayedC) (Internal.credited_classes_le h tailC
      highC)

/-- The previous-only keys are at most the keys that R reads as exiting and the queue keys.

A previous-only key is read as exiting at R, or has a departure charge on C's run. -/
theorem card_previousOnlyKeys_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (previousOnlyKeys counted V).card ≤ ((pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).exitingB i = true).card +
      (pinTerms config pulled anc fin).queueKeys := by
  classical
  set A := (previousOnlyKeys counted V).filter fun v =>
    (pinTerms config pulled anc fin).exitingB v.toNat = true
  set B := (previousOnlyKeys counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
      v.toNat
  have cover : previousOnlyKeys counted V ⊆ A ∪ B := by
    intro v inK5
    by_cases exiting : (pinTerms config pulled anc fin).exitingB v.toNat = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inK5, exiting⟩)
    · have flag : (pinTerms config pulled anc fin).exitingB v.toNat = false := by
        simpa using exiting
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨inK5, previousOnlyKeys_charged h tailC inK5 flag⟩)
  have exitingLe := Internal.card_exitingB_le config pulled anc fin A fun v hv =>
    (Finset.mem_filter.mp hv).2
  have chargedLe := charged_count h tailC
  exact (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add exitingLe chargedLe))

/-- The events of the sources of consolidations and deposits are at most those of each source. -/
private theorem sum_filter_cons_dep_le (events : List (BalanceEvent preset))
    (f : BalanceEvent preset → ℕ) :
    ((events.filter fun e => decide (e.source = .consolidations ∨ e.source = .deposits)).map
        f).sum ≤
      ((events.filter fun e => decide (e.source = .deposits)).map f).sum +
        ((events.filter fun e => decide (e.source = .consolidations)).map f).sum := by
  have same : (fun e : BalanceEvent preset =>
      decide (e.source = .consolidations ∨ e.source = .deposits)) =
        fun e => decide (e.source = .deposits) || decide (e.source = .consolidations) := by
    funext e
    cases e.source <;> decide
  rw [same]
  have apart : ∀ s : BalanceSource, ¬ (decide (s = .deposits) = true ∧
      decide (s = .consolidations) = true) := fun s h => by
    simp at h
    exact absurd (h.1.symm.trans h.2) (by decide)
  exact (Internal.sum_filter_or events (fun e => decide (e.source = .deposits))
    (fun e => decide (e.source = .consolidations)) (fun e => apart e.source) f).le

/-- A slot step raises the balance of a key that is idle in the previous epoch by its credits.

The credits are those of deposits and consolidations.

The epoch rewards of such a key are 0, and the slot has no sync events. -/
private theorem slot_idle_step {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (ok : advanceSlotAcross config checks m = .ok n) (early : n.fork < .glamsterdam)
    (electra : .pectra ≤ m.fork) (v : ℕ)
    (known : v < m.state.validators.data.size ∨ BalancesMatch m.state)
    (idle : v.toUInt64 ∉ getActiveValidatorIndices m.state (getPreviousEpoch m.state)) :
    actualBalanceAt n v ≤ actualBalanceAt m v +
      Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) v
        (Step.slot ok : Step config checks m n) +
      Internal.stepCredit (fun _ => false) (fun s => decide (s = .consolidations)) v
        (Step.slot ok : Step config checks m n) := by
  have altair : .altair ≤ m.fork := Nat.le_trans (by decide) electra
  obtain ⟨events, replayed⟩ := (Step.slot ok : Step config checks m n).balanceEvents_ok early
  have base := Internal.step_balance_le (Step.slot ok : Step config checks m n) early v
  have rewards := Internal.epochRewards_le (Step.slot ok : Step config checks m n) altair early v
    known 0 0 (.inl idle) (.inl idle)
  have rewardsZero : Internal.epochRewards v (Step.slot ok : Step config checks m n) = 0 := by
    simpa using rewards
  have sources := Internal.step_credit_le_sources shared genesis (Step.slot ok : Step config checks
    m n)
    early electra v replayed
  have noSync := Internal.slot_noSync electra ok early replayed
  have syncZero : (events.map (Internal.syncCredit v)).sum = 0 :=
    List.sum_eq_zero fun x member => by
      obtain ⟨e, mem, rfl⟩ := List.mem_map.mp member
      simp [Internal.syncCredit, noSync e mem]
  have split := sum_filter_cons_dep_le events (Internal.keyCredit v)
  simp only [Internal.stepCredit, Internal.stepNet, replayed, Except.toOption, Option.getD_some,
    syncZero] at base sources ⊢
  simp only [List.filter_false, List.map_nil, List.sum_nil] at sources
  omega

/-- A block step gives no gross credit to a key that is not active and holds no seat.

A key that is not active at the epoch of the step is not its proposer.

A key whose activation is too late for a committee to sample it holds no seat. -/
private theorem block_idle_step {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) (v : ℕ)
    (notActive : ∀ w, s.validators.data[v]? = some w →
      isActiveValidator w (getCurrentEpoch s) = false)
    (notSeated : ∀ w, t.validators.data[v]? = some w → w.activationEpoch = FAR_FUTURE_EPOCH ∨
      (getCurrentEpoch t).toNat + 1 < w.activationEpoch.toNat) :
    Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
      false) v
      (Step.block engine signed due ok) = 0 := by
  obtain ⟨K, -, proposer, keys⟩ := Internal.block_step_gross_keys genesis apart shared fulu early
    (engine := engine) (signed := signed) (due := due) (ok := ok)
  by_contra nonzero
  rcases keys v (Nat.pos_of_ne_zero nonzero) with member | ⟨altair, w, found, seat⟩
  · obtain ⟨p, read, same⟩ := proposer v member
    have active := (Run.lookaheadActive covers genesis shared early).proposer_active fulu read
    rw [same] at active
    obtain ⟨w, found, isActive⟩ := isActiveAt_eq_true_iff.mp active
    rw [notActive w found] at isActive
    exact Bool.false_ne_true isActive
  · have run := shared.snoc (Step.block engine signed due ok)
    obtain ⟨j, w', found', keyed, assigned, late⟩ :=
      (run.syncCommittee_activation_bounded genesis altair).1 w.pubkey seat
    obtain rfl := (run.pubkeysDistinct genesis).index_eq found found' keyed.symm
    obtain rfl := Option.some.inj (found.symm.trans found')
    rcases notSeated w found with far | later
    · exact assigned far
    · have bound : w.activationEpoch.toNat ≤ (getCurrentEpoch t).toNat + 1 := late
      omega

/-- A key that is idle along a prefix of C's run has a balance at most its credits there. -/
private theorem key_idle_walk (h : Setting config checks g split fin pulled anc counted V)
    {z : ForkedBeaconState preset} (v : ℕ) (small : v < 2 ^ 64) (highC : ℕ)
    (zEarly : z.fork < .glamsterdam)
    (zHigh : (getCurrentEpoch z.state).toNat ≤ highC + 1)
    -- The key is two epochs from its activation at the end of the run.
    (ahead : ∀ m : ForkedBeaconState preset, Run config checks m z → ∀ w : Validator,
      m.state.validators.data[v]? = some w → w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch m.state).toNat + 1 < w.activationEpoch.toNat)
    -- The key is absent at the start.
    (start : actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v = 0) :
    ∀ {m : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ m),
      -- No block step gives it a gross credit, since it is neither a proposer nor on a seat.
      Run config checks m z → Internal.grossScan v highC pre = 0 ∧ actualBalanceAt m v ≤
        -- A slot step credits it the credits of deposits and consolidations, since it is idle.
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v highC pre) +
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v highC pre)
          := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- The key is not active at any epoch up to the current one, at a state of the rest of the run.
  have inactive : ∀ m : ForkedBeaconState preset, Run config checks m z → ∀ w : Validator,
      m.state.validators.data[v]? = some w → ∀ e : Epoch,
        e.toNat ≤ (getCurrentEpoch m.state).toNat → isActiveValidator w e = false := by
    intro m run w found e le
    by_contra active
    simp only [Bool.not_eq_false] at active
    have lowEpoch := UInt64.le_iff_toNat_le.mp (activationLe_of_active active)
    have := ahead m run w found (Consensus.Internal.assigned_of_active active)
    omega
  intro m pre
  induction pre with
  | nil =>
    intro _
    rw [start]
    exact ⟨rfl, Nat.zero_le _⟩
  | @snoc middle last pre step ih =>
    intro post
    have shared : Run config checks g middle := (toFin.append fromFin).append pre
    have afterStep : Run config checks middle z := (Run.nil.snoc step).append post
    have middleZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps afterStep.chainSteps)
    have middleFork := fork_le_of_chainSteps afterStep.chainSteps
    have lastFork := fork_le_of_chainSteps post.chainSteps
    have selected : (getCurrentEpoch middle.state).toNat ≤ highC + 1 := by omega
    rw [Internal.grossScan_snoc, Internal.creditScan_snoc, Internal.creditScan_snoc]
    simp only [selected, ↓reduceIte]
    obtain ⟨noGross, before⟩ := ih afterStep
    have lastEarly : last.fork < .glamsterdam := Nat.lt_of_le_of_lt lastFork zEarly
    cases step with
    | block engine signed due ok =>
      have gross := Internal.block_balance_le_gross (engine := engine) (signed := signed) (due :=
        due)
        (ok := ok) shared h.genesis lastEarly
        (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) v
      have zero := block_idle_step (engine := engine) (signed := signed) (due := due) (ok := ok)
        h.genesis h.parameters.lookahead h.facts.covers shared
        (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)) lastEarly v
        (fun w found => inactive _ afterStep w found _ (Nat.le_refl _))
        (fun w found => by
          by_cases assigned : w.activationEpoch = FAR_FUTURE_EPOCH
          · exact .inl assigned
          · exact .inr (ahead _ post w found assigned))
      exact ⟨by omega, by omega⟩
    | slot ok =>
      have middleElectra : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      have middleEarly : middle.fork < .glamsterdam := Nat.lt_of_le_of_lt middleFork zEarly
      have known : v < middle.state.validators.data.size ∨ BalancesMatch middle.state := by
        by_cases inside : v < middle.state.validators.data.size
        · exact .inl inside
        · exact .inr (Run.invariant (Genesis.invariant h.genesis) shared).balancesMatch
      have idle : v.toUInt64 ∉ getActiveValidatorIndices middle.state
          (getPreviousEpoch middle.state) := by
        intro active
        obtain ⟨w, found, isActive⟩ :=
          (mem_getActiveValidatorIndices (middle.state.validators.bound middleEarly)).mp active
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small] at found
        have previous := getPreviousEpoch_toNat middle.state
        rw [inactive middle afterStep w found _ (by omega)] at isActive
        exact Bool.false_ne_true isActive
      have noCredit : Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s =
        .sync))
          (fun _ => false) v (Step.slot ok : Step config checks middle last) = 0 := by
        simp [Internal.stepCredit]
      have step := slot_idle_step shared h.genesis ok lastEarly middleElectra v known idle
      exact ⟨by omega, by omega⟩

/-- A voter that is active at a state has its activation assigned and reached. -/
theorem activated_of_activeVoters (early : fork < .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ activeVoters s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧ w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
      w.activationEpoch ≤ getCurrentEpoch s := by
  obtain ⟨w, found, active⟩ := Internal.active_of_activeVoters early member
  exact ⟨w, found, Consensus.Internal.assigned_of_active active, activationLe_of_active active⟩

/-- A voter of the quorum has its activation assigned and reached.

The quorum holds the keys that are active at the current or the previous epoch. -/
theorem activated_of_quorum (early : fork < .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ countedQuorum s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧ w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
      w.activationEpoch ≤ getCurrentEpoch s := by
  have listed := (Finset.mem_filter.mp (member : v ∈ quorumVoters s)).1
  rw [List.mem_toFinset, List.mem_append] at listed
  rcases listed with now | before
  · exact Internal.activated_of_activeVoters early (by simpa [activeVoters] using now)
  · obtain ⟨w, found, active⟩ :=
      (mem_getActiveValidatorIndices (s.validators.bound early)).mp before
    exact ⟨w, found, Consensus.Internal.assigned_of_active active,
      UInt64.le_trans (activationLe_of_active active) (getPreviousEpoch_le s)⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C activates has its activation before its exit. -/
private theorem activated_ordered (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted) :
    ∀ vy, counted.validators.data[v.toNat]? = some vy →
      vy.activationEpoch.toNat < vy.exitEpoch.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨w, foundC, neFar, -⟩ := activated
  intro vy found
  obtain rfl := Option.some.inj (found.symm.trans foundC)
  have farToNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have bound := vy.activationEpoch.toNat_lt
  have notFar : vy.activationEpoch.toNat ≠ 2 ^ 64 - 1 := fun same =>
    neFar (UInt64.toNat_inj.mp (by rw [same]; rfl))
  by_cases exit : vy.exitEpoch = FAR_FUTURE_EPOCH
  · rw [exit]
    omega
  · have gap := (toFin.append (fromFin.append tailC)).exit_activation_gap h.genesis v.toNat vy
      found exit
    omega

/-- A key activated by C and absent at the split holds the activation reserve on C's run. -/
theorem created_start (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    -- The key is activated by C, before it exits, and absent at the split.
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) :
    -- The run from the split reaches that state first, and then C.
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks ⟨fork, split⟩ z)
      (post : Run config checks z ⟨fork, counted⟩), tailC = pre.append post ∧
      z.fork < .glamsterdam ∧ z.fork ≤ fork ∧
      (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch counted).toNat ∧
      v.toNat < z.state.validators.data.size ∧
      -- At that state the key's balance is at least `MAX_EFFECTIVE_BALANCE`.
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z v.toNat ∧
      -- Its effective balance is within the downward band of its balance, and at least that bound.
      effectiveAt z v.toNat ≤ actualBalanceAt z v.toNat + preset.downwardBand ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ effectiveAt z v.toNat ∧
      -- The key is idle before that state.
      --
      -- So its balance is at most the credits that the scans count.
      actualBalanceAt z v.toNat ≤ Internal.grossScan v.toNat highC pre +
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC pre) +
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v.toNat highC
          pre) ∧ Internal.grossScan v.toNat highC pre = 0 ∧
      ∀ p ∈ pre.balancePath, ∀ w : Validator, p.state.validators.data[v.toNat]? = some w →
        w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch p.state).toNat + 1 < w.activationEpoch.toNat := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- The key is activated at C, before its exit, and absent at the split.
  obtain ⟨w, foundC, neFar, lowC⟩ := activated
  have ordered := activated_ordered h fromFin tailC ⟨w, foundC, neFar, lowC⟩
  have splitAbsent : split.validators.data[v.toNat]? = none :=
    Array.getElem?_eq_none absent
  have pending : ∀ u, (⟨fork, split⟩ : ForkedBeaconState preset).state.validators.data[v.toNat]? =
      some u → (getCurrentEpoch (⟨fork, split⟩ : ForkedBeaconState preset).state).toNat + 1 <
        u.activationEpoch.toNat := fun u found => by
    simp only [splitAbsent] at found
    cases found
  obtain ⟨z, pre, post, v0, vy, splitEq, found0, foundY, sameAct, actEq, -⟩ :=
    Internal.Run.start_state tailC h.window v.toNat pending ⟨w, foundC, neFar, lowC⟩ ordered
  obtain rfl := Option.some.inj (foundY.symm.trans foundC)
  have actNeFar : v0.activationEpoch ≠ FAR_FUTURE_EPOCH := fun same =>
    neFar (sameAct.symm.trans same)
  have zFork : z.fork ≤ fork := fork_le_of_chainSteps post.chainSteps
  have zEarly : z.fork < .glamsterdam := Nat.lt_of_le_of_lt zFork h.early
  have actZ : (getCurrentEpoch z.state).toNat + 2 = v0.activationEpoch.toNat := by
    rw [sameAct]
    exact actEq
  -- At that state the key holds the activation reserve, which is positive.
  obtain ⟨-, funded, hysteresis, reserve⟩ :=
    Internal.Run.funded_at_start shared h.genesis h.caps h.aligned electra pre zEarly v.toNat found0
      actNeFar actZ
  have zCounted : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch counted).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  -- The key has no balance at the start, and no credit scan counts a step before that state.
  have startZero : actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat = 0 := by
    have matched : split.balances.data.size = split.validators.data.size :=
      (Run.invariant (Genesis.invariant h.genesis) shared).balancesMatch
    simp only [actualBalanceAt, Array.getElem?_eq_none (show
      split.balances.data.size ≤ v.toNat by omega), Option.map_none,
      Option.getD_none]
  -- the key is not yet active at a state before the one that schedules it
  have ahead : ∀ m : ForkedBeaconState preset, Run config checks m z → ∀ w : Validator,
      m.state.validators.data[v.toNat]? = some w → w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch m.state).toNat + 1 < w.activationEpoch.toNat :=
    fun m run w found assigned => by
      obtain ⟨later, foundLater, life⟩ := run.registryLifecycle.validators v.toNat w found
      have same : later = v0 := Option.some.inj (foundLater.symm.trans found0)
      subst same
      have act := life.activationEpoch assigned
      have mZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps run.chainSteps)
      rw [← act]
      omega
  obtain ⟨noGross, walk⟩ := key_idle_walk h v.toNat v.toNat_lt highC zEarly (by omega) ahead
    startZero pre Run.nil
  refine ⟨z, pre, post, splitEq, zEarly, zFork, zCounted,
    (Array.getElem?_eq_some_iff.mp found0).1, funded, hysteresis, reserve, by omega, noGross,
    fun p member => ?_⟩
  obtain ⟨-, r2, -⟩ := Internal.balancePath_endpoint pre (Run.nil : Run config checks z z) zFork
    member
  exact ahead p r2

/-- The activation reserve is positive. -/
theorem maxEffectiveBalance_pos
    (h : Setting config checks g split fin pulled anc counted V) :
    0 < preset.MAX_EFFECTIVE_BALANCE.toNat := by
  have newKey := h.facts.newKey .fusaka
  have size := h.facts.incrementSize
  by_contra zero
  have none : preset.MAX_EFFECTIVE_BALANCE.toNat = 0 := by omega
  rw [none] at newKey
  simp only [Nat.mul_zero, Nat.zero_div, Nat.zero_sub, Nat.le_zero] at newKey
  omega

/-- The consolidation credits of a run after the shared segment fit the due entries.

The keys of a set are credited at most the caps of the due entries of X's queue that name them.

The run from X to the end is the shared segment and then the run from the split.

The horizon is within the withdrawal delay of X, as `shallow` says. -/
theorem cons_due_bound (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {z : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, z⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch z).toNat ≤ high + 1)
    (highLe : high ≤ (getCurrentEpoch pulled).toNat)
    {events eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayed : tail.balanceEvents high = .ok events) (T : Finset ValidatorIndex) :
    ∑ v ∈ T, Internal.consAmt (eventsF ++ events) v.toNat ≤
      ((Internal.dueList fin (Nat.le_trans (by decide) h.fulu) high T).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
  classical
  have shallow := h.shallow
  obtain ⟨shared⟩ := h.toFin
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have bound := Internal.Run.consolidation_credits_le_X_targets (config := config)
    (checks := checks) shared h.genesis h.caps (fromFin.append tail)
    (Nat.le_trans (by decide) h.fulu) h.early high
    (Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed) endEpoch
    (by simp only; omega) (by omega) (T.image UInt64.toNat)
  have injective : Function.Injective UInt64.toNat := fun _ _ same => UInt64.toNat_inj.mp same
  simp only [injective.mem_finset_image] at bound
  rw [← Finset.sum_image (f := fun i => Internal.consAmt (eventsF ++ events) i)
    (fun _ _ _ _ e => UInt64.toNat_inj.mp e)]
  exact bound

/-- The keys that a consolidation of X's queue credits on C's run are at most its due entries.

Each such key is the target of a due entry, and each entry names one target. -/
theorem cons_keys_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    {eventsF eventsC : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents highC = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) (T : Finset ValidatorIndex)
    (credited : ∀ v ∈ T, 0 < Internal.consAmt eventsC v.toNat) :
    T.card ≤ (pinTerms config pulled anc fin).consolidationsXCount := by
  classical
  have shallow := h.shallow
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have each (v : ValidatorIndex) (hv : v ∈ T) : 1 ≤ Internal.dueAt fin highC {v} := by
    have bound := Internal.cons_due_bound h fromFin tailC highC endEpochC highLe replayedF replayedC
      {v}
    rw [Internal.dueAt_eq fin electra highC]
    by_contra none
    have empty : Internal.dueList fin electra highC {v} = [] := List.length_eq_zero_iff.mp (by
      omega)
    simp only [Finset.sum_singleton, empty, List.map_nil, List.sum_nil] at bound
    have positive := credited v hv
    unfold Internal.consAmt at positive bound
    simp only [List.filter_append, List.map_append, List.sum_append] at bound
    omega
  calc T.card = ∑ v ∈ T, 1 := by simp
    _ ≤ ∑ v ∈ T, Internal.dueAt fin highC {v} := Finset.sum_le_sum each
    _ = Internal.dueAt fin highC T := dueAt_sum fin electra highC T
    _ ≤ (Internal.dueList fin electra (getCurrentEpoch pulled).toNat T).length := by
      rw [Internal.dueAt_eq fin electra highC]
      exact dueList_length_mono fin electra highLe T
    _ ≤ _ := by
      unfold pinTerms
      dsimp only
      simp only [shallow, electra, ↓reduceIte, ↓reduceDIte]
      simpa using Internal.dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat T fun _ =>
        1

/-- The consolidation budget sums the source caps of due entries in X's queue.

It is zero beyond the withdrawal delay, so the setting's `shallow` selects the entries. -/
theorem consolidationsX_eq (h : Setting config checks g split fin pulled anc counted V)
    (electra : .pectra ≤ fork) :
    (pinTerms config pulled anc fin).consolidationsX =
      (((((fin.pendingConsolidations electra).data.toList.filterMap fun c =>
        fin.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed &&
            decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
            fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)).sum := by
  have shallow := h.shallow
  unfold pinTerms
  dsimp only
  simp only [shallow, electra, ↓reduceIte, ↓reduceDIte]

/-- The source caps are whole increments, so their sum is too. -/
theorem consolidationsX_aligned
    (h : Setting config checks g split fin pulled anc counted V) :
    (pinTerms config pulled anc fin).consolidationsX % preset.EFFECTIVE_BALANCE_INCREMENT.toNat =
      0 := by
  rw [Internal.consolidationsX_eq h (Nat.le_trans (by decide) h.fulu)]
  apply Nat.mod_eq_zero_of_dvd
  refine List.dvd_sum fun x hx => ?_
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  have := congrArg UInt64.toNat (withdrawalMaxEffectiveBalance_aligned (fork := fork) h.aligned v)
  exact Nat.dvd_of_mod_eq_zero (by simpa [UInt64.toNat_mod] using this)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key with no due consolidation entry takes no consolidation credit on C's run or before it.

The horizon of the due entries is cut to R's epoch, which C's replay does not read. -/
theorem consAmt_zero (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    {ending : BeaconState preset fork}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, ending⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch ending).toNat ≤ highC + 1)
    (near : (getCurrentEpoch ending).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (none : Internal.dueAt fin highC {v} = 0) :
    Internal.consAmt eventsF v.toNat + Internal.consAmt eventsC v.toNat = 0 := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have later := UInt64.le_iff_toNat_le.mp h.later
  have ahead : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch ending).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
  obtain ⟨hc, hhc⟩ : ∃ hc, hc = min highC (getCurrentEpoch pulled).toNat := ⟨_, rfl⟩
  rw [balanceEvents_eq_of_endpoint_le fromFin (localHigh := hc) (by simp only; omega)
    (by simp only; omega)] at replayedF
  rw [balanceEvents_eq_of_endpoint_le tailC (localHigh := hc) (by simp only; omega)
    (by simp only; omega)] at replayedC
  have bound := Internal.cons_due_bound h fromFin tailC hc (by omega) (by omega) replayedF replayedC
    {v}
  have empty : Internal.dueList fin electra hc {v} = [] := List.length_eq_zero_iff.mp (by
    have := dueList_length_mono fin electra (show hc ≤ highC by omega) {v}
    rw [Internal.dueAt_eq fin electra highC] at none
    omega)
  simp only [Finset.sum_singleton, empty, List.map_nil, List.sum_nil] at bound
  unfold Internal.consAmt at bound ⊢
  simp only [List.filter_append, List.map_append, List.sum_append] at bound
  omega

/-- The caps of a list of validators are at least the maximum effective balance each. -/
theorem cap_floor_sum (h : Setting config checks g split fin pulled anc counted V)
    (l : List Validator) :
    preset.MAX_EFFECTIVE_BALANCE.toNat * l.length ≤
      (l.map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
  have := List.length_nsmul_le_sum
    (l.map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    preset.MAX_EFFECTIVE_BALANCE.toNat (by
      simp only [List.mem_map]
      rintro _ ⟨v, -, rfl⟩
      exact UInt64.le_iff_toNat_le.mp
        (Internal.minimum_cap h.caps.activation h.caps.compounding v))
  simpa [smul_eq_mul, Nat.mul_comm] using this

/-- A sum over a subset can be extended by zero to use the ambient set's pointwise bounds. -/
theorem sum_eq_costKeys {M : Type*} [AddCommMonoid M] {S W : Finset ValidatorIndex}
    (sub : S ⊆ W) (f : ValidatorIndex → M) :
    ∑ v ∈ S, f v = ∑ v ∈ W, if v ∈ S then f v else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr sub]

/-- The consolidation credits of C's branch fit the caps of due entries at the finalized state.

The consolidation charge is zero beyond the withdrawal delay, so this bound needs a shallow call. -/
theorem budget_consolidations_base
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    -- The bound below needs `high` to be at most the epoch of the call.
    --
    -- It also needs X, the finalized block's state, to be within the withdrawal delay.
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat) :
    -- The credit bound sums the consolidation amounts for the selected targets.
    --
    -- The bound is the caps at X of the due entries of X's queue that name them.
    --
    -- It is over the whole run from X.
    --
    -- The run to R's state bounds the credits to V the same way.
    --
    -- `V` and the staying, previous-only and joined keys are disjoint.
    --
    -- So the sum over their union is at most the sum of the source caps for the due entries.
    (((∑ v ∈ (stayingKeys pulled counted V), Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.consAmt eventsC v.toNat) +
      -- A key of `V` and a previous-only key weigh three, and the others one.
      3 * (∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, Internal.consAmt events v.toNat) +
      -- The newly slashed keys are slashed at C.
      --
      -- So they are not staying, previous-only or joined keys, and not in `V`.
      --
      -- Their credits join those of the staying, previous-only and joined keys in the bound.
      --
      -- Take a whistleblower's share of the amounts of the newly and created slashed keys.
      --
      -- That share is at most the amounts.
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split, Internal.consAmt eventsC
        v.toNat) +
      -- A due entry that names a newly or created slashed key adds its band.
      (∑ v ∈ newlySlashed pulled counted split, Internal.bandX fin highC v.toNat) +
      -- The created slashed keys are created after R's registry and slashed at C.
      --
      -- So they are in none of those sets either.
      --
      -- Their credits join the bound with the same share and bands.
      Internal.wShare preset fork (∑ v ∈ createdSlashed counted split, Internal.consAmt eventsC
        v.toNat) +
      (∑ v ∈ createdSlashed counted split, Internal.bandX fin highC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
          Internal.consAmt eventsF v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.bandX fin high
          v.toNat)) +
      -- The target's rise includes the rounding from each applied entry.
      --
      -- Each due entry in X's queue adds one upward rounding band.
      preset.upwardBand * (Internal.dueAt fin highC (stayingKeys pulled counted V) +
        Internal.dueAt fin highC (joinedKeys pulled counted) + 3 * Internal.dueAt fin highC
          (previousOnlyKeys counted V) +
        3 * Internal.dueAt fin high V) ≤
        -- An entry is charged its cap at X, which is at least `MAX_EFFECTIVE_BALANCE`.
        --
        -- So three bands are at most three tenths of it.
        --
        -- The reserve rounds the consolidation charge `3.3 · X` up to `(33 · X + 9) / 10`.
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10) ∧
      (∑ v ∈ (stayingKeys pulled counted V), Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ (joinedKeys pulled counted), Internal.consAmt eventsC v.toNat) +
        3 * (∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
  -- The run from the finalized block's state X to C's state has the run from the split as its tail.
  classical
  have shallow := h.shallow
  have early := h.early
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  obtain ⟨eventsFin, replayedFin⟩ := fromFin.balanceEvents_ok early highC
  have sameF : eventsFin = eventsF := by
    have splitC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
    simp only at splitC
    have same := DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le fromFin
      (high := highC) (localHigh := high)
      (by simp only; omega) (by simp only; omega)
    rw [same, replayedF] at replayedFin
    exact (Except.ok.inj replayedFin).symm
  subst sameF
  obtain ⟨Kall, hKall⟩ : ∃ K : Finset ValidatorIndex,
      K = stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted ∪
        newlySlashed pulled counted split ∪
        createdSlashed counted split := ⟨_, rfl⟩
  have boundC := Internal.cons_due_bound h fromFin tailC highC endEpochC highLe replayedFin
    replayedC Kall
  have boundR := Internal.cons_due_bound h fromFin tail high endEpoch highLeR replayedF replayed V
  -- The shared segment's amounts of the newly slashed keys that exited before the finalized epoch.
  set S' := (newlySlashed pulled counted split).filter fun v =>
    (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true with hS'
  have subS : S' ⊆ Kall := fun v hv => by
    rw [hKall]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mp hv).1)
  have amountC : (∑ v ∈ Kall, Internal.consAmt eventsC v.toNat) + (∑ v ∈ S', Internal.consAmt
    eventsFin v.toNat) ≤
      ((Internal.dueList fin electra highC Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    rw [sum_eq_costKeys subS, ← Finset.sum_add_distrib]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundC
    simp only [Internal.consAmt, List.filter_append, List.map_append, List.sum_append]
    split_ifs <;> omega
  have amountR : (∑ v ∈ V, Internal.consAmt events v.toNat) ≤
      ((Internal.dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundR
    simp only [Internal.consAmt, List.filter_append, List.map_append, List.sum_append]
    exact Nat.le_add_left _ _
  -- The target sets are disjoint.
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  have d456 : Disjoint (stayingKeys pulled counted V ∪ previousOnlyKeys counted V) (joinedKeys
      pulled
    counted) :=
    Finset.disjoint_union_left.mpr ⟨d46, d56⟩
  obtain ⟨dS, dVS⟩ := newlySlashed_disjoint h
  obtain ⟨dC, dVC⟩ := createdSlashed_disjoint h
  have dKV : Disjoint Kall V := by
    rw [hKall, Finset.disjoint_left]
    intro v hk hv
    simp only [Finset.mem_union] at hk
    rcases hk with (((h4 | h5) | h6) | hS) | hC
    · simp only [stayingKeys, Finset.mem_filter] at h4
      exact h4.2.2.2 hv
    · simp only [previousOnlyKeys, Finset.mem_filter] at h5
      exact h5.2.2 hv
    · simp only [joinedKeys, Finset.mem_filter] at h6
      exact h6.2.2 (h.voting v hv).1
    · exact Finset.disjoint_left.mp dVS hv hS
    · exact Finset.disjoint_left.mp dVC hv hC
  -- The amounts and the entries split over the three sets of C's keys.
  have splitAmount : (∑ v ∈ Kall, Internal.consAmt eventsC v.toNat) =
      (∑ v ∈ stayingKeys pulled counted V, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ previousOnlyKeys counted V, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ joinedKeys pulled counted, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ newlySlashed pulled counted split, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ createdSlashed counted split, Internal.consAmt eventsC v.toNat) := by
    rw [hKall, Finset.sum_union dC, Finset.sum_union dS, Finset.sum_union d456,
      Finset.sum_union d45]
  have splitEntries (H : ℕ) : (Internal.dueList fin electra H Kall).length =
      (Internal.dueList fin electra H (stayingKeys pulled counted V)).length +
        (Internal.dueList fin electra H (previousOnlyKeys counted V)).length +
        (Internal.dueList fin electra H (joinedKeys pulled counted)).length +
        (Internal.dueList fin electra H (newlySlashed pulled counted split)).length +
        (Internal.dueList fin electra H (createdSlashed counted split)).length := by
    rw [hKall, dueList_length_union fin electra H dC, dueList_length_union fin electra H dS,
      dueList_length_union fin electra H d456, dueList_length_union fin electra H d45]
  -- The caps of the due entries are at least `MAX_EFFECTIVE_BALANCE` each.
  have floorC := Internal.cap_floor_sum h (Internal.dueList fin electra (getCurrentEpoch
    pulled).toNat Kall)
  have floorR := Internal.cap_floor_sum h (Internal.dueList fin electra high V)
  -- Both runs charge entries of X's queue, at most those that `consolidationsX` counts.
  have total : ((Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum +
      ((Internal.dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum ≤
      (pinTerms config pulled anc fin).consolidationsX := by
    have hcX := Internal.consolidationsX_eq h electra
    have laterR := Internal.dueList_sum_mono fin electra highLeR V
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have union := dueList_sum_union fin electra (getCurrentEpoch pulled).toNat dKV
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have all := Internal.dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat (Kall ∪ V)
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    rw [hcX]
    omega
  have laterC := Internal.dueList_sum_mono fin electra highLe Kall
    (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
  -- Whole, the due caps of C's keys fit `consolidationsX`, so the weighted amounts fit three of it.
  have whole : (∑ v ∈ (stayingKeys pulled counted V), Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
    omega
  refine ⟨?_, whole⟩
  have bandLen : (Internal.dueList fin electra highC (newlySlashed pulled counted split)).length +
      (Internal.dueList fin electra highC (createdSlashed counted split)).length +
      (Internal.dueList fin electra highC (stayingKeys pulled counted V)).length +
      (Internal.dueList fin electra highC (joinedKeys pulled counted)).length +
      3 * (Internal.dueList fin electra highC (previousOnlyKeys counted V)).length +
      (Internal.dueList fin electra high S').length ≤
        3 * (Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).length := by
    have union := splitEntries (getCurrentEpoch pulled).toNat
    have m4 := dueList_length_mono fin electra highLe (stayingKeys pulled counted V)
    have m5 := dueList_length_mono fin electra highLe (previousOnlyKeys counted V)
    have m6 := dueList_length_mono fin electra highLe (joinedKeys pulled counted)
    have mS := dueList_length_mono fin electra highLe (newlySlashed pulled counted split)
    have mC := dueList_length_mono fin electra highLe (createdSlashed counted split)
    have mF := (dueList_length_mono fin electra highLeR S').trans
      (dueList_length_subset fin electra (getCurrentEpoch pulled).toNat
        (Finset.filter_subset _ _ : S' ⊆ newlySlashed pulled counted split))
    omega
  have shareF := Internal.wShare_le (fork := fork) h.facts (∑ v ∈ S', Internal.consAmt eventsFin
    v.toNat)
  have shareS := Internal.wShare_le (fork := fork) h.facts
    (∑ v ∈ newlySlashed pulled counted split, Internal.consAmt eventsC v.toNat)
  have shareC := Internal.wShare_le (fork := fork) h.facts
    (∑ v ∈ createdSlashed counted split, Internal.consAmt eventsC v.toNat)
  rw [Internal.bandX_sum fin electra highC (newlySlashed pulled counted split),
    Internal.bandX_sum fin electra highC (createdSlashed counted split), Internal.bandX_sum fin
        electra
      high S']
  rw [Internal.dueAt_eq fin electra highC, Internal.dueAt_eq fin electra highC, Internal.dueAt_eq
    fin electra highC,
    Internal.dueAt_eq fin electra highC, Internal.dueAt_eq fin electra highC, Internal.dueAt_eq fin
      electra high,
    Internal.dueAt_eq fin electra high]
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  generalize (Internal.dueList fin electra highC (stayingKeys pulled counted V)).length = d4 at *
  generalize (Internal.dueList fin electra highC (previousOnlyKeys counted V)).length = d5 at *
  generalize (Internal.dueList fin electra highC (joinedKeys pulled counted)).length = d6 at *
  generalize (Internal.dueList fin electra highC (newlySlashed pulled counted split)).length =
      dS' at *
  generalize (Internal.dueList fin electra highC (createdSlashed counted split)).length = dC' at *
  generalize (∑ v ∈ newlySlashed pulled counted split, Internal.consAmt eventsC v.toNat) = aS at *
  generalize Internal.wShare preset fork aS = wS at *
  generalize (∑ v ∈ createdSlashed counted split, Internal.consAmt eventsC v.toNat) = aC at *
  generalize Internal.wShare preset fork aC = wC at *
  generalize (Internal.dueList fin electra high S').length = dF at *
  generalize (∑ v ∈ S', Internal.consAmt eventsFin v.toNat) = aF at *
  generalize Internal.wShare preset fork aF = wF at *
  generalize (Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).length = dK at *
  generalize (Internal.dueList fin electra high V).length = dV at *
  generalize ((Internal.dueList fin electra highC Kall).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PK' at *
  generalize ((Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PK at *
  generalize ((Internal.dueList fin electra high V).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PV at *
  generalize (pinTerms config pulled anc fin).consolidationsX = cX at *
  have bandsK : preset.upwardBand * dS' + preset.upwardBand * dC' +
      preset.upwardBand * (d4 + d6 + 3 * d5 + 3 * dV) + preset.upwardBand * dF ≤
        3 * (preset.upwardBand * (dK + dV)) := by
    have : dS' + dC' + (d4 + d6 + 3 * d5 + 3 * dV) + dF ≤ 3 * (dK + dV) := by omega
    calc preset.upwardBand * dS' + preset.upwardBand * dC' +
          preset.upwardBand * (d4 + d6 + 3 * d5 + 3 * dV) + preset.upwardBand * dF
        = preset.upwardBand * (dS' + dC' + (d4 + d6 + 3 * d5 + 3 * dV) + dF) := by ring
      _ ≤ preset.upwardBand * (3 * (dK + dV)) := Nat.mul_le_mul_left _ this
      _ = 3 * (preset.upwardBand * (dK + dV)) := by ring
  have bandsM : 10 * (preset.upwardBand * (dK + dV)) ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat * dK + preset.MAX_EFFECTIVE_BALANCE.toNat * dV := by
    calc 10 * (preset.upwardBand * (dK + dV))
        = (10 * preset.upwardBand) * (dK + dV) := by ring
      _ ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * (dK + dV) := Nat.mul_le_mul_right _ h.facts.band
      _ = preset.MAX_EFFECTIVE_BALANCE.toNat * dK + preset.MAX_EFFECTIVE_BALANCE.toNat * dV :=
        Nat.mul_add _ _ _
  omega

/-- The consolidation credits of the third window, with created slashed and shared segment shares.

The shared segment's shares are those of newly slashed keys exited before the finalized epoch. -/
theorem budget_consolidations (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat) :
    ((∑ v ∈ (stayingKeys pulled counted V), Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (previousOnlyKeys counted V), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, Internal.consAmt events v.toNat) +
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split, Internal.consAmt eventsC
        v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split, Internal.bandX fin highC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ createdSlashed counted split, Internal.consAmt eventsC
        v.toNat) +
      (∑ v ∈ createdSlashed counted split, Internal.bandX fin highC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
          Internal.consAmt eventsF v.toNat) +
      (∑ v ∈ newlySlashed pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.bandX fin high
          v.toNat)) +
      preset.upwardBand * (Internal.dueAt fin highC (stayingKeys pulled counted V) +
        Internal.dueAt fin highC (joinedKeys pulled counted) + 3 * Internal.dueAt fin highC
          (previousOnlyKeys counted V) +
        3 * Internal.dueAt fin high V) ≤
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10 := by
  exact (Internal.budget_consolidations_base h fromFin tail high endEpoch replayed replayedF highLeR
    tailC highC
    endEpochC replayedC highLe).1

/-- The joined keys whose exit started on R's branch after the split. -/
theorem budget_exitedR :
    (∑ v ∈ (joinedKeys pulled counted) with (pinTerms config pulled anc fin).exitedRB v.toNat =
      true,
      (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤
        (pinTerms config pulled anc fin).exitedR := by
  rw [Internal.exitedR_eq]
  refine voters_sum_le (fun i => balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
    fun v hv => ?_
  have flag := (Finset.mem_filter.mp hv).2
  obtain ⟨w, found⟩ := Internal.validator_of_flag (state := pulled) (i := v.toNat) (Or.inl flag)
  exact Internal.mem_positions_filter config pulled anc fin found flag

/-- Three sets with disjoint keys: the weights one, three and one are at most three. -/
theorem weighted_le {A B C : Finset ValidatorIndex} (f : ValidatorIndex → ℕ)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C) :
    ∑ v ∈ A, f v + 3 * ∑ v ∈ B, f v + ∑ v ∈ C, f v ≤ 3 * ∑ v ∈ A ∪ B ∪ C, f v := by
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨ac, bc⟩), Finset.sum_union ab]
  omega

/-- The branch slashing test uses the key's slashed flag and withdrawable epoch. -/
theorem slashedRB_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (i : ℕ) :
    (pinTerms config state ancestor finalizedState).slashedRB i =
      decide ((((state.validators.data[i]?).map (·.slashed)).getD false = true) ∧
        ((state.validators.data[i]?).any fun v => decide (
          ancestor.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
            v.withdrawableEpoch.toNat)) = true) := rfl

/-- A key that the pin counts as slashed on this branch holds a position of the registry. -/
private theorem slashedRB_lt (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ} (h : (pinTerms config state ancestor finalizedState).slashedRB i = true) :
    i < state.validators.data.size := by
  by_contra out
  have none : state.validators.data[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt out)
  rw [Internal.slashedRB_eq] at h
  simp [none] at h

/-- A slashed key counts toward the branch charge if its withdrawable epoch is late enough.

That epoch must be a slashing vector past the finalized epoch. -/
theorem slashedRB_of_withdrawable (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) {i : ℕ} {w : Validator}
    (found : state.validators.data[i]? = some w) (slashed : w.slashed = true)
    (late : ancestor.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      w.withdrawableEpoch.toNat) :
    (pinTerms config state ancestor finalizedState).slashedRB i = true := by
  rw [Internal.slashedRB_eq]
  simpa [found, slashed] using late

/-- A key unslashed at `c` and slashed later on a run has a late withdrawable epoch.

That epoch is at least `c`'s epoch plus the length of the slashings vector. -/
private theorem withdrawable_of_clean_run (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (i : ℕ)
    {c : BeaconState preset fork} (inside : i < c.validators.data.size)
    (clean : ∀ u, c.validators.data[i]? = some u → u.slashed = false)
    {a : ForkedBeaconState preset} (run : Run config checks ⟨fork, c⟩ a)
    (u : Validator)
    (foundU : a.state.validators.data[i]? = some u) (flag : u.slashed = true) :
    (getCurrentEpoch c).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      u.withdrawableEpoch.toNat := by
  obtain ⟨uC, foundC⟩ : ∃ uC, c.validators.data[i]? = some uC :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have lower := (run.newly_slashed_withdrawableEpoch caps.activation caps.compounding
    delay i uC u foundC foundU (clean uC foundC) flag).2
  simp only at lower
  exact lower

/-- The branch charge counts a key unslashed at the split and slashed at R.

R slashes it after the split, so its withdrawable epoch is a slashing vector past the split's. -/
theorem slashedRB_of_newly_slashed
    (h : Setting config checks g split fin pulled anc counted V) {i : ℕ} {s w : Validator}
    (foundS : split.validators.data[i]? = some s)
    (foundP : pulled.validators.data[i]? = some w) (cleanS : s.slashed = false)
    (slashedP : w.slashed = true) :
    (pinTerms config pulled anc fin).slashedRB i = true := by
  obtain ⟨tail⟩ := h.toPulled
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have delayed := withdrawable_of_clean_run h.caps (Internal.Setting.delay h) i
    (Array.getElem?_eq_some_iff.mp foundS).1
    (fun u found => by rw [foundS] at found; cases found; exact cleanS) tail w foundP
    slashedP
  exact Internal.slashedRB_of_withdrawable config pulled anc fin foundP slashedP (by omega)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The exit of a counted voter of the finalized registry is late at R.

The voter is not active at `counted` since an exit before the finalized epoch is excluded.

Its exit at R is then at least the finalized epoch, so it is late for the whole run. -/
theorem voter_late (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (v : ValidatorIndex) (voter : v ∈ countedQuorum counted) :
    ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  classical
  intro wP foundP
  obtain ⟨tailC⟩ := h.toCounted
  have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  have inQ := voter
  simp only [countedQuorum, quorumVoters, Finset.mem_filter, List.mem_toFinset,
      List.mem_append] at inQ
  obtain ⟨listed, -⟩ := inQ
  obtain ⟨uC, foundC, activeC⟩ : ∃ uC, counted.validators.data[v.toNat]? = some uC ∧
      (isActiveValidator uC (getCurrentEpoch counted) = true ∨
        isActiveValidator uC (getPreviousEpoch counted) = true) := by
    rcases listed with now | before
    · obtain ⟨u, foundU, act⟩ := (mem_getActiveValidatorIndices within).mp now
      exact ⟨u, foundU, .inl act⟩
    · obtain ⟨u, foundU, act⟩ := (mem_getActiveValidatorIndices within).mp before
      exact ⟨u, foundU, .inr act⟩
  -- the voter's exit at R is not before the finalized epoch, so it is late for the whole run
  have short := Internal.window_short h
  by_cases exitedFin : wP.exitEpoch.toNat < (getCurrentEpoch fin).toNat
  · exfalso
    obtain ⟨uF', foundF', sameExit⟩ := Internal.exit_kept_of_le_fin h foundP (Nat.le_of_lt
      exitedFin)
    have exitNat : uF'.exitEpoch.toNat = wP.exitEpoch.toNat := congrArg UInt64.toNat sameExit
    have assigned : uF'.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      have far1 := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
      have far2 := congrArg UInt64.toNat far
      omega
    have previous := getPreviousEpoch_toNat counted
    have idle : ∀ e : Epoch, uF'.exitEpoch ≤ e → isActiveValidator uC e = false :=
      fun e reached => by
        have inactive := Internal.inactive_from_exit (fromFin.append tailC) foundF' assigned reached
        cases act : isActiveValidator uC e
        · rfl
        · exact absurd (inactive.symm.trans (isActiveAt_eq_true_iff.mpr ⟨uC, foundC, act⟩))
            Bool.false_ne_true
    rcases activeC with act | act
    · rw [idle (getCurrentEpoch counted) (UInt64.le_iff_toNat_le.mpr (by omega))] at act
      exact Bool.false_ne_true act
    · rw [idle (getPreviousEpoch counted) (UInt64.le_iff_toNat_le.mpr (by omega))] at act
      exact Bool.false_ne_true act
  · omega

/-- A key whose exit at R is at or after the finalized epoch is late for the whole run.

The call's cutoff is within the withdrawal delay of the finalized epoch.

The same restriction applies to a counted voter. -/
theorem late_of_exitAfterFin (h : Setting config checks g split fin pulled anc counted V)
    (i : ℕ) (exitAfterFin : ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch fin).toNat ≤ w.exitEpoch.toNat) :
    ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  intro w found
  have after := exitAfterFin w found
  have short := Internal.window_short h
  omega

/-- A counted voter is unslashed at the split.

It is unslashed at `counted`, and a slashing stays. -/
theorem voter_unslashed (h : Setting config checks g split fin pulled anc counted V)
    (v : ValidatorIndex) (voter : v ∈ countedQuorum counted) :
    (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false := by
  obtain ⟨tailC⟩ := h.toCounted
  have unslashedC := (Finset.mem_filter.mp (voter : v ∈ quorumVoters counted)).2
  obtain ⟨uC, foundC, -, -⟩ := Internal.activated_of_quorum h.early voter
  have cleanC : uC.slashed = false := by simpa [foundC] using unslashedC
  cases foundS : split.validators.data[v.toNat]? with
  | none => rfl
  | some uS =>
    simp [Internal.unslashed_of_run tailC foundS (fun u read => by
      rw [foundC] at read
      cases read
      exact cleanC)]

/-- A key slashed at R after a state of its run, where it is unslashed, is withdrawable late.

It is withdrawable a slashings vector after that state.

The state is at or after the finalized epoch, so the pin counts the slashing. -/
theorem slashed_withdrawable_of_clean
    (h : Setting config checks g split fin pulled anc counted V) {d : BeaconState preset fork}
    (run : Run config checks ⟨fork, d⟩ ⟨fork, pulled⟩) (v : ValidatorIndex)
    (clean : ∀ u, d.validators.data[v.toNat]? = some u → u.slashed = false)
    (inside : v.toNat < d.validators.data.size)
    (finalized : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch d) :
    ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
      anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat := by
  intro wP foundP slashedP
  have newly := withdrawable_of_clean_run h.caps (Internal.Setting.delay h) v.toNat inside clean run
    wP foundP slashedP
  have finalizedNat := UInt64.le_iff_toNat_le.mp finalized
  omega

/-- Under the guard, the window from the finalized epoch through R's horizon is under half a vector.

It is the short window of the guard, read at R's horizon. -/
theorem depthFin_lt_half (h : Setting config checks g split fin pulled anc counted V) :
    (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat <
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, short, _⟩ := id h.guard
  change (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat + 2 <
    preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 at short
  omega

/-- A step that slashes a key stays in its epoch.

A slot step keeps each slashed flag, and a block keeps the slot. -/
private theorem step_slash_epoch {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork) (i : ℕ)
    (clean : (slashedFlagAt m.state i).getD false = false)
    (slashed : (slashedFlagAt n.state i).getD false = true) :
    (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    obtain rfl := DirectSafety.Apriori.Internal.processUpgrades_eq_of_window upgraded fulu early
    have same := slashedFlagAt_advanceSlot advancedOk i
    rw [clean] at same
    exact absurd (same.symm.trans slashed) Bool.false_ne_true
  | @block f s t engine signed due ok =>
    obtain ⟨-, processed, -⟩ := applySignedBlock_ok ok
    have slot := (frame_processBlock processed).slot
    simp only [getCurrentEpoch, slot]

/-- A state before the last step of a run leads to the first state of that step. -/
private theorem prefix_leads {x m n : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) {m1 n1 : ForkedBeaconState preset}
    (before : Run config checks x m1) (step1 : Step config checks m1 n1)
    (after : Run config checks n1 n) (cut : (before.snoc step1).append after = pre.snoc step) :
    Nonempty (Run config checks m1 m) := by
  cases after with
  | nil =>
    obtain ⟨rfl, -, -⟩ := Run.snoc.inj cut
    exact ⟨Run.nil⟩
  | snoc rest step2 =>
    obtain ⟨rfl, -, -⟩ := Run.snoc.inj cut
    exact ⟨(Run.nil.snoc step1).append rest⟩

/-- A key unslashed at `c` and slashed at a later state is withdrawable a vector past `fin`.

The key is slashed after `c`, so its withdrawable epoch is the slashings vector past that epoch.

The finalized epoch is at most the epoch of `c`. -/
private theorem slashed_withdrawable_vector
    (h : Setting config checks g split fin pulled anc counted V) (v : ValidatorIndex)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (inside : v.toNat < c.validators.data.size)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    {a : ForkedBeaconState preset} (run : Run config checks ⟨fork, c⟩ a)
    (u : Validator)
    (foundU : a.state.validators.data[v.toNat]? = some u) (flag : u.slashed = true) :
    (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      u.withdrawableEpoch.toNat := by
  have finC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toC.chainSteps)
  have lower := withdrawable_of_clean_run h.caps (Internal.Setting.delay h) v.toNat inside clean run
    u foundU flag
  simp only at finC
  omega

/-- A key unslashed at `c` and slashed at a later state is withdrawable beyond R's horizon.

The guard keeps the window from the finalized epoch through R's horizon under half a vector. -/
private theorem slashed_beyond_horizon
    (h : Setting config checks g split fin pulled anc counted V) (v : ValidatorIndex)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (inside : v.toNat < c.validators.data.size)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    {a : ForkedBeaconState preset} (run : Run config checks ⟨fork, c⟩ a)
    (u : Validator)
    (foundU : a.state.validators.data[v.toNat]? = some u) (flag : u.slashed = true) :
    (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat := by
  have := slashed_withdrawable_vector h v toC inside clean run u foundU flag
  have half := Internal.depthFin_lt_half h
  omega

/-- If an unslashed key is not withdrawable by R's next epoch, its exit plus the delay is later.

Its withdrawable epoch is its exit plus the delay, or both are unset. -/
theorem late_of_withdrawable (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (i : ℕ) (w : Validator)
    (found : pulled.validators.data[i]? = some w) (clean : w.slashed = false)
    (beyond : (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) :
    (getCurrentEpoch pulled).toNat + 1 <
      w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  obtain ⟨shared⟩ := h.toFin
  have far := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  rcases Run.withdrawable_eq_exit_delay (shared.append (fromFin.append tail)) h.genesis i w found
    clean with ⟨exitFar, -⟩ | eq
  · have := congrArg UInt64.toNat exitFar
    have farEq : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  · omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The floor of a key slashed at R, from a state of R's run, across the step that slashes it.

If the key is already slashed, the floor starts at that state. -/
theorem slash_floor_across (h : Setting config checks g split fin pulled anc counted V)
    (v : ValidatorIndex) {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩) (inside : v.toNat < c.validators.data.size)
    -- The key is unslashed at `c`.
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    (wP : Validator) (foundP : pulled.validators.data[v.toNat]? = some wP)
    (slashedP : wP.slashed = true)
    -- The pin counts the key as slashed on R's branch.
    (rb : (pinTerms config pulled anc fin).slashedRB v.toNat = true)
    {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
    (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩)
    {evs : List (BalanceEvent preset)}
    (ev : rest.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs) :
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
        (evs.map (floorPartialDebit v)).sum +
          -- The floor allows for the run's debits against R's balance.
          --
          -- It also allows for the maximum initial slashing penalty.
          Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
  -- The run from the state splits at the step that slashes the key.
  --
  -- Before the step the key is unslashed.
  --
  -- Its withdrawable epoch is then beyond the epoch of that step.
  --
  -- After it the key is slashed, so its withdrawable epoch is beyond R's horizon.
  classical
  obtain ⟨shared⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨uB, foundB⟩ : ∃ uB, c.validators.data[v.toNat]? = some uB :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have cleanB : uB.slashed = false := clean uB foundB
  have finC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toC.chainSteps)
  obtain ⟨val, foundZ⟩ : ∃ val, zs.validators.data[v.toNat]? = some val :=
    ⟨_, Array.getElem?_eq_getElem
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps))⟩
  -- the cap of the voter at the state is the cap that the floor reads
  have atZ : PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat =
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    simp [PinTerms.capAt, foundZ]
  have topDiv : PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat /
      (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
      Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
    have hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat =
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
      simp [Internal.slashW, rb]
    rw [hW, Internal.parameters_of_fusaka h.fulu h.early]
    exact Nat.div_le_div_right (Internal.capAt_le_capMax h.caps electra v.toNat)
  -- the floor of a slashed key from a state to R
  have slashedTail : ∀ {a : BeaconState preset fork}
      (runA : Run config checks ⟨fork, c⟩ ⟨fork, a⟩)
      (restA : Run config checks ⟨fork, a⟩ ⟨fork, pulled⟩) {evsA : List (BalanceEvent preset)},
      restA.balanceEvents (getCurrentEpoch pulled).toNat = .ok evsA → ∀ ua : Validator,
      a.validators.data[v.toNat]? = some ua → ua.slashed = true →
      min (actualBalanceAt (⟨fork, a⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, a⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evsA.map (penaltyDebit v.toNat)).sum + (evsA.map (Internal.syncDebit v.toNat)).sum +
          (evsA.map (floorPartialDebit v)).sum := by
    intro a runA restA evsA evA ua foundA flagA
    have floor := Internal.slashed_floor h (toC.append runA) (e := pulled) (Nat.le_succ _) restA
      (getCurrentEpoch pulled).toNat (Nat.le_succ _) evA v ua foundA
      (fun flag => slashed_withdrawable_vector h v toC inside clean runA ua foundA flag)
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (Internal.path_le_cap_pulled h (toC.append runA) restA .nil v.toNat)
      (fun before step after _ _ _ => .inr fun u foundU => by
        obtain ⟨w', foundW', flagW'⟩ := before.slashedPersistence v.toNat ua foundA flagA
        have same := Option.some.inj (foundW'.symm.trans foundU)
        have low := Nat.lt_of_le_of_lt
          (fork_le_of_chainSteps ((Run.nil.snoc step).append after).chainSteps) h.early
        exact slashed_beyond_horizon h v toC inside clean (runA.append before) u foundU
          (same ▸ flagW'))
    have capEq : PinTerms.capAt (⟨fork, a⟩ : ForkedBeaconState preset) v.toNat =
        (withdrawalMaxEffectiveBalance preset fork ua).toNat := by
      simp [PinTerms.capAt, foundA]
    rw [ite_eq_left flagA] at floor
    omega
  by_cases startSlashed : val.slashed = true
  · -- the key is slashed already at the state
    have := slashedTail pre rest ev val foundZ startSlashed
    omega
  · have cleanZ : val.slashed = false := by simpa using startSlashed
    -- the run splits at the step that slashes the key
    obtain ⟨m, n, pre', step, post, split', notYet, arrived⟩ := Run.split_at_flip rest
      (fun z => ∃ w, z.state.validators.data[v.toNat]? = some w ∧ w.slashed = true)
      (fun hx => by
        obtain ⟨w, found, flag⟩ := hx
        have found' : zs.validators.data[v.toNat]? = some w := found
        rw [foundZ] at found'
        cases found'
        simp [cleanZ] at flag)
      ⟨wP, foundP, slashedP⟩
    subst split'
    have forkM : m.fork = fork :=
      Internal.fork_eq_of_run pre' ((Run.nil.snoc step).append post) (Nat.le_refl _)
    have forkN : n.fork = fork := Internal.fork_eq_of_run (pre'.snoc step) post (Nat.le_refl _)
    obtain ⟨mf, mS⟩ := m
    obtain ⟨nf, nS⟩ := n
    have forkM' : fork = mf := forkM.symm
    have forkN' : fork = nf := forkN.symm
    subst forkM'
    subst forkN'
    obtain ⟨valM, foundM⟩ : ∃ valM, mS.validators.data[v.toNat]? = some valM :=
      ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le
        (Array.getElem?_eq_some_iff.mp foundZ).1 (registryGrows_of_chainSteps pre'.chainSteps))⟩
    have cleanM : valM.slashed = false := by
      by_contra flag
      exact notYet ⟨valM, foundM, by simpa using flag⟩
    obtain ⟨valN, foundN, slashedN⟩ := arrived
    have flagM : (slashedFlagAt mS v.toNat).getD false = false := by
      simp [slashedFlagAt, foundM, cleanM]
    have flagN : (slashedFlagAt nS v.toNat).getD false = true := by
      simp [slashedFlagAt, foundN, slashedN]
    -- the slashing step is a block, so it stays in its epoch
    have sameEpoch : (getCurrentEpoch nS).toNat = (getCurrentEpoch mS).toNat :=
      step_slash_epoch step h.early h.fulu v.toNat flagM flagN
    have nearN : (getCurrentEpoch nS).toNat ≤ (getCurrentEpoch pulled).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    -- the key is not yet withdrawable when the step slashes it
    have slashable : (getCurrentEpoch mS).toNat < valM.withdrawableEpoch.toNat :=
      Internal.newly_slashed_unwithdrawable h.genesis h.caps (shared.append (toC.append (pre.append
        pre')))
        step foundM foundN cleanM slashedN
    -- before the step the key is withdrawable beyond the epoch of the step
    have wide : ∀ {m1 : ForkedBeaconState preset} (toM1 : Run config checks ⟨fork, c⟩ m1)
        (toM : Run config checks m1 ⟨fork, mS⟩) (u : Validator),
        m1.state.validators.data[v.toNat]? = some u →
        (getCurrentEpoch mS).toNat - 1 + 1 < u.withdrawableEpoch.toNat := by
      intro m1 toM1 toM u foundU
      have low : m1.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps toM.chainSteps) h.early
      have reach : (getCurrentEpoch mS).toNat ≤ (getCurrentEpoch pulled).toNat := by omega
      by_cases flag : u.slashed = true
      · have := slashed_beyond_horizon h v toC inside clean toM1 u foundU flag
        omega
      · have clean : u.slashed = false := by simpa using flag
        have farBound := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
        rcases (shared.append (toC.append toM1)).withdrawable_eq_exit_delay h.genesis v.toNat u
          foundU clean with ⟨-, far⟩ | eqW
        · rw [far]
          omega
        · by_cases assigned : u.exitEpoch = FAR_FUTURE_EPOCH
          · rw [assigned] at eqW
            omega
          · obtain ⟨mm, foundMM, life⟩ := toM.registryLifecycle.validators v.toNat u foundU
            have mmEq : mm = valM := Option.some.inj (foundMM.symm.trans foundM)
            have exM : valM.exitEpoch = u.exitEpoch := by
              rw [← mmEq]
              exact life.exitEpoch assigned
            rcases (shared.append (toC.append (pre.append pre'))).withdrawable_eq_exit_delay
              h.genesis v.toNat valM foundM cleanM with ⟨farM, -⟩ | exactM
            · exact absurd (exM.symm.trans farM) assigned
            · have lower := (shared.append (toC.append toM1)).exit_withdrawable_delay h.genesis
                v.toNat u foundU assigned
              have gap := (shared.append (toC.append toM1)).exit_activation_gap h.genesis
                v.toNat u foundU assigned
              have delayPos := (Internal.Setting.delay h)
              rw [exM] at exactM
              omega
    -- the floor of the run up to the slashed state
    obtain ⟨evs1, ok1⟩ := (pre'.snoc step).balanceEvents_ok h.early
      ((getCurrentEpoch mS).toNat - 1)
    obtain ⟨evs2, ok2⟩ := post.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
    have ok1' : (pre'.snoc step).balanceEvents (getCurrentEpoch pulled).toNat = .ok evs1 := by
      rw [balanceEvents_eq_of_endpoint_le (pre'.snoc step)
        (localHigh := (getCurrentEpoch mS).toNat - 1) (by simp only; omega)
        (by simp only; omega)]
      exact ok1
    have evEq : evs = evs1 ++ evs2 :=
      Except.ok.inj (ev.symm.trans (balanceEvents_append (pre'.snoc step) post _ ok1' ok2))
    have floor1 := Internal.slashed_floor h (toC.append pre) (e := nS) (by omega) (pre'.snoc step)
      ((getCurrentEpoch mS).toNat - 1) (by omega) ok1 v val foundZ
      (fun flag => absurd flag startSlashed)
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (Internal.path_le_cap_pulled h (toC.append pre) (pre'.snoc step) post v.toNat)
      (fun before step1 after1 cutB _ _ => .inr fun u foundU => by
        obtain ⟨toM⟩ := prefix_leads pre' step before step1 after1 cutB
        exact wide (pre.append before) toM u foundU)
    rw [ite_eq_right startSlashed] at floor1
    have floor2 := slashedTail (pre.append (pre'.snoc step)) post ok2 valN foundN slashedN
    have capMono := Internal.cap_le_cap_of_run h.caps (pre'.snoc step) v.toNat
    rw [atZ] at capMono
    rw [evEq]
    simp only [List.map_append, List.sum_append] at floor1 floor2 ⊢
    rw [atZ]
    omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The floor of a key unslashed at `c` at each state of R's run from `c`. -/
theorem voter_floorAt (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (v : ValidatorIndex)
    {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (rest : Run config checks ⟨fork, c⟩ ⟨fork, pulled⟩)
    -- The run from `c` is the rest of the run from the finalized state to R's, cut at `c`.
    (cutC : toC.append rest = fromFin.append tail)
    -- The key is unslashed at `c`.
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    -- A key slashed on R is not withdrawable until at least a slashings vector past finality.
    (slashedLate : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
      anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat)
    (inside : v.toNat < c.validators.data.size)
    -- The exit of the key at R is late for the whole run.
    --
    -- The same exit-epoch restriction holds for a finalized key.
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = false →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
    (after : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append after = rest →
    ∀ {evs : List (BalanceEvent preset)},
    after.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs →
    -- The floor starts from the smaller of the voter's balance there and its cap there.
    --
    -- The cap there is the cap at R if it is frozen.
    --
    -- It is less if the voter switches to compounding on R.
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      -- The floor is R's balance, plus the debits of the rest of R's run.
      --
      -- It also adds the slack of a slashing on R.
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
        (evs.map (floorPartialDebit v)).sum +
          -- A voter unslashed at R uses the floor without a slashing deduction.
          --
          -- A voter slashed at R uses the floor with an allowance for the slashing loss.
          --
          -- The pin allows for the initial penalty at the largest effective-balance cap.
          Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
  classical
  have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  -- the key's records at the four states
  have sizeC := registryGrows_of_chainSteps rest.chainSteps
  obtain ⟨uB, foundB⟩ : ∃ uB, c.validators.data[v.toNat]? = some uB :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨wP, foundP⟩ : ∃ wP, pulled.validators.data[v.toNat]? = some wP :=
    ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside sizeC)⟩
  -- a record that is unslashed is the unslashed record at its index
  have only : ∀ {s : BeaconState preset fork} {u : Validator},
      s.validators.data[v.toNat]? = some u → u.slashed = false →
      ∀ w, s.validators.data[v.toNat]? = some w → w.slashed = false :=
    fun fu cu w fw => by
      rw [fu] at fw
      cases fw
      exact cu
  have cleanB : uB.slashed = false := clean uB foundB
  have finC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toC.chainSteps)
  intro zs pre after cut' evs ev
  have cut : (toC.append pre).append after = fromFin.append tail := by
    rw [← Run.append_assoc, cut', cutC]
  obtain ⟨val, foundZ⟩ : ∃ val, zs.validators.data[v.toNat]? = some val :=
    ⟨_, Array.getElem?_eq_getElem
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps))⟩
  -- the cap of the voter at the state is the cap that the floor reads
  have atZ : PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat =
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    simp [PinTerms.capAt, foundZ]
  by_cases slashedP : wP.slashed = true
  · -- slashed on R after the split: the pin counts it, and `slashW` holds its slack
    have rb : (pinTerms config pulled anc fin).slashedRB v.toNat = true :=
      Internal.slashedRB_of_withdrawable config pulled anc fin foundP slashedP
        (slashedLate wP foundP slashedP)
    exact Internal.slash_floor_across h v toC inside (fun u fu => only foundB cleanB u fu) wP foundP
      slashedP rb pre after ev
  · have cleanP : wP.slashed = false := by simpa using slashedP
    have lateP := late wP foundP cleanP
    have cleanZ : val.slashed = false := Internal.unslashed_of_run after foundZ (only foundP cleanP)
    have retainedZ : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, zs⟩ m)
        (step : Step config checks m n) (later : Run config checks n ⟨fork, pulled⟩),
        (before.snoc step).append later = after → ∀ w,
        n.state.validators.data[v.toNat]? = some w →
        ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
          ∀ u, m.state.validators.data[v.toNat]? = some u →
            (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) :=
      fun before step later cutB w foundW =>
        Internal.retained_of_exit h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_refl _) v
          foundP
          lateP ((toC.append pre).append before) step later
          (by
            rw [← cut, ← cutB]
            exact (Run.append_assoc (toC.append pre) (before.snoc step) later).symm)
          w foundW
    have floor := Internal.key_floorR_from h (toC.append pre) after (getCurrentEpoch pulled).toNat
      (Nat.le_succ _) ev v
      val foundZ cleanZ
      (fun w fw => by
        rw [← Option.some.inj (foundP.symm.trans fw)]
        exact cleanP)
      retainedZ
    rw [atZ]
    omega

/-- The effective-balance ceiling covers the key's finalized effective balance. -/
theorem effective_fin_le_ebUp (h : Setting config checks g split fin pulled anc counted V)
    (i : ℕ) :
    effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i ≤
      (pinTerms config pulled anc fin).ebUp i := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  rw [Internal.ebUp_eq config pulled anc fin electra i _ rfl]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The floor of a key slashed at the finalized state, from a state of a run to R.

The key keeps its withdrawable epoch along every run, once it is slashed.

Its withdrawable epoch at R is the slashings vector past the finalized epoch, and past R's horizon.

The floor at each state needs no further allowance for slashing. -/
theorem slash_floor_from_slashed
    (h : Setting config checks g split fin pulled anc counted V) (v : ValidatorIndex)
    (inFin : v.toNat < fin.validators.data.size)
    (slashedFin : ∀ u, fin.validators.data[v.toNat]? = some u → u.slashed = true)
    (wP : Validator) (foundP : pulled.validators.data[v.toNat]? = some wP)
    (frozen : (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      wP.withdrawableEpoch.toNat)
    (late : (getCurrentEpoch pulled).toNat + 1 < wP.withdrawableEpoch.toNat)
    {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) {evs : List (BalanceEvent preset)}
    (ev : r2.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs) :
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
        (evs.map (floorPartialDebit v)).sum := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨uF, foundF⟩ : ∃ uF, fin.validators.data[v.toNat]? = some uF :=
    ⟨_, Array.getElem?_eq_getElem inFin⟩
  obtain ⟨val, foundZ, slashedZ⟩ := r1.slashedPersistence v.toNat uF foundF (slashedFin uF foundF)
  have assigned : val.exitEpoch ≠ FAR_FUTURE_EPOCH :=
    run_slashed_exit_assigned (shared.append r1) h.genesis h.caps.activation
      h.caps.compounding (Internal.Setting.delay h) v.toNat val foundZ slashedZ
  have kept := r2.slashed_withdrawable_eq h.caps.activation h.caps.compounding
    v.toNat val wP foundZ foundP slashedZ assigned
  have capEq : PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat =
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    simp [PinTerms.capAt, foundZ]
  have floor := Internal.slashed_floor h r1 (e := pulled) (Nat.le_succ _) r2
    (getCurrentEpoch pulled).toNat (Nat.le_succ _) ev v val foundZ
    (fun _ => by
      have := frozen
      rw [kept.2] at this
      exact this)
    (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (Internal.path_le_cap_pulled h r1 r2 .nil v.toNat)
    (fun before step after _ _ _ => .inr fun u foundU => by
      have low := Nat.lt_of_le_of_lt
        (fork_le_of_chainSteps ((Run.nil.snoc step).append after).chainSteps) h.early
      have keptU := before.slashed_withdrawable_eq h.caps.activation h.caps.compounding
        v.toNat val u foundZ foundU slashedZ assigned
      have lateW := late
      rw [kept.2] at lateW
      rw [keptU.2]
      exact lateW)
  rw [ite_eq_left slashedZ] at floor
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A finalized key slashed at the split keeps its effective balance in its envelope on R's run. -/
theorem kc_envelope (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (inFin : v.toNat < fin.validators.data.size)
    -- A key unslashed at the finalized state is slashed on the shared segment or on R's run.
    (slashedSplit : ∃ u, split.validators.data[v.toNat]? = some u ∧ u.slashed = true)
    (rb : (pinTerms config pulled anc fin).slashedRB v.toNat = true)
    -- Its withdrawable epoch at R is the slashings vector past the finalized epoch.
    (frozen : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat)
    -- Its withdrawable epoch is also past R's horizon.
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) :
    ∀ z ∈ (fromFin.append tail).balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  -- The floor starts at the finalized state.
  --
  -- A key slashed at the finalized state keeps its withdrawable epoch along every run.
  --
  -- The floor at each state needs no further allowance for slashing.
  --
  -- That actual-balance floor gives a lower bound on effective balance.
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨uF, foundF⟩ : ∃ uF, fin.validators.data[v.toNat]? = some uF :=
    ⟨_, Array.getElem?_eq_getElem inFin⟩
  obtain ⟨uS, foundS, flagS⟩ := slashedSplit
  obtain ⟨wP, foundP, slashedP⟩ := toPulled.slashedPersistence v.toNat uS foundS flagS
  have floorAt : ∀ {zs : BeaconState preset fork}
      (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩),
      pre.append rest = fromFin.append tail → ∀ {evs : List (BalanceEvent preset)},
      rest.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
    intro zs pre rest _ evs ev
    by_cases cleanF : uF.slashed = false
    · exact Internal.slash_floor_across h v Run.nil inFin (fun u fu => by
        rw [← Option.some.inj (foundF.symm.trans fu)]
        exact cleanF) wP foundP slashedP rb pre rest ev
    · -- slashed at the finalized state, so slashed at every state of the run
      have slashedF : uF.slashed = true := by simpa using cleanF
      have := Internal.slash_floor_from_slashed h v inFin (fun u fu => by
        rw [← Option.some.inj (foundF.symm.trans fu)]
        exact slashedF) wP foundP (frozen wP foundP) (late wP foundP) pre rest ev
      omega
  exact Internal.prefix_envelope h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _)
    replayedF
    replayed v Run.nil (fromFin.append tail) (Run.nil_append (fromFin.append tail)) inFin
    (Internal.slashW (pinTerms config pulled anc fin) v.toNat)
    (Or.inl ⟨Internal.effective_fin_le_ebUp h v.toNat, Nat.le_refl _⟩) floorAt

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key unslashed at `c` at each state of R's run from `c`.

If it starts below the reserve's ceiling, it stays within that ceiling plus the allowed increments.

The increments are the whole ones of its sync debits and its slashing slack. -/
theorem envelope_of_voter (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (rest : Run config checks ⟨fork, c⟩ ⟨fork, pulled⟩)
    -- The run from `c` is the rest of the run from the finalized state to R's, cut at `c`.
    (cutC : toC.append rest = fromFin.append tail)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    (slashedLate : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
      anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat)
    (inside : v.toNat < c.validators.data.size)
    -- The key may instead start within the floor of its balance at `c`.
    (start : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ balanceAt fin v.toNat) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = false →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ z ∈ rest.balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
              Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  -- The actual-balance floor holds at each state of that run.
  --
  -- It gives a lower bound on effective balance.
  exact Internal.prefix_envelope h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _)
    replayedF
    replayed v toC rest cutC inside (Internal.slashW (pinTerms config pulled anc fin) v.toNat) start
    (Internal.voter_floorAt h fromFin tail v toC rest cutC clean slashedLate inside late)

/-- The branch slashing count bounds the number of charged slashings in any set of keys. -/
theorem slashedRB_card_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (W : Finset ValidatorIndex) :
    (W.filter fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat =
      true).card ≤ (pinTerms config state ancestor finalizedState).slashedR := by
  classical
  rw [Internal.slashedR_eq]
  refine Finset.card_le_card_of_injOn UInt64.toNat (fun v member => ?_)
    (fun a _ b _ same => UInt64.toNat_inj.mp same)
  obtain ⟨_, flag⟩ := Finset.mem_filter.mp member
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (slashedRB_lt config state ancestor
    finalizedState flag), flag⟩

/-- The keys slashed on this branch after the finalized epoch cost one increment each, once. -/
theorem slashR_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    (W : Finset ValidatorIndex) :
    ∑ v ∈ W, Internal.slashR (pinTerms config state ancestor finalizedState) v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config state ancestor finalizedState).slashedR := by
  classical
  have sum : ∑ v ∈ W, Internal.slashR (pinTerms config state ancestor finalizedState) v.toNat =
      ∑ v ∈ W.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
        = true), preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [Finset.sum_filter]
    rfl
  rw [sum, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Internal.slashedRB_card_le config state ancestor finalizedState W)

/-- A key that exited by the epoch of a run's start is inactive at the end of the run.

The run keeps an assigned exit epoch, and the epoch of its end is not before that of its start. -/
theorem inactive_of_exited (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) {i : ℕ} {v : Validator}
    (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat ≤ (getCurrentEpoch x.state).toNat) :
    isActiveAt y.state (getCurrentEpoch y.state) i = false := by
  have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro same
    rw [same] at exited
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have bound := (getCurrentEpoch x.state).toNat_lt_size
    simp only [UInt64.size] at bound
    exact getCurrentEpoch_ne_farFuture twoSlots x.state (UInt64.toNat_inj.mp (by omega))
  have forward := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  exact Internal.inactive_from_exit tail found assigned
    (UInt64.le_iff_toNat_le.mpr (Nat.le_trans exited forward))

/-- No block of a run from the finalized state has as proposer a key that exited by that state.

The key's exit is already assigned at the finalized state, so it is inactive on the whole run.

A proposer is active, which the lookahead of the run gives. -/
theorem exited_not_proposer (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)
    (u : ForkedBeaconState preset) (run : Run config checks ⟨fork, fin⟩ u) (p : ValidatorIndex) :
    u.fork < .glamsterdam → getBeaconProposerIndex u.state = .ok p → p.toNat ≠ i := by
  intro early proposer same
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨w0, foundFin, kept⟩ := Internal.exit_kept_of_le_fin h foundPulled exited
  have inactive := Internal.inactive_of_exited h.twoSlots run foundFin (by rw [kept]; exact exited)
  have look := Run.lookaheadActive h.facts.covers h.genesis (toFin.append run) early
  have active := look.proposer_active
    (Nat.le_trans h.fulu (fork_le_of_chainSteps run.chainSteps)) proposer
  rw [same, inactive] at active
  exact Bool.false_ne_true active

/-- A scan over sources that the gross credits hold is at most the gross credits. -/
theorem scan_le_gross {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) (p : BalanceSource → Bool)
    (inside : ∀ s, p s = true → s = .rewards ∨ s = .slashings ∨ s = .sync) :
    (Internal.creditScan p (fun _ => false) v high tail) ≤ Internal.grossScan v high tail := by
  have split := Internal.creditScan_or (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync))
    (fun _ => false) p (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync) && !p s)
    (fun _ => false) (fun _ => false)
    (fun s => by
      by_cases hp : p s = true
      · simp [hp, inside s hp]
      · simp [hp])
    (fun _ => rfl) (fun s ⟨first, second⟩ => by simp [first] at second)
    (fun s h => by simp at h) v high tail
  unfold Internal.grossScan
  omega

/-- A key with a sync credit over a run's replayed events has a gross credit on the run. -/
theorem syncCr_gross {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (tailC : Run config checks x y) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ℕ) (positive : 0 < Internal.syncCr eventsC v) : 0 < Internal.grossScan v highC tailC := by
  obtain ⟨-, sync⟩ := Internal.creditScan_bounds (∅ : Finset ValidatorIndex) UInt64.toNat
    (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) highC
    (fun _ => 0) tailC replayedC (fun e _ _ => by simp)
  have bound := sync (fun s => decide (s = .sync)) (Or.inl fun s covered => by
      simp only [decide_eq_true_eq] at covered ⊢
      exact Or.inr (Or.inr covered))
    (Or.inr fun ok _ fork early replayed i =>
      (Internal.sum_map_sync _ (Internal.keyCredit i)).symm.trans
        (Internal.slot_syncDebit_zero fork ok early replayed i).2) electra early v
  have conv : Internal.syncCr eventsC v = ((eventsC.filter (·.source = .sync)).map
    (Internal.keyCredit v)).sum :=
    Internal.sum_map_sync _ (Internal.keyCredit v)
  unfold Internal.grossScan
  rw [conv] at positive
  omega

/-- A key with a sync credit over the events of the shared segment has a gross credit on a run.

The run is the shared segment followed by a tail from the split. -/
theorem syncCr_gross_shared (h : Setting config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, z⟩) (high : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (v : ℕ) (positive : 0 < Internal.syncCr eventsF v) :
    0 < Internal.grossScan v high (fromFin.append tailC) := by
  have shared := Internal.syncCr_gross (Nat.le_trans (by decide) h.fulu) h.early fromFin high
    replayedF v
    positive
  have split := Internal.creditScan_append (fun s => decide (s = .rewards ∨ s = .slashings ∨ s =
    .sync))
    (fun _ => false) v high fromFin tailC
  unfold Internal.grossScan at shared ⊢
  omega

/-- The rounding bands of a set of keys are the band for each key with a sync debit. -/
private theorem sum_bandR (events : List (BalanceEvent preset)) (T : Finset ValidatorIndex) :
    ∑ v ∈ T, Internal.bandR events v.toNat =
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
        (T.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum).card := by
  classical
  simp only [Internal.bandR_eq]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Keys of R's registry newly slashed on C's branch and charged to depart there.

A key charged in the split's epoch reads the balance before the credits of `pre` that follow it.

A key charged later holds those credits in its charge, so reading them is an overpayment.

The excess charge also covers counted but inactive keys outside the voter set. -/
def chargedNewlySlashed (pulled counted split : BeaconState preset fork)
    {x y : ForkedBeaconState preset} (tailC : Run config checks x y) : Finset ValidatorIndex :=
  (newlySlashed pulled counted split).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
      v.toNat

/-- The keys of R's registry that are slashed at the split and that R's call reads as slashed.

They are the keys that the shared run slashes in its last epoch, and some before it. -/
def cutKeys (config : Config) (pulled anc fin split : BeaconState preset fork) :
    Finset ValidatorIndex :=
  ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter fun v =>
    -- None is a newly slashed key, which is unslashed at the split.
    --
    -- None is in C's quorum, since a flag set at the split persists to C.
    ((split.validators.data[v.toNat]?).map (·.slashed)).getD false = true ∧
      (pinTerms config pulled anc fin).slashedRB v.toNat = true ∧
      -- The withdrawable epoch at R is a slashing vector past the finalized state's epoch.
      --
      -- The anchor's finalized epoch can lag that of the finalized state.
      --
      -- So this leaves out a key slashed before the finalized state's epoch.
      --
      -- Its correlation penalty can fall in the window.
      ((pulled.validators.data[v.toNat]?).any fun w =>
        decide ((getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat)) = true

/-- A key that exited by the finalized epoch is exited at R's record. -/
private theorem exited_of_exitBeforeFin {v : ValidatorIndex}
    (exit : (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) :
    ∃ w, pulled.validators.data[v.toNat]? = some w ∧
      w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat := by
  have flag : ((pulled.validators.data[v.toNat]?).any fun w =>
      decide (w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)) = true := exit
  cases found0 : pulled.validators.data[v.toNat]? with
  | none => simp [found0] at flag
  | some w0 =>
    simp [found0] at flag
    exact ⟨w0, rfl, flag⟩

/-- A key that C's run charges to depart has not exited by the finalized epoch.

Its exit is assigned at the finalized state, so it is assigned at the start of C's run.

The charge is of a step that starts with the exit unassigned. -/
private theorem chargedNewlySlashed_not_exited
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ chargedNewlySlashed pulled counted split tailC) :
    (pinTerms config pulled anc fin).exitBeforeFin v.toNat ≠ true := by
  intro exit
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨-, c, cMember, cIndex⟩ := Finset.mem_filter.mp member
  obtain ⟨w, foundPulled, exited⟩ := exited_of_exitBeforeFin exit
  obtain ⟨u, foundFin, kept⟩ := Internal.exit_kept_of_le_fin h foundPulled exited
  have assigned : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat (kept.symm.trans far)
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  obtain ⟨at_split, foundSplit, life⟩ := fromFin.registryLifecycle.validators v.toNat u foundFin
  have keptSplit := life.exitEpoch assigned
  obtain ⟨a, b, front, step, post, -, vv, w2, found, foundB, unset, set, amount, epoch⟩ :=
    tailC.departure_charge_site c cMember
  rw [cIndex] at found foundB
  obtain ⟨at_a, foundA, lifeA⟩ := front.registryLifecycle.validators v.toNat at_split foundSplit
  have same : at_a = vv := Option.some.inj (foundA.symm.trans found)
  have assignedSplit : at_split.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [keptSplit]
    exact assigned
  have keptA := lifeA.exitEpoch assignedSplit
  rw [same] at keptA
  exact assignedSplit (by rw [← keptA]; exact unset)

/-- A key with a proposer, whistleblower or sync credit on a run has a gross credit. -/
private theorem credit_gross {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (r : Run config checks x y) (highC : ℕ)
    {eventsP : List (BalanceEvent preset)} (replayedP : r.balanceEvents highC = .ok eventsP)
    (v : ℕ) (positive : 0 < Internal.propN r highC v + Internal.whistC r highC v + Internal.syncCr
      eventsP v) :
    0 < Internal.grossScan v highC r := by
  have prop := Internal.scan_le_gross r highC v (fun s => decide (s = .rewards))
    fun s h => by simp at h; simp [h]
  have whist := Internal.scan_le_gross r highC v (fun s => decide (s = .slashings))
    fun s h => by simp at h; simp [h]
  by_cases sync : 0 < Internal.syncCr eventsP v
  · exact Internal.syncCr_gross electra early r highC replayedP v sync
  · unfold Internal.propN Internal.whistC at positive
    omega

/-- A key credited on `pre` is a proposer of its epoch, or holds a seat of the split's committee.

The run `pre` is inside one epoch, from the start `b` of the split's epoch.

At most one block of `pre` is proposed in each of the epoch's slots. -/
private theorem pre_credit_seat (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b) (highC : ℕ) :
    ∃ B : Finset ℕ, B.card ≤ preset.SLOTS_PER_EPOCH.toNat ∧
      ∀ i, 0 < Internal.grossScan i highC pre → i ∈ B ∨ ∃ w, split.validators.data[i]? = some w ∧
        w.pubkey ∈
          (split.currentSyncCommittee (Nat.le_trans (by decide) h.fulu)).value.pubkeys.toList := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have samePeriod : (getCurrentEpoch split).toNat /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch b).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
    rw [sameEpoch]
  obtain ⟨B, D, cardB, -, gross, -, -, -⟩ := Internal.credited_piece h.genesis
    h.parameters.lookahead toB
    pre h.fulu altair h.early (Internal.Setting.delay h) highC samePeriod
  refine ⟨B, ?_, fun i pos => ?_⟩
  · -- the blocks of `pre` are at most one in each slot of the epoch
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := h.twoSlots; omega
    have count : pre.blockCount ≤
        ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch b).toNat) *
          preset.SLOTS_PER_EPOCH.toNat := pre.blockCount_le_epochs positive
    have one : (getCurrentEpoch split).toNat + 1 - (getCurrentEpoch b).toNat = 1 := by
      rw [sameEpoch]
      omega
    rw [one, Nat.one_mul] at count
    exact cardB.trans count
  · rcases gross i pos with inB | ⟨w, found, mem⟩
    · exact .inl inB
    · refine .inr ⟨w, found, ?_⟩
      rw [pre.currentSyncCommittee_eq_of_same_period samePeriod altair altair]
      exact mem

/-- Three roundings of an increment's reward are below the increment, from quotient thirty. -/
private theorem whistle_round_le (inc W : ℕ) (quotient : 30 ≤ W) (large : 3600 ≤ inc) :
    3 * ((inc + W - 1) / W) ≤ inc - 1 := by
  have le := Nat.div_mul_le_self (inc + W - 1) W
  generalize (inc + W - 1) / W = c at le ⊢
  rcases c with _ | k
  · omega
  · rw [Nat.succ_mul] at le
    have := Nat.mul_le_mul_left k quotient
    omega

/-- The bands of the classes and of the charged and cut keys fit the seats and slots, as numbers. -/
private theorem bands_arith (UP β cc SPE seats nV n4 n5 n6 nS nE nQ nB nU nK : ℕ)
    (bandUp : UP ≤ 2 * β) (ceil : 3 * cc ≤ β)
    (linear : 3 * nV + n4 + 3 * n5 + n6 + 3 * nU + nK ≤ 3 * seats) (subS : nS ≤ nU)
    (subEQ : nE + nQ ≤ nU) (cardB : nB ≤ SPE) :
    3 * (β * nV) + β * n4 + 3 * (β * n5) + β * n6 + β * nS + UP * nE + UP * (nB + nQ) +
        3 * (cc * nK) ≤ 3 * (β * (seats + SPE)) := by
  have scaled := Nat.mul_le_mul_left β linear
  have bandS := Nat.mul_le_mul_left β subS
  have bandEQ : UP * (nE + nQ) ≤ 2 * β * nU := Nat.mul_le_mul bandUp subEQ
  have bandB : UP * nB ≤ 2 * β * SPE := Nat.mul_le_mul bandUp cardB
  have bandK : 3 * cc * nK ≤ β * nK := Nat.mul_le_mul_right nK ceil
  nlinarith

/-- The cut keys are disjoint from the other classes in the sync budget. -/
theorem cut_disjoint (h : Setting config checks g split fin pulled anc counted V) :
    Disjoint (Internal.cutKeys config pulled anc fin split)
      (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted ∪
        newlySlashed pulled counted split ∪ createdSlashed counted split) := by
  -- A cut key is slashed at the split, and the flag persists to C.
  --
  -- So it is not in `V` or a quorum class.
  --
  -- It is not a newly slashed key either, which is unslashed at the split.
  --
  -- It is in the split's registry, so it is not a created slashed key.
  rw [Finset.disjoint_left]
  intro v cut member
  simp only [Internal.cutKeys, Finset.mem_filter] at cut
  obtain ⟨w, found, marked⟩ : ∃ w, split.validators.data[v.toNat]? = some w ∧ w.slashed = true := by
    cases hw : split.validators.data[v.toNat]? <;> simp_all
  obtain ⟨toCounted⟩ := h.toCounted
  obtain ⟨u, foundC, markedC⟩ := toCounted.slashedPersistence v.toNat w found marked
  have atCounted : slashedFlagAt counted v.toNat = some true := by
    simp [slashedFlagAt, foundC, markedC]
  simp only [Finset.mem_union] at member
  rcases member with ((((inV | in4) | in5) | in6) | inSC) | inCS
  · have unslashed := (h.voting v inV).2
    simp [atCounted] at unslashed
  · exact Internal.classes_unslashed (Finset.mem_union_left _ (Finset.mem_union_left _ in4))
      atCounted
  · exact Internal.classes_unslashed (pulled := pulled)
      (Finset.mem_union_left _ (Finset.mem_union_right _ in5)) atCounted
  · exact Internal.classes_unslashed (V := V) (Finset.mem_union_right _ in6) atCounted
  · simp only [newlySlashed, Finset.mem_filter] at inSC
    have fresh := inSC.2.2
    simp [slashedFlagAt, found, marked] at fresh
  · simp only [createdSlashed, Finset.mem_filter] at inCS
    have := (Array.getElem?_eq_some_iff.mp found).1
    omega

/-- The bands of the classes, the charged newly slashed and the cut keys fit the seats and slots. -/
theorem bands_seats (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high highC : ℕ)
    -- The end epoch of R is at most `high + 1`, and that of C at most `highC + 1`.
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    {events eventsF eventsC eventsP : List (BalanceEvent preset)}
    -- C's run is read at `highC`, and the shared segment and R's run at `high`.
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (replayedP : pre.balanceEvents highC = .ok eventsP) :
    3 * (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ stayingKeys pulled counted V, Internal.bandR (eventsF ++ events) v.toNat) +
        3 * (∑ v ∈ previousOnlyKeys counted V, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ joinedKeys pulled counted, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ newlySlashed pulled counted split, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ newlySlashed pulled counted split,
          if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
            (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) +
        -- Keys slashed and charged to depart on C's branch also use a band if credited on `pre`.
        --
        -- A key that proposed in `pre` pays it from a slot of the epoch.
        --
        -- The run `pre` starts at a state of the split's epoch.
        --
        -- So its proposers fill the slots of one epoch.
        --
        -- Any other key holds a seat, by its sync credit, and pays it from the spare of its seat.
        (∑ v ∈ chargedNewlySlashed pulled counted split tailC,
          if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
            Internal.syncCr eventsP v.toNat then
            preset.upwardBand else 0) +
        -- A cut key with a sync debit holds a seat.
        --
        -- It pays the rounding of an increment's reward there.
        3 * (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          if 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat then
            (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) ≤
      3 * ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
        (preset.SYNC_COMMITTEE_SIZE.toNat *
          (((getCurrentEpoch pulled).toNat + 1) /
              max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
          ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) +
          -- The bound adds the slots of an epoch to the seats.
          preset.SLOTS_PER_EPOCH.toNat)) := by
  classical
  obtain ⟨d45, d46, d56, d4v, d5v, d6v⟩ := Internal.classes_disjoint h
  obtain ⟨dSC, dSV⟩ := newlySlashed_disjoint h
  have cutApart := Internal.cut_disjoint h
  have dKV : Disjoint (Internal.cutKeys config pulled anc fin split) V :=
    Finset.disjoint_of_subset_right (fun v hv => by simp [Finset.mem_union, hv]) cutApart
  have dKK : Disjoint (Internal.cutKeys config pulled anc fin split)
      (stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted) :=
    Finset.disjoint_of_subset_right (fun v hv => by
      simp only [Finset.mem_union] at hv ⊢
      tauto) cutApart
  have dKS : Disjoint (Internal.cutKeys config pulled anc fin split) (newlySlashed pulled counted
    split) :=
    Finset.disjoint_of_subset_right (fun v hv => by simp [Finset.mem_union, hv]) cutApart
  obtain ⟨B, cardB, creditB⟩ := pre_credit_seat h toB pre sameEpoch highC
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have altairF : .altair ≤ fork := Nat.le_trans (by decide) electra
  have whistleblower := h.facts.whistleblower fork
  -- the charged newly slashed keys that were credited on `pre`
  set fP := (chargedNewlySlashed pulled counted split tailC).filter fun v =>
    0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat + Internal.syncCr
      eventsP v.toNat with hfP
  have sumP : (∑ v ∈ chargedNewlySlashed pulled counted split tailC,
      if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat + Internal.syncCr
        eventsP v.toNat then
        preset.upwardBand else 0) = preset.upwardBand * fP.card := by
    rw [hfP, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases credit : 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
      Internal.syncCr eventsP v.toNat <;> simp [credit]
  set fB := fP.filter fun v => v.toNat ∈ B with hfB
  set fQ := fP.filter fun v => v.toNat ∉ B with hfQ
  have splitP : fB.card + fQ.card = fP.card :=
    Finset.card_filter_add_card_filter_not (s := fP) (fun v : ValidatorIndex => v.toNat ∈ B)
  have cardFB : fB.card ≤ B.card :=
    Finset.card_le_card_of_injOn (fun v : ValidatorIndex => v.toNat)
      (fun v hv => (Finset.mem_filter.mp hv).2)
      (fun a _ b _ same => UInt64.toNat_inj.mp same)
  -- a charged key credited on `pre`, and not a proposer there, holds a seat of the split
  have seatQ : ∀ v ∈ fQ, ∃ w, split.validators.data[v.toNat]? = some w ∧
      w.pubkey ∈ (split.currentSyncCommittee altairF).value.pubkeys.toList := by
    intro v hv
    obtain ⟨hvP, notB⟩ := Finset.mem_filter.mp hv
    obtain ⟨-, credit⟩ := Finset.mem_filter.mp hvP
    have gross := credit_gross electra h.early pre highC replayedP v.toNat credit
    rcases creditB v.toNat gross with inB | seat
    · exact absurd inB notB
    · exact seat
  have subQ : fQ ⊆ newlySlashed pulled counted split := fun v hv =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).1
  -- the cut keys with a sync debit
  set fK := (Internal.cutKeys config pulled anc fin split).filter fun v =>
    0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat with hfK
  have sumK : (∑ v ∈ Internal.cutKeys config pulled anc fin split,
      if 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat then
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) =
      ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) * fK.card := by
    rw [hfK, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases debit : 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat <;> simp
      [debit]
  -- the rounding of an increment's reward at the whistleblower quotient is a third of a band
  have ceil : 3 * ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 := by
    have rounding := h.facts.rounding
    have vector := h.facts.vector
    have := whistle_round_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat _ whistleblower (by omega)
    omega
  -- the upward band of a shared credit is paid by each exited newly slashed key with such a credit
  set fE := (newlySlashed pulled counted split).filter fun v =>
    (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
      0 < Internal.syncCr eventsF v.toNat with hfE
  have sumE : (∑ v ∈ newlySlashed pulled counted split,
      if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
        (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) =
      preset.upwardBand * fE.card := by
    rw [hfE, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases exit : (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true <;>
      by_cases credit : 0 < Internal.syncCr eventsF v.toNat <;> simp [exit, credit]
  rw [sum_bandR, sum_bandR, sum_bandR, sum_bandR, sum_bandR, sumE, sumP, sumK]
  have upward := h.facts.upward
  have rounding := h.facts.rounding
  have vector := h.facts.vector
  have bandUp : preset.upwardBand ≤
      2 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) := by omega
  generalize preset.upwardBand = UP at bandUp ⊢
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 = β at bandUp ceil ⊢
  generalize ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) = cc at ceil ⊢
  generalize preset.SLOTS_PER_EPOCH.toNat = SPE at cardB ⊢
  generalize hSeats : preset.SYNC_COMMITTEE_SIZE.toNat *
    (((getCurrentEpoch pulled).toNat + 1) / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
    ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) = seats
  set fV := V.filter fun v => 0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum with
    hfV
  set f4 := (stayingKeys pulled counted V).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hf4
  set f5 := (previousOnlyKeys counted V).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hf5
  set f6 := (joinedKeys pulled counted).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hf6
  set fS := (newlySlashed pulled counted split).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hfS
  set U := fS ∪ fE ∪ fQ with hU
  have subU : U ⊆ newlySlashed pulled counted split :=
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) subQ
  -- the charged newly slashed keys are not exited by the finalized state
  have dEQ : Disjoint fE fQ := Finset.disjoint_left.mpr fun v hE hQ =>
    chargedNewlySlashed_not_exited h tailC
      (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1 (Finset.mem_filter.mp hE).2.1
  have dKf : Disjoint fV fK := dKV.symm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have dK456 : Disjoint (f4 ∪ f5 ∪ f6) fK := dKK.symm.mono
    (Finset.union_subset_union (Finset.union_subset_union (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)) (Finset.filter_subset _ _)
  have dKU : Disjoint U fK := dKS.symm.mono subU (Finset.filter_subset _ _)
  have dSK : Disjoint (f4 ∪ f5 ∪ f6) U := dSC.mono
    (Finset.union_subset_union (Finset.union_subset_union (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)) subU
  have dSf : Disjoint fV U := dSV.mono (Finset.filter_subset _ _) subU
  have d45' : Disjoint f4 f5 := d45.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d46' : Disjoint f4 f6 := d46.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d56' : Disjoint f5 f6 := d56.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d4f : Disjoint fV f4 := d4v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d5f : Disjoint fV f5 := d5v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d6f : Disjoint fV f6 := d6v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have inj : Function.Injective fun v : ValidatorIndex => v.toNat := fun a b same =>
    UInt64.toNat_inj.mp same
  -- A key debited on the shared segment is debited on C's run, and any other on R's tail.
  --
  -- A key that exited by the finalized epoch and has a shared credit holds a seat of C's run.
  obtain ⟨everyone, hEveryone⟩ : ∃ everyone, everyone = fV ∪ (f4 ∪ f5 ∪ f6 ∪ U ∪ fK) :=
    ⟨_, rfl⟩
  have replayedFC : fromFin.balanceEvents highC = .ok eventsF := by
    have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have laterNat := UInt64.le_iff_toNat_le.mp h.later
    rw [← DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le fromFin (high := high)
      (localHigh := highC) (by simp only; omega) (by simp only; omega)]
    exact replayedF
  have union := Internal.seat_union_card h fromFin tail tailC high highC replayed replayedFC
    replayedC
    altairF
    ((everyone.filter fun v =>
      0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
        ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
          0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ).image fun v => v.toNat)
    ((everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum).image
      fun v => v.toNat)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      rcases (Finset.mem_filter.mp hv).2 with debit | ⟨exit, credit⟩ | seat
      · exact .inl debit
      · obtain ⟨w, found, exited⟩ := exited_of_exitBeforeFin exit
        exact .inr (.inl ⟨Internal.syncCr_gross_shared h fromFin tailC highC replayedFC v.toNat
          credit,
          fun u run p early proposer => Internal.exited_not_proposer h found exited u run p early
            proposer⟩)
      · exact .inr (.inr (seatQ v seat)))
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hv).2)
  rw [hSeats] at union
  have cover : (everyone.image fun v => v.toNat) ⊆
      ((everyone.filter fun v =>
        0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
            0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ).image fun v => v.toNat) ∪
      ((everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum).image
        fun v => v.toNat) := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    -- a key debited over both runs is debited on one of them
    have debited : 0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum →
        0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          0 < (events.map (Internal.syncDebit v.toNat)).sum := fun pos => by
      simp only [List.map_append, List.sum_append] at pos ⊢
      omega
    have inEv : v ∈ everyone := hv
    have viaF : 0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum →
        v ∈ everyone.filter (fun v =>
          0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
            0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ) ∨
        v ∈ everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum := fun pos =>
      (debited pos).elim
        (fun d => .inl (Finset.mem_filter.mpr ⟨inEv, .inl d⟩))
        (fun d => .inr (Finset.mem_filter.mpr ⟨inEv, d⟩))
    have viaK : 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat →
        v ∈ everyone.filter (fun v =>
          0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
            0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ) ∨
        v ∈ everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum := fun pos =>
      viaF (by simp only [Internal.syncD, List.map_append, List.sum_append] at pos ⊢; omega)
    have inV : v ∈ everyone.filter (fun v =>
        0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
        ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
          0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ) ∨
        v ∈ everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum := by
      have split : v ∈ fV ∪ (f4 ∪ f5 ∪ f6 ∪ U ∪ fK) := hEveryone ▸ hv
      rcases Finset.mem_union.mp split with member | member
      · exact .inl (Finset.mem_filter.mpr ⟨inEv, .inl (Finset.mem_filter.mp member).2⟩)
      · rcases Finset.mem_union.mp member with member | member
        · rcases Finset.mem_union.mp member with member | member
          · rcases Finset.mem_union.mp member with member | member
            · rcases Finset.mem_union.mp member with member | member
              · exact viaF (Finset.mem_filter.mp member).2
              · exact viaF (Finset.mem_filter.mp member).2
            · exact viaF (Finset.mem_filter.mp member).2
          · rcases Finset.mem_union.mp member with member | member
            · rcases Finset.mem_union.mp member with member | member
              · exact viaF (Finset.mem_filter.mp member).2
              · exact .inl (Finset.mem_filter.mpr
                  ⟨inEv, .inr (.inl (Finset.mem_filter.mp member).2)⟩)
            · exact .inl (Finset.mem_filter.mpr ⟨inEv, .inr (.inr member)⟩)
        · exact viaK (Finset.mem_filter.mp member).2
    rcases inV with c | r
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, c, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, r, rfl⟩)
  have union' := (Finset.card_le_card cover).trans union
  have dEQU : Disjoint (f4 ∪ f5 ∪ f6 ∪ U) fK := Finset.disjoint_union_left.mpr ⟨dK456, dKU⟩
  have disjoint : Disjoint fV (f4 ∪ f5 ∪ f6 ∪ U ∪ fK) := by
    rw [Finset.disjoint_union_right, Finset.disjoint_union_right, Finset.disjoint_union_right,
      Finset.disjoint_union_right]
    exact ⟨⟨⟨⟨d4f, d5f⟩, d6f⟩, dSf⟩, dKf⟩
  rw [hEveryone, Finset.card_image_of_injective _ inj, Finset.card_union_of_disjoint disjoint,
    Finset.card_union_of_disjoint dEQU, Finset.card_union_of_disjoint dSK,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d46', d56'⟩),
    Finset.card_union_of_disjoint d45'] at union'
  have subS : fS.card ≤ U.card :=
    Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)
  have subEQ : fE.card + fQ.card ≤ U.card := by
    rw [← Finset.card_union_of_disjoint dEQ]
    exact Finset.card_le_card (Finset.union_subset
      (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right)
  have linear : 3 * fV.card + f4.card + 3 * f5.card + f6.card + 3 * U.card + fK.card ≤
      3 * seats := by
    omega
  have key := bands_arith UP β cc SPE seats fV.card f4.card f5.card f6.card fS.card fE.card
    fQ.card fB.card U.card fK.card bandUp ceil linear subS subEQ (cardFB.trans cardB)
  rw [← splitP]
  linarith

/-- The flag reward of one increment is at most the reward of one increment. -/
private theorem flagRate_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).flagRate ≤
      (pinTerms config state ancestor finalizedState).perIncrement := by
  show _ * _ / _ ≤ _
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum ≤ WEIGHT_DENOMINATOR.toNat := by
    decide
  exact (Nat.div_le_div_right (Nat.mul_le_mul_left _ weights)).trans
    (Nat.mul_div_cancel _ (by decide : 0 < WEIGHT_DENOMINATOR.toNat)).le

/-- The rewards of the keys of a set that a test marks fit a quotient.

The quotient is of the sum over the positions that meet a stronger test.

Each reward is a quotient of the key's value.

A sum of quotients is at most the quotient of the sum. -/
private theorem floor_aux {A : Finset ValidatorIndex} {S : Finset ℕ} {P : ℕ → Prop}
    [DecidablePred P] {c q : ℕ} (f : ℕ → ℕ) (rb : ℕ → Bool)
    (inside : ∀ v ∈ A, rb v.toNat = true → v.toNat ∈ S ∧ P v.toNat) :
    ∑ v ∈ A.filter (fun v => rb v.toNat = true), f v.toNat / q ≤
      (∑ i ∈ S.filter P, f i + c) / q :=
  le_trans (DirectSafety.Apriori.Internal.sum_div_le (A.filter fun v => rb v.toNat = true)
    (fun v : ValidatorIndex => f v.toNat) q)
    (Nat.div_le_div_right (Nat.le_trans (voters_sum_le f fun v hv =>
      Finset.mem_filter.mpr (inside v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2))
      (Nat.le_add_right _ _)))

/-- R's branch budget covers whistleblower rewards, slashings, proposer rewards and rounding. -/
theorem branchR_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    ∃ Wh W : ℕ, (pinTerms config state ancestor finalizedState).branchR =
      -- The slashed, proposer and rounding charges have weight three.
      --
      -- So has the whistleblower charge `Wh`.
      3 * (Wh + W + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (pinTerms config state ancestor finalizedState).slashedR +
        (pinTerms config state ancestor finalizedState).depth *
          (pinTerms config state ancestor finalizedState).proposerCredit +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
          ((pinTerms config state ancestor finalizedState).depth * preset.SLOTS_PER_EPOCH.toNat +
            (pinTerms config state ancestor finalizedState).depth *
              preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
            preset.SYNC_COMMITTEE_SIZE.toNat *
              (((getCurrentEpoch state).toNat + 1) /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
                (getCurrentEpoch finalizedState).toNat /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
                (pinTerms config state ancestor finalizedState).depth /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat))) ∧
      -- The slashed charge covers the flag gain of two windows and the leak of one increment.
      --
      -- The remainder `W` holds those and the unit gain.
      (pinTerms config state ancestor finalizedState).slashedR *
          (2 * (pinTerms config state ancestor finalizedState).depthFin *
            (pinTerms config state ancestor finalizedState).flagRate) +
        (pinTerms config state ancestor finalizedState).slashedR *
          (pinTerms config state ancestor finalizedState).slashLeak +
        (pinTerms config state ancestor finalizedState).unitGain *
          (pinTerms config state ancestor finalizedState).slashedR ≤ W ∧
      -- `Wh` pays the whistleblower reward of any set of keys.
      --
      -- The keys are those that R's call reads as slashed on its branch.
      --
      -- Each reward is the larger of two amounts.
      --
      -- One is at the key's effective balance and rise, the other at its finalized balance.
      ∀ A : Finset ValidatorIndex,
        ∑ v ∈ A.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
          = true), max (balanceAt state v.toNat +
            (pinTerms config state ancestor finalizedState).rise v.toNat)
              (balanceAt finalizedState v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ Wh := by
  -- The slashed charge is an increment and the leak of the dropped balance; the leak joins `W`.
  have charge : ∀ d p a b Q f : ℕ, f ≤ p → a ≤ b →
      2 * d * f + d * (2 * p + a / Q + 1) ≤ d * (2 * (2 * p) + b / Q + 1) :=
    fun d p a b Q f le ab => by
      have floor := Nat.div_le_div_right (c := Q) ab
      calc 2 * d * f + d * (2 * p + a / Q + 1) = d * (2 * f + (2 * p + a / Q + 1)) := by ring
        _ ≤ d * (2 * (2 * p) + b / Q + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨W, D, U, split, gain, unit, floorW⟩ : ∃ W D U : ℕ,
      (pinTerms config state ancestor finalizedState).branchR =
      3 * (W + (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + D) *
          (pinTerms config state ancestor finalizedState).slashedR +
        U * (pinTerms config state ancestor finalizedState).slashedR +
        (pinTerms config state ancestor finalizedState).depth *
          (pinTerms config state ancestor finalizedState).proposerCredit +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
          ((pinTerms config state ancestor finalizedState).depth * preset.SLOTS_PER_EPOCH.toNat +
            (pinTerms config state ancestor finalizedState).depth *
              preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
            preset.SYNC_COMMITTEE_SIZE.toNat *
              (((getCurrentEpoch state).toNat + 1) /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
                (getCurrentEpoch finalizedState).toNat /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
                (pinTerms config state ancestor finalizedState).depth /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat))) ∧
      2 * (pinTerms config state ancestor finalizedState).depthFin *
          (pinTerms config state ancestor finalizedState).flagRate +
        (pinTerms config state ancestor finalizedState).slashLeak ≤ D ∧
      U = (pinTerms config state ancestor finalizedState).unitGain ∧
      ∀ A : Finset ValidatorIndex,
        ∑ v ∈ A.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
          = true), max (balanceAt state v.toNat +
            (pinTerms config state ancestor finalizedState).rise v.toNat)
              (balanceAt finalizedState v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ W := by
    refine ⟨_, _, _, rfl, ?_, rfl, fun A => ?_⟩
    · exact charge _ _ _ _ _ _ (flagRate_le _ _ _ _)
        (by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num))
    · -- The reward of a key is read at its position among the keys slashed on this branch.
      refine floor_aux (A := A) (fun i => max (balanceAt state i +
        (pinTerms config state ancestor finalizedState).rise i) (balanceAt finalizedState i))
        (fun i => (pinTerms config state ancestor finalizedState).slashedRB i) fun v _ flag => ?_
      refine ⟨Finset.mem_range.mpr (slashedRB_lt config state ancestor finalizedState flag), ?_⟩
      rw [Internal.slashedRB_eq] at flag
      exact of_decide_eq_true flag
  subst unit
  refine ⟨W, D * (pinTerms config state ancestor finalizedState).slashedR +
    (pinTerms config state ancestor finalizedState).unitGain *
      (pinTerms config state ancestor finalizedState).slashedR, by rw [split]; ring, ?_, floorW⟩
  have step : (pinTerms config state ancestor finalizedState).slashedR *
      (2 * (pinTerms config state ancestor finalizedState).depthFin *
          (pinTerms config state ancestor finalizedState).flagRate +
        (pinTerms config state ancestor finalizedState).slashLeak) ≤
      D * (pinTerms config state ancestor finalizedState).slashedR :=
    (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_right _ gain)
  rw [Nat.mul_add] at step
  omega

/-- The sync part of the proposer credit is at most the proposer credit. -/
theorem syncProposer_le_credit (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).syncProposer ≤
      (pinTerms config state ancestor finalizedState).proposerCredit :=
  Nat.le_add_left _ _

/-- Keys of R's registry newly slashed on C's branch whose rise funds whistleblower rewards.

They are active at C and do not qualify for R's slashing or slashable-exit charges. -/
def activeNewlySlashed (config : Config) (pulled anc fin counted split : BeaconState preset fork) :
    Finset ValidatorIndex :=
  (newlySlashed pulled counted split).filter fun v =>
    (¬ (pinTerms config pulled anc fin).slashedRB v.toNat = true ∧
      ¬ PinTerms.exitedSlashable anc pulled v.toNat = true) ∧
    isActiveAt counted (getCurrentEpoch counted) v.toNat = true

/-- The share of the cap budget for joined keys outside R's registry.

At a high gain rate each takes the largest cap. -/
def capUse (config : Config) (pulled anc fin counted : BeaconState preset fork) : ℕ :=
  if (pinTerms config pulled anc fin).gainHigh = true then
    ((joinedKeys pulled counted).filter fun v => pulled.validators.data.size ≤ v.toNat).card *
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  else 0

end Internal

end Terms
end PinDrift
end EthLib.Consensus.Models.Network
