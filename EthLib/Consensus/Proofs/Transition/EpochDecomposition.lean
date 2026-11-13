module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.StateTransition

/-!
# Equation-bearing epoch schedules

The fixed schedule records each epoch operation, including identities at inactive forks.

A successful trace retains the intermediate states and the equation of each operation.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- The operations of an epoch, in specification order. -/
inductive EpochStage where
  | justification | inactivity | rewards | registry | slashings | eth1Reset
  | pendingDeposits | pendingConsolidations | payments | effectiveBalances
  | slashingsReset | randaoReset | history | participation | syncCommittees
  | proposerLookahead | ptcWindow

namespace EpochStage

/-- The operations before builder payments. -/
def prefixStages : List EpochStage :=
  [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
    .pendingDeposits, .pendingConsolidations]

/-- Payments and balance updates, followed by the resets and history update. -/
def middleStages : List EpochStage :=
  [.payments, .effectiveBalances, .slashingsReset, .randaoReset, .history]

/-- Participation rotation and the committee updates. -/
def tailStages : List EpochStage :=
  [.participation, .syncCommittees, .proposerLookahead, .ptcWindow]

/-- The complete fixed epoch schedule. -/
def epochStages : List EpochStage := prefixStages ++ middleStages ++ tailStages

/-- One epoch operation, with an identity at forks where it is absent. -/
def action (config : Config) (checks : SignatureChecks) (stage : EpochStage)
    (state : BeaconState preset fork) : Except TransitionError (BeaconState preset fork) :=
  match stage with
  | .justification => processJustificationAndFinalization state
  | .inactivity =>
    if altair : .altair ≤ fork then processInactivityUpdates config state altair else pure state
  | .rewards => processRewardsAndPenalties config state
  | .registry => processRegistryUpdates config state
  | .slashings => processSlashings state
  | .eth1Reset =>
    if before : fork < .hegota then processEth1DataReset before state else pure state
  | .pendingDeposits =>
    if electra : .pectra ≤ fork then processPendingDeposits config checks state electra
    else pure state
  | .pendingConsolidations =>
    if electra : .pectra ≤ fork then processPendingConsolidations state electra else pure state
  | .payments =>
    if gloas : .glamsterdam ≤ fork then liftAccessor (processBuilderPendingPayments state gloas)
    else pure state
  | .effectiveBalances => processEffectiveBalanceUpdates state
  | .slashingsReset => processSlashingsReset state
  | .randaoReset => processRandaoMixesReset state
  | .history =>
    if capella : .shapella ≤ fork then processHistoricalSummariesUpdate state capella
    else processHistoricalRootsUpdate state
  | .participation =>
    if altair : .altair ≤ fork then pure (processParticipationFlagUpdates state altair)
    else processParticipationRecordUpdates state
  | .syncCommittees =>
    if altair : .altair ≤ fork then processSyncCommitteeUpdates state altair else pure state
  | .proposerLookahead =>
    if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead state fulu)
    else pure state
  | .ptcWindow =>
    if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow state gloas)
    else pure state

/-- A stage equation in the operation's native error type, or an identity when disabled. -/
def Edge (config : Config) (checks : SignatureChecks) (stage : EpochStage)
    (s t : BeaconState preset fork) : Prop :=
  match stage with
  | .justification => processJustificationAndFinalization s = .ok t
  | .inactivity =>
    if h : .altair ≤ fork then processInactivityUpdates config s h = .ok t else s = t
  | .rewards => processRewardsAndPenalties config s = .ok t
  | .registry => processRegistryUpdates config s = .ok t
  | .slashings => processSlashings s = .ok t
  | .eth1Reset =>
    if h : fork < .hegota then processEth1DataReset h s = .ok t else s = t
  | .pendingDeposits =>
    if h : .pectra ≤ fork then processPendingDeposits config checks s h = .ok t else s = t
  | .pendingConsolidations =>
    if h : .pectra ≤ fork then processPendingConsolidations s h = .ok t else s = t
  | .payments =>
    if h : .glamsterdam ≤ fork then processBuilderPendingPayments s h = .ok t else s = t
  | .effectiveBalances => processEffectiveBalanceUpdates s = .ok t
  | .slashingsReset => processSlashingsReset s = .ok t
  | .randaoReset => processRandaoMixesReset s = .ok t
  | .history =>
    if h : .shapella ≤ fork then processHistoricalSummariesUpdate s h = .ok t
    else processHistoricalRootsUpdate s = .ok t
  | .participation =>
    if h : .altair ≤ fork then processParticipationFlagUpdates s h = t
    else processParticipationRecordUpdates s = .ok t
  | .syncCommittees =>
    if h : .altair ≤ fork then processSyncCommitteeUpdates s h = .ok t else s = t
  | .proposerLookahead =>
    if h : .fusaka ≤ fork then processProposerLookahead s h = .ok t else s = t
  | .ptcWindow =>
    if h : .glamsterdam ≤ fork then processPtcWindow s h = .ok t else s = t

/-- Remove accessor lifting and resolve each stage's fork guard. -/
theorem action_cases {config : Config} {checks : SignatureChecks} {stage : EpochStage}
    {s t : BeaconState preset fork} :
    action config checks stage s = .ok t ↔ Edge config checks stage s t := by
  cases stage <;> simp only [action, Edge]
  all_goals first
    | rfl
    | split <;> simp only [liftAccessor_ok, pure, Except.pure, Except.ok.injEq]

end EpochStage

/-- The successful equations of a schedule, with its input and output states. -/
inductive EpochTrace {σ ε : Type} (action : EpochStage → σ → Except ε σ) :
    List EpochStage → σ → σ → Prop where
  | nil : EpochTrace action [] s s
  | cons : action k s = .ok u → EpochTrace action ks u t → EpochTrace action (k :: ks) s t

namespace EpochTrace

variable {σ ε : Type} {action : EpochStage → σ → Except ε σ}
  {ks xs ys : List EpochStage} {s t : σ}

/-- Run a schedule with the ordinary monadic left fold. -/
def run (action : EpochStage → σ → Except ε σ) (ks : List EpochStage) (s : σ) :
    Except ε σ := ks.foldlM (fun s k => action k s) s

/-- Success of the fold is exactly an equation-bearing trace. -/
theorem run_ok_iff : run action ks s = .ok t ↔ EpochTrace action ks s t := by
  induction ks generalizing s with
  | nil =>
    simp only [run, List.foldlM_nil, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | cons k ks ih =>
    simp only [run, List.foldlM_cons, bind_ok_iff]
    constructor
    · rintro ⟨u, first, rest⟩
      exact .cons first (ih.mp rest)
    · intro h
      cases h with
      | cons first rest => exact ⟨_, first, ih.mpr rest⟩

/-- Splitting a schedule retains the state at the cut. -/
theorem append_iff : EpochTrace action (xs ++ ys) s t ↔
    ∃ m, EpochTrace action xs s m ∧ EpochTrace action ys m t := by
  simp only [← run_ok_iff, run, List.foldlM_append, bind_ok_iff]

/-- Transport an invariant indexed by the unconsumed part of the schedule. -/
theorem induction_on (Q : List EpochStage → σ → Prop)
    (trace : EpochTrace action ks s t) (start : Q ks s)
    (step : ∀ k rest a b, action k a = .ok b → Q (k :: rest) a → Q rest b) :
    Q [] t := by
  induction trace with
  | nil => exact start
  | cons first rest ih => exact ih (step _ _ _ _ first start)

/-- Compose the relation proved by each equation in a trace. -/
theorem transport (R : σ → σ → Prop) (refl : ∀ a, R a a)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (step : ∀ k ∈ ks, ∀ a b, action k a = .ok b → R a b)
    (trace : EpochTrace action ks s t) : R s t := by
  apply trace.induction_on (fun rest b => (∀ k ∈ rest, k ∈ ks) ∧ R s b)
    ⟨fun _ h => h, refl s⟩ (fun k rest a b eq held =>
      ⟨fun j h => held.1 j (List.mem_cons_of_mem k h),
        trans held.2 (step k (held.1 k List.mem_cons_self) a b eq)⟩) |>.2

end EpochTrace

open EpochStage EpochTrace

/-- The state that the epoch transition reaches before the step of the payments.

It runs the steps of the epoch transition that come before that step, in their order.

Before Altair it skips the inactivity scores, as the epoch transition does. -/
def epochBeforePayments (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Except TransitionError (BeaconState preset fork) := do
  let state ← processJustificationAndFinalization state
  let state ← (if altair : .altair ≤ fork then processInactivityUpdates config state altair
    else pure state)
  let state ← processRewardsAndPenalties config state
  let state ← processRegistryUpdates config state
  let state ← processSlashings state
  let state ← (if before : fork < .hegota then processEth1DataReset before state else pure state)
  processPendingBalances config checks state

/-- The payment prefix is the first eight stages, including its error results. -/
theorem epochBeforePayments_eq_run (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) :
    epochBeforePayments config checks state = run (action config checks) prefixStages state := by
  by_cases electra : Fork.pectra ≤ fork <;>
    simp [epochBeforePayments, processPendingBalances, run, prefixStages,
      List.foldlM_cons, action, electra]

/-- The Altair transition is the fixed schedule, including its error results. -/
theorem processEpochAltair_eq_run (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    processEpochAltair config checks state altair =
      run (action config checks) epochStages state := by
  by_cases electra : Fork.pectra ≤ fork <;>
    by_cases capella : Fork.shapella ≤ fork <;>
    simp [processEpochAltair, processPendingBalances, run, epochStages, prefixStages,
      middleStages, tailStages, List.foldlM_cons, action, altair, electra, capella, bind_assoc]

/-- The schedule also computes the Phase 0 transition, with the same error results. -/
theorem processEpoch_eq_run (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) :
    processEpoch config checks state = run (action config checks) epochStages state := by
  by_cases altair : Fork.altair ≤ fork
  · simpa only [processEpoch, altair, ↓reduceDIte] using
      processEpochAltair_eq_run config checks state altair
  · have electra : ¬ Fork.pectra ≤ fork :=
      fun h => altair (Nat.le_trans (by decide) h)
    have gloas : ¬ Fork.glamsterdam ≤ fork :=
      fun h => altair (Nat.le_trans (by decide) h)
    have fulu : ¬ Fork.fusaka ≤ fork :=
      fun h => altair (Nat.le_trans (by decide) h)
    have capella : ¬ Fork.shapella ≤ fork :=
      fun h => altair (Nat.le_trans (by decide) h)
    have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
    simp [processEpoch, run, epochStages, prefixStages, middleStages, tailStages,
      List.foldlM_cons, action, altair, electra, gloas, fulu, capella, before]

/-- A successful epoch exposes the equations of all its stages. -/
theorem processEpoch_trace {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (computed : processEpoch config checks state = .ok after) :
    EpochTrace (action config checks) epochStages state after :=
  run_ok_iff.mp ((processEpoch_eq_run config checks state).symm.trans computed)

/-- The RANDAO reset separates the balance updates from history and rotation.

After the reset, the equations of history, rotation and the three committee stages follow. -/
theorem processEpoch_randaoCut {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (computed : processEpoch config checks state = .ok after) :
    ∃ cleared mixed rooted rotated synced looked,
      EpochTrace (action config checks)
        (prefixStages ++ [.payments, .effectiveBalances, .slashingsReset]) state cleared ∧
      processRandaoMixesReset cleared = .ok mixed ∧
      Edge config checks .history mixed rooted ∧
      Edge config checks .participation rooted rotated ∧
      Edge config checks .syncCommittees rotated synced ∧
      Edge config checks .proposerLookahead synced looked ∧
      Edge config checks .ptcWindow looked after := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ((prefixStages ++ [.payments, .effectiveBalances, .slashingsReset]) ++
    (.randaoReset :: .history :: tailStages)) _ _ at trace
  obtain ⟨cleared, head, tail⟩ := append_iff.mp trace
  cases tail; rename_i reset tail
  cases tail; rename_i history tail
  cases tail; rename_i rotation tail
  cases tail; rename_i sync tail
  cases tail; rename_i lookahead tail
  cases tail; rename_i window tail
  cases tail
  exact ⟨cleared, _, _, _, _, _, head, reset, action_cases.mp history, action_cases.mp rotation,
    action_cases.mp sync, action_cases.mp lookahead, action_cases.mp window⟩

/-- From Altair, the epoch transition first runs the steps that come before the payments.

It then runs the rest of its steps in their order.

So those first steps are a factor of the epoch transition, and not a second form of it. -/
theorem processEpochAltair_eq_epochBeforePayments_bind (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    processEpochAltair config checks state altair = (do
      let state ← epochBeforePayments config checks state
      let state ← (if gloas : .glamsterdam ≤ fork then
          liftAccessor (processBuilderPendingPayments state gloas)
        else pure state)
      let state ← processEffectiveBalanceUpdates state
      let state ← processSlashingsReset state
      let state ← processRandaoMixesReset state
      let state ← if capella : .shapella ≤ fork then processHistoricalSummariesUpdate state capella
        else processHistoricalRootsUpdate state
      let state := processParticipationFlagUpdates state altair
      let state ← processSyncCommitteeUpdates state altair
      let state ← (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead state fulu)
        else pure state)
      if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow state gloas)
      else pure state) := by
  rw [processEpochAltair_eq_run, epochBeforePayments_eq_run]
  by_cases capella : Fork.shapella ≤ fork <;>
    simp [epochStages, run, List.foldlM_append, middleStages, tailStages,
      List.foldlM_cons, action, altair, capella]

end EthLib.Consensus
