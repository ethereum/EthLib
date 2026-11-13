module

public import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds
public import EthLib.Consensus.Proofs.DirectSafety.Identity
public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Transition.DepositCarry
public import EthLib.Consensus.Proofs.Transition.PendingConsolidations
public import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import EthLib.Consensus.Proofs.Transition.Totality.EffectiveBalances

/-!
# Source bounds over a selected execution interval

The replay below executes the concrete transition passes and records their inputs and results.

It records positive changes per validator, so transfers cannot cancel losses or gains elsewhere.

No caller supplies the amount of a source or an accounting cap.

The source bounds retain the initial queues, scores and balances needed by arbitrary intervals.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

inductive BalanceSource where
  | rewards | penalties | inactivity | slashings | deposits | consolidations
  | withdrawals | sync | excess | crossing
  deriving DecidableEq

structure BalanceEvent (preset : Preset) where
  source : BalanceSource
  before : ForkedBeaconState preset
  after : ForkedBeaconState preset
  creditLimit : Nat
  debitLimit : Nat

def BalanceEvent.credits (event : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range event.after.state.balances.data.size,
    (actualBalanceAt event.after i - actualBalanceAt event.before i)

def BalanceEvent.debits (event : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range event.before.state.balances.data.size,
    (actualBalanceAt event.before i - actualBalanceAt event.after i)

abbrev BalanceReplay (preset : Preset) (fork : Fork) :=
  BeaconState preset fork × List (BalanceEvent preset)

/-- Replay a pass and charge its protocol-computed limits, not its observed balance difference. -/
def recordBalance {fork : Fork} (source : BalanceSource)
    (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (pre : BalanceReplay preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  let (credit, debit) ← limits pre.1
  let post ← action pre.1
  return (post, pre.2 ++ [⟨source, ⟨fork, pre.1⟩, ⟨fork, post⟩, credit, debit⟩])

def carryBalance {fork : Fork}
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (pre : BalanceReplay preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  return (← action pre.1, pre.2)

/-- Separate the reward and penalty updates even when the concrete pass interleaves them. -/
def replayDeltas {fork : Fork} (penaltySource : BalanceSource)
    (deltas : Array Gwei × Array Gwei) (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) :=
  (List.range pre.1.validators.data.size).foldlM (fun pre i => do
    let index ← liftAccessor (liftArith (Uint64.ofNatChecked i))
    let reward := deltas.1.getD i 0
    let penalty := deltas.2.getD i 0
    let pre ← recordBalance .rewards (fun _ => pure (reward.toNat, 0))
      (fun s => liftAccessor (increaseBalance s index reward)) pre
    recordBalance penaltySource (fun _ => pure (0, penalty.toNat))
      (fun s => liftAccessor (decreaseBalance s index penalty)) pre) pre

def replayRewards {fork : Fork} (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  if getCurrentEpoch pre.1 = GENESIS_EPOCH then return pre
  let ordinary ← rewardPasses pre.1
  let inactivity ← getInactivityPenaltyDeltas config pre.1
  if .altair ≤ fork then
    let pre ← ordinary.foldlM (fun pre deltas => replayDeltas .penalties deltas pre) pre
    replayDeltas .inactivity inactivity pre
  else
    -- Phase 0 combines arrays first; splitting their saturating debits has the same endpoint.
    let rewards ← (List.range pre.1.validators.data.size).mapM fun i =>
      liftAccessor (liftArith (Uint64.ofNatChecked
        ((ordinary.map fun p => (p.1.getD i 0).toNat).sum)))
    let pre ← replayDeltas .penalties (rewards.toArray, #[]) pre
    let pre ← ordinary.foldlM (fun pre p => replayDeltas .penalties (#[], p.2) pre) pre
    replayDeltas .inactivity (#[], inactivity.2) pre

/-- One stage of the epoch replay, over the stages that run before the payments.

Justification, inactivity, registry updates and the eth1 reset change no balance and record nothing.

The rewards and the slashings record their protocol-computed limits.

Pending deposits and pending consolidations record their consumed amounts.

A stage that is absent at the fork, or that runs after the payments, leaves the pair unchanged. -/
private def epochReplayAction {fork : Fork} (stage : EpochStage) (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) :=
  match stage with
  | .justification => carryBalance processJustificationAndFinalization pre
  | .inactivity =>
    if altair : .altair ≤ fork then carryBalance (processInactivityUpdates config · altair) pre
    else pure pre
  | .rewards => replayRewards (config := config) pre
  | .registry => carryBalance (processRegistryUpdates config) pre
  | .slashings =>
    recordBalance .slashings (fun s => return (0, ← delayedSlashingLimit s)) processSlashings pre
  | .eth1Reset =>
    if before : fork < .hegota then carryBalance (processEth1DataReset before) pre else pure pre
  | .pendingDeposits =>
    if electra : .pectra ≤ fork then do
      let deposited ← processPendingDeposits config checks pre.1 electra
      return (deposited, pre.2 ++ [⟨.deposits, ⟨fork, pre.1⟩, ⟨fork, deposited⟩,
        consumedDeposits pre.1 deposited electra, 0⟩])
    else pure pre
  | .pendingConsolidations =>
    if electra : .pectra ≤ fork then do
      let consolidated ← processPendingConsolidations pre.1 electra
      let moved := consumedConsolidations pre.1 consolidated electra
      return (consolidated, pre.2 ++
        [⟨.consolidations, ⟨fork, pre.1⟩, ⟨fork, consolidated⟩, moved, moved⟩])
    else pure pre
  | _ => pure pre

/-- The replay ends after the last balance-changing epoch pass, before effective-balance updates.

It runs the stages before the payments, in the order of the epoch schedule. -/
@[no_expose] def epochBalanceReplay {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError (BalanceReplay preset fork) :=
  EpochTrace.run (epochReplayAction (config := config) (checks := checks))
    EpochStage.prefixStages (s, [])

def slashingLimits {fork : Fork} (indices : List ValidatorIndex) (s : BeaconState preset fork) :
    Except TransitionError (Nat × Nat) := do
  let validators ← liftAccessor (indices.mapM (getValidator s))
  let p := EthLib.Consensus.parameters preset fork
  return ((validators.map fun v => v.effectiveBalance.toNat /
      p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat).sum,
    (validators.map fun v => v.effectiveBalance.toNat / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat).sum)

/-- Pre-Gloas block replay, with limits read at the actual site of each operation. -/
def blockBalanceReplay {fork : Fork} (early : fork < .glamsterdam)
    (engine : ExecutionEngine preset fork) (s : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  let before := Nat.lt_trans early (by decide : Fork.glamsterdam < .hegota)
  let pre ← carryBalance (processBlockHeader · block) (s, [])
  let pre ← if bellatrix : .bellatrix ≤ fork then
      recordBalance .withdrawals (fun s => do
        if capella : .shapella ≤ fork then
          return (0, ((← getExpectedWithdrawals s capella).withdrawals.toList.map
            fun w => w.amount.toNat).sum)
        else return (0, 0))
        (processBlockExecution config checks engine · block.body bellatrix) pre
    else pure pre
  let pre ← carryBalance (processRandao config checks · block.body) pre
  let pre ← carryBalance (processEth1Data before · block.body) pre
  let expected ← expectedDepositCount pre.1 before
  let deposits := (block.body.deposits before).data
  ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
  let pre ← block.body.proposerSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits [sl.signedHeader1.message.proposerIndex])
      (processProposerSlashing config checks · sl) pre) pre
  let pre ← block.body.attesterSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits (slashingIndices sl))
      (processAttesterSlashing config checks · sl) pre) pre
  let pre ← block.body.attestations.data.toList.foldlM (fun pre att =>
    recordBalance .rewards (fun site => do
      return (← attestationCredit site att s.latestBlockHeader.slot, 0))
      (processAttestation config checks · s.latestBlockHeader.slot att) pre) pre
  let pre ← (block.body.deposits before).data.toList.foldlM (fun pre dep =>
    recordBalance .deposits (fun _ => pure (if fork < .pectra then dep.data.amount.toNat else 0, 0))
      (processDeposit config checks before · dep) pre) pre
  let pre ← carryBalance (fun s => block.body.voluntaryExits.data.foldlM
    (processVoluntaryExit config checks) s) pre
  let pre ← carryBalance (processBlsToExecutionChanges config checks · block.body) pre
  let pre ← if electra : .pectra ≤ fork then do
      let requests := block.body.executionRequests ⟨electra, early⟩
      let pre ← carryBalance (fun s => requests.deposits.data.foldlM
        (processDepositRequest · electra ·) s) pre
      let pre ← carryBalance (fun s => requests.withdrawals.data.foldlM
        (processWithdrawalRequest config · electra ·) s) pre
      requests.consolidations.data.toList.foldlM (fun pre request =>
        recordBalance .excess (fun s => pure (0,
          match findValidatorByPubkey s request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
          (processConsolidationRequest config · electra request) pre) pre
    else pure pre
  if altair : .altair ≤ fork then
    recordBalance .sync (fun s => do
      let reward ← syncParticipantReward s
      let proposer ← liftAccessor (liftArith do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
      return (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat))
      (processSyncAggregate config checks · altair (block.body.syncAggregate altair)) pre
  else pure pre

private theorem replay_fold_result {α : Type} {fork : Fork}
    (action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork))
    (replay : BalanceReplay preset fork → α → Except TransitionError (BalanceReplay preset fork))
    (step : ∀ s x t, action s x = .ok t → ∀ events,
      ∃ recorded, replay (s, events) x = .ok (t, recorded))
    (items : List α) (s t : BeaconState preset fork)
    (ok : items.foldlM action s = .ok t) (events : List (BalanceEvent preset)) :
    ∃ recorded, items.foldlM replay (s, events) = .ok (t, recorded) := by
  induction items generalizing s events with
  | nil =>
    cases ok
    exact ⟨events, rfl⟩
  | cons x xs ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok ⊢
    obtain ⟨middle, first, rest⟩ := ok
    obtain ⟨recorded, replayed⟩ := step s x middle first events
    obtain ⟨final, replayedRest⟩ := ih middle rest recorded
    exact ⟨final, (middle, recorded), replayed, replayedRest⟩

private theorem replayDeltas_result {fork : Fork} (s t : BeaconState preset fork)
    (source : BalanceSource) (deltas : Array Gwei × Array Gwei)
    (ok : applyAllDeltas s deltas = .ok t) (events : List (BalanceEvent preset)) :
    ∃ recorded, replayDeltas source deltas (s, events) = .ok (t, recorded) := by
  unfold replayDeltas applyAllDeltas at *
  apply replay_fold_result _ _ ?_ _ s t ok events
  intro state i after step previous
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨index, indexOk, raised, raisedOk, loweredOk⟩ := step
  have indexLift := liftAccessor_ok.mpr indexOk
  have raisedLift := liftAccessor_ok.mpr raisedOk
  have loweredLift := liftAccessor_ok.mpr loweredOk
  simp only [recordBalance, indexLift, raisedLift, loweredLift,
    bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

private theorem replayRewards_altair {fork : Fork} (altair : .altair ≤ fork)
    (s t : BeaconState preset fork) (events : List (BalanceEvent preset))
    (ok : processRewardsAndPenalties config s = .ok t) :
    ∃ recorded, replayRewards (config := config) (s, events) = .ok (t, recorded) := by
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · simp only [processRewardsAndPenalties, genesis, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq] at ok
    subst t
    exact ⟨events, by simp only [replayRewards, genesis, ↓reduceIte]; rfl⟩
  · simp only [processRewardsAndPenalties, genesis, altair, ↓reduceIte, ↓reduceDIte,
      bind_ok_iff, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      bind_pure] at ok
    obtain ⟨ordinary, ordinaryOk, inactivity, inactivityOk, middle, ordinaryApplied,
      inactivityApplied⟩ := ok
    obtain ⟨recorded, ordinaryReplay⟩ := replay_fold_result applyAllDeltas
      (fun pre deltas => replayDeltas .penalties deltas pre)
      (fun s deltas t ok events => replayDeltas_result s t .penalties deltas ok events)
      ordinary s middle ordinaryApplied events
    obtain ⟨final, inactivityReplay⟩ :=
      replayDeltas_result middle t .inactivity inactivity inactivityApplied recorded
    refine ⟨final, ?_⟩
    simp only [replayRewards, rewardPasses, genesis, altair, ↓reduceIte, ↓reduceDIte,
      ordinaryOk, inactivityOk, ordinaryReplay, inactivityReplay,
      bind, Except.bind]

private theorem replay_distinct_exists {α σ ε : Type} {step : σ → α → Except ε σ}
    (key : α → Nat) (Ready : σ → α → Prop)
    (advance : ∀ last x, Ready last x → ∃ next, step last x = .ok next ∧
      ∀ y, key y ≠ key x → Ready last y → Ready next y) :
    ∀ (xs : List α) (start : σ), (xs.map key).Nodup → (∀ x ∈ xs, Ready start x) →
      ∃ out, xs.foldlM step start = .ok out
  | [], start, _, _ => ⟨start, rfl⟩
  | x :: rest, start, distinct, ready => by
    rw [List.map_cons, List.nodup_cons] at distinct
    obtain ⟨next, stepped, keeps⟩ := advance start x (ready x List.mem_cons_self)
    obtain ⟨out, folded⟩ := replay_distinct_exists key Ready advance rest next distinct.2
      fun y member => keeps y (fun same => distinct.1 (same ▸ List.mem_map_of_mem member))
        (ready y (List.mem_cons_of_mem _ member))
    exact ⟨out, by rw [List.foldlM_cons, stepped]; exact folded⟩

private theorem replay_apply_exists {fork : Fork} (s : BeaconState preset fork)
    (rewards penalties : Array Gwei)
    (ready : ∀ i, i < s.validators.data.size → i < 2 ^ 64 ∧
      ∃ balance, s.balances.data[i]? = some balance ∧
        balance.toNat + (rewards.getD i 0).toNat < 2 ^ 64) :
    ∃ t, applyAllDeltas s (rewards, penalties) = .ok t := by
  unfold applyAllDeltas
  refine replay_distinct_exists id (fun (last : BeaconState preset fork) i =>
      ∃ inside : i < last.balances.data.size, i < 2 ^ 64 ∧
        last.balances.data[i].toNat + (rewards.getD i 0).toNat < 2 ^ 64)
    (fun last i ⟨inside, lt, fit⟩ => ?_) _ s (by simpa using List.nodup_range) ?_
  · intro i member
    obtain ⟨small, balance, found, fits⟩ := ready i (List.mem_range.mp member)
    obtain ⟨inside, same⟩ := Array.getElem?_eq_some_iff.mp found
    exact ⟨inside, small, by simpa [same] using fits⟩
  · refine ⟨_, applyDeltas_eq_ok_iff.mpr ⟨lt, inside, fit, rfl⟩,
      fun j other ⟨insideJ, ltJ, fitJ⟩ => ?_⟩
    have ne : i ≠ j := fun same => other same.symm
    exact ⟨by simpa [BeaconState.putBalance] using insideJ, ltJ,
      by simpa [BeaconState.putBalance, Array.getElem_set, ne] using fitJ⟩

private theorem replay_indices_small {fork : Fork} {s t : BeaconState preset fork}
    {deltas : Array Gwei × Array Gwei} (ok : applyAllDeltas s deltas = .ok t)
    {i : Nat} (inside : i < s.validators.data.size) : i < 2 ^ 64 := by
  have all := foldlM_forall_of_ok (P := fun j => j < 2 ^ 64)
    (fun _ _ _ step => (applyDeltas_eq_ok_iff.mp step).1) _ _ _ ok
  exact all i (List.mem_range.mpr inside)

private theorem replay_penalties_exists {fork : Fork} (s : BeaconState preset fork)
    (penalties : List (Array Gwei))
    (ready : ∀ i, i < s.validators.data.size → i < 2 ^ 64 ∧
      ∃ balance, s.balances.data[i]? = some balance) :
    ∃ t, (penalties.map fun p => (#[], p)).foldlM applyAllDeltas s = .ok t := by
  induction penalties generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons p ps ih =>
    obtain ⟨middle, applied⟩ := replay_apply_exists s #[] p (fun i inside => by
      obtain ⟨small, balance, found⟩ := ready i inside
      exact ⟨small, balance, found, by simpa using balance.toNat_lt_size⟩)
    have sizes := sameSizes_applyAllDeltas applied
    obtain ⟨t, rest⟩ := ih middle (fun i inside => by
      rw [sizes.1] at inside
      obtain ⟨balance, _, _, found⟩ := (applyAllDeltas_balances applied i).1 inside
      exact ⟨(ready i inside).1, _, found⟩)
    exact ⟨t, by simpa only [List.map_cons, List.foldlM_cons, applied, bind, Except.bind]
      using rest⟩

/-- The instrumented reward pass has the same endpoint as the real reward pass. -/
private theorem replayRewards_result {fork : Fork} (s t : BeaconState preset fork)
    (events : List (BalanceEvent preset))
    (ok : processRewardsAndPenalties config s = .ok t) :
    ∃ recorded, replayRewards (config := config) (s, events) = .ok (t, recorded) := by
  by_cases altair : .altair ≤ fork
  · exact replayRewards_altair altair s t events ok
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · simp only [processRewardsAndPenalties, genesis, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq] at ok
    subst t
    exact ⟨events, by simp only [replayRewards, genesis, ↓reduceIte]; rfl⟩
  simp only [processRewardsAndPenalties, genesis, altair, ↓reduceIte, ↓reduceDIte,
    bind_ok_iff] at ok
  obtain ⟨⟨rewards, penalties⟩, computed, applied⟩ := ok
  obtain ⟨source, target, head, inclusion, inactivity, sourceOk, targetOk, headOk,
    inclusionOk, inactivityOk, sums⟩ := getAttestationDeltas_getD _ computed
  let ordinary := [source, target, head, inclusion]
  let amounts := (List.range s.validators.data.size).map fun i => rewards.getD i 0
  have amountsOk : (List.range s.validators.data.size).mapM (fun i =>
      liftAccessor (liftArith (Uint64.ofNatChecked
        ((ordinary.map fun p => (p.1.getD i 0).toNat).sum)))) = .ok amounts := by
    apply mapM_eq_ok_iff.mpr
    refine ⟨by simp [amounts], fun i inside => ?_⟩
    simp only [List.length_range] at inside
    have sum := (sums i inside).1
    have value : ((ordinary.map fun p => (p.1.getD i 0).toNat).sum) =
        (rewards.getD i 0).toNat := by simpa [ordinary, Nat.add_assoc] using sum.symm
    simp only [amounts, List.getElem_map, List.getElem_range, value]
    rw [Uint64.ofNatChecked_ok_iff.mpr ⟨(rewards.getD i 0).toNat_lt_size, rfl⟩]
    rfl
  have amountAt (i : Nat) (inside : i < s.validators.data.size) :
      amounts.toArray.getD i 0 = rewards.getD i 0 := by
    simp [amounts, Array.getD, inside]
  obtain ⟨raised, raisedOk⟩ := replay_apply_exists s amounts.toArray #[] (fun i inside => by
    obtain ⟨balance, found, fits, _⟩ := (applyAllDeltas_balances applied i).1 inside
    exact ⟨replay_indices_small applied inside, balance, found, by rwa [amountAt i inside]⟩)
  let ps := [source.2, target.2, head.2, inclusion.2, inactivity.2]
  obtain ⟨final, loweredOk⟩ := replay_penalties_exists raised ps (fun i inside => by
    have original : i < s.validators.data.size :=
      (sameSizes_applyAllDeltas raisedOk).1 ▸ inside
    obtain ⟨balance, _, _, found⟩ := (applyAllDeltas_balances raisedOk i).1 original
    exact ⟨replay_indices_small applied original, _, found⟩)
  have inclusionZero (i : Nat) : inclusion.2.getD i 0 = 0 := by
    unfold getInclusionDelayDeltas at inclusionOk
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at inclusionOk
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := inclusionOk
    exact replicate_getD_zero _ _
  have endpoint : final = t := by
    have finalFrame : final = {s with balances := final.balances} := by
      have kept := foldlM_ok_invariant
        (fun next : BeaconState preset fork => next = {s with balances := next.balances})
        (fun _ _ _ previous step => by rw [applyAllDeltas_frame step, previous])
        (applyAllDeltas_frame raisedOk) loweredOk
      exact kept
    have balances : final.balances = t.balances := by
      suffices data : final.balances.data = t.balances.data by
        have ext (a b : Balances preset fork) (h : a.data = b.data) : a = b := by
          cases a
          cases b
          cases h
          rfl
        exact ext _ _ data
      apply Array.ext_getElem?
      intro i
      by_cases inside : i < s.validators.data.size
      · obtain ⟨balance, found, fits, result⟩ := (applyAllDeltas_balances applied i).1 inside
        obtain ⟨balance', found', fits', result'⟩ :=
          (applyAllDeltas_balances raisedOk i).1 inside
        have same : balance' = balance := Option.some.inj (found'.symm.trans found)
        subst balance'
        have lowered := (foldlM_applyAllDeltas_balances loweredOk i).1
          (by rwa [(sameSizes_applyAllDeltas raisedOk).1])
        rw [lowered, result', result]
        simp only [Option.map_some, Option.some.injEq]
        apply UInt64.toNat_inj.mp
        have empty : (#[] : Array Gwei).getD i 0 = 0 := by simp
        simp only [ps, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          empty, UInt64.add_zero, Uint64.toNat_saturatingSub, UInt64.toNat_zero,
          Nat.sub_zero, amountAt i inside, inclusionZero]
        rw [← Nat.sub_add_eq, ← Nat.sub_add_eq, ← Nat.sub_add_eq]
        rw [(sums i inside).2]
        simp only [Nat.add_assoc]
      · rw [(applyAllDeltas_balances applied i).2 (by omega)]
        rw [(foldlM_applyAllDeltas_balances loweredOk i).2.2
          (by rw [(sameSizes_applyAllDeltas raisedOk).1]; omega)]
        exact (applyAllDeltas_balances raisedOk i).2 (by omega)
    rw [finalFrame, applyAllDeltas_frame applied, balances]
  subst final
  have folded : ((amounts.toArray, #[]) :: ps.map (fun p => (#[], p))).foldlM
      applyAllDeltas s = .ok t := by
    simpa only [List.foldlM_cons, raisedOk, bind, Except.bind] using loweredOk
  -- The final inactivity pass has the same state action, but a different event label.
  simp only [ps, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil,
    bind_pure, bind_ok_iff] at folded
  obtain ⟨r, rOk, a, aOk, b, bOk, c, cOk, d, dOk, lastOk⟩ := folded
  obtain ⟨er, erOk⟩ := replayDeltas_result s r .penalties _ rOk events
  obtain ⟨ea, eaOk⟩ := replayDeltas_result r a .penalties _ aOk er
  obtain ⟨eb, ebOk⟩ := replayDeltas_result a b .penalties _ bOk ea
  obtain ⟨ec, ecOk⟩ := replayDeltas_result b c .penalties _ cOk eb
  obtain ⟨ed, edOk⟩ := replayDeltas_result c d .penalties _ dOk ec
  obtain ⟨et, etOk⟩ := replayDeltas_result d t .inactivity _ lastOk ed
  refine ⟨et, ?_⟩
  simp only [replayRewards, rewardPasses, genesis, altair, ↓reduceIte, ↓reduceDIte,
    sourceOk, targetOk, headOk, inclusionOk, inactivityOk, bind, Except.bind, pure, Except.pure]
  change (do
    let rs ← (List.range s.validators.data.size).mapM (fun i =>
      liftAccessor (liftArith (Uint64.ofNatChecked
        ((ordinary.map fun (p : Array Gwei × Array Gwei) => (p.1.getD i 0).toNat).sum))))
    let pre ← replayDeltas .penalties (rs.toArray, #[]) (s, events)
    let pre ← ordinary.foldlM
      (fun pre (p : Array Gwei × Array Gwei) => replayDeltas .penalties (#[], p.2) pre) pre
    replayDeltas .inactivity (#[], inactivity.2) pre) = .ok (t, et)
  simp only [amountsOk, erOk, ordinary, List.foldlM_cons, List.foldlM_nil,
    eaOk, ebOk, ecOk, edOk, etOk, bind, Except.bind, pure, Except.pure]

private theorem carryBalance_result {fork : Fork} {s t : BeaconState preset fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    (ok : action s = .ok t) (events : List (BalanceEvent preset)) :
    carryBalance action (s, events) = .ok (t, events) := by
  simp [carryBalance, ok]

private theorem recordBalance_result {fork : Fork} {s t : BeaconState preset fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    (ok : action s = .ok t) (bounded : ∃ limit, limits s = .ok limit)
    (source : BalanceSource) (events : List (BalanceEvent preset)) :
    ∃ recorded, recordBalance source limits action (s, events) = .ok (t, recorded) := by
  obtain ⟨⟨credit, debit⟩, computed⟩ := bounded
  refine ⟨events ++ [⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩], ?_⟩
  simp only [recordBalance, computed, ok, bind, Except.bind, pure, Except.pure]

private theorem delayedSlashingLimit_result {fork : Fork} {s t : BeaconState preset fork}
    (ok : processSlashings s = .ok t) : ∃ limit, delayedSlashingLimit s = .ok limit := by
  simp only [processSlashings, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨total, totalOk, sum, sumOk, scaled, scaledOk, _⟩ := ok
  simp only [delayedSlashingLimit, bind_ok_iff, liftAccessor_ok, totalOk, sumOk,
    Except.ok.injEq, pure, Except.pure]
  exact ⟨_, total, rfl, sum, rfl, rfl⟩

/-- Justification, inactivity, registry updates and the eth1 reset record nothing. -/
private theorem epochReplayAction_carried {fork : Fork} {k : EpochStage}
    (member : k ∈ [EpochStage.justification, .inactivity, .registry, .eth1Reset])
    {s t : BeaconState preset fork} (edge : EpochStage.Edge config checks k s t)
    (events : List (BalanceEvent preset)) :
    epochReplayAction (config := config) (checks := checks) k (s, events) = .ok (t, events) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp only [EpochStage.Edge] at edge <;>
    simp only [epochReplayAction]
  case inl | inr.inr.inl => exact carryBalance_result edge events
  all_goals
    split at edge <;> rename_i h <;> simp only [h, ↓reduceDIte]
    · exact carryBalance_result edge events
    · subst edge
      rfl

/-- Each stage before the payments has a replay step that reaches the same state. -/
private theorem epochReplayAction_of_action {fork : Fork} {k : EpochStage}
    (member : k ∈ EpochStage.prefixStages) {s t : BeaconState preset fork}
    (ok : EpochStage.action config checks k s = .ok t) (events : List (BalanceEvent preset)) :
    ∃ recorded, epochReplayAction (config := config) (checks := checks) k (s, events) =
      .ok (t, recorded) := by
  have edge := EpochStage.action_cases.mp ok
  cases k
  case justification | inactivity | registry | eth1Reset =>
    exact ⟨events, epochReplayAction_carried (by simp) edge events⟩
  all_goals simp only [EpochStage.Edge] at edge
  all_goals simp only [epochReplayAction]
  case rewards => exact replayRewards_result s t events edge
  case slashings =>
    obtain ⟨limit, computed⟩ := delayedSlashingLimit_result edge
    exact recordBalance_result edge ⟨(0, limit), by rw [computed]; rfl⟩ .slashings events
  case pendingDeposits | pendingConsolidations =>
    split at edge <;> rename_i h <;> simp only [h, ↓reduceDIte]
    · simp only [edge, bind, Except.bind, pure, Except.pure]
      exact ⟨_, rfl⟩
    · subst edge
      exact ⟨events, rfl⟩
  all_goals simp [EpochStage.prefixStages] at member

/-- A trace of stages before the payments has a replay trace with the same end state. -/
private theorem epochReplay_of_trace {fork : Fork} {ks : List EpochStage}
    {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks) ks s t)
    (inside : ∀ k ∈ ks, k ∈ EpochStage.prefixStages) (events : List (BalanceEvent preset)) :
    ∃ recorded, EpochTrace (epochReplayAction (config := config) (checks := checks)) ks
      (s, events) (t, recorded) := by
  induction trace generalizing events with
  | nil => exact ⟨events, .nil⟩
  | cons first rest ih =>
    obtain ⟨middle, step⟩ := epochReplayAction_of_action (inside _ List.mem_cons_self) first events
    obtain ⟨recorded, tail⟩ := ih (fun k member => inside k (List.mem_cons_of_mem _ member)) middle
    exact ⟨recorded, .cons step tail⟩

/-- The stages before the payments have a replay with the same end state. -/
theorem epochBalanceReplay_before {fork : Fork} {s t : BeaconState preset fork}
    (ok : epochBeforePayments config checks s = .ok t) :
    ∃ events, epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events) := by
  rw [epochBeforePayments_eq_run] at ok
  obtain ⟨events, trace⟩ := epochReplay_of_trace (EpochTrace.run_ok_iff.mp ok)
    (fun _ member => member) []
  exact ⟨events, EpochTrace.run_ok_iff.mpr trace⟩

/-- The remaining epoch passes keep balances; the replay endpoint is the effective-update input.

The epoch is cut after the stages before the payments, which have a replay.

Before Gloas the payments are the identity.

The stages after the effective-balance update keep the validators and the balances. -/
theorem epochBalanceReplay_result {fork : Fork} (s t : BeaconState preset fork)
    (early : fork < .glamsterdam) (ok : processEpoch config checks s = .ok t) :
    ∃ middle updated events,
      epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events) ∧
      processEffectiveBalanceUpdates middle = .ok updated ∧
      updated.validators = t.validators ∧ middle.balances = t.balances := by
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have trace := processEpoch_trace ok
  change EpochTrace _ (EpochStage.prefixStages ++ [.payments, .effectiveBalances,
    .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨middle, head, tail⟩ := EpochTrace.append_iff.mp trace
  obtain ⟨events, replay⟩ := epochReplay_of_trace head (fun _ member => member) []
  cases tail
  rename_i paid paidOk tail
  cases tail
  rename_i updated updatedOk tail
  have paidEdge := EpochStage.action_cases.mp paidOk
  simp only [EpochStage.Edge, gloas, ↓reduceDIte] at paidEdge
  subst paidEdge
  have updatedEdge := EpochStage.action_cases.mp updatedOk
  have kept := balanceDrift_late tail
  exact ⟨middle, updated, events, EpochTrace.run_ok_iff.mpr replay, updatedEdge, kept.1.symm,
    ((kept.2).trans (processEffectiveBalanceUpdates_balances updatedEdge)).symm⟩

private theorem slashingLimits_result {fork : Fork} (s : BeaconState preset fork)
    (indices : List ValidatorIndex)
    (found : ∀ i ∈ indices, ∃ v, getValidator s i = .ok v) :
    ∃ limit, slashingLimits indices s = .ok limit := by
  obtain ⟨validators, computed⟩ := mapM_exists_ok found
  simp only [slashingLimits, bind_ok_iff, liftAccessor_ok]
  exact ⟨_, validators, computed, rfl⟩

private theorem proposerLimits_result {fork : Fork} {s t : BeaconState preset fork}
    {sl : ProposerSlashing} (ok : processProposerSlashing config checks s sl = .ok t) :
    ∃ limit, slashingLimits [sl.signedHeader1.message.proposerIndex] s = .ok limit := by
  simp only [processProposerSlashing, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, proposer, found, _⟩ := ok
  apply slashingLimits_result
  intro i member
  simp only [List.mem_singleton] at member
  exact member ▸ ⟨proposer, found⟩

private theorem attesterLimits_result {fork : Fork} {s t : BeaconState preset fork}
    {sl : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s sl = .ok t) :
    ∃ limit, slashingLimits (slashingIndices sl) s = .ok limit := by
  obtain ⟨_, first, _⟩ := processAttesterSlashing_checks ok
  obtain ⟨_, _, _, pubkeys, _⟩ := isValidIndexedAttestation_signature first
  apply slashingLimits_result
  intro i member
  rw [slashingIndices, mem_sortedSet, List.mem_filter, decide_eq_true_iff] at member
  rw [Array.mapM_eq_mapM_toList] at pubkeys
  change (do
    let keys ← sl.attestation1.attestingIndices.data.toList.mapM
      (fun index => do return (← liftAccessor (getValidator s index)).pubkey)
    pure keys.toArray) = .ok _ at pubkeys
  rw [bind_ok_iff] at pubkeys
  obtain ⟨keys, mapped, _⟩ := pubkeys
  obtain ⟨key, computed⟩ := mapM_ok_of_mem mapped i (by simpa using member.1)
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨v, found, _⟩ := computed
  exact ⟨v, found⟩

private theorem attestationCredit_result {fork : Fork} {s t : BeaconState preset fork}
    {att : Attestation preset fork} {parent : Slot}
    (ok : processAttestation config checks s parent att = .ok t) :
    ∃ credit, attestationCredit s att parent = .ok credit := by
  unfold processAttestation at ok
  split at ok <;> rename_i altair
  · simp only [processAttestationAltair, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, earnedOk,
      _, _, _, _, _, _, total, totalOk, attesters, attestersOk, result, resultOk, _⟩ := ok
    simp only [attestationCredit, altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok]
    exact ⟨_, earned, earnedOk, total, totalOk, attesters, attestersOk,
      result, resultOk, rfl⟩
  · simp only [attestationCredit, altair, ↓reduceDIte]
    exact ⟨0, rfl⟩

private theorem syncLimits_result {fork : Fork} {s t : BeaconState preset fork}
    {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∃ reward proposer,
      syncParticipantReward s = .ok reward ∧
      liftAccessor (liftArith (do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))) =
        (Except.ok proposer : Except TransitionError Gwei) := by
  simp only [processSyncAggregate, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposer, proposerOk, _⟩ := ok
  exact ⟨reward, proposer, rewardOk, proposerOk⟩

private theorem execution_bounds {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (body : BeaconBlockBody preset fork) (bellatrix : .bellatrix ≤ fork)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ debit, (if capella : .shapella ≤ fork then do
        return (0, ((← getExpectedWithdrawals s capella).withdrawals.toList.map
          fun w => w.amount.toNat).sum)
      else pure (0, 0)) = Except.ok (0, debit) ∧
      balanceCredits s t ≤ 0 ∧ balanceDebits s t ≤ debit := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr early
  simp only [processBlockExecution, notGloas, ↓reduceDIte] at ok
  split at ok
  · rename_i capella
    obtain ⟨u, withdrawals, payload⟩ := bind_ok_iff.mp ok
    obtain ⟨_, header, _, rfl⟩ := processExecutionPayload_ok payload
    obtain ⟨expected, expectedOk, _, applied⟩ := processWithdrawals_expected early withdrawals
    obtain ⟨v, applied, balances, _⟩ := applyExpectedWithdrawals_balances applied
    have bounds := withdrawal_debit_bound s v expected.withdrawals applied
    refine ⟨(expected.withdrawals.toList.map fun w => w.amount.toNat).sum, ?_, ?_, ?_⟩
    · simp [capella, expectedOk, bind, Except.bind, pure, Except.pure]
    · simpa only [balanceCredits, actualBalanceAt, balances] using bounds.1.le
    · simpa only [balanceDebits, actualBalanceAt, balances] using bounds.2
  · rename_i notCapella
    refine ⟨0, by simp [notCapella, pure, Except.pure], ?_⟩
    split at ok
    · obtain ⟨_, header, _, rfl⟩ := processExecutionPayload_ok ok
      simp [balanceCredits, balanceDebits, actualBalanceAt]
    · cases ok
      simp [balanceCredits, balanceDebits]

/-- Every real pre-Gloas block has the exact endpoint of the instrumented passes. -/
private theorem blockBalanceReplay_result {fork : Fork} (s t : BeaconState preset fork)
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork)
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ events, blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok (t, events) := by
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  obtain ⟨voted, operated, ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk,
    randaoOk, eth1Ok⟩, operationsOk, _, syncOk⟩ := processBlock_operationsInput ok
  simp only [gloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at paidOk
  subst paidOk
  simp only [before, ↓reduceDIte] at eth1Ok
  have executedReplay : ∃ events,
      (if bellatrix : Fork.bellatrix ≤ fork then
        recordBalance .withdrawals (fun site => do
          if capella : Fork.shapella ≤ fork then
            return (0, ((← getExpectedWithdrawals site capella).withdrawals.toList.map
              fun w => w.amount.toNat).sum)
          else return (0, 0))
          (processBlockExecution config checks engine · block.body bellatrix) (headed, [])
        else pure (headed, [])) = (Except.ok (executed, events) : Except TransitionError _) := by
    split at executionOk <;> rename_i h
    · simp only [h, ↓reduceDIte]
      obtain ⟨_, limits, _⟩ := execution_bounds early engine block.body h executionOk
      exact recordBalance_result executionOk ⟨_, limits⟩ _ []
    · simp only [pure, Except.pure, Except.ok.injEq] at executionOk
      exact ⟨[], by simp only [h, ↓reduceDIte, ← executionOk]; rfl⟩
  obtain ⟨executionEvents, executionReplay⟩ := executedReplay
  simp only [processOperations, gloas, ↓reduceDIte, bind_ok_iff,
    ← Array.foldlM_toList] at operationsOk
  obtain ⟨expected, expectedOk, _, countOk, proposed, proposedOk, attestedSlashes,
    attestedSlashesOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, requestsOk⟩ := operationsOk
  obtain ⟨proposedEvents, proposedReplay⟩ := replay_fold_result
    (processProposerSlashing config checks)
    (fun pre sl => recordBalance .slashings
      (slashingLimits [sl.signedHeader1.message.proposerIndex])
      (processProposerSlashing config checks · sl) pre)
    (fun _ _ _ step events => recordBalance_result step (proposerLimits_result step) _ events)
    _ voted proposed proposedOk executionEvents
  obtain ⟨slashedEvents, slashedReplay⟩ := replay_fold_result
    (processAttesterSlashing config checks)
    (fun pre sl => recordBalance .slashings (slashingLimits (slashingIndices sl))
      (processAttesterSlashing config checks · sl) pre)
    (fun _ _ _ step events => recordBalance_result step (attesterLimits_result step) _ events)
    _ proposed attestedSlashes attestedSlashesOk proposedEvents
  obtain ⟨attestedEvents, attestedReplay⟩ := replay_fold_result
    (processAttestation config checks · s.latestBlockHeader.slot ·)
    (fun pre att => recordBalance .rewards (fun site => do
      return (← attestationCredit site att s.latestBlockHeader.slot, 0))
      (processAttestation config checks · s.latestBlockHeader.slot att) pre)
    (fun site att result step events => recordBalance_result step (by
      obtain ⟨credit, computed⟩ := attestationCredit_result step
      exact ⟨(credit, 0), by rw [computed]; rfl⟩) _ events)
    _ attestedSlashes attested attestedOk slashedEvents
  obtain ⟨depositEvents, depositReplay⟩ := replay_fold_result
    (processDeposit config checks before)
    (fun pre dep => recordBalance .deposits
      (fun _ => pure (if fork < .pectra then dep.data.amount.toNat else 0, 0))
      (processDeposit config checks before · dep) pre)
    (fun _ _ _ step events => recordBalance_result step ⟨_, rfl⟩ _ events)
    _ attested deposited depositedOk attestedEvents
  have requestReplay : ∃ events, (if electra : Fork.pectra ≤ fork then do
      let requests := block.body.executionRequests ⟨electra, early⟩
      let pre ← carryBalance (fun site => requests.deposits.data.foldlM
        (processDepositRequest · electra ·) site) (changed, depositEvents)
      let pre ← carryBalance (fun site => requests.withdrawals.data.foldlM
        (processWithdrawalRequest config · electra ·) site) pre
      requests.consolidations.data.toList.foldlM (fun pre request =>
        recordBalance .excess (fun site => pure (0,
          match findValidatorByPubkey site request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, site⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
          (processConsolidationRequest config · electra request) pre) pre
      else pure (changed, depositEvents)) =
        (Except.ok (operated, events) : Except TransitionError _) := by
    split at requestsOk <;> rename_i h
    · simp only [processExecutionRequests, bind_ok_iff] at requestsOk
      obtain ⟨deposits, depositsOk, withdrawals, withdrawalsOk, consolidationsOk⟩ := requestsOk
      obtain ⟨events, replay⟩ := replay_fold_result
        (processConsolidationRequest config · h ·)
        (fun pre request => recordBalance .excess (fun site => pure (0,
          match findValidatorByPubkey site request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, site⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
          (processConsolidationRequest config · h request) pre)
        (fun _ _ _ step events => recordBalance_result step ⟨_, rfl⟩ _ events)
        _ withdrawals operated (by simpa only [← Array.foldlM_toList] using consolidationsOk)
        depositEvents
      refine ⟨events, ?_⟩
      have depositsReplay := carryBalance_result (action := fun site =>
        (block.body.executionRequests ⟨h, early⟩).deposits.data.foldlM
          (processDepositRequest · h ·) site) depositsOk depositEvents
      have withdrawalsReplay := carryBalance_result (action := fun site =>
        (block.body.executionRequests ⟨h, early⟩).withdrawals.data.foldlM
          (processWithdrawalRequest config · h ·) site) withdrawalsOk depositEvents
      simp only [h, ↓reduceDIte, depositsReplay, withdrawalsReplay, replay, bind, Except.bind]
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact ⟨depositEvents, by simp only [h, ↓reduceDIte, requestsOk]; rfl⟩
  obtain ⟨requestEvents, requestsReplay⟩ := requestReplay
  have syncedReplay : ∃ events, (if altair : Fork.altair ≤ fork then
      recordBalance .sync (fun site => do
        let reward ← syncParticipantReward site
        let proposer ← liftAccessor (liftArith do
          Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
            (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
        return (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
          preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat))
        (processSyncAggregate config checks · altair (block.body.syncAggregate altair))
        (operated, requestEvents)
      else pure (operated, requestEvents)) =
        (Except.ok (t, events) : Except TransitionError _) := by
    split at syncOk <;> rename_i h
    · simp only [h, ↓reduceDIte]
      apply recordBalance_result syncOk
      obtain ⟨reward, proposer, rewardOk, proposerOk⟩ := syncLimits_result syncOk
      simp only [bind, Except.bind] at proposerOk
      simp only [rewardOk, proposerOk, bind, Except.bind, pure, Except.pure]
      exact ⟨_, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at syncOk
      exact ⟨requestEvents, by simp only [h, ↓reduceDIte, syncOk]; rfl⟩
  obtain ⟨events, synced⟩ := syncedReplay
  have headerReplay := carryBalance_result (action := (processBlockHeader · block)) headerOk []
  have randaoReplay := carryBalance_result
    (action := (processRandao config checks · block.body)) randaoOk executionEvents
  have eth1Replay := carryBalance_result (action := (processEth1Data before · block.body))
    eth1Ok executionEvents
  have exitReplay := carryBalance_result
    (action := fun site => block.body.voluntaryExits.data.foldlM
      (processVoluntaryExit config checks) site)
    (by simpa only [← Array.foldlM_toList] using exitedOk) depositEvents
  have changeReplay := carryBalance_result
    (action := (processBlsToExecutionChanges config checks · block.body)) changedOk depositEvents
  refine ⟨events, ?_⟩
  by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
    by_cases electra : Fork.pectra ≤ fork
  all_goals
    simp only [altair, bellatrix, electra, ↓reduceDIte, bind, Except.bind,
      pure, Except.pure] at executionReplay requestsReplay synced attestedReplay depositReplay
    simp only [blockBalanceReplay, altair, bellatrix, electra, ↓reduceDIte,
      headerReplay, executionReplay, randaoReplay, eth1Replay,
      expectedOk, countOk, proposedReplay, slashedReplay, attestedReplay, depositReplay,
      exitReplay, changeReplay, requestsReplay, synced,
      bind, Except.bind, pure, Except.pure]
    repeat' (split at requestsReplay <;> simp_all)

def upgradeBalanceReplay (s : ForkedBeaconState preset) :
    Except TransitionError (List (BalanceEvent preset)) := do
  if upgradeDue config s then
    let next ← upgradeNext config checks s
    let rest ← upgradeBalanceReplay next.val
    if s.fork = .dencun then
      if electra : .pectra ≤ next.val.fork then
        let queued := ((next.val.state.pendingDeposits electra).data.toList.map
          fun d => d.amount.toNat).sum
        return ⟨.crossing, s, next.val, 0, queued⟩ :: rest
      else return rest
    else return rest
  else return []
termination_by Fork.hegota.ctorIdx + 1 - s.fork.ctorIdx
decreasing_by
  have later : s.fork.ctorIdx < next.val.fork.ctorIdx := next.property
  have last : next.val.fork.ctorIdx ≤ Fork.hegota.ctorIdx := by cases next.val.fork <;> decide
  omega

def _root_.EthLib.Consensus.Step.balanceEvents {x y : ForkedBeaconState preset}
    (step : Step config checks x y) :
    Except TransitionError (List (BalanceEvent preset)) :=
  match step with
  | .block engine signed _ _ => do
    if early : x.fork < .glamsterdam then
      return (← blockBalanceReplay (config := config) (checks := checks)
        early engine x.state signed.message).2
    else throw (.accessor (.forkNotYetSpecified x.fork))
  | .slot _ => do
    let cached ← processSlot x.state
    let next ← liftAccessor (liftArith (Uint64.addChecked x.state.slot 1))
    let events ← if next % preset.SLOTS_PER_EPOCH = 0 then do
        pure (← epochBalanceReplay (config := config) (checks := checks) cached).2
      else pure []
    let advanced ← advanceSlot config checks x.state
    return events ++
      (← upgradeBalanceReplay (config := config) (checks := checks) ⟨x.fork, advanced⟩)

/-- Before Gloas, the events of a block step are those of the replay of its block.

That replay ends at the state after the block. -/
theorem _root_.EthLib.Consensus.Step.balanceEvents_block {fork : Fork}
    {s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (early : fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events) :
    blockBalanceReplay (config := config) (checks := checks) early engine s signed.message =
      .ok (t, events) := by
  obtain ⟨blockEvents, blockReplay⟩ :=
    blockBalanceReplay_result _ _ early engine signed.message (applySignedBlock_ok ok).2.1
  simp only [Step.balanceEvents, early, ↓reduceDIte, blockReplay,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at replayed
  subst replayed
  exact blockReplay

/-- Start at this run's first state and include tests with target epoch at most `high`. -/
def _root_.EthLib.Consensus.Run.balanceEvents {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y →
      Except TransitionError (List (BalanceEvent preset))
  | _, .nil => pure []
  | _, .snoc (middle := m) pre step => do
    let prior ← pre.balanceEvents high
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      return prior ++ (← step.balanceEvents)
    else return prior

/-- Filtering by the same horizon preserves the selected prefix's events. -/
theorem _root_.EthLib.Consensus.Run.balanceEvents_prefix {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (tail : Run config checks m y) (high : Nat)
    (events : List (BalanceEvent preset))
    (ok : (pre.append tail).balanceEvents high = .ok events) :
    ∃ before, pre.balanceEvents high = .ok before ∧ before <+: events := by
  induction tail generalizing events with
  | nil => exact ⟨events, ok, List.prefix_refl _⟩
  | snoc tail step ih =>
    simp only [Run.append, Run.balanceEvents, bind_ok_iff] at ok
    obtain ⟨prior, priorOk, remaining⟩ := ok
    obtain ⟨before, beforeOk, initial⟩ := ih prior priorOk
    refine ⟨before, beforeOk, ?_⟩
    split at remaining
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at remaining
      obtain ⟨added, _, rfl⟩ := remaining
      exact initial.trans (List.prefix_append _ _)
    · cases remaining
      exact initial

/-- A property of a replay that each recorded reward and each recorded penalty keep.

It then holds through the whole replay of the rewards, at every fork. -/
theorem replayRewards_induction {fork : Fork} (P : BalanceReplay preset fork → Prop)
    (rewarded : ∀ {pre post : BalanceReplay preset fork} {index : ValidatorIndex}
      {reward : Gwei}, P pre →
      recordBalance .rewards (fun _ => pure (reward.toNat, 0))
        (fun s => liftAccessor (increaseBalance s index reward)) pre = .ok post → P post)
    (penalized : ∀ {source : BalanceSource} {pre post : BalanceReplay preset fork}
      {index : ValidatorIndex} {penalty : Gwei}, (source = .penalties ∨ source = .inactivity) →
      P pre → recordBalance source (fun _ => pure (0, penalty.toNat))
        (fun s => liftAccessor (decreaseBalance s index penalty)) pre = .ok post → P post)
    {pre post : BalanceReplay preset fork} (initial : P pre)
    (ok : replayRewards (config := config) pre = .ok post) : P post := by
  -- One pass of deltas records a reward and then a penalty for each validator.
  have deltas {source : BalanceSource} (penalty : source = .penalties ∨ source = .inactivity)
      (amounts : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
      (initial : P pre) (ok : replayDeltas source amounts pre = .ok post) : P post := by
    refine foldlM_ok_invariant P (fun _ _ _ prior ok => ?_) initial ok
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, _, rewardOk, penaltyOk⟩ := ok
    exact penalized penalty (rewarded prior rewardOk) penaltyOk
  have passes {amounts : List (Array Gwei × Array Gwei)} {f : _ → Array Gwei × Array Gwei}
      {pre post : BalanceReplay preset fork} (initial : P pre)
      (ok : amounts.foldlM (fun pre p => replayDeltas .penalties (f p) pre) pre = .ok post) :
      P post :=
    foldlM_ok_invariant P (fun _ _ _ prior ok => deltas (.inl rfl) _ prior ok) initial ok
  unfold replayRewards at ok
  split at ok
  · cases ok; exact initial
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, folded, last⟩ := bind_ok_iff.mp ok
      exact deltas (.inr rfl) _ (passes (f := id) initial folded) last
    · simp only [bind_ok_iff] at ok
      obtain ⟨rewards, _, rewarded, rewardOk, middle, folded, last⟩ := ok
      exact deltas (.inr rfl) _ (passes (deltas (.inl rfl) _ initial rewardOk) folded) last

def EventsBounded (events : List (BalanceEvent preset)) : Prop :=
  ∀ event ∈ events, event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit

private theorem eventsBounded_append {left right : List (BalanceEvent preset)}
    (first : EventsBounded left) (last : EventsBounded right) :
    EventsBounded (left ++ right) := by
  intro event member
  rcases List.mem_append.mp member with member | member
  · exact first event member
  · exact last event member

private theorem recordBalance_bounded {fork : Fork} (source : BalanceSource)
    (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (bound : ∀ s t credit debit, limits s = .ok (credit, debit) → action s = .ok t →
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit)
    {pre post : BalanceReplay preset fork} (initial : EventsBounded pre.2)
    (ok : recordBalance source limits action pre = .ok post) : EventsBounded post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, limitOk, after, actionOk, rfl⟩ := ok
  apply eventsBounded_append initial
  intro event member
  simp only [List.mem_singleton] at member
  subst event
  exact bound pre.1 after credit debit limitOk actionOk

/-- The rewards replay records only bounded events. -/
theorem replayRewards_bounded {fork : Fork} {pre post : BalanceReplay preset fork}
    (initial : EventsBounded pre.2)
    (ok : replayRewards (config := config) pre = .ok post) : EventsBounded post.2 :=
  replayRewards_induction (fun pre => EventsBounded pre.2)
    (fun prior ok => recordBalance_bounded .rewards _ _ (fun _ _ _ _ limits action => by
      cases limits
      have bounds := credits_increase (liftAccessor_ok.mp action)
      exact ⟨bounds.1.le, bounds.2.le⟩) prior ok)
    (fun _ prior ok => recordBalance_bounded _ _ _ (fun _ _ _ _ limits action => by
      cases limits
      have bounds := debits_decrease (liftAccessor_ok.mp action)
      exact ⟨bounds.1.le, bounds.2⟩) prior ok) initial ok

private theorem deposit_bounds {fork : Fork} {s t : BeaconState preset fork}
    (matched : BalancesMatch s) (before : fork < .hegota) (deposit : Deposit)
    (ok : processDeposit config checks before s deposit = .ok t) :
    balanceCredits s t ≤ (if fork < .pectra then deposit.data.amount.toNat else 0) ∧
      balanceDebits s t ≤ 0 := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  let site := { s with eth1DepositIndex := fun _ => next }
  have matchedSite : BalancesMatch site := matched
  change applyDeposit config checks site _ _ _ _ = .ok t at applied
  rcases applyDeposit_cases applied with
    unchanged | ⟨electra, u, _, added, rfl⟩ | ⟨early, applied⟩
  · subst unchanged
    simp [balanceCredits, balanceDebits, actualBalanceAt, site]
  · have notEarly : ¬ fork < .pectra := Nat.not_lt.mpr electra
    simp only [notEarly, ↓reduceIte]
    rcases added with rfl | add
    · simp [balanceCredits, balanceDebits, actualBalanceAt, site]
    have balances := (addValidatorToRegistry_push add matchedSite).2
    have point (j : Nat) : actualBalanceAt ⟨fork, u⟩ j = actualBalanceAt ⟨fork, s⟩ j := by
      simp only [actualBalanceAt, balances, site, Array.getElem?_push]
      split <;> simp_all
    have zero : balanceCredits s u = 0 ∧ balanceDebits s u = 0 := by
      simp [balanceCredits, balanceDebits, point]
    exact ⟨zero.1.le, zero.2.le⟩
  · have early : fork < .pectra := early
    have bounds := deposit_credit_bound site t matchedSite _ applied
    simpa only [early, ↓reduceIte, balanceCredits, balanceDebits, actualBalanceAt, site]
      using And.intro bounds.2 bounds.1.le

private theorem balance_triangle {fork : Fork} (s u t : BeaconState preset fork)
    (first : s.balances.data.size = u.balances.data.size)
    (last : t.balances.data.size = u.balances.data.size) :
    balanceCredits s t ≤ balanceCredits s u + balanceCredits u t ∧
      balanceDebits s t ≤ balanceDebits s u + balanceDebits u t := by
  constructor
  · unfold balanceCredits
    rw [last, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    omega
  · unfold balanceDebits
    rw [first, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    omega

private theorem sync_bounds {fork : Fork} {s t : BeaconState preset fork}
    (altair : .altair ≤ fork) (aggregate : SyncAggregate preset)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∃ reward proposer,
      syncParticipantReward s = .ok reward ∧
      liftAccessor (liftArith (do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))) = Except.ok proposer ∧
      balanceCredits s t ≤
        preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat) ∧
      balanceDebits s t ≤ preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat := by
  simp only [processSyncAggregate, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposer, proposerOk,
    members, membersOk, folded⟩ := ok
  refine ⟨reward, proposer, rewardOk, proposerOk, ?_⟩
  have fold (xs : List (ValidatorIndex × Bool)) (s t : BeaconState preset fork)
      (proposerIndex : Except AccessorError ValidatorIndex)
      (ok : xs.foldlM (applySyncReward reward proposer proposerIndex) s = .ok t) :
      t.balances.data.size = s.balances.data.size ∧
      balanceCredits s t ≤ xs.length * (reward.toNat + proposer.toNat) ∧
      balanceDebits s t ≤ xs.length * reward.toNat := by
    induction xs generalizing s with
    | nil => cases ok; simp [balanceCredits, balanceDebits]
    | cons x xs ih =>
      obtain ⟨u, one, rest⟩ := bind_ok_iff.mp ok
      have bounds := sync_reward_bounds s u reward proposer proposerIndex x one
      have sizes : u.balances.data.size = s.balances.data.size := by
        unfold applySyncReward at one
        split at one
        · simp only [bind_ok_iff, liftAccessor_ok] at one
          obtain ⟨v, first, _, _, last⟩ := one
          exact (sameSizes_increaseBalance last).2.trans (sameSizes_increaseBalance first).2
        · exact (sameSizes_decreaseBalance (liftAccessor_ok.mp one)).2
      have tail := ih u rest
      have triangle := balance_triangle s u t sizes.symm tail.1
      refine ⟨tail.1.trans sizes, ?_, ?_⟩ <;>
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;>
        split_ifs at bounds <;> omega
  have bounds := fold _ s t _ (by simpa only [← Array.foldlM_toList] using folded)
  have length : (members.zip aggregate.syncCommitteeBits.bits.toArray).toList.length ≤
      preset.SYNC_COMMITTEE_SIZE.toNat := by
    simp only [Array.length_toList, Array.size_zip]
    exact (Nat.min_le_right _ _).trans (by simp)
  exact ⟨bounds.2.1.trans (Nat.mul_le_mul_right _ length),
    bounds.2.2.trans (Nat.mul_le_mul_right _ length)⟩

private theorem proposer_slashing_bounds {fork : Fork} {s t : BeaconState preset fork}
    (sl : ProposerSlashing) (ok : processProposerSlashing config checks s sl = .ok t) :
    ∃ credit debit,
      slashingLimits [sl.signedHeader1.message.proposerIndex] s = .ok (credit, debit) ∧
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, v, found, _, _, _, _, _, _, slashed⟩ := ok
  have bounds := initial_slashing_bounds s t _ none v found slashed
  refine ⟨_, _, ?_, bounds.2, bounds.1⟩
  simp [slashingLimits, found, List.mapM_cons, List.mapM_nil, liftAccessor,
    Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem slash_effective {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    ∀ j, (getValidator t j).map Validator.effectiveBalance =
      (getValidator s j).map Validator.effectiveBalance := by
  have set {s t : BeaconState preset fork} {i : ValidatorIndex} {v w : Validator}
      (read : getValidator s i = .ok v) (ok : s.setValidator i w = .ok t)
      (same : w.effectiveBalance = v.effectiveBalance) (j : ValidatorIndex) :
      (getValidator t j).map Validator.effectiveBalance =
        (getValidator s j).map Validator.effectiveBalance := by
    by_cases h : j = i
    · subst j
      rw [getValidator_setValidator_self ok, read]
      exact congrArg Except.ok same
    · rw [getValidator_setValidator_of_ne ok h]
  have exit {s t : BeaconState preset fork}
      (ok : initiateValidatorExit config s index = .ok t) (j : ValidatorIndex) :
      (getValidator t j).map Validator.effectiveBalance =
        (getValidator s j).map Validator.effectiveBalance := by
    obtain ⟨v, read, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, changed⟩⟩ :=
      initiateValidatorExit_ok ok
    · rw [unchanged.2]
    · have same := (exitQueue_validators queue).1
      rw [set (v := v) (by rw [getValidator_of_validators_eq same]; exact read) changed rfl,
        getValidator_of_validators_eq same]
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, changed,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  intro j
  have middle := set found changed rfl
  have endpoint : ∀ j, (getValidator last j).map Validator.effectiveBalance =
      (getValidator s j).map Validator.effectiveBalance := by
    intro j
    rw [getValidator_of_validators_eq (increaseBalance_validators paid),
      getValidator_of_validators_eq (increaseBalance_validators raised),
      getValidator_of_validators_eq (decreaseBalance_validators lowered)]
    change (getValidator marked j).map Validator.effectiveBalance = _
    rw [middle j, exit exited j]
  split <;> exact endpoint j

private theorem attester_slashing_bounds {fork : Fork} {s t : BeaconState preset fork}
    (sl : AttesterSlashing preset fork)
    (ok : processAttesterSlashing config checks s sl = .ok t) :
    ∃ credit debit, slashingLimits (slashingIndices sl) s = .ok (credit, debit) ∧
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit := by
  have fold (indices : List ValidatorIndex) (s t : BeaconState preset fork) (flag last : Bool)
      (ok : indices.foldlM (slashIfSlashable config) (s, flag) = .ok (t, last)) :
      ∃ credit debit, slashingLimits indices s = .ok (credit, debit) ∧
        balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit ∧
        t.balances.data.size = s.balances.data.size := by
    induction indices generalizing s flag with
    | nil =>
      cases ok
      exact ⟨0, 0, by simp [slashingLimits, liftAccessor, Except.mapError, pure,
        Except.pure, bind, Except.bind], by simp [balanceCredits],
        by simp [balanceDebits], rfl⟩
    | cons i indices ih =>
      obtain ⟨⟨u, flag'⟩, one, rest⟩ := bind_ok_iff.mp ok
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at one
      obtain ⟨v, read, one⟩ := one
      have oneFacts :
          balanceCredits s u ≤ v.effectiveBalance.toNat /
            (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
          balanceDebits s u ≤ v.effectiveBalance.toNat /
            (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
          u.balances.data.size = s.balances.data.size ∧
          ∀ j, (getValidator u j).map Validator.effectiveBalance =
            (getValidator s j).map Validator.effectiveBalance := by
        split at one
        · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at one
          obtain ⟨u', slashed, rfl, rfl⟩ := one
          have bounds := initial_slashing_bounds s u' i none v read slashed
          exact ⟨bounds.2, bounds.1, (sameSizes_slashValidator slashed).2,
            slash_effective slashed⟩
        · cases one
          exact ⟨by simp [balanceCredits], by simp [balanceDebits], rfl, fun _ => rfl⟩
      obtain ⟨credit, debit, limits, credits, debits, sizes⟩ := ih u flag' rest
      have triangle := balance_triangle s u t oneFacts.2.2.1.symm sizes
      refine ⟨v.effectiveBalance.toNat /
          (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat + credit,
        v.effectiveBalance.toNat /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat + debit,
        ?_, by omega, by omega, sizes.trans oneFacts.2.2.1⟩
      simp only [slashingLimits, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at limits ⊢
      obtain ⟨validators, found, limits⟩ := limits
      have original : ∃ validators', indices.mapM (getValidator s) = .ok validators' ∧
          (validators'.map fun v => v.effectiveBalance) =
            (validators.map fun v => v.effectiveBalance) := by
        clear limits credits debits triangle sizes rest ih ok
        induction indices generalizing validators with
        | nil => cases found; exact ⟨[], rfl, rfl⟩
        | cons j js ih =>
          simp only [List.mapM_cons, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at found
          obtain ⟨v', read', vs, rest, rfl⟩ := found
          have eq := oneFacts.2.2.2 j
          rw [read'] at eq
          cases originalRead : getValidator s j with
          | error e => simp [originalRead, Except.map] at eq
          | ok w =>
            simp only [originalRead, Except.map, Except.ok.injEq] at eq
            obtain ⟨ws, wsOk, same⟩ := ih vs rest
            refine ⟨w :: ws, ?_, ?_⟩
            · simp [List.mapM_cons, originalRead, wsOk, bind, Except.bind, pure, Except.pure]
            · simp only [List.map_cons, same, eq]
      obtain ⟨validators', found', same⟩ := original
      refine ⟨v :: validators', ?_, ?_⟩
      · simp [List.mapM_cons, read, found', bind, Except.bind, pure, Except.pure]
      · have creditsEq := congrArg (fun vs => (vs.map fun b => b.toNat /
            (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat).sum)
          same
        have debitsEq := congrArg (fun vs => (vs.map fun b => b.toNat /
            (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat).sum)
          same
        simp only [List.map_map, Function.comp_def] at creditsEq debitsEq
        cases limits
        simp only [List.map_cons, List.sum_cons, creditsEq, debitsEq]
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨u, flag⟩, folded, _, _, rfl⟩ := ok
  obtain ⟨credit, debit, limits, credits, debits, _⟩ := fold _ s u false flag folded
  exact ⟨credit, debit, limits, credits, debits⟩

private theorem consolidation_request_bounds {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (request : ConsolidationRequest)
    (ok : processConsolidationRequest config s electra request = .ok t) :
    balanceCredits s t ≤ 0 ∧ balanceDebits s t ≤
      (match findValidatorByPubkey s request.sourcePubkey with
      | none => 0
      | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  have unchanged (same : t.balances = s.balances) : balanceCredits s t ≤ 0 ∧
      balanceDebits s t ≤ (match findValidatorByPubkey s request.sourcePubkey with
        | none => 0
        | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat) := by
    simp [balanceCredits, balanceDebits, actualBalanceAt, same]
  have switched (i : Fin s.validators.data.size) (index : ValidatorIndex)
      (found : findValidatorByPubkey s request.sourcePubkey = some i)
      (indexOk : Uint64.ofNatChecked i.val = .ok index)
      (ok : switchToCompoundingValidator s electra index = .ok t) :
      balanceCredits s t ≤ 0 ∧ balanceDebits s t ≤
        (match findValidatorByPubkey s request.sourcePubkey with
        | none => 0
        | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat) := by
    simp only [switchToCompoundingValidator, bind_ok_iff] at ok
    obtain ⟨v, _, u, set, queued⟩ := ok
    have queuedCopy := queued
    simp only [queueExcessActiveBalance, bind_ok_iff] at queuedCopy
    obtain ⟨balance, read, _⟩ := queuedCopy
    have bounds := excess_queue_debit u t electra index balance read queued
    obtain ⟨_, rfl⟩ := setValidator_ok set
    have actual : actualBalanceAt ⟨fork, s⟩ i.val = balance.toNat := by
      have read := getBalance_eq_ok_iff.mp read
      simp only [BeaconState.putValidator] at read
      rw [(Uint64.ofNatChecked_ok_iff.mp indexOk).2] at read
      simp [actualBalanceAt, read]
    rw [found]
    dsimp only
    rw [actual]
    simpa only [balanceCredits, balanceDebits, actualBalanceAt,
      BeaconState.putValidator] using And.intro bounds.1.le bounds.2
  have queued (source : Validator) (sourceIndex targetIndex : ValidatorIndex)
      (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
      t.balances = s.balances := by
    simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨⟨u, epoch⟩, churned, _, _, v, set, _, _, rfl⟩ := ok
    obtain ⟨_, _, balances⟩ := computeConsolidationEpochAndUpdateChurn_earliest churned
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact balances
  unfold processConsolidationRequest at ok
  split at ok
  · split at ok
    · rename_i position found
      obtain ⟨index, indexOk, ok⟩ := bind_ok_iff.mp ok
      split at ok
      · exact switched position index found
          (by cases h : Uint64.ofNatChecked position.val <;>
                simp [liftAccessor, liftArith, Except.mapError, h] at indexOk ⊢; exact indexOk)
          (liftAccessor_ok.mp ok)
      · cases ok
        exact unchanged rfl
    · cases ok
      exact unchanged rfl
  · simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact unchanged rfl)
      | exact unchanged (queued _ _ _ ok)

private def ReplayBounded {fork : Fork} (pre : BalanceReplay preset fork) : Prop :=
  BalancesMatch pre.1 ∧ EventsBounded pre.2

private theorem carryBalance_bounded {fork : Fork}
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (preserves : ∀ s t, action s = .ok t → BalancesMatch s → BalancesMatch t)
    {pre post : BalanceReplay preset fork} (initial : ReplayBounded pre)
    (ok : carryBalance action pre = .ok post) : ReplayBounded post := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, afterOk, rfl⟩ := ok
  exact ⟨preserves pre.1 after afterOk initial.1, initial.2⟩

private theorem recordBalance_matched {fork : Fork} (source : BalanceSource)
    (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (preserves : ∀ s t, action s = .ok t → BalancesMatch s → BalancesMatch t)
    (bound : ∀ s t credit debit, BalancesMatch s →
      limits s = .ok (credit, debit) → action s = .ok t →
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit)
    {pre post : BalanceReplay preset fork} (initial : ReplayBounded pre)
    (ok : recordBalance source limits action pre = .ok post) : ReplayBounded post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, limitOk, after, actionOk, rfl⟩ := ok
  refine ⟨preserves pre.1 after actionOk initial.1, eventsBounded_append initial.2 ?_⟩
  intro event member
  simp only [List.mem_singleton] at member
  subst event
  exact bound pre.1 after credit debit initial.1 limitOk actionOk

/-- Every event of a block replay is bounded by its recorded limits. -/
theorem blockBalanceReplay_bounded {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork) {post : BalanceReplay preset fork}
    (matched : BalancesMatch s)
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : EventsBounded post.2 := by
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have record {pre post : BalanceReplay preset fork} {source : BalanceSource}
      {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
      (preserves : ∀ s t, action s = .ok t → BalancesMatch s → BalancesMatch t)
      (bound : ∀ s t credit debit, BalancesMatch s →
        limits s = .ok (credit, debit) → action s = .ok t →
        balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit)
      (initial : ReplayBounded pre) (ok : recordBalance source limits action pre = .ok post) :
      ReplayBounded post := recordBalance_matched _ _ _ preserves bound initial ok
  have proposer {pre post : BalanceReplay preset fork} (sl : ProposerSlashing)
      (initial : ReplayBounded pre)
      (ok : recordBalance .slashings (slashingLimits [sl.signedHeader1.message.proposerIndex])
        (processProposerSlashing config checks · sl) pre = .ok post) : ReplayBounded post := by
    apply record (fun _ _ ok => (frame_processProposerSlashing ok).balancesMatch) _ initial ok
    intro s t credit debit _ limits action
    obtain ⟨credit', debit', limits', bounds⟩ := proposer_slashing_bounds sl action
    cases Except.ok.inj (limits.symm.trans limits')
    exact bounds
  have attester {pre post : BalanceReplay preset fork} (sl : AttesterSlashing preset fork)
      (initial : ReplayBounded pre)
      (ok : recordBalance .slashings (slashingLimits (slashingIndices sl))
        (processAttesterSlashing config checks · sl) pre = .ok post) : ReplayBounded post := by
    apply record (fun _ _ ok => (frame_processAttesterSlashing ok).balancesMatch) _ initial ok
    intro s t credit debit _ limits action
    obtain ⟨credit', debit', limits', bounds⟩ := attester_slashing_bounds sl action
    cases Except.ok.inj (limits.symm.trans limits')
    exact bounds
  have attestation {pre post : BalanceReplay preset fork} (att : Attestation preset fork)
      (initial : ReplayBounded pre)
      (ok : recordBalance .rewards (fun site => do
          return (← attestationCredit site att s.latestBlockHeader.slot, 0))
        (processAttestation config checks · s.latestBlockHeader.slot att) pre = .ok post) :
      ReplayBounded post := by
    apply record (fun _ _ ok => (frame_processAttestation ok).balancesMatch) _ initial ok
    intro site t credit debit _ limits action
    obtain ⟨credit', limits', debits, credits⟩ :=
      attestation_proposer_bound site t att s.latestBlockHeader.slot early action
    simp only [limits', bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at limits
    rcases limits with ⟨rfl, rfl⟩
    exact ⟨credits, debits.le⟩
  have deposit {pre post : BalanceReplay preset fork} (dep : Deposit)
      (initial : ReplayBounded pre)
      (ok : recordBalance .deposits
        (fun _ => pure (if fork < .pectra then dep.data.amount.toNat else 0, 0))
        (processDeposit config checks before · dep) pre = .ok post) : ReplayBounded post := by
    apply record (fun _ _ ok => balancesMatch_processDeposit ok) _ initial ok
    intro site t credit debit matched limits action
    cases limits
    exact deposit_bounds matched before dep action
  have excess {pre post : BalanceReplay preset fork} (electra : .pectra ≤ fork)
      (request : ConsolidationRequest) (initial : ReplayBounded pre)
      (ok : recordBalance .excess (fun site => pure (0,
          match findValidatorByPubkey site request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, site⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
        (processConsolidationRequest config · electra request) pre = .ok post) :
      ReplayBounded post := by
    apply record (fun _ _ ok =>
      balancesMatch_of_sameSizes (sameSizes_processConsolidationRequest ok)) _ initial ok
    intro site t credit debit _ limits action
    cases limits
    exact consolidation_request_bounds electra request action
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headerOk, ok⟩ := bind_ok_iff.mp ok
  have headedBound := carryBalance_bounded _
    (fun _ _ ok => (frame_processBlockHeader ok).balancesMatch)
    ⟨matched, by simp [EventsBounded]⟩ headerOk
  by_cases bellatrix : .bellatrix ≤ fork
  case' pos =>
    simp only [bellatrix, ↓reduceDIte] at ok
    obtain ⟨executed, executionOk, rest⟩ := bind_ok_iff.mp ok
    have executedBound : ReplayBounded executed := by
      apply record (fun _ _ ok => (frame_processBlockExecution ok).balancesMatch) _
        headedBound executionOk
      intro site t credit debit _ limits action
      obtain ⟨debit', limits', credits, debits⟩ := execution_bounds early engine block.body
        bellatrix action
      cases Except.ok.inj (limits.symm.trans limits')
      exact ⟨credits, debits⟩
  case' neg =>
    simp only [bellatrix, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
      Except.ok.injEq, exists_eq_left'] at ok
    have rest := ok
    have executedBound := headedBound
  all_goals
    try simp only [bind_ok_iff] at rest
    obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
      proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
      exited, exitOk, changed, changedOk, rest⟩ := rest
    have randaoBound := carryBalance_bounded _
      (fun _ _ ok => (frame_processRandao ok).balancesMatch) executedBound randaoOk
    have votedBound := carryBalance_bounded _
      (fun _ _ ok => (frame_processEth1Data ok).balancesMatch) randaoBound votedOk
    have proposedBound := foldlM_ok_invariant ReplayBounded
      (fun _ sl _ h ok => proposer sl h ok) votedBound proposedOk
    have attestedBound := foldlM_ok_invariant ReplayBounded
      (fun _ sl _ h ok => attester sl h ok) proposedBound attestedOk
    have rewardedBound := foldlM_ok_invariant ReplayBounded
      (fun _ att _ h ok => attestation att h ok) attestedBound rewardedOk
    have depositedBound := foldlM_ok_invariant ReplayBounded
      (fun _ dep _ h ok => deposit dep h ok) rewardedBound depositOk
    have exitedBound := carryBalance_bounded _ (fun _ _ ok h =>
      foldlM_ok_invariant BalancesMatch
        (fun _ _ _ h ok => (frame_processVoluntaryExit ok).balancesMatch h) h
        (by simpa only [← Array.foldlM_toList] using ok)) depositedBound exitOk
    have changedBound := carryBalance_bounded _ (fun _ _ ok h => by
      unfold processBlsToExecutionChanges at ok
      split at ok
      · exact foldlM_ok_invariant BalancesMatch
          (fun _ _ _ h ok => (frame_processBlsToExecutionChange ok).balancesMatch h) h
          (by simpa only [← Array.foldlM_toList] using ok)
      · cases ok; exact h) exitedBound changedOk
    by_cases electra : .pectra ≤ fork
    case' pos =>
      simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
      obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
        requested, consolidations, rest⟩ := rest
      have requestedBound : ReplayBounded requested := by
        have depositsBound := carryBalance_bounded _ (fun _ _ ok h =>
          foldlM_ok_invariant BalancesMatch
            (fun _ _ _ h ok => (frame_processDepositRequest ok).balancesMatch h) h
            (by simpa only [← Array.foldlM_toList] using ok)) changedBound depositRequestOk
        have withdrawalsBound := carryBalance_bounded _ (fun _ _ ok h =>
          foldlM_ok_invariant BalancesMatch
            (fun _ _ _ h ok => (frame_processWithdrawalRequest ok).balancesMatch h) h
            (by simpa only [← Array.foldlM_toList] using ok)) depositsBound withdrawalOk
        exact foldlM_ok_invariant ReplayBounded
          (fun _ request _ h ok => excess electra request h ok) withdrawalsBound consolidations
    case' neg =>
      simp only [electra, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
        Except.ok.injEq, exists_eq_left'] at rest
      have requestedBound := changedBound
    all_goals
      split at rest
      · have final : ReplayBounded post := by
          apply record (fun _ _ ok => (frame_processSyncAggregate ok).balancesMatch) _
            requestedBound rest
          intro site t credit debit _ limits action
          obtain ⟨reward, proposer, rewardOk, proposerOk, bounds⟩ := sync_bounds _ _ action
          rw [rewardOk] at limits
          dsimp only [bind, Except.bind] at limits
          simp only [bind, Except.bind] at proposerOk
          rw [proposerOk] at limits
          simp only [pure, Except.pure, Except.ok.injEq] at limits
          cases limits
          exact bounds
        exact final.2
      · cases rest
        exact requestedBound.2

/-- The fork upgrades of a slot have a replay, and its events are bounded. -/
theorem upgradeBalanceReplay_bounded {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) :
    ∃ events, upgradeBalanceReplay (config := config) (checks := checks) s = .ok events ∧
      EventsBounded events := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, restOk⟩ := bind_ok_iff.mp ok
    obtain ⟨rest, replay, bounded⟩ := ih next restOk
    rw [upgradeBalanceReplay]
    simp only [due, ↓reduceIte, nextOk, bind, Except.bind, replay]
    by_cases crossing : s.fork = .dencun
    · obtain ⟨fork, state⟩ := s
      dsimp only at crossing
      subst fork
      simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨after, upgraded, rfl⟩ := nextOk
      simp only [↓reduceIte, show Fork.pectra ≤ .pectra from Nat.le_refl _, ↓reduceDIte,
        pure, Except.pure, Except.ok.injEq, exists_eq_left']
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · have bound := electra_upgrade_debit state after upgraded
        exact ⟨bound.1.le, bound.2⟩
      · exact bounded event member
    · simpa only [crossing, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
        exists_eq_left'] using bounded
  | case2 s due =>
    refine ⟨[], ?_, by simp [EventsBounded]⟩
    rw [upgradeBalanceReplay]
    simp [due, pure, Except.pure]

/-- The credit or the debit of validator `i` between two states. -/
def coverageDelta (debit : Bool) (x y : ForkedBeaconState preset) (i : Nat) : Nat :=
  if debit then actualBalanceAt x i - actualBalanceAt y i
  else actualBalanceAt y i - actualBalanceAt x i

/-- The events cover each credit and each debit between two states, per validator. -/
def Coverage (x y : ForkedBeaconState preset)
    (events : List (BalanceEvent preset)) : Prop :=
  ∀ debit i, coverageDelta debit x y i ≤
    (events.map fun e => coverageDelta debit e.before e.after i).sum

/-- No events cover a state to itself. -/
theorem coverage_refl (x : ForkedBeaconState preset) : Coverage x x [] := by
  intro debit i
  cases debit <;> simp [coverageDelta]

private theorem coverage_trans {x y z : ForkedBeaconState preset}
    {left right : List (BalanceEvent preset)} (first : Coverage x y left)
    (last : Coverage y z right) : Coverage x z (left ++ right) := by
  intro debit i
  have a := first debit i
  have b := last debit i
  simp only [List.map_append, List.sum_append]
  cases debit <;> simp only [coverageDelta, Bool.false_eq_true, ↓reduceIte] at * <;> omega

/-- The events of a replay cover the balance changes from its start. -/
abbrev ReplayCoverage {fork : Fork} (start : BeaconState preset fork)
    (pre : BalanceReplay preset fork) : Prop := Coverage ⟨fork, start⟩ ⟨fork, pre.1⟩ pre.2

private theorem coverage_record {fork : Fork} {start : BeaconState preset fork}
    {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {pre post : BalanceReplay preset fork} (initial : ReplayCoverage start pre)
    (ok : recordBalance source limits action pre = .ok post) : ReplayCoverage start post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, after, _, rfl⟩ := ok
  exact coverage_trans initial (by intro debit i; simp)

/-- The rewards replay extends the coverage. -/
theorem coverage_rewards {fork : Fork} {start : BeaconState preset fork}
    {pre post : BalanceReplay preset fork} (initial : ReplayCoverage start pre)
    (ok : replayRewards (config := config) pre = .ok post) : ReplayCoverage start post :=
  replayRewards_induction (ReplayCoverage start) (fun prior ok => coverage_record prior ok)
    (fun _ prior ok => coverage_record prior ok) initial ok

/-- A voluntary exit keeps the balances. -/
theorem coverage_voluntary {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedVoluntaryExit} (ok : processVoluntaryExit config checks s signed = .ok t) :
    t.balances = s.balances :=
  (initiateValidatorExit_balances_eq_and_pendingConsolidations_eq
    (processVoluntaryExit_initiates ok)).1

/-- A BLS-to-execution change keeps the balances. -/
theorem coverage_bls {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    t.balances = s.balances := by
  simp only [processBlsToExecutionChange, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, set⟩ := ok
  obtain ⟨_, rfl⟩ := setValidator_ok (liftAccessor_ok.mp set)
  rfl

/-- A withdrawal request keeps the balances. -/
theorem coverage_withdrawal_request {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    t.balances = s.balances := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · rfl
  · exact (initiateValidatorExit_balances_eq_and_pendingConsolidations_eq exited).1
  · exact (requestPartialWithdrawal_kept withdrawn).2.1

/-- The coverage of one event, summed over validators, is at most its credits or debits. -/
theorem coverage_event_sum (event : BalanceEvent preset) (n : Nat) (debit : Bool) :
    (∑ i ∈ Finset.range n, coverageDelta debit event.before event.after i) ≤
      if debit then event.debits else event.credits := by
  have bound (a b : ForkedBeaconState preset) :
      (∑ i ∈ Finset.range n, (actualBalanceAt a i - actualBalanceAt b i)) ≤
        ∑ i ∈ Finset.range a.state.balances.data.size,
          (actualBalanceAt a i - actualBalanceAt b i) := by
    by_cases small : n ≤ a.state.balances.data.size
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono small) (by intros; omega)
    · have le : a.state.balances.data.size ≤ n := by omega
      apply le_of_eq
      symm
      apply Finset.sum_subset (Finset.range_mono le)
      intro i _ outside
      have ge : a.state.balances.data.size ≤ i := by simpa using outside
      simp [actualBalanceAt, Array.getElem?_eq_none (by omega)]
  cases debit <;> exact bound _ _

/-- The coverage of a list of events, summed over validators, is at most its totals. -/
theorem coverage_sum_events (events : List (BalanceEvent preset)) (n : Nat) (debit : Bool) :
    (∑ i ∈ Finset.range n,
      (events.map fun e => coverageDelta debit e.before e.after i).sum) ≤
      (events.map fun e => if debit then e.debits else e.credits).sum := by
  induction events with
  | nil => simp
  | cons event rest ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    exact Nat.add_le_add (coverage_event_sum event n debit) ih

def queueCarry (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
      (x.state.exitBalanceToConsume electra).toNat else 0) +
    (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
      (x.state.consolidationBalanceToConsume electra).toNat else 0)
  else 0

/-- Pre-Gloas consolidation churn is the whole balance churn less the activation/exit cap. -/
def consolidationRate (stake : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (max preset.EFFECTIVE_BALANCE_INCREMENT.toNat stake / config.CHURN_LIMIT_QUOTIENT.toNat) -
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- Includes both epoch tests that can justify a target at high. -/
def driftHorizon (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  high + 2 - (getCurrentEpoch x.state).toNat

/-- New registry entries come from block deposits or the bounded pending-deposit pass. -/
def registryWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  x.state.validators.data.size + driftHorizon x high *
    (preset.SLOTS_PER_EPOCH.toNat * preset.MAX_DEPOSITS.toNat +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat)

/-- Electra deposit churn includes active top-ups, but not credits to already withdrawn keys. -/
def depositWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  (if electra : .pectra ≤ x.fork then (x.state.depositBalanceToConsume electra).toNat else 0) +
    driftHorizon x high * config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- Funding that can still support active stake, including queued consolidation sources.

The maximum retains effective stake above actual balance without counting all registry entries. -/
def fundedStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    let pending := if electra : .pectra ≤ x.fork then
      (x.state.pendingConsolidations electra).data.any (fun c => c.sourceIndex.toNat == i)
      else false
    if isActiveValidator v (getCurrentEpoch x.state) ||
        getCurrentEpoch x.state < v.activationEpoch || pending then
      max (effectiveAt x i) (actualBalanceAt x i)
    else 0).sum

/-- Consolidation credits whose source has already withdrawn stay explicit in the bound.

They do not consume deposit churn. -/
def withdrawnConsolidationCredit (event : BalanceEvent preset) : Nat :=
  if electra : .pectra ≤ event.before.fork then
    (event.before.state.validators.data.toList.zipIdx.map fun (v, i) =>
      if v.withdrawableEpoch.toNat ≤ (getCurrentEpoch event.before.state).toNat &&
          (event.before.state.pendingConsolidations electra).data.any
            (fun c => c.sourceIndex.toNat == i) then
        actualBalanceAt event.after i - actualBalanceAt event.before i
      else 0).sum
  else 0

/-- Consolidations move existing funding; deposits have churn and a withdrawn-source exception.

Before Electra a deposit credits its balance at once, with no churn, so it is a credit. -/
def fundingCredit (event : BalanceEvent preset) : Nat :=
  match event.source with
  | .consolidations => 0
  | .deposits =>
    if .pectra ≤ event.before.fork then withdrawnConsolidationCredit event
    else event.creditLimit
  | _ => event.creditLimit

/-- Active stake is funded initially, by deposit churn, or by non-transfer credits.

With a withdrawal delay below two epochs, it is the registry envelope. -/
def activeStakeWindow (x : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  if 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat then
    fundedStake x + depositWindow (config := config) x high + (events.map fundingCredit).sum
  else registryWindow x high * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- A sum over the indexed registry is a sum over the index range. -/
private theorem funding_sum_zipIdx (vs : List Validator) (f : Validator → Nat → Nat) :
    (vs.zipIdx.map fun (v, i) => f v i).sum =
      ∑ i ∈ Finset.range vs.length, (vs[i]?.map (fun v => f v i)).getD 0 := by
  let weight := fun i => (vs[i]?.map (fun v => f v i)).getD 0
  have same : vs.zipIdx.map (fun (v, i) => f v i) =
      (vs.zipIdx.map Prod.snd).map weight := by
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨v, i⟩ member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    simp [weight, found]
  rw [same, List.zipIdx_map_snd]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
    Multiset.map_coe, Multiset.sum_coe, List.range_eq_range']

private theorem funding_active_le (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) (unique : PubkeysDistinct x.state) :
    Models.stake (effectiveWeight x.state) (activeKeys x.state) ≤ fundedStake x := by
  have within : x.state.RegistryWithinLimit := x.state.validators.bound early
  have foundActive {i : ValidatorIndex}
      (member : i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state)) :=
    (mem_getActiveValidatorIndices within).mp member
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := by
    intro i member
    obtain ⟨v, found, _⟩ := foundActive member
    exact (Array.getElem?_eq_some_iff.mp found).1
  rw [activeKeys, keys_weight _ _ unique inside]
  unfold fundedStake
  rw [funding_sum_zipIdx x.state.validators.data.toList (fun v i =>
    if isActiveValidator v (getCurrentEpoch x.state) ||
        decide (getCurrentEpoch x.state < v.activationEpoch) ||
        (if electra : .pectra ≤ x.fork then
          (x.state.pendingConsolidations electra).data.any (fun c => c.sourceIndex.toNat == i)
          else false) then max (effectiveAt x i) (actualBalanceAt x i) else 0)]
  simp only [Array.length_toList, Array.getElem?_toList]
  apply Finset.sum_le_sum_of_injOn (fun i => i.toNat)
  · intro i _ j _ eq
    exact UInt64.toNat_inj.mp eq
  · intro i member
    obtain ⟨j, chosen, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_range.mpr (inside j (List.mem_toFinset.mp chosen))
  · intro i member
    obtain ⟨v, found, active⟩ := foundActive (List.mem_toFinset.mp member)
    simp only [found, Option.map_some, Option.getD_some, active, Bool.true_or, ↓reduceIte]
    exact (by simp [effectiveAt, found] : v.effectiveBalance.toNat ≤
      max (effectiveAt x i.toNat) (actualBalanceAt x i.toNat))
  · intro _ _ _
    exact Nat.zero_le _

private theorem funding_lifecycle_support {v w : Validator} {before after : Epoch}
    (life : ValidatorLifecycle v w) (epochs : before.toNat ≤ after.toNat)
    (active : isActiveValidator w after = true ∨ after < w.activationEpoch) :
    isActiveValidator v before = true ∨ before < v.activationEpoch := by
  have farValue : (UInt64.ofNat (2 ^ 64 - 1)).toNat = 18446744073709551615 := rfl
  by_cases future : before < v.activationEpoch
  · exact Or.inr future
  have activation : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    have maxEpoch : after.toNat ≤ FAR_FUTURE_EPOCH.toNat := by
      have := after.toNat_lt
      simp only [FAR_FUTURE_EPOCH]
      omega
    have old : before = FAR_FUTURE_EPOCH := by
      apply UInt64.toNat_inj.mp
      have bound := before.toNat_lt
      rw [UInt64.lt_iff_toNat_lt, far] at future
      simp only [FAR_FUTURE_EPOCH] at *
      omega
    have later : after = FAR_FUTURE_EPOCH := by
      apply UInt64.toNat_inj.mp
      rw [old] at epochs
      omega
    rcases active with active | active
    · have bound := w.exitEpoch.toNat_lt
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
        UInt64.lt_iff_toNat_lt, later, FAR_FUTURE_EPOCH] at active
      omega
    · have bound := w.activationEpoch.toNat_lt
      rw [UInt64.lt_iff_toNat_lt, later] at active
      simp only [FAR_FUTURE_EPOCH] at active
      omega
  have sameActivation := life.activationEpoch activation
  have oldActivation : v.activationEpoch ≤ before := UInt64.not_lt.mp future
  rcases active with active | futureAfter
  · have bounds : w.activationEpoch ≤ after ∧ after < w.exitEpoch := by
      simpa only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] using active
    have exits := bounds.2
    have exit : before < v.exitEpoch := by
      by_cases assigned : v.exitEpoch = FAR_FUTURE_EPOCH
      · have beyond := UInt64.lt_iff_toNat_lt.mp exits
        have bound := w.exitEpoch.toNat_lt
        rw [UInt64.lt_iff_toNat_lt, assigned]
        simp only [FAR_FUTURE_EPOCH]
        omega
      · rw [life.exitEpoch assigned] at exits
        exact UInt64.lt_iff_toNat_lt.mpr (lt_of_le_of_lt epochs
          (UInt64.lt_iff_toNat_lt.mp exits))
    exact Or.inl (by simp [isActiveValidator, oldActivation, exit])
  · rw [sameActivation, UInt64.lt_iff_toNat_lt] at futureAfter
    have old := UInt64.le_iff_toNat_le.mp oldActivation
    omega

private theorem funding_source_inactive (v : Validator) (current next : Epoch)
    (nextEq : next.toNat = current.toNat + 1)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ordered : v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
      v.withdrawableEpoch.toNat)
    (eligible : v.withdrawableEpoch ≤ next) : isActiveValidator v current = false := by
  have withdrawable := UInt64.le_iff_toNat_le.mp eligible
  have exited : v.exitEpoch ≤ current := UInt64.le_iff_toNat_le.mpr (by omega)
  simp [isActiveValidator, UInt64.not_lt.mpr exited]

/-- The funded stake with an explicit queue of pending consolidations.

During the pass, only the unprocessed suffix supplies pending-source support. -/
def funding_potential {fork : Fork} (s : BeaconState preset fork)
    (queue : List PendingConsolidation) : Nat :=
  ∑ i ∈ Finset.range s.validators.data.size,
    (s.validators.data[i]?.map fun v =>
      if isActiveValidator v (getCurrentEpoch s) ||
          decide (getCurrentEpoch s < v.activationEpoch) ||
          queue.any (fun c => c.sourceIndex.toNat == i) then
        max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i)
      else 0).getD 0

/-- The pending consolidations of a state, and none before Electra. -/
def fundingSources {fork : Fork} (s : BeaconState preset fork) : List PendingConsolidation :=
  if electra : .pectra ≤ fork then (s.pendingConsolidations electra).data.toList else []

/-- With the state's own queue, the potential is the funded stake. -/
theorem funding_potential_eq {fork : Fork} (s : BeaconState preset fork) :
    funding_potential s (fundingSources s) = fundedStake ⟨fork, s⟩ := by
  unfold fundedStake fundingSources
  rw [funding_sum_zipIdx s.validators.data.toList (fun v i =>
    if isActiveValidator v (getCurrentEpoch s) ||
        decide (getCurrentEpoch s < v.activationEpoch) ||
        (if electra : .pectra ≤ fork then
          (s.pendingConsolidations electra).data.any (fun c => c.sourceIndex.toNat == i)
          else false)
      then max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) else 0)]
  by_cases electra : .pectra ≤ fork
  · simp only [funding_potential, electra, ↓reduceDIte, Array.length_toList,
      Array.getElem?_toList, Array.any_toList]
  · simp [funding_potential, electra]

private theorem funding_potential_mono {fork : Fork} (s : BeaconState preset fork)
    {one two : List PendingConsolidation} (included : ∀ c ∈ one, c ∈ two) :
    funding_potential s one ≤ funding_potential s two := by
  apply Finset.sum_le_sum
  intro i _
  cases found : s.validators.data[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    have pending : one.any (fun c => c.sourceIndex.toNat == i) = true →
        two.any (fun c => c.sourceIndex.toNat == i) = true := by
      intro present
      obtain ⟨c, member, eq⟩ := List.any_eq_true.mp present
      exact List.any_eq_true.mpr ⟨c, included c member, eq⟩
    cases active : isActiveValidator v (getCurrentEpoch s) <;>
      cases future : decide (getCurrentEpoch s < v.activationEpoch) <;>
      cases queued : one.any (fun c => c.sourceIndex.toNat == i) <;>
      simp_all

/-- A step that keeps the registry size and lifecycle raises the potential by at most its credits.

The epoch must not decrease, and each validator's funding must rise by at most its credit.

Each pending source in the later queue is pending, active or not yet activated before the step. -/
theorem funding_potential_change {fork : Fork} {s t : BeaconState preset fork}
    (queue beforeQueue : List PendingConsolidation) (credits : Nat → Nat)
    (size : t.validators.data.size = s.validators.data.size)
    (life : RegistryLifecycle s t)
    (epochs : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat)
    (pending : ∀ i, queue.any (fun c => c.sourceIndex.toNat == i) = true →
      beforeQueue.any (fun c => c.sourceIndex.toNat == i) = true ∨
        ∃ v, s.validators.data[i]? = some v ∧
          (isActiveValidator v (getCurrentEpoch s) = true ∨ getCurrentEpoch s < v.activationEpoch))
    (funding : ∀ i, max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) + credits i) :
    funding_potential t queue ≤ funding_potential s beforeQueue +
      ∑ i ∈ Finset.range s.validators.data.size, credits i := by
  unfold funding_potential
  rw [size, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i member
  have inside := Finset.mem_range.mp member
  have found : s.validators.data[i]? = some s.validators.data[i] := by simp [inside]
  obtain ⟨w, read, lifecycle⟩ := life.validators i _ found
  simp only [found, read, Option.map_some, Option.getD_some]
  by_cases chosen : (isActiveValidator w (getCurrentEpoch t) ||
      decide (getCurrentEpoch t < w.activationEpoch) ||
      queue.any (fun c => c.sourceIndex.toNat == i)) = true
  · have prior : (isActiveValidator s.validators.data[i] (getCurrentEpoch s) ||
        decide (getCurrentEpoch s < s.validators.data[i].activationEpoch) ||
        beforeQueue.any (fun c => c.sourceIndex.toNat == i)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at chosen ⊢
      rcases chosen with recent | queued
      · exact Or.inl (funding_lifecycle_support lifecycle epochs recent)
      · rcases pending i queued with queued | ⟨v, same, recent⟩
        · exact Or.inr queued
        · have equal := Option.some.inj (found.symm.trans same)
          exact Or.inl (equal ▸ recent)
    simpa only [chosen, prior, ↓reduceIte] using funding i
  · split <;> simp_all

private theorem funding_balance_change {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (registry : t.validators = s.validators)
    (slot : t.slot = s.slot) :
    funding_potential t queue ≤ funding_potential s queue +
      ∑ i ∈ Finset.range s.validators.data.size,
        (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  apply funding_potential_change queue queue _ (congrArg (·.data.size) registry)
    (.of_data (congrArg (·.data) registry)) (by rw [epoch]) (fun _ h => Or.inl h)
  intro i
  have effective : effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i := by
    simp [effectiveAt, registry]
  rw [effective]
  omega

private theorem funding_append {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (v : Validator) (amount : Gwei)
    (registry : t.validators.data = s.validators.data.push v)
    (balances : t.balances.data = s.balances.data.push amount)
    (matched : BalancesMatch s) (slot : t.slot = s.slot) :
    funding_potential t queue ≤ funding_potential s queue +
      max v.effectiveBalance.toNat amount.toNat := by
  change s.balances.data.size = s.validators.data.size at matched
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  unfold funding_potential
  rw [registry, Array.size_push, Finset.sum_range_succ]
  have old : (∑ i ∈ Finset.range s.validators.data.size,
      ((s.validators.data.push v)[i]?.map fun w =>
        if isActiveValidator w (getCurrentEpoch t) ||
            decide (getCurrentEpoch t < w.activationEpoch) ||
            queue.any (fun c => c.sourceIndex.toNat == i) then
          max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i)
        else 0).getD 0) =
      ∑ i ∈ Finset.range s.validators.data.size,
        (s.validators.data[i]?.map fun w =>
          if isActiveValidator w (getCurrentEpoch s) ||
              decide (getCurrentEpoch s < w.activationEpoch) ||
              queue.any (fun c => c.sourceIndex.toNat == i) then
            max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i)
          else 0).getD 0 := by
    apply Finset.sum_congr rfl
    intro i member
    have inside := Finset.mem_range.mp member
    have balanceInside : i < s.balances.data.size := by simpa [matched] using inside
    simp only [effectiveAt, actualBalanceAt, registry, balances,
      Array.getElem?_push_lt inside, Array.getElem?_push_lt balanceInside,
      getElem?_pos s.validators.data i inside, getElem?_pos s.balances.data i balanceInside,
      epoch]
  rw [old]
  apply Nat.add_le_add_left
  have lastBalance : (s.balances.data.push amount)[s.validators.data.size]? = some amount := by
    rw [← matched, Array.getElem?_push_size]
  simp only [effectiveAt, actualBalanceAt, registry, balances, lastBalance,
    Array.getElem?_push_size, Option.map_some, Option.getD_some]
  split <;> omega

/-- Adding a validator raises the potential by at most its amount. -/
theorem funding_registration {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (matched : BalancesMatch s)
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    funding_potential t queue ≤ funding_potential s queue + amount.toNat := by
  obtain ⟨registry, balances⟩ := addValidatorToRegistry_push ok matched
  have rounded : amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ amount := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  have lowered := UInt64.le_iff_toNat_le.mp (UInt64.sub_le rounded)
  have cap : (getValidatorFromDeposit preset fork key credentials amount).effectiveBalance.toNat ≤
      amount.toNat := by
    simp only [getValidatorFromDeposit, Uint64.toNat_min]
    exact (Nat.min_le_left _ _).trans lowered
  simpa only [Nat.max_eq_right cap] using
    funding_append queue _ amount registry balances matched (addValidatorToRegistry_slot ok)

/-- Effective-balance updates do not raise the potential. -/
theorem funding_effective_updates {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (ok : processEffectiveBalanceUpdates s = .ok t) :
    funding_potential t queue ≤ funding_potential s queue := by
  have slot := (frame_processEffectiveBalanceUpdates ok).slot
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  have bound := funding_potential_change queue queue (fun _ => 0)
    (sameSizes_processEffectiveBalanceUpdates ok).1
    (registryLifecycle_processEffectiveBalanceUpdates ok)
    (by rw [epoch]) (fun _ h => Or.inl h)
    (fun i => by simpa using processEffectiveBalanceUpdates_funding ok i)
  simpa using bound

private theorem funding_potential_transfer {fork : Fork} {s t : BeaconState preset fork}
    (c : PendingConsolidation) (rest : List PendingConsolidation) (v : Validator) (moved : Nat)
    (registry : t.validators = s.validators) (slot : t.slot = s.slot)
    (found : s.validators.data[c.sourceIndex.toNat]? = some v)
    (inactive : isActiveValidator v (getCurrentEpoch s) = false)
    (activated : v.activationEpoch ≤ getCurrentEpoch s)
    (absent : ∀ d ∈ rest, d.sourceIndex ≠ c.sourceIndex)
    (funded : moved ≤ v.effectiveBalance.toNat)
    (balances : ∀ i, actualBalanceAt ⟨fork, t⟩ i ≤ actualBalanceAt ⟨fork, s⟩ i +
      if i = c.targetIndex.toNat then moved else 0) :
    funding_potential t rest ≤ funding_potential s (c :: rest) := by
  let before := fun i => (s.validators.data[i]?.map fun w =>
    if isActiveValidator w (getCurrentEpoch s) ||
        decide (getCurrentEpoch s < w.activationEpoch) ||
        (c :: rest).any (fun d => d.sourceIndex.toNat == i) then
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) else 0).getD 0
  let after := fun i => (t.validators.data[i]?.map fun w =>
    if isActiveValidator w (getCurrentEpoch t) ||
        decide (getCurrentEpoch t < w.activationEpoch) ||
        rest.any (fun d => d.sourceIndex.toNat == i) then
      max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) else 0).getD 0
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  have effective : ∀ i, effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i := by
    intro i; simp [effectiveAt, registry]
  have point : ∀ i, after i + (if i = c.sourceIndex.toNat then moved else 0) ≤
      before i + (if i = c.targetIndex.toNat then moved else 0) := by
    intro i
    by_cases source : i = c.sourceIndex.toNat
    · subst i
      have noSource : rest.any (fun d => d.sourceIndex.toNat == c.sourceIndex.toNat) = false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        obtain ⟨d, member, eq⟩ := List.any_eq_true.mp yes
        exact absent d member (UInt64.toNat_inj.mp (by simpa using eq))
      simp only [after, before, registry, epoch, found, Option.map_some, Option.getD_some,
        inactive, UInt64.not_lt.mpr activated, decide_false, Bool.false_or, noSource,
        Bool.false_eq_true, ↓reduceIte, List.any_cons, beq_self_eq_true, Bool.true_or,
        Nat.zero_add]
      have eff : effectiveAt ⟨fork, s⟩ c.sourceIndex.toNat = v.effectiveBalance.toNat := by
        simp [effectiveAt, found]
      rw [eff]
      omega
    · have credit := balances i
      cases read : s.validators.data[i]? with
      | none => simp [after, before, registry, read, source]
      | some w =>
        simp only [after, before, registry, epoch, read, Option.map_some, Option.getD_some,
          effective, source, ↓reduceIte, Nat.add_zero, List.any_cons,
          show (c.sourceIndex.toNat == i) = false by simp [Ne.symm source], Bool.false_or]
        split <;> omega
  have total := Finset.sum_le_sum (s := Finset.range s.validators.data.size)
    (fun i _ => point i)
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range,
    inside, ↓reduceIte] at total
  change (∑ i ∈ Finset.range t.validators.data.size, after i) ≤
    ∑ i ∈ Finset.range s.validators.data.size, before i
  rw [registry]
  split at total <;> omega

private theorem funding_transfer_balances {fork : Fork} {s lowered t : BeaconState preset fork}
    {source target : ValidatorIndex} {amount : Gwei}
    (debit : decreaseBalance s source amount = .ok lowered)
    (credit : increaseBalance lowered target amount = .ok t) :
    ∀ i, actualBalanceAt ⟨fork, t⟩ i ≤ actualBalanceAt ⟨fork, s⟩ i +
      if i = target.toNat then amount.toNat else 0 := by
  intro i
  cases found : s.balances.data[i]? with
  | some balance =>
    obtain ⟨low, lowFound, lowEq⟩ := balance_decreaseBalance debit found
    obtain ⟨high, highFound, highEq⟩ := balance_increaseBalance credit lowFound
    simp only [actualBalanceAt, found, highFound, Option.map_some, Option.getD_some]
    by_cases hs : source.toNat = i <;> by_cases ht : target.toNat = i <;>
      simp_all
    omega
  | none =>
    have size := (sameSizes_increaseBalance credit).2.trans (sameSizes_decreaseBalance debit).2
    have outside := Array.getElem?_eq_none_iff.mp found
    have final : t.balances.data[i]? = none := Array.getElem?_eq_none (by omega)
    simp [actualBalanceAt, found, final]

private theorem funding_pass_consolidations {fork : Fork} {next : Epoch}
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ {queue : List PendingConsolidation} {s : BeaconState preset fork} {result},
      passPendingConsolidations next s queue = .ok result →
      next.toNat = (getCurrentEpoch s).toNat + 1 →
      (queue.map (·.sourceIndex)).Nodup →
      (∀ c ∈ queue, ∃ v, s.validators.data[c.sourceIndex.toNat]? = some v ∧
        v.activationEpoch ≤ getCurrentEpoch s ∧
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat) →
      funding_potential result.1 (queue.drop result.2) ≤ funding_potential s queue
  | [], s, result, ok, _, _, _ => by
    cases ok
    exact Nat.le_refl _
  | c :: rest, s, result, ok, nextEq, distinct, sources => by
    have distinct' := List.nodup_cons.mp distinct
    obtain ⟨v, found, activated, ordered⟩ := sources c (by simp)
    have read : getValidator s c.sourceIndex = .ok v := by simp [getValidator, found]
    unfold passPendingConsolidations at ok
    rw [show liftAccessor (getValidator s c.sourceIndex) =
      (Except.ok v : Except TransitionError _) by simp [read, liftAccessor, Except.mapError]] at ok
    simp only [bind_ok_iff, Except.ok.injEq, exists_eq_left'] at ok
    by_cases slashed : v.slashed = true
    · simp only [slashed, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨result', passed, rfl⟩ := ok
      have ih := funding_pass_consolidations delay passed nextEq distinct'.2
        (fun d member => sources d (List.mem_cons_of_mem c member))
      exact ih.trans (funding_potential_mono s (fun d member => List.mem_cons_of_mem c member))
    · simp only [slashed] at ok
      by_cases waits : next < v.withdrawableEpoch
      · simp only [waits, ↓reduceIte, pure, Except.pure] at ok
        cases ok
        exact Nat.le_refl _
      · simp only [waits, ↓reduceIte, pure, Except.pure] at ok
        obtain ⟨balance, balanceOk, ok⟩ := bind_ok_iff.mp ok
        simp only [bind_ok_iff, Except.ok.injEq] at ok
        obtain ⟨lowered, loweredOk, raised, raisedOk, result', passed, rfl⟩ := ok
        have debit := liftAccessor_ok.mp loweredOk
        have credit := liftAccessor_ok.mp raisedOk
        have registry := (increaseBalance_validators credit).trans
          (decreaseBalance_validators debit)
        have slot : raised.slot = s.slot :=
          (frame_increaseBalance credit).slot.trans (frame_decreaseBalance debit).slot
        have epoch : getCurrentEpoch raised = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
        have ih := funding_pass_consolidations delay passed (epoch ▸ nextEq) distinct'.2 (by
          intro d member
          obtain ⟨w, found, activated, ordered⟩ := sources d (List.mem_cons_of_mem c member)
          exact ⟨w, by rw [registry]; exact found, epoch ▸ activated, ordered⟩)
        have one := funding_potential_transfer c rest v (min balance v.effectiveBalance).toNat
          registry slot found
          (funding_source_inactive v _ _ nextEq delay ordered (UInt64.not_lt.mp waits))
          activated (by
            intro d member equal
            exact distinct'.1 (List.mem_map.mpr ⟨d, member, equal⟩))
          (UInt64.le_iff_toNat_le.mp Std.min_le_right) (funding_transfer_balances debit credit)
        exact ih.trans one

private theorem funding_consolidations {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (distinct : ((s.pendingConsolidations electra).data.toList.map (·.sourceIndex)).Nodup)
    (sources : ∀ c ∈ (s.pendingConsolidations electra).data.toList,
      ∃ v, s.validators.data[c.sourceIndex.toNat]? = some v ∧
        v.activationEpoch ≤ getCurrentEpoch s ∧
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat)
    (ok : processPendingConsolidations s electra = .ok t) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  simp only [processPendingConsolidations, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨next, nextOk, result, passed, rfl⟩ := ok
  have nextEq := (Uint64.addChecked_ok_iff.mp
    (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  simp only [UInt64.toNat_one] at nextEq
  have bound := funding_pass_consolidations delay passed nextEq distinct sources
  rw [← funding_potential_eq, ← funding_potential_eq]
  simp only [fundingSources, electra, ↓reduceDIte]
  have takeEq : ((s.pendingConsolidations electra).data.toList.drop result.2).take
      ((s.pendingConsolidations electra).data.size - result.2) =
      (s.pendingConsolidations electra).data.toList.drop result.2 :=
    List.take_of_length_le (by simp)
  convert bound using 1
  simp only [funding_potential, Array.toList_extract, takeEq, effectiveAt, actualBalanceAt,
    getCurrentEpoch]
  congr 3

private theorem funding_consolidations_invariant {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (holds : PendingConsolidationInvariant config s)
    (ok : processPendingConsolidations s electra = .ok t) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  obtain ⟨distinct, sources⟩ := holds electra
  apply funding_consolidations electra delay distinct ?_ ok
  intro c member
  obtain ⟨v, found, activated, ordered, _⟩ := sources c member
  exact ⟨v, found, activated, ordered⟩

private theorem funding_deposit_spending {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    ∃ nextEpoch churn available finalizedSlot pass,
      liftArith (Uint64.addChecked (getCurrentEpoch s) 1) = .ok nextEpoch ∧
      depositChurnLimit config s = .ok churn ∧
      passPendingDeposits config checks (depositWaits s finalizedSlot) nextEpoch available
        s 0 0 #[] (s.pendingDeposits electra).data.toList = .ok pass ∧
      t.validators = pass.1.state.validators ∧ t.balances = pass.1.state.balances ∧
      pass.1.processed.toNat + (t.depositBalanceToConsume electra).toNat ≤
        (s.depositBalanceToConsume electra).toNat +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  obtain ⟨nextEpoch, churn, available, finalizedSlot, pass, nextOk, churnOk, availableOk,
    _, passed, validators, balances, _, carried⟩ := processPendingDeposits_pass ok
  refine ⟨nextEpoch, churn, available, finalizedSlot, pass, nextOk, churnOk, passed,
    validators, balances, ?_⟩
  have processed := UInt64.le_iff_toNat_le.mp
    (passPendingDeposits_processed_le passed (by simp))
  have availableEq := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp availableOk)).2
  have churnBound : churn.toNat ≤
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
    rw [depositChurnLimit_of_lt early] at churnOk
    simp only [getActivationExitChurnLimit, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churnOk
    obtain ⟨whole, _, rfl⟩ := churnOk
    simp only [Uint64.toNat_min]
    exact Nat.min_le_left _ _
  rw [carried]
  split <;> omega

private theorem funding_deposit_selection {fork : Fork} {s t : BeaconState preset fork}
    {deposit : PendingDeposit} {nextEpoch : Epoch}
    (ok : applyPendingDeposit config checks s deposit = .ok t)
    (i : Nat) (selected : ∀ v, s.validators.data[i]? = some v →
      ¬ v.withdrawableEpoch < nextEpoch) :
    ∀ v, t.validators.data[i]? = some v → ¬ v.withdrawableEpoch < nextEpoch := by
  intro v found
  have fresh (v : Validator)
      (same : v.withdrawableEpoch = FAR_FUTURE_EPOCH) : ¬ v.withdrawableEpoch < nextEpoch := by
    rw [same, UInt64.lt_iff_toNat_lt]
    have := nextEpoch.toNat_lt
    change ¬ (2 ^ 64 - 1 < nextEpoch.toNat)
    omega
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact selected v found
  · rw [increaseBalance_validators raised] at found
    exact selected v found
  · rcases addValidatorToRegistry_validator added found with old | rfl
    · exact selected v old
    · exact fresh _ rfl

private theorem funding_withdrawn_deposit {fork : Fork} {s t : BeaconState preset fork}
    {deposit : PendingDeposit} {nextEpoch : Epoch} {exited : Bool}
    (status : depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true))
    (ok : applyPendingDeposit config checks s deposit = .ok t)
    (i : Nat) (selected : ∀ v, s.validators.data[i]? = some v →
      ¬ v.withdrawableEpoch < nextEpoch) :
    actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
  unfold depositTargetStatus at status
  split at status
  · rename_i position found
    simp only [bind_ok_iff] at status
    obtain ⟨index, converted, status⟩ := status
    have indexEq := (Uint64.ofNatChecked_ok_iff.mp (mapError_ok_iff.mp converted)).2
    cases read : s.validators.data[index.toNat]? with
    | none => simp [read] at status
    | some validator =>
      simp only [read, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at status
      have withdrawn : validator.withdrawableEpoch < nextEpoch := by
        exact of_decide_eq_true status.2
      have other : i ≠ position := by
        intro same
        subst i
        rw [indexEq] at read
        exact selected validator read withdrawn
      have kept := (applyPendingDeposit_known_balances found ok).2 i other
      simp only [actualBalanceAt, kept]
  · cases status

private theorem funding_selected_credit {fork : Fork} (s t : BeaconState preset fork)
    (indices : Finset Nat) :
    (∑ i ∈ indices, (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) ≤
      balanceCredits s t := by
  have restrict : (∑ i ∈ indices,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) =
      ∑ i ∈ indices ∩ Finset.range t.balances.data.size,
        (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro i inside outside
    have beyond : t.balances.data.size ≤ i := by simpa [inside] using outside
    simp [actualBalanceAt, Array.getElem?_eq_none beyond]
  rw [restrict]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by intros; omega)

private theorem funding_supported_balance_change {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (registry : t.validators = s.validators)
    (slot : t.slot = s.slot) :
    funding_potential t queue ≤ funding_potential s queue +
      ∑ i ∈ Finset.range s.validators.data.size,
        (s.validators.data[i]?.map fun v =>
          if isActiveValidator v (getCurrentEpoch s) ||
              decide (getCurrentEpoch s < v.activationEpoch) ||
              queue.any (fun c => c.sourceIndex.toNat == i) then
            actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i
          else 0).getD 0 := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  unfold funding_potential
  rw [registry, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have effective : effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i := by
    simp [effectiveAt, registry]
  cases found : s.validators.data[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some, epoch, effective]
    split <;> omega

private theorem funding_withdrawn_support (v : Validator) (epoch : Epoch)
    (ordered : v.exitEpoch ≤ v.withdrawableEpoch)
    (activated : v.activationEpoch ≤ epoch) (withdrawn : v.withdrawableEpoch ≤ epoch) :
    isActiveValidator v epoch = false ∧ ¬ epoch < v.activationEpoch := by
  have exited : v.exitEpoch ≤ epoch := UInt64.le_trans ordered withdrawn
  exact ⟨by simp [isActiveValidator, UInt64.not_lt.mpr exited], UInt64.not_lt.mpr activated⟩

private theorem funding_balance_selection {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (registry : t.validators = s.validators)
    (slot : t.slot = s.slot) (ordered : ExitsOrdered s)
    (activation : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) :
    funding_potential t queue ≤ funding_potential s queue +
      ∑ i ∈ Finset.range s.validators.data.size,
        (s.validators.data[i]?.map fun v =>
          if v.withdrawableEpoch ≤ getCurrentEpoch s then
            if queue.any (fun c => c.sourceIndex.toNat == i) then
              actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i
            else 0
          else actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i).getD 0 := by
  apply (funding_supported_balance_change queue registry slot).trans
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  cases found : s.validators.data[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    by_cases withdrawn : v.withdrawableEpoch ≤ getCurrentEpoch s
    · have member := Array.mem_of_getElem? found
      have activated := UInt64.le_trans (activation v member)
        (UInt64.le_trans (ordered v member) withdrawn)
      obtain ⟨inactive, notFuture⟩ := funding_withdrawn_support v _
        (ordered v member) activated withdrawn
      simp [withdrawn, inactive, notFuture]
    · simp only [withdrawn, ↓reduceIte]
      split <;> omega

private theorem funding_pending_deposit {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (matched : BalancesMatch s) {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    funding_potential t queue ≤ funding_potential s queue + deposit.amount.toNat := by
  have credit := (deposit_credit_bound s t matched deposit ok).2
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · omega
  · have bound := funding_balance_change queue (increaseBalance_validators ok)
      (frame_increaseBalance ok).slot
    have selected := funding_selected_credit s t (Finset.range s.validators.data.size)
    omega
  · exact funding_registration queue matched ok

private theorem funding_deposit_monotone {fork : Fork} {s t : BeaconState preset fork}
    (matched : BalancesMatch s) {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) (i : Nat) :
    actualBalanceAt ⟨fork, s⟩ i ≤ actualBalanceAt ⟨fork, t⟩ i := by
  have zero := (deposit_credit_bound s t matched deposit ok).1
  by_cases inside : i < s.balances.data.size
  · have point := Finset.single_le_sum (f := fun j =>
      actualBalanceAt ⟨fork, s⟩ j - actualBalanceAt ⟨fork, t⟩ j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr inside)
    change _ ≤ balanceDebits s t at point
    omega
  · simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt inside)]

private theorem funding_withdrawn_change {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) {deposit : PendingDeposit} {nextEpoch : Epoch}
    {exited : Bool}
    (status : depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true))
    (nextEq : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1)
    (ordered : ExitsOrdered s)
    (activation : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    funding_potential t queue ≤ funding_potential s queue +
      ∑ i ∈ Finset.range s.validators.data.size,
        (s.validators.data[i]?.map fun v =>
          if v.withdrawableEpoch ≤ getCurrentEpoch s ∧
              queue.any (fun c => c.sourceIndex.toNat == i) = true then
            actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i
          else 0).getD 0 := by
  have known : ∃ position, s.validators.data.findIdx? (·.pubkey == deposit.pubkey) =
      some position := by
    unfold depositTargetStatus at status
    split at status
    · exact ⟨_, by assumption⟩
    · cases status
  obtain ⟨position, found⟩ := known
  have registry : t.validators = s.validators := (applyPendingDeposit_known found ok).2
  apply (funding_balance_selection queue registry (frame_applyPendingDeposit ok).slot
    ordered activation).trans
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  cases read : s.validators.data[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    by_cases withdrawn : v.withdrawableEpoch ≤ getCurrentEpoch s
    · simp [withdrawn]
    · have unchanged := funding_withdrawn_deposit status ok i (by
        intro w same
        have equal := Option.some.inj (read.symm.trans same)
        subst w
        rw [UInt64.lt_iff_toNat_lt]
        have after := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp withdrawn)
        omega)
      simp [withdrawn, unchanged]

private theorem funding_withdrawn_selected {fork : Fork} {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (indices : Finset Nat)
    {deposit : PendingDeposit} {nextEpoch : Epoch} {exited : Bool}
    (status : depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true))
    (nextEq : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1)
    (ordered : ExitsOrdered s)
    (activation : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (selected : ∀ i, i ∉ indices → queue.any (fun c => c.sourceIndex.toNat == i) = true →
      ∀ v, s.validators.data[i]? = some v → ¬ v.withdrawableEpoch < nextEpoch)
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    funding_potential t queue ≤ funding_potential s queue +
      ∑ i ∈ indices, (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
  apply (funding_withdrawn_change queue status nextEq ordered activation ok).trans
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ i ∈ Finset.range s.validators.data.size,
        if i ∈ indices then actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i
        else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases inside : i ∈ indices
      · simp only [inside, ↓reduceIte]
        cases read : s.validators.data[i]? with
        | none => simp
        | some v => simp only [Option.map_some, Option.getD_some]; split <;> omega
      simp only [inside, ↓reduceIte]
      cases read : s.validators.data[i]? with
      | none => simp
      | some v =>
        simp only [Option.map_some, Option.getD_some]
        split
        · rename_i supported
          have notWithdrawn := selected i inside supported.2 v read
          have withdrawn := UInt64.le_iff_toNat_le.mp supported.1
          rw [UInt64.lt_iff_toNat_lt] at notWithdrawn
          omega
        · omega
    _ ≤ _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => (Finset.mem_filter.mp hi).2) (by intros; omega)

private theorem funding_pass_monotone {fork : Fork} {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} {deposits : List PendingDeposit}
    {s : BeaconState preset fork} {processed : Gwei} {count : Nat}
    {postponed : Array PendingDeposit} {pass}
    (ok : passPendingDeposits config checks stop nextEpoch available s processed count
      postponed deposits = .ok pass) (matched : BalancesMatch s) :
    ∀ i, actualBalanceAt ⟨fork, s⟩ i ≤ actualBalanceAt ⟨fork, pass.1.state⟩ i := by
  obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied ok
  have bound := foldlM_ok_invariant (fun t => BalancesMatch t ∧
      ∀ i, actualBalanceAt ⟨fork, s⟩ i ≤ actualBalanceAt ⟨fork, t⟩ i)
    (fun a deposit b prior credited =>
      ⟨(applyPendingDeposit_kept credited).1 prior.1,
        fun i => (prior.2 i).trans (funding_deposit_monotone prior.1 credited i)⟩)
    (show BalancesMatch s ∧ ∀ i, actualBalanceAt ⟨fork, s⟩ i ≤
      actualBalanceAt ⟨fork, s⟩ i from ⟨matched, fun _ => le_rfl⟩) facts.applies
  exact bound.2

private theorem funding_pass_potential {fork : Fork} {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} (queue : List PendingConsolidation)
    (indices : Finset Nat)
    (activationKept : ∀ (s t : BeaconState preset fork) (deposit : PendingDeposit),
      (∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) →
      applyPendingDeposit config checks s deposit = .ok t →
      ∀ v ∈ t.validators.data, v.activationEpoch ≤ v.exitEpoch) :
    ∀ {deposits : List PendingDeposit} {s : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available s processed count postponed
        deposits = .ok pass → BalancesMatch s → ExitsOrdered s →
      (∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) →
      nextEpoch.toNat = (getCurrentEpoch s).toNat + 1 →
      (∀ i, i ∉ indices → queue.any (fun c => c.sourceIndex.toNat == i) = true →
        ∀ v, s.validators.data[i]? = some v → ¬ v.withdrawableEpoch < nextEpoch) →
      funding_potential pass.1.state queue + processed.toNat ≤
        funding_potential s queue + pass.1.processed.toNat +
          ∑ i ∈ indices,
            (actualBalanceAt ⟨fork, pass.1.state⟩ i - actualBalanceAt ⟨fork, s⟩ i)
  | [], _, _, _, _, _, ok, _, _, _, _, _ => by cases ok; simp
  | deposit :: rest, s, processed, count, postponed, pass, ok, matched, ordered,
      activation, nextEq, selected => by
    unfold passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; simp
    split at ok
    · cases ok
    rename_i status statusOk
    split at ok
    · rename_i withdrawn
      split at ok
      · cases ok
      rename_i t credited
      split at ok
      · cases ok
      rename_i result passed
      cases ok
      have frame := frame_applyPendingDeposit credited
      have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, frame.slot]
      have ih := funding_pass_potential queue indices activationKept (deposits := rest) passed
        (frame.balancesMatch matched) (frame.exitsOrdered ordered)
        (activationKept s t deposit activation credited) (epoch ▸ nextEq)
        (fun i outside pending => funding_deposit_selection credited i (selected i outside pending))
      have one := funding_withdrawn_selected queue indices (exited := status.1)
        (by
          have equal : status = (status.1, true) := by cases status; simp_all
          exact equal ▸ (liftAccessor_ok.mp statusOk)) nextEq ordered activation selected credited
      have sums : (∑ i ∈ indices, (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) +
          (∑ i ∈ indices,
            (actualBalanceAt ⟨fork, result.1.state⟩ i - actualBalanceAt ⟨fork, t⟩ i)) =
          ∑ i ∈ indices,
            (actualBalanceAt ⟨fork, result.1.state⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have := funding_deposit_monotone matched credited i
        have := funding_pass_monotone passed (frame.balancesMatch matched) i
        omega
      dsimp only at ⊢
      omega
    split at ok
    · split at ok
      · cases ok
      rename_i passed
      cases ok
      exact funding_pass_potential queue indices activationKept (deposits := rest) passed
        matched ordered activation nextEq selected
    split at ok
    · cases ok
    rename_i total totalOk
    split at ok
    · cases ok; simp
    split at ok
    · cases ok
    rename_i t credited
    split at ok
    · cases ok
    rename_i result passed
    cases ok
    have frame := frame_applyPendingDeposit credited
    have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, frame.slot]
    have ih := funding_pass_potential queue indices activationKept (deposits := rest) passed
      (frame.balancesMatch matched) (frame.exitsOrdered ordered)
      (activationKept s t deposit activation credited) (epoch ▸ nextEq)
      (fun i outside pending => funding_deposit_selection credited i (selected i outside pending))
    have one := funding_pending_deposit queue matched credited
    have spent := (Uint64.addChecked_ok_iff.mp
      (mapError_ok_iff.mp (liftAccessor_ok.mp totalOk))).2
    have sums : (∑ i ∈ indices,
        (actualBalanceAt ⟨fork, result.1.state⟩ i - actualBalanceAt ⟨fork, t⟩ i)) ≤
        ∑ i ∈ indices,
          (actualBalanceAt ⟨fork, result.1.state⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
      apply Finset.sum_le_sum
      intro i _
      have := funding_deposit_monotone matched credited i
      omega
    dsimp only at ⊢
    omega

private theorem funding_pending_potential {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (queue : List PendingConsolidation) (indices : Finset Nat)
    (activationKept : ∀ (s t : BeaconState preset fork) (deposit : PendingDeposit),
      (∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) →
      applyPendingDeposit config checks s deposit = .ok t →
      ∀ v ∈ t.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (selected : ∀ i, i ∉ indices → queue.any (fun c => c.sourceIndex.toNat == i) = true →
      ∀ v, s.validators.data[i]? = some v →
        (getCurrentEpoch s).toNat < v.withdrawableEpoch.toNat)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    funding_potential t queue + (t.depositBalanceToConsume electra).toNat ≤
      funding_potential s queue + (s.depositBalanceToConsume electra).toNat +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        ∑ i ∈ indices, (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
  obtain ⟨next, churn, available, finalized, pass, nextOk, _, passed, registry, balances, spent⟩ :=
    funding_deposit_spending electra early ok
  have nextEq := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp nextOk)).2
  simp only [UInt64.toNat_one] at nextEq
  have bound := funding_pass_potential queue indices activationKept passed matched ordered
    activation nextEq (by
      intro i outside pending v read
      have later := selected i outside pending v read
      rw [UInt64.lt_iff_toNat_lt]
      omega)
  obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied passed
  have slot : pass.1.state.slot = s.slot := foldlM_ok_invariant (fun t => t.slot = s.slot)
    (fun a deposit b prior credited => (frame_applyPendingDeposit credited).slot.trans prior)
    rfl facts.applies
  have finalSlot : t.slot = pass.1.state.slot :=
    (frame_processPendingDeposits ok).slot.trans slot.symm
  have potential : funding_potential t queue = funding_potential pass.1.state queue := by
    simp only [funding_potential, registry, balances, effectiveAt, actualBalanceAt,
      getCurrentEpoch, finalSlot]
    congr 3
  have credits : (∑ i ∈ indices, (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) =
      ∑ i ∈ indices,
        (actualBalanceAt ⟨fork, pass.1.state⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
    simp only [actualBalanceAt, balances]
  simp only [UInt64.toNat_zero, Nat.add_zero] at bound
  rw [potential, credits]
  omega

private theorem funding_pending_funded {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (activationKept : ∀ (s t : BeaconState preset fork) (deposit : PendingDeposit),
      (∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) →
      applyPendingDeposit config checks s deposit = .ok t →
      ∀ v ∈ t.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    fundedStake ⟨fork, t⟩ + (t.depositBalanceToConsume electra).toNat ≤
      fundedStake ⟨fork, s⟩ + (s.depositBalanceToConsume electra).toNat +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        withdrawnConsolidationCredit ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ := by
  let indices := (Finset.range s.validators.data.size).filter fun i =>
    (s.validators.data[i]?.map fun v =>
      v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat ∧
        (s.pendingConsolidations electra).data.any (fun c => c.sourceIndex.toNat == i)).getD false
  have bound := funding_pending_potential electra early
    (s.pendingConsolidations electra).data.toList indices activationKept matched ordered activation
    (by
      intro i outside pending v read
      have inside := (Array.getElem?_eq_some_iff.mp read).1
      have notWithdrawn : ¬ v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat := by
        intro withdrawn
        apply outside
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr inside, ?_⟩
        simpa only [read, Option.map_some, Option.getD_some, ← Array.any_toList] using
          And.intro withdrawn pending
      omega) ok
  have credit : (∑ i ∈ indices,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) =
      withdrawnConsolidationCredit ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ := by
    unfold withdrawnConsolidationCredit
    simp only [electra, ↓reduceDIte]
    rw [funding_sum_zipIdx s.validators.data.toList (fun v i =>
      if decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat) &&
          (s.pendingConsolidations electra).data.any (fun c => c.sourceIndex.toNat == i) then
        actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i else 0)]
    simp only [indices, Finset.sum_filter, Array.length_toList, Array.getElem?_toList]
    apply Finset.sum_congr rfl
    intro i _
    cases read : s.validators.data[i]? with
    | none => simp
    | some v => simp [Bool.and_eq_true]
  have queue := processPendingDeposits_pendingConsolidations ok
  rw [credit] at bound
  rw [← funding_potential_eq s, ← funding_potential_eq t]
  simpa only [fundingSources, electra, ↓reduceDIte, queue] using bound

/-- The pending deposits and consolidations raise the funding by at most one epoch of churn.

The deposit credit of withdrawn validators is the only other credit. -/
theorem funding_pending_balances {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ActivationExitOrder s)
    (pending : PendingConsolidationInvariant config s)
    (ok : processPendingBalances config checks s = .ok t) :
    ∃ deposited, processPendingDeposits config checks s electra = .ok deposited ∧
      processPendingConsolidations deposited electra = .ok t ∧
      fundedStake ⟨fork, t⟩ + (t.depositBalanceToConsume electra).toNat ≤
        fundedStake ⟨fork, s⟩ + (s.depositBalanceToConsume electra).toNat +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
          withdrawnConsolidationCredit ⟨.deposits, ⟨fork, s⟩, ⟨fork, deposited⟩, 0, 0⟩ := by
  simp only [processPendingBalances, electra, ↓reduceDIte, bind_ok_iff] at ok
  obtain ⟨deposited, depositedOk, consolidatedOk⟩ := ok
  have deposit := funding_pending_funded electra early
    (fun _ _ _ holds credited => ActivationExitOrder.applyPendingDeposit holds credited)
    matched ordered activation depositedOk
  have consolidate := funding_consolidations_invariant electra delay
    (pending.pendingDeposits depositedOk) consolidatedOk
  have carry := depositCarryLaws.processPendingConsolidations consolidatedOk
  refine ⟨deposited, depositedOk, consolidatedOk, ?_⟩
  rw [carry]
  omega

/-- Unspent deposit capacity retained across post-Electra operations. -/
def funding_carry (x : ForkedBeaconState preset) : Nat :=
  if h : .pectra ≤ x.fork then (x.state.depositBalanceToConsume h).toNat else 0

/-- Before Gloas, the stages before the payments and the events of their replay.

The replay records the rewards and the slashings.

From Electra it then records the pending deposits and the pending consolidations. -/
theorem funding_epoch_site {fork : Fork} {s t : BeaconState preset fork}
    (ok : epochBeforePayments config checks s = .ok t)
    {events : List (BalanceEvent preset)}
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events)) :
    ∃ (justified scored rewarded registered slashed reset deposited : BeaconState preset fork)
      (rewardEvents : List (BalanceEvent preset)) (limit : Nat),
      EpochStage.Edge config checks .justification s justified ∧
      EpochStage.Edge config checks .inactivity justified scored ∧
      processRewardsAndPenalties config scored = .ok rewarded ∧
      processRegistryUpdates config rewarded = .ok registered ∧
      processSlashings registered = .ok slashed ∧
      EpochStage.Edge config checks .eth1Reset slashed reset ∧
      EpochStage.Edge config checks .pendingDeposits reset deposited ∧
      EpochStage.Edge config checks .pendingConsolidations deposited t ∧
      replayRewards (config := config) (scored, []) = .ok (rewarded, rewardEvents) ∧
      events = rewardEvents ++
        [⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩] ++
        if electra : .pectra ≤ fork then
          [⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩,
            consumedDeposits reset deposited electra, 0⟩,
          ⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, t⟩,
            consumedConsolidations deposited t electra,
            consumedConsolidations deposited t electra⟩]
        else [] := by
  have trace :=
    EpochTrace.run_ok_iff.mp ((epochBeforePayments_eq_run config checks s).symm.trans ok)
  unfold EpochStage.prefixStages at trace
  cases trace; rename_i justified justifiedOk trace
  cases trace; rename_i scored scoredOk trace
  cases trace; rename_i rewarded rewardedOk trace
  cases trace; rename_i registered registeredOk trace
  cases trace; rename_i slashed slashedOk trace
  cases trace; rename_i reset resetOk trace
  cases trace; rename_i deposited depositedOk trace
  cases trace; rename_i consolidatedOk trace
  cases trace
  replace justifiedOk := EpochStage.action_cases.mp justifiedOk
  replace scoredOk := EpochStage.action_cases.mp scoredOk
  replace rewardedOk := EpochStage.action_cases.mp rewardedOk
  replace registeredOk := EpochStage.action_cases.mp registeredOk
  replace slashedOk := EpochStage.action_cases.mp slashedOk
  replace resetOk := EpochStage.action_cases.mp resetOk
  replace depositedOk := EpochStage.action_cases.mp depositedOk
  replace consolidatedOk := EpochStage.action_cases.mp consolidatedOk
  simp only [EpochStage.Edge] at rewardedOk registeredOk slashedOk
  obtain ⟨rewardEvents, rewardReplay⟩ := replayRewards_result scored rewarded [] rewardedOk
  obtain ⟨limit, limitOk⟩ := delayedSlashingLimit_result slashedOk
  refine ⟨justified, scored, rewarded, registered, slashed, reset, deposited, rewardEvents, limit,
    justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk, depositedOk,
    consolidatedOk, rewardReplay, ?_⟩
  have slashReplay : epochReplayAction (config := config) (checks := checks) .slashings
      (registered, rewardEvents) = .ok
        (slashed, rewardEvents ++
          [⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩]) := by
    simp [epochReplayAction, recordBalance, limitOk, slashedOk, bind, Except.bind, pure,
      Except.pure]
  simp only [epochBalanceReplay, EpochTrace.run, EpochStage.prefixStages, List.foldlM_cons,
    List.foldlM_nil, epochReplayAction_carried (by simp) justifiedOk,
    epochReplayAction_carried (by simp) scoredOk,
    show epochReplayAction (config := config) (checks := checks) .rewards (scored, []) =
      .ok (rewarded, rewardEvents) from rewardReplay,
    epochReplayAction_carried (k := .registry) (by simp) registeredOk, slashReplay,
    epochReplayAction_carried (by simp) resetOk, bind, Except.bind] at replayed
  simp only [EpochStage.Edge] at depositedOk consolidatedOk
  by_cases electra : .pectra ≤ fork
  · simp only [electra, ↓reduceDIte] at depositedOk consolidatedOk ⊢
    simp only [epochReplayAction, electra, ↓reduceDIte, depositedOk, consolidatedOk, bind,
      Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at replayed
    rw [← replayed.2]
    simp
  · simp only [electra, ↓reduceDIte] at depositedOk consolidatedOk ⊢
    subst depositedOk consolidatedOk
    simp only [epochReplayAction, electra, ↓reduceDIte, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at replayed
    simp [← replayed.2]

/-- A potential grows along a run by at most the churn per epoch plus the event credits. -/
private theorem funding_run_bound (potential : ForkedBeaconState preset → Nat)
    (spent gained : BalanceEvent preset → Nat) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (stepBound : ∀ {a b : ForkedBeaconState preset}, Run config checks x a →
      ∀ (step : Step config checks a b), b.fork < .glamsterdam →
      ∀ added, step.balanceEvents = .ok added →
      potential b + (added.map spent).sum ≤ potential a +
        ((getCurrentEpoch b.state).toNat - (getCurrentEpoch a.state).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + (added.map gained).sum) :
    potential y + (events.map spent).sum ≤ potential x +
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + (events.map gained).sum := by
  induction tail generalizing events with
  | nil => cases replayed; simp
  | @snoc middle last pre step ih =>
    have beforeEarly : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have beforeEpoch := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    have within := beforeEpoch.trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [within, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    have previous := ih beforeEarly within prior priorOk
    have latest := stepBound pre step early added addedOk
    have start : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch middle.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have count : (getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat =
        ((getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat) +
        ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) := by omega
    rw [count, Nat.add_mul, List.map_append, List.sum_append, List.map_append, List.sum_append]
    omega

theorem funding_window_of_steps {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (unique : PubkeysDistinct y.state)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (stepBound : ∀ {a b : ForkedBeaconState preset}, Run config checks x a →
      ∀ (step : Step config checks a b), b.fork < .glamsterdam →
      ∀ added, step.balanceEvents = .ok added →
      fundedStake b + funding_carry b ≤ fundedStake a + funding_carry a +
        ((getCurrentEpoch b.state).toNat - (getCurrentEpoch a.state).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (added.map fundingCredit).sum) :
    Models.stake (effectiveWeight y.state) (activeKeys y.state) ≤
      activeStakeWindow (config := config) x high events := by
  have bound := funding_run_bound (fun s => fundedStake s + funding_carry s) (fun _ => 0)
    fundingCredit tail early high endEpoch events replayed (fun pre step early added ok => by
      simpa using stepBound pre step early added ok)
  rw [show ∀ l : List (BalanceEvent preset), (l.map fun _ => 0).sum = 0 by simp,
    Nat.add_zero] at bound
  have active := funding_active_le y early unique
  have count : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high := by unfold driftHorizon; omega
  have larger := Nat.mul_le_mul_right
    config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat count
  simp only [activeStakeWindow, delay, ↓reduceIte, depositWindow, funding_carry] at *
  omega

end

end EthLib.Consensus.DirectSafety
