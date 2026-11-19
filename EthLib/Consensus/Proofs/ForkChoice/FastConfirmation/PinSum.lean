module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.FfgJustification
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedExit
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.EpochReads
import EthLib.Consensus.Proofs.Transition.PendingConsolidations
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Penalties
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Ledger
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Reserved.Operations
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Whistleblower
import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Notation
import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.BranchLedger
import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.BlockCredits
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Issuance
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Branch
import EthLib.Consensus.Proofs.Transition.EpochRewards
import EthLib.Consensus.Proofs.Transition.RewardDeltas
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Time
import EthLib.Consensus.Proofs.Participation

/-!
SCRATCH BASE for D-1 (not for merge): the summation of `pinReserve` at spec rev 2.5.3.
The per-term lemmas are `sorry` stubs, one owner each; `pinDrift_le_of_stubs` is closed from them.
Statements are frozen: a prover fills only its own stubs' bodies, with private helpers right above them.
It reads PinDriftBound's private lemmas by `import all` (a scratch-only waiver).
At the merge its content moves into PinDriftBound, every helper private, and this file is deleted.
-/

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety PinSplit

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The terms of `pinReserve`, by name. -/
structure PinTerms (preset : Preset) where
  quorum : ℕ
  exiting : ℕ
  queues : ℕ
  queueDep : ℕ
  queueExit : ℕ
  exitingRise : ℕ
  exitingCredits : ℕ
  queueRise : ℕ
  reserveW : ℕ
  flagged : ℕ
  seatShortfall : ℕ
  consolidationsX : ℕ
  exitedR : ℕ
  depth : ℕ
  syncProposer : ℕ
  proposerCredit : ℕ
  exitingBands : ℕ
  pendingR : ℕ
  creditGain : ℕ
  creditLow : ℕ
  creditCap : ℕ
  creditUnits : ℕ
  syncLeak : ℕ
  unitGain : ℕ
  consolidationsXCount : ℕ
  exitBeforeFin : ℕ → Bool
  bF : ℕ → ℕ
  perIncrement : ℕ
  depthFin : ℕ
  scoreMaxFin : ℕ
  slashCharge : ℕ
  consolidationGain : ℕ
  otherGain : ℕ
  keptArm : ℕ → Bool
  gainHigh : Bool
  pendingRB : ℕ → Bool
  credits : ℕ
  branchR : ℕ
  late : ℕ
  syncSeats : ℕ
  rise : ℕ → ℕ
  fall : ℕ → ℕ
  positions : Finset ℕ
  current : ℕ → Bool
  joining : ℕ
  joinRise : ℕ
  exitingB : ℕ → Bool
  lateB : ℕ → Bool
  exitedRB : ℕ → Bool
  slashedR : ℕ
  slashedRB : ℕ → Bool
  tight : Bool
  queueKeys : ℕ
  queueWindow : ℕ
  gainRateMax : ℕ
  exitFloor : ℕ
  lowKeys : ℕ
  lowB : ℕ → Bool
  lowEB : ℕ → ℕ
  newKeySeats : ℕ
  newKeySlack : ℕ
  newKeyFloor : ℕ
  leakAt : ℕ → ℕ → ℕ
  ebUp : ℕ → ℕ
  leak : ℕ → ℕ
  partialsDue : ℕ → ℕ
  base0 : ℕ → ℕ
  gainRate : ℕ → ℕ
  floorC : ℕ → ℕ
  drop : ℕ → ℕ

/-- `pinReserve` as the sum of its named terms, with the code's weights. -/
def PinTerms.total (t : PinTerms preset) : ℕ :=
  t.quorum + (3 * t.exiting + t.queues + t.credits + t.branchR + t.late +
    t.syncSeats + (∑ i ∈ t.positions with t.current i = true, t.rise i) + t.joinRise +
    3 * (∑ i ∈ t.positions with t.current i = true, t.fall i) +
    3 * t.exitingRise + t.exitingCredits + t.exitingBands + t.queueRise + t.reserveW + t.flagged +
    t.seatShortfall + (33 * t.consolidationsX + 9) / 10 + t.exitedR + t.pendingR + t.creditGain +
    t.creditUnits + t.syncLeak + 3 * t.unitGain * t.consolidationsXCount)

/-- A verbatim copy of `pinReserve`'s lets (spec rev 2.5.3), returning the named terms. -/
def pinTerms (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    PinTerms preset :=
  let epoch := getCurrentEpoch state
  let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  let slots := preset.SLOTS_PER_EPOCH.toNat
  let p := parameters preset fork
  let positions := Finset.range state.validators.data.size
  let validator (i : ℕ) := state.validators.data[i]?
  let effective (i : ℕ) := balanceAt state i
  let actual (i : ℕ) := ((state.balances.data[i]?).map (·.toNat)).getD 0
  let current (i : ℕ) := isActiveAt state epoch i
  let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
  let upcoming (i : ℕ) := isActiveAt state (epoch + 1) i
  let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
  let cap (i : ℕ) :=
    ((validator i).map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).getD 0
  let capMax := preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  let finalized := ancestor.finalizedCheckpoint.epoch.toNat
  let depth := epoch.toNat + 2 - finalized
  let tight := decide (depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
  let recentSlashing (i : ℕ) := (validator i).any fun v =>
    decide (finalized + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ v.withdrawableEpoch.toNat)
  let exiting := ∑ i ∈ positions with (before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true,
    effective i
  let totalGwei := (getTotalActiveBalance state).toOption.getD 0
  let total := totalGwei.toNat
  -- The rates are read at a quarter of the call's total.
  --
  -- A counting state that keeps that much has a base reward per increment at most twice this one.
  let quarter := if 18 * inc ≤ total then totalGwei / 4
    else preset.EFFECTIVE_BALANCE_INCREMENT / 5
  let perIncrement := ((getBaseRewardPerIncrement preset quarter).toOption.getD 0).toNat
  let depositChurn := config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  -- The exit and consolidation churns are bounded at three halves of the call's total.
  --
  -- A counting state on another branch can spend churn at a total up to that much.
  --
  -- They follow `exitChurnLimit` and `getConsolidationChurnLimit` on natural numbers.
  --
  -- They do not model the error branch of those reads.
  --
  -- `wide` is a natural-number bound on another branch's total, not a copy of a read.
  --
  -- It holds within the band of totals that the producer of the pin premise assumes.
  let wide := 3 * total / 2
  let round (amount : ℕ) := amount - amount % inc
  let balanceChurn := round (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (wide / config.CHURN_LIMIT_QUOTIENT.toNat))
  let activationExitChurn :=
    min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat balanceChurn
  let exitChurn := if .glamsterdam ≤ fork then
      round (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (wide / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat))
    else activationExitChurn
  let consolidationChurn := if .glamsterdam ≤ fork then
      round (wide / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat)
    else balanceChurn - activationExitChurn
  let consolidationCarry := max (if electra : .pectra ≤ fork then
      (finalizedState.consolidationBalanceToConsume electra).toNat else 0) consolidationChurn
  let exitCarry := max capMax depositChurn
  let depthFin := epoch.toNat + 2 - (getCurrentEpoch finalizedState).toNat
  let depositCarry := if electra : .pectra ≤ fork then
      (finalizedState.depositBalanceToConsume electra).toNat else 0
  let queueDep := 3 * (depthFin * depositChurn + depositCarry)
  let queueExit := if tight then 0 else
    3 * (depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry)
  let queues := queueDep + queueExit
  -- A sync seat's reward is bounded by its envelope at three halves of the call's total.
  --
  -- The integer reward is not monotone in the total, and the envelope is.
  --
  -- `div_mul_div_sqrt_le` bounds the reward of any total up to that much by it.
  let syncEnvelope := preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt (3 * total / 2) + 2) *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / slots / preset.SYNC_COMMITTEE_SIZE.toNat
  -- The inactivity score is read at the finalized block's state, with depth from its epoch.
  --
  -- That state lies on every branch, and a score rises by at most the bias per epoch on any.
  --
  -- So this bounds the score of a counting state, whose score can rise while the call's falls.
  let scoreFin (i : ℕ) := if altair : .altair ≤ fork then
      (((finalizedState.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  -- Sync-seat penalties are charged in aggregate, by the sync-seat terms, not per key.
  let leakAt (eb : ℕ) (i : ℕ) := 2 * (eb / inc * perIncrement) +
    eb * (scoreFin i + depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
  -- The largest inactivity score at the finalized block's state.
  let scoreMaxFin := if altair : .altair ≤ fork then
      ((finalizedState.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0
  -- A key's effective balance before its sync debits on this branch can sit above `ebUp`.
  --
  -- `ebUp` reads its balance after them.
  --
  -- Its inactivity and flag penalties then run at the raised balance, which `rise` does not read.
  --
  -- The seats of the window debit at most `syncDebitMax` in all, so this charges the extra leak.
  let syncDebitMax := depthFin * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope
  let syncLeak := 3 * depthFin * (2 * perIncrement * (2 * syncDebitMax / (inc - 1) + 1) +
    2 * syncDebitMax * (scoreMaxFin + depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat) + 1)
  let partialsR (i : ℕ) := if electra : .pectra ≤ fork then
      (((state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ epoch.toNat + 1).map
          (·.amount.toNat)).sum
    else 0
  let partialsX (i : ℕ) := if electra : .pectra ≤ fork then
      (((finalizedState.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ epoch.toNat + 1).map
          (·.amount.toNat)).sum
    else 0
  -- The rates are read at a computed envelope of the key's effective balance on any branch.
  --
  -- That is at least its effective balance here and at the finalized block's state.
  --
  -- A key can rise by its leak at the cap and its partials, then by a band, up to its cap.
  let finEB (i : ℕ) := balanceAt finalizedState i
  let ebUp (i : ℕ) :=
    let top := actual i + depthFin * leakAt (cap i) i + (partialsX i - partialsR i) +
      preset.downwardBand + inc - 1
    max (max (effective i) (finEB i)) (min (cap i) (top - top % inc))
  let leak (i : ℕ) := leakAt (ebUp i) i
  let gainRate (i : ℕ) := ebUp i / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  -- A partial due by the next epoch was queued at least `partialDelay` epochs before it.
  --
  -- Within that depth it predates finality and sits in the queue of the finalized block's state.
  let partialDelay := config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  let partialsDue (i : ℕ) := max (partialsX i) (partialsR i)
  -- Deeper than `partialDelay` from the finalized block's state, a key can fall to nothing.
  --
  -- A partial requested after that state can then be paid on a branch and sit in no queue read
  -- here, so its whole balance is charged.
  let actualFin (i : ℕ) := ((finalizedState.balances.data[i]?).map (·.toNat)).getD 0
  -- A key whose exit was set by the finalized block's state can be swept here and slashed there.
  --
  -- There it keeps at least its finalized effective balance or its rounded finalized balance.
  let exitBeforeFin (i : ℕ) := (validator i).any fun v =>
    decide (v.exitEpoch.toNat ≤ (getCurrentEpoch finalizedState).toNat)
  let bF (i : ℕ) := if exitBeforeFin i then max (finEB i) (actualFin i - actualFin i % inc) else 0
  let capFin (i : ℕ) := ((finalizedState.validators.data[i]?).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).getD 0
  let base0 (i : ℕ) := min (actualFin i) (capFin i)
  let carry (i : ℕ) := leakAt (finEB i - actualFin i + inc) i + 1
  let floorC (i : ℕ) :=
    let low := base0 i - (carry i +
      depthFin * (leakAt (base0 i + preset.downwardBand + inc) i + gainRate i + 1) +
      partialsDue i)
    if max (finEB i) (base0 i) ≤ low + preset.downwardBand then finEB i
      else min (finEB i) (low - low % inc)
  let fall (i : ℕ) := if depthFin ≤ partialDelay then effective i - floorC i else effective i
  -- Gains compound across the window, so the rise reads the gain at eleven tenths, rounded up.
  --
  -- Three more units per epoch pay the floors of the rates.
  --
  -- At eleven tenths they still cover the two floor units of every epoch.
  let gainScaled (i : ℕ) := (11 * gainRate i + 9) / 10 + 3
  -- A key's rate is low when its gain from the finalized block's state stays below an increment.
  --
  -- Eleven times its gain plus one over the depth must also stay within its bound.
  let lowRate (i : ℕ) : Bool :=
    decide (depthFin * gainScaled i < inc) && decide (11 * depth * (gainRate i + 1) ≤ ebUp i)
  let capFor (i : ℕ) :=
    if lowRate i then cap i else capMax
  -- A key keeps its own path when its gain stays within its bound and partials stay queued.
  --
  -- Its rise is then its rounded balance; otherwise it is its whole headroom.
  let keptArm (i : ℕ) : Bool :=
    decide (depthFin ≤ partialDelay) && decide (11 * depth * (gainRate i + 1) ≤ ebUp i)
  let rise (i : ℕ) :=
    let high := actual i + depthFin * (gainScaled i + leak i) + (partialsX i - partialsR i)
    -- Deeper than `partialDelay`, the call's branch can pay partials that neither queue holds.
    --
    -- So the rise is the key's whole headroom.
    --
    -- It is too once eleven times the gain plus one over the depth exceeds that bound.
    if keptArm i then
      let kept := high + preset.downwardBand
      min (capFor i) (min (kept - kept % inc) (max (finEB i) (high - high % inc))) - effective i
    else capFor i - effective i
  let period := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat
  let due := if electra : .pectra ≤ fork then
      (state.pendingConsolidations electra).data.toList.filter fun c =>
        ((validator c.sourceIndex.toNat).map fun v =>
          v.slashed || decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
    else []
  let depositRecipients := preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
  let creditedKeys := depth * slots + (depth / period + 2) * preset.SYNC_COMMITTEE_SIZE.toNat +
    depth * depositRecipients + due.length
  let consolidationsX := if depthFin ≤ partialDelay then
      (if electra : .pectra ≤ fork then
        ((((finalizedState.pendingConsolidations electra).data.toList.filterMap fun c =>
          finalizedState.validators.data[c.sourceIndex.toNat]?).filter fun v =>
            !v.slashed && decide (v.withdrawableEpoch.toNat ≤ epoch.toNat + 1)).map fun v =>
              (withdrawalMaxEffectiveBalance preset fork v).toNat).sum
      else 0)
    else 0
  -- Each entry of `consolidationsX` can raise its target by one more increment.
  --
  -- That increment earns `unitGain`, three times.
  let consolidationsXCount := if depthFin ≤ partialDelay then
      (if electra : .pectra ≤ fork then
        (((finalizedState.pendingConsolidations electra).data.toList.filterMap fun c =>
          finalizedState.validators.data[c.sourceIndex.toNat]?).filter fun v =>
            !v.slashed && decide (v.withdrawableEpoch.toNat ≤ epoch.toNat + 1)).length
      else 0)
    else 0
  -- Each sync seat of the window debits at most its envelope on each branch.
  --
  -- A key whose sync debits can lower its effective balance has debits of at least an increment.
  --
  -- So there are at most the total seat debits over `inc - 1` such keys.
  let seatExcess := 2 * (depthFin * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope) /
    (inc - 1)
  -- The window's proposer rewards are read at every key that can attest in it.
  --
  -- Such a key exits no earlier than the finalized epoch.
  --
  -- It can activate on the other branch while it is still pending here.
  --
  -- Its effective balance on either branch is at most its effective balance here plus its rise.
  let proposerBase := ∑ i ∈ positions with (validator i).any (fun v =>
      decide (finalized ≤ v.exitEpoch.toNat)),
    max (effective i + rise i) (bF i) / inc * perIncrement
  -- Each key the call's branch credits or debits can move by a rounding step and a band.
  --
  -- The keys are the window's proposers and deposit recipients.
  --
  -- They also hold the sync seats of each period from the finalized epoch to the next epoch.
  --
  -- Each period crossing adds one more set of seats.
  let roundedKeys := depth * slots + depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
    preset.SYNC_COMMITTEE_SIZE.toNat *
      (((epoch.toNat + 1) / period - (getCurrentEpoch finalizedState).toNat / period + 1) +
        depth / period)
  -- The other branch's credits can raise its attesters' effective balances above that read.
  --
  -- Each increment they add is counted, with one rounding step per credited key or seat key.
  --
  -- Each deposit the window can apply to a new key counts at the largest effective balance.
  --
  -- A key this branch debits keeps one more rounding step, and the leak its sync debits induce.
  let attesterExcess := (depositCarry + depthFin * depositChurn + consolidationsX +
      depth * proposerBase + depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope) /
        inc +
    creditedKeys + seatExcess +
    depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * (capMax / inc) +
    roundedKeys + syncLeak / inc
  -- This follows `syncProposerReward` on natural numbers, at the envelope.
  --
  -- It is a bound on the reward, not a read.
  let syncProposer := slots * preset.SYNC_COMMITTEE_SIZE.toNat *
    (syncEnvelope * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
  let proposerCredit := proposerBase + attesterExcess * perIncrement + syncProposer
  -- The slashable keys of the window that the quorum reserve's whistleblower term leaves out.
  --
  -- Those are keys active from the next epoch, or withdrawable after the finalized epoch.
  --
  -- With that term, the allowance covers one slashing credit of each key, and the rises.
  let whistleblowerExtra := ((∑ i ∈ positions with (validator i).any (fun v =>
      v.activationEpoch.toNat = epoch.toNat + 1 ||
        (decide (finalized < v.withdrawableEpoch.toNat) &&
          decide (v.withdrawableEpoch.toNat ≤ epoch.toNat))), max (effective i) (bF i)) +
      ∑ i ∈ positions with current i = true, rise i) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  -- Slashings on the call's branch after the finalized epoch, which the other branch can lack.
  --
  -- A slashing sets the withdrawable epoch at least `EPOCHS_PER_SLASHINGS_VECTOR` later.
  --
  -- Its effective balance can exceed what it is here by its rise, or by sync debits it had here.
  let whistleblowerR := ((∑ i ∈ positions with slashed i = true ∧ recentSlashing i = true,
      (effective i + rise i)) + seatExcess * inc) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let slashedR := (positions.filter fun i => slashed i = true ∧ recentSlashing i = true).card
  let gainRateMax := capMax / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  let late := if tight then 0 else
    ∑ i ∈ positions with (validator i).any (fun v =>
      decide (v.activationEligibilityEpoch.toNat ≤ epoch.toNat) &&
        decide (finalized + preset.MAX_SEED_LOOKAHEAD.toNat < v.activationEpoch.toNat)),
      (3 * effective i + rise i)
  -- Every seat of every sync committee in the window counts, at the seat's envelope.
  --
  -- The window can include the call's previous period, which its state does not store.
  --
  -- Both branches can credit and debit those seats after the split, so they count twice there.
  --
  -- From the finalized block's state to the split the seats are shared, and they count once more.
  let syncSeats := 3 * ((depth + depthFin) * slots * preset.SYNC_COMMITTEE_SIZE.toNat *
    syncEnvelope)
  -- The credits are scaled by eleven tenths, rounded up, for the gains they compound.
  --
  -- The band of each credited key is not scaled.
  let credits :=
    (11 * (depth * proposerCredit + depositCarry + depthFin * depositChurn +
      whistleblowerExtra) + 9) / 10 +
      creditedKeys * preset.upwardBand
  -- A key slashed on this branch drops by at most one increment of effective balance.
  --
  -- Its leak over the window is then read at the dropped balance, so the drop's leak is charged.
  let slashCharge := inc + depthFin * (2 * (2 * perIncrement) +
    2 * inc * (scoreMaxFin + depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat) + 1)
  let unitGain := depth * (perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
    WEIGHT_DENOMINATOR.toNat + 2)
  -- A key slashed on this branch can also take one more increment, which earns `unitGain`.
  --
  -- The rounding is weighted 3 exactly once, by the `3 *` of this branch term.
  let branchR := 3 * (whistleblowerR + slashCharge * slashedR + unitGain * slashedR +
    depth * proposerCredit + (inc + preset.downwardBand - 1) * roundedKeys)
  -- A key previous-epoch-only in a counting state weighs three times there, at its balance there.
  --
  -- `exiting` reads it here, so its rise since the split also weighs three times.
  --
  -- That rise is its gains, the call's branch's penalties and the other branch's credits.
  --
  -- A credit raises an effective balance by at most itself plus the upward band.
  let exitingRise := ∑ i ∈ positions with (before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true,
    rise i
  -- An exiting key can still be credited as a proposer or as the target of a due consolidation.
  --
  -- `credits` charges those credits once at eleven tenths and their bands once.
  --
  -- These charge them twice more, also at eleven tenths, rounded up.
  let exitingCredits := (22 * (depth * proposerCredit) + 9) / 10
  -- A lower bound on a key's effective balance on another branch, up to the counting state.
  --
  -- It starts at the finalized block's state, which lies on every branch, and at most this one's.
  --
  -- The start is also at most the finalized block's balance.
  --
  -- The carry, the leak over the depth, partials, the band and one increment of rounding are drops.
  --
  -- A partial in that state's own epoch can be paid before it, but leaves the activation balance.
  let drop (i : ℕ) := carry i + depthFin * (leakAt (base0 i + inc) i + 1) +
    preset.downwardBand + inc
  let lowEB (i : ℕ) := min (min (min (effective i) (finEB i)) (actualFin i) - partialsDue i)
    preset.MIN_ACTIVATION_BALANCE.toNat - drop i
  -- A key can exit on the other branch with an effective balance below the ejection balance.
  --
  -- Such a key uses little churn, so each one whose `lowEB` falls below that bound is counted.
  --
  -- Every key not yet withdrawable after the finalized epoch counts.
  --
  -- Its exit here is not its exit there.
  --
  -- A key not active by this epoch here, or created on the other branch, activates there only
  -- with at least the activation balance, which it keeps until then.
  --
  -- No lemma here proves yet that it keeps at least `newKeyFloor` from its activation, less its
  -- own sync-seat debits and pending partial payments.
  let newKeyFloor := 2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
    preset.MAX_EFFECTIVE_BALANCE.toNat / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - inc
  let exitFloor := max 1 (min (config.EJECTION_BALANCE.toNat - inc) newKeyFloor)
  let newKeySlack := newKeyFloor - exitFloor
  let lowKeys := (positions.filter fun i =>
    (validator i).any (fun v => decide (finalized < v.withdrawableEpoch.toNat) &&
      decide (v.activationEpoch.toNat ≤ epoch.toNat)) ∧
      lowEB i < newKeyFloor).card
  -- Outside the tight window, keys can start to exit on the other branch.
  --
  -- The queues admit at most this many keys at the ejection balance less an increment each.
  --
  -- The `+ 2` counts one key at each end of the window that the churn covers only in part.
  --
  -- `lowKeys` adds every key whose effective balance can fall below that.
  --
  -- After an exit starts, the key's proposer and due-consolidation credits are in `exitingCredits`.
  --
  -- Its whistleblower credits are in `reserveW`, `flagged` and the drift's slashed keys.
  let newKeySeats := depthFin * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope /
    max 1 newKeySlack
  let queueKeys := (depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry) /
    exitFloor + 2 + lowKeys + newKeySeats
  -- The largest gain rate of one key, its gain rate at the largest effective balance.
  let exitingCount := (positions.filter fun i => (before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v =>
        decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true).card
  let exitingBands := 2 * (exitingCount + queueKeys) * preset.upwardBand
  let queueRise := if tight then 0 else
    3 * queueKeys * (preset.upwardBand + depth * gainRateMax)
  -- A key slashed on another branch credits its whistleblower, the block's proposer.
  --
  -- A key still active there is meant to pay three times that reward from its own balance.
  --
  -- A key that has exited there by then has no such balance in the count, so it is charged here.
  --
  -- Those are the keys whose exit the call reads.
  --
  -- Outside the tight window, they include the keys that the queues let exit on the other branch.
  let exitedSlashable := ∑ i ∈ positions with slashed i = false ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true ∧
      (validator i).any (fun v => decide (finalized < v.withdrawableEpoch.toNat)),
    max (effective i + rise i) (bF i)
  let reserveW := 3 * (exitedSlashable + (if tight then 0 else
      depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry +
        queueKeys * (preset.upwardBand + depth * gainRateMax))) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  -- A key active there is meant to pay for its reward unless its effective balance can be low.
  --
  -- `lowEB` bounds that balance from below, before the slashing penalty and sync-seat debits.
  --
  -- A key that fails the test is charged its reward three times.
  let slashable (i : ℕ) := slashed i = false ∧ (validator i).any (fun v =>
    decide (v.activationEpoch.toNat ≤ epoch.toNat + 1) &&
      decide (finalized < v.withdrawableEpoch.toNat))
  -- The reward is read at `ebUp`.
  --
  -- The slashing's loss is read at the finalized balance plus an increment, if that is larger.
  let flagged := ∑ i ∈ positions with slashable i ∧
      2 * (lowEB i - max (ebUp i) (max (finEB i) (base0 i) + inc) /
        p.MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
        3 * (ebUp i / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat),
    3 * (ebUp i / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
  -- No key's sync-seat debits are bounded from what the call reads, so they are charged together.
  --
  -- Twice the debits of every seat in the window covers what they take from the test.
  let seatShortfall := 2 * (depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope)
  let exitedR := ∑ i ∈ positions with (validator i).any (fun v =>
      decide (finalized + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ v.exitEpoch.toNat) &&
        decide (v.exitEpoch.toNat + 1 ≤ epoch.toNat)),
    (effective i + rise i)
  let consolidationGain := consolidationsX / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  -- A key whose only flows are seat debits pays a unit too.
  --
  -- Its seats are those of the call's branch beyond the two shared at the split.
  --
  -- They are also those of the shared segment.
  let seatUnits := (depth / period + (depthFin / period + 2)) * preset.SYNC_COMMITTEE_SIZE.toNat
  let creditUnits := (creditedKeys + seatUnits + 2 * (exitingCount + queueKeys)) * unitGain
  let otherCredits := 3 * (2 * ((∑ i ∈ positions,
          max (max (ebUp i) (effective i + rise i)) (bF i)) +
        (11 * (depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax +
          consolidationsX + depth * proposerCredit +
          -- The proposer share of the shared segment's seat rewards.
          --
          -- Those are the rewards of keys that exited before the finalized state.
          depthFin * syncProposer +
          -- C's seat rewards.
          depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope +
          -- The shared segment's and R's seat debits.
          depthFin * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope) + 9) / 10 +
        creditedKeys * inc +
        -- The bands of the keys that hold a seat on the shared segment or on R's run.
        (depthFin / period + 2) * preset.SYNC_COMMITTEE_SIZE.toNat *
          (inc + preset.downwardBand) +
        -- The units of the keys whose only flows are seat debits, and the leak that those induce.
        creditUnits + syncLeak +
        -- The units and the leak of the keys that only a consolidation or a slashing on R moves.
        unitGain * (consolidationsXCount + slashedR) +
        slashedR * (depthFin * (2 * perIncrement +
          inc * (scoreMaxFin + depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
            (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat) + 1))) /
          -- The credits include the keys' own whistleblower credits, so two quotient steps go.
          (p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 2) +
      -- C's seat flows, and R's and the shared segment's seat debits.
      (depth + depthFin) * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope +
        depth * syncProposer)
  let otherGain := otherCredits / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  let creditGain :=
    (33 * depth * consolidationGain + 11 * depth * otherGain +
      30 * depth * (perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat + 1) + 9) / 10 +
      (if 11 * depth * (gainRateMax + 1) ≤ capMax then 0
        else depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax)
  let pendingR := if tight then 0 else
    ∑ i ∈ positions with (validator i).any (fun v =>
      decide (epoch.toNat < v.activationEligibilityEpoch.toNat) &&
        v.activationEpoch == FAR_FUTURE_EPOCH), (effective i + rise i)
  { quorum := quorumReserve config state ancestor, exiting, queues, queueDep, queueExit, credits,
    branchR, late, syncSeats, rise, fall, positions, current, exitingRise, exitingCredits,
    queueRise, reserveW, flagged, seatShortfall, consolidationsX, exitedR, depth, syncProposer,
    proposerCredit, exitingBands, pendingR, creditGain, creditUnits, syncLeak, unitGain,
    consolidationsXCount, exitBeforeFin, bF, perIncrement, depthFin, scoreMaxFin, slashCharge,
    consolidationGain,
    otherGain, keptArm,
    creditLow := (33 * depth * consolidationGain + 11 * depth * otherGain +
      30 * depth * (perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat + 1) + 9) / 10,
    creditCap := if 11 * depth * (gainRateMax + 1) ≤ capMax then 0
      else depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax,
    gainHigh := !decide (11 * depth * (gainRateMax + 1) ≤ capMax),
    pendingRB := fun i => (validator i).any (fun v =>
      decide (epoch.toNat < v.activationEligibilityEpoch.toNat) &&
        v.activationEpoch == FAR_FUTURE_EPOCH),
    joining := ∑ i ∈ positions with current i = false ∧ upcoming i = true, effective i,
    joinRise := ∑ i ∈ positions with current i = false ∧ upcoming i = true, rise i,
    exitingB := fun i => decide ((before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true),
    lateB := fun i => (validator i).any (fun v =>
      decide (v.activationEligibilityEpoch.toNat ≤ epoch.toNat) &&
        decide (finalized + preset.MAX_SEED_LOOKAHEAD.toNat < v.activationEpoch.toNat)),
    exitedRB := fun i => (validator i).any (fun v =>
      decide (finalized + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ v.exitEpoch.toNat) &&
        decide (v.exitEpoch.toNat + 1 ≤ epoch.toNat)),
    slashedR,
    slashedRB := fun i => decide (slashed i = true ∧ recentSlashing i = true),
    tight, queueKeys,
    queueWindow := depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry,
    gainRateMax, exitFloor, lowKeys,
    lowB := fun i => decide ((validator i).any (fun v =>
      decide (finalized < v.withdrawableEpoch.toNat) &&
        decide (v.activationEpoch.toNat ≤ epoch.toNat)) ∧ lowEB i < newKeyFloor),
    lowEB, newKeySeats, newKeySlack, newKeyFloor, leakAt, ebUp, leak, partialsDue, base0, gainRate,
    floorC, drop }
/-- The copy is faithful: the named terms sum to `pinReserve`. -/
theorem pinReserve_eq_total (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    pinReserve config state ancestor finalizedState =
      (pinTerms config state ancestor finalizedState).total := rfl

/-- `creditGain` is its part for compounding flows and its part for new keys past the cap. -/
private theorem creditGain_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).creditGain =
      (pinTerms config state ancestor finalizedState).creditLow +
        (pinTerms config state ancestor finalizedState).creditCap := rfl

/-- `exitedRB` is the filter of `exitedR`: the keys whose exit started on this branch after the split.-/
theorem exitedR_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).exitedR =
      ∑ i ∈ (pinTerms config state ancestor finalizedState).positions with
        (pinTerms config state ancestor finalizedState).exitedRB i = true,
        (balanceAt state i + (pinTerms config state ancestor finalizedState).rise i) := rfl

/-- `slashedRB` is the filter of `slashedR`.

They are the keys slashed on this branch after the finalized epoch. -/
theorem slashedR_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).slashedR =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).slashedRB i = true).card := rfl

/-- The copy splits `queues` into its deposit part and its exit and consolidation part. -/
theorem queues_split (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queues =
      (pinTerms config state ancestor finalizedState).queueDep +
        (pinTerms config state ancestor finalizedState).queueExit := rfl

/-- `queueRise` charges each key the queues let exit, at a band and the largest gain rate. -/
theorem queueRise_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueRise =
      if (pinTerms config state ancestor finalizedState).tight then 0 else
        3 * (pinTerms config state ancestor finalizedState).queueKeys *
          (preset.upwardBand + (pinTerms config state ancestor finalizedState).depth *
            (pinTerms config state ancestor finalizedState).gainRateMax) := rfl

/-- `queueKeys` counts the window's churn by `exitFloor`, the ends, the low keys and new keys. -/
theorem queueKeys_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueKeys =
      (pinTerms config state ancestor finalizedState).queueWindow /
          (pinTerms config state ancestor finalizedState).exitFloor + 2 +
        (pinTerms config state ancestor finalizedState).lowKeys +
        (pinTerms config state ancestor finalizedState).newKeySeats := rfl

/-- A key's fall is its effective balance less `floorC` within the delay, and all of it beyond. -/
theorem fall_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork)
    (i : ℕ) :
    (pinTerms config state ancestor finalizedState).fall i =
      if (getCurrentEpoch state).toNat + 2 - (getCurrentEpoch finalizedState).toNat ≤
          config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat then
        balanceAt state i - (pinTerms config state ancestor finalizedState).floorC i
      else balanceAt state i := rfl

/-- `lowEB` takes the drops from the least of its starting balances, capped at activation. -/
theorem lowEB_unfold (config : Config) (state ancestor finalizedState : BeaconState preset fork)
    (i : ℕ) :
    (pinTerms config state ancestor finalizedState).lowEB i =
      min (min (min (balanceAt state i) (balanceAt finalizedState i))
            (((finalizedState.balances.data[i]?).map (·.toNat)).getD 0) -
          (pinTerms config state ancestor finalizedState).partialsDue i)
        preset.MIN_ACTIVATION_BALANCE.toNat -
        (pinTerms config state ancestor finalizedState).drop i := rfl

/-- `lowB` is the filter of `lowKeys`. -/
theorem lowKeys_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).lowKeys =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).lowB i = true).card := rfl

/-! ## D-1's setting -/

/-- D-1's setting, as D-2 supplies it (the call's own-epoch runs are left out: they feed
`quorumReserve`, which this check uses only for `joining`). -/
structure Setting (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset)
    (split fin pulled anc counted : BeaconState preset fork) (V : Finset ValidatorIndex) : Prop where
  genesis : Genesis config checks g
  toFin : Nonempty (Run config checks g ⟨fork, fin⟩)
  fromFin : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
  toPulled : Nonempty (Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
  toCounted : Nonempty (Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
  early : fork < .glamsterdam
  fulu : .fusaka ≤ fork
  bands : preset.IncrementWithinUpwardBand
  caps : CapOrder preset
  window : preset.SeedLookaheadAtLeastThree
  parameters : DirectSafety.Parameters preset
  aligned : MaxEffectiveBalancesAligned preset
  twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  shallow : (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  pulledTotal : ∃ t, getTotalActiveBalance pulled = .ok t
  room : 2 ^ 32 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat
  below : preset.downwardBand < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  facts : PinPresetFacts preset
  guard : DirectSafety.Apriori.aprioriGuardAt config ⟨fork, fin⟩ (getCurrentEpoch pulled).toNat
  finalized : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch split
  called : getCurrentEpoch split ≤ getCurrentEpoch pulled
  later : getCurrentEpoch pulled ≤ getCurrentEpoch counted
  near : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1
  voting : ∀ v ∈ V, v ∈ activeVoters pulled ∧ (slashedFlagAt counted v.toNat).getD false = false

/-! ## Flows of the two branches -/

/-- The deposits applied to the key on R's branch, over the replayed events of the run from the
split. -/
def credDepR (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .deposits)).map (keyCredit v)).sum

/-- The consolidation credits to the key over the replayed events of a run.

It is the quantity that `Run.consolidation_credits_le_X_targets` bounds, summed over targets. -/
def consAmt (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .consolidations)).map (keyCredit v)).sum

/-! ### The C-side credits of a key, read from the run (prover D)

They are read from the run itself, as E's `riseQ` is.

A block step's `.rewards` events are its proposer's credits.

A slot step's `.rewards` events are the epoch's flag rewards, so a slot step counts only the sources
named below.

Sync events are in `syncF` with the seats. -/

/-- Proposer and due-consolidation credits to the key on C's branch since the split.

The rounding slack of a credited key is `bandC`, once for each key.

The consolidation bands are not here: `bud_consolidations` charges them. -/
def propC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations)) v high tail).1

/-- Proposer credits to the key on C's branch since the split, without the consolidation credits.

A credited stake compounds by at most a tenth.

The stubs charge an exact tenth of the keys' total, at ten times their terms.

The consolidation credits are under `consolidationsX`, so their compounding is not charged here. -/
def propN {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v high tail).1

/-- Proposer and deposit credits to the key on C's branch since the split.

They are `credC` without its consolidation credits.

A credited stake compounds by at most a tenth.

The stubs charge an exact tenth of the keys' total, at ten times their terms. -/
def credN {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards)) (fun s => decide (s = .deposits)) v high tail).1

/-- The deposits credited to a key by events whose state before them does not hold it slashed.

A slashed key's whistleblower reward reads its effective balance at the slashing.

Of `credN`'s credits, only these deposits and its proposer credits can raise that balance.

This holds because a slashed key proposes no block. -/
private def depPre (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter fun e => e.source = .deposits ∧
      ¬ (slashedFlagAt e.before.state v = some true)).map (keyCredit v)).sum

/-- Non-attestation credits to the key on C's branch since the split, whistleblower and sync credits
excluded: proposer, deposits applied and consolidations.

The rounding slack of a credited key is `bandC`, once for each key. -/
def credC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations ∨ s = .deposits)) v high tail).1

/-- The block credits to the key on R's branch since the split: proposer and whistleblower credits.

A slot step's credits are not here: `fall` reads the epoch rewards at its gain rate.

A key that gains in a block step or by a deposit moves by one more rounding step.

The band comes with the step.

A block step that nets the key no credit cannot push its effective balance up.

That step is `inc + downwardBand - 1`, the one that `branchR` charges for each of its keys. -/
def credR {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s ≠ .deposits ∧ s ≠ .sync ∧ s ≠ .consolidations))
    (fun _ => false) v high tail).1 +
    if netScan v high tail = 0 ∧ (creditScan (fun _ => false) (fun s => decide (s = .deposits))
        v high tail).1 = 0 then 0
    else preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1

/-- Whistleblower credits to the key on C's branch since the split.

A whistleblower credit lands in the block of the proposer's own slot.

The rounding slack of a credited key is `bandC`, once for each key.

A slot step records only debits for a slashing. -/
def whistC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .slashings)) (fun _ => false) v high tail).1

/-- The entries of X's queue of pending consolidations that name a target in `T` and apply by
`high + 1`.

It is the set of `Run.consolidation_credits_le_X_targets`, counted instead of summed. -/
def dueAt (X : BeaconState preset fork) (high : ℕ) (T : Finset ValidatorIndex) : ℕ :=
  if electra : .pectra ≤ fork then
    ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
        !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).length
  else 0

/-- The debit that one balance event takes from the key at position `i`. -/
def keyDebit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.before i - actualBalanceAt e.after i

/-- The sync-seat movement of the key over the replayed events of one run.

It is the key's credits and debits of the sync aggregates: a seat's debit, a seat's reward, and the
proposer's share of it.

The caller adds it over the two runs from the split, since both branches credit and debit seats. -/
def syncF (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .sync)).map (keyCredit v)).sum +
    ((events.filter (·.source = .sync)).map (keyDebit v)).sum

/-- One increment for a key slashed on R's branch after the finalized epoch.

The effective-balance drop of R's initial penalty is at most one increment, by `slashBand`.

`branchR` charges each such key `slashCharge`, at least one increment. -/
def slashR (t : PinTerms preset) (i : ℕ) : ℕ :=
  if t.slashedRB i = true then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0

/-- The gross credits to the key in the block steps of a run, from rewards, slashings and sync.

A block step counts the credits of its events from those sources, whatever the step takes back. -/
private def grossScan (v high : ℕ) {x y : ForkedBeaconState preset} (tail : Run config checks x y) :
    ℕ :=
  (creditScan (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) v
    high tail).1

/-- The gross credits of a run, after one more step. -/
private theorem grossScan_snoc (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m y) :
    grossScan v high (pre.snoc step) = if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      grossScan v high pre + stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) v step
      else grossScan v high pre := by
  unfold grossScan
  exact creditScan_snoc_fst _ _ v high pre step

/-- The gross credits of a run add over `append`. -/
private theorem grossScan_append (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) :
    grossScan v high (pre.append post) = grossScan v high pre + grossScan v high post := by
  unfold grossScan
  exact creditScan_append _ _ v high pre post

/-- The rounding slack of a key with any C-side credit, once for each key.

The credits are the gross credits of its block steps, and an applied deposit.

A proposer reward, a whistleblower reward and a sync reward are block credits.

A consolidation credit is not here: `bud_consolidations` charges its band for each entry.

`credits` charges `upwardBand` for each credited key. -/
def bandC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  if 0 < grossScan v high tail +
      (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail).1 then
    preset.upwardBand else 0

/-- The credits of events from two apart sources are the credits of each source. -/
private theorem sum_filter_or (L : List (BalanceEvent preset)) (p q : BalanceSource → Bool)
    (apart : ∀ s, ¬ (p s = true ∧ q s = true)) (f : BalanceEvent preset → ℕ) :
    ((L.filter fun e => p e.source || q e.source).map f).sum =
      ((L.filter fun e => p e.source).map f).sum + ((L.filter fun e => q e.source).map f).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    by_cases hp : p a.source = true
    · have hq : q a.source = false := by
        cases h : q a.source
        · rfl
        · exact absurd ⟨hp, h⟩ (apart a.source)
      simp [hp, hq, ih]; omega
    · by_cases hq : q a.source = true
      · simp [hp, hq, ih]; omega
      · simp [hp, hq, ih]

/-- The credits of a run that a scan reads add over two apart sets of sources.

The block sources of the scan and the slot sources are each the union of two apart sources. -/
private theorem creditScan_or (blockP slotP b₁ b₂ s₁ s₂ : BalanceSource → Bool)
    (hb : ∀ s, blockP s = (b₁ s || b₂ s)) (hs : ∀ s, slotP s = (s₁ s || s₂ s))
    (apartB : ∀ s, ¬ (b₁ s = true ∧ b₂ s = true)) (apartS : ∀ s, ¬ (s₁ s = true ∧ s₂ s = true))
    (v high : ℕ) {x y : ForkedBeaconState preset} (tail : Run config checks x y) :
    (creditScan blockP slotP v high tail).1 =
      (creditScan b₁ s₁ v high tail).1 + (creditScan b₂ s₂ v high tail).1 := by
  obtain rfl : blockP = fun s => b₁ s || b₂ s := funext hb
  obtain rfl : slotP = fun s => s₁ s || s₂ s := funext hs
  induction tail with
  | nil => rfl
  | @snoc middle last pre step ih =>
    have split : stepCredit (fun s => b₁ s || b₂ s) (fun s => s₁ s || s₂ s) v step =
        stepCredit b₁ s₁ v step + stepCredit b₂ s₂ v step := by
      cases step with
      | slot ok => simp only [stepCredit]; exact sum_filter_or _ _ _ apartS _
      | block engine signed due ok => simp only [stepCredit]; exact sum_filter_or _ _ _ apartB _
    rw [creditScan_snoc_fst, creditScan_snoc_fst, creditScan_snoc_fst, split]
    split_ifs <;> omega

/-- The credits of a key on C's branch are its proposer credits and the deposits it is credited. -/
private theorem credN_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    credN tail high v = propN tail high v +
      (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail).1 :=
  creditScan_or _ _ (fun s => decide (s = .rewards)) (fun _ => false) (fun _ => false)
    (fun s => decide (s = .deposits)) (fun s => by cases s <;> decide)
    (fun s => by cases s <;> decide)
    (fun s h => by simp at h) (fun s h => by simp at h) v high tail

/-- The credits of a key with the consolidations are its `credN` and its consolidation credits. -/
private theorem credC_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    credC tail high v = credN tail high v +
      (creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v high tail).1 :=
  creditScan_or _ _ (fun s => decide (s = .rewards)) (fun s => decide (s = .consolidations))
    (fun s => decide (s = .deposits)) (fun s => decide (s = .consolidations))
    (fun s => by cases s <;> decide) (fun s => by cases s <;> decide)
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide))
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide)) v high tail

/-- The proposer credits with the consolidations are `propN` and the consolidation credits. -/
private theorem propC_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    propC tail high v = propN tail high v +
      (creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v high tail).1 :=
  creditScan_or _ _ (fun s => decide (s = .rewards)) (fun s => decide (s = .consolidations))
    (fun _ => false) (fun s => decide (s = .consolidations))
    (fun s => by cases s <;> decide) (fun s => by cases s <;> decide)
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide))
    (fun s h => by simp at h) v high tail

/-- The gain of `C` credited gwei over `depth` epochs, at the reward rate `P`.

The credits count in whole increments rounded up, and each epoch's gain is rounded down. -/
private def gainOn (preset : Preset) (depth P C : ℕ) : ℕ :=
  depth * ((((C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) / WEIGHT_DENOMINATOR.toNat)

/-- The rounding slack of a key whose balance on R's branch took a sync debit that `high` omits.

It is the step of `credR`, one increment and the downward band less one.

`branchR` charges that step for each of its keys. -/
def bandR (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  if 0 < ((events.filter (·.source = .sync)).map (keyDebit v)).sum then
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0

/-- The sync credits to the key over the replayed events of one run. -/
def syncCr (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  (events.map (syncCredit v)).sum

/-- The sync debits of the key over the replayed events of one run. -/
def syncD (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  (events.map (syncDebit v)).sum

/-- A whistleblower's share of an amount at eleven tenths of three, rounded up.

It is `⌈33·x/(10·WRQ)⌉`, with the whistleblower quotient of the fork. -/
def wShare (preset : Preset) (fork : Fork) (x : ℕ) : ℕ :=
  (33 * x + 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
    (10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)

/-- The band of each due consolidation entry of the state `X` that targets the key. -/
def bandX (X : BeaconState preset fork) (high v : ℕ) : ℕ :=
  preset.upwardBand * dueAt X high {UInt64.ofNat v}

/-- The flag reward of one increment over one epoch, at the pin's rate. -/
private def flagRate (t : PinTerms preset) : ℕ :=
  t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat

/-- The leak of one increment over the window, at the largest score of the finalized state.

It is the leak part of `slashCharge`, read at one increment.

`slashCharge` covers it and the flag gain of two windows. -/
private def slashLeak (config : Config) (fork : Fork) (t : PinTerms preset) : ℕ :=
  t.depthFin * (2 * t.perIncrement +
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (t.scoreMaxFin + t.depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) + 1)

/-- The initial slashing penalty of a key slashed on R's branch after the split, at the cap. -/
private def slashW (t : PinTerms preset) (i : ℕ) : ℕ :=
  if t.slashedRB i = true then
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  else 0

/-- The leak a key's sync debits on R's run from the finalized block induce above `ebUp`.

It is the leak at the largest effective balance on the run, less the leak at `ebUp`. -/
private def inducedR (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : ℕ) : ℕ :=
  t.depthFin * (t.leakAt ((tail.balancePath.map fun z => effectiveAt z i).foldl max 0) i -
    t.leakAt (t.ebUp i) i)

/-- The flows that can raise a key's balance on C above R's base, besides its epoch rewards.

They are its credits on C's branch and its sync debits on R's branch and on the shared segment.

They also include the initial penalty of a slashing on R's branch.

The credits `cred` default to `credC`, which counts the key's deposits.

A key of `K5` passes `propC`, which does not. -/
private def flowCredit (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := credC tailC high i) : ℕ :=
  cred + whistC tailC high i + syncCr eventsC i + syncD events i + syncD eventsF i +
    slashW t i

/-- The gain of a key's flows over the window, at eleven tenths in whole increments.

It is one floor of all the flows; the closure splits it by kind in aggregate.

Its rate is floored once, after the increments, as the gain of the credits is.

A gain-carrying run starts at the split, so the gain runs over at most the shorter window. -/
private def flowGain (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := credC tailC high i) : ℕ :=
  min t.depth t.depthFin * (11 * flowCredit t tailC high eventsC events eventsF i cred /
    (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * t.perIncrement *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat)

/-- The flow gain of a key whose rise is on its kept arm, or that R's registry does not hold.

On the other arm the rise is the key's whole headroom, which holds its gains already.

A key that R's registry does not hold is charged here only in the low regime.

In the high regime `creditCap` charges it up to the cap. -/
private def flowK (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := credC tailC high i) : ℕ :=
  if t.keptArm i = true ∨ (i ∉ t.positions ∧ t.gainHigh = false) then
    flowGain t tailC high eventsC events eventsF i cred
  else 0

/-- One unit of gain for a key with any flow.

A flow can raise the key's effective balance by one more increment than its rewards alone. -/
private def unitK (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := credC tailC high i) : ℕ :=
  if 0 < flowCredit t tailC high eventsC events eventsF i cred then t.unitGain else 0

/-- The terms of a key's rise that the third window adds.

They are its sync debits on the shared segment, its flow gain and its unit.

They also include the leak that its sync debits on R's branch induce.

`bud_sync`, `flow_split`, `bud_units` and `bud_syncLeak` pay them, in that order. -/
private def keyExtra (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (tailC : Run config checks x' y') (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := credC tailC high i) : ℕ :=
  syncD eventsF i + flowK t tailC high eventsC events eventsF i cred +
    unitK t tailC high eventsC events eventsF i cred + inducedR t tail i

/-- A quantity of the sync events, summed over all events with the others at zero. -/
private theorem sum_map_sync (events : List (BalanceEvent preset))
    (k : BalanceEvent preset → ℕ) :
    (events.map fun e => if e.source = .sync then k e else 0).sum =
      ((events.filter (·.source = .sync)).map k).sum := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    by_cases sync : e.source = .sync
    · simp [sync, ih]
    · simp [sync, ih]

/-- The sync debits of a key over a list of events are the debits of its sync events. -/
private theorem sum_syncDebit_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    (events.map (syncDebit v)).sum =
      ((events.filter (·.source = .sync)).map (keyDebit v)).sum :=
  sum_map_sync events (keyDebit v)

/-- The rounding band of a key is the band if the key has a sync debit, and zero otherwise. -/
private theorem bandR_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    bandR events v = if 0 < (events.map (syncDebit v)).sum then
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0 := by
  unfold bandR
  rw [← sum_syncDebit_eq]

/-- A key's credit in an event is at most the event's credit limit. -/
private theorem keyCredit_le_creditLimit (i : ℕ) (e : BalanceEvent preset)
    (bounded : e.credits ≤ e.creditLimit) : keyCredit i e ≤ e.creditLimit := by
  refine le_trans ?_ bounded
  unfold keyCredit
  by_cases within : i < e.after.state.balances.data.size
  · exact Finset.single_le_sum (f := fun j =>
      actualBalanceAt e.after j - actualBalanceAt e.before j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr within)
  · have missing : actualBalanceAt e.after i = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt within)]
    omega

/-- The stages of an epoch replay record no slashing event with a credit limit. -/
private theorem epochReplayAction_slashing_credit {fork : Fork} (k : EpochStage)
    {pre post : BalanceReplay preset fork}
    (held : ∀ e ∈ pre.2, e.source = .slashings → e.creditLimit = 0)
    (ok : epochReplayAction (config := config) (checks := checks) k pre = .ok post) :
    ∀ e ∈ post.2, e.source = .slashings → e.creditLimit = 0 := by
  have carried : ∀ {a : BeaconState preset fork → Except TransitionError (BeaconState preset fork)},
      carryBalance a pre = .ok post → ∀ e ∈ post.2, e.source = .slashings → e.creditLimit = 0 := by
    intro a ok'
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok'
    obtain ⟨_, _, rfl⟩ := ok'
    exact held
  have unchanged : (pure pre : Except TransitionError (BalanceReplay preset fork)) = .ok post →
      ∀ e ∈ post.2, e.source = .slashings → e.creditLimit = 0 := by
    intro ok'
    simp only [pure, Except.pure, Except.ok.injEq] at ok'
    subst ok'
    exact held
  cases k
  case justification =>
    simp only [epochReplayAction] at ok
    exact carried ok
  case inactivity =>
    simp only [epochReplayAction] at ok
    split at ok
    · exact carried ok
    · exact unchanged ok
  case rewards =>
    simp only [epochReplayAction] at ok
    refine replayRewards_induction (config := config)
      (fun p => ∀ e ∈ p.2, e.source = .slashings → e.creditLimit = 0) ?_ ?_ held ok
    · intro pre' post' index reward held' ok'
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok'
      obtain ⟨_, _, _, _, rfl⟩ := ok'
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held' e old source
      · obtain rfl := List.mem_singleton.mp new
        exact absurd source (by simp)
    · intro src pre' post' index penalty pen held' ok'
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok'
      obtain ⟨_, _, _, _, rfl⟩ := ok'
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held' e old source
      · obtain rfl := List.mem_singleton.mp new
        have same : src = .slashings := source
        rcases pen with h | h <;> rw [h] at same <;> cases same
  case registry =>
    simp only [epochReplayAction] at ok
    exact carried ok
  case slashings =>
    simp only [epochReplayAction, recordBalance, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, limited, after, computed, rfl⟩ := ok
    simp only [Prod.mk.injEq] at limited
    obtain ⟨_, _, zero, _⟩ := limited
    intro e member source
    rcases List.mem_append.mp member with old | new
    · exact held e old source
    · obtain rfl := List.mem_singleton.mp new
      exact zero.symm
  case eth1Reset =>
    simp only [epochReplayAction] at ok
    split at ok
    · exact carried ok
    · exact unchanged ok
  case pendingDeposits =>
    simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, rfl⟩ := ok
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held e old source
      · obtain rfl := List.mem_singleton.mp new
        exact absurd source (by simp)
    · exact unchanged ok
  case pendingConsolidations =>
    simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, rfl⟩ := ok
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held e old source
      · obtain rfl := List.mem_singleton.mp new
        exact absurd source (by simp)
    · exact unchanged ok
  all_goals
    simp only [epochReplayAction] at ok
    exact unchanged ok

/-- A slot step records no slashing event with a credit limit. -/
private theorem slot_slashing_credit {m n : ForkedBeaconState preset}
    {ok : advanceSlotAcross config checks m = .ok n} (early : n.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .slashings → e.creditLimit = 0 := by
  intro e member source
  obtain ⟨advanced, cached, crossings, -, -, -, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  have notCrossing : e ∉ crossings := fun inside => by
    have crossing := upgradeBalanceReplay_crossing crossingOk e inside
    rw [crossing] at source
    cases source
  rcases split with ⟨-, rfl⟩ | ⟨middle, updated, recorded, recordOk, -, -, -, shape, -⟩
  · exact absurd member notCrossing
  · rw [shape] at member
    rcases List.mem_append.mp member with inside | inside
    · exact EpochTrace.induction_on
        (fun _ p => ∀ e ∈ p.2, e.source = .slashings → e.creditLimit = 0)
        (epochBalanceReplay_trace recordOk) (fun e member => by simp at member)
        (fun k _ a b ok held => epochReplayAction_slashing_credit k held ok) e inside source
    · exact absurd inside notCrossing

/-- An event of a block step credits a key only from the sources of `credC`, `whistC` and sync.

A deposit event of a block credits nothing from Electra. -/
private theorem block_event_credit {g : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨fork, s⟩) (genesis : Genesis config checks g)
    (early : fork < .glamsterdam) (electra : .pectra ≤ fork) (i : ℕ)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ∀ e ∈ events, keyCredit i e ≤
      (if e.source = .rewards ∨ e.source = .consolidations then keyCredit i e else 0) +
        (if e.source = .slashings then keyCredit i e else 0) + syncCredit i e := by
  intro e member
  obtain ⟨fk, positive⟩ := Step.balanceEvents_credit_sources
    (Step.block engine signed due ok) early (run_justified_separated shared genesis).1
    replayed e member
  have limit := keyCredit_le_creditLimit i e (bounded e member)
  by_cases rc : e.source = .rewards ∨ e.source = .consolidations
  · simp only [rc, ↓reduceIte]
    omega
  by_cases sl : e.source = .slashings
  · simp [sl]
  by_cases sy : e.source = .sync
  · simp [sy, syncCredit, keyCredit]
  have zero : e.creditLimit = 0 := by
    by_contra pos
    rcases positive (Nat.pos_of_ne_zero pos) with h | h | h | h | h
    · exact rc (.inl h)
    · exact sy h
    · exact sl h
    · exact pos (funding_block_events (config := config) (checks := checks) early engine
        signed.message (Step.balanceEvents_block early replayed) e member h
        (Nat.le_trans electra fk))
    · exact rc (.inr h)
  simp only [rc, sl, ↓reduceIte]
  omega

/-- An event of a slot step, but for the epoch rewards, credits a key only from `credC` and sync. -/
private theorem slot_event_credit {g m n : ForkedBeaconState preset}
    {ok : advanceSlotAcross config checks m = .ok n}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (early : n.fork < .glamsterdam) (i : ℕ) {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ∀ e ∈ events, e.source ≠ .rewards → keyCredit i e ≤
      (if e.source = .consolidations ∨ e.source = .deposits then keyCredit i e else 0) +
        syncCredit i e := by
  intro e member notRewards
  obtain ⟨-, positive⟩ := Step.balanceEvents_credit_sources (Step.slot ok) early
    (run_justified_separated shared genesis).1 replayed e member
  have limit := keyCredit_le_creditLimit i e (bounded e member)
  by_cases cd : e.source = .consolidations ∨ e.source = .deposits
  · simp [cd]
  by_cases sy : e.source = .sync
  · simp [sy, syncCredit, keyCredit]
  have zero : e.creditLimit = 0 := by
    by_contra pos
    rcases positive (Nat.pos_of_ne_zero pos) with h | h | h | h | h
    · exact notRewards h
    · exact sy h
    · exact pos (slot_slashing_credit early replayed e member h)
    · exact cd (.inr h)
    · exact cd (.inl h)
  simp only [cd, ↓reduceIte]
  omega

/-- A bound for each selected event gives the bound for the sums of the credits that it splits. -/
private theorem sum_credits_split (events : List (BalanceEvent preset))
    (f g : BalanceEvent preset → ℕ) (r p q : BalanceSource → Bool)
    (each : ∀ e ∈ events, r e.source = true →
      f e ≤ (if p e.source = true then f e else 0) + (if q e.source = true then f e else 0) +
        g e) :
    ((events.filter (r ·.source)).map f).sum ≤ ((events.filter (p ·.source)).map f).sum +
      ((events.filter (q ·.source)).map f).sum + (events.map g).sum := by
  have ite (p : BalanceSource → Bool) : ((events.filter (p ·.source)).map f).sum =
      (events.map fun e => if p e.source = true then f e else 0).sum := by
    rw [List.sum_map_ite (fun e : BalanceEvent preset => p e.source = true) f (fun _ => 0)]
    simp
  rw [ite, ite, ite, ← List.sum_map_add, ← List.sum_map_add]
  refine List.sum_le_sum fun e member => ?_
  by_cases hr : r e.source = true
  · simp only [hr, ↓reduceIte]
    exact each e member hr
  · simp only [hr]
    exact Nat.zero_le _

/-- A filter that selects no event sums to zero. -/
private theorem sum_filter_none (events : List (BalanceEvent preset))
    (f : BalanceEvent preset → ℕ) :
    ((events.filter fun _ => false).map f).sum = 0 := by
  induction events with
  | nil => rfl
  | cons e rest ih => simp

/-- The events of a step are within their credit limits. -/
private theorem step_events_bounded {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events) :
    ∀ e ∈ events, e.credits ≤ e.creditLimit := by
  have run := PinSplit2.run_one_step_events step ok
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared (Run.nil.snoc step)
    genesis early (getCurrentEpoch n.state).toNat
  rw [run] at foundOk
  cases foundOk
  exact fun e member => (bounded e member).1

/-- The credits of a block step to a key are at most those of `credC`, `whistC` and sync. -/
private theorem block_credit_le_sources {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (notSlot : ∀ ok, step ≠ Step.slot ok)
    (early : n.fork < .glamsterdam) (electra : .pectra ≤ m.fork) (i : ℕ)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    stepCredit (fun _ => true) (fun _ => true) i step ≤
      stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (syncCredit i)).sum := by
  have bounded := step_events_bounded shared genesis step early replayed
  cases step with
  | block engine signed due ok =>
    have each := block_event_credit shared genesis early electra i replayed bounded
    have split : (events.map (keyCredit i)).sum ≤
        ((events.filter fun x => decide (x.source = .rewards ∨ x.source = .consolidations)).map
          (keyCredit i)).sum +
        ((events.filter fun x => decide (x.source = .slashings)).map (keyCredit i)).sum +
        (events.map (syncCredit i)).sum := by
      simpa using sum_credits_split events (keyCredit i) (syncCredit i) (fun _ => true)
        (fun s => decide (s = .rewards ∨ s = .consolidations)) (fun s => decide (s = .slashings))
        (fun e m _ => by simpa using each e m)
    simp only [stepCredit, replayed, Except.toOption, Option.getD_some, List.filter_true] at split ⊢
    exact split
  | slot ok => exact absurd rfl (notSlot ok)

/-- A block step raises the balance of a key by at most its gross credits. -/
private theorem block_balance_le_gross {g : ForkedBeaconState preset} {f : Fork}
    {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (genesis : Genesis config checks g)
    (early : f < .glamsterdam) (electra : .pectra ≤ f) (i : ℕ) :
    actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i ≤
      actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i + stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i
        (Step.block engine signed due ok) := by
  obtain ⟨events, replayed⟩ := (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩).balanceEvents_ok early
  have base := PinSplit2.step_balance_le_events (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩) early i replayed
  have bounded := step_events_bounded shared genesis (Step.block engine signed due ok) early
    replayed
  have noCons := blockReplay_noConsolidations electra early engine s signed.message
    (Step.balanceEvents_block early replayed)
  have split : (events.map (keyCredit i)).sum ≤ ((events.filter fun e => decide
      (e.source = .rewards ∨ e.source = .slashings ∨ e.source = .sync)).map (keyCredit i)).sum := by
    simpa using sum_credits_split events (keyCredit i) (fun _ => 0) (fun _ => true)
      (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false)
      fun e member _ => by
        have each := block_event_credit shared genesis early electra i replayed bounded e member
        by_cases kept : e.source = .rewards ∨ e.source = .slashings ∨ e.source = .sync
        · simp [kept]
        · simp only [not_or] at kept
          simp [kept.1, kept.2.1, kept.2.2, noCons e member, syncCredit] at each ⊢
          omega
  simp only [stepCredit, replayed, Except.toOption, Option.getD_some]
  omega

/-- The credits of a step, net for a block step, are at most those of `credC`, `whistC` and sync. -/
private theorem step_credit_le_sources {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam) (electra : .pectra ≤ m.fork)
    (i : ℕ) {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    stepNet i step + stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step ≤
      stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (syncCredit i)).sum := by
  have bounded := step_events_bounded shared genesis step early replayed
  have base := PinSplit2.step_balance_le_events step early i replayed
  cases step with
  | block engine signed due ok =>
    have split := block_credit_le_sources shared genesis (Step.block engine signed due ok)
      (by intro ok' h; cases h) early electra i replayed
    simp only [stepNet, stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none, List.filter_true] at base split ⊢
    omega
  | slot ok =>
    have each := slot_event_credit shared genesis early i replayed bounded
    have split := sum_credits_split events (keyCredit i) (syncCredit i)
      (fun s => decide (s ≠ .rewards)) (fun s => decide (s = .consolidations ∨ s = .deposits))
      (fun _ => false) (fun e m notRewards => by simpa using each e m (by simpa using notRewards))
    simp only [stepNet, stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at split ⊢
    omega

/-- The gross credits of a step, with its slot credits other than rewards, are within the sources.

The sources are `credC`, `whistC` and sync.

A block step's net rise is within its gross credits.

Its slot credits other than rewards are at most those of consolidations and deposits. -/
private theorem step_gross_le_sources {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam) (electra : .pectra ≤ m.fork)
    (i : ℕ) {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i
        step + stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step ≤
      stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (syncCredit i)).sum ∧
    stepNet i step ≤ stepCredit
      (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i step ∧
    stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step ≤
      stepCredit (fun _ => false)
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step := by
  have bounded := step_events_bounded shared genesis step early replayed
  cases step with
  | block engine signed due ok =>
    have each := block_event_credit shared genesis early electra i replayed bounded
    have split : (events.map (keyCredit i)).sum ≤
        ((events.filter fun x => decide (x.source = .rewards ∨ x.source = .consolidations)).map
          (keyCredit i)).sum +
        ((events.filter fun x => decide (x.source = .slashings)).map (keyCredit i)).sum +
        (events.map (syncCredit i)).sum := by
      simpa using sum_credits_split events (keyCredit i) (syncCredit i) (fun _ => true)
        (fun s => decide (s = .rewards ∨ s = .consolidations)) (fun s => decide (s = .slashings))
        (fun e m _ => by simpa using each e m)
    have gross := block_balance_le_gross (engine := engine) (signed := signed) (due := due)
      (ok := ok) shared genesis early electra i
    have part : ((events.filter fun x => decide
        (x.source = .rewards ∨ x.source = .slashings ∨ x.source = .sync)).map (keyCredit i)).sum ≤
        (events.map (keyCredit i)).sum :=
      (((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _)
    simp only [stepNet, stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at gross part split ⊢
    omega
  | slot ok =>
    have each := slot_event_credit shared genesis early i replayed bounded
    have split := sum_credits_split events (keyCredit i) (syncCredit i)
      (fun s => decide (s ≠ .rewards)) (fun s => decide (s = .consolidations ∨ s = .deposits))
      (fun _ => false) (fun e m notRewards => by simpa using each e m (by simpa using notRewards))
    have zero := (PinSplit5.slot_syncDebit_zero electra ok early replayed i).2
    simp only [stepNet, stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at split ⊢
    omega

/-- The credits of a run, gross for its block steps, are at most those of `credC`, `whistC`, sync.

A block step's net rise is within its gross credits, so the net credits of the run are too.

Its slot credits other than epoch rewards are at most those of consolidations and deposits. -/
private theorem credits_le_sources {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (electra : .pectra ≤ x.fork)
    (i high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    grossScan i high tail + (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high
      tail).1 ≤ credC tail high i + whistC tail high i + (events.map (syncCredit i)).sum ∧
    netScan i high tail ≤ grossScan i high tail ∧
    (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high tail).1 ≤
      (creditScan (fun _ => false)
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i high tail).1 := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp [credC, whistC, grossScan, netScan_nil, creditScan_nil_fst]
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    obtain ⟨previous, previousNet, previousSlot⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      obtain ⟨one, oneNet, oneSlot⟩ := step_gross_le_sources (shared.append pre) genesis step early
        (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) i addedOk
      unfold credC whistC grossScan at previous ⊢
      unfold grossScan at previousNet
      simp only [netScan_snoc, creditScan_snoc_fst, selected, ↓reduceIte, List.map_append,
        List.sum_append]
      exact ⟨by omega, by omega, by omega⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      obtain rfl := rest
      unfold credC whistC grossScan at previous ⊢
      unfold grossScan at previousNet
      simp only [netScan_snoc, creditScan_snoc_fst, selected, ↓reduceIte]
      exact ⟨previous, previousNet, previousSlot⟩

/-- The credits of a switch step, whole, and of the runs around it are at most the sources. -/
private theorem flip_credits_le_sources {g x s s' y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (pre : Run config checks x s) (step : Step config checks s s') (post : Run config checks s' y)
    (notSlot : ∀ ok, step ≠ Step.slot ok) (early : y.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (i high : ℕ) (inside : (getCurrentEpoch s.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)}
    (replayed : ((pre.snoc step).append post).balanceEvents high = .ok events) :
    netScan i high pre + (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high
        pre).1 + stepCredit (fun _ => true) (fun _ => true) i step +
      (netScan i high post + (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high
        post).1) ≤ credC ((pre.snoc step).append post) high i +
      whistC ((pre.snoc step).append post) high i + (events.map (syncCredit i)).sum := by
  have s'Early : s'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have sEarly : s.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le s'Early
  obtain ⟨e1, replayed1⟩ := pre.balanceEvents_ok sEarly high
  obtain ⟨es, replayedS⟩ := step.balanceEvents_ok s'Early
  obtain ⟨e2, replayed2⟩ := post.balanceEvents_ok early high
  have snoc : (pre.snoc step).balanceEvents high = .ok (e1 ++ es) := by
    simp [Run.balanceEvents, replayed1, replayedS, inside]
    rfl
  have whole := DirectSafety.Apriori.Internal.balanceEvents_append (pre.snoc step) post high snoc
    replayed2
  rw [whole] at replayed
  obtain rfl := Except.ok.inj replayed
  have first := credits_le_sources shared genesis pre sEarly electra i high replayed1
  have last := credits_le_sources (shared.append (pre.snoc step)) genesis post early
    (Nat.le_trans electra (fork_le_of_chainSteps (pre.snoc step).chainSteps)) i high replayed2
  have middle := block_credit_le_sources (shared.append pre) genesis step notSlot s'Early
    (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) i replayedS
  unfold credC whistC
  rw [creditScan_append, creditScan_append, creditScan_snoc_fst, creditScan_snoc_fst]
  simp only [inside, ↓reduceIte]
  unfold credC whistC at first last
  simp only [List.map_append, List.sum_append] at first last ⊢
  omega

/-- The key's effective balance when its exit starts on a run, or 0.

It is the amount of the key's departure charge, which reads the effective balance at the exit call.

A key has a charge only if its exit was not assigned at the run's start.

Only a charge whose exit epoch is at most the run's last epoch counts. -/
def exitQ {x y : ForkedBeaconState preset} (tail : Run config checks x y) (v : ℕ) : ℕ :=
  ((tail.departureCharges.find? fun c =>
      c.index == v && decide (c.epoch ≤ (getCurrentEpoch y.state).toNat)).map (·.amount)).getD 0

/-- Whether a run has the key's departure charge, and the epoch rewards of the steps from it on.

The step with the charge counts too, since the key's epoch pass in it follows its exit.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def riseScan (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → Bool × ℕ
  | _, .nil => (false, 0)
  | _, .snoc (middle := m) pre step =>
    let before := riseScan v high pre
    (before.1 || step.departureCharges.any (·.index == v),
      if (before.1 = true ∨ step.departureCharges.any (·.index == v) = true) ∧
          (getCurrentEpoch m.state).toNat ≤ high + 1 then
        before.2 + PinSplit2.epochRewards v step
      else before.2)

/-- The key's rise on a run after its exit starts there.

It is one upward band for the rise of the effective balance beyond the key's epoch rewards, plus
those rewards over the slot steps that come after the step with its departure charge.

It is 0 for a key whose exit does not start on the run. -/
def riseQ {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  if (riseScan v high tail).1 = true then preset.upwardBand + (riseScan v high tail).2 else 0

/-! ### The keys that a run credits -/

/-- The net credits to a key in the block steps of a run add over `append`. -/
private theorem netScan_append (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) :
    netScan v high (pre.append post) = netScan v high pre + netScan v high post := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change netScan v high ((pre.append post).snoc step) = _
    rw [netScan_snoc, netScan_snoc, ih]
    split <;> omega

/-- A key keeps its public key at its position along a run. -/
private theorem key_persists {x y : ForkedBeaconState preset} (run : Run config checks x y)
    {i : ℕ} {w : Validator} (found : x.state.validators.data[i]? = some w) :
    ∃ w', y.state.validators.data[i]? = some w' ∧ w'.pubkey = w.pubkey :=
  validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps run.chainSteps).1 found

/-- A sync aggregate changes the balance of a position only if its key is in the committee.

The position is then the one of a validator that holds a seat, which the committee keeps.

Otherwise the position is the proposer's, and its balance rises. -/
private theorem sync_moved_seat {f : Fork} {c t : BeaconState preset f} (altair : .altair ≤ f)
    {aggregate : SyncAggregate preset}
    (synced : processSyncAggregate config checks c altair aggregate = .ok t)
    (matched : BalancesMatch t) {i : ℕ}
    (moved : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i ≠
      actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i) :
    (∃ w, t.validators.data[i]? = some w ∧
      w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList) ∨
    ∃ proposer, getBeaconProposerIndex c = .ok proposer ∧ proposer.toNat = i ∧
      actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i := by
  obtain ⟨vals, comm⟩ := BlockLedger.processSyncAggregate_kept synced
  have sizes := sameSizes_processSyncAggregate synced
  have matchedC : BalancesMatch c := by
    unfold BalancesMatch at matched ⊢
    rw [← sizes.1, ← sizes.2]
    exact matched
  have inside : i < c.balances.data.size := by
    by_contra outside
    have missing : actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]
    have outT : t.balances.data[i]? = none :=
      Array.getElem?_eq_none (by have := sizes.2; omega)
    have missingT : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i = 0 := by
      simp [actualBalanceAt, outT]
    omega
  have insideV : i < c.validators.data.size := by
    unfold BalancesMatch at matchedC
    omega
  obtain ⟨w, found⟩ : ∃ w, c.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem insideV⟩
  have foundT : t.validators.data[i]? = some w := by rw [vals]; exact found
  by_cases seat : w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList
  · exact .inl ⟨w, foundT, seat⟩
  refine .inr ?_
  have unseated : w.pubkey ∉ (c.currentSyncCommittee altair).value.pubkeys.toList := by
    rw [← congrFun comm altair]
    exact seat
  obtain ⟨reward, proposerReward, members, chosen, -, -, membersOk, signed, balances⟩ :=
    processSyncAggregate_balance synced
  have seatless : ∀ bit : Bool, ∀ member ∈ (members.zip
      aggregate.syncCommitteeBits.bits.toArray).toList, member.2 = bit →
      member.1.toNat ≠ i := by
    intro bit
    refine signers_elsewhere membersOk found fun member inside _ same => unseated ?_
    rw [Array.toList_zip] at inside
    rw [← same, ← Vector.toList_toArray]
    exact List.of_mem_zip inside |>.1
  obtain ⟨b, held⟩ : ∃ b, c.balances.data[i]? = some b :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨final, atFinal, value⟩ := balances i b held
  have low := (syncRewards_bounds (reward := reward.toNat)
    (proposerReward := proposerReward.toNat) (index := i) (chosen := chosen) _ b.toNat).2
    (fun member inside _ => seatless member.2 member inside rfl)
  rw [← value] at low
  simp only [actualBalanceAt, held, atFinal, Option.map_some, Option.getD_some] at moved ⊢
  by_cases signer : ∃ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.2 = true ∧ chosen.toNat = i
  · obtain ⟨member, inside, signedBit, same⟩ := signer
    exact ⟨chosen, signed ⟨member, inside, signedBit⟩, same, by omega⟩
  · exfalso
    have high := (syncRewards_bounds (reward := reward.toNat)
      (proposerReward := proposerReward.toNat) (index := i) (chosen := chosen) _ b.toNat).1
      (fun member inside bit => ⟨seatless true member inside bit,
        fun same => signer ⟨member, inside, bit, same⟩⟩)
    rw [← value] at high
    omega

/-- A sync aggregate lowers the balance of a position only if its key is in the committee.

The position is then the one of a validator that holds a seat, which the committee keeps. -/
private theorem sync_debit_seat {f : Fork} {c t : BeaconState preset f} (altair : .altair ≤ f)
    {aggregate : SyncAggregate preset}
    (synced : processSyncAggregate config checks c altair aggregate = .ok t)
    (matched : BalancesMatch t) {i : ℕ}
    (lowered : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i <
      actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i) :
    ∃ w, t.validators.data[i]? = some w ∧
      w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList := by
  rcases sync_moved_seat altair synced matched (Nat.ne_of_lt lowered) with seat | ⟨_, _, _, risen⟩
  · exact seat
  · omega

/-- The events of a block's passes credit no key but the proposer, from the sources that matter.

None of them has a sync or consolidation source.

A rewards or slashings event credits only the proposer. -/
private def PassCredits (proposer : ℕ) (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source ≠ .sync ∧ e.source ≠ .consolidations ∧
    ((e.source = .rewards ∨ e.source = .slashings) →
      ∀ i, proposer ≠ i → keyCredit i e = 0)

/-- A carried pass records nothing. -/
private theorem PassCredits.carry {f : Fork} {proposer : ℕ}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (held : PassCredits proposer pre.2)
    (ok : carryBalance action pre = .ok post) : PassCredits proposer post.2 := by
  rw [(PinSplit4.carryBalance_cases ok).2]
  exact held

/-- A recorded pass adds an event.

A rewards or slashings event credits only the proposer. -/
private theorem PassCredits.record {f : Fork} {proposer : ℕ} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (held : PassCredits proposer pre.2)
    (ok : recordBalance source limits action pre = .ok post)
    (notSync : source ≠ .sync) (notConsolidation : source ≠ .consolidations)
    (lowered : (source = .rewards ∨ source = .slashings) → ∀ t, action pre.1 = .ok t →
      ∀ i, proposer ≠ i →
        actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i ≤
          actualBalanceAt (⟨f, pre.1⟩ : ForkedBeaconState preset) i) :
    PassCredits proposer post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, t, computed, rfl⟩ := ok
  intro e member
  rcases List.mem_append.mp member with old | new
  · exact held e old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨notSync, notConsolidation, fun source i other =>
      Nat.sub_eq_zero_of_le (lowered source t computed i other)⟩

/-- A pass that does not lower a balance, and keeps the sizes, does not raise it. -/
private theorem actualBalanceAt_le_of_down {f : Fork} {s u : BeaconState preset f}
    (sizes : SameSizes s u) {i : ℕ} (down : BalanceDown i s u) :
    actualBalanceAt (⟨f, u⟩ : ForkedBeaconState preset) i ≤
      actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i := by
  by_cases inside : i < s.balances.data.size
  · obtain ⟨b, held⟩ : ∃ b, s.balances.data[i]? = some b :=
      ⟨_, Array.getElem?_eq_getElem inside⟩
    obtain ⟨later, found, le⟩ := down b held
    simp only [actualBalanceAt, held, found, Option.map_some, Option.getD_some]
    exact UInt64.le_iff_toNat_le.mp le
  · have outS : s.balances.data[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt inside)
    have outU : u.balances.data[i]? = none :=
      Array.getElem?_eq_none (by have := sizes.2; omega)
    simp [actualBalanceAt, outS, outU]

/-- A fold of recorded passes ends at the state of the fold of their actions. -/
private theorem record_fold_state {α : Type} (src : BalanceSource)
    (lim : α → BeaconState preset fork → Except TransitionError (ℕ × ℕ))
    (act : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)) :
    ∀ (items : List α) (p q : BalanceReplay preset fork),
      items.foldlM (fun pre x => recordBalance src (lim x) (act · x) pre) p = .ok q →
      items.foldlM act p.1 = .ok q.1 := by
  intro items
  induction items with
  | nil =>
    intro p q ok
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    rfl
  | cons x rest ih =>
    rintro ⟨first, events⟩ q ok
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨⟨second, recorded⟩, step, others⟩ := ok
    obtain ⟨_, _, -, actionOk, -⟩ := DirectSafety.Apriori.Internal.recordBalance_single step
    show List.foldlM act first (x :: rest) = _
    rw [List.foldlM_cons, actionOk]
    exact ih _ _ others

/-- The replay of a block ends with its sync pass, after passes that credit only its proposer.

The proposer of the block is the one that the state before the sync pass reads.

The other passes record events that `PassCredits` describes.

The mixes must span more than the seed lookahead plus two epochs. -/
private theorem blockReplay_proposer_credits {fork : Fork} {a t : BeaconState preset fork}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine a block =
      .ok (t, events)) :
    ∃ (c : BeaconState preset fork) (rest : List (BalanceEvent preset)) (altair : .altair ≤ fork)
      (aggregate : SyncAggregate preset) (credit debit : ℕ),
      events = rest ++ [⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, credit, debit⟩] ∧
      getBeaconProposerIndex c = .ok block.proposerIndex ∧
      processSyncAggregate config checks c altair aggregate = .ok t ∧
      PassCredits block.proposerIndex.toNat rest := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have normalized := replay
  unfold blockBalanceReplay at normalized
  simp only [altair, bellatrix, electra, ↓reduceDIte] at normalized
  simp only [← bind_assoc] at normalized
  simp only [bind_assoc] at normalized
  simp only [bind_ok_iff, ensure_ok_iff] at normalized
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk, x1, x2, x3,
    x4, proposed, proposedOk, slashed, slashedOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, requested, requestedOk, withdrawn, withdrawnOk,
    consolidated, consolidatedOk, syncOk⟩ := normalized
  -- The proposer of the block is read at the state before its operations.
  have headerOk : processBlockHeader a block = .ok headed.1 :=
    (PinSplit4.carryBalance_cases headedOk).1
  have input : OperationsInput config checks engine a block voted.1 :=
    ⟨a, headed.1, executed.1, revealed.1, by simp [notGloas, pure, Except.pure], headerOk,
      by simpa only [bellatrix, ↓reduceDIte] using (PinSplit4.recordBalance_cases executedOk).1,
      (PinSplit4.carryBalance_cases revealedOk).1,
      by simpa only [before, ↓reduceDIte] using (PinSplit4.carryBalance_cases votedOk).1⟩
  have read := (operationsInput_proposer apart input).1
  -- The operations apply the actions of the replay in order, so they keep that proposer.
  have operated : processOperations config checks voted.1 block.body a.latestBlockHeader.slot =
      .ok consolidated.1 := by
    have pOk := record_fold_state _ _ _ _ _ _ proposedOk
    have sOk := record_fold_state _ _ _ _ _ _ slashedOk
    have aOk := record_fold_state _ _ _ _ _ _ attestedOk
    have dOk := record_fold_state _ _ _ _ _ _ depositedOk
    have cOk := record_fold_state _ _ _ _ _ _ consolidatedOk
    simp only [Array.foldlM_toList] at pOk sOk aOk dOk cOk
    unfold processOperations
    simp only [notGloas, electra, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, processExecutionRequests]
    exact ⟨x1, x2, x3, x4, proposed.1, pOk, slashed.1, sOk, attested.1, aOk, deposited.1, dOk,
      exited.1, (PinSplit4.carryBalance_cases exitedOk).1, changed.1,
      (PinSplit4.carryBalance_cases changedOk).1, requested.1,
      (PinSplit4.carryBalance_cases requestedOk).1, withdrawn.1,
      (PinSplit4.carryBalance_cases withdrawnOk).1, cOk⟩
  have link := (processOperations_proposer apart operated).1.trans read
  -- The passes before the operations record no credit but the proposer's.
  have base : PassCredits block.proposerIndex.toNat ([] : List (BalanceEvent preset)) :=
    fun e member => by simp at member
  have start : PassCredits block.proposerIndex.toNat voted.2 :=
    (((base.carry headedOk).record executedOk (by decide) (by decide)
      fun h => absurd h (by decide)).carry revealedOk).carry votedOk
  have step : ∀ {source : BalanceSource}
      {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
      (pre post : BalanceReplay preset fork), (source = .rewards ∨ source = .slashings) →
      (getBeaconProposerIndex pre.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat pre.2) →
      recordBalance source limits action pre = .ok post →
      (∀ s u, action s = .ok u → getBeaconProposerIndex s = .ok block.proposerIndex →
        SameSizes s u ∧ (∀ i, block.proposerIndex.toNat ≠ i → BalanceDown i s u) ∧
          getBeaconProposerIndex u = .ok block.proposerIndex) →
      getBeaconProposerIndex post.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat post.2 := by
    intro source limits action pre post src ⟨seen, held⟩ ok props
    obtain ⟨-, -, kept⟩ := props _ _ (PinSplit4.recordBalance_cases ok).1 seen
    refine ⟨kept, held.record ok ?_ ?_ fun _ u computed i other => ?_⟩
    · rcases src with rfl | rfl <;> decide
    · rcases src with rfl | rfl <;> decide
    · obtain ⟨sizes, down, -⟩ := props _ _ computed seen
      exact actualBalanceAt_le_of_down sizes (down i other)
  have away : block.proposerIndex.toNat ≠ block.proposerIndex.toNat + 1 := by omega
  have proposedR := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      getBeaconProposerIndex p.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat p.2)
    (fun pre _ post held ok => step pre post (Or.inr rfl) held ok fun s u c r =>
      ⟨sameSizes_processProposerSlashing c,
        fun i other => (processProposerSlashing_balanceDown apart c r other).1,
        ((processProposerSlashing_balanceDown apart c r away).2).trans r⟩)
    ⟨read, start⟩ proposedOk
  have slashedR := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      getBeaconProposerIndex p.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat p.2)
    (fun pre _ post held ok => step pre post (Or.inr rfl) held ok fun s u c r =>
      ⟨sameSizes_processAttesterSlashing c,
        fun i other => (processAttesterSlashing_balanceDown apart c r other).1,
        ((processAttesterSlashing_balanceDown apart c r away).2).trans r⟩)
    proposedR slashedOk
  have attestedR := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      getBeaconProposerIndex p.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat p.2)
    (fun pre _ post held ok => step pre post (Or.inl rfl) held ok fun s u c r =>
      ⟨sameSizes_processAttestation c,
        fun i other => (processAttestation_balanceDown apart c r other).1,
        ((processAttestation_balanceDown apart c r away).2).trans r⟩)
    slashedR attestedOk
  -- The remaining passes before the sync pass record no rewards or slashings.
  have depositedC := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      PassCredits block.proposerIndex.toNat p.2)
    (fun _ _ _ held ok => held.record ok (by decide) (by decide) fun h => absurd h (by decide))
    attestedR.2 depositedOk
  have requestedC := ((((depositedC.carry exitedOk).carry changedOk).carry requestedOk).carry
    withdrawnOk)
  have consolidatedC := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      PassCredits block.proposerIndex.toNat p.2)
    (fun _ _ _ held ok => held.record ok (by decide) (by decide) fun h => absurd h (by decide))
    requestedC consolidatedOk
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at syncOk
  obtain ⟨⟨credit, debit⟩, -, u, synced, rfl, rfl⟩ := syncOk
  exact ⟨consolidated.1, consolidated.2, altair, _, credit, debit, rfl, link, synced,
    consolidatedC⟩

/-- A key that an event of a block step credits is its proposer, or a seat holder for a sync event.

The mixes must span more than the seed lookahead plus two epochs. -/
private theorem block_gross_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ ∀ e ∈ events, ∀ i, 0 < keyCredit i e →
      i ∈ K ∨ (e.source = .sync ∧ ∃ altair : .altair ≤ f, ∃ w, t.validators.data[i]? = some w ∧
        w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList) := by
  have electra : .pectra ≤ f := Nat.le_trans (by decide) fulu
  obtain ⟨c, rest, altair, aggregate, credit, debit, split, read, synced, passes⟩ :=
    blockReplay_proposer_credits apart electra early (Step.balanceEvents_block early replayed)
  have bounded := step_events_bounded shared genesis (Step.block engine signed due ok) early
    replayed
  have matchedT : BalancesMatch t :=
    (frame_processBlock (applySignedBlock_ok ok).2.1).balancesMatch
      (run_justified_separated shared genesis).1.balancesMatch
  refine ⟨{signed.message.proposerIndex.toNat}, by simp, fun e member i positive => ?_⟩
  have member' := member
  rw [split] at member'
  rcases List.mem_append.mp member' with inRest | inSync
  · obtain ⟨notSync, notConsolidation, only⟩ := passes e inRest
    refine .inl (Finset.mem_singleton.mpr ?_)
    by_contra other
    by_cases credited : e.source = .rewards ∨ e.source = .slashings
    · have := only credited i fun same => other same.symm
      omega
    · have each := block_event_credit shared genesis early electra i replayed bounded e member
      have noRewards : ¬ (e.source = .rewards ∨ e.source = .consolidations) := by
        rintro (h | h)
        · exact credited (.inl h)
        · exact notConsolidation h
      have noSync : syncCredit i e = 0 := by simp [syncCredit, notSync]
      have noSlash : ¬ e.source = .slashings := fun h => credited (.inr h)
      simp only [noRewards, noSlash, noSync, ↓reduceIte] at each
      omega
  · obtain rfl := List.mem_singleton.mp inSync
    simp only [keyCredit] at positive
    rcases sync_moved_seat (i := i) altair synced matchedT (by omega) with h | ⟨_, found, same, -⟩
    · exact .inr ⟨rfl, altair, h⟩
    · exact .inl (Finset.mem_singleton.mpr (by rw [read] at found; cases found; exact same.symm))

/-- A key that rewards, slashings or sync credit in a block step is a proposer or a seat holder. -/
private theorem block_step_gross_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ ∀ i, 0 < stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i
        (Step.block engine signed due ok) →
      i ∈ K ∨ ∃ altair : .altair ≤ f, ∃ w, t.validators.data[i]? = some w ∧
        w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList := by
  cases replayed : (Step.block engine signed due ok).balanceEvents with
  | error _ =>
    exact ⟨∅, by simp, fun i pos => by simp [stepCredit, replayed, Except.toOption] at pos⟩
  | ok events =>
    obtain ⟨K, card, keys⟩ := block_gross_keys genesis apart shared fulu early replayed
    refine ⟨K, card, fun i pos => ?_⟩
    simp only [stepCredit, replayed, Except.toOption, Option.getD_some] at pos
    by_contra none
    refine absurd (List.sum_eq_zero fun x member => ?_) (Nat.pos_iff_ne_zero.mp pos)
    obtain ⟨e, inFilter, rfl⟩ := List.mem_map.mp member
    obtain ⟨inEvents, source⟩ := List.mem_filter.mp inFilter
    refine Nat.eq_zero_of_not_pos fun positive => none ?_
    rcases keys e inEvents i positive with inK | ⟨-, altair, seat⟩
    · exact .inl inK
    · exact .inr ⟨altair, seat⟩

/-- A list of at most one element has equal members. -/
private theorem list_eq_of_length_le_one {α : Type} {L : List α} (short : L.length ≤ 1) {a b : α}
    (ha : a ∈ L) (hb : b ∈ L) : a = b := by
  cases L with
  | nil => simp at ha
  | cons c rest =>
    cases rest with
    | nil =>
      rw [List.mem_singleton] at ha hb
      rw [ha, hb]
    | cons d rest => exact absurd short (by simp)

/-- The keys that one step credits by a pending-deposit pass.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits, in one slot step.

So the keys are at most that many for each epoch that the step leaves. -/
private theorem step_deposit_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (step : Step config checks x y)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∃ D : Finset ℕ, D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      ∀ i, 0 < stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i step → i ∈ D := by
  classical
  cases step with
  | block engine signed due ok =>
    refine ⟨∅, by simp, fun i here => ?_⟩
    exfalso
    have zero : stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
        (Step.block engine signed due ok : Step config checks _ _) = 0 := by
      show ((((Step.block (config := config) (checks := checks) engine signed due
        ok).balanceEvents.toOption.getD []).filter ((fun _ => false) ·.source)).map
          (keyCredit i)).sum = 0
      rw [List.filter_eq_nil_iff.mpr (fun a _ => by simp)]
      rfl
    omega
  | slot across =>
    obtain ⟨events, eventsOk⟩ :=
      (Step.slot across : Step config checks x y).balanceEvents_ok early
    -- A slot step credits a key by deposits only if one of its deposit events does.
    have quiet : ∀ i, (∀ e ∈ events, e.source = .deposits → keyCredit i e = 0) →
        stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
          (Step.slot across : Step config checks x y) = 0 := fun i none' => by
      show (((((Step.slot (config := config) (checks := checks)
        across).balanceEvents.toOption.getD []).filter
          ((fun s => decide (s = .deposits)) ·.source))).map (keyCredit i)).sum = 0
      simp only [eventsOk, Except.toOption, Option.getD_some]
      exact List.sum_eq_zero fun _ member => by
        obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
        obtain ⟨mem, test⟩ := List.mem_filter.mp inside
        exact none' e mem (by simpa using test)
    by_cases any : ∃ e ∈ events, e.source = .deposits
    · obtain ⟨sites, ends, single⟩ :=
        DirectSafety.Apriori.Internal.Step.slot_deposit_site shared genesis across early delay
          eventsOk
      have epochNext := ends any
      obtain ⟨e0, mem0, dep0⟩ := any
      obtain ⟨electra, a, b, matched, -, -, deposited, before0, after0⟩ := sites e0 mem0 dep0
      obtain ⟨-, -, rises⟩ := pending_deposit_rises a b matched electra deposited
      have oneEpoch : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat = 1 := by
        omega
      refine ⟨(Finset.range b.balances.data.size).filter fun i =>
          actualBalanceAt (⟨x.fork, a⟩ : ForkedBeaconState preset) i <
            actualBalanceAt (⟨x.fork, b⟩ : ForkedBeaconState preset) i, ?_, fun i here => ?_⟩
      · rw [oneEpoch, Nat.mul_one]
        exact rises
      · refine Finset.mem_filter.mpr ?_
        have mono : ∃ e ∈ events, e.source = .deposits ∧ 0 < keyCredit i e := by
          by_contra none
          have none' : ∀ e ∈ events, e.source = .deposits → keyCredit i e = 0 :=
            fun e mem dep => by
              by_contra ne
              exact none ⟨e, mem, dep, Nat.pos_of_ne_zero ne⟩
          have := quiet i none'
          omega
        obtain ⟨e, mem, dep, positive⟩ := mono
        -- A slot step records one deposit event, so it is the one that the site names.
        have same : e = e0 := list_eq_of_length_le_one single
          (List.mem_filter.mpr ⟨mem, by simpa using dep⟩)
          (List.mem_filter.mpr ⟨mem0, by simpa using dep0⟩)
        subst same
        unfold keyCredit at positive
        rw [before0, after0] at positive
        refine ⟨?_, ?_⟩
        · by_contra outside
          have outside' : ¬ i < b.balances.data.size := fun h =>
            outside (Finset.mem_range.mpr h)
          have missing : actualBalanceAt (⟨x.fork, b⟩ : ForkedBeaconState preset) i = 0 := by
            simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside')]
          omega
        · omega
    · refine ⟨∅, by simp, fun i here => ?_⟩
      exfalso
      have := quiet i fun e mem dep => absurd ⟨e, mem, dep⟩ any
      omega

/-- The keys credited in the block steps of a run inside one period of sync committees.

A key credited by a block is a proposer, at most one for each block.

Otherwise it holds a seat of the committee that the run starts with. -/
private theorem credited_piece {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (altair : .altair ≤ x.fork) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ)
    (same : (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) :
    ∃ B D : Finset ℕ, B.card ≤ r.blockCount ∧
      D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∀ i, 0 < grossScan i high r →
      i ∈ B ∨ ∃ w, y.state.validators.data[i]? = some w ∧
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList) ∧
      (∀ i, 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r).1 →
        i ∈ D) ∧
      ∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (syncDebit i)).sum →
        ∃ w, y.state.validators.data[i]? = some w ∧
          w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
  classical
  induction r with
  | nil =>
    refine ⟨∅, ∅, by simp, by simp, fun i pos => (Nat.lt_irrefl 0 pos).elim,
      fun i pos => (Nat.lt_irrefl 0 pos).elim, ?_⟩
    intro events replayed i pos
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp at pos
  | @snoc u l pre step ih =>
    have uEarly : u.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have up := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    have uSame : (getCurrentEpoch u.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
      have above := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) up
      have under := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
      omega
    obtain ⟨B, D, cardB, cardD, hB, hDep, hS⟩ := ih uEarly uSame
    obtain ⟨Ds, cardDs, hDs⟩ := step_deposit_keys genesis (shared.append pre) step early delay
    have cardUnion : (D ∪ Ds).card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat) := by
      have joined := Nat.mul_le_mul_left preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
        (show (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat +
          ((getCurrentEpoch l.state).toNat - (getCurrentEpoch u.state).toNat) ≤
            (getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat by omega)
      rw [Nat.mul_add] at joined
      exact (Finset.card_union_le _ _).trans (Nat.le_trans (Nat.add_le_add cardD cardDs) joined)
    have depMem : ∀ i, 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high
        (pre.snoc step)).1 → i ∈ D ∪ Ds := by
      intro i pos
      rw [creditScan_snoc_fst] at pos
      split at pos
      · by_cases prior : 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i
            high pre).1
        · exact Finset.mem_union_left _ (hDep i prior)
        · exact Finset.mem_union_right _ (hDs i (by omega))
      · exact Finset.mem_union_left _ (hDep i pos)
    have carry : ∀ (i : ℕ) (w : Validator), u.state.validators.data[i]? = some w →
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList →
          ∃ w', l.state.validators.data[i]? = some w' ∧
            w'.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
      intro i w found mem
      obtain ⟨w', found', same'⟩ := key_persists (Run.nil.snoc step) found
      exact ⟨w', found', same' ▸ mem⟩
    cases step with
    | slot ok =>
      have fulu' : .fusaka ≤ u.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      refine ⟨B, D ∪ Ds, cardB, cardUnion, fun i pos => ?_, depMem, ?_⟩
      rw [grossScan_snoc] at pos
      have prior : 0 < grossScan i high pre := by
        split at pos
        · simpa [stepCredit] using pos
        · exact pos
      rcases hB i prior with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (carry i w found mem)
      intro events replayed i pos
      simp only [Run.balanceEvents, bind_ok_iff] at replayed
      obtain ⟨prior, priorOk, rest⟩ := replayed
      split at rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        have zero := (PinSplit5.slot_syncDebit_zero
          (Nat.le_trans (show Fork.pectra ≤ Fork.fusaka by decide) fulu') ok early addedOk i).1
        simp only [List.map_append, List.sum_append, zero, Nat.add_zero] at pos
        obtain ⟨w, found, mem⟩ := hS prior priorOk i pos
        exact carry i w found mem
      · simp only [pure, Except.pure, Except.ok.injEq] at rest
        subst rest
        obtain ⟨w, found, mem⟩ := hS _ priorOk i pos
        exact carry i w found mem
    | @block f s t engine signed due ok =>
      have fulu' : .fusaka ≤ f := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      obtain ⟨K, cardK, hK⟩ := block_step_gross_keys (engine := engine) (signed := signed)
        (due := due) (ok := ok) genesis apart (shared.append pre) fulu' uEarly
      refine ⟨B ∪ K, D ∪ Ds, ?_, cardUnion, fun i pos => ?_, depMem, ?_⟩
      · exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB cardK)
      · rw [grossScan_snoc] at pos
        rcases Nat.eq_zero_or_pos (grossScan i high pre) with zero | prior
        · rcases hK i (by split at pos <;> omega) with member | ⟨altair', w, hv, mem⟩
          · exact .inl (Finset.mem_union_right _ member)
          · have committee := (Run.snoc pre (Step.block engine signed due ok)
                ).currentSyncCommittee_eq_of_same_period early same altair' altair
            exact .inr ⟨w, hv, by rw [← committee]; exact mem⟩
        · rcases hB i prior with member | ⟨w, found, mem⟩
          · exact .inl (Finset.mem_union_left _ member)
          · exact .inr (carry i w found mem)
      · intro events replayed i pos
        simp only [Run.balanceEvents, bind_ok_iff] at replayed
        obtain ⟨prior, priorOk, rest⟩ := replayed
        split at rest
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
          obtain ⟨added, addedOk, rfl⟩ := rest
          simp only [List.map_append, List.sum_append] at pos
          by_cases first : 0 < (prior.map (syncDebit i)).sum
          · obtain ⟨w, found, mem⟩ := hS prior priorOk i first
            exact carry i w found mem
          · have here : 0 < (added.map (syncDebit i)).sum := by omega
            have altair' : .altair ≤ f := Nat.le_trans (by decide) fulu'
            obtain ⟨c, rest', aggregate, credit, debit, rfl, silent, -, synced⟩ :=
              PinSplit5.blockReplay_sync_split (show f < .glamsterdam from uEarly) altair'
                (Step.balanceEvents_block uEarly addedOk)
            simp only [List.map_append, List.sum_append, silent, syncDebit, ↓reduceIte,
              List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add,
              Nat.add_zero] at here
            have matchedT : BalancesMatch t :=
              (frame_processBlock (applySignedBlock_ok ok).2.1).balancesMatch
                (run_justified_separated (shared.append pre) genesis).1.balancesMatch
            obtain ⟨w, hv, mem⟩ := sync_debit_seat (i := i) altair' synced matchedT (by omega)
            have committee := (Run.snoc pre (Step.block engine signed due ok)
                ).currentSyncCommittee_eq_of_same_period early same altair' altair
            refine ⟨w, hv, ?_⟩
            rw [← committee]
            exact mem
        · simp only [pure, Except.pure, Except.ok.injEq] at rest
          subst rest
          obtain ⟨w, found, mem⟩ := hS _ priorOk i pos
          exact carry i w found mem

/-- The positions that hold a key of a committee of a list are at most the keys of the list.

The registry has distinct keys, and each committee has at most `SYNC_COMMITTEE_SIZE` keys. -/
private theorem listed_positions_card (state : BeaconState preset fork)
    (distinct : PubkeysDistinct state) (Ls : List (List Cryptography.Bls.BLSPubkey))
    (each : ∀ L ∈ Ls, L.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat) :
    ((Finset.range state.validators.data.size).filter fun i =>
        ∃ w, state.validators.data[i]? = some w ∧ ∃ L ∈ Ls, w.pubkey ∈ L).card ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * Ls.length := by
  classical
  have mapped : ((Finset.range state.validators.data.size).filter fun i =>
      ∃ w, state.validators.data[i]? = some w ∧ ∃ L ∈ Ls, w.pubkey ∈ L).card ≤
        Ls.flatten.toFinset.card := by
    refine Finset.card_le_card_of_injOn (keyAt state) (fun i member => ?_)
      (fun i mi j mj eq => ?_)
    · obtain ⟨w, found, L, hL, mem⟩ := (Finset.mem_filter.mp member).2
      simp only [keyAt, found, Option.map_some, Option.getD_some]
      exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨L, hL, mem⟩)
    · obtain ⟨w, found, -⟩ := (Finset.mem_filter.mp mi).2
      obtain ⟨w', found', -⟩ := (Finset.mem_filter.mp mj).2
      simp only [keyAt, found, found', Option.map_some, Option.getD_some] at eq
      exact distinct.index_eq found found' eq
  have total : Ls.flatten.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat * Ls.length := by
    rw [List.length_flatten]
    have := List.sum_le_length_nsmul (Ls.map List.length) preset.SYNC_COMMITTEE_SIZE.toNat
      (fun a ha => by
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp ha
        exact each L hL)
    simpa [List.length_map, smul_eq_mul, Nat.mul_comm] using this
  exact mapped.trans ((List.toFinset_card_le _).trans total)

/-- The positions that hold a key of a committee are at most the size of the committee. -/
private theorem seat_positions {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y) (altair : .altair ≤ x.fork) :
    ∃ S : Finset ℕ, S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat ∧ ∀ (i : ℕ) (w : Validator),
      y.state.validators.data[i]? = some w →
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList → i ∈ S := by
  classical
  have distinct := (shared.append r).pubkeysDistinct genesis
  let L := (x.state.currentSyncCommittee altair).value.pubkeys.toList
  refine ⟨(Finset.range y.state.validators.data.size).filter fun i =>
      ∃ w, y.state.validators.data[i]? = some w ∧ w.pubkey ∈ L, ?_, ?_⟩
  · have listed := listed_positions_card y.state distinct [L] (by simp [L])
    rw [List.length_singleton, Nat.mul_one] at listed
    refine le_trans (Finset.card_le_card ?_) listed
    intro i member
    obtain ⟨inside, w, found, mem⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨inside, w, found, L, List.mem_singleton_self L, mem⟩
  · intro i w found mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
      w, found, mem⟩

/-- A later epoch of a period is in the same period or the next one. -/
private theorem succ_div_le (a c : ℕ) : (a + 1) / c ≤ a / c + 1 := by
  rcases Nat.eq_zero_or_pos c with zero | positive
  · subst zero
    simp
  · apply Nat.div_le_of_le_mul
    have := Nat.lt_mul_div_succ a positive
    omega

/-- The empty run before a run changes nothing. -/
private theorem run_nil_append {x y : ForkedBeaconState preset} (r : Run config checks x y) :
    Run.nil.append r = r := by
  induction r with
  | nil => rfl
  | snoc r step ih => exact congrArg (fun run => run.snoc step) ih

/-- The keys credited in the block steps of a run, counted by the periods that it touches.

The keys that a sync aggregate debits hold a seat of one committee for each period of the run.

Each committee is the current one at a state of the run, in the period of its index. -/
private theorem credited_pieces_seated {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {y : ForkedBeaconState preset}
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ) :
    ∀ (n : ℕ) {x : ForkedBeaconState preset}, Run config checks g x →
      ∀ (r : Run config checks x y), .fusaka ≤ x.fork →
    (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + n →
    ∃ (Ls : ℕ → List Cryptography.Bls.BLSPubkey) (B S D : Finset ℕ), B.card ≤ r.blockCount ∧
      S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) ∧
      D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∀ i, 0 < grossScan i high r → i ∈ B ∨ i ∈ S) ∧
      (∀ i, 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r).1 →
        i ∈ D) ∧
      (∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (syncDebit i)).sum →
        i ∈ S ∧ ∃ w j, y.state.validators.data[i]? = some w ∧ j ≤ n ∧ w.pubkey ∈ Ls j) ∧
      ∀ j ≤ n, ∃ (z : ForkedBeaconState preset) (r1 : Run config checks x z)
        (r2 : Run config checks z y) (alt : .altair ≤ z.fork), r1.append r2 = r ∧
        (getCurrentEpoch z.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + j ∧
        Ls j = (z.state.currentSyncCommittee alt).value.pubkeys.toList := by
  classical
  intro n
  induction n with
  | zero =>
    intro x shared r fulu count
    have electra : .pectra ≤ x.fork := Nat.le_trans (by decide) fulu
    have altair : .altair ≤ x.fork := Nat.le_trans (by decide) electra
    obtain ⟨B, D, cardB, cardD, hB, hDep, hD⟩ := credited_piece genesis apart shared r fulu altair
      early delay high (by simpa using count)
    obtain ⟨S, cardS, hS⟩ := seat_positions genesis shared r altair
    refine ⟨fun _ => (x.state.currentSyncCommittee altair).value.pubkeys.toList, B, S, D, cardB,
      by simpa using cardS, cardD, fun i pos => ?_, hDep, ?_, ?_⟩
    · rcases hB i pos with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (hS i w found mem)
    · intro events replayed i pos
      obtain ⟨w, found, mem⟩ := hD events replayed i pos
      exact ⟨hS i w found mem, w, 0, found, Nat.le_refl _, mem⟩
    · intro j hj
      obtain rfl : j = 0 := by omega
      exact ⟨x, Run.nil, r, altair, run_nil_append r, (Nat.add_zero _).symm, rfl⟩
  | succ n ih =>
    intro x shared r fulu count
    have electra : .pectra ≤ x.fork := Nat.le_trans (by decide) fulu
    have altair : .altair ≤ x.fork := Nat.le_trans (by decide) electra
    obtain ⟨m, v, pre, step, post, split, hm, hv⟩ := Run.split_at_flip r
      (fun z => (getCurrentEpoch x.state).toNat /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
        (getCurrentEpoch z.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      (Nat.lt_irrefl _) (by omega)
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have up := PinSplit.ChainStep.epoch_le_succ step.chainStep
    have mSame : (getCurrentEpoch m.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
      have under := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
      omega
    have vNext : (getCurrentEpoch v.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 := by
      have above := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) up
      have step' := succ_div_le (getCurrentEpoch m.state).toNat
        (max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      omega
    have mEarly : m.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (Nat.le_trans step.chainStep.fork_le
        (fork_le_of_chainSteps post.chainSteps)) early
    have vFulu : .fusaka ≤ v.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps (pre.snoc step).chainSteps)
    obtain ⟨B₁, D₁, cardB₁, cardD₁, hB₁, hDep₁, hD₁⟩ := credited_piece genesis apart shared pre fulu
      altair mEarly delay high (by simpa using mSame)
    obtain ⟨S₁, cardS₁, hS₁⟩ := seat_positions genesis shared pre altair
    obtain ⟨Ls₂, B₂, S₂, D₂, cardB₂, cardS₂, cardD₂, hB₂, hDep₂, hD₂, hz₂⟩ := ih (x := v)
      (shared.append (pre.snoc step)) post vFulu
      (by omega)
    -- The step leaves an epoch, so it is a slot step: a block step keeps its epoch.
    have slotStep : ∃ ok, step = Step.slot ok := by
      cases step with
      | slot ok => exact ⟨ok, rfl⟩
      | @block f before after engine signed due ok =>
        exfalso
        have same := processBlock_slot (applySignedBlock_ok ok).2.1
        have e : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
          simp only [getCurrentEpoch, same]
        have hm' : ¬ (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
              (getCurrentEpoch before).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := hm
        have hv' : (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
              (getCurrentEpoch after).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := hv
        rw [e] at hv'
        exact hm' hv'
    obtain ⟨ok, rfl⟩ := slotStep
    subst split
    have vEarly : v.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
    obtain ⟨Ds, cardDs, hDs⟩ := step_deposit_keys genesis (shared.append pre) (Step.slot ok)
      vEarly delay
    have stepUp := UInt64.le_iff_toNat_le.mp
      (Step.slot ok : Step config checks m v).chainStep.currentEpoch_le
    have postUp := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    refine ⟨fun j => if j = 0 then (x.state.currentSyncCommittee altair).value.pubkeys.toList
        else Ls₂ (j - 1), B₁ ∪ B₂, S₁ ∪ S₂, D₁ ∪ Ds ∪ D₂, ?_, ?_, ?_, fun i pos => ?_,
      fun i pos => ?_, ?_, ?_⟩
    · rw [Run.blockCount_append]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB₁ cardB₂)
    · refine (Finset.card_union_le _ _).trans ?_
      calc _ ≤ preset.SYNC_COMMITTEE_SIZE.toNat +
            preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) := Nat.add_le_add cardS₁ cardS₂
        _ = _ := by ring
    · have joined := Nat.mul_le_mul_left preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
        (show ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
          ((getCurrentEpoch v.state).toNat - (getCurrentEpoch m.state).toNat) +
            ((getCurrentEpoch y.state).toNat - (getCurrentEpoch v.state).toNat) ≤
              (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat by omega)
      rw [Nat.mul_add, Nat.mul_add] at joined
      exact (Finset.card_union_le _ _).trans (Nat.le_trans (Nat.add_le_add
        ((Finset.card_union_le _ _).trans (Nat.add_le_add cardD₁ cardDs)) cardD₂) joined)
    · rw [grossScan_append] at pos
      by_cases first : 0 < grossScan i high (pre.snoc (Step.slot ok))
      · have prior : 0 < grossScan i high pre := by
          rw [grossScan_snoc] at first
          split at first
          · simpa [stepCredit] using first
          · exact first
        rcases hB₁ i prior with member | ⟨w, found, mem⟩
        · exact .inl (Finset.mem_union_left _ member)
        · exact .inr (Finset.mem_union_left _ (hS₁ i w found mem))
      · have later : 0 < grossScan i high post := by omega
        rcases hB₂ i later with member | member
        · exact .inl (Finset.mem_union_right _ member)
        · exact .inr (Finset.mem_union_right _ member)
    · rw [creditScan_append] at pos
      by_cases first : 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high
          (pre.snoc (Step.slot ok))).1
      · rw [creditScan_snoc_fst] at first
        split at first
        · by_cases prior : 0 < (creditScan (fun _ => false)
              (fun s => decide (s = .deposits)) i high pre).1
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hDep₁ i prior))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hDs i (by omega)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hDep₁ i first))
      · exact Finset.mem_union_right _ (hDep₂ i (by omega))
    · intro events replayed i pos
      obtain ⟨e1, ok1⟩ := (pre.snoc (Step.slot ok)).balanceEvents_ok vEarly high
      obtain ⟨e2, ok2⟩ := post.balanceEvents_ok early high
      rw [DirectSafety.Apriori.Internal.balanceEvents_append _ _ high ok1 ok2] at replayed
      have joined := Except.ok.inj replayed
      subst joined
      simp only [List.map_append, List.sum_append] at pos
      by_cases first : 0 < ((e1.map (syncDebit i))).sum
      · have seated : ∃ w, m.state.validators.data[i]? = some w ∧
            w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
          simp only [Run.balanceEvents, bind_ok_iff] at ok1
          obtain ⟨prior, priorOk, rest⟩ := ok1
          split at rest
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
            obtain ⟨added, addedOk, rfl⟩ := rest
            have zero := (PinSplit5.slot_syncDebit_zero
              (Nat.le_trans (show Fork.pectra ≤ Fork.fusaka by decide)
                (Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps))) ok vEarly addedOk i).1
            simp only [List.map_append, List.sum_append, zero, Nat.add_zero] at first
            exact hD₁ prior priorOk i first
          · simp only [pure, Except.pure, Except.ok.injEq] at rest
            subst rest
            exact hD₁ _ priorOk i first
        obtain ⟨w, found, mem⟩ := seated
        refine ⟨Finset.mem_union_left _ (hS₁ i w found mem), ?_⟩
        have kept := (validatorKeys_prefix_and_distinct_of_chainSteps
          (Relation.ReflTransGen.head (Step.slot ok : Step config checks m v).chainStep
            post.chainSteps)).1
        obtain ⟨w', found', same⟩ := validators_getElem?_of_validatorKeys_prefix kept found
        exact ⟨w', 0, found', Nat.zero_le _, by simpa [same] using mem⟩
      · obtain ⟨inS, w, j, found, hj, mem⟩ := hD₂ e2 ok2 i (by omega)
        exact ⟨Finset.mem_union_right _ inS, w, j + 1, found, by omega, by simpa using mem⟩
    · intro j hj
      by_cases j0 : j = 0
      · subst j0
        exact ⟨x, Run.nil, (pre.snoc (Step.slot ok)).append post, altair, run_nil_append _,
          (Nat.add_zero _).symm, by simp⟩
      · obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := hz₂ (j - 1) (by omega)
        refine ⟨z, (pre.snoc (Step.slot ok)).append r1, r2, alt, ?_, ?_, ?_⟩
        · rw [← Run.append_assoc, cut]
        · omega
        · simpa [j0] using hL

/-- The keys credited in the block steps of a run, counted by the periods that it touches. -/
private theorem credited_pieces {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {y : ForkedBeaconState preset}
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ) :
    ∀ (n : ℕ) {x : ForkedBeaconState preset}, Run config checks g x →
      ∀ (r : Run config checks x y), .fusaka ≤ x.fork →
    (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + n →
    ∃ B S D : Finset ℕ, B.card ≤ r.blockCount ∧
      S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) ∧
      D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∀ i, 0 < grossScan i high r → i ∈ B ∨ i ∈ S) ∧
      (∀ i, 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r).1 →
        i ∈ D) ∧
      ∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (syncDebit i)).sum →
        i ∈ S := by
  intro n x shared r fulu count
  obtain ⟨_, B, S, D, cardB, cardS, cardD, hBS, hDep, hSD, _⟩ :=
    credited_pieces_seated genesis apart early delay high n shared r fulu count
  exact ⟨B, S, D, cardB, cardS, cardD, hBS, hDep,
    fun events replayed i pos => (hSD events replayed i pos).1⟩

/-- A key of an earlier registry has the same position in a later registry.

The later registry has distinct keys, and the earlier keys are a prefix of the later ones. -/
private theorem position_in_prefix {f f' : Fork} {x : BeaconState preset f}
    {t : BeaconState preset f'} (kept : validatorKeys x <+: validatorKeys t)
    (distinct : PubkeysDistinct t) {pk : Cryptography.Bls.BLSPubkey}
    (mem : pk ∈ validatorKeys x) {i : ℕ} {w : Validator}
    (found : t.validators.data[i]? = some w) (same : w.pubkey = pk) :
    ∃ v, x.validators.data[i]? = some v ∧ v.pubkey = pk := by
  simp only [validatorKeys] at mem
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp mem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
  have foundX : x.validators.data[j]? = some v := by simpa using hj
  obtain ⟨cur, foundT, same'⟩ := validators_getElem?_of_validatorKeys_prefix kept foundX
  have index := distinct.index_eq found foundT (same.trans same'.symm)
  subst index
  exact ⟨v, foundX, rfl⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The keys that a sync aggregate debits on the two branches fit the committees of their periods.

The keys of C's run from the finalized block are counted in its committees.

The keys of R's run from the split hold a seat of its committees.

Its first two committees are the current and next ones at the split, which C's run holds too.

So each key counts once, and the later committees of R's run count after C's.

The next committee at the start of a run is the current one at its end, if it crosses a period. -/
private theorem seat_union_card (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high : ℕ)
    {events eventsF eventsC : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents high = .ok eventsC)
    (AV AK : Finset ℕ)
    (debitsC : ∀ i ∈ AV, 0 < ((eventsF ++ eventsC).map (syncDebit i)).sum)
    (debitsR : ∀ i ∈ AK, 0 < (events.map (syncDebit i)).sum) :
    (AV ∪ AK).card ≤ preset.SYNC_COMMITTEE_SIZE.toNat *
      (((getCurrentEpoch pulled).toNat + 1) /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  have apart := h.parameters.lookahead
  have altairF : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled := UInt64.le_iff_toNat_le.mp h.called
  have pulledCounted := UInt64.le_iff_toNat_le.mp h.later
  have near := h.near
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  simp only at finSplit
  generalize hP : max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat = P at *
  -- the periods of the two runs
  have divFS := Nat.div_le_div_right (c := P) finSplit
  have divSP := Nat.div_le_div_right (c := P) splitPulled
  have divPC := Nat.div_le_div_right (c := P) pulledCounted
  have divCN := Nat.div_le_div_right (c := P) near
  have divSC : (getCurrentEpoch split).toNat / P ≤ (getCurrentEpoch counted).toNat / P :=
    Nat.div_le_div_right (Nat.le_trans splitPulled pulledCounted)
  have divRS : (getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P ≤
      ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P + 1 := by
    rcases Nat.le_total (getCurrentEpoch pulled).toNat (getCurrentEpoch split).toNat with
      order | order
    · have := Nat.div_le_div_right (c := P) order
      have nonneg :=
        Nat.zero_le (((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P)
      omega
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le order
      rw [hd, Nat.add_sub_cancel_left]
      have := Nat.add_div_le_div_add_div_add_one (getCurrentEpoch split).toNat d P
      have nonneg := Nat.zero_le (d / P)
      omega
  have divDepth : ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P ≤
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) / P :=
    Nat.div_le_div_right (by omega)
  have periodsR : (getCurrentEpoch pulled).toNat / P =
      (getCurrentEpoch split).toNat / P +
        ((getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P) := by omega
  have periodsC : (getCurrentEpoch counted).toNat / P =
      (getCurrentEpoch fin).toNat / P +
        ((getCurrentEpoch counted).toNat / P - (getCurrentEpoch fin).toNat / P) := by omega
  obtain ⟨LsR, BR, SR, DR, -, -, -, -, -, debitR, familyR⟩ :=
    credited_pieces_seated h.genesis apart (y := ⟨fork, pulled⟩) h.early h.delay high
      ((getCurrentEpoch pulled).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      (toFin.append fromFin) tail h.fulu (by rw [hP]; exact periodsR)
  obtain ⟨LsC, BC, SC, DC, -, -, -, -, -, debitC, familyC⟩ :=
    credited_pieces_seated h.genesis apart (y := ⟨fork, counted⟩) h.early h.delay high
      ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      toFin (fromFin.append tailC) h.fulu (by rw [hP]; exact periodsC)
  simp only [hP] at familyR familyC debitR debitC
  have replayedRC : (fromFin.append tailC).balanceEvents high = .ok (eventsF ++ eventsC) :=
    DirectSafety.Apriori.Internal.balanceEvents_append fromFin tailC high replayedF replayedC
  have arith : ((getCurrentEpoch counted).toNat / P - (getCurrentEpoch fin).toNat / P + 1) +
      ((getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P - 1) ≤
      ((getCurrentEpoch pulled).toNat + 1) / P - (getCurrentEpoch fin).toNat / P + 1 +
        ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) / P := by
    generalize (getCurrentEpoch counted).toNat / P = A at divCN ⊢
    generalize ((getCurrentEpoch pulled).toNat + 1) / P = B at divCN ⊢
    generalize (getCurrentEpoch fin).toNat / P = F
    generalize (getCurrentEpoch pulled).toNat / P = E at divRS ⊢
    generalize (getCurrentEpoch split).toNat / P = T at divRS ⊢
    generalize ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P = D1
      at divRS divDepth
    generalize ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) / P = D2
      at divDepth ⊢
    omega
  generalize hnR : (getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P = nR
    at *
  generalize hnC : (getCurrentEpoch counted).toNat / P - (getCurrentEpoch fin).toNat / P = nC
    at *
  -- the current and next committees at the split
  have keysSplit := (toFin.append fromFin).syncCommittee_keys h.genesis altairF
  generalize hLcur : (split.currentSyncCommittee altairF).value.pubkeys.toList = Lcur at *
  generalize hLnext : (split.nextSyncCommittee altairF).value.pubkeys.toList = Lnext at *
  have sizeOf : ∀ {f : Fork} (alt : .altair ≤ f) (b : BeaconState preset f),
      (b.currentSyncCommittee alt).value.pubkeys.toList.length =
        preset.SYNC_COMMITTEE_SIZE.toNat := fun _ _ => Vector.length_toList
  -- R's first two committees are the current and next ones at the split
  have firstR : LsR 0 = Lcur := by
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyR 0 (Nat.zero_le _)
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLcur]
    exact r1.currentSyncCommittee_eq_of_same_period earlyZ (by rw [hP]; simpa using per) alt
      altairF
  have secondR : 1 ≤ nR → LsR 1 = Lnext := fun one => by
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyR 1 one
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLnext]
    exact r1.currentSyncCommittee_eq_nextSyncCommittee_of_next_period earlyZ
      h.facts.divisors.syncPeriod (by rw [hP]; simpa using per) alt altairF
  -- C's committees hold them too
  have firstC : ∃ j ≤ nC, LsC j = Lcur := by
    refine ⟨(getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P, by omega, ?_⟩
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyC
      ((getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P) (by omega)
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLcur]
    rcases Run.prefix_total r1 r2 fromFin tailC cut rfl with ⟨r, -⟩ | ⟨r, -⟩
    · exact (r.currentSyncCommittee_eq_of_same_period h.early
        (by rw [hP]; simp only; omega) altairF alt).symm
    · exact r.currentSyncCommittee_eq_of_same_period earlyZ
        (by rw [hP]; simp only; omega) alt altairF
  have secondC : 1 ≤ nR → ∃ j ≤ nC, LsC j = Lnext := fun one => by
    refine ⟨(getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P + 1,
      by omega, ?_⟩
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyC
      ((getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P + 1) (by omega)
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLnext]
    rcases Run.prefix_total r1 r2 fromFin tailC cut rfl with ⟨r, -⟩ | ⟨r, -⟩
    · exfalso
      have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r.chainSteps)
      simp only at order
      have := Nat.div_le_div_right (c := P) order
      omega
    · exact r.currentSyncCommittee_eq_nextSyncCommittee_of_next_period earlyZ
        h.facts.divisors.syncPeriod (by rw [hP]; simp only; omega) alt altairF
  -- the positions that hold a key of the committees of each run
  have distinctR : PubkeysDistinct pulled :=
    ((toFin.append fromFin).append tail).pubkeysDistinct h.genesis
  have distinctC : PubkeysDistinct counted :=
    (toFin.append (fromFin.append tailC)).pubkeysDistinct h.genesis
  have eachC : ∀ L ∈ (List.range (nC + 1)).map LsC, L.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat :=
    fun L member => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp member
      obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyC j (by
        have := List.mem_range.mp hj
        omega)
      rw [hL]
      exact (sizeOf alt z.state).le
  have eachR : ∀ L ∈ (List.range' 2 (nR - 1)).map LsR,
      L.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat := fun L member => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp member
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyR j (by
      have := List.mem_range'_1.mp hj
      omega)
    rw [hL]
    exact (sizeOf alt z.state).le
  have cardC := listed_positions_card counted distinctC _ eachC
  have cardR := listed_positions_card pulled distinctR _ eachR
  rw [List.length_map, List.length_range] at cardC
  rw [List.length_map, List.length_range'] at cardR
  have keptR := (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1
  have keptC := (validatorKeys_prefix_and_distinct_of_chainSteps tailC.chainSteps).1
  have union_le := le_trans (Finset.card_union_le _ _) (Nat.add_le_add cardC cardR)
  refine le_trans (Finset.card_le_card ?_) (le_trans union_le ?_)
  · intro i member
    rcases Finset.mem_union.mp member with inV | inK
    · obtain ⟨-, w, j, found, hj, mem⟩ := debitC (eventsF ++ eventsC) replayedRC i
        (debitsC i inV)
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, w, found, LsC j,
          List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, mem⟩)
    · obtain ⟨-, w, j, found, hj, mem⟩ := debitR events replayed i (debitsR i inK)
      by_cases late : 2 ≤ j
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, w, found, LsR j,
            List.mem_map.mpr ⟨j, List.mem_range'_1.mpr (by omega), rfl⟩, mem⟩)
      · -- a seat of the first two committees: the key is at its position in the split
        have inSplit : w.pubkey ∈ validatorKeys split ∧
            ∃ L ∈ (List.range (nC + 1)).map LsC, w.pubkey ∈ L := by
          rcases Nat.lt_or_ge j 1 with zero | one
          · have j0 : j = 0 := by omega
            subst j0
            rw [firstR] at mem
            obtain ⟨L, hL, hLmem⟩ : ∃ L ∈ (List.range (nC + 1)).map LsC, L = Lcur := by
              obtain ⟨jc, hjc, e⟩ := firstC
              exact ⟨LsC jc, List.mem_map.mpr ⟨jc, List.mem_range.mpr (by omega), rfl⟩, e⟩
            exact ⟨keysSplit.1 w.pubkey mem, L, hL,
              by rw [hLmem]; exact mem⟩
          · have j1 : j = 1 := by omega
            subst j1
            have oneR : 1 ≤ nR := hj
            rw [secondR oneR] at mem
            obtain ⟨L, hL, hLmem⟩ : ∃ L ∈ (List.range (nC + 1)).map LsC, L = Lnext := by
              obtain ⟨jc, hjc, e⟩ := secondC oneR
              exact ⟨LsC jc, List.mem_map.mpr ⟨jc, List.mem_range.mpr (by omega), rfl⟩, e⟩
            exact ⟨keysSplit.2 w.pubkey mem, L, hL,
              by rw [hLmem]; exact mem⟩
        obtain ⟨inKeys, L, hL, hLmem⟩ := inSplit
        obtain ⟨v, foundS, sameS⟩ := position_in_prefix keptR distinctR inKeys found rfl
        obtain ⟨c, foundC, sameC⟩ := validators_getElem?_of_validatorKeys_prefix keptC foundS
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp foundC).1, c, foundC, L, hL,
            by rw [sameC, sameS]; exact hLmem⟩)
  · rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ arith

/-- The keys that a run from the split credits or debits through a sync seat.

They are at most its proposers, its seat holders and its deposit recipients.

A key counts if a block step of the run nets it a rise, or an epoch pass applies a deposit to it.

A block step has one proposer, and an epoch has at most one block for each slot.

The seat holders are those of one sync committee for each period that the run touches.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits.

A key that a sync aggregate debits holds a seat of the committee of its period. -/
private theorem banded_keys_le (h : Setting config checks g split fin pulled anc counted V)
    {x : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, x⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (keys : Finset ℕ) (banded : ∀ i ∈ keys, 0 < grossScan i high tail +
      (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail).1 +
        (events.map (syncDebit i)).sum) :
    keys.card ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
        preset.SYNC_COMMITTEE_SIZE.toNat *
          ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
              1) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have apart := h.parameters.lookahead
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have slots := h.twoSlots
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by omega
  have low : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch x).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have periodLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
  have periods : (getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
          (getCurrentEpoch split).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by omega
  obtain ⟨B, S, D, cardB, cardS, cardD, hBS, hD, hSD⟩ := credited_pieces h.genesis apart
    (y := ⟨fork, x⟩) h.early h.delay high
    ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    shared tail h.fulu periods
  have cardD' : D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) := cardD
  have subset : keys ⊆ B ∪ S ∪ D := fun i member => by
    have pos := banded i member
    by_cases net : 0 < grossScan i high tail
    · rcases hBS i net with inB | inS
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ inB)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ inS)
    · by_cases dep : 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high
          tail).1
      · exact Finset.mem_union_right _ (hD i dep)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hSD events replayed i (by omega)))
  -- The blocks of the run are at most one for each slot of its epochs.
  have blocks : tail.blockCount ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat := by
    have start : (getCurrentEpoch split).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        split.slot.toNat := by
      rw [getCurrentEpoch_toNat]
      exact Nat.div_mul_le_self _ _
    have finish : x.slot.toNat <
        ((getCurrentEpoch x).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
      rw [getCurrentEpoch_toNat]
      exact lt_of_lt_of_eq (Nat.lt_mul_div_succ _ positive) (Nat.mul_comm _ _)
    have last : x.slot.toNat ≤
        ((getCurrentEpoch x).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat - 1 := by omega
    have count := tail.blocks_le_slots (a := (getCurrentEpoch split).toNat *
      preset.SLOTS_PER_EPOCH.toNat) (b := ((getCurrentEpoch x).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat - 1) start last
    have gap := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (show (getCurrentEpoch split).toNat + 1 ≤ (getCurrentEpoch x).toNat + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at gap
    have shape : ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat = ((getCurrentEpoch x).toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat - (getCurrentEpoch split).toNat *
            preset.SLOTS_PER_EPOCH.toNat := by
      rw [← Nat.sub_mul]
      congr 1
      omega
    rw [shape]
    omega
  have total := (Finset.card_le_card subset).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have expand : ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
      (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) =
        ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
            ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) +
              preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by ring
  omega

/-- The keys that a run from the split credits.

They are at most its proposers, its seat holders and its deposit recipients. -/
private theorem credited_keys_le (h : Setting config checks g split fin pulled anc counted V)
    {x : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, x⟩) (high : ℕ) :
    ((Finset.range x.validators.data.size).filter fun i =>
        0 < grossScan i high tail +
          (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail).1).card ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
        preset.SYNC_COMMITTEE_SIZE.toNat *
          ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
              1) := by
  obtain ⟨events, replayed⟩ := tail.balanceEvents_ok h.early high
  exact banded_keys_le h tail high replayed _ fun i member => by
    have pos := (Finset.mem_filter.mp member).2
    omega

/-! ## The classes of keys and their costs -/

section Costs
variable (pulled counted : BeaconState preset fork) (V : Finset ValidatorIndex)

def AC := activeVoters counted
def AR := activeVoters pulled
def Q := quorumVoters counted
def U := Q counted ∪ AC counted ∪ AR pulled
def eC (v : ValidatorIndex) : ℕ := balanceAt counted v.toNat
def eR (v : ValidatorIndex) : ℕ := balanceAt pulled v.toNat

/-- V keys active in C: twice their fall. -/
def cV1 : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ V ∧ v ∈ AC counted then (eR pulled v : ℤ) - eC counted v else 0
/-- V keys not active in C: twice their stake at R. -/
def cV2 : ℤ := ∑ v ∈ U pulled counted, if v ∈ V ∧ v ∉ AC counted then (eR pulled v : ℤ) else 0
/-- (K4 pulled counted V), other keys active in both and counted in C: once their rise. -/
def cN : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AC counted ∧ v ∈ AR pulled ∧ v ∈ Q counted ∧ v ∉ V then
    (eC counted v : ℤ) - eR pulled v else 0
/-- (K5 counted V), other keys previous-epoch-only in C: three times their stake at C. -/
def cP : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ Q counted ∧ v ∉ AC counted ∧ v ∉ V then (eC counted v : ℤ) else 0
/-- (K6 pulled counted), keys counted in C and not active at R: once their stake at C. -/
def cJ : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AC counted ∧ v ∈ Q counted ∧ v ∉ AR pulled then (eC counted v : ℤ) else 0

/-- K7, keys active at C and outside its quorum (slashed at C): minus twice their stake at C, and
minus their stake at R if active there. -/
def cK7 : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AC counted ∧ v ∉ Q counted then
    -(2 * (eC counted v : ℤ)) - (if v ∈ AR pulled then (eR pulled v : ℤ) else 0) else 0
/-- cS, other keys active at R, not at C and outside C's quorum: minus their stake at R. -/
def cS : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AR pulled ∧ v ∉ AC counted ∧ v ∉ Q counted ∧ v ∉ V then -(eR pulled v : ℤ) else 0
def VN : Finset ValidatorIndex := V.filter (· ∉ AC counted)
def K4 : Finset ValidatorIndex := (AC counted).filter fun v => v ∈ AR pulled ∧ v ∈ Q counted ∧ v ∉ V
def K5 : Finset ValidatorIndex := (Q counted).filter fun v => v ∉ AC counted ∧ v ∉ V
def K6 : Finset ValidatorIndex := (AC counted).filter fun v => v ∈ Q counted ∧ v ∉ AR pulled
/-- SC, keys of R's registry unslashed at the split and slashed at C. -/
def SC (split : BeaconState preset fork) : Finset ValidatorIndex :=
  ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter fun v =>
    slashedFlagAt counted v.toNat = some true ∧ slashedFlagAt split v.toNat = some false

/-- Keys created beyond R's registry and slashed at C. -/
private def CS : Finset ValidatorIndex :=
  ((Finset.range counted.validators.data.size).image UInt64.ofNat).filter fun v =>
    pulled.validators.data.size ≤ v.toNat ∧ slashedFlagAt counted v.toNat = some true

end Costs

/-! ## Sums over validator indices, read at positions -/

/-- A sum over validator indices is at most the sum over a set of positions that holds them all.

An index is read at its position, `toNat` is injective, and the terms are natural numbers. -/
private theorem sum_toNat_le {S : Finset ValidatorIndex} {P : Finset ℕ} (f : ℕ → ℕ)
    (inside : ∀ v ∈ S, v.toNat ∈ P) : ∑ v ∈ S, f v.toNat ≤ ∑ i ∈ P, f i := by
  classical
  refine Finset.sum_le_sum_of_injOn (fun v : ValidatorIndex => v.toNat)
    (fun a _ b _ same => UInt64.toNat_inj.mp same) ?_ (fun _ _ => le_rfl)
    (fun _ _ _ => Nat.zero_le _)
  intro i hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  exact inside v hv

/-- A position that holds a validator and meets a test is among the positions that meet it. -/
private theorem mem_positions_filter (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) {i : ℕ} {w : Validator}
    (found : state.validators.data[i]? = some w) {p : ℕ → Prop} [DecidablePred p] (test : p i) :
    i ∈ (pinTerms config state ancestor finalizedState).positions.filter p :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, test⟩

/-- A flag read from the validator at a position can hold only where the position holds one.

The flag is the `any` of the validator, or its `map` read with a default of `false`. -/
private theorem validator_of_flag {state : BeaconState preset fork} {i : ℕ} {f : Validator → Bool}
    (flag : (state.validators.data[i]?).any f = true ∨
      ((state.validators.data[i]?).map f).getD false = true) :
    ∃ w, state.validators.data[i]? = some w := by
  cases found : state.validators.data[i]? with
  | none =>
    rw [found] at flag
    simp at flag
  | some w => exact ⟨w, rfl⟩

/-- A voter active at the epoch of a state holds a validator there that is active at that epoch. -/
private theorem active_of_activeVoters (early : fork < .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ activeVoters s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧
      isActiveValidator w (getCurrentEpoch s) = true := by
  have listed : v ∈ getActiveValidatorIndices s (getCurrentEpoch s) := by
    simpa [activeVoters] using member
  exact (mem_getActiveValidatorIndices (s.validators.bound early)).mp listed

/-! ## Per-term stubs -/

section Stubs
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-- A key active at C's epoch is activated by then at R, when that epoch is within the lookahead.

Activity up to the seed lookahead after the split is the same on both branches. -/
private theorem activation_le_of_active {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V)
    (bound : (getCurrentEpoch counted).toNat ≤
      anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat)
    {v : ValidatorIndex} (member : v ∈ AC counted) {w : Validator}
    (found : pulled.validators.data[v.toNat]? = some w) :
    w.activationEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  obtain ⟨u, foundU, activeU⟩ := active_of_activeVoters h.early member
  obtain ⟨rp⟩ := h.toPulled
  obtain ⟨rc⟩ := h.toCounted
  have fixed : getCurrentEpoch counted ≤ activityFixedEpoch split := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := (getCurrentEpoch counted).toNat_lt
    omega
  have kc := activeKept_of_chainSteps rc.chainSteps (getCurrentEpoch counted) fixed v.toNat
  have kp := activeKept_of_chainSteps rp.chainSteps (getCurrentEpoch counted) fixed v.toNat
  have activeAtC : isActiveAt counted (getCurrentEpoch counted) v.toNat = true :=
    isActiveAt_eq_true_iff.mpr ⟨u, foundU, activeU⟩
  have activeAtR : isActiveAt pulled (getCurrentEpoch counted) v.toNat = true := by
    rw [kp, ← kc]
    exact activeAtC
  obtain ⟨w', found', active⟩ := isActiveAt_eq_true_iff.mp activeAtR
  rw [found] at found'
  cases found'
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact UInt64.le_iff_toNat_le.mp active.1

/-- Glue: an unslashed V key active in C counts in C's quorum. -/
theorem glue_quorum (h : Setting config checks g split fin pulled anc counted V) :
    ∀ v ∈ V, v ∈ AC counted → v ∈ Q counted := by
  intro v member active
  have unslashed := (h.voting v member).2
  have listed : v ∈ getActiveValidatorIndices counted (getCurrentEpoch counted) := by
    simpa [AC, activeVoters] using active
  have inside := lt_size_of_mem_getActiveValidatorIndices listed
  have found : counted.validators.data[v.toNat]? = some counted.validators.data[v.toNat] :=
    Array.getElem?_eq_getElem inside
  have flag : ((counted.validators.data[v.toNat]?).map (·.slashed)).getD true = false := by
    simpa [slashedFlagAt, found] using unslashed
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append]
  exact ⟨.inl listed, flag⟩

/-- The two costs of V keys are the fall of those active in C and the stake of the others. -/
private theorem cV_split (h : Setting config checks g split fin pulled anc counted V) :
    cV1 pulled counted V + cV2 pulled counted V =
      ∑ v ∈ V.filter (· ∈ AC counted), ((eR pulled v : ℤ) - eC counted v) +
        ∑ v ∈ VN counted V, (eR pulled v : ℤ) := by
  classical
  have sub : V ⊆ U pulled counted := fun v hv =>
    Finset.mem_union_right _ (h.voting v hv).1
  unfold cV1 cV2 VN
  congr 1
  · rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨sub a, a, b⟩⟩
  · rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨sub a, a, b⟩⟩

/-- D-5/D-6 (fall, V) from its per-key facts.

The first fact is for a V key that is active in C: its fall and what C's floor leaves out.

The floor leaves out the key's sync debits from the finalized block, and their rounding band.

The second is for a V key that is not active in C: the same, and the charges that the sum names.

The shared run from the finalized block adds the key's sync debits to the sum.

C's tail adds its sync movement.
-/
private theorem stub_V_of (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)}
    (active : ∀ v ∈ V, v ∈ AC counted → (eR pulled v : ℤ) - eC counted v ≤
      ((pinTerms config pulled anc fin).fall v.toNat : ℤ) +
        ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat) +
          bandR (eventsF ++ eventsC) v.toNat)
    (left : ∀ v ∈ VN counted V, (eR pulled v : ℤ) ≤
      ((pinTerms config pulled anc fin).fall v.toNat +
        ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat) +
        bandR (eventsF ++ eventsC) v.toNat + exitQ tailC v.toNat +
        (if (pinTerms config pulled anc fin).exitingB v.toNat = true then eR pulled v else 0) +
        (if (pinTerms config pulled anc fin).lateB v.toNat = true then eR pulled v else 0) : ℕ)) :
    cV1 pulled counted V + cV2 pulled counted V ≤
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) +
        (∑ v ∈ V, ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat)) +
        (∑ v ∈ V, bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ (VN counted V), exitQ tailC v.toNat) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
          eR pulled v) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
          eR pulled v) : ℕ) := by
  classical
  rw [cV_split h]
  -- the bound of each key that does not depend on how it left
  let P : ValidatorIndex → ℕ := fun v =>
    (pinTerms config pulled anc fin).fall v.toNat +
      ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat) +
        bandR (eventsF ++ eventsC) v.toNat
  let X : ValidatorIndex → ℕ := fun v =>
    exitQ tailC v.toNat +
      (if (pinTerms config pulled anc fin).exitingB v.toNat = true then eR pulled v else 0) +
      (if (pinTerms config pulled anc fin).lateB v.toNat = true then eR pulled v else 0)
  have first : ∑ v ∈ V.filter (· ∈ AC counted), ((eR pulled v : ℤ) - eC counted v) ≤
      ∑ v ∈ V.filter (· ∈ AC counted), (P v : ℤ) := by
    refine Finset.sum_le_sum fun v hv => ?_
    obtain ⟨member, act⟩ := Finset.mem_filter.mp hv
    have := active v member act
    simp only [P]
    push_cast at this ⊢
    omega
  have second : ∑ v ∈ VN counted V, (eR pulled v : ℤ) ≤
      ∑ v ∈ VN counted V, ((P v : ℤ) + X v) := by
    refine Finset.sum_le_sum fun v hv => ?_
    have := left v hv
    simp only [P, X]
    push_cast at this ⊢
    omega
  have partition : ∑ v ∈ V, (P v : ℤ) =
      ∑ v ∈ V.filter (· ∈ AC counted), (P v : ℤ) + ∑ v ∈ VN counted V, (P v : ℤ) := by
    unfold VN
    exact (Finset.sum_filter_add_sum_filter_not V (· ∈ AC counted) _).symm
  have total : ∑ v ∈ V, (P v : ℤ) =
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) +
        (∑ v ∈ V, ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat)) +
        (∑ v ∈ V, bandR (eventsF ++ eventsC) v.toNat) : ℕ) := by
    simp only [P]
    push_cast
    simp only [Finset.sum_add_distrib]
  have exits : ∑ v ∈ VN counted V, (X v : ℤ) =
      ((∑ v ∈ (VN counted V), exitQ tailC v.toNat) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
          eR pulled v) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
          eR pulled v) : ℕ) := by
    simp only [X, Finset.sum_filter]
    push_cast
    simp only [Finset.sum_add_distrib]
  have split : ∑ v ∈ VN counted V, ((P v : ℤ) + X v) =
      ∑ v ∈ VN counted V, (P v : ℤ) + ∑ v ∈ VN counted V, (X v : ℤ) := Finset.sum_add_distrib
  push_cast at total exits ⊢
  omega

/-- A key that is unslashed at the end of a run is unslashed at its start.

A slashed validator stays slashed at its index along a run. -/
private theorem unslashed_of_run {x y : ForkedBeaconState preset} (run : Run config checks x y)
    {i : ℕ} {a : Validator} (found : x.state.validators.data[i]? = some a)
    (clean : ∀ w, y.state.validators.data[i]? = some w → w.slashed = false) :
    a.slashed = false := by
  cases flag : a.slashed
  · rfl
  · obtain ⟨u, read, marked⟩ := run.slashedPersistence i a found flag
    simp [clean u read] at marked

/-- The guards of the floor trace of a run from a state `zs` of the run from the finalized block.

The run ends at any state `y` that is at most one epoch after `pulled`.

The slashing quotient at `zs` is the guard's, which is positive.

The window of the slashing vector and the slashing quotient of each step are the guard's.

No upgrade runs from Fulu, so no step records a crossing.

It is the part of the floor of a key, on R's run and on C's, that does not read the key. -/
private theorem floor_guards (h : Setting config checks g split fin pulled anc counted V)
    {zs y : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (endpoint : (getCurrentEpoch y).toNat ≤ (getCurrentEpoch pulled).toNat + 1) :
    0 < DirectSafety.Apriori.minSlashingPenaltyQuotient preset
      (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩ (getCurrentEpoch pulled).toNat) ∧
    ∀ {m n : ForkedBeaconState preset}, Run config checks ⟨fork, zs⟩ m →
      ∀ step : Step config checks m n, Run config checks n ⟨fork, y⟩ →
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch zs).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      DirectSafety.Apriori.minSlashingPenaltyQuotient preset
        (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩
          (getCurrentEpoch pulled).toNat) ≤
        (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing := by
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finZ : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch zs).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have atFin := DirectSafety.Apriori.Internal.slashing_quotient_of_electra (config := config)
    (checks := checks) (high := (getCurrentEpoch pulled).toNat)
    (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) electra
  have atZ := DirectSafety.Apriori.Internal.slashing_quotient_of_electra (config := config)
    (checks := checks) (high := (getCurrentEpoch pulled).toNat)
    (Run.nil : Run config checks ⟨fork, zs⟩ ⟨fork, zs⟩) electra
  refine ⟨?_, fun before step after => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨_, _, _, _, _, _, _, quotient, _⟩ := h.guard
    rw [atZ, ← atFin]
    exact quotient
  · have window := DirectSafety.Apriori.Internal.short_window_of_guard h.guard endpoint
      ((Run.nil.snoc step).append after)
    simp only at window ⊢
    omega
  · exact (DirectSafety.Apriori.Internal.slashing_quotient_of_electra before electra).le
  · intro added addedOk
    exact DirectSafety.Apriori.Internal.no_crossing_of_regime (toFin.append pre) before
      h.genesis h.caps step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps after.chainSteps) h.early)
      (.inl (Nat.le_trans electra (fork_le_of_chainSteps before.chainSteps))) addedOk

/-- R's balance of a key that does not exit in the window falls only by its debit events.

The floor starts from the smaller of the key's balance at a state `zs` of R's run and its cap.

The state `zs` lies on R's run from the finalized block, and the rest of the run leads to `pulled`.

The guards of the floor trace come from the setting's guard at the finalized block.

The window of the slashing vector and the slashing quotient are the guard's.

No upgrade runs from Fulu, so no step records a crossing. -/
private theorem key_floorR_from (h : Setting config checks g split fin pulled anc counted V)
    {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : rest.balanceEvents high = .ok events)
    (i : ValidatorIndex) (val : Validator)
    (initial : zs.validators.data[i.toNat]? = some val) (unslashed : val.slashed = false)
    (stays : ∀ w, pulled.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, zs⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pulled⟩),
      (before.snoc step).append after = rest → ∀ w,
      n.state.validators.data[i.toNat]? = some w → high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u → high + 1 < u.withdrawableEpoch.toNat) :
    min (actualBalanceAt ⟨fork, zs⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat ≤
      actualBalanceAt ⟨fork, pulled⟩ i.toNat +
        (events.map (DirectSafety.Apriori.Internal.penaltyDebit i.toNat)).sum +
        (events.map (syncDebit i.toNat)).sum +
        (events.map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨positive, guards⟩ := floor_guards h pre (y := pulled) (Nat.le_succ _)
  refine Run.balanceFloor_events_or_fulu (toFin.append pre) rest h.genesis h.caps h.delay
    h.early high endEpoch i val initial unslashed (Or.inr h.fulu) _ positive ?_ stays replayed
  intro m n before step after cut w found
  exact ⟨retained before step after cut w found, guards before step after⟩

/-- R's balance of a key that does not exit in the window falls only by its debit events.

The floor starts from the smaller of the key's balance at the split and its largest balance.

The guards of the floor trace come from the setting's guard at the finalized block.

The window of the slashing vector and the slashing quotient are the guard's.

No upgrade runs from Fulu, so no step records a crossing. -/
private theorem key_floorR (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (i : ValidatorIndex) (val : Validator)
    (initial : split.validators.data[i.toNat]? = some val) (unslashed : val.slashed = false)
    (stays : ∀ w, pulled.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ m)
      (step : Step config checks m n) (post : Run config checks n ⟨fork, pulled⟩),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[i.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u → high + 1 < u.withdrawableEpoch.toNat) :
    min (actualBalanceAt ⟨fork, split⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat ≤
      actualBalanceAt ⟨fork, pulled⟩ i.toNat +
        (events.map (DirectSafety.Apriori.Internal.penaltyDebit i.toNat)).sum +
        (events.map (syncDebit i.toNat)).sum +
        (events.map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum := by
  obtain ⟨fromFin⟩ := h.fromFin
  exact key_floorR_from h fromFin tail high endEpoch replayed i val initial unslashed stays
    retained

/-- The floor debit of a replay is its penalties plus its sync debits. -/
private theorem floorPenaltyDebit_sum (i : ℕ) (events : List (BalanceEvent preset)) :
    (events.map (DirectSafety.Apriori.Internal.floorPenaltyDebit i)).sum =
      (events.map (DirectSafety.Apriori.Internal.penaltyDebit i)).sum +
        (events.map (syncDebit i)).sum := by
  rw [← List.sum_map_add]
  rfl

/-- A run's debit events and one slashing penalty bound the fall of a key's balance.

The run starts at a state `zs` of R's run from the finalized block.

It ends within one epoch after the call.

The floor starts from the smaller of the key's balance at `zs` and its largest balance.

Its effective balance stays at most `top` along the run.

The key is unslashed at `zs`.

Or it is slashed there, with its withdrawal at least the slashings vector past the finalized epoch.

Then its delayed penalty is not due along the run, since the window is shorter than half the vector.

The slashing penalty is then at most `top` over the slashing quotient, whenever the run slashes it.

The guards of the floor trace are `floor_guards`, from the setting's guard at the finalized block.

Nothing in the statement needs the key to be slashed, so it holds for a key that stays unslashed.

A step may assign the key's exit within the window, if its withdrawable epoch is beyond the window.

No upgrade runs from Fulu, so no step records a crossing. -/
private theorem slashed_floor (h : Setting config checks g split fin pulled anc counted V)
    {zs e : BeaconState preset fork}
    (toZ : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (tail : Run config checks ⟨fork, zs⟩ ⟨fork, e⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch e).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (i : ValidatorIndex) (val : Validator)
    (initial : zs.validators.data[i.toNat]? = some val)
    (slashedLate : val.slashed = true → (getCurrentEpoch fin).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ val.withdrawableEpoch.toNat)
    (top : ℕ)
    (envelope : ∀ z ∈ tail.balancePath, effectiveAt z i.toNat ≤ top)
    (retained : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks ⟨fork, zs⟩ m)
      (step : Step config checks m n) (post : Run config checks n ⟨fork, e⟩),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[i.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u → high + 1 < u.withdrawableEpoch.toNat) :
    min (actualBalanceAt ⟨fork, zs⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat ≤
      actualBalanceAt ⟨fork, e⟩ i.toNat +
        (events.map (DirectSafety.Apriori.Internal.penaltyDebit i.toNat)).sum +
        (events.map (syncDebit i.toNat)).sum +
        (events.map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum +
        top / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨positive, guards⟩ := floor_guards h toZ (y := e) near
  have member : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks ⟨fork, zs⟩ m)
      (step : Step config checks m n) (post : Run config checks n ⟨fork, e⟩),
      (pre.snoc step).append post = tail → m ∈ tail.balancePath := by
    intro m n pre step post cut
    obtain ⟨front, atEnd⟩ := Run.balancePath_last pre
    have path := Run.balancePath_append (pre.snoc step) post
    rw [cut] at path
    rw [path]
    simp [Run.balancePath, atEnd]
  have start : effectiveAt ⟨fork, zs⟩ i.toNat ≤ top := by
    obtain ⟨rest, atHead⟩ := Run.balancePath_head tail
    exact envelope _ (by rw [atHead]; exact List.mem_cons_self)
  obtain ⟨last, trace, balance, debt, -, w, final, -, -, -, ceiling, -⟩ :=
    DirectSafety.Apriori.Internal.FloorTrace.run_of_le_cap_general (toFin.append toZ) tail
      h.genesis h.caps h.delay h.early high endEpoch i val initial (Or.inr h.fulu)
      (min (actualBalanceAt ⟨fork, zs⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat) top _
      (Nat.min_le_right _ _) positive
      (fun pre step post cut w found =>
        ⟨retained pre step post cut w found,
          ⟨fun _ => (guards pre step post).1, fun s => by
            have window := DirectSafety.Apriori.Internal.short_window_of_guard h.guard near
              ((Run.nil.snoc step).append post)
            have late := slashedLate s
            simp only [UInt64.toNat_div, UInt64.reduceToNat] at window ⊢
            omega⟩,
          (guards pre step post).2⟩)
      replayed
  obtain ⟨-, below⟩ := ceiling top start fun pre step post cut =>
    envelope _ (member pre step post cut)
  have floor := DirectSafety.Apriori.Internal.FloorTrace.balance_floor_general trace
    (by simp)
  have penalty : last.slashedHigh.elim 0 (fun s =>
      top / DirectSafety.Apriori.minSlashingPenaltyQuotient preset
        (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩
          (getCurrentEpoch pulled).toNat) + (s - top)) ≤
      top / DirectSafety.Apriori.minSlashingPenaltyQuotient preset
        (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩
          (getCurrentEpoch pulled).toNat) := by
    cases flag : last.slashedHigh with
    | none => exact Nat.zero_le _
    | some s =>
      have capped := below s flag
      simp only [Option.elim]
      omega
  rw [balance, debt, floorPenaltyDebit_sum] at floor
  have same : DirectSafety.Apriori.minSlashingPenaltyQuotient preset
      (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩ (getCurrentEpoch pulled).toNat) =
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat :=
    DirectSafety.Apriori.Internal.slashing_quotient_of_electra (config := config)
      (checks := checks) (high := (getCurrentEpoch pulled).toNat)
      (Run.nil : Run config checks ⟨fork, zs⟩ ⟨fork, zs⟩) electra
  rw [← same]
  omega

/-- A state of the balance path of a run is the end of a prefix of the run.

The state inside a slot step comes after the epoch transition and before the upgrades.

It is the end of the step, since no fork upgrade runs when the fork does not rise. -/
private theorem balancePath_endpoint {x m y : ForkedBeaconState preset}
    (rp : Run config checks x m) (rest : Run config checks m y) (back : y.fork ≤ x.fork)
    {p : ForkedBeaconState preset} (member : p ∈ rp.balancePath) :
    ∃ (r1 : Run config checks x p) (r2 : Run config checks p y),
      r1.append r2 = rp.append rest := by
  rcases PinSplit.Run.mem_balancePath_split rp member with
    ⟨rq, rest', eq⟩ | ⟨q, n, rq, ok, rest', adv, eq, -, hp, up⟩
  · subst eq
    exact ⟨rq, rest'.append rest, Run.append_assoc _ _ _⟩
  · subst eq
    have order : n.fork ≤ q.fork :=
      Nat.le_trans (fork_le_of_chainSteps rest'.chainSteps)
        (Nat.le_trans (fork_le_of_chainSteps rest.chainSteps)
          (Nat.le_trans back (fork_le_of_chainSteps rq.chainSteps)))
    have same := processUpgrades_eq_of_fork_le up order
    have pn : p = n := hp.trans same.symm
    subst pn
    exact ⟨rq.snoc (Step.slot ok), rest'.append rest, Run.append_assoc _ _ _⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The guards of the floor trace of a segment of C's run.

The segment runs from `wS` to `pS`, and a run to the end `e` of C's run follows it.

The guards are `floor_guards`, with the exit guard `retained` of the segment.

The slashing quotient is the fork's, and the segment ends by the call's cutoff. -/
private theorem segment_guards (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork}
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (i : ValidatorIndex)
    {wS pS : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, wS⟩)
    (seg : Run config checks ⟨fork, wS⟩ ⟨fork, pS⟩) (rest : Run config checks ⟨fork, pS⟩ ⟨fork, e⟩)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat)) :
    (getCurrentEpoch pS).toNat ≤ (getCurrentEpoch pulled).toNat + 1 ∧
      ∃ quotient : ℕ, 0 < quotient ∧
        quotient = (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
        ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
          (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
          (before.snoc step).append after = seg → ∀ w,
          n.state.validators.data[i.toNat]? = some w →
          ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
            ∀ u, m.state.validators.data[i.toNat]? = some u →
              (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) ∧
          (getCurrentEpoch m.state).toNat < (getCurrentEpoch wS).toNat +
            preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
              (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
          quotient ≤
            (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
          ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing := by
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  simp only at order
  have endEpoch : (getCurrentEpoch pS).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  obtain ⟨positive, guards⟩ := floor_guards h (zs := wS) (y := pS) pre endEpoch
  exact ⟨endEpoch, _, positive,
    slashing_quotient_of_electra (high := (getCurrentEpoch pulled).toNat)
      (Run.nil : Run config checks ⟨fork, wS⟩ ⟨fork, wS⟩) (Nat.le_trans (by decide) h.fulu),
    fun before step after cut w found =>
      ⟨retained before step after cut w found, guards before step after⟩⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The potential floor of a segment of C's run, read at the state where the segment starts.

The segment runs from `wS` to `pS`.

A run from the finalized block to `wS` comes before it, and a run to the end `e` after it.

The key is unslashed at the end, and its exit is after the call's cutoff at each state of the run.

The rate bounds the pass penalties of each step by a fraction of its effective balance.

The closed form reads the balance and the cap of the key at the start of the segment. -/
private theorem segment_potential (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork}
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (i : ValidatorIndex)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    {wS pS : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, wS⟩)
    (seg : Run config checks ⟨fork, wS⟩ ⟨fork, pS⟩) (rest : Run config checks ⟨fork, pS⟩ ⟨fork, e⟩)
    (valW : Validator) (initialW : wS.validators.data[i.toNat]? = some valW)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd : ℕ)
    (start : effectiveAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ evs, step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    {segEvents : List (BalanceEvent preset)}
    (segOk : seg.balanceEvents (getCurrentEpoch pulled).toNat = .ok segEvents) :
    ∃ D, D + (segEvents.map (penaltyDebit i.toNat)).sum =
        (segEvents.map (floorPenaltyDebit i.toNat)).sum +
          (segEvents.map (floorPartialDebit i)).sum ∧
      (ρd - ρn * ((getCurrentEpoch pS).toNat - (getCurrentEpoch wS).toNat)) *
          (min (actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat)
              (withdrawalMaxEffectiveBalance preset fork valW).toNat +
            preset.downwardBand) ≤
        ρd * (actualBalanceAt (⟨fork, pS⟩ : ForkedBeaconState preset) i.toNat + D +
          preset.downwardBand) + ρn * slack := by
  obtain ⟨toFin⟩ := h.toFin
  have early : (⟨fork, pS⟩ : ForkedBeaconState preset).fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) h.early
  obtain ⟨endEpoch, quotient, positive, -, guards⟩ :=
    segment_guards h near i pre seg rest retained
  exact FloorTrace.run_potential_floor_once (toFin.append pre) seg h.genesis h.caps h.delay early
    h.fulu h.bands (getCurrentEpoch pulled).toNat endEpoch i valW initialW
    (fun w found => unslashed_of_run rest found clean) quotient positive guards segOk slack ρn ρd
    start pass

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The balance of a key at every prefix end of C's run is above `floor`.

The run is C's from the finalized block, and `floor` is below what the potential floor gives.

The potential floor is `segment_potential`, read at the end of each prefix from the finalized block.

The guards are `floor_guards`, with the exit guard `retained` and the pass rate `pass`.

The step `arith` is the arithmetic that fits the closed form of the potential floor to `floor`.

It holds for each epoch count up to C's.

It also holds for each debit that is at most the key's sync and partial debits over the run. -/
private theorem cfloor_balance (h : Setting config checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd floor : ℕ)
    (start : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ evs,
      step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    (arith : ∀ a D k : ℕ,
      k ≤ (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat →
      D ≤ (events.map (syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
      (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
          (withdrawalMaxEffectiveBalance preset fork val).toNat +
        preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
      floor ≤ a) :
    ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, e⟩), r1.append r2 = wholeRun →
      floor ≤ actualBalanceAt p i.toNat := by
  intro p r1 r2 whole
  obtain ⟨pFork, pState⟩ := p
  have sameFork : pFork = fork := Fork.ctorIdx_injective
    (Nat.le_antisymm (fork_le_of_chainSteps r2.chainSteps)
      (fork_le_of_chainSteps r1.chainSteps))
  obtain rfl : fork = pFork := sameFork.symm
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
  simp only at order
  have nonDecreasing := UInt64.le_iff_toNat_le.mp
    (currentEpoch_le_of_chainSteps r1.chainSteps)
  simp only at nonDecreasing
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix r1 r2
    (getCurrentEpoch pulled).toNat events (by rw [whole]; exact replayed)
  obtain ⟨D, split, closed⟩ := segment_potential h near i clean Run.nil r1 r2 val initial
    (fun before' step after cut' w found => retained before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) w found)
    slack ρn ρd start
    (fun before' step after cut' evs ok => pass before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) evs ok)
    beforeOk
  have splitDebit := floorPenaltyDebit_sum i.toNat before
  obtain ⟨rest', rfl⟩ := isPrefix
  have syncSum : ((before ++ rest').map (syncDebit i.toNat)).sum =
      (before.map (syncDebit i.toNat)).sum + (rest'.map (syncDebit i.toNat)).sum := by
    simp only [List.map_append, List.sum_append]
  have partialSum : ((before ++ rest').map (floorPartialDebit i)).sum =
      (before.map (floorPartialDebit i)).sum + (rest'.map (floorPartialDebit i)).sum := by
    simp only [List.map_append, List.sum_append]
  have window : (getCurrentEpoch pState).toNat - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat :=
    Nat.sub_le_sub_right order _
  exact arith _ D _ window (by omega) closed

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at a prefix end of C's run is the finalized one or an update's.

An update is at a state of the prefix.

There the effective balance is aligned and at most the balance. -/
private theorem cfloor_origin (h : Setting config checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
    (r2 : Run config checks p ⟨fork, e⟩) (whole : r1.append r2 = wholeRun) :
    effectiveAt p i.toNat = effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ∨
      ∃ (w : ForkedBeaconState preset) (pre : Run config checks ⟨fork, fin⟩ w)
          (post : Run config checks w p),
        pre.append post = r1 ∧ effectiveAt p i.toNat = effectiveAt w i.toNat ∧
          effectiveAt w i.toNat ≤ actualBalanceAt w i.toNat ∧
          effectiveAt w i.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨pFork, pState⟩ := p
  have sameFork : pFork = fork := Fork.ctorIdx_injective
    (Nat.le_antisymm (fork_le_of_chainSteps r2.chainSteps) (fork_le_of_chainSteps r1.chainSteps))
  obtain rfl : fork = pFork := sameFork.symm
  have early : (⟨fork, pState⟩ : ForkedBeaconState preset).fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  obtain ⟨before, beforeOk, -⟩ := Run.balanceEvents_prefix r1 r2
    (getCurrentEpoch pulled).toNat events (by rw [whole]; exact replayed)
  obtain ⟨endEpoch, quotient, positive, -, guards⟩ := segment_guards h near i
    Run.nil r1 r2 (fun before' step after cut' w found => retained before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) w found)
  exact FloorTrace.run_effective_origin toFin r1 h.genesis h.caps h.delay early h.fulu h.aligned
    (getCurrentEpoch pulled).toNat endEpoch i val initial (fun w found => unslashed_of_run r2 found
      clean) quotient positive guards beforeOk

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at a state of C's run is above a least value.

The balance of the key at every prefix end is above `floor`, by `cfloor_balance`.

The effective balance of the key at the end of a prefix is then at least a least value.

That value is the least of its effective balance and its cap at the finalized block.

And of `floor` rounded down to an increment. -/
private theorem cfloor_endpoint (h : Setting config checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd floor : ℕ)
    (start : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ evs,
      step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    (arith : ∀ a D k : ℕ,
      k ≤ (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat →
      D ≤ (events.map (syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
      (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
          (withdrawalMaxEffectiveBalance preset fork val).toNat +
        preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
      floor ≤ a)
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, e⟩) (cut : rp.append rest = wholeRun) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt z i.toNat := by
  have forkEnd : ∀ {p : ForkedBeaconState preset} (r2 : Run config checks p ⟨fork, e⟩),
      p.fork < .glamsterdam := fun r2 =>
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  -- the balance at the end of each prefix of the run is above `floor`
  have endpointFloor : ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, e⟩), r1.append r2 = wholeRun →
      floor ≤ actualBalanceAt p i.toNat := fun r1 r2 whole =>
    cfloor_balance h e wholeRun near replayed i val initial clean retained slack ρn ρd floor start
      pass arith r1 r2 whole
  have pathEndpoint : ∀ {p : ForkedBeaconState preset}, p ∈ rp.balancePath →
      ∃ (r1 : Run config checks ⟨fork, fin⟩ p) (r2 : Run config checks p ⟨fork, e⟩),
        r1.append r2 = wholeRun := fun member => by
    obtain ⟨r1, r2, whole⟩ := balancePath_endpoint rp rest (Nat.le_refl _) member
    exact ⟨r1, r2, whole.trans cut⟩
  have inside : i.toNat < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp initial).1
  refine PinSplit2.Run.effective_floor_rounded rp (forkEnd rest) h.fulu i.toNat inside floor
    (withdrawalMaxEffectiveBalance preset fork val).toNat ?_ ?_
  · intro p member
    obtain ⟨r1, r2, whole⟩ := pathEndpoint member
    exact endpointFloor r1 r2 whole
  · intro p member
    obtain ⟨r1, r2, -⟩ := pathEndpoint member
    obtain ⟨w, found, mono⟩ := r1.validatorCap_mono h.caps.activation h.caps.compounding
      (forkEnd r2) i.toNat val initial
    simpa [PinSplit2.capAt, found] using UInt64.le_iff_toNat_le.mp mono

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key's effective balance on C's run is above the floor of its fall.

The run starts at the finalized block, and the bound holds at each state of it.

It is above that floor less the key's sync debits and their band.

The floor starts from the smaller of the key's balance and its cap at the finalized block.

It falls by what `fall` charges, in `X`: the leak and the gain over the depth, and the partials.

If the test of `fall` holds, the balance stays within a band of the envelope.

Then the effective balance stays at its finalized value, by `stay`.

Otherwise the floor is rounded down to an increment, by `cfloor_endpoint`.

The hypothesis `margin` fits the closed form of the potential floor to the floor of the fall.

The hypothesis `stay` keeps the effective balance at its finalized value if the test holds.

It is `floorC_stay`, for a key with no sync debits. -/
private theorem floorC_at (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, counted.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (base0 X low finEB floorC : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (hfin : finEB = effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    (hfloorC : floorC = if max finEB base0 ≤ low + preset.downwardBand then finEB
      else min finEB (low - low % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC)
    (margin : ∃ slack ρn ρd : ℕ,
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          (preset.downwardBand + slack) ∧
      (∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
        (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
        (before.snoc step).append after = fromFin.append tailC → ∀ evs,
        step.balanceEvents = .ok evs →
        (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd) ∧
      ∀ a D k : ℕ, k ≤ (getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat →
        D ≤ (events.map (syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
        (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
            (withdrawalMaxEffectiveBalance preset fork val).toNat +
          preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
        low - (events.map (syncDebit i.toNat)).sum ≤ a)
    (stay : max finEB base0 ≤ low + preset.downwardBand →
      (events.map (syncDebit i.toNat)).sum = 0 → finEB ≤ effectiveAt z i.toNat) :
    floorC ≤ effectiveAt z i.toNat + (events.map (syncDebit i.toNat)).sum +
      bandR events i.toNat := by
  obtain ⟨slack, ρn, ρd, start, pass, arith⟩ := margin
  have eff := cfloor_endpoint h counted (fromFin.append tailC) h.near replayed i val initial clean
    retained slack ρn ρd
    (low - (events.map (syncDebit i.toNat)).sum) start pass arith rp rest cut
  have incPos := h.bands.1
  have bandEq := bandR_eq events i.toNat
  have lowLe : low ≤ (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    have := Nat.min_le_right (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat
    omega
  rw [hfloorC]
  rw [← hfin] at eff
  have lowMod := Nat.mod_lt low incPos
  have lowModLe := Nat.mod_le low preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  rcases Nat.eq_zero_or_pos (events.map (syncDebit i.toNat)).sum with zero | positive
  · have same : low - (events.map (syncDebit i.toNat)).sum = low := by omega
    rw [same] at eff
    have noBand : bandR events i.toNat = 0 := by
      rw [bandEq]
      simp [zero]
    split
    · next test =>
      have kept := stay test zero
      omega
    · omega
  · have mod := Nat.mod_lt (low - (events.map (syncDebit i.toNat)).sum) incPos
    have band : bandR events i.toNat =
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 := by
      rw [bandEq]
      simp [positive]
    split <;> omega

/-- If `X * S * b + K * a * b ≤ K * a * X`, then the floors `q` and `P` of `X` over `a` and `b`
satisfy `q * S ≤ P * K`. -/
private theorem rate_final {X a b q P K S : ℕ} (hq : q * a ≤ X) (hP : X < (P + 1) * b)
    (ha : 0 < a) (hK : 0 < K)
    (key : X * S * b + K * a * b ≤ K * a * X) : q * S ≤ P * K := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h] at hP
    · exact h
  have h1 : q * S * (a * b) ≤ X * S * b := by
    calc q * S * (a * b) = (q * a) * (S * b) := by ring
      _ ≤ X * (S * b) := Nat.mul_le_mul_right _ hq
      _ = X * S * b := by ring
  have h2 : K * a * X < K * a * ((P + 1) * b) := by
    rw [Nat.mul_lt_mul_left (Nat.mul_pos hK ha)]
    exact hP
  have h3 : q * S * (a * b) < P * K * (a * b) := by nlinarith [h1, h2, key]
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right h3)

/-- Below eighteen increments of the pulled total, a fifth of an increment gives the pin's rate. -/
private theorem rate_small_key {X I a b K S M : ℕ} (hI : 10 ^ 8 ≤ I) (hIX : I ≤ X)
    (hM1 : K * I ≤ M) (hM : I ≤ M) (ha' : M < (a + 1) * (a + 1))
    (hb : b * b ≤ I / 5) (hb' : I / 5 < (b + 1) * (b + 1)) (hK : 1 ≤ K)
    (hS : 2 * S ≤ 3 * K + 2) :
    X * S * b + K * a * b ≤ K * a * X := by
  have hS2 : S ≤ 2 * K := by omega
  have hb5 : 5 * (b * b) ≤ I := by omega
  have hb4472 : 4472 ≤ b := by
    by_contra h
    have : b + 1 ≤ 4472 := by omega
    have : (b + 1) * (b + 1) ≤ 4472 * 4472 := Nat.mul_le_mul this this
    omega
  have ha1e4 : 10 ^ 4 ≤ a := by
    by_contra h
    have : a + 1 ≤ 10 ^ 4 := by omega
    have : (a + 1) * (a + 1) ≤ 10 ^ 4 * 10 ^ 4 := Nat.mul_le_mul this this
    omega
  -- `a² > 4.999 K b²`
  have shift : 10 ^ 4 * (a + 1) ≤ 10001 * a := by omega
  have sq : 10 ^ 4 * (a + 1) * (10 ^ 4 * (a + 1)) ≤ 10001 * a * (10001 * a) :=
    Nat.mul_le_mul shift shift
  have kb : 5 * K * (b * b) ≤ M := by
    have : K * (5 * (b * b)) ≤ K * I := Nat.mul_le_mul_left K hb5
    nlinarith
  have big : 500000000 * K * (b * b) < 100020001 * (a * a) := by nlinarith
  have kb1 : b * b ≤ K * (b * b) := by nlinarith
  have h40 : 40 * b ≤ 19 * a := by
    by_contra h
    have h' : 19 * a < 40 * b := by omega
    have := Nat.mul_self_lt_mul_self h'
    nlinarith
  have h20 : 20 * S * b ≤ 19 * K * a := by
    calc 20 * S * b ≤ 20 * (2 * K) * b := by
          have := Nat.mul_le_mul_right b (Nat.mul_le_mul_left 20 hS2)
          exact this
      _ = K * (40 * b) := by ring
      _ ≤ K * (19 * a) := Nat.mul_le_mul_left K h40
      _ = 19 * K * a := by ring
  have h20b : 20 * b ≤ X := by
    have : 20 * b ≤ b * b := Nat.mul_le_mul_right b (by omega)
    omega
  have e1 : X * (20 * S * b) ≤ X * (19 * K * a) := Nat.mul_le_mul_left X h20
  have e2 : K * a * (20 * b) ≤ K * a * X := Nat.mul_le_mul_left (K * a) h20b
  nlinarith [e1, e2]

/-- Three of the terms that the floors leave are small against `K * a * X`, for a large total. -/
private theorem rate_big_common {X K a : ℕ} (hK : 12 ≤ K) (s2 : 1000 ≤ a) (hX : 2 ^ 35 ≤ X) :
    1000 * (144 * K * X) ≤ 144 * (K * a * X) ∧ 12000 * (96 * X) ≤ 96 * (K * a * X) ∧
      2 ^ 28 * (96 * K * a) ≤ K * a * X := by
  have Ka : 12000 ≤ K * a := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_left (144 * K * X) s2
    linarith
  · have := Nat.mul_le_mul_left (96 * X) Ka
    linarith
  · have h96 : 2 ^ 28 * 96 ≤ X := by omega
    have := Nat.mul_le_mul_left (K * a) h96
    linarith

/-- With at least `2 ^ 20` increments, the terms that the floors leave fit in `13 * K * a * X`. -/
private theorem rate_big_large {X K a : ℕ} (hK : 2 ^ 20 ≤ K) (s2 : 1000 ≤ a) (hX : 2 ^ 35 ≤ X)
    (s3' : 8 * a ≤ X) :
    144 * K * X + 98 * a * X + 96 * X + 98 * K * a * a + 96 * K * a ≤ 13 * K * a * X := by
  obtain ⟨f1, f2, f3⟩ := rate_big_common (K := K) (by omega) s2 hX
  have f4 : 2 ^ 20 * (98 * a * X) ≤ 98 * (K * a * X) := by
    have := Nat.mul_le_mul_right (98 * a * X) hK
    linarith
  have f5 : 8 * (98 * K * a * a) ≤ 98 * K * a * X := by
    have := Nat.mul_le_mul_left (98 * K * a) s3'
    linarith
  have hu : 0 ≤ K * a * X := Nat.zero_le _
  linarith

/-- With fewer than `2 ^ 20` increments, the terms that the floors leave fit in `13 * K * a * X`. -/
private theorem rate_big_small {X K a : ℕ} (hK : 12 ≤ K) (small : K + 1 ≤ 2 ^ 20) (s2 : 1000 ≤ a)
    (hX : 2 ^ 35 ≤ X) (s4 : a * a < (K + 1) * X) :
    144 * K * X + 98 * a * X + 96 * X + 98 * K * a * a + 96 * K * a ≤ 13 * K * a * X := by
  obtain ⟨f1, f2, f3⟩ := rate_big_common hK s2 hX
  have g4 : 12 * (98 * a * X) ≤ 98 * (K * a * X) := by
    have := Nat.mul_le_mul_right (98 * a * X) hK
    linarith
  have g5 : 490 * a ≤ 3 * X := by
    by_contra h
    have h' : 3 * X < 490 * a := by omega
    have h2 := Nat.mul_self_lt_mul_self h'
    have h3 : a * a < 2 ^ 20 * X := by
      have := Nat.mul_le_mul_right X small
      nlinarith
    have h4 : 9 * X * X < 240100 * 2 ^ 20 * X := by nlinarith
    have h5 : 9 * X < 240100 * 2 ^ 20 := by
      exact Nat.lt_of_mul_lt_mul_right h4
    omega
  have g6 : 490 * K * a * a ≤ 3 * K * a * X := by
    have := Nat.mul_le_mul_left (K * a) g5
    linarith
  have hu : 0 ≤ K * a * X := Nat.zero_le _
  linarith

/-- From eighteen increments of the pulled total, a quarter of it gives the pin's rate. -/
private theorem rate_big_key {X I a b K S M T : ℕ} (hX : 2 ^ 35 ≤ X) (hIX : I ≤ X) (hI : 10 ^ 8 ≤ I)
    (hK : 12 ≤ K) (hM1 : K * I ≤ M) (hM2 : M < (K + 1) * I) (ha : a * a ≤ M)
    (ha' : M < (a + 1) * (a + 1)) (hMhi : M < 2 ^ 64) (hb : 4 * (b * b) ≤ T)
    (hT : 2 * T ≤ 3 * M) (hS : 2 * S ≤ 3 * K + 2) :
    X * S * b + K * a * b ≤ K * a * X := by
  have s1 : 80 * b ≤ 49 * a + 48 := by
    by_contra h
    have h1 : 49 * (a + 1) ≤ 80 * b := by omega
    have h2 := Nat.mul_le_mul h1 h1
    nlinarith
  have s2 : 1000 ≤ a := by
    by_contra h
    have h1 : a + 1 ≤ 1000 := by omega
    have h2 := Nat.mul_le_mul h1 h1
    nlinarith
  have s3 : a < 2 ^ 32 := by
    by_contra h
    have h1 : 2 ^ 32 ≤ a := by omega
    have h2 := Nat.mul_le_mul h1 h1
    nlinarith
  have s3' : 8 * a ≤ X := by omega
  have s4 : a * a < (K + 1) * X := by
    have := Nat.mul_le_mul_left (K + 1) hIX
    omega
  have T2 : 144 * K * X + 98 * a * X + 96 * X + 98 * K * a * a + 96 * K * a ≤
      13 * K * a * X := by
    by_cases large : 2 ^ 20 ≤ K
    · exact rate_big_large large s2 hX s3'
    · exact rate_big_small hK (by omega) s2 hX s4
  have e1 : (3 * K + 2) * X * (80 * b) ≤ (3 * K + 2) * X * (49 * a + 48) :=
    Nat.mul_le_mul_left _ s1
  have e2 : 2 * K * a * (80 * b) ≤ 2 * K * a * (49 * a + 48) := Nat.mul_le_mul_left _ s1
  have e3 : 2 * S * (X * b) ≤ (3 * K + 2) * (X * b) := Nat.mul_le_mul_right _ hS
  nlinarith [e1, e2, e3, T2]

/-- The reward per increment at the total, times the previous stake's increments, is at most the
pin's rate times the total's increments. -/
private theorem rate_arith {I c M T S : ℕ} (scale : 2 ^ 35 ≤ I * c) (size : 10 ^ 8 ≤ I)
    (factor : 1 ≤ c)
    (clamp : I ≤ M) (high : M < 2 ^ 64) (band : 2 * T ≤ 3 * M) (stake : 2 * S ≤ 3 * M) :
    I * c / Nat.sqrt M * (S / I) ≤
      I * c / Nat.sqrt (if 18 * I ≤ T then T / 4 else I / 5) * (M / I) := by
  have hI : 0 < I := by omega
  have hIX : I ≤ I * c := Nat.le_mul_of_pos_right I factor
  have hK1 : M / I * I ≤ M := Nat.div_mul_le_self M I
  have hK2 : M < (M / I + 1) * I := by
    have := Nat.lt_mul_div_succ M hI
    rw [Nat.mul_comm] at this
    exact this
  have hK0 : 1 ≤ M / I := (Nat.le_div_iff_mul_le hI).mpr (by omega)
  have hS : 2 * (S / I) ≤ 3 * (M / I) + 2 := by
    have h1 : S / I * I ≤ S := Nat.div_mul_le_self S I
    have h2 : 2 * (S / I) * I < 3 * (M / I + 1) * I := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right h2
    omega
  have ha := Nat.sqrt_le M
  have ha' := Nat.lt_succ_sqrt M
  have apos : 0 < Nat.sqrt M := Nat.sqrt_pos.mpr (by omega)
  by_cases big : 18 * I ≤ T
  · simp only [big, ↓reduceIte]
    have bpos : 0 < Nat.sqrt (T / 4) := Nat.sqrt_pos.mpr (by omega)
    have hb := Nat.sqrt_le (T / 4)
    have hK12 : 12 ≤ M / I := (Nat.le_div_iff_mul_le hI).mpr (by omega)
    refine rate_final (Nat.div_mul_le_self _ _) ?_ apos (by omega)
      (rate_big_key (a := Nat.sqrt M) (b := Nat.sqrt (T / 4)) scale hIX size hK12 hK1 hK2 ha
        ha' high (by omega) band hS)
    exact (Nat.lt_mul_div_succ (I * c) bpos).trans_eq (Nat.mul_comm _ _)
  · simp only [big, ↓reduceIte]
    have bpos : 0 < Nat.sqrt (I / 5) := Nat.sqrt_pos.mpr (by omega)
    have hb := Nat.sqrt_le (I / 5)
    have hb' := Nat.lt_succ_sqrt (I / 5)
    refine rate_final (Nat.div_mul_le_self _ _) ?_ apos (by omega)
      (rate_small_key (a := Nat.sqrt M) (b := Nat.sqrt (I / 5)) size hIX hK1 clamp ha' hb hb'
        hK0 hS)
    exact (Nat.lt_mul_div_succ (I * c) bpos).trans_eq (Nat.mul_comm _ _)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- From Electra and before Gloas, the previous epoch's active stake of a state reached from a
guarded state in its window is within three halves of its total. -/
private theorem prevStake_band_of_guard {g x z : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (toZ : Run config checks x z) (zEarly : z.fork < .glamsterdam)
    (zWithin : (getCurrentEpoch z.state).toNat ≤ high + 1) {total : Gwei}
    (totalOk : getTotalActiveBalance z.state = .ok total) :
    2 * ∑ i ∈ (getActiveValidatorIndices z.state (getPreviousEpoch z.state)).toFinset,
        effectiveAt z i.toNat ≤ 3 * total.toNat := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by
    simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ratioGuard, -⟩ := id guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  obtain ⟨low, -⟩ := total_within_guard shared genesis parameters caps aligned twoSlots electra
    guard toZ zEarly zWithin totalOk
  obtain ⟨-, previous, -⟩ := ceilingFloor_electra shared toZ high
    ⟨genesis, parameters, caps, aligned, zEarly, zWithin, guard⟩ twoSlots electra
  have index : ix x z ≤ high + 1 - (getCurrentEpoch x.state).toNat := by
    simp only [ix]
    omega
  have mono := stakeCeilingAt_mono (config := config) (x := x) (high := high) electra index
  simp only [stakeCeilingAt, stakeFloorAt, zero] at low previous mono ⊢
  omega

/-- The reward per increment at a state of a run from the finalized state is at most the pin's rate.

It is read times the increments active at the previous epoch or at the current one.

The pin's rate is read times the active increments. -/
private theorem rate_of_guard
    (h : Setting config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork} (toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩)
    (inside : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {epoch : Epoch} (which : epoch = getPreviousEpoch m ∨ epoch = getCurrentEpoch m)
    {pq : Gwei} (pqOk : getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq) :
    ∀ total perIncrement : Gwei, getTotalActiveBalance m = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat *
          ((∑ i ∈ (getActiveValidatorIndices m epoch).toFinset,
            effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        pq.toNat * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  intro total perIncrement totalOk perOk
  obtain ⟨T, pulledOk⟩ := h.pulledTotal
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have toP := fromFin.append toPulled
  have band := total_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
    electra h.guard toM h.early inside toP h.early (Nat.le_succ _)
    totalOk pulledOk
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  have stake : 2 * ∑ i ∈ (getActiveValidatorIndices m epoch).toFinset,
      effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat ≤ 3 * total.toNat := by
    rcases which with rfl | rfl
    · exact prevStake_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
        electra h.guard toM h.early inside totalOk
    · have current := le_max_right preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (stake (fun index => balanceAt m index.toNat)
          (getActiveValidatorIndices m (getCurrentEpoch m)).toFinset)
      rw [← value] at current
      exact Nat.le_trans (Nat.mul_le_mul_left 2 current) (Nat.mul_le_mul_right _ (by omega))
  have clamp : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ total.toNat := by
    rw [value]
    exact le_max_left _ _
  have high : total.toNat < 2 ^ 64 := total.toNat_lt
  rw [toNat_getBaseRewardPerIncrement perOk]
  simp only [pulledOk, Except.toOption, Option.getD_some] at pqOk
  rw [toNat_getBaseRewardPerIncrement pqOk]
  have quarter : ((if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei)).toNat =
      if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T.toNat / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT.toNat / 5 := by
    split <;> simp [UInt64.toNat_div]
  rw [quarter]
  exact rate_arith h.facts.rewardScale h.facts.incrementSize h.facts.reward clamp high band stake

/-- Adding `S` to a number loses at most `U` of rounding down to a multiple of `inc`.

That holds if `S` is zero, or if `U` is at least `inc - 1`.

It also holds if `S` is below `inc` and `S + U` reaches `inc`.

A shift below `inc` moves the rounded value by `inc` or by nothing. -/
private theorem round_add_le {inc x S U : ℕ} (incPos : 0 < inc)
    (slack : S = 0 ∨ inc ≤ U + 1 ∨ (S < inc ∧ inc ≤ S + U)) :
    x + S - (x + S) % inc ≤ x - x % inc + S + U := by
  have := Nat.mod_lt x incPos
  have := Nat.mod_lt (x + S) incPos
  have := Nat.mod_le x inc
  have := Nat.mod_le (x + S) inc
  rcases slack with z | big | ⟨small, need⟩
  · subst z; simp only [Nat.add_zero]; omega
  · omega
  · have up : (x + S) / inc ≤ x / inc + 1 :=
      (Nat.div_le_div_right (by omega : x + S ≤ x + inc)).trans (Nat.add_div_right x incPos).le
    have := Nat.mul_le_mul_left inc up
    rw [Nat.mul_add, Nat.mul_one] at this
    have := Nat.div_add_mod x inc
    have := Nat.div_add_mod (x + S) inc
    omega

/-- The effective balance of a key that stays on its path is at most the rise of the main regime. -/
private theorem rise_arith {inc band capFor high finEB start eR eC Bc capHigh S U : Nat}
    (incPos : 0 < inc)
    (stay : eC = eR ∨ (eC ≤ Bc + band ∧ eC ≤ max start (min (Bc - Bc % inc) capHigh)))
    (startLe : start ≤ max finEB ((high + S) - (high + S) % inc))
    (aligned : eC % inc = 0) (capped : eC ≤ capFor + S + U) (ceiling : Bc ≤ high + S)
    (slack : S = 0 ∨ inc ≤ U + 1 ∨ (S < inc ∧ inc ≤ S + U)) :
    eC ≤ eR + (min capFor (min (high + band - (high + band) % inc)
      (max finEB (high - high % inc))) - eR) + S + U := by
  rcases stay with same | ⟨boundary, update⟩
  · omega
  · have alignedLe : ∀ x, eC ≤ x → eC ≤ x - x % inc := fun x le => by
      have := rounded_mono inc le
      rw [aligned] at this
      simpa using this
    have first := alignedLe _ (show eC ≤ high + band + S by omega)
    have second : eC ≤ max finEB (high - high % inc) + S + U := by
      have r := rounded_mono inc ceiling
      have b := round_add_le (x := high) incPos slack
      omega
    have third : eC ≤ high + band - (high + band) % inc + S + U := by
      have b := round_add_le (x := high + band) incPos slack
      omega
    omega

/-- A key's effective balance on C's branch is at most the cap that `capFor` reads. -/
private theorem key_capped {g : ForkedBeaconState preset}
    {counted : BeaconState preset fork} (run : Run config checks g ⟨fork, counted⟩)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : fork < .glamsterdam) (electra : .pectra ≤ fork) (i : ℕ) {vC vR : Validator}
    (foundC : counted.validators.data[i]? = some vC) {capFor : ℕ}
    (cases : capFor = preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat ∨
      (capFor = (withdrawalMaxEffectiveBalance preset fork vR).toNat ∧
        (hasCompoundingWithdrawalCredential vC = true →
          hasCompoundingWithdrawalCredential vR = true))) :
    effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i ≤ capFor := by
  rcases cases with high | ⟨low, frozen⟩
  · rw [high]
    exact PinSplit5.effectiveAt_le_capMax run genesis caps early i
  · have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax run genesis caps
      early foundC
    rw [low]
    exact le_trans capped
      (UInt64.le_iff_toNat_le.mp (PinSplit.withdrawalMax_le electra electra caps frozen))

/-- The effective balance at the end of a run is at most the rounded bound on its balance.

The run starts at a state where the key's effective balance is within the largest one.

`Run.effective_floor_pair` bounds the balance at every state by `creditBound`, given the right `E`.

`E` is at least the effective balances that the bound allows.

Then the update of the effective balances reads that bound as its ceiling. -/
private theorem key_credit_ceiling {n y : ForkedBeaconState preset}
    (post : Run config checks n y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ n.fork)
    (i : ℕ) (inside : i < n.state.validators.data.size) (high P E : ℕ)
    (aligned : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt n i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (capCeil : ∀ z ∈ post.balancePath,
      PinSplit2.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (rate : ∀ z ∈ post.balancePath,
      i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) ∨
      ∀ total perIncrement : Gwei,
        getTotalActiveBalance z.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
          (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (fixpoint : max (effectiveAt n i) (min preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      (PinSplit2.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
        PinSplit2.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E) :
    effectiveAt y i ≤ max (effectiveAt n i) (min
      (PinSplit2.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
        PinSplit2.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) := by
  obtain ⟨-, -, third, fourth⟩ := PinSplit2.Run.effective_floor_pair post early fulu i inside 0 0
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat high E P
  have balances := fourth aligned startCap capCeil rate endEpoch fixpoint
  exact (third _ aligned startCap
    (fun z member => balances z member) capCeil).1

/-- Rounding down after adding an amount adds at most its whole increments.

The base is first raised by one increment less one, which covers the rest of the amount. -/
private theorem rounded_add_floor_le (I x y : ℕ) (hI : 0 < I) :
    (x + y) - (x + y) % I ≤ (x + I - 1) - (x + I - 1) % I + I * (y / I) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < I ∧ y = I * q + r :=
    ⟨y / I, y % I, Nat.mod_lt _ hI, (Nat.div_add_mod y I).symm⟩
  have quotient : (I * q + r) / I = q := by
    rw [Nat.mul_add_div hI, Nat.div_eq_of_lt hr, Nat.add_zero]
  have shifted : x + (I * q + r) = (x + r) + I * q := by ring
  have modulo : ((x + r) + I * q) % I = (x + r) % I := Nat.add_mul_mod_self_left _ _ _
  have mono := rounded_mono I (show x + r ≤ x + I - 1 by omega)
  rw [quotient, shifted, modulo]
  omega

/-- A cap above the activation balance belongs to a validator with compounding credentials. -/
private theorem compounding_of_cap {z : ForkedBeaconState preset} {i : ℕ}
    (electra : .pectra ≤ z.fork)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt z i) :
    ∃ v, z.state.validators.data[i]? = some v ∧ hasCompoundingWithdrawalCredential v = true := by
  unfold PinSplit2.capAt at large
  cases found : z.state.validators.data[i]? with
  | none => simp [found] at large
  | some v =>
    refine ⟨v, rfl, ?_⟩
    by_contra not
    have plain : hasCompoundingWithdrawalCredential v = false := by simpa using not
    simp [found, withdrawalMaxEffectiveBalance, electra, getMaxEffectiveBalance, plain] at large

/-- The cap of a validator is the largest effective balance if it compounds.

Otherwise it is the activation balance. -/
private theorem capAt_of_found {z : ForkedBeaconState preset} {i : ℕ} {v : Validator}
    (electra : .pectra ≤ z.fork) (found : z.state.validators.data[i]? = some v) :
    PinSplit2.capAt z i = if hasCompoundingWithdrawalCredential v = true then
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat else preset.MIN_ACTIVATION_BALANCE.toNat := by
  unfold PinSplit2.capAt
  rw [found]
  by_cases compounds : hasCompoundingWithdrawalCredential v = true <;>
    simp [withdrawalMaxEffectiveBalance, electra, getMaxEffectiveBalance, compounds]

/-- The activation balance and the largest balance are whole numbers of increments. -/
private theorem cap_values_aligned (aligned : MaxEffectiveBalancesAligned preset) :
    preset.MIN_ACTIVATION_BALANCE.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
  ⟨by simpa [UInt64.toNat_mod] using congrArg UInt64.toNat aligned.2.1,
    by simpa [UInt64.toNat_mod] using congrArg UInt64.toNat aligned.2.2⟩

/-- A key's cap is a whole number of increments. -/
private theorem capAt_aligned (aligned : MaxEffectiveBalancesAligned preset)
    {z : ForkedBeaconState preset} (electra : .pectra ≤ z.fork) {i : ℕ} {w : Validator}
    (found : z.state.validators.data[i]? = some w) :
    PinSplit2.capAt z i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  rw [capAt_of_found electra found]
  have values := cap_values_aligned aligned
  split <;> first | exact values.1 | exact values.2

/-- From Fusaka, a slot step before Gloas keeps whether each validator of its first state compounds.

It keeps the position of each such validator. -/
private theorem slot_compounding_kept {m n : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks m = .ok n) (fulu : .fusaka ≤ m.fork)
    (early : n.fork < .glamsterdam) {i : ℕ} {v : Validator}
    (found : m.state.validators.data[i]? = some v) :
    ∃ w, n.state.validators.data[i]? = some w ∧
      hasCompoundingWithdrawalCredential w = hasCompoundingWithdrawalCredential v := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  obtain rfl := DirectSafety.Apriori.Internal.processUpgrades_eq_of_window upgraded fulu early
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advancedOk
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  rcases epochIfLast_cases epochedOk with ⟨_, epochOk⟩ | ⟨_, rfl⟩
  · have altair : .altair ≤ m.fork := Nat.le_trans (by decide) fulu
    simp only [processEpoch, altair, ↓reduceDIte] at epochOk
    obtain ⟨later, laterFound, same⟩ := processEpochAltair_credentials epochOk found
    exact ⟨later, laterFound, by unfold hasCompoundingWithdrawalCredential; rw [same]⟩
  · exact ⟨v, found, rfl⟩

/-- A consolidation request keeps whether a validator compounds.

Otherwise it makes the validator compound and leaves its balance within the activation balance. -/
private theorem consolidationRequest_flip {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    {key : ValidatorIndex} {v : Validator} (found : s.validators.data[key.toNat]? = some v) :
    ∃ w, t.validators.data[key.toNat]? = some w ∧
      (hasCompoundingWithdrawalCredential w = hasCompoundingWithdrawalCredential v ∨
        (hasCompoundingWithdrawalCredential w = true ∧
          actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) key.toNat ≤
            preset.MIN_ACTIVATION_BALANCE.toNat)) := by
  obtain ⟨conv, ledger, -⟩ := BlockLedger.ledger_processConsolidationRequest ok
  by_cases member : key ∈ conv
  · obtain ⟨w, located, compounds⟩ := ledger.switched key member
    have capped := ledger.converted key member
    exact ⟨w, located, .inr ⟨compounds, by simpa using capped⟩⟩
  · obtain ⟨w, located, same⟩ := ledger.kept key v member found
    exact ⟨w, located, .inl same⟩

/-- A fold of consolidation requests that each record an excess event.

The balance of a key rises by at most the credits of the events.

The key may switch from plain to compounding credentials in the fold.

Then it ends within the activation balance plus the credits of the events. -/
private theorem excess_fold {electra : .pectra ≤ fork}
    (lim : ConsolidationRequest → BeaconState preset fork → Except TransitionError (ℕ × ℕ))
    (key : ValidatorIndex) :
    ∀ (requests : List ConsolidationRequest) (r rN : BeaconState preset fork)
      (E E' : List (BalanceEvent preset)),
      requests.foldlM (fun pre request => recordBalance .excess (lim request)
        (processConsolidationRequest config · electra request) pre) (r, E) = .ok (rN, E') →
      ∃ Ec : List (BalanceEvent preset), E' = E ++ Ec ∧
        actualBalanceAt (⟨fork, rN⟩ : ForkedBeaconState preset) key.toNat ≤
          actualBalanceAt (⟨fork, r⟩ : ForkedBeaconState preset) key.toNat +
            (Ec.map (keyCredit key.toNat)).sum ∧
        ∀ v, r.validators.data[key.toNat]? = some v →
          hasCompoundingWithdrawalCredential v = false → ∀ w,
          rN.validators.data[key.toNat]? = some w → hasCompoundingWithdrawalCredential w = true →
            actualBalanceAt (⟨fork, rN⟩ : ForkedBeaconState preset) key.toNat ≤
              preset.MIN_ACTIVATION_BALANCE.toNat + (Ec.map (keyCredit key.toNat)).sum := by
  intro requests
  induction requests with
  | nil =>
    intro r rN E E' ok
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    refine ⟨[], by simp, by simp, fun v found plain w foundW switched => ?_⟩
    have same := Option.some.inj (found.symm.trans foundW)
    subst same
    exact absurd (switched.symm.trans plain) (by decide)
  | cons request rest ih =>
    intro r rN E E' ok
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨⟨after, recorded⟩, step, others⟩ := ok
    obtain ⟨credit, debit, -, actionOk, rfl⟩ :=
      DirectSafety.Apriori.Internal.recordBalance_single step
    obtain ⟨Ec, rfl, rise, later⟩ := ih after rN _ E' others
    refine ⟨⟨.excess, ⟨fork, r⟩, ⟨fork, after⟩, credit, debit⟩ :: Ec, by simp, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, keyCredit]
      omega
    · intro v found plain w foundW switched
      obtain ⟨v', found', changed⟩ := consolidationRequest_flip actionOk found
      rcases changed with same | ⟨_, capped⟩
      · have bound := later v' found' (same.trans plain) w foundW switched
        simp only [List.map_cons, List.sum_cons, keyCredit]
        omega
      · simp only [List.map_cons, List.sum_cons, keyCredit]
        omega

/-- Whether each validator compounds is the same at two states. -/
private def CompKept {f : Fork} (s t : BeaconState preset f) : Prop :=
  ∀ (v : ValidatorIndex) (validator : Validator), s.validators.data[v.toNat]? = some validator →
    ∃ later, t.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator

private theorem CompKept.trans {f : Fork} {s u t : BeaconState preset f} (one : CompKept s u)
    (two : CompKept u t) : CompKept s t := fun v validator located => by
  obtain ⟨middle, middleFound, same⟩ := one v validator located
  obtain ⟨later, laterFound, same'⟩ := two v middle middleFound
  exact ⟨later, laterFound, same'.trans same⟩

private theorem CompKept.of_ledger {f : Fork} {s t : BeaconState preset f}
    {paid : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (ledger : BlockLedger.Ledger s t paid ∅ sync other slash) : CompKept s t :=
  fun v validator located => ledger.kept v validator (Finset.notMem_empty v) located

/-- From Fulu and before Gloas, a block's replay leaves a switched key within activation balance.

The key switches by a consolidation request.

The events after the switch then add their credits. -/
private theorem block_flip_balance {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    {events : List (BalanceEvent preset)} (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (matched : BalancesMatch s)
    (replayed : blockBalanceReplay (config := config) (checks := checks) early engine s block =
      .ok (t, events))
    (key : ValidatorIndex) {v w : Validator} (found : s.validators.data[key.toNat]? = some v)
    (plain : hasCompoundingWithdrawalCredential v = false)
    (foundT : t.validators.data[key.toNat]? = some w)
    (switched : hasCompoundingWithdrawalCredential w = true) :
    actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) key.toNat ≤
      preset.MIN_ACTIVATION_BALANCE.toNat + (events.map (keyCredit key.toNat)).sum := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) fulu
  unfold blockBalanceReplay at replayed
  dsimp only at replayed
  obtain ⟨⟨u1, E1⟩, h1, replayed⟩ := bind_ok_iff.mp replayed
  rw [dite_eq_left_of_eq_true (eq_true bellatrix)] at replayed
  obtain ⟨⟨u2, E2⟩, h2, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u3, E3⟩, h3, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u4, E4⟩, h4, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨_, -, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨_, -, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p5, h5, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p6, h6, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p7, h7, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p8, h8, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u9, E9⟩, h9, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u10, E10⟩, h10, replayed⟩ := bind_ok_iff.mp replayed
  rw [dite_eq_left_of_eq_true (eq_true electra)] at replayed
  obtain ⟨⟨u11, E11⟩, h11, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u12, E12⟩, h12, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨rN, E13⟩, hfold, replayed⟩ := bind_ok_iff.mp replayed
  rw [dite_eq_left_of_eq_true (eq_true altair)] at replayed
  -- The states before the consolidation requests.
  obtain ⟨hu1, -⟩ := PinSplit4.carryBalance_cases h1
  obtain ⟨_, _, -, hu2, -⟩ := DirectSafety.Apriori.Internal.recordBalance_single h2
  obtain ⟨hu3, -⟩ := PinSplit4.carryBalance_cases h3
  obtain ⟨hu4, -⟩ := PinSplit4.carryBalance_cases h4
  have f5 := record_fold_state _ _ _ _ _ _ h5
  have f6 := record_fold_state _ _ _ _ _ _ h6
  have f7 := record_fold_state _ _ _ _ _ _ h7
  have f8 := record_fold_state _ _ _ _ _ _ h8
  obtain ⟨hu9, -⟩ := PinSplit4.carryBalance_cases h9
  obtain ⟨hu10, -⟩ := PinSplit4.carryBalance_cases h10
  obtain ⟨hu11, -⟩ := PinSplit4.carryBalance_cases h11
  obtain ⟨hu12, -⟩ := PinSplit4.carryBalance_cases h12
  have matchedInput : BalancesMatch u4 :=
    ((frame_processBlockHeader hu1).toFrame.trans
      ((frame_processBlockExecution hu2).toFrame.trans
        ((frame_processRandao hu3).toFrame.trans
          (frame_processEth1Data hu4).toFrame))).balancesMatch matched
  obtain ⟨_, executed, -⟩ := BlockLedger.ledger_processBlockExecution early hu2
  have toInput : CompKept s u4 :=
    (CompKept.of_ledger (BlockLedger.ledger_processBlockHeader hu1)).trans <|
      (CompKept.of_ledger executed).trans <|
        (CompKept.of_ledger (BlockLedger.ledger_processRandao hu3)).trans
          (CompKept.of_ledger (BlockLedger.ledger_processEth1Data hu4))
  have toRequests : CompKept u4 u12 := BlockCredits.compoundingKept_beforeConsolidations
    early fulu electra matchedInput f5 f6 f7 f8 (by rw [Array.foldlM_toList]; exact hu9) hu10
    (by rw [Array.foldlM_toList]; exact hu11) (by rw [Array.foldlM_toList]; exact hu12)
  obtain ⟨v0, found0, same0⟩ := (toInput.trans toRequests) key v found
  -- The consolidation requests, then the sync aggregate.
  obtain ⟨Ec, rfl, -, switchedBound⟩ := excess_fold (electra := electra) _ key _ _ _ _ _ hfold
  obtain ⟨_, _, -, hu, rfl⟩ := DirectSafety.Apriori.Internal.recordBalance_single replayed
  have kept := (BlockLedger.processSyncAggregate_kept hu).1
  rw [kept] at foundT
  have bound := switchedBound v0 found0 (same0.trans plain) w foundT switched
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, keyCredit]
  omega

/-- A step makes a key compound.

It leaves the balance of the key within the activation balance plus the credits of the step. -/
private theorem step_flip_balance {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork) (invariant : Invariant m.state)
    (i : ℕ) (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt n i) :
    actualBalanceAt n i ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
      stepCredit (fun _ => true) (fun _ => true) i step := by
  obtain ⟨events, replayed⟩ := step.balanceEvents_ok early
  have base := PinSplit2.step_balance_le_events step early i replayed
  have credit : stepCredit (fun _ => true) (fun _ => true) i step =
      (events.map (keyCredit i)).sum := by
    cases step <;> simp [stepCredit, replayed, Except.toOption]
  rw [credit]
  have electraM : .pectra ≤ m.fork := Nat.le_trans (by decide) fulu
  have electraN : .pectra ≤ n.fork := Nat.le_trans electraM step.chainStep.fork_le
  obtain ⟨w, foundN, switched⟩ := compounding_of_cap electraN large
  have strict : preset.MIN_ACTIVATION_BALANCE.toNat <
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
    rw [capAt_of_found electraN foundN, switched] at large
    simpa using large
  cases found : m.state.validators.data[i]? with
  | none =>
    have out := Array.getElem?_eq_none_iff.mp found
    have sizes := invariant.balancesMatch
    unfold BalancesMatch at sizes
    have zero : actualBalanceAt m i = 0 := by
      simp [actualBalanceAt,
        Array.getElem?_eq_none (show m.state.balances.data.size ≤ i by omega)]
    omega
  | some v =>
    have plain : hasCompoundingWithdrawalCredential v = false := by
      by_contra compounds
      have yes : hasCompoundingWithdrawalCredential v = true := by simpa using compounds
      rw [capAt_of_found electraM found, yes] at flat
      simp at flat
      omega
    cases step with
    | slot ok =>
      obtain ⟨w', found', same⟩ := slot_compounding_kept ok fulu early found
      have equal := Option.some.inj (found'.symm.trans foundN)
      subst equal
      simp [switched, plain] at same
    | @block f s t engine signed due ok =>
      have replay := Step.balanceEvents_block (fork := f) early replayed
      have limit := s.registryWithinLimit_of_lt early
      unfold BeaconState.RegistryWithinLimit at limit
      have inside : i < s.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
      have bound := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
      obtain ⟨key, hkey⟩ : ∃ key : ValidatorIndex, key.toNat = i :=
        ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)⟩
      subst hkey
      exact block_flip_balance (fork := f) early fulu invariant.balancesMatch replay key found
        plain foundN switched

/-- A step that makes a key compound leaves its balance within the smaller of two bounds.

Those are its balance before the step and the activation balance, each plus the credits of the step.

Both bounds add the same credits, so the smaller of the two bases carries them. -/
private theorem step_flip_min {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork) (invariant : Invariant m.state)
    (i : ℕ) (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt n i) :
    actualBalanceAt n i ≤ min (actualBalanceAt m i) preset.MIN_ACTIVATION_BALANCE.toNat +
      stepCredit (fun _ => true) (fun _ => true) i step := by
  obtain ⟨events, replayed⟩ := step.balanceEvents_ok early
  have base := PinSplit2.step_balance_le_events step early i replayed
  have credit : stepCredit (fun _ => true) (fun _ => true) i step =
      (events.map (keyCredit i)).sum := by
    cases step <;> simp [stepCredit, replayed, Except.toOption]
  have flip := step_flip_balance step early fulu invariant i flat large
  rw [credit] at flip ⊢
  omega

/-- A step that makes a registered key compound is not a slot step.

A slot step keeps whether each validator of its first state compounds. -/
private theorem step_flip_not_slot {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork)
    (i : ℕ) (inside : i < m.state.validators.data.size)
    (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt n i) :
    ∀ ok : advanceSlotAcross config checks m = .ok n, step ≠ Step.slot ok := by
  intro ok same
  subst same
  have electraM : .pectra ≤ m.fork := Nat.le_trans (by decide) fulu
  have electraN : .pectra ≤ n.fork := Nat.le_trans electraM (Step.slot ok).chainStep.fork_le
  obtain ⟨v, found⟩ : ∃ v, m.state.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨w, foundN, switched⟩ := compounding_of_cap electraN large
  have strict : preset.MIN_ACTIVATION_BALANCE.toNat <
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
    have large' := large
    rw [capAt_of_found electraN foundN, switched] at large'
    simpa using large'
  have plain : hasCompoundingWithdrawalCredential v = false := by
    by_contra compounds
    have yes : hasCompoundingWithdrawalCredential v = true := by simpa using compounds
    rw [capAt_of_found electraM found, yes] at flat
    simp at flat
    omega
  obtain ⟨w', found', same⟩ := slot_compounding_kept ok fulu early found
  have equal := Option.some.inj (found'.symm.trans foundN)
  subst equal
  simp [switched, plain] at same

/-- A step that makes a registered key compound stays in its epoch.

It is a block step, and a block keeps the slot. -/
private theorem step_flip_epoch {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork)
    (i : ℕ) (inside : i < m.state.validators.data.size)
    (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt n i) :
    (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat := by
  cases step with
  | slot ok =>
    exact absurd rfl (step_flip_not_slot (Step.slot ok) early fulu i inside flat large ok)
  | @block f s t engine signed due ok =>
    obtain ⟨-, processed, -⟩ := applySignedBlock_ok ok
    have slot := (frame_processBlock processed).slot
    simp only [getCurrentEpoch, slot]

/-- A run from a key with plain credentials to a key with compounding credentials splits at a step.

The step makes the key compound.

It leaves the balance of the key within the activation balance plus the credits of the step.

If the key is in the registry of the first state, the step does not cross an epoch. -/
private theorem Run.flip_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork) (invariant : Invariant x.state)
    (i : ℕ) (flat : PinSplit2.capAt x i ≤ preset.MIN_ACTIVATION_BALANCE.toNat)
    (compounding : preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt y i) :
    ∃ (m n : ForkedBeaconState preset) (pre : Run config checks x m) (step : Step config checks m n)
      (post : Run config checks n y),
      (pre.snoc step).append post = tail ∧
      PinSplit2.capAt m i ≤ preset.MIN_ACTIVATION_BALANCE.toNat ∧
      preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt n i ∧
      actualBalanceAt n i ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
        stepCredit (fun _ => true) (fun _ => true) i step ∧
      (i < x.state.validators.data.size →
        (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat) := by
  obtain ⟨m, n, pre, step, post, split, notYet, arrived⟩ := Run.split_at_flip tail
    (fun z => preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt z i)
    (show ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt x i by omega) compounding
  have before : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt m i := notYet
  have after : preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt n i := arrived
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have earlyN : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  exact ⟨m, n, pre, step, post, split.symm, Nat.le_of_not_lt before, after,
    step_flip_balance step earlyN fuluM (Run.invariant invariant pre) i before after,
    fun inside => step_flip_epoch step earlyN fuluM i
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)) before after⟩

/-- The penalty rate of a rewards pass at a state of a run from the finalized state is at most the
pin's leak rate at the key's effective balance there. -/
private theorem passRate_le_leakAt (h : Setting config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork} (toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩)
    (inside : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {total : Gwei} (totalOk : getTotalActiveBalance m = .ok total)
    {pq : Gwei} (pqOk : getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq) (v : ℕ) :
    passPenaltyRate config (⟨fork, m⟩ : ForkedBeaconState preset) v ≤
      (pinTerms config pulled anc fin).leakAt (effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) v)
        v := by
  obtain ⟨T, pulledOk⟩ := h.pulledTotal
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have toP := fromFin.append toPulled
  have aligned : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣
      effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) v :=
    Nat.dvd_of_mod_eq_zero
      (DirectSafety.Apriori.Internal.FloorTrace.effective_aligned (shared.append toM) h.genesis
        h.aligned v)
  have bandTotal := total_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
    electra h.guard toM h.early inside toP h.early (Nat.le_succ _) totalOk pulledOk
  have band : 2 * T.toNat ≤ 3 * activeBalanceTotal m := by
    rw [← getTotalActiveBalance_toNat totalOk]
    exact bandTotal
  have fromFinEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
  simp only at fromFinEpoch
  have scored : (if altair : .altair ≤ fork then
        (((m.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤
      (if altair : .altair ≤ fork then
        (((fin.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        config.INACTIVITY_SCORE_BIAS.toNat := by
    simp only [altair, ↓reduceDIte]
    have depth : (getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat + 1 ≤
        (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
    have times := Nat.mul_le_mul_right config.INACTIVITY_SCORE_BIAS.toNat depth
    cases read : (m.inactivityScores altair).data[v]? with
    | none =>
      simp only [Option.map_none, Option.getD_none, Nat.zero_add]
      refine le_trans ?_ (Nat.le_add_left _ _)
      rw [Nat.add_mul, Nat.one_mul] at times
      omega
    | some score =>
      have grown := DirectSafety.Apriori.Internal.runScore_le_start toM altair h.early
        (.inl electra) altair (i := v) read
      simp only [Option.map_some, Option.getD_some]
      rw [Nat.add_mul, Nat.one_mul] at times
      simp only at grown
      rw [Nat.mul_comm (_ - _)] at times
      nlinarith
  have key := PinSplit2.passPenaltyRate_le_leak (config := config)
    (⟨fork, m⟩ : ForkedBeaconState preset) v T.toNat _ h.facts.incrementSize h.facts.room
    T.toNat_lt aligned band scored
  dsimp only at key
  refine Nat.le_trans (Nat.le_of_eq rfl) (Nat.le_trans key ?_)
  simp only [pinTerms]
  have totalRead : (getTotalActiveBalance pulled).toOption.getD 0 = T := by
    rw [pulledOk]
    rfl
  rw [totalRead] at pqOk ⊢
  rw [pqOk]
  simp only [Except.toOption, Option.getD_some]
  have quarter : ((if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei)).toNat =
      if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T.toNat / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT.toNat / 5 := by
    split <;> simp [UInt64.toNat_div]
  have perIncrement := toNat_getBaseRewardPerIncrement pqOk
  rw [quarter] at perIncrement
  refine Nat.le_of_eq ?_
  rw [perIncrement]

/-- The pending keys of `pinTerms` are validators of R's registry.

Each is not yet eligible at R's epoch, and has no activation epoch. -/
private theorem pendingRB_iff (config : Config) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) : (pinTerms config pulled anc fin).pendingRB i = true ↔
      ∃ w, pulled.validators.data[i]? = some w ∧
        (getCurrentEpoch pulled).toNat < w.activationEligibilityEpoch.toNat ∧
        w.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [pinTerms]
  cases pulled.validators.data[i]? <;> simp

/-- The late keys of `pinTerms` are validators of R's registry.

Each has an eligibility epoch by R's epoch.

Its activation epoch is beyond the seed lookahead of the finalized epoch. -/
private theorem lateB_iff (config : Config) (pulled anc fin : BeaconState preset fork) (i : ℕ) :
    (pinTerms config pulled anc fin).lateB i = true ↔ ∃ w, pulled.validators.data[i]? = some w ∧
      w.activationEligibilityEpoch.toNat ≤ (getCurrentEpoch pulled).toNat ∧
      anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
        w.activationEpoch.toNat := by
  simp only [pinTerms]
  cases pulled.validators.data[i]? <;> simp

/-- The keys of `pinTerms` whose exit R reads are validators of R's registry.

Each is active in R's previous epoch or its current one, and unslashed or recently slashed.

Its exit epoch is at most one after R's epoch. -/
private theorem exitingB_iff (config : Config) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) : (pinTerms config pulled anc fin).exitingB i = true ↔
      ∃ w, pulled.validators.data[i]? = some w ∧
        (isActiveAt pulled (getPreviousEpoch pulled) i = true ∨
          isActiveAt pulled (getCurrentEpoch pulled) i = true) ∧
        (w.slashed = false ∨ anc.finalizedCheckpoint.epoch.toNat +
          preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ w.withdrawableEpoch.toNat) ∧
        w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
  simp only [pinTerms]
  rcases Option.eq_none_or_eq_some (pulled.validators.data[i]?) with none | ⟨w, some⟩
  · simp [none]
  · simp [some]

/-- The keys of `pinTerms` whose exit R holds are validators of R's registry.

Each exit was set after the finalized epoch, and R's epoch is past it. -/
private theorem exitedRB_iff (config : Config) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) : (pinTerms config pulled anc fin).exitedRB i = true ↔
      ∃ w, pulled.validators.data[i]? = some w ∧
        anc.finalizedCheckpoint.epoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
          w.exitEpoch.toNat ∧ w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch pulled).toNat := by
  simp only [pinTerms]
  cases pulled.validators.data[i]? <;> simp

/-- Activity up to the seed lookahead after the split is the same at R and C. -/
private theorem activity_shared {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) {e : Epoch}
    (fixed : e.toNat ≤ (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat)
    (i : ℕ) : isActiveAt pulled e i = isActiveAt counted e i := by
  obtain ⟨rp⟩ := h.toPulled
  obtain ⟨rc⟩ := h.toCounted
  have inside : e ≤ activityFixedEpoch split := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := e.toNat_lt
    omega
  exact (activeKept_of_chainSteps rp.chainSteps e inside i).trans
    (activeKept_of_chainSteps rc.chainSteps e inside i).symm

/-- The finalized epoch of R is at most its current epoch. -/
private theorem finalized_le_current {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) :
    pulled.finalizedCheckpoint.epoch ≤ getCurrentEpoch pulled := by
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  have valid := Run.invariant (Genesis.invariant h.genesis) ((rf.append rs).append rp)
  exact UInt64.le_trans valid.ordered.1 (UInt64.le_trans valid.ordered.2
    (UInt64.le_trans valid.settled (getPreviousEpoch_le pulled)))

/-- A key of `K6` in R's registry has no exit, or an exit after the split's lookahead.

An exit at or before the split's epoch plus the seed lookahead is on the shared prefix of the runs.

Both runs then agree on the key's activity up to that exit, so C would not count the key.

The records of the key at R and at C, and what they say of its activity, are the premises. -/
private theorem K6_exit_late {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) {v : ValidatorIndex}
    {w u : Validator} (found : pulled.validators.data[v.toNat]? = some w)
    (rActive : ∀ e : Epoch, isActiveAt pulled e v.toNat = true ↔
      (w.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < w.exitEpoch.toNat))
    (cActive : ∀ e : Epoch, isActiveAt counted e v.toNat = true ↔
      (u.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < u.exitEpoch.toNat))
    (uExit : (getCurrentEpoch counted).toNat < u.exitEpoch.toNat)
    (notActive : ¬ (w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat ∧
      (getCurrentEpoch pulled).toNat < w.exitEpoch.toNat)) :
    w.exitEpoch = FAR_FUTURE_EPOCH ∨
      (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < w.exitEpoch.toNat := by
  by_cases far : w.exitEpoch = FAR_FUTURE_EPOCH
  · exact .inl far
  refine .inr ?_
  by_contra early
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  have gap := Run.exit_activation_gap ((rf.append rs).append rp) h.genesis v.toNat w found far
  have called := UInt64.le_iff_toNat_le.mp h.called
  have later := UInt64.le_iff_toNat_le.mp h.later
  have shareA := activity_shared h (e := w.activationEpoch) (by omega) v.toNat
  have shareX := activity_shared h (e := w.exitEpoch) (by omega) v.toNat
  have activeA : isActiveAt pulled w.activationEpoch v.toNat = true :=
    (rActive _).mpr ⟨Nat.le_refl _, by omega⟩
  have atA := (cActive _).mp (shareA.symm.trans activeA)
  have notX : ¬ isActiveAt counted w.exitEpoch v.toNat = true := by
    rw [← shareX]
    intro active
    have := (rActive _).mp active
    omega
  have ended := mt (cActive w.exitEpoch).mpr notX
  omega

/-- A key of the split's registry that R has withdrawable by the finalized epoch is not charged.

The charge would be on C's tail.

Its exit is at most its withdrawable epoch, so R's exit is assigned by the finalized epoch.

An exit assigned after the split is at least the split's epoch plus one and the seed lookahead.

So the split already holds the exit, and a run never charges an exit twice. -/
private theorem no_charge_of_settled {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {i : ℕ} {w : Validator}
    (inside : i < split.validators.data.size) (found : pulled.validators.data[i]? = some w)
    (settled : w.withdrawableEpoch.toNat ≤ anc.finalizedCheckpoint.epoch.toNat) :
    ∀ c ∈ tailC.departureCharges, c.index ≠ i := by
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  have valid := Run.invariant (Genesis.invariant h.genesis) ((rf.append rs).append rp)
  have ordered := UInt64.le_iff_toNat_le.mp
    (valid.exitsOrdered w (Array.mem_of_getElem? found))
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots split
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have oldFound := Array.getElem?_eq_getElem inside
  have assigned : split.validators.data[i].exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro unset
    have wAssigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro far
      rw [far, farNat] at ordered
      omega
    obtain ⟨c, member, -, epoch⟩ := rp.departure_charge_of_assigned i _ w oldFound found unset
      wAssigned
    have late : (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
      DirectSafety.Run.departureCharges_epoch_ge_start rp (Nat.le_trans (by decide) h.fulu)
        h.early c member
    omega
  intro c member
  exact tailC.departure_charge_ne_of_assigned i _ oldFound assigned c member

/-- A key counted in C and inactive at R, read at R's record, is in one of five classes.

It joins at R's next epoch.

Or it activates late, has exited at R, is exiting at R, or is not yet eligible at R. -/
private theorem K6_class {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) {v : ValidatorIndex}
    (member : v ∈ K6 pulled counted) {w : Validator}
    (found : pulled.validators.data[v.toNat]? = some w) :
    (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true) ∨
      (pinTerms config pulled anc fin).lateB v.toNat = true ∨
      (pinTerms config pulled anc fin).exitedRB v.toNat = true ∨
      (pinTerms config pulled anc fin).exitingB v.toNat = true ∨
      (pinTerms config pulled anc fin).pendingRB v.toNat = true := by
  classical
  obtain ⟨memberAC, memberQ, notAR⟩ := Finset.mem_filter.mp member
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  obtain ⟨rc⟩ := h.toCounted
  have chain := (rf.append rs).append rp
  -- Epochs, as natural numbers.
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have later := UInt64.le_iff_toNat_le.mp h.later
  have near := h.near
  have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have succNat : (getCurrentEpoch pulled + 1).toNat = (getCurrentEpoch pulled).toNat + 1 := by
    have one : (1 : UInt64).toNat = 1 := rfl
    rw [UInt64.toNat_add, one]
    exact Nat.mod_eq_of_lt (by omega)
  have finCur := UInt64.le_iff_toNat_le.mp (finalized_le_current h)
  -- The records of the key at R and at C, and the activity they give.
  obtain ⟨u, foundU, activeU⟩ := active_of_activeVoters h.early memberAC
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeU
  have uAct := UInt64.le_iff_toNat_le.mp activeU.1
  have uExit := UInt64.lt_iff_toNat_lt.mp activeU.2
  have uUnslashed : u.slashed = false := by
    have := (Finset.mem_filter.mp memberQ).2
    simpa [foundU] using this
  have rActive : ∀ e : Epoch, isActiveAt pulled e v.toNat = true ↔
      (w.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < w.exitEpoch.toNat) := by
    intro e
    simp [isActiveAt, found, isActiveValidator, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  have cActive : ∀ e : Epoch, isActiveAt counted e v.toNat = true ↔
      (u.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < u.exitEpoch.toNat) := by
    intro e
    simp [isActiveAt, foundU, isActiveValidator, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  have notActive : ¬ (w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat ∧
      (getCurrentEpoch pulled).toNat < w.exitEpoch.toNat) := by
    intro both
    apply notAR
    simpa [AR, activeVoters] using
      mem_getActiveValidatorIndices_of_isActiveAt ((rActive _).mpr both)
  -- The key joins at R's next epoch.
  have joins : w.activationEpoch.toNat = (getCurrentEpoch pulled).toNat + 1 →
      (w.exitEpoch = FAR_FUTURE_EPOCH ∨
        w.activationEpoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ w.exitEpoch.toNat) →
      isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true := by
    intro first gap
    refine ⟨Bool.eq_false_iff.mpr fun active => ?_, (rActive _).mpr ⟨by omega, ?_⟩⟩
    · have := (rActive _).mp active
      omega
    · rcases gap with far | gap
      · rw [succNat, far, farNat]
        omega
      · rw [succNat]
        omega
  by_cases hA : (getCurrentEpoch pulled).toNat < w.activationEpoch.toNat
  · -- Not activated at R's epoch.
    by_cases window : (getCurrentEpoch counted).toNat ≤
        (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat
    · -- The key's activity at C's epoch is shared, so R activates it by then.
      have shared := activity_shared h (e := getCurrentEpoch counted) window v.toNat
      have activeAtC : isActiveAt counted (getCurrentEpoch counted) v.toNat = true :=
        (cActive _).mpr ⟨uAct, uExit⟩
      have atR := (rActive _).mp (shared.trans activeAtC)
      left
      refine joins (by omega) ?_
      by_cases far : w.exitEpoch = FAR_FUTURE_EPOCH
      · exact .inl far
      · exact .inr (Run.exit_activation_gap chain h.genesis v.toNat w found far)
    · -- Beyond the shared window, the finalized epoch is before R's epoch.
      by_cases far : w.activationEpoch = FAR_FUTURE_EPOCH
      · by_cases elig : (getCurrentEpoch pulled).toNat < w.activationEligibilityEpoch.toNat
        · exact .inr (.inr (.inr (.inr
            ((pendingRB_iff config pulled anc fin v.toNat).mpr ⟨w, found, elig, far⟩))))
        · refine .inr (.inl ((lateB_iff config pulled anc fin v.toNat).mpr
            ⟨w, found, by omega, ?_⟩))
          rw [far, farNat]
          omega
      · have eligible := Run.eligibility_le_finalized chain h.genesis v.toNat w found far
        have eligNat : w.activationEligibilityEpoch.toNat ≤
            pulled.finalizedCheckpoint.epoch.toNat := UInt64.le_iff_toNat_le.mp eligible
        by_cases first : w.activationEpoch.toNat = (getCurrentEpoch pulled).toNat + 1
        · left
          refine joins first ?_
          by_cases farExit : w.exitEpoch = FAR_FUTURE_EPOCH
          · exact .inl farExit
          · exact .inr (Run.exit_activation_gap chain h.genesis v.toNat w found farExit)
        · exact .inr (.inl ((lateB_iff config pulled anc fin v.toNat).mpr
            ⟨w, found, by omega, by omega⟩))
  · -- Exited at R's epoch or before.
    have exited : w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat := by omega
    have exitNear : w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro far
      rw [far, farNat] at exited
      omega
    have gap := Run.exit_activation_gap chain h.genesis v.toNat w found exitNear
    have afterFin : anc.finalizedCheckpoint.epoch.toNat + 1 +
        preset.MAX_SEED_LOOKAHEAD.toNat ≤ w.exitEpoch.toNat := by
      rcases K6_exit_late h found rActive cActive uExit notActive with far | late
      · exact absurd far exitNear
      · omega
    by_cases settled : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch pulled).toNat
    · exact .inr (.inr (.inl ((exitedRB_iff config pulled anc fin v.toNat).mpr
        ⟨w, found, afterFin, settled⟩)))
    · -- The exit is at R's epoch.
      refine .inr (.inr (.inr (.inl ((exitingB_iff config pulled anc fin v.toNat).mpr
        ⟨w, found, .inl ((rActive _).mpr ⟨?_, ?_⟩), ?_, by omega⟩))))
      · rw [getPreviousEpoch_toNat]
        omega
      · rw [getPreviousEpoch_toNat]
        omega
      · by_cases unslashed : w.slashed = false
        · exact .inl unslashed
        · right
          have slashed : w.slashed = true := by simpa using unslashed
          have delayed := slashed_waits (rf.append rs) h.genesis rp rc h.early h.caps h.delay
            found slashed (by simp [foundU, uUnslashed])
          omega

/-- The keys that join at R's next epoch are charged their stake in `joining`. -/
private theorem joining_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).joining =
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (isActiveAt pulled (getCurrentEpoch pulled) i = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) i = true), balanceAt pulled i := rfl

/-- The keys that join at R's next epoch are charged their rise in `joinRise`. -/
private theorem joinRise_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).joinRise =
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (isActiveAt pulled (getCurrentEpoch pulled) i = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) i = true),
            (pinTerms config pulled anc fin).rise i := rfl

/-- The window is tight when its depth is at most one more than the seed lookahead. -/
private theorem tight_iff (config : Config) (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).tight = true ↔
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat ≤
        1 + preset.MAX_SEED_LOOKAHEAD.toNat := by
  simp only [pinTerms, decide_eq_true_eq]

/-- Outside the tight window, `pendingR` is the stake and rise of the pending keys. -/
private theorem pendingR_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).pendingR =
      if (pinTerms config pulled anc fin).tight = true then 0 else
        ∑ i ∈ (pinTerms config pulled anc fin).positions with
          (pinTerms config pulled anc fin).pendingRB i = true,
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i) := rfl

/-- K6 keys of R's registry that are not yet eligible at R: their stake at R and their rise. -/
theorem bud_pendingR (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat = true,
      (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤
        (pinTerms config pulled anc fin).pendingR := by
  classical
  rw [pendingR_eq]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · -- Tight: no key of K6 is pending, since activity near the split is shared.
    rw [ite_eq_left tight]
    have fin_le := UInt64.le_iff_toNat_le.mp h.finalized
    have called := UInt64.le_iff_toNat_le.mp h.called
    have bound := (tight_iff config pulled anc fin).mp tight
    have near : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := h.near
    apply Nat.le_of_eq
    apply Finset.sum_eq_zero
    intro v hv
    exfalso
    have hv' := Finset.mem_filter.mp hv
    obtain ⟨w, found, -, far⟩ := (pendingRB_iff config pulled anc fin v.toNat).mp hv'.2
    have le := activation_le_of_active h (by omega) (Finset.mem_filter.mp hv'.1).1 found
    have farNat : w.activationEpoch.toNat = 2 ^ 64 - 1 := by rw [far]; rfl
    have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots counted
    have farValue : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  · rw [ite_eq_right tight]
    refine sum_toNat_le (fun i => balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
      fun v hv => ?_
    have flag := (Finset.mem_filter.mp hv).2
    obtain ⟨w, found, -⟩ := (pendingRB_iff config pulled anc fin v.toNat).mp flag
    exact mem_positions_filter config pulled anc fin found flag

/-- The keys that `exitingB` marks have their effective balances in `exiting`. -/
private theorem sum_le_exiting (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (S : Finset ValidatorIndex)
    (member : ∀ v ∈ S, (pinTerms config state ancestor finalizedState).exitingB v.toNat = true) :
    ∑ v ∈ S, balanceAt state v.toNat ≤ (pinTerms config state ancestor finalizedState).exiting := by
  dsimp only [pinTerms]
  refine sum_toNat_le (fun i => balanceAt state i) fun v hv => ?_
  have mark := of_decide_eq_true (member v hv)
  obtain ⟨w, found⟩ := validator_of_flag (state := state) (Or.inr mark.2.2)
  exact mem_positions_filter config state ancestor finalizedState found mark

/-- `exitingBands` is two bands for each key that `exitingB` marks and for each queue key. -/
private theorem exitingBands_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).exitingBands =
      2 * ((((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).exitingB i = true).card +
        (pinTerms config state ancestor finalizedState).queueKeys)) * preset.upwardBand := by
  dsimp only [pinTerms]
  simp only [decide_eq_true_eq]

/-- At most as many keys as the positions that `exitingB` marks are marked. -/
private theorem card_exitingB_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (S : Finset ValidatorIndex)
    (member : ∀ v ∈ S, (pinTerms config state ancestor finalizedState).exitingB v.toNat = true) :
    S.card ≤ ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
      (pinTerms config state ancestor finalizedState).exitingB i = true).card := by
  refine Finset.card_le_card_of_injOn (fun v : ValidatorIndex => v.toNat) (fun v hv => ?_)
    (fun a _ b _ same => UInt64.toNat_inj.mp same)
  have mark := of_decide_eq_true (member v hv)
  obtain ⟨w, found⟩ := validator_of_flag (state := state) (Or.inr mark.2.2)
  exact mem_positions_filter config state ancestor finalizedState found
    (p := fun i => (pinTerms config state ancestor finalizedState).exitingB i = true) (member v hv)

/-- The two further bands of the keys of `K5` are at most `exitingBands`, given their charges. -/
private theorem two_bands_le_exitingBands (config : Config)
    (pulled anc fin counted : BeaconState preset fork) (V : Finset ValidatorIndex)
    {x : ForkedBeaconState preset} (tailC : Run config checks x ⟨fork, counted⟩) (highC : ℕ)
    (charged : ∀ v ∈ K5 counted V, (pinTerms config pulled anc fin).exitingB v.toNat = false →
      0 < bandC tailC highC v.toNat → ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (count : ((K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges,
      c.index = v.toNat).card ≤ (pinTerms config pulled anc fin).queueKeys) :
    2 * (∑ v ∈ K5 counted V, bandC tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).exitingBands := by
  have bounded (v : ℕ) : bandC tailC highC v ≤ preset.upwardBand := by
    unfold bandC
    split <;> omega
  rw [exitingBands_eq]
  set A := (K5 counted V).filter fun v => (pinTerms config pulled anc fin).exitingB v.toNat = true
  set B := (K5 counted V).filter fun v => (pinTerms config pulled anc fin).exitingB v.toNat = false
  have parts : ∑ v ∈ K5 counted V, bandC tailC highC v.toNat =
      ∑ v ∈ A, bandC tailC highC v.toNat + ∑ v ∈ B, bandC tailC highC v.toNat := by
    rw [← Finset.sum_filter_add_sum_filter_not (K5 counted V)
      (fun v => (pinTerms config pulled anc fin).exitingB v.toNat = true)]
    simp [A, B]
  have first : ∑ v ∈ A, bandC tailC highC v.toNat ≤ A.card * preset.upwardBand := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun v _ => bounded _
  have second : ∑ v ∈ B, bandC tailC highC v.toNat ≤
      (B.filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card *
        preset.upwardBand := by
    have pointwise : ∀ v ∈ B, bandC tailC highC v.toNat ≤
        (if ∃ c ∈ tailC.departureCharges, c.index = v.toNat then preset.upwardBand else 0) := by
      intro v hv
      by_cases hc : ∃ c ∈ tailC.departureCharges, c.index = v.toNat
      · simp only [hc, ↓reduceIte]
        exact bounded _
      · simp only [hc, ↓reduceIte]
        have notBand : ¬ 0 < bandC tailC highC v.toNat := fun pos =>
          hc (charged v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2 pos)
        omega
    calc ∑ v ∈ B, bandC tailC highC v.toNat
        ≤ ∑ v ∈ B, (if ∃ c ∈ tailC.departureCharges, c.index = v.toNat
          then preset.upwardBand else 0) := Finset.sum_le_sum pointwise
      _ = (B.filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card *
          preset.upwardBand := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have inA := card_exitingB_le config pulled anc fin A fun v hv => (Finset.mem_filter.mp hv).2
  have times := Nat.mul_le_mul_right preset.upwardBand inA
  have countB : (B.filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card ≤
      (pinTerms config pulled anc fin).queueKeys :=
    (Finset.card_le_card fun v hv => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1, (Finset.mem_filter.mp hv).2⟩).trans
        count
  have timesB := Nat.mul_le_mul_right preset.upwardBand countB
  rw [parts]
  nlinarith

/-- A key whose exit C assigned by C's epoch and that R does not read as exiting has a charge.

The key is active at R's epoch or the one before it, if R's record has the exit of C's.

The charge is on C's run, if the exit is not inherited from the split. -/
private theorem exit_charged (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    {u : Validator} (foundU : counted.validators.data[v.toNat]? = some u)
    (assignedC : u.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (exited : u.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat)
    (unslashedC : u.slashed = false)
    (atR : ∀ w, pulled.validators.data[v.toNat]? = some w → w.exitEpoch = u.exitEpoch →
      isActiveAt pulled (getPreviousEpoch pulled) v.toNat = true ∨
        isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true)
    (flag : (pinTerms config pulled anc fin).exitingB v.toNat = false) :
    ∃ c ∈ tailC.departureCharges, c.index = v.toNat := by
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  by_cases inherited : ∃ old, split.validators.data[v.toNat]? = some old ∧
      old.exitEpoch ≠ FAR_FUTURE_EPOCH
  · exfalso
    obtain ⟨old, oldFound, oldAssigned⟩ := inherited
    obtain ⟨uC, foundUC, keptC⟩ := tailC.registryLifecycle.validators v.toNat old oldFound
    have sameU : uC = u := Option.some.inj (foundUC.symm.trans foundU)
    rw [sameU] at keptC
    obtain ⟨w, foundW, keptP⟩ := toPulled.registryLifecycle.validators v.toNat old oldFound
    have exitU : u.exitEpoch = old.exitEpoch := keptC.exitEpoch oldAssigned
    have exitW : w.exitEpoch = old.exitEpoch := keptP.exitEpoch oldAssigned
    have exitWU : w.exitEpoch = u.exitEpoch := exitW.trans exitU.symm
    have exitWNat : w.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
      rw [exitWU]
      exact exited
    have nearNat := h.near
    have activeR := atR w foundW exitWU
    have notSlashed : w.slashed = false ∨ anc.finalizedCheckpoint.epoch.toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ w.withdrawableEpoch.toNat := by
      cases slashed : w.slashed
      · exact .inl rfl
      · have delayed := slashed_waits (shared.append fromFin) h.genesis toPulled tailC h.early
          h.caps h.delay foundW slashed (by simp [foundU, unslashedC])
        have := UInt64.le_iff_toNat_le.mp h.finalized
        exact .inr (Nat.le_trans (Nat.add_le_add_right this _) delayed)
    have marked : (pinTerms config pulled anc fin).exitingB v.toNat = true := by
      simp only [pinTerms, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩
      · rcases activeR with active | active <;> simp [active]
      · simpa [foundW] using notSlashed
      · simpa [foundW] using
          (show w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 by omega)
    rw [flag] at marked
    exact Bool.false_ne_true marked
  · obtain ⟨c, member, index, -⟩ := PinSplit.Run.charge_of_exit tailC electra h.early v.toNat
      (fun w hw => by
        by_contra far
        exact inherited ⟨w, hw, far⟩) u foundU assignedC
    exact ⟨c, member, index⟩

/-- A key of `K5` that R does not read as exiting has a departure charge on C's run. -/
private theorem K5_charged (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ K5 counted V) (flag : (pinTerms config pulled anc fin).exitingB v.toNat = false) :
    ∃ c ∈ tailC.departureCharges, c.index = v.toNat := by
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  have inK5 := Finset.mem_filter.mp member
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inK5
  obtain ⟨⟨listed, unslashedC⟩, notActive, -⟩ := inK5
  have notCurrent : v ∉ getActiveValidatorIndices counted (getCurrentEpoch counted) := fun now =>
    notActive (by simpa [AC, activeVoters] using now)
  rcases listed with now | before
  · exact absurd now notCurrent
  obtain ⟨u, foundU, activeBefore⟩ := (mem_getActiveValidatorIndices within).mp before
  have notNow : isActiveValidator u (getCurrentEpoch counted) = false := by
    cases now : isActiveValidator u (getCurrentEpoch counted)
    · rfl
    · exact absurd ((mem_getActiveValidatorIndices within).mpr ⟨u, foundU, now⟩) notCurrent
  have exitC := (previous_only_iff_exit counted u).mp ⟨activeBefore, notNow⟩
  have notFar := getCurrentEpoch_ne_farFuture h.twoSlots counted
  have assignedC : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far =>
    notFar (UInt64.toNat_inj.mp (by rw [← exitC.2, far]))
  refine exit_charged h tailC foundU assignedC (Nat.le_of_eq exitC.2) (by simpa [foundU] using
    unslashedC) (fun w foundW sameExit => ?_) flag
  have gap := ((shared.append fromFin).append toPulled).exit_activation_gap h.genesis v.toNat w
    foundW (sameExit ▸ assignedC)
  have exitW : w.exitEpoch.toNat = (getCurrentEpoch counted).toNat := by
    rw [sameExit]
    exact exitC.2
  have actLt : w.activationEpoch.toNat < (getCurrentEpoch counted).toNat := by omega
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have nearNat := h.near
  have previous := getPreviousEpoch_toNat pulled
  have activeAt (e : Epoch) (low : w.activationEpoch.toNat ≤ e.toNat)
      (high : e.toNat < w.exitEpoch.toNat) : isActiveAt pulled e v.toNat = true :=
    isActiveAt_eq_true_iff.mpr ⟨w, foundW, by
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
        UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
      exact ⟨low, high⟩⟩
  rcases Nat.lt_or_ge (getCurrentEpoch pulled).toNat (getCurrentEpoch counted).toNat with
    before | same
  · exact .inr (activeAt _ (by omega) (by omega))
  · exact .inl (activeAt _ (by omega) (by omega))

/-- A key of `K5` without a departure charge on C's run is one whose exit R reads.

It is the contrapositive of `K5_charged`. -/
private theorem K5_exiting_of_not_charged
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ K5 counted V) (none : ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    (pinTerms config pulled anc fin).exitingB v.toNat = true := by
  by_contra flag
  exact none (K5_charged h tailC member (by simpa using flag))

/-- D-4: the keys whose exit R reads.

The keys of `K5` are those without a departure charge on C's run. -/
theorem bud_exiting (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, eR pulled v) +
      (∑ v ∈ (K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        eR pulled v) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        eR pulled v) ≤ (pinTerms config pulled anc fin).exiting := by
  have apartVK5 : Disjoint (VN counted V) (K5 counted V) := by
    rw [Finset.disjoint_left]
    intro v inV inK5
    simp only [VN, K5, Finset.mem_filter] at inV inK5
    exact inK5.2.2 inV.1
  have apartVK6 : Disjoint (VN counted V) (K6 pulled counted) := by
    rw [Finset.disjoint_left]
    intro v inV inK6
    simp only [VN, K6, Finset.mem_filter] at inV inK6
    exact inV.2 inK6.1
  have apartK5K6 : Disjoint (K5 counted V) (K6 pulled counted) := by
    rw [Finset.disjoint_left]
    intro v inK5 inK6
    simp only [K5, K6, Finset.mem_filter] at inK5 inK6
    exact inK5.2.1 inK6.1
  rw [← Finset.sum_union (Finset.disjoint_filter_filter apartVK5),
    ← Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_filter_filter apartVK6, Finset.disjoint_filter_filter apartK5K6⟩)]
  exact sum_le_exiting config pulled anc fin _ fun v member => by
    rcases Finset.mem_union.mp member with member | member
    · rcases Finset.mem_union.mp member with member | member
      · exact (Finset.mem_filter.mp member).2
      · exact K5_exiting_of_not_charged h tailC (Finset.mem_filter.mp member).1
          (Finset.mem_filter.mp member).2
    · exact (Finset.mem_filter.mp member).2

/-- Outside the tight window, `late` is three times the stake of the late keys and their rise. -/
private theorem late_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).late =
      if (pinTerms config pulled anc fin).tight = true then 0 else
        ∑ i ∈ (pinTerms config pulled anc fin).positions with
          (pinTerms config pulled anc fin).lateB i = true,
            (3 * balanceAt pulled i + (pinTerms config pulled anc fin).rise i) := rfl

/-- Late activations, weight 3 for V keys and for new keys. -/
theorem bud_late (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true, eR pulled v) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat = true,
        (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤ (pinTerms config pulled anc fin).late := by
  classical
  rw [late_eq]
  have disjoint : Disjoint (VN counted V) (K6 pulled counted) := by
    rw [Finset.disjoint_left]
    intro v hv hk
    have inV := (Finset.mem_filter.mp hv).1
    exact (Finset.mem_filter.mp hk).2.2 (h.voting v inV).1
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · rw [ite_eq_left tight]
    -- Tight: no key of VN or K6 is late.
    have fin_le := UInt64.le_iff_toNat_le.mp h.finalized
    have called := UInt64.le_iff_toNat_le.mp h.called
    have bound := (tight_iff config pulled anc fin).mp tight
    have near := h.near
    have lowerEpoch : (getCurrentEpoch pulled).toNat + 1 ≤
        anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat := by omega
    have none : ∀ v ∈ (VN counted V) ∪ (K6 pulled counted),
        (pinTerms config pulled anc fin).lateB v.toNat = false := by
      intro v hv
      by_contra late
      obtain ⟨w, found, -, beyond⟩ := (lateB_iff config pulled anc fin v.toNat).mp
        (by simpa using late)
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨w', found', active⟩ := active_of_activeVoters h.early
          (h.voting v (Finset.mem_filter.mp hv).1).1
        rw [found] at found'
        cases found'
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
        have := UInt64.le_iff_toNat_le.mp active.1
        omega
      · have le := activation_le_of_active h (by omega) (Finset.mem_filter.mp hv).1 found
        omega
    have zeroA : ∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
        eR pulled v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have := none v (Finset.mem_union_left _ (Finset.mem_filter.mp hv).1)
      simp [(Finset.mem_filter.mp hv).2] at this
    have zeroB : ∑ v ∈ (K6 pulled counted) with
        (pinTerms config pulled anc fin).lateB v.toNat = true,
          (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have := none v (Finset.mem_union_right _ (Finset.mem_filter.mp hv).1)
      simp [(Finset.mem_filter.mp hv).2] at this
    rw [zeroA, zeroB]
  · rw [ite_eq_right tight]
    set A := (VN counted V).filter fun v => (pinTerms config pulled anc fin).lateB v.toNat = true
      with hA
    set B := (K6 pulled counted).filter
      fun v => (pinTerms config pulled anc fin).lateB v.toNat = true with hB
    have disj : Disjoint A B :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) disjoint)
    have le : ∑ v ∈ A ∪ B, (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) ≤
        ∑ i ∈ (pinTerms config pulled anc fin).positions.filter
          (fun i => (pinTerms config pulled anc fin).lateB i = true),
            (3 * balanceAt pulled i + (pinTerms config pulled anc fin).rise i) :=
      sum_toNat_le (fun i => 3 * balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        fun v hv => by
        have flag : (pinTerms config pulled anc fin).lateB v.toNat = true := by
          rcases Finset.mem_union.mp hv with hv | hv <;> exact (Finset.mem_filter.mp hv).2
        obtain ⟨w, found, -⟩ := (lateB_iff config pulled anc fin v.toNat).mp flag
        exact mem_positions_filter config pulled anc fin found flag
    rw [Finset.sum_union disj] at le
    have split : ∑ v ∈ A, (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) =
        3 * ∑ v ∈ A, eR pulled v + ∑ v ∈ A, (pinTerms config pulled anc fin).rise v.toNat := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    omega

/-- The pin's bound on another branch's total: three halves of the call's total. -/
private def pinWide (state : BeaconState preset fork) : ℕ :=
  3 * ((getTotalActiveBalance state).toOption.getD 0).toNat / 2

/-- The pin's balance churn at a total, rounded down to an increment. -/
private def pinBalance (preset : Preset) (config : Config) (wide : ℕ) : ℕ :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (wide / config.CHURN_LIMIT_QUOTIENT.toNat) -
    max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (wide / config.CHURN_LIMIT_QUOTIENT.toNat) %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- The pin's exit churn at a total, before Gloas. -/
private def pinExit (preset : Preset) (config : Config) (wide : ℕ) : ℕ :=
  min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (pinBalance preset config wide)

/-- The pin's consolidation churn at a total, before Gloas. -/
private def pinCons (preset : Preset) (config : Config) (wide : ℕ) : ℕ :=
  pinBalance preset config wide - pinExit preset config wide

/-- Before Gloas, `queueWindow` is the depth's exit and consolidation churn and the two carries. -/
private theorem queueWindow_unfold (early : fork < .glamsterdam) (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueWindow =
      (pinTerms config state ancestor finalizedState).depth *
        (pinExit preset config (pinWide state) + pinCons preset config (pinWide state)) +
        max preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        max (if electra : .pectra ≤ fork then
          (finalizedState.consolidationBalanceToConsume electra).toNat else 0)
          (pinCons preset config (pinWide state)) := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold pinTerms
  simp only [notGloas, pinWide, pinCons, pinExit, pinBalance, ↓reduceIte]

/-- A state with a total of at most `wide` has an exit churn limit of at most the pin's. -/
private theorem exitRate_le {fork' : Fork} {s : BeaconState preset fork'}
    (early : fork' < .glamsterdam) {rate : Gwei} (wide : ℕ)
    (band : ∀ t : Gwei, getTotalActiveBalance s = .ok t → t.toNat ≤ wide)
    (computed : exitChurnLimit config s = .ok rate) :
    rate.toNat ≤ pinExit preset config wide := by
  have notGloas : ¬ .glamsterdam ≤ fork' := Nat.not_le_of_lt early
  obtain ⟨total, read⟩ : ∃ t, getTotalActiveBalance s = .ok t := by
    cases first : getTotalActiveBalance s with
    | error e =>
      simp [exitChurnLimit, notGloas, getActivationExitChurnLimit, getBalanceChurnLimit, first,
        bind, Except.bind] at computed
    | ok t => exact ⟨t, rfl⟩
  have le := band total read
  have value : rate = min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
      (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT))) := by
    simpa [exitChurnLimit, notGloas, getActivationExitChurnLimit,
      getBalanceChurnLimit, read, bind, Except.bind, pure, Except.pure] using computed.symm
  rw [value, Uint64.toNat_min, toNat_roundToIncrement, Uint64.toNat_max, UInt64.toNat_div]
  exact min_le_min_left _ (rounded_mono _ (max_le_max_left _
    (Nat.div_le_div_right le)))

/-- A state with a total of at most `wide` has a consolidation churn limit of at most the pin's.

The pin reads it at `wide`. -/
private theorem consRate_le {fork' : Fork} {s : BeaconState preset fork'}
    (early : fork' < .glamsterdam) {rate : Gwei} (wide : ℕ)
    (band : ∀ t : Gwei, getTotalActiveBalance s = .ok t → t.toNat ≤ wide)
    (computed : getConsolidationChurnLimit config s = .ok rate) :
    rate.toNat ≤ pinCons preset config wide := by
  have notGloas : ¬ .glamsterdam ≤ fork' := Nat.not_le_of_lt early
  obtain ⟨total, read⟩ : ∃ t, getTotalActiveBalance s = .ok t := by
    cases first : getTotalActiveBalance s with
    | error e =>
      simp [getConsolidationChurnLimit, notGloas, getBalanceChurnLimit, first, bind,
        Except.bind] at computed
    | ok t => exact ⟨t, rfl⟩
  have le := band total read
  have value : rate = roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT)) -
      min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
        (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
          (total / config.CHURN_LIMIT_QUOTIENT))) := by
    simpa [getConsolidationChurnLimit, notGloas, getActivationExitChurnLimit,
      getBalanceChurnLimit, read, bind, Except.bind, pure, Except.pure] using computed.symm
  have fits : min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
      (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT))) ≤
      roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT)) :=
    UInt64.le_iff_toNat_le.mpr (by rw [Uint64.toNat_min]; exact Nat.min_le_right _ _)
  rw [value, UInt64.toNat_sub_of_le _ _ fits, Uint64.toNat_min, toNat_roundToIncrement,
    Uint64.toNat_max, UInt64.toNat_div]
  have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat (max_le_max_left
    config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (Nat.div_le_div_right (c := config.CHURN_LIMIT_QUOTIENT.toNat) le))
  unfold pinCons pinExit pinBalance
  omega

/-- The amount that `exitQ` reads is at most the amounts of the charges at its position.

Those charges are the ones with an epoch up to a later one. -/
private theorem exitQ_amount_le (L : List DepartureCharge) (b₀ b v : ℕ) (le : b₀ ≤ b) :
    ((L.find? fun c => c.index == v && decide (c.epoch ≤ b₀)).map (·.amount)).getD 0 ≤
      ((L.filter fun c => c.epoch ≤ b).map fun c => if c.index = v then c.amount else 0).sum := by
  cases found : L.find? fun c => c.index == v && decide (c.epoch ≤ b₀) with
  | none => simp
  | some c =>
    have member := List.mem_of_find?_eq_some found
    have both := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at both
    have kept : c ∈ L.filter fun c => c.epoch ≤ b :=
      List.mem_filter.mpr ⟨member, by simpa using both.2.trans le⟩
    have term : c.amount ∈ (L.filter fun c => c.epoch ≤ b).map
        fun c => if c.index = v then c.amount else 0 :=
      List.mem_map.mpr ⟨c, kept, by simp [both.1]⟩
    simpa using List.single_le_sum (fun _ _ => Nat.zero_le _) _ term

/-- The `exitQ` of a set of keys is at most the amounts of the charges of the run.

Those charges are the ones with an epoch up to one that the run's end does not pass. -/
private theorem sum_exitQ_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (b : ℕ) (le : (getCurrentEpoch y.state).toNat ≤ b) (S : Finset ValidatorIndex) :
    ∑ v ∈ S, exitQ tail v.toNat ≤
      ((tail.departureCharges.filter fun c => c.epoch ≤ b).map (·.amount)).sum := by
  classical
  have each : ∀ v ∈ S, exitQ tail v.toNat ≤
      ((tail.departureCharges.filter fun c => c.epoch ≤ b).map
        fun c => if c.index = v.toNat then c.amount else 0).sum :=
    fun v _ => exitQ_amount_le _ _ b v.toNat le
  refine (Finset.sum_le_sum each).trans ?_
  refine (sum_toNat_le (S := S) (P := S.image fun v : ValidatorIndex => v.toNat)
    (fun n => ((tail.departureCharges.filter fun c => c.epoch ≤ b).map
      fun c => if c.index = n then c.amount else 0).sum)
    fun v member => Finset.mem_image_of_mem _ member).trans ?_
  have swap := Multiset.sum_map_sum
    (m := (tail.departureCharges.filter fun c => c.epoch ≤ b : List DepartureCharge))
    (s := S.image fun v : ValidatorIndex => v.toNat)
    (f := fun (c : DepartureCharge) (n : ℕ) => if c.index = n then c.amount else 0)
  simp only [Multiset.map_coe, Multiset.sum_coe, Finset.sum_ite_eq] at swap
  rw [← swap]
  exact List.sum_le_sum fun c _ => by split <;> simp

/-- The departure charges of C's branch fit the window's churn and carries.

They are the charges with an epoch up to the run's last epoch.

The bound is the churn of the window and the two carries. -/
private theorem charges_le_queueWindow (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    ((tailC.departureCharges.filter fun c =>
      c.epoch ≤ (getCurrentEpoch counted).toNat - 1 + 1).map (·.amount)).sum ≤
        (pinTerms config pulled anc fin).queueWindow := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have early := h.early
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have later := UInt64.le_iff_toNat_le.mp h.later
  have near := h.near
  -- the exit and consolidation churn of every state on the runs from the finalized state
  have band : ∀ (u : ForkedBeaconState preset) (run : Run config checks ⟨fork, fin⟩ u),
      u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
      ∀ t : Gwei, getTotalActiveBalance u.state = .ok t → t.toNat ≤ pinWide pulled := by
    intro u run uEarly uWithin t read
    have := total_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots electra
      h.guard (fromFin.append toPulled) h.early (Nat.le_succ_of_le (Nat.le_refl _)) run uEarly
      uWithin pulledOk read
    simp only [pinWide, pulledOk, Except.toOption, Option.getD_some]
    omega
  have exitBound : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tailC.Contains step → ∀ rate : Gwei, exitChurnLimit config u.state = .ok rate →
        rate.toNat ≤ pinExit preset config (pinWide pulled) := by
    intro u w step member rate computed
    obtain ⟨pre, post, _, uEarly, uEpoch⟩ := Run.contains_step_facts member h.early
    have uEpoch' : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch counted).toNat := uEpoch
    exact exitRate_le uEarly _ (band u (fromFin.append pre) uEarly (by omega)) computed
  have consTail : ∀ site ∈ tailC.consolidationSites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate →
        rate.toNat ≤ pinCons preset config (pinWide pulled) := by
    intro site member _ rate computed
    obtain ⟨u, w, step, contained, _, same⟩ := consolidationSite_rate tailC h.early site member
    obtain ⟨pre, post, _, uEarly, uEpoch⟩ := Run.contains_step_facts contained h.early
    have uEpoch' : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch counted).toNat := uEpoch
    exact consRate_le uEarly _ (band u (fromFin.append pre) uEarly (by omega))
      (same rate computed)
  have consFin : ∀ site ∈ fromFin.consolidationSites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate →
        rate.toNat ≤ pinCons preset config (pinWide pulled) := by
    intro site member _ rate computed
    obtain ⟨u, w, step, contained, _, same⟩ := consolidationSite_rate fromFin h.early site member
    obtain ⟨pre, post, _, uEarly, uEpoch⟩ := Run.contains_step_facts contained h.early
    have uEpoch' : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch split).toNat := uEpoch
    exact consRate_le uEarly _ (band u pre uEarly (by omega)) (same rate computed)
  obtain ⟨exitCarry, consolidationCarry⟩ :
      (split.exitBalanceToConsume electra).toNat ≤
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat ∧
      (split.consolidationBalanceToConsume electra).toNat ≤
        max (fin.consolidationBalanceToConsume electra).toNat
          (pinCons preset config (pinWide pulled)) :=
    queueCarry_le_of_run shared h.genesis fromFin electra h.early electra _ consFin
  have window := departure_charges_le_window_electra_cap tailC electra h.early
    ((getCurrentEpoch counted).toNat - 1) (pinCons preset config (pinWide pulled))
    (pinExit preset config (pinWide pulled)) exitBound consTail
  dsimp only at window
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  rw [queueWindow_unfold h.early]
  simp only [electra, ↓reduceDIte]
  generalize (pinTerms config pulled anc fin).depth = depth at depthEq ⊢
  generalize pinExit preset config (pinWide pulled) = E at *
  generalize pinCons preset config (pinWide pulled) = C at *
  have firstLe : (getCurrentEpoch counted).toNat - 1 + 2 - max (getCurrentEpoch split).toNat
      (split.earliestExitEpoch electra).toNat ≤ depth := by omega
  have secondLe : (getCurrentEpoch counted).toNat - 1 + 2 - max (getCurrentEpoch split).toNat
      (split.earliestConsolidationEpoch electra).toNat ≤ depth := by omega
  have exitTerm : (if (split.earliestExitEpoch electra).toNat ≤
        (getCurrentEpoch counted).toNat - 1 + 1
      then (split.exitBalanceToConsume electra).toNat else 0) ≤
      max preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
    split <;> omega
  have consolidationTerm : (if (split.earliestConsolidationEpoch electra).toNat ≤
        (getCurrentEpoch counted).toNat - 1 + 1
      then (split.consolidationBalanceToConsume electra).toNat else 0) ≤
      max (fin.consolidationBalanceToConsume electra).toNat C := by
    split <;> omega
  have a := Nat.mul_le_mul_right E firstLe
  have b := Nat.mul_le_mul_right C secondLe
  rw [Nat.mul_add depth E C]
  omega

/-- The keys with a charge of at least `exitFloor` are at most the window over `exitFloor`. -/
private theorem card_big_charges_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (S : Finset ValidatorIndex) :
    (S.filter fun v => (pinTerms config pulled anc fin).exitFloor ≤ exitQ tailC v.toNat).card ≤
      (pinTerms config pulled anc fin).queueWindow /
        (pinTerms config pulled anc fin).exitFloor := by
  classical
  have positive : 0 < (pinTerms config pulled anc fin).exitFloor := by
    unfold pinTerms
    exact lt_max_of_lt_left Nat.one_pos
  rw [Nat.le_div_iff_mul_le positive]
  have each := Finset.card_nsmul_le_sum
    (S.filter fun v => (pinTerms config pulled anc fin).exitFloor ≤ exitQ tailC v.toNat)
    (fun v => exitQ tailC v.toNat) (pinTerms config pulled anc fin).exitFloor
    fun v member => (Finset.mem_filter.mp member).2
  have subset := Finset.sum_le_sum_of_subset (f := fun v => exitQ tailC v.toNat)
    (Finset.filter_subset (fun v => (pinTerms config pulled anc fin).exitFloor ≤
      exitQ tailC v.toNat) S)
  have kept := sum_exitQ_le tailC ((getCurrentEpoch counted).toNat - 1 + 1)
    (by simp only; omega) S
  have window := charges_le_queueWindow h tailC
  simp only [smul_eq_mul] at each
  omega
/-- D-8 (queues): exits and consolidations initiated on C's branch (none in the tight window). -/
theorem bud_queues (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    3 * ((∑ v ∈ (VN counted V), exitQ tailC v.toNat) +
      (∑ v ∈ (K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        exitQ tailC v.toNat)) ≤
      (pinTerms config pulled anc fin).queueExit := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have early := h.early
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have later := UInt64.le_iff_toNat_le.mp h.later
  have near := h.near
  -- the two sets are disjoint
  have apart : Disjoint (VN counted V)
      ((K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat) := by
    refine Finset.disjoint_left.mpr fun v first second => ?_
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp second).1).2.2
      (Finset.mem_filter.mp first).1
  have queueExit_eq : (pinTerms config pulled anc fin).queueExit =
      if (pinTerms config pulled anc fin).tight = true then 0 else
        3 * (pinTerms config pulled anc fin).queueWindow := rfl
  rw [← Finset.sum_union apart, queueExit_eq]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · -- the tight window has no exit of a counting key
    simp only [tight, ↓reduceIte]
    have tightLe : (pinTerms config pulled anc fin).depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat :=
      of_decide_eq_true tight
    have depthEq : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    rw [depthEq] at tightLe
    have none : ∀ v : ValidatorIndex, exitQ tailC v.toNat = 0 := by
      intro v
      have missing : (tailC.departureCharges.find? fun c =>
          c.index == v.toNat && decide (c.epoch ≤ (getCurrentEpoch counted).toNat)) = none := by
        rw [List.find?_eq_none]
        intro c member
        have far : (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
          DirectSafety.Run.departureCharges_epoch_ge_start tailC electra early c member
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and]
        intro _
        omega
      simp [exitQ, missing]
    simp [none]
  · simp only [tight, Bool.false_eq_true, ↓reduceIte]
    have window := charges_le_queueWindow h tailC
    have kept := sum_exitQ_le tailC ((getCurrentEpoch counted).toNat - 1 + 1)
      (by simp only; omega) ((VN counted V) ∪
        ((K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat))
    omega

/-- The deposit credits of a set of keys, as events, fit any per-event bound on them.

An event counts for a key only when `keep` holds there.

The bound reads the credits of the keys that the event keeps. -/
private theorem credDepR_sum_le (V : Finset ValidatorIndex) (events : List (BalanceEvent preset))
    (keep : BalanceEvent preset → ℕ → Prop) [∀ e i, Decidable (keep e i)]
    (T : BalanceEvent preset → ℕ)
    (each : ∀ e ∈ events, e.source = .deposits →
      ∑ v ∈ V.filter fun v => keep e v.toNat, keyCredit v.toNat e ≤ T e) :
    ∑ v ∈ V, ((events.filter fun e => e.source = .deposits ∧ keep e v.toNat).map
      (keyCredit v.toNat)).sum ≤ (events.map T).sum := by
  induction events with
  | nil => simp
  | cons e rest ih =>
    have tail := ih fun e' member => each e' (List.mem_cons_of_mem _ member)
    by_cases dep : e.source = .deposits
    · have head := each e List.mem_cons_self dep
      have split : ∑ v ∈ V, (((e :: rest).filter fun e => e.source = .deposits ∧
            keep e v.toNat).map (keyCredit v.toNat)).sum =
          ∑ v ∈ V.filter (fun v => keep e v.toNat), keyCredit v.toNat e +
            ∑ v ∈ V, ((rest.filter fun e => e.source = .deposits ∧ keep e v.toNat).map
              (keyCredit v.toNat)).sum := by
        rw [Finset.sum_filter, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases kept : keep e v.toNat <;> simp [dep, kept]
      simp only [List.map_cons, List.sum_cons]
      omega
    · have same : ∑ v ∈ V, (((e :: rest).filter fun e => e.source = .deposits ∧
            keep e v.toNat).map (keyCredit v.toNat)).sum =
          ∑ v ∈ V, ((rest.filter fun e => e.source = .deposits ∧ keep e v.toNat).map
            (keyCredit v.toNat)).sum :=
        Finset.sum_congr rfl fun v _ => by simp [dep]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- `queueDep` is three times the deposit churn of each epoch of the window, and the carry. -/
private theorem queueDep_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueDep =
      3 * (((getCurrentEpoch state).toNat + 2 - (getCurrentEpoch finalizedState).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (if electra : .pectra ≤ fork then
          (finalizedState.depositBalanceToConsume electra).toNat else 0)) := rfl

/-- The funding credits of the deposit events of a run from the split fit the deposit churn.

The run ends within one epoch of R's, and its events are read at any horizon that its end allows.

The window is the carry of the finalized block and a churn for each epoch from it. -/
private theorem deposit_events_le (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (high : ℕ)
    (endEpoch : (getCurrentEpoch e).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (events.map DirectSafety.funding_deposit_credit).sum ≤
      (pinTerms config pulled anc fin).queueDep := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  -- Every step of the run starts within the epochs of `pulled`, so `high` can be that epoch.
  have same := DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le tail endEpoch within
  have tailOk : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events := by
    rw [← same]
    exact replayed
  obtain ⟨ef, efOk⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  have fullOk := DirectSafety.Apriori.Internal.balanceEvents_append fromFin tail
    (getCurrentEpoch pulled).toNat efOk tailOk
  have capacity := DirectSafety.funding_deposit_capacity toFin (fromFin.append tail) h.genesis
    h.early (getCurrentEpoch pulled).toNat within (ef ++ events) fullOk
  have bound : ((ef ++ events).map DirectSafety.funding_deposit_credit).sum ≤
      (if electra : .pectra ≤ fork then (fin.depositBalanceToConsume electra).toNat else 0) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := capacity
  rw [List.map_append, List.sum_append] at bound
  rw [queueDep_eq]
  omega

/-- D-8 (deposit queue) from the per-event bound of V's deposit credits.

The credits that a deposit event gives to V keys are at most its deposit credit.

That credit leaves out the keys that are withdrawn, which V keys never are.

The deposit credits of the run from the finalized block fit its carry and a churn for each epoch. -/
private theorem bud_deposits_of (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (each : ∀ e ∈ events, e.source = .deposits →
      ∑ v ∈ V, keyCredit v.toNat e ≤ DirectSafety.funding_deposit_credit e) :
    3 * (∑ v ∈ V, credDepR events v.toNat) ≤ (pinTerms config pulled anc fin).queueDep := by
  have sum : ∑ v ∈ V, credDepR events v.toNat ≤
      (events.map DirectSafety.funding_deposit_credit).sum := by
    simpa [credDepR] using credDepR_sum_le V events (fun _ _ => True)
      DirectSafety.funding_deposit_credit (by simpa using each)
  have capacity := deposit_events_le h tail (Nat.le_succ _) high endEpoch replayed
  omega

/-- A deposit event credits a set of keys at most its funding credit, when none is withdrawable.

Each key of the set that is present before the event must not be withdrawable there.

A key absent before the event has no balance after it either, since its balances match. -/
private theorem deposit_each_le (e : BalanceEvent preset) (S : Finset ValidatorIndex)
    (dep : e.source = .deposits) (electra : .pectra ≤ e.before.fork)
    (matched : BalancesMatch e.after.state)
    (held : ∀ v ∈ S, ∀ w, e.before.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch e.before.state).toNat < w.withdrawableEpoch.toNat) :
    ∑ v ∈ S, keyCredit v.toNat e ≤ DirectSafety.funding_deposit_credit e := by
  have inj : Set.InjOn (fun v : ValidatorIndex => v.toNat) S := fun a _ b _ same =>
    UInt64.toNat_inj.mp same
  have image := selected_deposit_le (S.image fun v => v.toNat) e matched fun i member => by
    obtain ⟨v, inS, rfl⟩ := Finset.mem_image.mp member
    cases found : e.before.state.validators.data[v.toNat]? with
    | none => rfl
    | some w => simpa using held v inS w found
  rw [Finset.sum_image inj] at image
  simpa [DirectSafety.funding_deposit_credit, dep, electra, keyCredit] using image

/-- The deposits credited to two sets of keys on C's run fit the window's deposit churn.

The first set's credits are read as the scan of the deposit events.

The second set's are the deposits of events whose before-state does not hold the key slashed.

Each deposit event credits both sets together at most its funding credit. -/
private theorem deposits_scan_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (S P : Finset ValidatorIndex)
    (each : ∀ e ∈ eventsC, e.source = .deposits →
      ∑ v ∈ S, keyCredit v.toNat e +
        ∑ v ∈ P.filter (fun v => ¬ slashedFlagAt e.before.state v.toNat = some true),
          keyCredit v.toNat e ≤ DirectSafety.funding_deposit_credit e) :
    3 * (∑ v ∈ S, (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
      tailC).1 + ∑ v ∈ P, depPre eventsC v.toNat) ≤ (pinTerms config pulled anc fin).queueDep := by
  obtain ⟨X, hX⟩ : ∃ X : BalanceEvent preset → ℕ, ∀ e, X e =
      ∑ v ∈ P.filter (fun v => ¬ slashedFlagAt e.before.state v.toNat = some true),
        keyCredit v.toNat e := ⟨_, fun _ => rfl⟩
  have scan := creditScan_sum_le S (fun _ => false) (fun s => decide (s = .deposits)) highC
    (fun e => DirectSafety.funding_deposit_credit e - X e) tailC replayedC
    fun e member selected => by
      have := each e member (by simpa using selected)
      have := hX e
      omega
  have pre := credDepR_sum_le P eventsC (fun e i => ¬ slashedFlagAt e.before.state i = some true)
    (fun e => if e.source = .deposits then X e else 0) fun e _ dep => by simp [dep, hX e]
  have capacity := deposit_events_le h tailC h.near highC endEpochC replayedC
  have chain : (eventsC.map fun e => if (false = true ∨ decide (e.source = .deposits) = true)
        then DirectSafety.funding_deposit_credit e - X e else 0).sum +
      (eventsC.map fun e => if e.source = .deposits then X e else 0).sum ≤
        (eventsC.map DirectSafety.funding_deposit_credit).sum := by
    rw [← List.sum_map_add]
    refine List.sum_le_sum fun e member => ?_
    by_cases dep : e.source = .deposits
    · have := each e member dep
      have := hX e
      simp only [dep, decide_true, or_true, ↓reduceIte]
      omega
    · simp [dep]
  have exchange : ∑ v ∈ P, depPre eventsC v.toNat ≤
      (eventsC.map fun e => if e.source = .deposits then X e else 0).sum := pre
  omega

/-- A key slashed at C and not slashed at the start of a deposit event is not withdrawable there.

The key is not slashed at the step's start, and the run from there ends with it slashed.

At the step that slashes it, the key is slashable, so it is not yet withdrawable.

Until then its withdrawable epoch is the one it has at the event's start, or its exit is far off. -/
private theorem slashed_deposit_held (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
    (contained : tailC.Contains (Step.slot ok)) {es : List (BalanceEvent preset)}
    (replayedEs : (Step.slot ok : Step config checks u w).balanceEvents = .ok es)
    {e : BalanceEvent preset} (inStep : e ∈ es) (dep : e.source = .deposits)
    (ordered : ExitsOrdered e.before.state) (life : RegistryLifecycle e.before.state counted)
    {i : ℕ} (slashedC : ∃ b, counted.validators.data[i]? = some b ∧ b.slashed = true)
    {a : Validator} (found : e.before.state.validators.data[i]? = some a)
    (clean : a.slashed = false) :
    (getCurrentEpoch e.before.state).toNat < a.withdrawableEpoch.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨pre, post, rfl⟩ := Run.contains_split tailC (Step.slot ok) contained
  have earlyW : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have fuluU : .fusaka ≤ u.fork := Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)
  have toU := (toFin.append fromFin).append pre
  obtain ⟨-, wdKept, -, size, persist, sameEpoch⟩ := PinSplit4.Run.events_kept toU h.genesis
    (Run.nil.snoc (Step.slot ok)) fuluU earlyW ok (.last .nil _) replayedEs e inStep dep
  obtain ⟨au, foundU⟩ : ∃ au, u.state.validators.data[i]? = some au :=
    ⟨_, Array.getElem?_eq_getElem (lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 size)⟩
  have cleanU : au.slashed = false := by
    cases flag : au.slashed
    · rfl
    · obtain ⟨x, read, marked⟩ := persist i au foundU flag
      obtain rfl := Option.some.inj (read.symm.trans found)
      simp [clean] at marked
  obtain ⟨m, n, preR, step, postR, -, notM, isN⟩ := Run.split_at_flip
    ((Run.nil.snoc (Step.slot ok)).append post)
    (fun z => ∃ b, z.state.validators.data[i]? = some b ∧ b.slashed = true)
    (by
      rintro ⟨b, read, marked⟩
      obtain rfl := Option.some.inj (foundU.symm.trans read)
      simp [cleanU] at marked) slashedC
  have toM := toU.append preR
  obtain ⟨bn, foundN, slashedN⟩ := isN
  obtain ⟨bm, foundM⟩ : ∃ bm, m.state.validators.data[i]? = some bm := by
    by_cases inside : i < m.state.validators.data.size
    · exact ⟨_, Array.getElem?_eq_getElem inside⟩
    · have := fresh_unslashed toM step h.genesis (Nat.le_of_not_lt inside) foundN
      simp [this] at slashedN
  have cleanM : bm.slashed = false := by
    cases flag : bm.slashed
    · rfl
    · exact absurd ⟨bm, foundM, flag⟩ notM
  have earlyN : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps postR.chainSteps) h.early
  have lateM : (getCurrentEpoch m.state).toNat < bm.withdrawableEpoch.toNat := by
    have holds := Run.invariant (Genesis.invariant h.genesis) toM
    have bound := UInt64.le_iff_toNat_le.mp (holds.exitsOrdered bm (Array.mem_of_getElem? foundM))
    by_cases exited : bm.exitEpoch ≤ getCurrentEpoch m.state
    · have slashable := (Run.nil.snoc step).newly_slashed_initial_exited_unwithdrawable
        h.caps.activation h.caps.compounding earlyN i bm bn foundM foundN cleanM slashedN exited
      exact UInt64.lt_iff_toNat_lt.mp slashable
    · have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp exited)
      omega
  have epochs : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch m.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps preR.chainSteps)
  have sameNat := congrArg UInt64.toNat sameEpoch
  by_cases unset : au.exitEpoch = FAR_FUTURE_EPOCH
  · have bound := UInt64.le_iff_toNat_le.mp (ordered a (Array.mem_of_getElem? found))
    have far := getCurrentEpoch_succ_lt_farFuture h.twoSlots e.before.state
    by_cases assigned : a.exitEpoch = FAR_FUTURE_EPOCH
    · rw [assigned] at bound
      omega
    · obtain ⟨wc, readC, bC⟩ := slashedC
      obtain ⟨later, readL, lifeL⟩ := life.validators i a found
      obtain rfl : later = wc := Option.some.inj (readL.symm.trans readC)
      have exitC := congrArg UInt64.toNat (lifeL.exitEpoch assigned)
      obtain ⟨charge, member, -, charged⟩ := Run.departure_charge_of_assigned
        ((Run.nil.snoc (Step.slot ok)).append post) i au later foundU readC unset
        (by rw [lifeL.exitEpoch assigned]; exact assigned)
      have late := DirectSafety.Run.departureCharges_epoch_ge_start
        ((Run.nil.snoc (Step.slot ok)).append post) (Nat.le_trans (by decide) fuluU) h.early charge
        member
      omega
  · have keptM := PinSplit4.kept_run toU h.genesis fuluU preR
      (Nat.lt_of_le_of_lt step.chainStep.fork_le earlyN)
    obtain ⟨le1, moved1⟩ := wdKept i au a foundU found unset
    obtain ⟨le2, moved2⟩ := keptM.withdrawable i au bm foundU foundM unset
    have e1 := UInt64.le_iff_toNat_le.mp le1
    have e2 := UInt64.le_iff_toNat_le.mp le2
    have eq1 : a.withdrawableEpoch = au.withdrawableEpoch := moved1.resolve_left (by simp [clean])
    have eq2 : bm.withdrawableEpoch = au.withdrawableEpoch := moved2.resolve_left (by simp [cleanM])
    have := congrArg UInt64.toNat eq1
    have := congrArg UInt64.toNat eq2
    omega

/-- The deposits credited to keys active at C's end, and to keys slashed there, fit the churn.

A key that exits after C's epoch is not withdrawable at any deposit event of C's run.

Its exit epoch is constant once set, and the exit epoch bounds the withdrawable epoch.

A key slashed at C counts only the deposits of events that do not hold it slashed.

An event that raises no balance credits nothing. -/
private theorem deposits_active_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (S P : Finset ValidatorIndex) (apart : Disjoint S P)
    (active : ∀ v ∈ S, ∃ w, counted.validators.data[v.toNat]? = some w ∧
      (getCurrentEpoch counted).toNat < w.exitEpoch.toNat)
    (slashedC : ∀ v ∈ P, ∃ b, counted.validators.data[v.toNat]? = some b ∧ b.slashed = true) :
    3 * (∑ v ∈ S, (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
      tailC).1 + ∑ v ∈ P, depPre eventsC v.toNat) ≤ (pinTerms config pulled anc fin).queueDep := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have located := run_located tailC (Nat.le_trans (by decide) h.fulu) h.early highC replayedC
  refine deposits_scan_le h tailC highC endEpochC replayedC S P fun e member dep => ?_
  rcases located e member dep with unconditional | ⟨u, w, ok, es, contained, replayedEs, inStep, -⟩
  · have zero (i : ℕ) : keyCredit i e = 0 := by
      have := unconditional i
      simp only [keyCredit]
      omega
    simp [zero]
  have forkLe := ((toFin.append fromFin).withdrawnConsolidationCredit_eq_zero tailC h.genesis
    h.early h.delay replayedC e member).2.2
  obtain ⟨-, life, life', ordered, matched, -, epoch⟩ := replay_event_provenance
    (toFin.append fromFin) tailC h.genesis h.early highC endEpochC _ replayedC e member
  have union := deposit_each_le e
    (S ∪ P.filter fun v => ¬ slashedFlagAt e.before.state v.toNat = some true) dep
    (Nat.le_trans (Nat.le_trans (by decide) h.fulu) forkLe) matched fun v inUnion a found => ?_
  · rwa [Finset.sum_union (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) apart)]
      at union
  rcases Finset.mem_union.mp inUnion with inS | inP
  · obtain ⟨wC, foundC, late⟩ := active v inS
    obtain ⟨u, foundU, lifeU⟩ := (life.trans life').validators v.toNat a found
    obtain rfl : u = wC := Option.some.inj (foundU.symm.trans foundC)
    have epoch' : (getCurrentEpoch e.before.state).toNat ≤ (getCurrentEpoch counted).toNat := epoch
    have bound := UInt64.le_iff_toNat_le.mp (ordered a (Array.mem_of_getElem? found))
    have far := getCurrentEpoch_succ_lt_farFuture h.twoSlots e.before.state
    by_cases unset : a.exitEpoch = FAR_FUTURE_EPOCH
    · rw [unset] at bound
      omega
    · have same := congrArg UInt64.toNat (lifeU.exitEpoch unset)
      omega
  · obtain ⟨inP, clean⟩ := Finset.mem_filter.mp inP
    simp only [slashedFlagAt, found, Option.map_some, Option.some.injEq,
      Bool.not_eq_true] at clean
    exact slashed_deposit_held h tailC ok contained replayedEs inStep dep ordered
      (life.trans life') (slashedC v inP) found clean

/-- D-8 (deposit queue): deposits applied on R's branch to V keys, weight 3. -/
theorem bud_deposits (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (∑ v ∈ V, credDepR events v.toNat) ≤ (pinTerms config pulled anc fin).queueDep := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have within := BeaconState.registryWithinLimit_of_lt h.early pulled
  -- The keys of `V` are active at R's epoch, so no deposit event credits a withdrawable one.
  have recent : ∀ i ∈ V.image UInt64.toNat, ∃ w, pulled.validators.data[i]? = some w ∧
      (isActiveValidator w (getCurrentEpoch pulled) = true ∨
        isActiveValidator w (getPreviousEpoch pulled) = true) := by
    intro i hi
    obtain ⟨v, member, rfl⟩ := Finset.mem_image.mp hi
    have listed : v ∈ getActiveValidatorIndices pulled (getCurrentEpoch pulled) := by
      simpa [activeVoters] using (h.voting v member).1
    obtain ⟨u, found, active⟩ := (mem_getActiveValidatorIndices within).mp listed
    exact ⟨u, found, .inl active⟩
  refine bud_deposits_of h tail high endEpoch replayed fun e member deposit => ?_
  have forkLe := ((toFin.append fromFin).withdrawnConsolidationCredit_eq_zero tail h.genesis h.early
    h.delay replayed e member).2.2
  have credited := Run.deposit_credit_le_funding (toFin.append fromFin) tail h.genesis h.early
    h.twoSlots high endEpoch replayed (V.image UInt64.toNat) recent e member deposit
    (Nat.le_trans electra forkLe)
  rw [Finset.sum_image fun _ _ _ _ same => UInt64.toNat_inj.mp same] at credited
  exact credited

/-- Two charges of a run at one position are the same charge. -/
private theorem charge_unique {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {c d : DepartureCharge} (hc : c ∈ tail.departureCharges) (hd : d ∈ tail.departureCharges)
    (same : c.index = d.index) : c = d :=
  List.inj_on_of_nodup_map (DirectSafety.departureCharges_run_indices tail) hc hd same

/-- A state between two runs is of the fork of the start.

The end of the runs must not be of a later fork than the start.

A run never moves the fork back. -/
private theorem fork_eq_of_run {x m y : ForkedBeaconState preset} (r1 : Run config checks x m)
    (r2 : Run config checks m y) (back : y.fork ≤ x.fork) : m.fork = x.fork :=
  Fork.ctorIdx_injective (Nat.le_antisymm
    (Nat.le_trans (fork_le_of_chainSteps r2.chainSteps) back) (fork_le_of_chainSteps r1.chainSteps))

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The slashing credits of C's run are paid for each key by its envelope or its charge.

A key of the split's registry is paid by the envelope on its effective balance.

A key beyond it is paid by the charge that its exit leaves. -/
private theorem slashing_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (env cr : ℕ → ℕ)
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i ≤ env i)
    (created : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, split.validators.data.size ≤ i →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ cr i) :
    (eventsC.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      ∑ i ∈ (Finset.range counted.validators.data.size).filter (fun i =>
          (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
            (counted.validators.data[i]?.map (·.slashed)).getD false = true),
        (if i < split.validators.data.size then
          env i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else cr i) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  refine slashing_credits_le (shared.append fromFin) tailC h.genesis h.early h.caps.compounding
    highC endEpochC _ _ ?_ replayedC
  intro a b step member i inside flag
  obtain ⟨pre, post, -, -, -⟩ := Run.contains_step_facts member h.early
  have sameFork : a.fork = fork :=
    fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at flag
  obtain ⟨unslashedA, slashedB⟩ := flag
  have insideCounted : i < counted.validators.data.size :=
    Nat.lt_of_lt_of_le (Finset.mem_range.mp inside) post.registryLifecycle.size_le
  have unslashedSplit : (split.validators.data[i]?.map (·.slashed)).getD false = false := by
    cases found : split.validators.data[i]? with
    | none => rfl
    | some w =>
      simp [unslashed_of_run pre found (fun u read => by simpa [read] using unslashedA)]
  have slashedCounted : (counted.validators.data[i]?.map (·.slashed)).getD false = true := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at slashedB
    | some w =>
      have marked : w.slashed = true := by simpa [found] using slashedB
      obtain ⟨u, read, kept⟩ := post.slashedPersistence i w found marked
      simp [read, kept]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr insideCounted, unslashedSplit,
    slashedCounted⟩, ?_⟩
  by_cases registered : i < split.validators.data.size
  · simp only [registered, ↓reduceIte, sameFork]
    exact Nat.div_le_div_right (registry step member i registered
      (by simp [unslashedA, slashedB]))
  · simp only [registered, ↓reduceIte, sameFork]
    exact created step member i (Nat.le_of_not_lt registered)
      (by simp [unslashedA, slashedB])

/-- The amount of the departure charge of a key on a run, or 0.

The charge reads the effective balance before the step that assigns the exit. -/
private def chargeAmt {x y : ForkedBeaconState preset} (tail : Run config checks x y) (i : ℕ) :
    ℕ :=
  ((tail.departureCharges.find? fun c => c.index == i).map (·.amount)).getD 0

/-- A charge that meets a test, and is the only one that does, is the first that does. -/
private theorem find_charge {l : List DepartureCharge} {p : DepartureCharge → Bool}
    {c : DepartureCharge} (member : c ∈ l) (hp : p c = true)
    (unique : ∀ d ∈ l, p d = true → d = c) : l.find? p = some c := by
  obtain ⟨d, chosen⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨c, member, hp⟩)
  obtain rfl := unique d (List.mem_of_find?_eq_some chosen) (List.find?_some chosen)
  exact chosen

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that a step slashes with its exit unset is charged its effective balance before the step.

The slashing assigns its exit, so the step records a departure charge of that amount.

The charge of the run at the key is that one. -/
private theorem slash_exit_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (old new : Validator) (foundA : a.state.validators.data[i]? = some old)
    (foundB : b.state.validators.data[i]? = some new) (unset : old.exitEpoch = FAR_FUTURE_EPOCH)
    (slashed : new.slashed = true) :
    effectiveAt a i ≤ chargeAmt tailC i := by
  classical
  unfold chargeAmt
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨pre, post, cut, -, -⟩ := Run.contains_step_facts member h.early
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have assigned : new.exitEpoch ≠ FAR_FUTURE_EPOCH :=
    run_slashed_exit_assigned (((shared.append fromFin).append pre).snoc step) h.genesis
      h.caps.activation h.caps.compounding bEarly h.delay i new foundB slashed
  have inStep : (⟨i, new.exitEpoch.toNat, old.effectiveBalance.toNat⟩ : DepartureCharge) ∈
      step.departureCharges := by
    apply List.mem_filterMap.mpr
    refine ⟨(old, i), ?_, ?_⟩
    · simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using foundA
    · simp [foundB, unset, assigned]
  have inRun : (⟨i, new.exitEpoch.toNat, old.effectiveBalance.toNat⟩ : DepartureCharge) ∈
      tailC.departureCharges := by
    rw [cut, Run.departureCharges_append]
    simp [Run.departureCharges, inStep]
  rw [find_charge inRun (by simp)
    (fun d inD hd => charge_unique tailC inD inRun (by simpa using hd))]
  simp [effectiveAt, foundA]

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key beyond R's registry is charged the amount of its exit and what it gains after it.

An exit that a step assigns by the slashing is the charge of that step.

An earlier exit adds its gains, bands and credits, which `extra` bounds. -/
private theorem created_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (extra : ℕ → ℕ)
    (earlier : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ (i : ℕ), split.validators.data.size ≤ i → ∀ (old : Validator),
        a.state.validators.data[i]? = some old → old.exitEpoch ≠ FAR_FUTURE_EPOCH →
          effectiveAt a i ≤ chargeAmt tailC i + extra i)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (created : split.validators.data.size ≤ i)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    effectiveAt a i ≤ chargeAmt tailC i + extra i := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at flag
  obtain ⟨-, slashedB⟩ := flag
  cases foundA : a.state.validators.data[i]? with
  | none => simp [effectiveAt, foundA]
  | some old =>
    by_cases unset : old.exitEpoch = FAR_FUTURE_EPOCH
    · cases foundB : b.state.validators.data[i]? with
      | none => simp [foundB] at slashedB
      | some new =>
        have marked : new.slashed = true := by simpa [foundB] using slashedB
        exact (slash_exit_charge h fromFin tailC step member i old new foundA foundB unset
          marked).trans (Nat.le_add_right _ _)
    · exact earlier step member i created old foundA unset

/-- The keys whose exit is charged within the run's epochs pay at most the window of the queues.

For such a key `chargeAmt` is the `exitQ` of the run. -/
private theorem charge_amounts_le_queueWindow
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (S : Finset ValidatorIndex)
    (charged : ∀ v ∈ S, ∃ c ∈ tailC.departureCharges,
      c.index = v.toNat ∧ c.epoch ≤ (getCurrentEpoch counted).toNat) :
    ∑ v ∈ S, chargeAmt tailC v.toNat ≤ (pinTerms config pulled anc fin).queueWindow := by
  classical
  have same : ∀ v ∈ S, chargeAmt tailC v.toNat = exitQ tailC v.toNat := by
    intro v member
    obtain ⟨c, inRun, index, epoch⟩ := charged v member
    have unique : ∀ d ∈ tailC.departureCharges, d.index = v.toNat → d = c := fun d inD same =>
      charge_unique tailC inD inRun (same.trans index.symm)
    unfold chargeAmt exitQ
    rw [find_charge inRun (by simp [index]) (fun d inD hd => unique d inD (by simpa using hd)),
      find_charge inRun (by simp [index, epoch])
        (fun d inD hd => unique d inD (by simp at hd; exact hd.1))]
  rw [Finset.sum_congr rfl same]
  refine (sum_exitQ_le tailC ((getCurrentEpoch counted).toNat - 1 + 1)
    (by simp only; omega) S).trans ?_
  exact charges_le_queueWindow h tailC

/-- Either a run has no counted charge of a key and `exitQ` is zero.

Or `exitQ` is the amount of a counted charge of the key.

The counted charges are those whose exit epoch is at most the run's last epoch. -/
private theorem exitQ_cases {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (v : ℕ) :
    ((∀ c ∈ tail.departureCharges, c.index = v → ¬ c.epoch ≤ (getCurrentEpoch y.state).toNat) ∧
      exitQ tail v = 0) ∨
    ∃ c ∈ tail.departureCharges, c.index = v ∧ c.epoch ≤ (getCurrentEpoch y.state).toNat ∧
      exitQ tail v = c.amount := by
  cases found : tail.departureCharges.find? fun c =>
      c.index == v && decide (c.epoch ≤ (getCurrentEpoch y.state).toNat) with
  | none =>
    refine .inl ⟨fun c mem idx le => ?_, by simp [exitQ, found]⟩
    have := List.find?_eq_none.mp found c mem
    simp [idx, le] at this
  | some c =>
    have both := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at both
    exact .inr ⟨c, List.mem_of_find?_eq_some found, both.1, both.2, by simp [exitQ, found]⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A charge of a run is the charge of the stop at its position, on the run after a prefix.

The stop is the state before the step that assigns the exit, and the charge reads its balance. -/
private theorem stop_of_charge {x s y : ForkedBeaconState preset} (fromX : Run config checks x s)
    (tail : Run config checks s y) {c0 : DepartureCharge} (member : c0 ∈ tail.departureCharges)
    {i : ℕ} (index : c0.index = i) :
    ∃ stop : Stop (fromX.append tail) i, stop.charge = some c0 := by
  subst index
  have inTail : c0 ∈ (fromX.append tail).departureCharges := by
    rw [Run.departureCharges_append]
    exact List.mem_append_right _ member
  obtain ⟨stop⟩ := Stop.exists (fromX.append tail) c0.index
  obtain ⟨c, chosen⟩ : ∃ c, stop.charge = some c := by
    cases hc : stop.charge with
    | none =>
      have selected := stop.selected
      rw [hc] at selected
      exact absurd rfl (selected.2 c0 inTail)
    | some c => exact ⟨c, rfl⟩
  have selected := stop.selected
  rw [chosen] at selected
  have cEq : c = c0 := charge_unique _ selected.1 inTail selected.2.1
  subst cEq
  exact ⟨stop, chosen⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at its exit call, from the finalized state.

It is at most the amount of the key's departure charge on the run from the finalized state.

It is also at most the balance shortfall at that state, the debits of the key and one increment.

The debits are its penalties, its sync debits and the partial payments to it. -/
private theorem exitQ_floor (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (val : Validator) (initial : fin.validators.data[v.toNat]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false)
    (charged : exitQ tailC v.toNat ≠ 0) :
    effectiveAt ⟨fork, fin⟩ v.toNat ≤ exitQ tailC v.toNat +
      (effectiveAt ⟨fork, fin⟩ v.toNat - actualBalanceAt ⟨fork, fin⟩ v.toNat) +
      ((events.map (floorPenaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  classical
  obtain ⟨shared⟩ := h.toFin
  -- the charge of `tailC`
  obtain ⟨c0, member0, index0, -, amount0⟩ : ∃ c ∈ tailC.departureCharges,
      c.index = v.toNat ∧ c.epoch ≤ (getCurrentEpoch counted).toNat ∧
        exitQ tailC v.toNat = c.amount := by
    rcases exitQ_cases tailC v.toNat with ⟨-, zero⟩ | found
    · exact absurd zero charged
    · exact found
  obtain ⟨stop, chosen⟩ := stop_of_charge fromFin tailC member0 index0
  -- the ends
  obtain ⟨w, final, _⟩ := (fromFin.append tailC).registryLifecycle.validators v.toNat val initial
  have cleanEnd := clean w final
  have unslashed : val.slashed = false := unslashed_of_run (fromFin.append tailC) initial clean
  have stopEarly : stop.state.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps stop.post.chainSteps) h.early
  have near := h.near
  have toEnd := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps stop.post.chainSteps)
  have endpoint :
      (getCurrentEpoch stop.state.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    simp only at toEnd
    omega
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix stop.pre stop.post
    (getCurrentEpoch pulled).toNat events (by rw [stop.split]; exact replayed)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, window, -, -, -⟩ := id h.guard
  have loss := Stop.selected_charge_loss stop chosen shared h.genesis h.caps h.bands.1 h.twoSlots
    h.delay stopEarly val w initial final unslashed cleanEnd activated endpoint beforeOk 0
    (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
    (by have := h.facts.quotient; omega)
    (fun {m n} pre step post split => by
      have mOrder := UInt64.le_iff_toNat_le.mp
        (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
      have xOrder := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
      refine ⟨?_, ?_, ?_⟩
      · unfold driftHorizon at window
        simp only at window mOrder toEnd xOrder ⊢
        have half : (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat =
          preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 := by simp
        rw [half]
        omega
      · rw [PinSplit6.mspq_fusaka (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps))]
      · intro found replay
        exact no_crossing_of_regime shared pre h.genesis h.caps step
          (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) stopEarly)
          (.inl (Nat.le_trans (Nat.le_trans (by decide) h.fulu)
            (fork_le_of_chainSteps pre.chainSteps))) replay)
  have bound : (if FirstDown stop.pre v.toNat then preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      else 0) ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by split <;> omega
  have penalties :=
    (isPrefix.sublist.map (floorPenaltyDebit v.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
  have partials :=
    (isPrefix.sublist.map (floorPartialDebit v)).sum_le_sum fun _ _ => Nat.zero_le _
  rw [amount0] at *
  omega

/-- A run has a charge at a position exactly when `riseScan` has seen one. -/
private theorem riseScan_fst {x : ForkedBeaconState preset} (v high : ℕ)
    {y : ForkedBeaconState preset} (tail : Run config checks x y) :
    (riseScan (config := config) (checks := checks) v high tail).1 = true ↔
      ∃ c ∈ tail.departureCharges, c.index = v := by
  induction tail with
  | nil => simp [riseScan, Run.departureCharges]
  | snoc pre step ih =>
    simp only [riseScan, Run.departureCharges, Bool.or_eq_true, ih, List.any_eq_true,
      List.mem_append, beq_iff_eq]
    constructor
    · rintro (⟨c, member, same⟩ | ⟨c, member, same⟩)
      · exact ⟨c, .inl member, same⟩
      · exact ⟨c, .inr member, same⟩
    · rintro ⟨c, member | member, same⟩
      · exact .inl ⟨c, member, same⟩
      · exact .inr ⟨c, member, same⟩

/-- A key with no charge on the run has no rise after its exit. -/
private theorem riseQ_eq_zero {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) (none : ∀ c ∈ tail.departureCharges, c.index ≠ v) : riseQ tail high v = 0 := by
  have unseen : (riseScan (config := config) (checks := checks) v high tail).1 ≠ true := fun seen =>
    let ⟨c, member, same⟩ := (riseScan_fst v high tail).mp seen
    none c member same
  simp [riseQ, unseen]

/-- A key of `K5` that has a charge on the run exits by the run's last epoch. -/
private theorem charge_epoch_le_of_K5 (early : fork < .glamsterdam)
    {x : ForkedBeaconState preset} (tail : Run config checks x ⟨fork, counted⟩)
    {v : ValidatorIndex} (member : v ∈ K5 counted V) :
    ∀ c ∈ tail.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat := by
  intro c charged same
  obtain ⟨w, found, assigned, epoch⟩ := Run.departure_charge_exit tail c charged
  have within := BeaconState.registryWithinLimit_of_lt early counted
  have inK5 := Finset.mem_filter.mp member
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inK5
  obtain ⟨⟨listed, -⟩, notActive, -⟩ := inK5
  have notCurrent : v ∉ getActiveValidatorIndices counted (getCurrentEpoch counted) := fun now =>
    notActive (by simpa [AC, activeVoters] using now)
  rcases listed with now | before
  · exact absurd now notCurrent
  obtain ⟨u, foundU, activeBefore⟩ := (mem_getActiveValidatorIndices within).mp before
  rw [same] at found
  have equal : u = w := Option.some.inj (foundU.symm.trans found)
  subst equal
  have notNow : isActiveValidator u (getCurrentEpoch counted) = false := by
    cases now : isActiveValidator u (getCurrentEpoch counted)
    · rfl
    · exact absurd ((mem_getActiveValidatorIndices within).mpr ⟨u, foundU, now⟩) notCurrent
  have previous := getPreviousEpoch_toNat counted
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeBefore
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not] at notNow
  have low := UInt64.le_iff_toNat_le.mp activeBefore.1
  rw [← epoch]
  rcases notNow with notLow | notHigh
  · exact absurd (UInt64.le_iff_toNat_le.mpr (by omega)) notLow
  · have : ¬ (getCurrentEpoch counted).toNat < u.exitEpoch.toNat :=
      fun lt => notHigh (UInt64.lt_iff_toNat_lt.mpr lt)
    omega

/-- The quarter of any total has a base reward per increment, if any total has one.

The factor times the increment fits in a `UInt64` for every total, and the quarter is positive.
-/
private theorem quarter_base_ok (facts : PinPresetFacts preset) {total perIncrement : Gwei}
    (perOk : getBaseRewardPerIncrement preset total = .ok perIncrement) (T : Gwei) :
    ∃ pq, getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq := by
  have size := facts.incrementSize
  have positive : 0 < (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei).toNat := by
    split
    · rename_i big
      simp only [UInt64.toNat_div]
      show 0 < T.toNat / 4
      omega
    · simp only [UInt64.toNat_div]
      show 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat / 5
      omega
  generalize (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
    else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei) = q at positive ⊢
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at perOk
  obtain ⟨scaled, scaledOk, -⟩ := perOk
  have root : integerSquareroot q ≠ 0 := fun zero => by
    have value := toNat_integerSquareroot q
    rw [zero] at value
    have := Nat.sqrt_pos.mpr positive
    simp only [UInt64.toNat_zero] at value
    omega
  refine ⟨scaled / integerSquareroot q, ?_⟩
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff]
  exact ⟨scaled, scaledOk, divChecked_ok_iff.mpr ⟨root, by rw [UInt64.toNat_div]⟩⟩

/-- The pin has a rate `P` that bounds the reward rate at every state of a run from `fin`.

The rate is the base reward per increment that `pinTerms` reads, or zero if there is none.

The rate also bounds the largest gain rate, which `gainRateMax` is. -/
private theorem pin_rate_exists (h : Setting config checks g split fin pulled anc counted V) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ≤
          (pinTerms config pulled anc fin).gainRateMax ∧
      ∀ {m : BeaconState preset fork} (_toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩),
        (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
        ∀ total perIncrement : Gwei, getTotalActiveBalance m = .ok total →
          getBaseRewardPerIncrement preset total = .ok perIncrement →
          perIncrement.toNat *
              ((∑ i ∈ (getActiveValidatorIndices m (getPreviousEpoch m)).toFinset,
                effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
                  preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
            P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  have gainMax : (pinTerms config pulled anc fin).gainRateMax =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((getBaseRewardPerIncrement preset
          (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
            (getTotalActiveBalance pulled).toOption.getD 0 / 4
          else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := rfl
  by_cases anyOk : ∃ total perIncrement : Gwei,
      getBaseRewardPerIncrement preset total = .ok perIncrement
  · obtain ⟨total, perIncrement, perOk⟩ := anyOk
    obtain ⟨pq, pqOk⟩ :=
      quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
    refine ⟨pq.toNat, by rw [pqOk]; rfl, ?_, fun toM inside =>
      rate_of_guard h toM inside (Or.inl rfl) pqOk⟩
    rw [gainMax, pqOk]
    simp only [Except.toOption, Option.getD_some, le_refl]
  · refine ⟨0, ?_, ?_, fun _ _ total perIncrement _ perOk =>
      absurd ⟨total, perIncrement, perOk⟩ anyOk⟩
    · cases hr : getBaseRewardPerIncrement preset
          (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
            (getTotalActiveBalance pulled).toOption.getD 0 / 4
          else preset.EFFECTIVE_BALANCE_INCREMENT / 5) with
      | error e => rfl
      | ok p => exact absurd ⟨_, p, hr⟩ anyOk
    · simp

/-- The pin's rate bounds the reward rate at each state of a prefix of C's tail.

The prefix ends at most one epoch after the call, and its states are of the fork of the setting. -/
private theorem key_rate_forked (h : Setting config checks g split fin pulled anc counted V) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      ∀ a : ForkedBeaconState preset, Run config checks ⟨fork, split⟩ a → a.fork ≤ fork →
      (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
      ∀ total perIncrement : Gwei, getTotalActiveBalance a.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices a.state
          (getPreviousEpoch a.state)).toFinset, effectiveAt a j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  obtain ⟨P, hP, -, rateAll⟩ := pin_rate_exists h
  obtain ⟨fromFin⟩ := h.fromFin
  refine ⟨P, hP, fun a run forkLe near total perIncrement totalOk perOk => ?_⟩
  obtain ⟨af, as⟩ := a
  have sameFork : af = fork := fork_eq_of_run run Run.nil forkLe
  subst sameFork
  simp only at near totalOk perOk ⊢
  exact rateAll (fromFin.append run) (by omega) total perIncrement totalOk perOk

/-- The pin's rate bounds the reward rate at every state of a prefix of C's tail.

The prefix ends at most one epoch after the call.

Each state of its balance path is the end of a run from the finalized block.

So the guard applies. -/
private theorem key_rate_pre (h : Setting config checks g split fin pulled anc counted V)
    {a : BeaconState preset fork} (pre : Run config checks ⟨fork, split⟩ ⟨fork, a⟩)
    (near : (getCurrentEpoch a).toNat ≤ (getCurrentEpoch pulled).toNat + 1) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      ∀ z ∈ pre.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  obtain ⟨P, hP, rate⟩ := key_rate_forked h
  refine ⟨P, hP, fun z member total perIncrement totalOk perOk => ?_⟩
  obtain ⟨r1, r2, -⟩ := balancePath_endpoint pre Run.nil
    (show (⟨fork, a⟩ : ForkedBeaconState preset).fork ≤
      (⟨fork, split⟩ : ForkedBeaconState preset).fork from Nat.le_refl _) member
  have order : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch a).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
  exact rate z r1 (fork_le_of_chainSteps r2.chainSteps) (by omega) total perIncrement totalOk
    perOk

/-- The depth times the reward rate for each increment stays below an eleventh of an increment.

It follows from the second test of the low rate at an aligned bound.

Its units are the gwei of the reward, scaled by the weight denominator. -/
private theorem rate_per_increment (I WD F P e0 D : ℕ) (hI : 0 < I) (hWD : 0 < WD)
    (alignedE : e0 % I = 0) (rateLow : 11 * D * (e0 / I * P * F / WD + 1) ≤ e0) :
    11 * D * (P * F) < WD * I := by
  rcases Nat.eq_zero_or_pos D with zero | pos
  · subst zero
    simpa using Nat.mul_pos hWD hI
  · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero alignedE
    have e : e0 / I = m := by rw [hm, Nat.mul_div_cancel_left _ hI]
    rw [e] at rateLow
    have big : 11 ≤ e0 := Nat.le_trans (by
      have := Nat.mul_le_mul (show 11 ≤ 11 * D by omega)
        (Nat.le_add_left 1 (m * P * F / WD))
      simpa using this) rateLow
    have mPos : 0 < m := Nat.pos_of_ne_zero (fun z => by rw [z] at hm; omega)
    have a : m * P * F < WD * (m * P * F / WD + 1) := Nat.lt_mul_div_succ _ hWD
    have b := Nat.mul_lt_mul_of_pos_left a (show 0 < 11 * D by omega)
    have d := Nat.mul_le_mul_left WD rateLow
    have f : (11 * D * (P * F)) * m < (WD * I) * m := by
      calc (11 * D * (P * F)) * m = 11 * D * (m * P * F) := by ring
        _ < 11 * D * (WD * (m * P * F / WD + 1)) := b
        _ = WD * (11 * D * (m * P * F / WD + 1)) := by ring
        _ ≤ WD * e0 := d
        _ = (WD * I) * m := by rw [hm]; ring
    exact Nat.lt_of_mul_lt_mul_right f

/-- The base reward per increment is at least four.

The root of a quarter total is below `2 ^ 31`, and `room` makes the scaled factor at least `2 ^ 33`.

Below the small total the root is at most a fifth of an increment, which the factor covers.

The read succeeds, since the quarter total is positive and `fits` bounds the scaled factor. -/
private theorem four_le_perIncrement (h : Setting config checks g split fin pulled anc counted V) :
    4 ≤ (pinTerms config pulled anc fin).perIncrement := by
  have definition : (pinTerms config pulled anc fin).perIncrement =
      ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat := rfl
  obtain ⟨q, hq⟩ : ∃ q : Gwei, q = (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5) := ⟨_, rfl⟩
  rw [← hq] at definition
  have small : q.toNat < 2 ^ 62 ∨ 5 * q.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [hq]
    split_ifs
    · left
      have : ((getTotalActiveBalance pulled).toOption.getD 0).toNat < 2 ^ 64 :=
        ((getTotalActiveBalance pulled).toOption.getD 0).toNat_lt
      rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
    · right
      rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
  have room := h.facts.room
  have reward := h.facts.reward
  have positive : 0 < q.toNat := by
    have size := h.facts.incrementSize
    rw [hq]
    split_ifs
    · rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
    · rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
  obtain ⟨per, computed⟩ :=
    DirectSafety.Apriori.Internal.perIncrement_exists positive h.facts.fits
  rw [computed] at definition
  simp only [Except.toOption, Option.getD_some] at definition
  have formula := toNat_getBaseRewardPerIncrement computed
  have rootPos : 0 < q.toNat.sqrt := Nat.sqrt_pos.mpr positive
  have rootSmall : 4 * q.toNat.sqrt ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat := by
    rcases small with low | tiny
    · have : q.toNat.sqrt < 2 ^ 31 := Nat.sqrt_lt'.mpr (by norm_num at low ⊢; omega)
      omega
    · have : q.toNat.sqrt ≤ q.toNat := Nat.sqrt_le_self _
      have : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat :=
        Nat.le_mul_of_pos_right _ reward
      omega
  have four : 4 ≤ per.toNat := by
    rw [formula]
    exact (Nat.le_div_iff_mul_le rootPos).mpr rootSmall
  rw [definition]
  exact four

/-- Rounding up a whole number of increments gives it back. -/
private theorem div_round_mul (I u : ℕ) (hI : 0 < I) : (I * u + I - 1) / I = u := by
  rw [show I * u + I - 1 = I * u + (I - 1) by omega, Nat.mul_add_div hI,
    Nat.div_eq_of_lt (show I - 1 < I by omega)]
  simp

/-- The gain on a positive number of increments is below an eleventh of them.

The rate for each increment is the one that `rate_per_increment` bounds. -/
private theorem gain_lt (I WD F P D k : ℕ) (hk : 0 < k)
    (key : 11 * D * (P * F) < WD * I) : 11 * (D * (k * P * F / WD)) < I * k := by
  have fl : WD * (k * P * F / WD) ≤ k * P * F := Nat.mul_div_le _ _
  have h1 : WD * (11 * (D * (k * P * F / WD))) < WD * (I * k) :=
    calc WD * (11 * (D * (k * P * F / WD))) = 11 * D * (WD * (k * P * F / WD)) := by ring
      _ ≤ 11 * D * (k * P * F) := Nat.mul_le_mul_left _ fl
      _ = k * (11 * D * (P * F)) := by ring
      _ < k * (WD * I) := Nat.mul_lt_mul_of_pos_left key hk
      _ = WD * (I * k) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

/-- The gain on a credit rounded up to an increment is at most an eleventh of the credit.

The credit is a whole number of increments, so its rounding up is itself. -/
private theorem gain_credit_le (I WD F P D C : ℕ) (hI : 0 < I)
    (alignedC : C % I = 0) (key : 11 * D * (P * F) < WD * I) :
    11 * (D * ((C + I - 1) / I * P * F / WD)) ≤ C := by
  obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero alignedC
  subst hu
  rw [div_round_mul I u hI]
  rcases Nat.eq_zero_or_pos u with zero | pos
  · subst zero
    simp
  · exact (gain_lt I WD F P D u pos key).le

/-- The gain at the stake `e0 + C` over `k` epochs splits into two parts.

They are the gain on the credits and the gain at the base stake `e0`.

The floor costs one unit per epoch. -/
private theorem gain_split_flat (I WD F P e0 C k depth : ℕ) (hI : 0 < I) (hk : k ≤ depth)
    (alignedE : e0 % I = 0) (alignedC : C % I = 0) :
    k * ((e0 + C) / I * P * F / WD) ≤
      depth * ((C + I - 1) / I * P * F / WD) + (depth * (e0 / I * P * F / WD) + depth) := by
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero alignedE
  obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero alignedC
  rw [← Nat.mul_add, Nat.mul_div_cancel_left _ hI, Nat.mul_div_cancel_left _ hI,
    div_round_mul I b hI]
  have floor := Nat.add_div_le_div_add_div_add_one (a * P * F) (b * P * F) WD
  have split : (a + b) * P * F = a * P * F + b * P * F := by ring
  rw [split]
  calc k * ((a * P * F + b * P * F) / WD)
      ≤ depth * ((a * P * F + b * P * F) / WD) := Nat.mul_le_mul_right _ hk
    _ ≤ depth * (a * P * F / WD + b * P * F / WD + 1) := Nat.mul_le_mul_left _ floor
    _ = depth * (b * P * F / WD) + (depth * (a * P * F / WD) + depth) := by ring

/-- The gain of one key's flows is at most the linear rate of the flows.

It drops the floor of the increments and the floor of the rate. -/
private theorem gain_lin (I WD FP D Z : ℕ) :
    10 * (I * WD) * (D * (11 * Z / (10 * I) * FP / WD)) ≤ 11 * D * FP * Z := by
  have floorLe : WD * (11 * Z / (10 * I) * FP / WD) ≤ 11 * Z / (10 * I) * FP :=
    Nat.mul_div_le _ _
  have increments : 10 * I * (11 * Z / (10 * I)) ≤ 11 * Z := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  calc 10 * (I * WD) * (D * (11 * Z / (10 * I) * FP / WD))
      = 10 * I * D * (WD * (11 * Z / (10 * I) * FP / WD)) := by ring
    _ ≤ 10 * I * D * (11 * Z / (10 * I) * FP) := Nat.mul_le_mul_left _ floorLe
    _ = D * FP * (10 * I * (11 * Z / (10 * I))) := by ring
    _ ≤ D * FP * (11 * Z) := Nat.mul_le_mul_left _ increments
    _ = 11 * D * FP * Z := by ring

/-- The gain on whole increments of a stake, at eleven tenths, is at most a tenth of the stake.

The rate for each increment is the one that `rate_per_increment` bounds. -/
private theorem gain_tenth (I WD F P D Zr : ℕ)
    (key : 11 * D * (P * F) < WD * I) :
    D * (11 * Zr / (10 * I) * P * F / WD) ≤ Zr / 10 := by
  have lin := gain_lin I WD (P * F) D Zr
  rw [Nat.mul_assoc (11 * Zr / (10 * I)) P F]
  generalize D * (11 * Zr / (10 * I) * (P * F) / WD) = G at lin ⊢
  have pos : 0 < I * WD := by
    have := Nat.lt_of_le_of_lt (Nat.zero_le _) key
    rwa [Nat.mul_comm] at this
  have rate : 11 * D * (P * F) * Zr ≤ WD * I * Zr := Nat.mul_le_mul_right Zr key.le
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  refine Nat.le_of_mul_le_mul_left ?_ pos
  calc I * WD * (G * 10) = 10 * (I * WD) * G := by ring
    _ ≤ 11 * D * (P * F) * Zr := lin
    _ ≤ WD * I * Zr := rate
    _ = I * WD * Zr := by ring

/-- The gain at the base stake, with its tenth, is within `rise`'s gain slack. -/
private theorem base_absorb (D Df q : ℕ) (hDf : D ≤ Df) :
    D * q + D + (D * q + D) / 10 ≤ Df * ((11 * q + 9) / 10 + 3) := by
  have step : 11 * q ≤ 10 * ((11 * q + 9) / 10) := by omega
  have scaled := Nat.mul_le_mul_left D step
  have left : D * (11 * q) = 11 * (D * q) := by ring
  have right : D * (10 * ((11 * q + 9) / 10)) = 10 * (D * ((11 * q + 9) / 10)) := by ring
  have widen := Nat.mul_le_mul_right ((11 * q + 9) / 10 + 3) hDf
  have expand : D * ((11 * q + 9) / 10 + 3) = D * ((11 * q + 9) / 10) + 3 * D := by ring
  omega

/-- The gain of a key's flows and of the base stake is at most its flow gain, a unit and the base.

The joint floor of the flows and the base stake splits by kind with one step.

With no flow there is no step. -/
private theorem flow_gain_split (I WD F P D Dt Df q Zk Z' : ℕ)
    (key : 11 * D * (P * F) < WD * I) (hDt : D ≤ Dt) (hDf : D ≤ Df) (hZ : Zk ≤ Z') :
    D * (11 * (Zk + (D * q + D)) / (10 * I) * P * F / WD) + (D * q + D) ≤
      Dt * (11 * Z' / (10 * I) * P * F / WD) +
        (if 0 < Z' then Dt * (P * F / WD + 2) else 0) + Df * ((11 * q + 9) / 10 + 3) := by
  have tenth := gain_tenth I WD F P D (D * q + D) key
  have absorb := base_absorb D Df q hDf
  have monoGain : D * (11 * Zk / (10 * I) * P * F / WD) ≤
      Dt * (11 * Z' / (10 * I) * P * F / WD) :=
    Nat.mul_le_mul hDt (Nat.div_le_div_right (Nat.mul_le_mul_right F (Nat.mul_le_mul_right P
      (Nat.div_le_div_right (Nat.mul_le_mul_left 11 hZ)))))
  rcases Nat.eq_zero_or_pos Zk with zero | pos
  · subst zero
    simp only [Nat.zero_add]
    split_ifs <;> omega
  · have posZ : 0 < Z' := Nat.lt_of_lt_of_le pos hZ
    have joint : 11 * (Zk + (D * q + D)) / (10 * I) ≤
        11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1 := by
      have := Nat.add_div_le_div_add_div_add_one (11 * Zk) (11 * (D * q + D)) (10 * I)
      rwa [← Nat.mul_add] at this
    have step : D * (11 * (Zk + (D * q + D)) / (10 * I) * P * F / WD) ≤
        D * ((11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1) * P * F / WD) :=
      Nat.mul_le_mul_left D (Nat.div_le_div_right (Nat.mul_le_mul_right F
        (Nat.mul_le_mul_right P joint)))
    have split : (11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1) * P * F =
        11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F + P * F := by ring
    have floors : (11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F + P * F) /
        WD ≤ 11 * Zk / (10 * I) * P * F / WD + 11 * (D * q + D) / (10 * I) * P * F / WD +
          P * F / WD + 2 := by
      have one := Nat.add_div_le_div_add_div_add_one
        (11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F) (P * F) WD
      have two := Nat.add_div_le_div_add_div_add_one (11 * Zk / (10 * I) * P * F)
        (11 * (D * q + D) / (10 * I) * P * F) WD
      omega
    rw [split] at step
    have wide := Nat.mul_le_mul_left D floors
    have expand : ∀ A B C : ℕ, D * (A + B + C + 2) = D * A + D * B + D * C + 2 * D :=
      fun A B C => by ring
    rw [expand] at wide
    have unit : D * (P * F / WD + 2) ≤ Dt * (P * F / WD + 2) := Nat.mul_le_mul_right _ hDt
    have unitSplit : D * (P * F / WD + 2) = D * (P * F / WD) + 2 * D := by ring
    simp only [posZ, ↓reduceIte]
    omega

/-- The closure test of the credit ceiling with the credits rounded down to increments.

The stake above `e0` is the credits, the slack `W` and the gain at the base stake.

The gain on the rounded credits is at most an eleventh of them.

Rounding down leaves less than an increment of that stake unrounded.

The increment of the bound covers it. -/
private theorem ceiling_closed_floor (I WD F P e0 D Cr Cr' S W C q : ℕ)
    (hq : q = e0 / I * P * F / WD) (hI : 0 < I) (key : 11 * D * (P * F) < WD * I)
    (hC : C = I * (11 * (Cr' + W + D * q + D) / (10 * I))) (start : S + Cr ≤ e0 + Cr' + W) :
    S + Cr + (D * ((C + I - 1) / I * P * F / WD) + (D * q + D)) < e0 + C + I := by
  subst hq
  have alignedC : C % I = 0 := by
    rw [hC]
    exact Nat.mul_mod_right _ _
  have credit := gain_credit_le I WD F P D C hI alignedC key
  have div := Nat.div_add_mod (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D)) (10 * I)
  have lt := Nat.mod_lt (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D)) (show 0 < 10 * I by omega)
  have times : 10 * I * (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D) / (10 * I)) = 10 * C := by
    rw [hC]
    ring
  omega

/-- A number below an aligned bound by less than an increment rounds down to at most the bound.

Rounding down is to a multiple of the increment. -/
private theorem floor_le_of_lt {B E I : ℕ} (hI : 0 < I) (aligned : E % I = 0)
    (lt : B < E + I) : B - B % I ≤ E := by
  obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero aligned
  have qlt : B / I < u + 1 := (Nat.div_lt_iff_lt_mul hI).mpr (by
    have : (u + 1) * I = E + I := by rw [hu]; ring
    omega)
  have mul : I * (B / I) ≤ I * u := Nat.mul_le_mul_left _ (by omega)
  have div := Nat.div_add_mod B I
  omega

/-- The arithmetic of the credit ceiling, for any run.

The bound `e0` on the effective balance, with the credits rounded down to increments, is closed.

The gain of any number of epochs up to the depth is at most the gain at the depth.

That gain is a tenth of the credits, the slack and the gain at the base stake. -/
private theorem ceiling_arith (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (P depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    (e0 + C) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
      S + Cr + (gainOn preset depth P C + (depth * q + depth)) <
        e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
      (∀ k, k ≤ depth → k * ((e0 + C) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ≤
        gainOn preset depth P C + (depth * q + depth)) ∧
      gainOn preset depth P C = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gainOn preset depth P C ≤ Cr' + W + depth * q + depth := by
  have closed := ceiling_closed_floor preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat F P e0 depth Cr Cr' S W C q hq incPos key hC start
  have alignedC : C % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [hC]
    exact Nat.mul_mod_right _ _
  have credit := gain_credit_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat F P depth C incPos alignedC key
  have rounded := Nat.mul_div_le (11 * (Cr' + W + depth * q + depth))
    (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
  have times : 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) =
        10 * C := by
    rw [hC]
    ring
  subst hF
  have alignedE : (e0 + C) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero alignedE0)
      (Nat.dvd_of_mod_eq_zero alignedC))
  refine ⟨alignedE, closed, fun k within => ?_, ?_, ?_⟩
  · have split := gain_split_flat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 C k depth
      incPos within alignedE0 alignedC
    rw [← hq] at split
    exact split
  · unfold gainOn
    rw [hC, div_round_mul _ _ incPos]
  · unfold gainOn
    omega

/-- A key's balance along a run is at most a stake bound, its credits and the gain at the bound.

The bound `e0` on the effective balance, with the credits rounded down to increments, is closed.

The stake above `e0` is the credits, the slack `W` and the gain at the base stake.

The rate premise is that of the low regime, at the depth of the call.

The gain on the rounded credits is at most a tenth of that stake. -/
private theorem c_ceiling_abstract {n y : ForkedBeaconState preset}
    (post : Run config checks n y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ n.fork)
    (i : ℕ) (inside : i < n.state.validators.data.size) (high P capHigh : ℕ)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt n i ≤ capHigh)
    (capCeil : ∀ z ∈ post.balancePath, PinSplit2.capAt z i ≤ capHigh)
    (rate : ∀ z ∈ post.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt n i) capHigh ≤ S)
    (startEff : effectiveAt n i ≤ e0 + C)
    (credits : netScan i high post +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post).1 ≤ Cr)
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    ∃ gc, gc = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gc ≤ Cr' + W + depth * q + depth ∧
      (∀ z ∈ post.balancePath, min (actualBalanceAt z i) capHigh ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      effectiveAt y i ≤ e0 + C := by
  obtain ⟨alignedE, closed, splitAll, hform, hten⟩ := ceiling_arith incPos P depth Cr Cr' e0 C S W F
    q hF hq alignedE0 hC key start
  subst hF
  have split := splitAll _ epochs
  have bound : PinSplit2.creditBound post i high (e0 + C) P capHigh ≤
      S + Cr + (gainOn preset depth P C + (depth * q + depth)) := by
    unfold PinSplit2.creditBound
    exact le_trans (le_of_eq (by ring)) (Nat.add_le_add (Nat.add_le_add startBal credits) split)
  have fixpoint : max (effectiveAt n i) (min capHigh
      (PinSplit2.creditBound post i high (e0 + C) P capHigh -
        PinSplit2.creditBound post i high (e0 + C) P capHigh %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le startEff (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt bound closed)))
  obtain ⟨-, -, third, fourth⟩ := PinSplit2.Run.effective_floor_pair post early fulu i inside 0 0
    capHigh high (e0 + C) P
  have balances := fourth alignedCap startCap capCeil (fun z member => .inr (rate z member))
    endEpoch fixpoint
  refine ⟨gainOn preset depth P C, hform, hten,
    fun z member => Nat.le_trans (balances z member) bound, ?_⟩
  · refine Nat.le_trans (third _ alignedCap startCap balances capCeil).1 ?_
    rw [Nat.min_comm]
    exact fixpoint

/-- A key's balance along a run that makes it compound has the ceiling of a run with one cap.

The run splits at the step that makes the key compound.

Before the step the balance counts up to `lo`, and after it up to `hi`.

The ceiling is that of `c_ceiling_abstract`, with the credits of the step added.

The step leaves its balance within the smaller of its balance before it and `lo`, plus its credits.

So the balance after the step is at most the ceiling before it, plus the credits of the step.

Both parts take the same closed bound `e0 + C`, and their epochs add up to those of the run. -/
private theorem c_ceiling_abstract_flip {x m n y : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m n) (post : Run config checks n y)
    (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (high P lo hi : ℕ)
    (alignedLo : lo % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (alignedHi : hi % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0) (loLe : lo ≤ hi)
    (startCap : effectiveAt x i ≤ lo)
    (capsPre : ∀ z ∈ pre.balancePath, PinSplit2.capAt z i ≤ lo)
    (capsPost : ∀ z ∈ post.balancePath, PinSplit2.capAt z i ≤ hi)
    (rate : ∀ z, z ∈ pre.balancePath ∨ z ∈ post.balancePath → ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt x i) lo ≤ S)
    (startEff : effectiveAt x i ≤ e0 + C)
    (junction : actualBalanceAt n i ≤ min (actualBalanceAt m i) lo +
      stepCredit (fun _ => true) (fun _ => true) i step)
    (keepEff : effectiveAt n i = effectiveAt m i)
    (credits : netScan i high pre + (creditScan (fun _ => false)
        (fun s => decide (s ≠ .rewards)) i high pre).1 +
      stepCredit (fun _ => true) (fun _ => true) i step + netScan i high post +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post).1 ≤ Cr)
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    ∃ gc, gc = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gc ≤ Cr' + W + depth * q + depth ∧
      (∀ z ∈ pre.balancePath, min (actualBalanceAt z i) lo ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      (∀ z ∈ post.balancePath, min (actualBalanceAt z i) hi ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      effectiveAt y i ≤ e0 + C := by
  obtain ⟨alignedE, closed, splitAll, hform, hten⟩ := ceiling_arith incPos P depth Cr Cr' e0 C S W F
    q hF hq alignedE0 hC key start
  subst hF
  have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
  have epochPre := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have epochPost := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have forkM : m.fork < .glamsterdam := Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps) early
  have fuluN : .fusaka ≤ n.fork :=
    Nat.le_trans fulu (fork_le_of_chainSteps (pre.snoc step).chainSteps)
  have insideN : i < n.state.validators.data.size :=
    Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps (pre.snoc step).chainSteps)
  have split := splitAll ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat +
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat)) (by omega)
  rw [Nat.add_mul] at split
  have boundPre : PinSplit2.creditBound pre i high (e0 + C) P lo ≤
      S + Cr + (gainOn preset depth P C + (depth * q + depth)) := by
    unfold PinSplit2.creditBound
    omega
  have fixPre : max (effectiveAt x i) (min lo (PinSplit2.creditBound pre i high (e0 + C) P lo -
      PinSplit2.creditBound pre i high (e0 + C) P lo %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le startEff (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt boundPre closed)))
  obtain ⟨-, -, thirdPre, fourthPre⟩ := PinSplit2.Run.effective_floor_pair pre
    forkM fulu i inside 0 0 lo high (e0 + C) P
  have balPre := fourthPre alignedLo startCap capsPre
    (fun z member => .inr (rate z (.inl member))) (by omega) fixPre
  obtain ⟨front, atLast⟩ := Run.balancePath_last pre
  have mPre : min (actualBalanceAt m i) lo ≤
      PinSplit2.creditBound pre i high (e0 + C) P lo :=
    balPre m (by rw [atLast]; simp)
  have effM : effectiveAt m i ≤ e0 + C := by
    refine Nat.le_trans (thirdPre _ alignedLo startCap balPre capsPre).1 ?_
    rw [Nat.min_comm]
    exact fixPre
  have effLo : effectiveAt m i ≤ lo := by
    have := (thirdPre _ alignedLo startCap balPre capsPre).1
    omega
  have boundPost : PinSplit2.creditBound post i high (e0 + C) P hi ≤
      S + Cr + (gainOn preset depth P C + (depth * q + depth)) := by
    unfold PinSplit2.creditBound at mPre ⊢
    omega
  have fixPost : max (effectiveAt n i) (min hi (PinSplit2.creditBound post i high (e0 + C) P hi -
      PinSplit2.creditBound post i high (e0 + C) P hi %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le (keepEff ▸ effM) (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt boundPost closed)))
  obtain ⟨-, -, thirdPost, fourthPost⟩ := PinSplit2.Run.effective_floor_pair post early fuluN i
    insideN 0 0 hi high (e0 + C) P
  have balPost := fourthPost alignedHi (by omega) capsPost
    (fun z member => .inr (rate z (.inr member))) endEpoch fixPost
  refine ⟨gainOn preset depth P C, hform, hten,
    fun z member => Nat.le_trans (balPre z member) boundPre,
    fun z member => Nat.le_trans (balPost z member) boundPost, ?_⟩
  refine Nat.le_trans (thirdPost _ alignedHi (by omega) balPost capsPost).1 ?_
  rw [Nat.min_comm]
  exact fixPost

open DirectSafety.Apriori.Internal in
/-- The amounts of the queued partial withdrawals of a key that are due by a cutoff.

It is spelled as `pinTerms` spells `partialsX` and `partialsR`. -/
private def dueAmount (state : BeaconState preset fork) (electra : .pectra ≤ fork) (i : ℕ)
    (cutoff : ℕ) : ℕ :=
  (((state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
    w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ cutoff).map (·.amount.toNat)).sum

/-- The top of a key at R before the downward band, as `rise` reads it.

It is `pinTerms`' `high` in `rise`.

It adds the leak and the gain of the window, and the net partials, to the balance at R. -/
private def riseTop (t : PinTerms preset) (pulled fin : BeaconState preset fork) (i : ℕ) : ℕ :=
  actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
    t.depthFin * ((11 * t.gainRate i + 9) / 10 + 3 + t.leak i) +
      ((if electra : .pectra ≤ fork then
          dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) else 0) -
        (if electra : .pectra ≤ fork then
          dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1) else 0))

/-- The cap of a key as `rise` reads it: its own cap when its gain is low, else the largest.

It is `pinTerms`' `capFor`. -/
private def capForOf (t : PinTerms preset) (state : BeaconState preset fork) (i : ℕ) : ℕ :=
  if (decide (t.depthFin * ((11 * t.gainRate i + 9) / 10 + 3) <
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) &&
      decide (11 * t.depth * (t.gainRate i + 1) ≤ t.ebUp i)) = true then
    PinSplit2.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i
  else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- The cap that `rise` reads is at least the key's own cap. -/
private theorem capAt_le_capForOf (t : PinTerms preset) (state : BeaconState preset fork) (i : ℕ)
    (capMax : PinSplit2.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) :
    PinSplit2.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i ≤ capForOf t state i := by
  unfold capForOf
  split
  · exact Nat.le_refl _
  · exact capMax

/-- The rise of a key on its kept arm is the least of its cap, its rounded top and its headroom.

The rounded top adds the downward band to `riseTop`.

The headroom starts from the finalized balance.

The rise is that less the effective balance at R. -/
private theorem rise_kept (config : Config) (pulled anc fin : BeaconState preset fork) (i : ℕ)
    {H : ℕ} (hH : H = riseTop (pinTerms config pulled anc fin) pulled fin i)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    (pinTerms config pulled anc fin).rise i =
      min (capForOf (pinTerms config pulled anc fin) pulled i)
        (min (H + preset.downwardBand - (H + preset.downwardBand) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          (max (balanceAt fin i) (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))) -
        balanceAt pulled i := by
  have unfold : (pinTerms config pulled anc fin).rise i =
      if (pinTerms config pulled anc fin).keptArm i = true then
        min (capForOf (pinTerms config pulled anc fin) pulled i)
          (min (H + preset.downwardBand - (H + preset.downwardBand) %
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
            (max (balanceAt fin i) (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))) -
          balanceAt pulled i
      else capForOf (pinTerms config pulled anc fin) pulled i - balanceAt pulled i := by
    rw [hH]
    rfl
  rw [unfold]
  split
  · rfl
  · exact absurd kept ‹_›

/-- A key on its kept arm has an effective balance within its rise, the flows and their slack.

The key's effective balance stays at that of R or within the ceiling of its balance.

The ceiling is within `riseTop` and the flows, and the slack is paid when there are flows.

It starts from any state: `start` bounds the effective balance there. -/
private theorem rise_close (config : Config) (pulled anc fin : BeaconState preset fork) (i : ℕ)
    {H : ℕ} (hH : H = riseTop (pinTerms config pulled anc fin) pulled fin i)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm i = true)
    {eC Bc S U start capHigh : ℕ}
    (alignedC : eC % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startLe : start ≤ max (balanceAt fin i)
      ((H + S) - (H + S) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (stay : eC = balanceAt pulled i ∨ (eC ≤ Bc + preset.downwardBand ∧
      eC ≤ max start (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh)))
    (capped : eC ≤ capForOf (pinTerms config pulled anc fin) pulled i + S + U)
    (ceiling : Bc ≤ H + S)
    (slack : S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
      (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) :
    eC ≤ balanceAt pulled i + (pinTerms config pulled anc fin).rise i + S + U := by
  rw [rise_kept config pulled anc fin i hH kept]
  have arith := rise_arith (finEB := max (balanceAt fin i)
      (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (capFor := capForOf (pinTerms config pulled anc fin) pulled i) incPos
    stay (Nat.le_trans startLe (max_le_max (Nat.le_max_left _ _) (Nat.le_refl _))) alignedC
    capped ceiling slack
  rwa [max_assoc, max_self] at arith

/-- The bound `ebUp` on a key's effective balance is its largest balance or its rounded top.

The top adds the leak at the cap, the net partials and a band to the balance at R.

It reads the partials through `dueAmount`. -/
private theorem ebUp_eq (config : Config) (pulled anc fin : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i t : ℕ)
    (ht : t = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (pinTerms config pulled anc fin).leakAt
          (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i +
      (dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
        dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1)) +
      preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) :
    (pinTerms config pulled anc fin).ebUp i =
      max (max (balanceAt pulled i) (balanceAt fin i))
        (min (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i)
          (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  subst ht
  simp only [pinTerms, dueAmount, electra, ↓reduceDIte]
  rfl

/-- The aligned effective balances make the bound `ebUp` of a key a whole number of increments. -/
private theorem ebUp_aligned (h : Setting config checks g split fin pulled anc counted V) (i : ℕ) :
    (pinTerms config pulled anc fin).ebUp i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨t, ht⟩ : ∃ t, (pinTerms config pulled anc fin).ebUp i =
      max (max (balanceAt pulled i) (balanceAt fin i))
        (min (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i)
          (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, ebUp_eq config pulled anc fin electra i _ rfl⟩
  have a1 : balanceAt pulled i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    DirectSafety.Apriori.Internal.FloorTrace.effective_aligned
      (shared.append (fromFin.append toPulled)) h.genesis h.aligned i
  have a2 : balanceAt fin i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    DirectSafety.Apriori.Internal.FloorTrace.effective_aligned shared h.genesis h.aligned i
  have a3 : (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm
  have capAligned : PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    cases found : pulled.validators.data[i]? with
    | none => simp [PinSplit2.capAt, found]
    | some w =>
      exact capAt_aligned h.aligned (z := (⟨fork, pulled⟩ : ForkedBeaconState preset)) electra found
  have maxAligned : ∀ a b : ℕ, a % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      b % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      max a b % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := fun a b ha hb => by
    rcases max_choice a b with e | e <;> rw [e] <;> assumption
  have minAligned : ∀ a b : ℕ, a % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      b % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      min a b % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := fun a b ha hb => by
    rcases min_choice a b with e | e <;> rw [e] <;> assumption
  rw [ht]
  exact maxAligned _ _ (maxAligned _ _ a1 a2) (minAligned _ _ capAligned a3)

/-- A call's cutoff is within the withdrawal delay of the finalized state. -/
private theorem window_short (h : Setting config checks g split fin pulled anc counted V) :
    (getCurrentEpoch pulled).toNat + 1 <
      (getCurrentEpoch fin).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  have shallow := h.shallow
  omega

/-- The due amounts of a key are those of the entries that name it and are due, in two filters. -/
private theorem dueAmount_eq (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (v : ValidatorIndex) (cutoff : ℕ) :
    dueAmount state electra v.toNat cutoff =
      ((((state.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum := by
  unfold dueAmount
  simp only [List.filter_filter]
  congr 3
  funext entry
  simp [Bool.decide_and, UInt64.toNat_inj, Bool.and_comm]

/-- The leak of the pin does not fall as the effective balance rises. -/
private theorem leakAt_mono (config : Config) (pulled anc fin : BeaconState preset fork) {a b : ℕ}
    (i : ℕ) (le : a ≤ b) :
    (pinTerms config pulled anc fin).leakAt a i ≤ (pinTerms config pulled anc fin).leakAt b i := by
  unfold pinTerms
  dsimp only
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right le)))
    (Nat.div_le_div_right (Nat.mul_le_mul_right _ le))

/-- The leak of the pin at the finalized state's score, spelled out.

The score is the key's inactivity score at the finalized state, or zero before Altair. -/
private theorem leakAt_eq (config : Config) (pulled anc fin : BeaconState preset fork)
    (eb i : ℕ) :
    (pinTerms config pulled anc fin).leakAt eb i =
      2 * (eb / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config pulled anc fin).perIncrement) +
      eb * ((if altair : .altair ≤ fork then
          (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
        (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  unfold pinTerms
  rfl

/-- A key's inactivity score at the finalized state is at most the largest score there. -/
private theorem score_le_scoreMax (fin : BeaconState preset fork) (i : ℕ) :
    (if altair : .altair ≤ fork then
        (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) ≤
      (if altair : .altair ≤ fork then
        ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) := by
  split
  · rename_i altair
    cases found : (fin.inactivityScores altair).data[i]? with
    | none => simp
    | some x =>
      have mem : x.toNat ∈ (fin.inactivityScores altair).data.toList.map (·.toNat) :=
        List.mem_map_of_mem (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
      rw [List.foldl_max_eq_max (List.ne_nil_of_mem mem)]
      exact le_max_of_le_right (List.le_max_of_mem mem)
  · exact Nat.le_refl _

/-- Raising the balance by whole increments raises the leak by an amount in those increments.

The amount is the leak of the increments at the key's per-increment reward and the largest score.

It is rounded up once. -/
private theorem leakAt_add_le (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (i eb m : ℕ) :
    (pinTerms config pulled anc fin).leakAt (eb + preset.EFFECTIVE_BALANCE_INCREMENT.toNat * m) i ≤
      (pinTerms config pulled anc fin).leakAt eb i +
        2 * ((pinTerms config pulled anc fin).perIncrement * m) +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * m *
          ((pinTerms config pulled anc fin).scoreMaxFin +
            (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) + 1) := by
  have scoreMax : (pinTerms config pulled anc fin).scoreMaxFin = (if altair : .altair ≤ fork then
      ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) := by
    unfold pinTerms
    rfl
  rw [leakAt_eq, leakAt_eq, scoreMax]
  have score := score_le_scoreMax fin i
  generalize (if altair : .altair ≤ fork then
    (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) = S at score ⊢
  generalize (if altair : .altair ≤ fork then
    ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) = M at score ⊢
  generalize (pinTerms config pulled anc fin).perIncrement = P
  generalize (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat = B
  generalize config.INACTIVITY_SCORE_BIAS.toNat *
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat = Q
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat = inc at incPos ⊢
  have quotient : (eb + inc * m) / inc = eb / inc + m := by
    rw [Nat.add_mul_div_left _ _ incPos]
  have rounded : (eb + inc * m) * (S + B) / Q ≤ eb * (S + B) / Q + inc * m * (S + B) / Q + 1 := by
    rw [Nat.add_mul]
    exact Nat.add_div_le_div_add_div_add_one _ _ _
  have larger : inc * m * (S + B) / Q ≤ inc * m * (M + B) / Q :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right score _))
  have step : 2 * ((eb / inc + m) * P) = 2 * (eb / inc * P) + 2 * (P * m) := by ring
  rw [quotient, step]
  generalize eb / inc * P = x at *
  generalize (eb + inc * m) * (S + B) / Q = u at *
  generalize eb * (S + B) / Q = v at *
  generalize inc * m * (S + B) / Q = w at *
  generalize inc * m * (M + B) / Q = z at *
  omega

/-- The leak that a rise above `ebUp` by `a` increments of debits and `s` of a penalty induces.

The debits cost the leak of their increments at the key's reward, and the penalty one increment.

A debited key pays one more for the rounding, which the reward of an increment covers. -/
private theorem inducedR_le (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) (i a s : ℕ) (slack : s ≤ 1)
    (envelope : ∀ z ∈ tail.balancePath, effectiveAt z i ≤
      (pinTerms config pulled anc fin).ebUp i +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (a + s)) :
    inducedR (pinTerms config pulled anc fin) tail i ≤
      (pinTerms config pulled anc fin).depthFin *
          (3 * (pinTerms config pulled anc fin).perIncrement * a +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a *
              ((pinTerms config pulled anc fin).scoreMaxFin +
                (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
              (config.INACTIVITY_SCORE_BIAS.toNat *
                (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)) +
        s * slashLeak config fork (pinTerms config pulled anc fin) := by
  have fold : ∀ (l : List ℕ) (b c : ℕ), b ≤ c → (∀ x ∈ l, x ≤ c) → l.foldl max b ≤ c := by
    intro l
    induction l with
    | nil => exact fun _ _ le _ => le
    | cons x xs ih =>
      exact fun b c le all => ih _ c (max_le le (all x List.mem_cons_self))
        fun y m => all y (List.mem_cons_of_mem _ m)
  have mono := leakAt_mono config pulled anc fin i (fold _ 0 _ (Nat.zero_le _) fun v member => by
    obtain ⟨z, inPath, rfl⟩ := List.mem_map.mp member
    exact envelope z inPath)
  have first := leakAt_add_le config pulled anc fin incPos i
    ((pinTerms config pulled anc fin).ebUp i) a
  have second := leakAt_add_le config pulled anc fin incPos i
    ((pinTerms config pulled anc fin).ebUp i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a) s
  have rate : (pinTerms config pulled anc fin).perIncrement * a ≥ 1 ∨ a = 0 := by
    rcases Nat.eq_zero_or_pos a with zero | pos
    · exact .inr zero
    · exact .inl (Nat.mul_pos perPos pos)
  rw [Nat.mul_add, ← Nat.add_assoc] at mono
  unfold inducedR slashLeak
  rw [Nat.mul_left_comm s, ← Nat.mul_add]
  refine Nat.mul_le_mul_left _ ?_
  have three : 3 * (pinTerms config pulled anc fin).perIncrement * a =
      3 * ((pinTerms config pulled anc fin).perIncrement * a) := by ring
  have n1 := Nat.zero_le (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
  have n2 := Nat.zero_le (preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp slack with rfl | rfl <;>
    rcases rate with rate | rfl <;>
    simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
      Nat.zero_div] at mono first second three n1 ⊢ <;>
    omega

/-- A key's cap does not fall along a run. -/
private theorem cap_le_cap_of_run (caps : CapOrder preset) {z y : ForkedBeaconState preset}
    (post : Run config checks z y) (early : y.fork < .glamsterdam) (i : ℕ) :
    PinSplit2.capAt z i ≤ PinSplit2.capAt y i := by
  unfold PinSplit2.capAt
  cases found : z.state.validators.data[i]? with
  | none => simp
  | some w =>
    obtain ⟨w', found', mono⟩ := post.validatorCap_mono caps.activation caps.compounding early i
      w found
    simp only [found', Option.map_some, Option.getD_some]
    exact UInt64.le_iff_toNat_le.mp mono

/-- A key's effective balance at the end of a run from genesis is at most its cap there.

The cap is the one at that state. -/
private theorem effective_le_cap_at {g z : ForkedBeaconState preset}
    (shared : Run config checks g z)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : z.fork < .glamsterdam) (i : ℕ) : effectiveAt z i ≤ PinSplit2.capAt z i := by
  cases found : z.state.validators.data[i]? with
  | none => simp [effectiveAt, found]
  | some w =>
    have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared genesis caps
      early found
    simpa [PinSplit2.capAt, found] using capped

/-- On R's branch a key's effective balance is at most its cap at R. -/
private theorem effective_le_cap_pulled (h : Setting config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (toZ : Run config checks ⟨fork, fin⟩ ⟨fork, z⟩)
    (post : Run config checks ⟨fork, z⟩ ⟨fork, pulled⟩) (i : ℕ) :
    effectiveAt (⟨fork, z⟩ : ForkedBeaconState preset) i ≤
      PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := by
  obtain ⟨shared⟩ := h.toFin
  exact Nat.le_trans (effective_le_cap_at (shared.append toZ) h.genesis h.caps h.early i)
    (cap_le_cap_of_run h.caps post h.early i)

/-- A state of the balance path of a run between two states of one fork is a state of that fork.

It is the end of a run from the start and the start of a run to the end. -/
private theorem balancePath_state {a b : BeaconState preset fork}
    (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩) {z : ForkedBeaconState preset}
    (member : z ∈ r.balancePath) :
    ∃ zs : BeaconState preset fork, z = ⟨fork, zs⟩ ∧
      Nonempty (Run config checks ⟨fork, a⟩ ⟨fork, zs⟩) ∧
      Nonempty (Run config checks ⟨fork, zs⟩ ⟨fork, b⟩) := by
  obtain ⟨r1, r2, -⟩ := balancePath_endpoint r
    (Run.nil : Run config checks ⟨fork, b⟩ ⟨fork, b⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  exact ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩

/-- The cap of a key in the registry is the activation balance, or the largest balance.

Both are a whole number of increments, and the cap is too. -/
private theorem capAt_kind (h : Setting config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (i : ℕ) (within : i < z.validators.data.size) :
    (PinSplit2.capAt (⟨fork, z⟩ : ForkedBeaconState preset) i =
        preset.MIN_ACTIVATION_BALANCE.toNat ∨
      PinSplit2.capAt (⟨fork, z⟩ : ForkedBeaconState preset) i =
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) ∧
    preset.MIN_ACTIVATION_BALANCE.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨w, found⟩ : ∃ w, z.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem within⟩
  obtain ⟨aMin, aMax⟩ := cap_values_aligned h.aligned
  refine ⟨?_, aMin, aMax⟩
  rw [capAt_of_found (z := (⟨fork, z⟩ : ForkedBeaconState preset)) electra found]
  split
  · exact .inr rfl
  · exact .inl rfl

/-- The states of the parts of a run cut at a step are states of the run. -/
private theorem flip_path_mem {x m n y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) (post : Run config checks n y)
    {tail : Run config checks x y} (cut : (pre.snoc step).append post = tail) :
    (∀ z ∈ pre.balancePath, z ∈ tail.balancePath) ∧
      ∀ z ∈ post.balancePath, z ∈ tail.balancePath := by
  have path := Run.balancePath_append (pre.snoc step) post
  rw [cut] at path
  obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
  refine ⟨fun z member => by rw [path]; simp [Run.balancePath, member], fun z member => ?_⟩
  rw [headPost] at member
  rw [path]
  rcases List.mem_cons.mp member with rfl | inRest
  · simp [Run.balancePath, List.mem_of_mem_getLast? (Step.balancePath_ends step).2]
  · simp [headPost, inRest]

/-- A state of a run cut at a block step is a state of one of the parts. -/
private theorem flip_path_cover {x m n y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) (post : Run config checks n y)
    (notSlot : ∀ ok, step ≠ Step.slot ok) {tail : Run config checks x y}
    (cut : (pre.snoc step).append post = tail) :
    ∀ z ∈ tail.balancePath, z ∈ pre.balancePath ∨ z ∈ post.balancePath := by
  have path := Run.balancePath_append (pre.snoc step) post
  rw [cut] at path
  have block : step.balancePath = [m, n] := by
    cases step with
    | slot ok => exact absurd rfl (notSlot ok)
    | block => rfl
  obtain ⟨front, atLast⟩ := Run.balancePath_last pre
  obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
  intro z member
  rw [path] at member
  simp only [Run.balancePath, block, headPost, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.tail_cons] at member
  rcases member with (inPre | rfl | rfl) | inRest
  · exact .inl inPre
  · exact .inl (by rw [atLast]; simp)
  · exact .inr (by rw [headPost]; exact List.mem_cons_self)
  · exact .inr (by rw [headPost]; exact List.mem_cons_of_mem _ inRest)

/-- The effective balance of a key along a run is bounded by its capped balance.

The cap of the key may rise once, at a step that makes it compound.

The cap of a key in the registry is the activation balance, or the largest balance if it compounds.

The balance counts up to the cap at each state, so a ceiling on it holds before and after the rise.

A key whose cap does not rise is the constant-cap case.

Otherwise the run splits at the step that makes the key compound.

The part before it has the activation balance as its cap, and the part after it the largest balance.

The step leaves the epoch, so it keeps the effective balance. -/
private theorem effective_ceiling_flip (h : Setting config checks g split fin pulled anc counted V)
    {x y : BeaconState preset fork} (tail : Run config checks ⟨fork, x⟩ ⟨fork, y⟩)
    (invariant : Invariant x) (i : ℕ) (inside : i < x.validators.data.size)
    (ceil capHigh : ℕ)
    (capped : ∀ z ∈ tail.balancePath, effectiveAt z i ≤ PinSplit2.capAt z i)
    (capCeil : ∀ z ∈ tail.balancePath, PinSplit2.capAt z i ≤ capHigh)
    (balanceCeil : ∀ z ∈ tail.balancePath,
      min (actualBalanceAt z i) (PinSplit2.capAt z i) ≤ ceil) :
    effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i ≤
        max (effectiveAt (⟨fork, x⟩ : ForkedBeaconState preset) i)
          (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
      ((getCurrentEpoch y).toNat ≤ (getCurrentEpoch x).toNat →
        effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i =
          effectiveAt (⟨fork, x⟩ : ForkedBeaconState preset) i) ∧
      ((getCurrentEpoch x).toNat < (getCurrentEpoch y).toNat →
        effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i ≤ ceil + preset.downwardBand) ∧
      (getCurrentEpoch x).toNat ≤ (getCurrentEpoch y).toNat := by
  have capOrder := h.caps
  have minMax := UInt64.le_iff_toNat_le.mp capOrder.compounding
  obtain ⟨-, alignedMin, alignedMax⟩ := capAt_kind h i inside
  -- a run of constant cap `c0`, below `capHigh`, is the constant-cap case
  have seg : ∀ {a b : BeaconState preset fork}
      (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩) (c0 : ℕ),
      c0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → c0 ≤ capHigh →
      i < a.validators.data.size →
      effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i ≤ c0 →
      (∀ z ∈ r.balancePath, PinSplit2.capAt z i = c0) →
      (∀ z ∈ r.balancePath, min (actualBalanceAt z i) (PinSplit2.capAt z i) ≤ ceil) →
      effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤
          max (effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i)
            (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
        ((getCurrentEpoch b).toNat ≤ (getCurrentEpoch a).toNat →
          effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i =
            effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i) ∧
        ((getCurrentEpoch a).toNat < (getCurrentEpoch b).toNat →
          effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤ ceil + preset.downwardBand) ∧
        (getCurrentEpoch a).toNat ≤ (getCurrentEpoch b).toNat := by
    intro a b r c0 aligned le insideA start cap bal
    obtain ⟨p1, p2, p3, p4⟩ := PinSplit2.Run.effective_ceiling_of_balance_ceiling r h.early h.fulu
      i insideA ceil c0 aligned start
      (fun z member => by rw [← cap z member]; exact bal z member)
      (fun z member => (cap z member).le)
    exact ⟨le_trans p1 (max_le_max le_rfl (min_le_min le_rfl le)), p2, p3, p4⟩
  -- the cap of a key in the registry is one of two values
  have kind := fun (z : BeaconState preset fork) (within : i < z.validators.data.size) =>
    (capAt_kind h i within).1
  obtain ⟨rest, atHead⟩ := Run.balancePath_head tail
  have headMem : (⟨fork, x⟩ : ForkedBeaconState preset) ∈ tail.balancePath := by
    rw [atHead]
    exact List.mem_cons_self
  obtain ⟨last, atLast⟩ := Run.balancePath_last tail
  have lastMem : (⟨fork, y⟩ : ForkedBeaconState preset) ∈ tail.balancePath := by
    rw [atLast]
    simp
  -- a run that ends with the activation cap has the activation cap throughout
  have lowRun : ∀ {a b : BeaconState preset fork} (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩),
      i < a.validators.data.size →
      PinSplit2.capAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤
        preset.MIN_ACTIVATION_BALANCE.toNat →
      ∀ z ∈ r.balancePath,
        PinSplit2.capAt z i = preset.MIN_ACTIVATION_BALANCE.toNat :=
    fun r within atEnd z member => by
      obtain ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩ := balancePath_state r member
      have hi := cap_le_cap_of_run h.caps r2 h.early i
      rcases kind zs (Nat.lt_of_lt_of_le within (registryGrows_of_chainSteps r1.chainSteps)) with
        low | high
      · exact low
      · omega
  -- a run that starts above the activation cap has the largest cap throughout
  have highRun : ∀ {a b : BeaconState preset fork} (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩),
      i < a.validators.data.size →
      preset.MIN_ACTIVATION_BALANCE.toNat <
        PinSplit2.capAt (⟨fork, a⟩ : ForkedBeaconState preset) i →
      ∀ z ∈ r.balancePath,
        PinSplit2.capAt z i = preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
    fun r within atStart z member => by
      obtain ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩ := balancePath_state r member
      have lo := cap_le_cap_of_run h.caps r1 h.early i
      rcases kind zs (Nat.lt_of_lt_of_le within (registryGrows_of_chainSteps r1.chainSteps)) with
        low | high
      · omega
      · exact high
  by_cases compoundsEnd : preset.MIN_ACTIVATION_BALANCE.toNat <
      PinSplit2.capAt (⟨fork, y⟩ : ForkedBeaconState preset) i
  · by_cases compoundsStart : preset.MIN_ACTIVATION_BALANCE.toNat <
        PinSplit2.capAt (⟨fork, x⟩ : ForkedBeaconState preset) i
    · -- the cap is the largest balance along the whole run
      have all := highRun tail inside compoundsStart
      have atX := all _ headMem
      exact seg tail _ alignedMax (by have := capCeil _ headMem; omega) inside
        (by have := capped _ headMem; omega) all balanceCeil
    · -- the cap is the activation balance until the step that makes the key compound
      obtain ⟨m, n, pre, step, post, cut, flatM, largeN, -, sameEpoch⟩ :=
        Run.flip_split tail h.early h.fulu invariant i
          (by omega) compoundsEnd
      obtain ⟨mf, ms⟩ := m
      obtain ⟨nf, ns⟩ := n
      have sameM : fork = mf :=
        (fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
      have sameN : fork = nf := (fork_eq_of_run (pre.snoc step) post (Nat.le_refl _)).symm
      subst sameM sameN
      have insideM : i < ms.validators.data.size :=
        Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)
      have insideN : i < ns.validators.data.size :=
        Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps (pre.snoc step).chainSteps)
      obtain ⟨preMem, postMem⟩ := flip_path_mem pre step post cut
      obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
      have nMem := postMem (⟨fork, ns⟩ : ForkedBeaconState preset)
        (by rw [headPost]; exact List.mem_cons_self)
      have capsPre := lowRun pre inside flatM
      have capsPost := highRun post insideN largeN
      have atX := kind x inside
      have atY := kind y (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tail.chainSteps))
      have capX := capCeil _ headMem
      have capY := capCeil _ lastMem
      have effX := capped _ headMem
      have effN := capped _ nMem
      have capN := capsPost _ (by
        rw [headPost]
        exact List.mem_cons_self)
      have first := seg pre _ alignedMin (by omega) inside (by omega) capsPre
        (fun z member => balanceCeil z (preMem z member))
      have second := seg post _ alignedMax (by omega) insideN (by omega) capsPost
        (fun z member => balanceCeil z (postMem z member))
      have epochN : getCurrentEpoch ns = getCurrentEpoch ms :=
        UInt64.toNat_inj.mp (sameEpoch inside)
      have keep := step_same_epoch_effective step (Nat.lt_of_le_of_lt
        (fork_le_of_chainSteps post.chainSteps) h.early) epochN i insideM
      have epochs : (getCurrentEpoch ns).toNat = (getCurrentEpoch ms).toNat := sameEpoch inside
      obtain ⟨f1, f2, f3, f4⟩ := first
      obtain ⟨s1, s2, s3, s4⟩ := second
      refine ⟨by omega, fun back => ?_, fun before => ?_, by omega⟩
      · have e1 := f2 (by omega)
        have e2 := s2 (by omega)
        omega
      · by_cases later : (getCurrentEpoch ns).toNat < (getCurrentEpoch y).toNat
        · exact s3 later
        · have e1 := f3 (by omega)
          have e2 := s2 (by omega)
          omega
  · -- the cap is the activation balance along the whole run
    have all := lowRun tail inside (Nat.le_of_not_lt compoundsEnd)
    have atX := all _ headMem
    exact seg tail _ alignedMin (by have := capCeil _ headMem; omega) inside
      (by have := capped _ headMem; omega) all balanceCeil

/-- The cap along the balance path of a run is at most the cap at its end. -/
private theorem capCeil_path {c e : ForkedBeaconState preset} (tail : Run config checks c e)
    (caps : CapOrder preset) (early : e.fork < .glamsterdam) (back : e.fork ≤ c.fork) (i : ℕ) :
    ∀ z ∈ tail.balancePath, PinSplit2.capAt z i ≤ PinSplit2.capAt e i := by
  intro z member
  obtain ⟨-, r2, -⟩ := balancePath_endpoint tail (Run.nil : Run config checks e e) back member
  exact cap_le_cap_of_run caps r2 early i

/-- On C's branch a key keeps R's effective balance, or stays within the ceiling of its balance.

The runs of C and of R start at a state `c` of the shared segment, which holds the key.

The cap of the key may rise once on either run, and the balance counts up to its cap at each state.

The cap at C bounds the cap along C's run, and the cap at R bounds it along R's.

The effective balance of the key is at most its cap at each state of a run from the finalized state.

The effective balance at C is that at R if C is no later than `c`. -/
private theorem key_stay (h : Setting config checks g split fin pulled anc counted V)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (i : ℕ)
    (inside : i < c.validators.data.size) (Bc Bp : ℕ)
    (balanceC : ∀ z ∈ (fromC.append tailC).balancePath,
      min (actualBalanceAt z i) (PinSplit2.capAt z i) ≤ Bc)
    (balanceR : ∀ z ∈ (fromC.append tail).balancePath,
      min (actualBalanceAt z i) (PinSplit2.capAt z i) ≤ Bp) :
    effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i =
        effectiveAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i ∨
      (effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i ≤ Bc + preset.downwardBand ∧
        effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i ≤
          max (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i)
            (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
              (PinSplit2.capAt (⟨fork, counted⟩ : ForkedBeaconState preset) i))) := by
  obtain ⟨shared⟩ := h.toFin
  have invariant : Invariant c := Run.invariant h.genesis.invariant (shared.append toC)
  have later := UInt64.le_iff_toNat_le.mp h.later
  have capped : ∀ {y : BeaconState preset fork} (r : Run config checks ⟨fork, split⟩ ⟨fork, y⟩),
      ∀ z ∈ (fromC.append r).balancePath, effectiveAt z i ≤ PinSplit2.capAt z i :=
    fun r z member => by
      obtain ⟨zs, rfl, ⟨r1⟩, -⟩ := balancePath_state (fromC.append r) member
      exact effective_le_cap_at (shared.append (toC.append r1)) h.genesis h.caps h.early i
  obtain ⟨c1, c2, c3, -⟩ := effective_ceiling_flip h (fromC.append tailC) invariant i inside Bc
    (PinSplit2.capAt (⟨fork, counted⟩ : ForkedBeaconState preset) i) (capped tailC)
    (capCeil_path (fromC.append tailC) h.caps h.early (Nat.le_refl _) i) balanceC
  obtain ⟨-, r2, -, -⟩ := effective_ceiling_flip h (fromC.append tail) invariant i inside Bp
    (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) (capped tail)
    (capCeil_path (fromC.append tail) h.caps h.early (Nat.le_refl _) i) balanceR
  by_cases flat : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch c).toNat
  · exact .inl ((c2 flat).trans (r2 (by omega)).symm)
  · exact .inr ⟨c3 (by omega), c1⟩

open DirectSafety.Apriori.Internal in
/-- A key's balance on C's branch is at most R's balance, its debits, its credits and the gains.

The key is in the low regime, so its effective balance bound `ebUp` closes the ceiling.

The balance counts up to the key's cap at each state, which rises at most once along C's run.

The balance at the split is at most R's balance plus R's debits, by the floor premise.

The start of the ceiling is that bound, held to the cap at the split.

R's balance can exceed that cap, and the balance counts only up to it.

R's penalty and partial debits are at most the leak at the cap and the net partials.

The credits are `Cr`, which covers C's net credits `credits`, and the sync debits of R's.

`flipCover` makes `Cr` cover all of C's gross credits, when the cap rises on C's run.

Its gain is at most a tenth of the credits, sync debits, slack and base gain. -/
private theorem c_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {e : BeaconState preset fork}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, e⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch e).toNat ≤ highC + 1)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (v : ValidatorIndex) (inside : v.toNat < split.validators.data.size)
    {events eventsF eventsC : List (BalanceEvent preset)} (W : ℕ)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) (Cr : ℕ)
    (credits : netScan v.toNat highC tailC +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC tailC).1 ≤ Cr)
    (flipCover : PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat ∧ preset.MIN_ACTIVATION_BALANCE.toNat <
          PinSplit2.capAt (⟨fork, e⟩ : ForkedBeaconState preset) v.toNat →
      credC tailC highC v.toNat + whistC tailC highC v.toNat +
        (eventsC.map (syncCredit v.toNat)).sum ≤ Cr)
    (startEff : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum + W) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (floorR : min (actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
        (PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (syncDebit v.toNat)).sum + W)
    (debits : (events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1) -
          dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1)))
    (rateLow : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRate v.toNat + 1) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat) :
    ∃ gc, gc = min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (11 * ((Cr +
            (events.map (syncDebit v.toNat)).sum + (eventsF.map (syncDebit v.toNat)).sum) + W +
          min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).gainRate v.toNat +
          min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gc ≤ (Cr +
            (events.map (syncDebit v.toNat)).sum + (eventsF.map (syncDebit v.toNat)).sum) + W +
        min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).gainRate v.toNat +
        min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) ∧
      ∀ z ∈ tailC.balancePath, min (actualBalanceAt z v.toNat) (PinSplit2.capAt z v.toNat) ≤
        min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
          (events.map (syncDebit v.toNat)).sum + W)
          (PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) +
          Cr +
          (gc + (min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).gainRate v.toNat +
            min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat))) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  have top : min (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) +
        preset.downwardBand) ≤ (pinTerms config pulled anc fin).ebUp v.toNat := by
    have key : ∀ T : ℕ, T ≤ (T + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) -
        (T + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := fun T => by
      have := Nat.mod_lt (T + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) incPos
      omega
    rw [ebUp_eq config pulled anc fin electra v.toNat _ rfl]
    exact le_trans (min_le_min le_rfl (key _)) (le_max_right _ _)
  obtain ⟨i, hi⟩ : ∃ i, i = v.toNat := ⟨_, rfl⟩
  rw [← hi] at inside startEff floorR debits rateLow top credits flipCover ⊢
  obtain ⟨capI, hcap0⟩ : ∃ capI, capI =
      PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := ⟨_, rfl⟩
  rw [← hcap0] at debits top
  obtain ⟨pd, hpd⟩ : ∃ pd, pd = dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
      dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1) := ⟨_, rfl⟩
  rw [← hpd] at debits top
  obtain ⟨Dp, hDp⟩ : ∃ Dp, Dp =
      (events.map (penaltyDebit i)).sum + (events.map (floorPartialDebit v)).sum := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ Ds, Ds = (events.map (syncDebit i)).sum := ⟨_, rfl⟩
  obtain ⟨DsF, hDsF⟩ : ∃ DsF, DsF = (eventsF.map (syncDebit i)).sum := ⟨_, rfl⟩
  rw [← hDp] at floorR debits ⊢
  rw [← hDs] at floorR startEff ⊢
  rw [← hDsF] at startEff ⊢
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  obtain ⟨Df, hDf⟩ : ∃ Df, Df =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := ⟨_, rfl⟩
  rw [← hDf] at debits top
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth Df := ⟨_, rfl⟩
  rw [← hDf, ← hD]
  obtain ⟨e0, he0⟩ : ∃ e0, e0 = (pinTerms config pulled anc fin).ebUp i := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (pinTerms config pulled anc fin).gainRate i := ⟨_, rfl⟩
  rw [← he0] at top startEff rateLow
  rw [← hq] at rateLow ⊢
  have hq' : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
    rw [hq, he0, hP]
    rfl
  obtain ⟨C, hC⟩ : ∃ C, C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr + Ds + DsF + W + D * q + D) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, rfl⟩
  have startEff' : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤ e0 + C := by
    refine Nat.le_trans startEff (Nat.add_le_add_left ?_ _)
    rw [hC]
    refine Nat.mul_le_mul_left _ ?_
    have le := Nat.div_le_div_right (c := 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      (show 10 * (DsF + Ds + W) ≤ 11 * (Cr + Ds + DsF + W + D * q + D) by omega)
    rwa [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 10)] at le
  have alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [he0]
    exact ebUp_aligned h i
  obtain ⟨P', hP', rateAll⟩ := key_rate_pre h tailC near
  rw [hP'.trans hP.symm] at rateAll
  have hDle : D ≤ (pinTerms config pulled anc fin).depth := hD ▸ min_le_left _ _
  have epochs : (getCurrentEpoch e).toNat - (getCurrentEpoch split).toNat ≤ D := by
    rw [hD]
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have sizeC : i < e.validators.data.size :=
    Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tailC.chainSteps)
  have capSC := cap_le_cap_of_run h.caps tailC h.early i
  have capSP : PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤ capI :=
    hcap0 ▸ cap_le_cap_of_run h.caps toPulled h.early i
  have capCeil := capCeil_path tailC h.caps h.early (Nat.le_refl _) i
  have effS := effective_le_cap_at (shared.append fromFin) h.genesis h.caps h.early i
  have minMax := UInt64.le_iff_toNat_le.mp h.caps.compounding
  obtain ⟨kindS, aMin, aMax⟩ := capAt_kind h i inside
  obtain ⟨kindC, -, -⟩ := capAt_kind h i sizeC
  obtain ⟨wC, foundC⟩ : ∃ w, e.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem sizeC⟩
  have alignedC := capAt_aligned h.aligned (z := (⟨fork, e⟩ : ForkedBeaconState preset))
    electra foundC
  have startKey : 11 * D * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    rate_per_increment preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 D incPos (by decide) alignedE0
      (by
        rw [← hq']
        exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 hDle)) rateLow)
  by_cases flipped : PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤
      preset.MIN_ACTIVATION_BALANCE.toNat ∧ preset.MIN_ACTIVATION_BALANCE.toNat <
        PinSplit2.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i
  · -- the cap rises on C's branch, so the run splits at the step that makes the key compound
    have cover := flipCover flipped
    have invariantS := Run.invariant h.genesis.invariant (shared.append fromFin)
    obtain ⟨m, n, pre, step, post, cut, flatM, largeN, -, sameEpoch⟩ :=
      Run.flip_split tailC h.early h.fulu invariantS i flipped.1 flipped.2
    obtain ⟨mf, ms⟩ := m
    have sameM : fork = mf :=
      (fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
    subst sameM
    have insideM : i < ms.validators.data.size :=
      Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)
    obtain ⟨preMem, postMem⟩ := flip_path_mem pre step post cut
    have notSlot := step_flip_not_slot step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)) i insideM
      (Nat.not_lt.mpr flatM) largeN
    have junction := step_flip_min step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps))
      (Run.invariant invariantS pre) i (Nat.not_lt.mpr flatM) largeN
    have capMin : PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i =
        preset.MIN_ACTIVATION_BALANCE.toNat := by omega
    clear kindS kindC
    have capsPre : ∀ z ∈ pre.balancePath, PinSplit2.capAt z i ≤
        preset.MIN_ACTIVATION_BALANCE.toNat := fun z member => by
      obtain ⟨zs, rfl, -, ⟨r2⟩⟩ := balancePath_state pre member
      exact Nat.le_trans (cap_le_cap_of_run h.caps r2 h.early i) flatM
    have epochM : (getCurrentEpoch ms).toNat ≤ highC + 1 := by
      have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
        ((Run.nil.snoc step).append post).chainSteps)
      simp only at this
      omega
    have fc := flip_credits_le_sources (shared.append fromFin) h.genesis pre step post notSlot
      h.early electra i highC epochM (by rw [cut]; exact replayedC)
    rw [cut] at fc
    have minLe : preset.MIN_ACTIVATION_BALANCE.toNat ≤ capI := capMin ▸ capSP
    obtain ⟨gc, hform, hgc, bPre, bPost, -⟩ := c_ceiling_abstract_flip pre step post h.early
      h.fulu i inside highC P preset.MIN_ACTIVATION_BALANCE.toNat
      (PinSplit2.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i) aMin alignedC
      (by omega) (by omega) capsPre (fun z member => capCeil z (postMem z member))
      (fun z member => rateAll z (member.elim (preMem z) (postMem z))) endEpochC incPos D Cr
      (Cr + Ds + DsF) e0 C
      (min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
        preset.MIN_ACTIVATION_BALANCE.toNat) W
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq' alignedE0 hC epochs
      (le_min (by rw [← capMin]; exact floorR) (min_le_right _ _)) startEff' junction
      (step_same_epoch_effective step
        (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
        (UInt64.toNat_inj.mp (sameEpoch inside)) i insideM)
      (by omega) startKey (by omega)
    refine ⟨gc, hform, hgc, fun z member => ?_⟩
    rcases flip_path_cover pre step post notSlot cut z member with inPre | inPost
    · have := bPre z inPre
      have := capsPre z inPre
      rw [capMin]
      omega
    · have := bPost z inPost
      have := capCeil z member
      rw [capMin]
      omega
  · -- the cap of C's branch is the cap at the split throughout
    have same : PinSplit2.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i =
        PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i := by
      rcases kindS with s1 | s1 <;> rcases kindC with f | f <;> omega
    clear kindS kindC
    obtain ⟨gc, hform, hgc, bound, -⟩ := c_ceiling_abstract tailC h.early h.fulu i inside highC P
      (PinSplit2.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i) alignedC
      (by omega) capCeil rateAll endEpochC incPos D Cr (Cr + Ds + DsF) e0 C
      (min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
        (PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i)) W
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq' alignedE0 hC epochs
      (le_min (by rw [same]; exact floorR) (by rw [same]; exact min_le_right _ _)) startEff'
      credits startKey (by omega)
    refine ⟨gc, hform, hgc, fun z member => ?_⟩
    have := bound z member
    have := capCeil z member
    omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The debits of a key on R's branch that the pin charges at the top: its passes and its partials.

The passes cost at most the leak at `M` for each epoch from the finalized state's.

The bound `M` is at least the key's effective balance at each state of the run to R.

The partials paid are at most those queued at the finalized state less those still queued at R. -/
private theorem debits_le_top (h : Setting config checks g split fin pulled anc counted V)
    {s : BeaconState preset fork} (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, s⟩)
    (tail : Run config checks ⟨fork, s⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (inside : v.toNat < s.validators.data.size) (M : ℕ)
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, s⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), tail = pre.append post →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M) :
    (events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt M v.toNat +
        (dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1) -
          dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1)) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨shared⟩ := h.toFin
  have passes : (events.map (penaltyDebit v.toNat)).sum ≤
      ((getCurrentEpoch pulled).toNat - (getCurrentEpoch s).toNat) *
        (pinTerms config pulled anc fin).leakAt M v.toNat :=
    Run.passDebit_le tail h.early altair high endEpoch inside
    ((pinTerms config pulled anc fin).leakAt M v.toNat)
    (fun {z} pre post cut before totals => by
      obtain ⟨T, perIncrement, totalOk, perOk⟩ := totals
      obtain ⟨zf, zs⟩ := z
      have same : zf = fork := fork_eq_of_run pre post (Nat.le_refl _)
      subst same
      have startE : (getCurrentEpoch zs).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
        simp only at before
        omega
      obtain ⟨pq, pqOk⟩ :=
        quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
      exact (passRate_le_leakAt h (fromFin.append pre) startE totalOk pqOk v.toNat).trans
        (leakAt_mono config pulled anc fin v.toNat (below pre post cut)))
    replayed
  have epochs : (getCurrentEpoch pulled).toNat - (getCurrentEpoch s).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
    have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
    simp only at this
    omega
  have whole := Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed
  have net := Run.partialDebit_net (fromFin.append tail) electra h.early high
    ((getCurrentEpoch pulled).toNat + 1) (Nat.le_succ _) (window_short h) v whole
  simp only [List.map_append, List.sum_append] at net
  have part : (events.map (floorPartialDebit v)).sum +
      dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1) ≤
        dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) := by
    rw [dueAmount_eq, dueAmount_eq]
    omega
  have := Nat.mul_le_mul_right ((pinTerms config pulled anc fin).leakAt M v.toNat) epochs
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The balance of a key at a state of R's run from the finalized state has a ceiling.

The balance counts up to the key's cap at that state.

The ceiling is R's balance, the leak at `M` over the window and the net partials.

It adds the sync debits of the two runs and the slack `W`.

The floor of the state gives it, with the debits of the run after the state.

The bound `M` is at least the key's effective balance at each state of the run. -/
private theorem prefix_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (W M : ℕ)
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append post = fromFin.append tail →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M)
    {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) (cut : r1.append r2 = fromFin.append tail)
    (inside : v.toNat < zs.validators.data.size)
    (floorAt : ∀ {evs : List (BalanceEvent preset)}, r2.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinSplit2.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinSplit2.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).leakAt M v.toNat +
          (dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1) -
            dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1))) +
        ((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum + W) := by
  have whole := Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed
  obtain ⟨e1, ok1⟩ := r1.balanceEvents_ok h.early high
  obtain ⟨e2, ok2⟩ := r2.balanceEvents_ok h.early high
  have app := Apriori.Internal.balanceEvents_append r1 r2 high ok1 ok2
  rw [cut, whole] at app
  have eq : eventsF ++ events = e1 ++ e2 := Except.ok.inj app
  have floor := floorAt ok2
  have debit := debits_le_top h r1 r2 high endEpoch ok1 ok2 v inside M
    (fun pre post same => below (r1.append pre) post
      (by rw [← Run.append_assoc, ← same]; exact cut))
  have sums : (e2.map (syncDebit v.toNat)).sum ≤
      (eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum := by
    have := congrArg (fun L => (L.map (syncDebit v.toNat)).sum) eq
    simp only [List.map_append, List.sum_append] at this
    omega
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at each state of R's run from a state `c` is bounded.

The run from `c` is the rest of the run from the finalized state to the split, then the run to R.

The finalized state is `c` for a key of the finalized registry.

The effective balance of a key at `c` is within `ebUp`.

It is within `ebUp` and a few increments at each state after `c`.

The increments are the whole ones of its sync debits and its slashing slack.

The balance at each state of R's run from `c` is at least R's less R's debits.

The balance counts up to the cap of the key at that state, which rises at most once.

The passes and partials cost at most the leak at the cap and the net partials, by `debits_le_top`.

The sync debits and `W` are the rest, and `floorAt` supplies the floor from each state.

A ceiling on the balance along the run gives one on the effective balance.

The bound `ebUp` reads it at the top. -/
private theorem prefix_envelope (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : v.toNat < c.validators.data.size) (W : ℕ)
    (start : effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat)
    (floorAt : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append rest = fromC.append tail →
      ∀ {evs : List (BalanceEvent preset)}, rest.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinSplit2.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    ∀ z ∈ (fromC.append tail).balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum + W) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  obtain ⟨shared⟩ := h.toFin
  -- the top of `ebUp`, `A`, and the balance ceiling, `B`, which adds the sync debits and `W` to it
  obtain ⟨A, hA⟩ : ∃ A, A = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = A +
      ((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum + W) :=
    ⟨_, rfl⟩
  -- the balance ceiling at each state of that run
  have ceiling : ∀ {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), r1.append r2 = fromC.append tail →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinSplit2.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤ B := by
    intro zs r1 r2 cut
    have := prefix_ceiling h fromFin tail high endEpoch replayedF replayed v W
      (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (fun pre post _ => effective_le_cap_pulled h pre post v.toNat) (toC.append r1) r2
      (by rw [← Run.append_assoc, cut, Run.append_assoc, cutC])
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps r1.chainSteps))
      (fun {evs} ev => floorAt r1 r2 cut ev)
    omega
  intro z member
  obtain ⟨r1, r2, cutZ⟩ := balancePath_endpoint (fromC.append tail)
    (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  -- every state of the run to `zs` is the end of a run from `c` to R's
  have atPath : ∀ z' ∈ r1.balancePath, ∃ (zs' : BeaconState preset fork)
      (s1 : Run config checks ⟨fork, c⟩ ⟨fork, zs'⟩)
      (s2 : Run config checks ⟨fork, zs'⟩ ⟨fork, pulled⟩),
      z' = ⟨fork, zs'⟩ ∧ s1.append s2 = fromC.append tail := by
    intro z' member'
    obtain ⟨s1, s2, cutS⟩ := balancePath_endpoint r1 r2 (Nat.le_refl _) member'
    obtain ⟨zf', zs'⟩ := z'
    have same' : fork = zf' := (fork_eq_of_run s1 s2 (Nat.le_refl _)).symm
    subst same'
    exact ⟨zs', s1, s2, rfl, cutS.trans cutZ⟩
  have bound := effective_ceiling_flip h r1
    (Run.invariant h.genesis.invariant (shared.append toC)) v.toNat inside B
    (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, cut⟩ := atPath z' member'
      exact effective_le_cap_at (shared.append (toC.append s1)) h.genesis h.caps h.early
        v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, cut⟩ := atPath z' member'
      exact cap_le_cap_of_run h.caps s2 h.early v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, cut⟩ := atPath z' member'
      exact ceiling s1 s2 cut)
  obtain ⟨origin, -⟩ := bound
  -- the envelope `ebUp` and the rounding
  obtain ⟨t, ht⟩ :
      ∃ t, t = A + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 := ⟨_, rfl⟩
  have up := ebUp_eq config pulled anc fin electra v.toNat t (by omega)
  have floorRound := rounded_add_floor_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat A
    ((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum + W) incPos
  have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (show A + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 ≤ t by omega)
  have upper : min (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat := by
    rw [up]
    exact Nat.le_max_right _ _
  rw [← hB] at floorRound
  omega

/-- Rounding down after adding an amount adds at most the whole increments that cover it. -/
private theorem rounded_add_ceil_le (I x C : ℕ) (hI : 0 < I) :
    (x + C) - (x + C) % I ≤ (x - x % I) + I * ((C + I - 1) / I) := by
  have sum := Nat.div_add_mod (x + C) I
  have base := Nat.div_add_mod x I
  have step : (x + C) / I ≤ x / I + (C + I - 1) / I := by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < I ∧ x = I * q + r :=
      ⟨x / I, x % I, Nat.mod_lt _ hI, (Nat.div_add_mod x I).symm⟩
    have quotient : (I * q + r) / I = q := by
      rw [Nat.mul_add_div hI, Nat.div_eq_of_lt hr, Nat.add_zero]
    have shifted : (I * q + r + C) / I = q + (r + C) / I := by
      rw [show I * q + r + C = I * q + (r + C) by ring, Nat.mul_add_div hI]
    rw [shifted, quotient]
    exact Nat.add_le_add_left (Nat.div_le_div_right (by omega)) _
  have scaled := Nat.mul_le_mul_left I step
  rw [Nat.mul_add] at scaled
  omega

/-- A cap at a state of the Electra forks is at most the largest cap. -/
private theorem capAt_le_capMax {z : ForkedBeaconState preset} (caps : CapOrder preset)
    (electra : .pectra ≤ z.fork) (i : ℕ) :
    PinSplit2.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
  cases found : z.state.validators.data[i]? with
  | none => simp [PinSplit2.capAt, found]
  | some w =>
    have compounding := UInt64.le_iff_toNat_le.mp caps.compounding
    rw [capAt_of_found electra found]
    split <;> omega

/-- A key with an assigned exit epoch is inactive at every epoch from the exit on, along a run.

The run keeps an assigned exit epoch. -/
private theorem inactive_from_exit {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {i : ℕ} {v : Validator} (found : x.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) {e : Epoch} (reached : v.exitEpoch ≤ e) :
    isActiveAt y.state e i = false := by
  obtain ⟨later, foundLater, kept⟩ := tail.registryLifecycle.validators i v found
  have inactive : isActiveValidator later e = false := by
    unfold isActiveValidator
    simp
    exact fun _ => by rw [kept.exitEpoch assigned]; exact reached
  simp [isActiveAt, foundLater, inactive]

/-- A key that exited before the finalized epoch stays within its finalized balance and credits.

The key is idle from the finalized block on.

Its exit is kept, and the previous epoch of each later state is at or past it.

An idle key earns no epoch reward, so the credit ceiling of the run needs no rate.

The ceiling on the balance is the finalized balance and the credits of the run.

Rounding adds the whole increments that cover the credits. -/
private theorem exited_ceiling (h : Setting config checks g split fin pulled anc counted V)
    {a : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, a⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch a).toNat ≤ high + 1) (i : ℕ) {w : Validator}
    (found : fin.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat) (Cr : ℕ)
    (credits : netScan i high run +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high run).1 ≤ Cr) :
    effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i ≤
      max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        ((actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            ((Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  have incPos := h.bands.1
  have inside : i < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨shared⟩ := h.toFin
  have alignedMax := (cap_values_aligned h.aligned).2
  have startCap := PinSplit5.effectiveAt_le_capMax shared h.genesis h.caps h.early i
  have capCeil : ∀ z ∈ run.balancePath,
      PinSplit2.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := fun z member => by
    obtain ⟨r1, -, -⟩ := balancePath_endpoint run
      (Run.nil : Run config checks ⟨fork, a⟩ ⟨fork, a⟩) (Nat.le_refl _) member
    exact capAt_le_capMax h.caps (Nat.le_trans (Nat.le_trans (by decide) h.fulu)
      (fork_le_of_chainSteps r1.chainSteps)) i
  have notFar : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat far
    omega
  have idle : ∀ z ∈ run.balancePath,
      i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) := by
    intro z member active
    obtain ⟨r1, r2, -⟩ := balancePath_endpoint run
      (Run.nil : Run config checks ⟨fork, a⟩ ⟨fork, a⟩) (Nat.le_refl _) member
    obtain ⟨zf, zs⟩ := z
    have within := BeaconState.registryWithinLimit_of_lt
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early) zs
    have index : i.toUInt64.toNat = i := toNat_toUInt64_of_lt within
      (Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 r1.registryLifecycle.size_le)
    have previous := getPreviousEpoch_toNat zs
    have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r1.chainSteps)
    simp only at epochs
    have inactive := inactive_from_exit r1 found notFar (e := getPreviousEpoch zs)
      (UInt64.le_iff_toNat_le.mpr (by omega))
    obtain ⟨v, foundV, isActive⟩ := (mem_getActiveValidatorIndices within).mp active
    rw [index] at foundV
    have := isActiveAt_eq_true_iff.mpr ⟨v, foundV, isActive⟩
    rw [inactive] at this
    exact Bool.false_ne_true this
  obtain ⟨cb, hcb⟩ : ∃ cb, cb = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat + (netScan i high run +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high run).1) := ⟨_, rfl⟩
  have cbE : ∀ E, PinSplit2.creditBound run i high E 0
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat = cb := fun E => by
    rw [hcb]
    unfold PinSplit2.creditBound
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_div, Nat.add_zero]
    omega
  obtain ⟨E, hE⟩ : ∃ E, E = max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
      (min preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        (cb - cb % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := ⟨_, rfl⟩
  have ceiling := key_credit_ceiling run h.early h.fulu i inside high 0 E alignedMax startCap
    capCeil (fun z member => .inl (idle z member)) endEpoch
    (by rw [cbE]; exact le_of_eq hE.symm)
  rw [cbE] at ceiling
  have mono := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (show cb ≤ actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i + Cr by
      have := Nat.min_le_left (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      omega)
  have split := rounded_add_ceil_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i) Cr incPos
  exact Nat.le_trans ceiling (max_le_max (Nat.le_refl _)
    (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans mono split)))

/-- A step that charges a key has it in the registry at its start. -/
private theorem charge_inside {m n : ForkedBeaconState preset} (step : Step config checks m n)
    {v : ℕ} (charged : step.departureCharges.any (·.index == v) = true) :
    v < m.state.validators.data.size := by
  obtain ⟨c, member, same⟩ := List.any_eq_true.mp charged
  obtain ⟨⟨u, j⟩, found, picked⟩ := List.mem_filterMap.mp member
  have inside := (Array.getElem?_eq_some_iff.mp (by simpa only [List.mem_zipIdx_iff_getElem?,
    Array.getElem?_toList] using found : m.state.validators.data[j]? = some u)).1
  dsimp only at picked
  split at picked
  · cases picked
  · split at picked
    · cases Option.some.inj picked
      have : j = v := by simpa using same
      exact this ▸ inside
    · cases picked

/-- The epoch rewards of a key over a run are at most the rate for each epoch of the run.

The steps from the key's departure charge on count, and the key is in the registry from then.

So the bound is needed for a step only when the key is in the registry at its start. -/
private theorem riseScan_snd_le (v high R : ℕ) {x : ForkedBeaconState preset}
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (bound : ∀ {m n : ForkedBeaconState preset} (step : Step config checks m n),
      tail.Contains step → v < m.state.validators.data.size →
        PinSplit2.epochRewards v step ≤
          ((getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat) * R) :
    (riseScan (config := config) (checks := checks) v high tail).2 ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * R := by
  induction tail with
  | nil => simp [riseScan]
  | @snoc m n pre step ih =>
    have prior := ih fun inner member inside => bound inner (.earlier member step) inside
    have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have mn := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (Run.nil.snoc step : Run config checks m n).chainSteps)
    simp only [riseScan]
    split
    · rename_i cond
      have inside : v < m.state.validators.data.size := by
        rcases cond.1 with seen | charged
        · obtain ⟨c, member, same⟩ := (riseScan_fst v high pre).mp seen
          obtain ⟨w, found, -, -⟩ := pre.departure_charge_exit c member
          rw [same] at found
          exact (Array.getElem?_eq_some_iff.mp found).1
        · exact charge_inside step charged
      have one := bound step (.last pre step) inside
      have split : (getCurrentEpoch n.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
            ((getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat) := by omega
      rw [split, Nat.add_mul]
      omega
    · exact prior.trans (Nat.mul_le_mul_right _ (by omega))

/-- The rise of a charged key on C's branch is one band and the depth's gains at the largest rate.

The gains are the epoch rewards of the key after its exit starts, over the epochs of the run. -/
private theorem riseQ_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) (v : ℕ) :
    riseQ tailC highC v ≤ preset.upwardBand + (pinTerms config pulled anc fin).depth *
      (pinTerms config pulled anc fin).gainRateMax := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have near := h.near
  unfold riseQ
  split
  swap
  · exact Nat.zero_le _
  obtain ⟨P, -, gainLe, rateAll⟩ := pin_rate_exists h
  have scan := riseScan_snd_le (config := config) (checks := checks) v highC
    (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) tailC
    (fun {m n} step member inside => by
      obtain ⟨pre, post, _, mEarly, mEpoch⟩ := Run.contains_step_facts member h.early
      have above : fork ≤ m.fork := Nat.le_trans (by exact le_refl _)
        (fork_le_of_chainSteps pre.chainSteps)
      have below : m.fork ≤ fork := Nat.le_trans step.chainStep.fork_le
        (fork_le_of_chainSteps post.chainSteps)
      obtain ⟨mf, ms⟩ := m
      have same : mf = fork := Fork.ctorIdx_injective (Nat.le_antisymm below above)
      subst same
      have nEarly : n.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
      exact PinSplit2.epochRewards_le step altair nEarly v (Or.inl inside)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
        (.inr (PinSplit5.effectiveAt_le_capMax (shared.append (fromFin.append pre)) h.genesis
          h.caps mEarly v))
        (.inr (rateAll (fromFin.append pre) (by simp only at mEpoch ⊢; omega))))
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have epochs : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤
      (pinTerms config pulled anc fin).depth := by omega
  calc _ ≤ preset.upwardBand + (pinTerms config pulled anc fin).depth *
        (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) :=
        Nat.add_le_add_left (scan.trans (Nat.mul_le_mul_right _ epochs)) _
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ gainLe) _

/-- A low key is in the registry. -/
private theorem lowB_found (config : Config) (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ} (low : (pinTerms config state ancestor finalizedState).lowB i = true) :
    ∃ w, state.validators.data[i]? = some w := by
  refine validator_of_flag (f := fun v =>
    decide (ancestor.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat) &&
      decide (v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat)) (.inl ?_)
  exact (of_decide_eq_true low).1

/-- A key is low if it is activated and not withdrawable at R and its low bound is below the floor. -/
private theorem lowB_intro (config : Config) (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ}
    (first : ((state.validators.data[i]?).any fun v =>
      decide (ancestor.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat) &&
        decide (v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat)) = true)
    (low : (pinTerms config state ancestor finalizedState).lowEB i <
      (pinTerms config state ancestor finalizedState).newKeyFloor) :
    (pinTerms config state ancestor finalizedState).lowB i = true :=
  decide_eq_true ⟨first, low⟩

/-- A key of `K5` is unslashed in C's state. -/
private theorem K5_unslashed {v : ValidatorIndex} (member : v ∈ K5 counted V) :
    ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
  intro w found
  have inK5 := Finset.mem_filter.mp member
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inK5
  obtain ⟨⟨-, flag⟩, -, -⟩ := inK5
  simpa [slashedFlagAt, found] using flag

/-- A key whose exit starts on a run is activated at the start of the step that starts it.

The hypothesis `site` is the split of the run at the step that assigns the charged exit.

The activation comes from `ChainStep.exit_assigned_activated` at that step. -/
private theorem charge_activated {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (tail : Run config checks x y) (charge : DepartureCharge)
    (site : ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y, (pre.snoc step).append post = tail ∧
        ∃ v w, a.state.validators.data[charge.index]? = some v ∧
          b.state.validators.data[charge.index]? = some w ∧
          v.exitEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
          charge.amount = v.effectiveBalance.toNat ∧ charge.epoch = w.exitEpoch.toNat) :
    ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y, (pre.snoc step).append post = tail ∧
        ∃ v w, a.state.validators.data[charge.index]? = some v ∧
          b.state.validators.data[charge.index]? = some w ∧ v.exitEpoch = FAR_FUTURE_EPOCH ∧
          w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ v.activationEpoch ≤ getCurrentEpoch a.state ∧
          charge.amount = v.effectiveBalance.toNat ∧ charge.epoch = w.exitEpoch.toNat := by
  obtain ⟨a, b, pre, step, post, split, v, w, found, later, unset, set, amount, epoch⟩ := site
  exact ⟨a, b, pre, step, post, split, v, w, found, later, unset, set,
    step.chainStep.exit_assigned_activated
      (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps))
      found later unset set, amount, epoch⟩

/-- A key of `K5` that is activated at the finalized state is active and not withdrawable at R.

Its activation at R is that of C, which is at most the epoch before C's: an assigned activation
does not change.

It is not withdrawable by the finalized epoch at R, since then it would be exited on both branches.

This is the argument of `slashed_waits` for any key, with the exit and withdrawable epochs that
the split fixes. -/
private theorem activated_key_at_pulled (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (v : ValidatorIndex)
    (member : v ∈ K5 counted V) {w : Validator}
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (found : fin.validators.data[v.toNat]? = some w)
    (activated : w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ((pulled.validators.data[v.toNat]?).any fun u =>
      decide (anc.finalizedCheckpoint.epoch.toNat < u.withdrawableEpoch.toNat) &&
        decide (u.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat)) = true := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have near := h.near
  -- the key at the split, at R and at C, with the activation of the finalized state
  obtain ⟨x, foundSplit, lifeFin⟩ := fromFin.registryLifecycle.validators v.toNat w found
  obtain ⟨u, foundPulled, lifeSplit⟩ := toPulled.registryLifecycle.validators v.toNat x foundSplit
  have actSplit : x.activationEpoch = w.activationEpoch := lifeFin.activationEpoch activated
  have actPulled : u.activationEpoch = w.activationEpoch :=
    (lifeSplit.activationEpoch (actSplit ▸ activated)).trans actSplit
  obtain ⟨c, foundCounted, lifeAll⟩ :=
    (fromFin.append tailC).registryLifecycle.validators v.toNat w found
  have actCounted : c.activationEpoch = w.activationEpoch := lifeAll.activationEpoch activated
  -- the key is active in the epoch before C's, so its activation is at most R's epoch
  have inK5 := Finset.mem_filter.mp member
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inK5
  obtain ⟨⟨listed, -⟩, notActive, -⟩ := inK5
  have notCurrent : v ∉ getActiveValidatorIndices counted (getCurrentEpoch counted) := fun now =>
    notActive (by simpa [AC, activeVoters] using now)
  rcases listed with now | before
  · exact absurd now notCurrent
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  obtain ⟨c', foundC', activeBefore⟩ := (mem_getActiveValidatorIndices within).mp before
  have same : c' = c := Option.some.inj (foundC'.symm.trans foundCounted)
  subst same
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeBefore
  have low := UInt64.le_iff_toNat_le.mp activeBefore.1
  have previous := getPreviousEpoch_toNat counted
  have atPulled : u.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat := by
    rw [actPulled, ← actCounted]
    omega
  -- the key is not withdrawable by the finalized epoch at R, since it has a charge on C's run
  have settled : anc.finalizedCheckpoint.epoch.toNat < u.withdrawableEpoch.toNat := by
    by_contra not
    obtain ⟨d, member, index⟩ := charged
    exact no_charge_of_settled h tailC
      (Array.getElem?_eq_some_iff.mp foundSplit).1 foundPulled (by omega) d member index
  simp [foundPulled, settled, atPulled]

section LowBound

open DirectSafety.Apriori DirectSafety.Apriori.Internal

/-- The penalties of one key in one step fit a rate read at the start of the step. -/
private theorem step_passDebit_le {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (startEpoch : (getCurrentEpoch m.state).toNat ≤ high + 1) {v : ℕ}
    (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : (getCurrentEpoch m.state).toNat < (getCurrentEpoch n.state).toNat →
      (∃ total perIncrement, getTotalActiveBalance m.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) →
      passPenaltyRate config m v ≤ pen)
    {evs : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok evs) :
    (evs.map (penaltyDebit v)).sum ≤ pen := by
  have run : (Run.nil.snoc step : Run config checks m n).balanceEvents high = .ok evs := by
    simp [Run.balanceEvents, startEpoch, replayed, bind, Except.bind, pure, Except.pure]
  have bound := segment_passDebit_le_guarded (Run.nil.snoc step : Run config checks m n) early
    altair high endEpoch
    (fun {u w} step' member => by
      cases member with
      | last => rfl
      | earlier inner _ => cases inner)
    inside pen
    (fun {z} pre ok split before total => by
      injection split with middle _ _ _
      subst middle
      exact rate before total) run
  refine bound.trans ?_
  split <;> simp

/-- A rate that is linear in the effective balance bounds the two terms of a leak.

It bounds the leak of an aligned balance, and the leak of any balance an increment above, less one.
-/
private theorem leak_linear (inc pi score depth bias quotient : ℕ) (incPos : 0 < inc) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧
      (∀ eb : ℕ, inc ∣ eb →
        2 * (eb / inc * pi) + eb * (score + depth * bias) / (bias * quotient) ≤ ρn * eb / ρd) ∧
      ∀ x : ℕ, ρn * x ≤ ρd * (2 * ((x + inc) / inc * pi) +
        (x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by
  have under : ∀ x : ℕ, x ≤ inc * ((x + inc) / inc) := fun x => by
    rw [Nat.add_div_right _ incPos]
    exact (Nat.lt_mul_div_succ x incPos).le
  by_cases zero : bias * quotient = 0
  · refine ⟨2 * pi, inc, incPos, fun eb aligned => ?_, fun x => ?_⟩
    · obtain ⟨u, rfl⟩ := aligned
      simp only [zero, Nat.div_zero, Nat.add_zero]
      rw [Nat.mul_div_cancel_left _ incPos, show 2 * pi * (inc * u) = inc * (2 * pi * u) by ring,
        Nat.mul_div_cancel_left _ incPos]
      ring_nf
      exact le_refl _
    · simp only [zero, Nat.div_zero, Nat.add_zero]
      calc 2 * pi * x ≤ 2 * pi * (inc * ((x + inc) / inc)) := Nat.mul_le_mul_left _ (under x)
        _ = inc * (2 * ((x + inc) / inc * pi)) := by ring
        _ ≤ inc * (2 * ((x + inc) / inc * pi) + 1) := Nat.mul_le_mul_left _ (by omega)
  · have positive : 0 < bias * quotient := Nat.pos_of_ne_zero zero
    refine ⟨2 * pi * (bias * quotient) + (score + depth * bias) * inc, inc * (bias * quotient),
      Nat.mul_pos incPos positive, fun eb aligned => ?_, fun x => ?_⟩
    · obtain ⟨u, rfl⟩ := aligned
      have lhs : 2 * (inc * u / inc * pi) + inc * u * (score + depth * bias) / (bias * quotient) =
          2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
        rw [Nat.mul_div_cancel_left _ incPos]
        congr 2
        ring
      have rhs : (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) /
          (inc * (bias * quotient)) =
          2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
        rw [show (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) =
          inc * ((bias * quotient) * (2 * (u * pi)) + (score + depth * bias) * inc * u) by ring,
          Nat.mul_div_mul_left _ _ incPos, Nat.mul_add_div positive]
      rw [lhs, rhs]
    · have first := Nat.mul_le_mul_left (bias * quotient * (2 * pi)) (under x)
      have second : (score + depth * bias) * x ≤
          bias * quotient * ((x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by
        have := Nat.lt_mul_div_succ ((x + inc) * (score + depth * bias)) positive
        have mono : (score + depth * bias) * x ≤ (x + inc) * (score + depth * bias) :=
          calc (score + depth * bias) * x = x * (score + depth * bias) := Nat.mul_comm _ _
            _ ≤ (x + inc) * (score + depth * bias) :=
              Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        omega
      have third := Nat.mul_le_mul_left inc second
      calc (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * x
          = bias * quotient * (2 * pi) * x + inc * ((score + depth * bias) * x) := by ring
        _ ≤ bias * quotient * (2 * pi) * (inc * ((x + inc) / inc)) +
            inc * (bias * quotient *
              ((x + inc) * (score + depth * bias) / (bias * quotient) + 1)) :=
          Nat.add_le_add first third
        _ = inc * (bias * quotient) * (2 * ((x + inc) / inc * pi) +
            (x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by ring

/-- The pass premise of the potential floor, from a rate that is linear in aligned balances. -/
private theorem pass_of_leak (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (whole : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (i : ValidatorIndex) (initial : ∃ val, fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = whole → ∀ evs, step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨val, initial⟩ := initial
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  intro m n pre step post cut evs ok
  have above : fork ≤ m.fork :=
    Nat.le_trans (le_refl _) (fork_le_of_chainSteps pre.chainSteps)
  have below : m.fork ≤ fork :=
    Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)
  have startE : (getCurrentEpoch m.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
    simp only at this
    omega
  have endE : (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    simp only at this
    omega
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have mSize := registryGrows_of_chainSteps pre.chainSteps
  obtain ⟨mf, ms⟩ := m
  have same : mf = fork := Fork.ctorIdx_injective (Nat.le_antisymm below above)
  subst same
  have inside : i.toNat < ms.validators.data.size :=
    Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp initial).1 mSize
  refine step_passDebit_le step nEarly altair (getCurrentEpoch pulled).toNat endE startE inside
    (ρn * effectiveAt ⟨mf, ms⟩ i.toNat / ρd) (fun _ total => ?_) ok
  obtain ⟨T, perIncrement, totalOk, perOk⟩ := total
  obtain ⟨pq, pqOk⟩ :=
    quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
  have rate := passRate_le_leakAt h pre startE totalOk pqOk i.toNat
  exact rate.trans (leaky _ (Nat.dvd_of_mod_eq_zero
    (FloorTrace.effective_aligned (shared.append pre) h.genesis h.aligned i.toNat)))

/-- The floor of the potential, in naturals.

It is the closed form less the debits, the band and the carried shortfall. -/
private def potentialFloor (ρn ρd K X band slack cost : ℕ) : ℕ :=
  ((ρd - ρn * K) * (X + band) - ρn * slack) / ρd - (band + cost)

/-- The queued partials of the key at the finalized state that are due by the call's cutoff.

They are at most the key's `partialsDue`. -/
private theorem partials_le_due (electra : .pectra ≤ fork) (v : ValidatorIndex) :
    ((((fin.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
            (·.amount.toNat)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat := by
  rw [← dueAmount_eq fin electra v]
  refine le_trans ?_ (le_max_left (_ : ℕ) _)
  dsimp only
  simp only [dueAmount, electra, ↓reduceDIte]
  exact le_rfl

/-- The partials paid to a key over a run from the finalized state are at most those due.

The run ends by the call's cutoff, which is within the withdrawal delay of the finalized state. -/
private theorem run_partials_le_due (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (whole : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (v : ValidatorIndex)
    {events : List (BalanceEvent preset)}
    (replayed : whole.balanceEvents (getCurrentEpoch pulled).toNat = .ok events) :
    (events.map (floorPartialDebit v)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  exact (Run.partialDebit_le whole electra h.early (getCurrentEpoch pulled).toNat
    ((getCurrentEpoch pulled).toNat + 1) near (window_short h) v replayed).trans
    (partials_le_due electra v)

/-- The effective balance of a key at a state of the run from the finalized state, before its exit.

It is at least the least of its effective balance and cap at the finalized state.

It is also at least the floor of its potential, rounded down to an increment.

The floor loses the shortfall of the balance below the stored effective balance.

It also loses the debits, which are the sync debits of the run and the partials due. -/
private theorem exitQ_at (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    {sd : ForkedBeaconState preset} (pre : Run config checks ⟨fork, fin⟩ sd)
    (post : Run config checks sd ⟨fork, counted⟩)
    (cut : pre.append post = fromFin.append tailC)
    (v : ValidatorIndex) (member : v ∈ K5 counted V) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (far : ∀ w, sd.state.validators.data[v.toNat]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) -
            potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt sd v.toNat := by
  have cleanC := K5_unslashed member
  have nearC := h.near
  obtain ⟨sf, se⟩ := sd
  have above : fork ≤ sf := Nat.le_trans (le_refl _) (fork_le_of_chainSteps pre.chainSteps)
  have below : sf ≤ fork := Nat.le_trans (le_refl _) (fork_le_of_chainSteps post.chainSteps)
  have same : fork = sf := (Fork.ctorIdx_injective (Nat.le_antisymm below above)).symm
  subst same
  have toCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  simp only at toCounted
  have near : (getCurrentEpoch se).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix pre post
    (getCurrentEpoch pulled).toNat events (by rw [cut]; exact replayed)
  have clean : ∀ w, se.validators.data[v.toNat]? = some w → w.slashed = false :=
    fun w found => unslashed_of_run post found cleanC
  have retained : ∀ {m n : ForkedBeaconState preset} (b : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (a : Run config checks n ⟨fork, se⟩),
      (b.snoc step).append a = pre → ∀ w, n.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat := by
    intro m n b step a cut' w found
    obtain ⟨last, located, kept⟩ := a.registryLifecycle.validators v.toNat w found
    by_cases e : w.exitEpoch = FAR_FUTURE_EPOCH
    · rw [e]
      exact .inl (getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled)
    · exact absurd ((kept.exitEpoch e).symm.trans (far last located)) e
  have syncLe : (before.map (syncDebit v.toNat)).sum ≤ (events.map (syncDebit v.toNat)).sum :=
    (isPrefix.sublist.map (syncDebit v.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
  have partialLe : (before.map (floorPartialDebit v)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat :=
    run_partials_le_due h pre near v beforeOk
  have final := cfloor_endpoint h se pre near beforeOk v val initial clean retained
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) ρn ρd
    (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
      (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat)
      preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      ((before.map (syncDebit v.toNat)).sum + (before.map (floorPartialDebit v)).sum))
    (by omega)
    (pass_of_leak h pre near v ⟨val, initial⟩ ρn ρd leaky)
    (fun a D k hk hD closed => by
      have mono : ρd - ρn * ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat) ≤
          ρd - ρn * k :=
        Nat.sub_le_sub_left (Nat.mul_le_mul_left _ (hk.trans (Nat.sub_le_sub_right toCounted _))) _
      have step2 := (Nat.mul_le_mul_right _ mono).trans closed
      have step3 := Nat.div_le_of_le_mul (Nat.sub_le_of_le_add step2)
      unfold potentialFloor
      omega)
    pre Run.nil rfl
  refine le_trans (min_le_min le_rfl (min_le_min le_rfl (rounded_mono _ ?_))) final
  unfold potentialFloor
  omega

/-- The charge of a key on C's run is its effective balance at a state where its exit is unset.

The state is the stop of the charge.

The runs to it and from it make C's run from the finalized block. -/
private theorem exit_stop (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (v : ℕ)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v →
      c.epoch ≤ (getCurrentEpoch counted).toNat) :
    ∃ (sd : ForkedBeaconState preset) (pre : Run config checks ⟨fork, fin⟩ sd)
        (post : Run config checks sd ⟨fork, counted⟩),
      pre.append post = fromFin.append tailC ∧
      (∀ w, sd.state.validators.data[v]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH) ∧
      exitQ tailC v = effectiveAt sd v := by
  classical
  obtain ⟨c0, member0, index0, -, amount0⟩ : ∃ c ∈ tailC.departureCharges,
      c.index = v ∧ c.epoch ≤ (getCurrentEpoch counted).toNat ∧ exitQ tailC v = c.amount := by
    obtain ⟨c, mem, idx⟩ := charged
    rcases exitQ_cases tailC v with ⟨none, -⟩ | found
    · exact absurd (epochLe c mem idx) (none c mem idx)
    · exact found
  obtain ⟨stop, chosen⟩ := stop_of_charge fromFin tailC member0 index0
  have selected := stop.selected
  rw [chosen] at selected
  obtain ⟨-, -, amount, next, assignedStep, rest, split', charged', vv, w, atStop, atNext,
    unset, assigned, epoch⟩ := selected
  refine ⟨stop.state, stop.pre, stop.post, stop.split, fun w' found => ?_, by rw [amount0, amount]⟩
  have same := Option.some.inj (found.symm.trans atStop)
  subst same
  exact unset

/-- The key's effective balance at its exit call, from the potential floor of the run to the call.

The key is in `K5`, activated at the finalized state, and charged on the run from the split. -/
private theorem exitQ_potential (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (member : v ∈ K5 counted V) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) -
            potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      exitQ tailC v.toNat := by
  obtain ⟨sd, pre, post, cut, far, amount⟩ := exit_stop fromFin tailC v.toNat charged
    (charge_epoch_le_of_K5 h.early tailC member)
  rw [amount]
  exact exitQ_at h fromFin tailC replayed pre post cut v member val initial far ρn ρd leaky

/-- The leak of an aligned effective balance is at most a rate times it.

The rate times any balance is at most the leak an increment above, plus one. -/
private theorem leak_rate (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (v : ℕ) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧
      (∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
        (pinTerms config pulled anc fin).leakAt eb v ≤ ρn * eb / ρd) ∧
      ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
        (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v + 1) := by
  obtain ⟨ρn, ρd, positive, bound, above⟩ := leak_linear preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat
    (if altair : .altair ≤ fork then
      (((fin.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    config.INACTIVITY_SCORE_BIAS.toNat
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat incPos
  exact ⟨ρn, ρd, positive, fun eb aligned => bound eb aligned, fun x => above x⟩

/-- The rate times the epochs and the base is at most the leak for each epoch, plus one.

The leak is read an increment above the base. -/
private theorem rate_cost (ρn ρd K L Y : ℕ) (first : ρn * Y ≤ ρd * (L + 1)) :
    ρn * K * Y ≤ ρd * (K * (L + 1)) :=
  calc ρn * K * Y = K * (ρn * Y) := by ring
    _ ≤ K * (ρd * (L + 1)) := Nat.mul_le_mul_left _ first
    _ = ρd * (K * (L + 1)) := by ring

/-- The leak at a base, for each epoch of the depth, covers the base's share of the closed form.

The rate bounds the base by the leak an increment above it, plus one.

The closed form takes the rate for each epoch from the base, and its rest is the base's share. -/
private theorem rate_step (ρn ρd K L Y : ℕ) (first : ρn * Y ≤ ρd * (L + 1)) :
    ρd * Y ≤ (ρd - ρn * K) * Y + ρd * (K * (L + 1)) := by
  have rate := rate_cost ρn ρd K L Y first
  have cover : ρd ≤ (ρd - ρn * K) + ρn * K := by omega
  calc ρd * Y ≤ ((ρd - ρn * K) + ρn * K) * Y := Nat.mul_le_mul_right _ cover
    _ = (ρd - ρn * K) * Y + ρn * K * Y := by ring
    _ ≤ (ρd - ρn * K) * Y + ρd * (K * (L + 1)) := Nat.add_le_add_left rate _

/-- The arithmetic of the low bound of an existing key.

The potential floor, rounded down to an increment, is at least the bound less the sync debits.

`L1` and `L2` are the leaks an increment above the base and above the shortfall.

The rate bounds the base and the shortfall by them, plus one each.

`R` is the bound before its drop, and it is at most the base less the partials due. -/
private theorem low_arith (inc band ρn ρd K depth X s R pd sync L1 L2 E0 cap : ℕ)
    (positive : 0 < ρd) (incPos : 0 < inc)
    (first : ρn * X ≤ ρd * (L1 + 1)) (second : ρn * s ≤ ρd * (L2 + 1)) (epochs : K ≤ depth)
    (baseLe : R ≤ X - pd) (effLe : R ≤ E0) (capLe : E0 ≤ cap) :
    R - ((L2 + 1) + depth * (L1 + 1) + band + inc) ≤
      min E0 (min cap
        (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) -
          (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd))) % inc)) + sync := by
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ epochs
  suffices rounded : R - ((L2 + 1) + depth * (L1 + 1) + band + inc) ≤
      (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) -
        (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd))) % inc) + sync by
    omega
  generalize hF : ((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) = F
  have modLt := Nat.mod_lt F incPos
  have modLe := Nat.mod_le F inc
  by_cases big : ρd ≤ ρn * K
  · -- the closed form is vacuous, and the leak already covers the base
    have zero : ρd - ρn * K = 0 := Nat.sub_eq_zero_of_le big
    rw [zero, Nat.zero_mul, Nat.zero_sub, Nat.zero_div, Nat.zero_sub] at hF
    have step := rate_step ρn ρd K L1 X first
    rw [zero, Nat.zero_mul, Nat.zero_add] at step
    have base := Nat.le_of_mul_le_mul_left step positive
    omega
  · have step := rate_step ρn ρd K L1 X first
    have mono : (ρd - ρn * K) * X ≤ (ρd - ρn * K) * (X + band) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have bound := Nat.lt_mul_div_succ
      ((ρd - ρn * K) * (X + band) - ρn * s) positive
    have total : ρd * (X + band) ≤ ((ρd - ρn * K) * (X + band) - ρn * s) + ρn * s +
        ρd * (K * (L1 + 1)) + ρd * band := by
      have split : ρd * (X + band) = ρd * X + ρd * band := by ring
      omega
    have lt : ρd * (X + band) < ρd * (((ρd - ρn * K) * (X + band) - ρn * s) / ρd + 1 +
        (L2 + 1) + K * (L1 + 1) + band) := by
      calc ρd * (X + band) ≤ _ := total
        _ < ρd * (((ρd - ρn * K) * (X + band) - ρn * s) / ρd + 1) + ρd * (L2 + 1) +
              ρd * (K * (L1 + 1)) + ρd * band := by omega
        _ = _ := by ring
    have cancel := Nat.lt_of_mul_lt_mul_left lt
    generalize ((ρd - ρn * K) * (X + band) - ρn * s) / ρd = W at cancel hF
    omega

/-- The low bound of an existing key, against the rev 2.5.4 form of `lowEB` and `drop`.

The key is in `K5`, activated at the finalized state, and charged on the run from the split.

The bound is its effective balance at the call, less its sync debits.

The form of `drop` carries the shortfall of the balance below the stored effective balance once.

It carries the leak at the base for each epoch of the depth. -/
private theorem existing_low_explicit
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (member : v ∈ K5 counted V) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    min (min (min (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
          (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) -
        (pinTerms config pulled anc fin).partialsDue v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat -
      (((pinTerms config pulled anc fin).leakAt
          (balanceAt fin v.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              (withdrawalMaxEffectiveBalance preset fork val).toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      exitQ tailC v.toNat + (events.map (syncDebit v.toNat)).sum := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin h.bands.1 v.toNat
  have potential := exitQ_potential h fromFin tailC replayed v member val initial charged ρn ρd
    leaky
  have finEB : balanceAt fin v.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat := rfl
  have capped : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared h.genesis h.caps h.early
      initial
  have toCounted := UInt64.le_iff_toNat_le.mp h.later
  have nearC := h.near
  have arith := low_arith preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand ρn ρd
    ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
    (min (min (min (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
          (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) -
        (pinTerms config pulled anc fin).partialsDue v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat)
    ((pinTerms config pulled anc fin).partialsDue v.toNat) (events.map (syncDebit v.toNat)).sum
    ((pinTerms config pulled anc fin).leakAt
      (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat)
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
    (withdrawalMaxEffectiveBalance preset fork val).toNat positive h.bands.1 (above _) (above _)
    (by omega) (by omega) (by omega) capped
  simp only [potentialFloor] at potential
  exact le_trans arith (Nat.add_le_add_right potential _)

/-- The arithmetic of the margin of the floor of a key on C's run.

The closed form of the potential floor, less the sync debits, is at least the base less the fall.

The fall holds the leak at the base and the band for each epoch of the depth, and the carry.

`L1` and `L2` are the leaks an increment above the base with the band and above the shortfall.

The rate bounds the base with the band and the shortfall by them, plus one each. -/
private theorem margin_arith (ρn ρd K depth B band s L1 L2 pd sync D a X : ℕ)
    (positive : 0 < ρd) (first : ρn * (B + band) ≤ ρd * (L1 + 1))
    (second : ρn * s ≤ ρd * (L2 + 1)) (epochs : K ≤ depth)
    (fall : (L2 + 1) + depth * (L1 + 1) + pd ≤ X) (debit : D ≤ sync + pd)
    (closed : (ρd - ρn * K) * (B + band) ≤ ρd * (a + D + band) + ρn * s) :
    B - X - sync ≤ a := by
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ epochs
  have step := rate_step ρn ρd K L1 (B + band) first
  have spread : ρd * (a + D + band + (L2 + 1) + K * (L1 + 1)) =
      ρd * (a + D + band) + ρd * (L2 + 1) + ρd * (K * (L1 + 1)) := by ring
  have total : ρd * (B + band) ≤ ρd * (a + D + band + (L2 + 1) + K * (L1 + 1)) := by omega
  have cancel := Nat.le_of_mul_le_mul_left total positive
  omega

/-- The arithmetic of the stay of the effective balance of a key on C's run.

The key has no sync debits, and the test of its floor holds.

An effective balance above the finalized one is at least an increment above it.

A segment of the run from a state with that effective balance ends at a balance of at least M.

Here `M` is the finalized effective balance.

The segment loses the rate of the leak for each epoch and the partials due.

The rate bounds the base with the band by the leak, and the test bounds the fall by the band.

A quarter of an increment bounds the band, as the preset requires. -/
private theorem stay_arith (ρn ρd K k depth inc band B M Bw X pd D bal L1 L2 : ℕ)
    (positive : 0 < ρd) (incPos : 0 < inc) (quarter : 4 * band ≤ inc) (big : inc ≤ M)
    (testB : M ≤ B + band) (fallX : X ≤ band) (first : ρn * (B + band) ≤ ρd * (L1 + 1))
    (fall : (L2 + 1) + depth * (L1 + 1) + pd ≤ X) (epochs : k ≤ K) (depthK : K ≤ depth)
    (start : M + inc ≤ Bw) (debit : D ≤ pd)
    (closed : (ρd - ρn * k) * (Bw + band) ≤ ρd * (bal + D + band)) : M ≤ bal := by
  have cost := rate_cost ρn ρd K L1 (B + band) first
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ depthK
  have rate : ρn * K * (B + band) + ρd * pd ≤ ρd * X := by
    have fits : ρd * (K * (L1 + 1) + pd) ≤ ρd * X := Nat.mul_le_mul_left ρd (by omega)
    rw [Nat.mul_add] at fits
    omega
  have yPos : 0 < B + band := by omega
  have bound : ρn * K * (B + band) ≤ ρd * (B + band) :=
    calc ρn * K * (B + band) ≤ ρd * X := by omega
      _ ≤ ρd * band := Nat.mul_le_mul_left _ fallX
      _ ≤ ρd * (B + band) := Nat.mul_le_mul_left _ (by omega)
  have under : ρn * K ≤ ρd := Nat.le_of_mul_le_mul_right bound yPos
  have fewer : ρn * k ≤ ρd := Nat.le_trans (Nat.mul_le_mul_left ρn epochs) under
  have mono : (ρd - ρn * k) * (M + inc + band) ≤ (ρd - ρn * k) * (Bw + band) :=
    Nat.mul_le_mul_left _ (by omega)
  have split : ρd * (M + inc + band) =
      (ρd - ρn * k) * (M + inc + band) + ρn * k * (M + inc + band) :=
    calc ρd * (M + inc + band) = ((ρd - ρn * k) + ρn * k) * (M + inc + band) := by
          rw [Nat.sub_add_cancel fewer]
      _ = _ := by ring
  have loss : ρn * k * (M + inc + band) ≤ 3 * (ρn * K * (B + band)) :=
    calc ρn * k * (M + inc + band) ≤ ρn * K * (M + inc + band) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ρn epochs)
      _ ≤ ρn * K * (3 * (B + band)) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (ρn * K * (B + band)) := by ring
  have left : ρd * (M + inc + band + 3 * pd) = ρd * (M + inc + band) + 3 * (ρd * pd) := by ring
  have right : ρd * (bal + D + band + 3 * X) = ρd * (bal + D + band) + 3 * (ρd * X) := by ring
  have total : ρd * (M + inc + band + 3 * pd) ≤ ρd * (bal + D + band + 3 * X) := by omega
  have cancel := Nat.le_of_mul_le_mul_left total positive
  omega

/-- The margin of the floor of a key on C's run, from a rate of its leak.

The rate is `leak_rate`'s for the key.

The balance of the key from the finalized block is above the closed form of the potential floor.

The closed form reads the rate that `leak_rate` gives and the shortfall of the balance.

It also reads the debits of the run, which are its sync debits and its partials.

The partials are at most those due.

`low` is the base less `X`.

`X` is at least the fall.

The fall is the carry, the leak for each epoch of the depth, and the partials due.

The leak is read at the base with the band. -/
private theorem floorC_margin (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ) (positive : 0 < ρd)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X) :
    ∃ slack : ℕ,
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          (preset.downwardBand + slack) ∧
      (∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
        (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
        (before.snoc step).append after = fromFin.append tailC → ∀ evs,
        step.balanceEvents = .ok evs →
        (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd) ∧
      ∀ a D k : ℕ, k ≤ (getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat →
        D ≤ (events.map (syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
        (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
            (withdrawalMaxEffectiveBalance preset fork val).toNat +
          preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
        low - (events.map (syncDebit i.toNat)).sum ≤ a := by
  have nearC := h.near
  have partialLe := run_partials_le_due h (fromFin.append tailC) nearC i replayed
  refine ⟨effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
    actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat, by omega,
    pass_of_leak h (fromFin.append tailC) nearC i ⟨val, initial⟩ ρn ρd leaky,
    fun a D k hk hD closed => ?_⟩
  rw [← hbase0] at closed
  have bound := margin_arith ρn ρd k
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) base0
    preset.downwardBand
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).partialsDue i.toNat)
    (events.map (syncDebit i.toNat)).sum D a X
    positive (above _) (above _) (by omega) fall (by omega) closed
  omega

/-- Two different whole numbers of increments differ by at least an increment. -/
private theorem aligned_gap {E M inc : ℕ} (e : E % inc = 0) (m : M % inc = 0) (lt : M < E) :
    M + inc ≤ E := by
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero e
  obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero m
  have next : b < a := Nat.lt_of_mul_lt_mul_left lt
  calc inc * b + inc = inc * (b + 1) := by ring
    _ ≤ inc * a := Nat.mul_le_mul_left _ next

/-- The effective balance of a key on C's run stays at its finalized value when the test holds.

The key has no sync debits on the run, and the test of its floor holds.

The proof runs conjunct (2) of the floor pair.

A downward update fires only at a step whose balance after it is at least the finalized balance.

Such an update is from an effective balance above the finalized one, set at an update `w`.

The potential floor of the run from `w` then keeps the balance, by `stay_arith`. -/
private theorem floorC_stay (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, counted.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (quarter : 4 * preset.downwardBand ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (ρn ρd : ℕ) (positive : 0 < ρd)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low finEB : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (hfin : finEB = effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X)
    (sync : (events.map (syncDebit i.toNat)).sum = 0)
    (test : max finEB base0 ≤ low + preset.downwardBand)
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC) :
    finEB ≤ effectiveAt z i.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  have incPos := h.bands.1
  have alignedFin := FloorTrace.effective_aligned toFin h.genesis h.aligned i.toNat
  have aligned : finEB % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [hfin]
    exact alignedFin
  by_cases small : finEB < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  · have zero : finEB = 0 := by rw [← Nat.mod_eq_of_lt small]; exact aligned
    omega
  have big : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ finEB := Nat.le_of_not_lt small
  have fallX : X ≤ preset.downwardBand := by omega
  have testB : finEB ≤ base0 + preset.downwardBand := by omega
  have first := above (base0 + preset.downwardBand)
  have partialLe := run_partials_le_due h (fromFin.append tailC) h.near i replayed
  obtain ⟨slack, start, pass, arith⟩ := floorC_margin h fromFin tailC replayed i val initial ρn ρd
    positive leaky above base0 X low hbase0 hlow fall
  have floorAt : ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, counted⟩), r1.append r2 = fromFin.append tailC →
      low - (events.map (syncDebit i.toNat)).sum ≤ actualBalanceAt p i.toNat :=
    fun r1 r2 whole => cfloor_balance h counted (fromFin.append tailC) h.near replayed i val
      initial clean retained slack ρn ρd (low - (events.map (syncDebit i.toNat)).sum) start pass
      arith r1 r2 whole
  have forkEnd : ∀ {p : ForkedBeaconState preset} (r2 : Run config checks p ⟨fork, counted⟩),
      p.fork < .glamsterdam := fun r2 =>
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  have inside : i.toNat < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp initial).1
  have cappedFin : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax toFin h.genesis h.caps h.early
      initial
  rw [hfin]
  refine (PinSplit2.Run.effective_floor_pair rp (forkEnd rest) h.fulu i.toNat inside 0 0 0 0 0
    0).2.1 alignedFin ?_ ?_
  · intro m n before step after cut' below
    obtain ⟨mF, mS⟩ := m
    obtain ⟨nF, nS⟩ := n
    have afterRest := Nat.le_trans (fork_le_of_chainSteps after.chainSteps)
      (fork_le_of_chainSteps rest.chainSteps)
    have nSame : nF = fork := Fork.ctorIdx_injective (Nat.le_antisymm afterRest
      (Nat.le_trans (fork_le_of_chainSteps before.chainSteps) step.chainStep.fork_le))
    obtain rfl : fork = nF := nSame.symm
    have mSame : mF = fork := Fork.ctorIdx_injective (Nat.le_antisymm
      (Nat.le_trans step.chainStep.fork_le afterRest)
      (fork_le_of_chainSteps before.chainSteps))
    obtain rfl : fork = mF := mSame.symm
    have eqn : (before.snoc step).append (after.append rest) = fromFin.append tailC := by
      rw [Run.append_assoc, cut', cut]
    have atN := floorAt (before.snoc step) (after.append rest) eqn
    by_cases down : effectiveAt (⟨fork, mS⟩ : ForkedBeaconState preset) i.toNat ≤ finEB
    · omega
    have alignedM := FloorTrace.effective_aligned (toFin.append before) h.genesis h.aligned i.toNat
    have gap := aligned_gap alignedM aligned (by omega)
    have origin := cfloor_origin h counted (fromFin.append tailC) h.near replayed i val initial
      clean retained before ((Run.nil.snoc step).append (after.append rest))
      (by rw [Run.append_assoc]; exact eqn)
    rcases origin with same | ⟨w, pre, post, hpre, hm, hle, -⟩
    · omega
    obtain ⟨wF, wS⟩ := w
    have wSame : wF = fork := Fork.ctorIdx_injective (Nat.le_antisymm
      (fork_le_of_chainSteps post.chainSteps) (fork_le_of_chainSteps pre.chainSteps))
    obtain rfl : fork = wF := wSame.symm
    obtain ⟨valW, initialW, -⟩ := pre.registryLifecycle.validators i.toNat val initial
    have hwhole : (pre.append (post.snoc step)).append (after.append rest) =
        fromFin.append tailC := by
      show ((pre.append post).snoc step).append (after.append rest) = _
      rw [hpre]
      exact eqn
    have lift : ∀ {m' n' : ForkedBeaconState preset} (before' : Run config checks ⟨fork, wS⟩ m')
        (step' : Step config checks m' n') (after' : Run config checks n' ⟨fork, nS⟩),
        (before'.snoc step').append after' = post.snoc step →
        ((pre.append before').snoc step').append (after'.append (after.append rest)) =
          fromFin.append tailC := by
      intro m' n' before' step' after' cut''
      have shift : ((pre.append before').snoc step').append after' =
          pre.append ((before'.snoc step').append after') :=
        (Run.append_assoc pre (before'.snoc step') after').symm
      rw [Run.append_assoc, shift, cut'']
      exact hwhole
    obtain ⟨segEv, segOk⟩ := Run.balanceEvents_ok (post.snoc step) h.early
      (getCurrentEpoch pulled).toNat
    obtain ⟨preEv, preOk⟩ := Run.balanceEvents_ok pre h.early (getCurrentEpoch pulled).toNat
    obtain ⟨D, split, closed⟩ := segment_potential h h.near i clean pre (post.snoc step)
      (after.append rest) valW initialW
      (fun before' step' after' cut'' w found => retained (pre.append before') step'
        (after'.append (after.append rest)) (lift before' step' after' cut'') w found)
      0 ρn ρd (by omega)
      (fun before' step' after' cut'' evs ok => pass (pre.append before') step'
        (after'.append (after.append rest)) (lift before' step' after' cut'') evs ok)
      segOk
    have app := balanceEvents_append pre (post.snoc step) (getCurrentEpoch pulled).toNat preOk
      segOk
    obtain ⟨b, hb, isPrefix⟩ := Run.balanceEvents_prefix (pre.append (post.snoc step))
      (after.append rest) (getCurrentEpoch pulled).toNat events (by rw [hwhole]; exact replayed)
    have sameEv : b = preEv ++ segEv := Except.ok.inj (hb.symm.trans app)
    have sub : segEv.Sublist events := by
      rw [sameEv] at isPrefix
      exact (List.sublist_append_right _ _).trans isPrefix.sublist
    have syncLe : (segEv.map (syncDebit i.toNat)).sum ≤ (events.map (syncDebit i.toNat)).sum :=
      (sub.map (syncDebit i.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
    have partialSeg : (segEv.map (floorPartialDebit i)).sum ≤
        (events.map (floorPartialDebit i)).sum :=
      (sub.map (floorPartialDebit i)).sum_le_sum fun _ _ => Nat.zero_le _
    have splitDebit := floorPenaltyDebit_sum i.toNat segEv
    have cappedW : effectiveAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat ≤
        (withdrawalMaxEffectiveBalance preset fork valW).toNat :=
      DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax (toFin.append pre) h.genesis
        h.caps h.early initialW
    have preEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have restEpoch := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (after.append rest).chainSteps)
    simp only at preEpoch restEpoch
    have kept := stay_arith ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
      ((getCurrentEpoch nS).toNat - (getCurrentEpoch wS).toNat)
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand base0 finEB
      (min (actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat)
        (withdrawalMaxEffectiveBalance preset fork valW).toNat) X
      ((pinTerms config pulled anc fin).partialsDue i.toNat)
      D (actualBalanceAt (⟨fork, nS⟩ : ForkedBeaconState preset) i.toNat)
      ((pinTerms config pulled anc fin).leakAt
        (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
      ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
      positive incPos quarter big testB fallX first fall (by omega)
      (by have := h.near; omega) (by omega) (by omega) (by simpa using closed)
    omega
  · intro p member
    obtain ⟨r1, r2, -⟩ : ∃ (r1 : Run config checks ⟨fork, fin⟩ p)
        (r2 : Run config checks p ⟨fork, counted⟩), r1.append r2 = rp.append rest := by
      obtain ⟨r1, r2, whole⟩ := balancePath_endpoint rp rest (Nat.le_refl _) member
      exact ⟨r1, r2, whole⟩
    obtain ⟨w, found, mono⟩ := r1.validatorCap_mono h.caps.activation h.caps.compounding
      (forkEnd r2) i.toNat val initial
    have := UInt64.le_iff_toNat_le.mp mono
    simp only [PinSplit2.capAt, found, Option.map_some, Option.getD_some]
    exact cappedFin.trans this

/-- A key whose exit comes late stays out of its withdrawal along a run from the finalized block.

Its exit epoch is constant from the state where it is set.

The withdrawable epoch is the delay after it, so it is after the horizon `high` of the call.

A key with no exit has the withdrawable epoch that no epoch reaches, since it exits no later. -/
private theorem retained_of_exit (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {e : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (high : ℕ) (highLe : high ≤ (getCurrentEpoch pulled).toNat) (i : ValidatorIndex)
    {wE : Validator} (foundE : e.validators.data[i.toNat]? = some wE)
    (late : high + 1 < wE.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = fromFin.append tail → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      (high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          high + 1 < u.withdrawableEpoch.toNat) := by
  obtain ⟨toFin⟩ := h.toFin
  intro m n before step after cut w found
  refine .inr fun u foundU => ?_
  have holds := Run.invariant (Genesis.invariant h.genesis) (toFin.append before)
  obtain ⟨last, located, kept⟩ := ((Run.nil.snoc step).append after).registryLifecycle.validators
    i.toNat u foundU
  by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
  · have ordered := holds.exitsOrdered u (Array.mem_of_getElem? foundU)
    rw [unset] at ordered
    have := UInt64.le_iff_toNat_le.mp ordered
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
    omega
  · have same := congrArg UInt64.toNat (kept.exitEpoch unset)
    have lastEq : last = wE := Option.some.inj (located.symm.trans foundE)
    have delayed := (toFin.append before).exit_withdrawable_delay h.genesis i.toNat u foundU unset
    subst lastEq
    omega

/-- A key whose exit at R is at or before the finalized epoch has that exit at the finalized state.

A key absent from the finalized registry was created after it, and its exit is assigned after it.

An exit assigned after the finalized state is at least the seed lookahead past its epoch.

An exit assigned before it is kept along the run. -/
private theorem exit_kept_of_le_fin (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat) :
    ∃ u, fin.validators.data[i]? = some u ∧ u.exitEpoch = w.exitEpoch := by
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat far
    omega
  have late : ∀ c ∈ (fromFin.append toPulled).departureCharges,
      (getCurrentEpoch fin).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
    DirectSafety.Run.departureCharges_epoch_ge_start (fromFin.append toPulled)
      (Nat.le_trans (by decide) h.fulu) h.early
  cases foundFin : fin.validators.data[i]? with
  | none =>
    obtain ⟨charge, member, -, epoch⟩ := PinSplit.Run.charge_of_exit (fromFin.append toPulled)
      (Nat.le_trans (by decide) h.fulu) h.early i (fun v hv => nomatch hv.symm.trans foundFin) w
      foundPulled assigned
    have := late charge member
    omega
  | some u =>
    refine ⟨u, rfl, ?_⟩
    by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨charge, member, -, epoch⟩ := (fromFin.append toPulled).departure_charge_of_assigned
        i u w foundFin foundPulled unset assigned
      have := late charge member
      omega
    · obtain ⟨last, located, kept⟩ :=
        (fromFin.append toPulled).registryLifecycle.validators i u foundFin
      have lastEq : last = w := Option.some.inj (located.symm.trans foundPulled)
      rw [← lastEq]
      exact (kept.exitEpoch unset).symm

/-- The events of C's run from the finalized block are those of its two parts.

They are read at R's epoch. -/
private theorem V_events (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat =
      .ok (eventsF ++ eventsC) := by
  have calledNat := UInt64.le_iff_toNat_le.mp h.called
  have nearC := h.near
  refine balanceEvents_append fromFin tailC _ ?_ ?_
  · rw [balanceEvents_eq_of_endpoint_le fromFin (localHigh := high) (by simp only; omega)
      (by simp only; omega)]
    exact replayedF
  · rw [balanceEvents_eq_of_endpoint_le tailC (localHigh := highC) (by simp only; omega)
      (by simp only; omega)]
    exact replayedC

/-- The sync debits of a key over two runs are at most those that `stub_V` charges. -/
private theorem V_sync_le (eventsF eventsC : List (BalanceEvent preset)) (v : ℕ) :
    ((eventsF ++ eventsC).map (syncDebit v)).sum ≤
      (eventsF.map (syncDebit v)).sum + syncF eventsC v := by
  have := sum_syncDebit_eq eventsC v
  unfold syncF
  rw [List.map_append, List.sum_append]
  omega

/-- A key falls by at least its effective balance at R, less any bound of its floor.

A key that is not in the finalized registry has the floor zero. -/
private theorem fall_floor (h : Setting config checks g split fin pulled anc counted V)
    (v : ValidatorIndex) (X : ℕ)
    (bound : fin.validators.data[v.toNat]? = none ∨
      (pinTerms config pulled anc fin).floorC v.toNat ≤ X) :
    (eR pulled v : ℤ) ≤ ((pinTerms config pulled anc fin).fall v.toNat : ℤ) + X := by
  have fallEq := fall_eq config pulled anc fin v.toNat
  simp only [h.shallow, ↓reduceIte] at fallEq
  have eRdef : eR pulled v = balanceAt pulled v.toNat := rfl
  rcases bound with none | le
  · obtain ⟨low, base, shape⟩ : ∃ low base : ℕ, (pinTerms config pulled anc fin).floorC v.toNat =
        if max (balanceAt fin v.toNat) base ≤ low + preset.downwardBand then balanceAt fin v.toNat
        else min (balanceAt fin v.toNat) (low - low % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :=
      ⟨_, _, rfl⟩
    have zero : balanceAt fin v.toNat = 0 := by simp [balanceAt, none]
    have : (pinTerms config pulled anc fin).floorC v.toNat = 0 := by
      rw [shape]
      split
      · exact zero
      · rw [zero]
        exact Nat.zero_min _
    omega
  · omega

/-- C's floor of a key is below its effective balance at each state of C's run, with its debits.

The debits are the key's sync debits over the run and their rounding band.

The key is in the finalized registry, unslashed at C's end, and kept out of withdrawal. -/
private theorem V_floor (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (val : Validator) (initial : fin.validators.data[v.toNat]? = some val)
    (clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC) :
    (pinTerms config pulled anc fin).floorC v.toNat ≤ effectiveAt z v.toNat +
      (events.map (syncDebit v.toNat)).sum + bandR events v.toNat := by
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin h.bands.1 v.toNat
  obtain ⟨base0, hbase0def⟩ : ∃ b, b = (pinTerms config pulled anc fin).base0 v.toNat := ⟨_, rfl⟩
  have hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    rw [hbase0def]
    simp only [pinTerms, initial, Option.map_some, Option.getD_some]
    rfl
  obtain ⟨X, hX⟩ : ∃ X, X = ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        ((pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat +
            (pinTerms config pulled anc fin).gainRate v.toNat + 1) +
      (pinTerms config pulled anc fin).partialsDue v.toNat := ⟨_, rfl⟩
  have hfall : ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        ((pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      (pinTerms config pulled anc fin).partialsDue v.toNat ≤ X := by
    rw [hX]
    have := Nat.mul_le_mul_left ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
      (show (pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1 ≤
        (pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat +
            (pinTerms config pulled anc fin).gainRate v.toNat + 1 by omega)
    omega
  have hfloorC : (pinTerms config pulled anc fin).floorC v.toNat =
      if max (balanceAt fin v.toNat) base0 ≤ (base0 - X) + preset.downwardBand
      then balanceAt fin v.toNat
      else min (balanceAt fin v.toNat)
        ((base0 - X) - (base0 - X) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    rw [hX, hbase0def]
    rfl
  have hfin : balanceAt fin v.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat := rfl
  obtain ⟨slack, margin⟩ := floorC_margin h fromFin tailC replayed v val initial ρn ρd positive
    leaky above base0 X (base0 - X) hbase0 rfl hfall
  exact floorC_at h fromFin tailC replayed v val initial clean retained base0 X (base0 - X)
    (balanceAt fin v.toNat) ((pinTerms config pulled anc fin).floorC v.toNat) hbase0 rfl hfin
    hfloorC rp rest cut ⟨slack, ρn, ρd, margin⟩
    (fun test sync => floorC_stay h fromFin tailC replayed v val initial clean retained
      h.facts.quarterBand ρn ρd positive leaky above base0 X (base0 - X) (balanceAt fin v.toNat)
      hbase0 rfl hfin hfall sync test rp rest cut)

/-- A V key that is active in C falls by at most `fall` and what C's floor leaves out.

C's floor is below the key's effective balance at C's end, plus its sync debits and their band.

The fall is the key's effective balance at R, less that floor, within the delay. -/
private theorem V_active (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ v ∈ V, v ∈ AC counted → (eR pulled v : ℤ) - eC counted v ≤
      ((pinTerms config pulled anc fin).fall v.toNat : ℤ) +
        ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat) +
          bandR (eventsF ++ eventsC) v.toNat := by
  intro v member act
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have delay := h.delay
  obtain ⟨wC, foundC, isActive⟩ := active_of_activeVoters h.early (s := counted) act
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActive
  have exitAfter := UInt64.lt_iff_toNat_lt.mp isActive.2
  have clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
    intro w found
    rw [foundC] at found
    cases found
    simpa [slashedFlagAt, foundC] using (h.voting v member).2
  have sync := V_sync_le eventsF eventsC v.toNat
  have := fall_floor h v (balanceAt counted v.toNat + ((eventsF.map (syncDebit v.toNat)).sum +
      syncF eventsC v.toNat) + bandR (eventsF ++ eventsC) v.toNat) (by
    cases initial : fin.validators.data[v.toNat]? with
    | none => exact .inl rfl
    | some val =>
      have floor := V_floor h fromFin tailC
        (V_events h fromFin tailC high highC endEpoch endEpochC replayedF replayedC) v val initial
        clean (retained_of_exit h fromFin tailC _ (Nat.le_refl _) v foundC (by omega))
          (fromFin.append tailC)
        Run.nil rfl
      exact .inr (by
        have : effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat =
          balanceAt counted v.toNat := rfl
        omega))
  have eCdef : eC counted v = balanceAt counted v.toNat := rfl
  omega

/-- A V key that left C's active set is charged by its exit, its late activation or its floor.

Its activation is at most R's epoch.

If that is within the seed lookahead of the split, the two branches agree on its activity there.

Then C's record exits it by C's epoch, which R reads as exiting or C charges.

Otherwise R activated it after finalizing the split, and R reads it as late.

R's registry may hold a key that C's does not, since the registries differ by position.

Then `h.voting` holds with the unslashed flag read as false.

Such a key activates late at R, so it is in the second case. -/
private theorem V_left (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ v ∈ VN counted V, (eR pulled v : ℤ) ≤
      ((pinTerms config pulled anc fin).fall v.toNat +
        ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat) +
        bandR (eventsF ++ eventsC) v.toNat + exitQ tailC v.toNat +
        (if (pinTerms config pulled anc fin).exitingB v.toNat = true then eR pulled v else 0) +
        (if (pinTerms config pulled anc fin).lateB v.toNat = true then eR pulled v
          else 0) : ℕ) := by
  intro v hv
  obtain ⟨member, notAC⟩ := Finset.mem_filter.mp hv
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨w, foundW, activeWb⟩ := active_of_activeVoters h.early (h.voting v member).1
  have activeW := activeWb
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt] at activeW
  have farEpoch := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have nearC := h.near
  by_cases early : w.activationEpoch.toNat ≤
      (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat
  · -- the key's activity at its activation epoch is shared, so C holds it
    have atAct : isActiveAt counted w.activationEpoch v.toNat = true := by
      rw [← activity_shared h (e := w.activationEpoch) early v.toNat]
      exact isActiveAt_eq_true_iff.mpr ⟨w, foundW, by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
        omega⟩
    obtain ⟨u, foundU, activeU⟩ := isActiveAt_eq_true_iff.mp atAct
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
      UInt64.lt_iff_toNat_lt] at activeU
    have exited : u.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
      by_contra later
      apply notAC
      simpa [AC, activeVoters] using mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨u, foundU, by
          simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
            UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
          omega⟩)
    have assigned : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at exited
      omega
    have unslashed : u.slashed = false := by
      simpa [slashedFlagAt, foundU] using (h.voting v member).2
    by_cases ex : (pinTerms config pulled anc fin).exitingB v.toNat = true
    · simp only [ex, ↓reduceIte]
      omega
    · obtain ⟨c, mem, idx⟩ := exit_charged h tailC foundU assigned exited unslashed
        (fun w' found _ => by
          obtain rfl : w' = w := Option.some.inj (found.symm.trans foundW)
          exact .inr (isActiveAt_eq_true_iff.mpr ⟨w', foundW, activeWb⟩))
        (by simpa using ex)
      have exitOf : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
          u.exitEpoch.toNat = c.epoch := by
        intro c' mem' idx'
        obtain ⟨x, found, -, epoch⟩ := Run.departure_charge_exit tailC c' mem'
        rw [idx'] at found
        obtain rfl : x = u := Option.some.inj (found.symm.trans foundU)
        exact epoch
      have startC := DirectSafety.Run.departureCharges_epoch_ge_start tailC
        (Nat.le_trans (by decide) h.fulu) h.early c mem
      simp only at startC
      have exitC := exitOf c mem idx
      have shallow := h.shallow
      have finOrder := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
      simp only at finOrder
      obtain ⟨sd, pre, post, cut, far, amount⟩ := exit_stop fromFin tailC v.toNat ⟨c, mem, idx⟩
        (fun c' mem' idx' => by have := exitOf c' mem' idx'; omega)
      have sync := V_sync_le eventsF eventsC v.toNat
      have clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
        intro w found
        rw [foundU] at found
        cases found
        exact unslashed
      have := fall_floor h v (exitQ tailC v.toNat + ((eventsF.map (syncDebit v.toNat)).sum +
          syncF eventsC v.toNat) + bandR (eventsF ++ eventsC) v.toNat) (by
        cases initial : fin.validators.data[v.toNat]? with
        | none => exact .inl rfl
        | some val =>
          have floor := V_floor h fromFin tailC
            (V_events h fromFin tailC high highC endEpoch endEpochC replayedF replayedC) v val
            initial clean
            (retained_of_exit h fromFin tailC _ (Nat.le_refl _) v foundU (by omega)) pre post cut
          exact .inr (by omega))
      omega
  · -- R activated the key after finalizing the split, so it reads the key as late
    have farAct : w.activationEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at activeW
      omega
    have eligible := Run.eligibility_le_finalized ((toFin.append fromFin).append toPulled)
      h.genesis v.toNat w foundW farAct
    have finCur := UInt64.le_iff_toNat_le.mp (finalized_le_current h)
    have late := (lateB_iff config pulled anc fin v.toNat).mpr ⟨w, foundW, by
      have := UInt64.le_iff_toNat_le.mp eligible
      simp only at this
      omega, by omega⟩
    simp only [late, ↓reduceIte]
    omega

/-- D-5/D-6 (fall, V): the fall of V keys, and the stake of V keys that left C's active set. -/
theorem stub_V (h : Setting config checks g split fin pulled anc counted V) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1) (events : List (BalanceEvent preset))
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cV1 pulled counted V + cV2 pulled counted V ≤
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) +
        (∑ v ∈ V, bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ V, (syncD eventsF v.toNat + (syncF events v.toNat + syncF eventsC v.toNat))) +
        (∑ v ∈ V, credDepR events v.toNat) +
        (∑ v ∈ V, consAmt events v.toNat) + preset.upwardBand * dueAt fin high V +
        (∑ v ∈ (VN counted V), exitQ tailC v.toNat) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
          eR pulled v) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
          eR pulled v) : ℕ) := by
  have base := stub_V_of h tailC
    (V_active h fromFin tailC high highC endEpoch endEpochC replayedF replayedC)
    (V_left h fromFin tailC high highC endEpoch endEpochC replayedF replayedC)
  have sync : ∑ v ∈ V, ((eventsF.map (syncDebit v.toNat)).sum + syncF eventsC v.toNat) ≤
      ∑ v ∈ V, (syncD eventsF v.toNat + (syncF events v.toNat + syncF eventsC v.toNat)) :=
    Finset.sum_le_sum fun v _ => by unfold syncD; omega
  refine le_trans base (Int.ofNat_le.mpr ?_)
  simp only [syncD, Finset.sum_add_distrib] at sync ⊢
  omega

end LowBound

/-- The low bound of an existing key is covered by its exit charge and its sync debits.

The key is in `K5`, so unslashed at C, activated at the finalized state, and charged on the run.

The charge is its effective balance at the exit call.

The bound reads the floor of its balance from the finalized state, with the penalties covered by
`drop`, the partials by `partialsDue`, and the hysteresis by the activation balance. -/
private theorem existing_low_or_floor (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (member : v ∈ K5 counted V) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    (pinTerms config pulled anc fin).lowEB v.toNat ≤
      exitQ tailC v.toNat + (events.map (syncDebit v.toNat)).sum := by
  have bound := existing_low_explicit h fromFin tailC replayed v member val initial charged
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
    simp only [pinTerms, initial, Option.map_some, Option.getD_some]
    rfl
  rw [lowEB_unfold, drop]
  exact bound

/-- The low and new-key floors are ordered: `newKeyFloor` is `newKeySlack` above `exitFloor`. -/
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

/-- From Fusaka and before Gloas, the parameters are those of Fusaka. -/
private theorem parameters_of_fusaka {fork : Fork} (fusaka : .fusaka ≤ fork)
    (early : fork < .glamsterdam) :
    EthLib.Consensus.parameters preset fork = EthLib.Consensus.parameters preset .fusaka := by
  cases fork <;> first
    | rfl
    | exact absurd fusaka (by decide)
    | exact absurd early (by decide)

/-- A key that is not yet activated at the finalized state and has a small charge loses seats.

The key is missing at the finalized state, or its activation there is unassigned.

It activates on the run from the finalized state, so it keeps at least `newKeyFloor` of effective
balance less its sync debits, from `Run.new_key_effective_floor`.

A small charge is below `exitFloor`, so the debits exceed `newKeySlack`.

It has no partial withdrawals queued, since a request needs an active key. -/
private theorem pending_key_claim (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (member : v ∈ K5 counted V)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (small : exitQ tailC v.toNat < (pinTerms config pulled anc fin).exitFloor)
    (fresh : fin.validators.data[v.toNat]? = none ∨
      ∃ w, fin.validators.data[v.toNat]? = some w ∧ w.activationEpoch = FAR_FUTURE_EPOCH) :
    (pinTerms config pulled anc fin).newKeySlack < (events.map (syncDebit v.toNat)).sum := by
  -- The charge splits C's run at the step that exits the key.
  --
  -- The key is activated there, by (I1).
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
    epoch⟩ := charge_activated (x := ⟨fork, split⟩) electra tailC c
    (tailC.departure_charge_site c cMember)
  rw [cIndex] at found foundB
  -- the exit epoch of the charge is at most C's epoch, since the key is not active there
  obtain ⟨wc, foundC, life⟩ := post.registryLifecycle.validators v.toNat w foundB
  have exitSame : wc.exitEpoch = w.exitEpoch := life.exitEpoch set
  have inK5 := Finset.mem_filter.mp member
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inK5
  obtain ⟨⟨listed, -⟩, notActive, -⟩ := inK5
  have notCurrent : v ∉ getActiveValidatorIndices counted (getCurrentEpoch counted) := fun now =>
    notActive (by simpa [AC, activeVoters] using now)
  rcases listed with now | before
  · exact absurd now notCurrent
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  obtain ⟨c', foundC', activeBefore⟩ := (mem_getActiveValidatorIndices within).mp before
  have same : c' = wc := Option.some.inj (foundC'.symm.trans foundC)
  subst same
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeBefore
  have exitLe : c'.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
    by_contra late
    refine notCurrent ((mem_getActiveValidatorIndices within).mpr ⟨c', foundC', ?_⟩)
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    have low := UInt64.le_iff_toNat_le.mp activeBefore.1
    have previous := getPreviousEpoch_toNat counted
    exact ⟨UInt64.le_iff_toNat_le.mpr (by omega), UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
  -- the charge counts, so `exitQ` is its amount
  have exitQEq : exitQ tailC v.toNat = c.amount := by
    have counts : c.epoch ≤ (getCurrentEpoch counted).toNat := by
      have exitNat := congrArg UInt64.toNat exitSame
      omega
    rcases exitQ_cases tailC v.toNat with ⟨none, -⟩ | ⟨d, dMember, dIndex, -, dQ⟩
    · exact absurd counts (none c cMember cIndex)
    · rw [dQ, charge_unique tailC dMember cMember (dIndex.trans cIndex.symm)]
  -- the run from the finalized state to the exit step, and its events, a prefix of the replay
  have shape : fromFin.append ((pre.snoc step).append post) =
      (fromFin.append pre).append ((Run.nil.snoc step).append post) := by
    have snoc : pre.snoc step = pre.append (Run.nil.snoc step) := rfl
    rw [snoc, ← Run.append_assoc pre (Run.nil.snoc step) post, Run.append_assoc]
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
  have floor := PinSplit.Run.new_key_effective_floor toFin h.genesis h.parameters h.caps h.aligned
    h.twoSlots electra h.fulu (getCurrentEpoch pulled).toNat h.guard (fromFin.append pre) aEarly
    aInside h.window h.delay h.bands h.facts v.toNat pending active
    (fun step fulu early crossing =>
      DirectSafety.Apriori.Internal.hysteresis_of_crossing_slot
        (DirectSafety.Apriori.Internal.slot_of_crossing step
          (UInt64.lt_iff_toNat_lt.mp crossing)) h.bands fulu early
        (UInt64.lt_iff_toNat_lt.mp crossing)) priorOk
  -- no queued partial withdrawal names the key at the finalized state, which has no activation
  have genesisPartials : Internal.AssignedPartials g.state := by
    obtain ⟨_, _, _, initialized⟩ := h.genesis
    have before := (initializeBeaconStateFromEth1_ok initialized).1
    intro fork
    exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) fork)).elim
  have finPartials : Internal.AssignedPartials fin :=
    (Internal.CapStep.run toFin h.caps.activation h.caps.compounding h.early).2.1 genesisPartials
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
  have debits := Run.partialDebit_le (fromFin.append pre) electra aEarly
    (getCurrentEpoch pulled).toNat ((getCurrentEpoch pulled).toNat + 1) aInside
    (window_short h) v priorOk
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
  rw [parameters_of_fusaka h.fulu h.early] at floorEq
  have effective : effectiveAt a v.toNat = c.amount := by
    simp only [effectiveAt, found, Option.map_some, Option.getD_some]
    exact amount.symm
  have prefixSum : (prior.map (syncDebit v.toNat)).sum ≤ (events.map (syncDebit v.toNat)).sum := by
    obtain ⟨rest, rfl⟩ := isPrefix
    simp only [List.map_append, List.sum_append]
    omega
  omega

/-- A key of `K5` that is not exiting at the call and has a small charge is low or loses seats.

A small charge is below `exitFloor`.

The key is then a low key, or its sync debits from the finalized state exceed `newKeySlack`.

The debits are those of the replay of the run from the finalized state to C's state.

A key that is not activated at the finalized state loses seats, by `pending_key_claim`.

An activated key is active and not withdrawable at R, by `activated_key_at_pulled`.

Its low bound is covered by its charge and its debits, by `existing_low_or_floor`. -/
private theorem small_charge_claim (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (member : v ∈ K5 counted V)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (small : exitQ tailC v.toNat < (pinTerms config pulled anc fin).exitFloor) :
    (pinTerms config pulled anc fin).lowB v.toNat = true ∨
      (pinTerms config pulled anc fin).newKeySlack < (events.map (syncDebit v.toNat)).sum := by
  classical
  by_cases fresh : fin.validators.data[v.toNat]? = none ∨
      ∃ w, fin.validators.data[v.toNat]? = some w ∧ w.activationEpoch = FAR_FUTURE_EPOCH
  · exact .inr (pending_key_claim h fromFin tailC replayed v member charged small fresh)
  obtain ⟨absent, notFar⟩ := not_or.mp fresh
  obtain ⟨w, found⟩ := Option.ne_none_iff_exists'.mp absent
  have activated : w.activationEpoch ≠ FAR_FUTURE_EPOCH := fun far => notFar ⟨w, found, far⟩
  by_cases rich : (pinTerms config pulled anc fin).newKeySlack < (events.map (syncDebit v.toNat)).sum
  · exact .inr rich
  refine .inl (lowB_intro config pulled anc fin
    (activated_key_at_pulled h tailC v member charged found activated) ?_)
  have floor := existing_low_or_floor h fromFin tailC replayed v member w found charged
  have order := exitFloor_add_slack h
  omega

/-- The total active balance at each step of a run from the finalized state is bounded.

It is at most three halves of the pulled total.

The run ends at most one epoch after the pulled epoch.

This is `total_band_of_guard` at the states of the steps of the run. -/
private theorem step_band_of_guard (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (r : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {pulledTotal : Gwei} (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      r.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  intro u w step member T read
  obtain ⟨pre, post, _, _, _⟩ := Run.contains_step_facts member h.early
  have wEarly : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have wEpoch : (getCurrentEpoch w.state).toNat ≤ (getCurrentEpoch e).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  exact total_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots electra
    h.guard (fromFin.append toPulled) h.early (Nat.le_succ _) (pre.snoc step) wEarly
    (by omega) pulledOk read

/-- The sync debits of any keys over a run from the finalized block fit the window's envelope.

The run ends within one epoch of R's, and its events are read at R's epoch.

The seats of the window debit at most its slots' envelopes, one for each epoch to the run's end. -/
private theorem syncDebits_window_le (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : run.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, (events.map (syncDebit v.toNat)).sum ≤
      ((getCurrentEpoch e).toNat + 1 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      run.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat :=
    step_band_of_guard h run within pulledOk
  have debits := (PinSplit5.Run.syncDebits_le run h.fulu h.early (getCurrentEpoch pulled).toNat
    replayed pulledTotal.toNat band (S.image fun v : ValidatorIndex => v.toNat)).1
  rw [Finset.sum_image fun _ _ _ _ same => UInt64.toNat_inj.mp same] at debits
  rwa [pulledOk]

/-- The keys whose sync debits from the finalized state exceed `newKeySlack` are at most the seats.

The sync debits of any keys over the run from the finalized state to C's state fit one envelope.

The envelope is for each seat and slot of the window.

A key over the slack has at least one more than the slack.

So the keys number at most the debits over the slack. -/
private theorem card_seat_keys_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (B : Finset ValidatorIndex)
    (seats : ∀ v ∈ B, (pinTerms config pulled anc fin).newKeySlack <
      (events.map (syncDebit v.toNat)).sum) :
    B.card ≤ (pinTerms config pulled anc fin).newKeySeats := by
  classical
  have debits := syncDebits_window_le h (fromFin.append tailC) h.near replayed B
  have each : B.card * ((pinTerms config pulled anc fin).newKeySlack + 1) ≤
      ∑ v ∈ B, (events.map (syncDebit v.toNat)).sum := by
    have := Finset.card_nsmul_le_sum B
      (fun v : ValidatorIndex => (events.map (syncDebit v.toNat)).sum)
      ((pinTerms config pulled anc fin).newKeySlack + 1) fun v member => seats v member
    simpa [smul_eq_mul] using this
  have seatsEq : (pinTerms config pulled anc fin).newKeySeats =
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat /
            max 1 (pinTerms config pulled anc fin).newKeySlack := rfl
  rw [seatsEq, Nat.le_div_iff_mul_le (lt_max_of_lt_left Nat.one_pos)]
  have epochs : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by have := h.near; omega
  have window := Nat.mul_le_mul_right
    (PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat)
    (Nat.mul_le_mul_right preset.SYNC_COMMITTEE_SIZE.toNat
      (Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochs))
  have unit : max 1 (pinTerms config pulled anc fin).newKeySlack ≤
      (pinTerms config pulled anc fin).newKeySlack + 1 := by omega
  calc B.card * max 1 (pinTerms config pulled anc fin).newKeySlack
      ≤ B.card * ((pinTerms config pulled anc fin).newKeySlack + 1) := Nat.mul_le_mul_left _ unit
    _ ≤ _ := each
    _ ≤ _ := debits
    _ ≤ _ := by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using window

/-- The keys of `K5` that C's branch charges are few.

A key is charged if the run has a departure charge at its position.

`card_big_charges_le` counts the charges of at least `exitFloor`.

`small_charge_claim` counts the small ones, and reads no exit flag of R.

They are at most the keys that `queueKeys` counts.

Those are the keys with a large charge, the low keys and the keys that lose seats. -/
private theorem charged_count (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    ((K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card ≤
      (pinTerms config pulled anc fin).queueKeys := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨events, replayed⟩ := (fromFin.append tailC).balanceEvents_ok h.early
    (getCurrentEpoch pulled).toNat
  set S := (K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat
    with hS
  have big := card_big_charges_le h tailC S
  set small := S.filter fun v => ¬ (pinTerms config pulled anc fin).exitFloor ≤
    exitQ tailC v.toNat with hSmall
  have claim : ∀ v ∈ small, (pinTerms config pulled anc fin).lowB v.toNat = true ∨
      (pinTerms config pulled anc fin).newKeySlack < (events.map (syncDebit v.toNat)).sum := by
    intro v member
    obtain ⟨inS, notBig⟩ := Finset.mem_filter.mp member
    obtain ⟨inK5, charged⟩ := Finset.mem_filter.mp inS
    exact small_charge_claim h fromFin tailC replayed v inK5 charged (Nat.lt_of_not_ge notBig)
  have seats := card_seat_keys_le h fromFin tailC replayed
    (small.filter fun v => ¬ (pinTerms config pulled anc fin).lowB v.toNat = true) (by
      intro v member
      obtain ⟨inSmall, notLow⟩ := Finset.mem_filter.mp member
      exact (claim v inSmall).resolve_left notLow)
  have lows : (small.filter fun v => (pinTerms config pulled anc fin).lowB v.toNat = true).card ≤
      (pinTerms config pulled anc fin).lowKeys := by
    rw [lowKeys_eq]
    have count := sum_toNat_le (S := small.filter fun v =>
        (pinTerms config pulled anc fin).lowB v.toNat = true)
      (P := (pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).lowB i = true) (fun _ => 1) (fun v member => by
      have low := (Finset.mem_filter.mp member).2
      obtain ⟨w, found⟩ := lowB_found config pulled anc fin low
      exact mem_positions_filter config pulled anc fin found low)
    simpa using count
  have coverSmall : small ⊆
      (small.filter fun v => (pinTerms config pulled anc fin).lowB v.toNat = true) ∪
        (small.filter fun v => ¬ (pinTerms config pulled anc fin).lowB v.toNat = true) := by
    intro v member
    by_cases low : (pinTerms config pulled anc fin).lowB v.toNat = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨member, low⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨member, low⟩)
  have coverS : S ⊆ (S.filter fun v => (pinTerms config pulled anc fin).exitFloor ≤
      exitQ tailC v.toNat) ∪ small := by
    intro v member
    by_cases large : (pinTerms config pulled anc fin).exitFloor ≤ exitQ tailC v.toNat
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨member, large⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨member, large⟩)
  have splitS := (Finset.card_le_card coverS).trans (Finset.card_union_le _ _)
  have splitSmall := (Finset.card_le_card coverSmall).trans (Finset.card_union_le _ _)
  rw [queueKeys_unfold]
  omega

/-- K5 bands: the two bands beyond `credits`' one of each credited K5 key, weight 3.

Split by `exitingB`: the keys whose exit R reads and those the queues let exit on C. -/
theorem bud_exitingBands (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    2 * (∑ v ∈ (K5 counted V), bandC tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).exitingBands :=
  two_bands_le_exitingBands config pulled anc fin counted V tailC highC
    (fun _ member flag _ => K5_charged h tailC member flag) (charged_count h tailC)

/-- K5 (`queueRise`): the rise of keys after their exit starts on C's branch.

Every key of `K5` with a departure charge counts, since `charged_count` bounds all of them. -/
theorem bud_queueRise (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) :
    3 * (∑ v ∈ (K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        riseQ tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).queueRise := by
  classical
  rw [queueRise_unfold]
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have near := h.near
  have later := UInt64.le_iff_toNat_le.mp h.later
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · simp only [tight, ↓reduceIte]
    have tightLe : (pinTerms config pulled anc fin).depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat :=
      of_decide_eq_true tight
    have depthEq : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    rw [depthEq] at tightLe
    have none : ∀ v ∈ (K5 counted V).filter
        (fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat),
        riseQ tailC highC v.toNat = 0 := by
      intro v member
      apply riseQ_eq_zero
      intro c charged same
      have inside := charge_epoch_le_of_K5 h.early tailC (Finset.mem_filter.mp member).1 c
        charged same
      have far : (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
        DirectSafety.Run.departureCharges_epoch_ge_start tailC electra h.early c charged
      omega
    rw [Finset.sum_eq_zero none]
    simp
  · simp only [tight, Bool.false_eq_true, ↓reduceIte]
    have sumEq := Finset.sum_filter_ne_zero
      (s := (K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
      (f := fun v : ValidatorIndex => riseQ tailC highC v.toNat)
    have each := Finset.sum_le_card_nsmul
      (((K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).filter
          fun v => riseQ tailC highC v.toNat ≠ 0)
      (fun v : ValidatorIndex => riseQ tailC highC v.toNat)
      (preset.upwardBand + (pinTerms config pulled anc fin).depth *
        (pinTerms config pulled anc fin).gainRateMax)
      fun v _ => riseQ_le h tailC highC endEpochC v.toNat
    have count := (Finset.card_le_card (Finset.filter_subset
      (fun v : ValidatorIndex => riseQ tailC highC v.toNat ≠ 0)
      ((K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat))).trans
      (charged_count h tailC)
    rw [smul_eq_mul] at each
    rw [← sumEq]
    calc _ ≤ 3 * ((((K5 counted V).filter fun v =>
            ∃ c ∈ tailC.departureCharges, c.index = v.toNat).filter
          fun v => riseQ tailC highC v.toNat ≠ 0).card *
        (preset.upwardBand + (pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).gainRateMax)) := Nat.mul_le_mul_left _ each
      _ ≤ _ := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ count)

/-- K5 (`exitingRise`): the keys whose exit R reads.

The keys of `K5` are those without a departure charge on C's run. -/
theorem bud_exitingRise (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (∑ v ∈ (K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (pinTerms config pulled anc fin).rise v.toNat) ≤
      (pinTerms config pulled anc fin).exitingRise := by
  classical
  have exitingRise : (pinTerms config pulled anc fin).exitingRise =
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).exitingB i = true,
        (pinTerms config pulled anc fin).rise i := by
    simp only [pinTerms, decide_eq_true_eq]
  have apart : Disjoint
      ((K5 counted V).filter fun v => ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
      ((K6 pulled counted).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = true) := by
    refine Finset.disjoint_left.mpr fun v first second => ?_
    have active := (Finset.mem_filter.mp (Finset.mem_filter.mp second).1).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp first).1).2.1 active
  rw [← Finset.sum_union apart, exitingRise]
  refine sum_toNat_le (pinTerms config pulled anc fin).rise fun v selected => ?_
  have exiting : (pinTerms config pulled anc fin).exitingB v.toNat = true := by
    rcases Finset.mem_union.mp selected with chosen | chosen
    · exact K5_exiting_of_not_charged h tailC (Finset.mem_filter.mp chosen).1
        (Finset.mem_filter.mp chosen).2
    · exact (Finset.mem_filter.mp chosen).2
  have found : ∃ w, pulled.validators.data[v.toNat]? = some w := by
    obtain ⟨-, -, read⟩ := (by simpa only [pinTerms, decide_eq_true_eq] using exiting :
      _ ∧ _ ∧ ((pulled.validators.data[v.toNat]?).map fun w =>
        decide (w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).getD false = true)
    exact validator_of_flag (.inr read)
  obtain ⟨w, found⟩ := found
  exact mem_positions_filter config pulled anc fin found exiting

/-- The credits of a set of keys in one event are at most the event's credit limit. -/
private theorem sum_keyCredit_le_creditLimit (S : Finset ValidatorIndex) (e : BalanceEvent preset)
    (bounded : e.credits ≤ e.creditLimit) : ∑ v ∈ S, keyCredit v.toNat e ≤ e.creditLimit := by
  refine Nat.le_trans ?_ bounded
  unfold keyCredit
  have inj : Set.InjOn (fun v : ValidatorIndex => v.toNat) S := fun a _ b _ same =>
    UInt64.toNat_inj.mp same
  rw [← Finset.sum_image (f := fun i => actualBalanceAt e.after i - actualBalanceAt e.before i)
    inj]
  exact PinSplit5.keys_credits_le _ e

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
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  rcases link with toMne | ⟨back, same⟩
  · obtain ⟨toM⟩ := toMne
    exact ⟨rate_of_guard h toM within (Or.inl rfl) pqOk total perIncrement totalOk per,
      rate_of_guard h toM within (Or.inr rfl) pqOk total perIncrement totalOk per,
      total_band_of_guard toFin h.genesis h.parameters h.caps h.aligned h.twoSlots electra
        h.guard (fromFin.append toPulled) h.early (Nat.le_succ _) toM h.early within pulledOk
        totalOk⟩
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
    have first := rate_of_guard h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) inside
      (Or.inl rfl) pqOk atFin perIncrement atFinOk per
    have second := rate_of_guard h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) inside
      (Or.inr rfl) pqOk atFin perIncrement atFinOk per
    refine ⟨?_, ?_, total_band_of_guard toFin h.genesis h.parameters h.caps h.aligned
      h.twoSlots electra h.guard (fromFin.append toPulled) h.early (Nat.le_succ _)
      (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) h.early inside pulledOk atFinOk⟩
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
    (∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      inner).1) * 896 ≤
      324 * ((pinTerms config pulled anc fin).perIncrement *
        (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have uFork : u.fork = fork := Fork.ctorIdx_injective (Nat.le_antisymm
    (fork_le_of_chainSteps rest.chainSteps) (fork_le_of_chainSteps inner.chainSteps))
  have uEarly : u.fork < .glamsterdam := by rw [uFork]; exact h.early
  have within : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (inner.append rest).chainSteps)) h.near
  obtain ⟨events, replayed, bounded⟩ :=
    Run.balanceEvents_bounded toM inner h.genesis uEarly highC
  have scan : ∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      inner).1 ≤ sourceCredits .rewards events := by
    have := creditScan_sum_le S (fun s => decide (s = .rewards)) (fun _ => false) highC
      (fun e => e.creditLimit) inner replayed fun e member _ =>
        sum_keyCredit_le_creditLimit S e (bounded e member).1
    simpa [sourceCredits] using this
  obtain ⟨reads, data⟩ := epoch_credits_data inner (by exact electra) uEarly same highC replayed
  rcases reads with ⟨total, perIncrement, totalOk, per⟩ | ⟨quiet, -⟩
  swap
  · rw [quiet] at scan
    simp [Nat.le_zero.mp scan]
  obtain ⟨credits, -⟩ := data total perIncrement totalOk per
  obtain ⟨pq, pqOk⟩ := quarter_base_ok h.facts per ((getTotalActiveBalance pulled).toOption.getD 0)
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
/-- The proposer credits of a set of keys over a one-epoch segment of C's branch are bounded.

The segment may follow a run `head` of its own epoch, whose credits it adds to.

The bound is the pin's rate on the pulled total, with `896` times the credits on the left.

The slot that ends the segment adds no block credit.

So the segment fits as its run before that slot does. -/
private theorem propN_segment_le (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) (S : Finset ValidatorIndex) {T : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok T) {s0 : BeaconState preset fork}
    {m n : ForkedBeaconState preset} (toS : Run config checks g ⟨fork, s0⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, s0⟩) ∨
      ∃ _ : Run config checks ⟨fork, s0⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch s0)
    (head : Run config checks ⟨fork, s0⟩ m) (mid : Run config checks m n)
    (rest : Run config checks n ⟨fork, counted⟩)
    (sameStart : getCurrentEpoch m.state = getCurrentEpoch s0)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state) :
    ((∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      head).1) + ∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat
        highC mid).1) * 896 ≤
      324 * ((pinTerms config pulled anc fin).perIncrement *
        (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement := by
  have mFork : m.fork = fork := Fork.ctorIdx_injective (Nat.le_antisymm
    (fork_le_of_chainSteps (mid.append rest).chainSteps) (fork_le_of_chainSteps head.chainSteps))
  obtain ⟨mf, ms⟩ := m
  obtain rfl : mf = fork := mFork
  by_cases same : getCurrentEpoch n.state = getCurrentEpoch ms
  · have whole := propN_epoch_le h highC S pulledOk toS link (head.append mid) rest
      (same.trans sameStart)
    simp only [creditScan_append, Finset.sum_add_distrib] at whole
    exact whole
  cases mid with
  | nil => exact absurd rfl same
  | @snoc u _ inner step =>
    have uEpoch : getCurrentEpoch u.state = getCurrentEpoch ms := starts step (.last _ _)
    have crossing : getCurrentEpoch u.state < getCurrentEpoch n.state :=
      UInt64.lt_of_le_of_ne step.chainStep.currentEpoch_le
        (fun equal => same (equal.symm.trans uEpoch))
    -- The last step leaves the epoch, so it is the slot that ends it.
    obtain ⟨boundary, rfl⟩ : ∃ boundary, step = .slot boundary := by
      cases step with
      | block engine signed due ok =>
        exact absurd (by simp only [getCurrentEpoch, (frame_processBlock
          (applySignedBlock_ok ok).2.1).slot]) (UInt64.ne_of_lt crossing).symm
      | slot ok => exact ⟨ok, rfl⟩
    have whole := propN_epoch_le h highC S pulledOk toS link (head.append inner)
      ((Run.nil.snoc (Step.slot boundary)).append rest) (uEpoch.trans sameStart)
    simp only [creditScan_append, Finset.sum_add_distrib] at whole
    refine Nat.le_trans (Nat.mul_le_mul_right 896 (Nat.add_le_add_left
      (Finset.sum_le_sum fun v _ => ?_) _)) whole
    rw [creditScan_snoc_fst]
    split <;> simp [stepCredit]

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

The proposer base pays the bound, and `attesterExcess` pays one more increment's rate. -/
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
/-- C's proposer credits to any set of keys, with the sync part of the bound, are bounded.

The credits start at a state `b` of the split's epoch, so they include the run `pre` from `b`.

The bound is the proposer credit of each epoch of the window.

The credits of each epoch are cut over the blocks, and the split's epoch is cut once from `b`.

So the flag rewards of its epoch pass are not read. -/
private theorem proposer_rewards_le (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
      ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch b)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (S : Finset ValidatorIndex) :
    (∑ v ∈ S, propN (pre.append tailC) highC v.toNat) +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer ≤
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit := by
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
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ v ∈ S, (creditScan (fun s => decide (s = .rewards))
    (fun _ => false) v.toNat highC pre).1 := ⟨_, rfl⟩
  have first : P ≤ B := by
    have one := propN_segment_le h highC S pulledOk toB link pre
      (Run.nil : Run config checks ⟨fork, split⟩ ⟨fork, split⟩) tailC sameEpoch
      (fun step member => by cases member)
    rw [hB, hP]
    refine (Nat.le_div_iff_mul_le (by norm_num)).mpr (Nat.le_trans ?_ one)
    simp only [creditScan_nil_fst, Finset.sum_const_zero, Nat.add_zero]
    exact Nat.le_refl _
  have cut := run_cuts_of_additive tailC h.early (fun _ => True)
    (fun r => ∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      r).1) (fun i => if i = 0 then B - P else B)
    (fun pre post _ => by simp only [creditScan_append, Finset.sum_add_distrib])
    (fun _ _ _ _ => trivial)
    (fun {m n} toM mid rest starts _ => by
      obtain ⟨mf, ms⟩ := m
      obtain rfl : fork = mf := (fork_eq_of_run toM (mid.append rest) (Nat.le_refl _)).symm
      by_cases e : getCurrentEpoch ms = getCurrentEpoch split
      · -- the segment is in the split's epoch, so it adds to the credits of `pre`
        have index : ix (⟨fork, split⟩ : ForkedBeaconState preset) ⟨fork, ms⟩ = 0 := by
          simp only [ix, e]
          omega
        simp only [index, ↓reduceIte]
        have one := propN_segment_le h highC S pulledOk toB link (pre.append toM) mid rest
          (by simpa only [sameEpoch] using e) starts
        have again : P ≤ ∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false)
            v.toNat highC (pre.append toM)).1 := by
          rw [hP]
          exact Finset.sum_le_sum fun v _ => by
            rw [creditScan_append]
            exact Nat.le_add_right _ _
        have bound : P + ∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false)
            v.toNat highC mid).1 ≤ B := by
          rw [hB]
          exact (Nat.le_div_iff_mul_le (by norm_num)).mpr
            (Nat.le_trans (Nat.mul_le_mul_right 896 (Nat.add_le_add_right again _)) one)
        omega
      · have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
        have later : getCurrentEpoch split < getCurrentEpoch ms :=
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
        simp only [creditScan_nil_fst, Finset.sum_const_zero, Nat.zero_add] at one
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
  have joined : ∑ v ∈ S, propN (pre.append tailC) highC v.toNat =
      P + ∑ v ∈ S, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
        tailC).1 := by
    rw [hP, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => creditScan_append _ _ _ _ pre tailC
  have depth : ix ⟨fork, split⟩ ⟨fork, counted⟩ + 1 ≤ (pinTerms config pulled anc fin).depth := by
    have fin' := UInt64.le_iff_toNat_le.mp h.finalized
    have called := UInt64.le_iff_toNat_le.mp h.called
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
      have called := UInt64.le_iff_toNat_le.mp h.called
      exact mem_positions_filter config pulled anc fin found (by simp [found]; omega)
    · have slots := h.twoSlots
      have two : 2 ≤ (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := by
        have := UInt64.le_iff_toNat_le.mp h.finalized
        have := UInt64.le_iff_toNat_le.mp h.called
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

/-- The due entries of a queue, summed over two disjoint sets of targets, add up. -/
private theorem sum_filterMap_filter_add {α β : Type} (L : List α) (look : α → Option β)
    (ok : β → Bool) (p q : α → Bool) (disjoint : ∀ a, ¬ (p a = true ∧ q a = true))
    (f : β → ℕ) :
    ((((L.filter fun a => p a || q a).filterMap look).filter ok).map f).sum =
      ((((L.filter p).filterMap look).filter ok).map f).sum +
        ((((L.filter q).filterMap look).filter ok).map f).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    by_cases hp : p a = true
    · have hq : q a = false := by
        cases h : q a
        · rfl
        · exact absurd ⟨hp, h⟩ (disjoint a)
      cases hl : look a with
      | none => simp [hp, hq, hl, ih]
      | some b =>
        by_cases hb : ok b = true
        · simp [hp, hq, hl, hb, ih]
          omega
        · simp [hp, hq, hl, hb, ih]
    · have hp' : p a = false := by simpa using hp
      by_cases hq : q a = true
      · cases hl : look a with
        | none => simp [hp', hq, hl, ih]
        | some b =>
          by_cases hb : ok b = true
          · simp [hp', hq, hl, hb, ih]
            omega
          · simp [hp', hq, hl, hb, ih]
      · have hq' : q a = false := by simpa using hq
        simp [hp', hq', ih]

/-- The sources of the due entries of X's queue that name a target in `T`. -/
private def dueList (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : List Validator :=
  (((X.pendingConsolidations electra).data.toList.filter fun c =>
      decide (c.targetIndex ∈ T)).filterMap fun c =>
    X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
      !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)

/-- `dueAt` counts `dueList`. -/
private theorem dueAt_eq (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : dueAt X high T = (dueList X electra high T).length := by
  unfold dueAt dueList
  simp only [electra, ↓reduceDIte]

/-- The caps of the due entries of two disjoint sets of targets add up. -/
private theorem dueList_sum_union (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (disjoint : Disjoint A B) (f : Validator → ℕ) :
    ((dueList X electra high (A ∪ B)).map f).sum =
      ((dueList X electra high A).map f).sum + ((dueList X electra high B).map f).sum := by
  unfold dueList
  have := sum_filterMap_filter_add (X.pendingConsolidations electra).data.toList
    (fun c => X.validators.data[c.sourceIndex.toNat]?)
    (fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1))
    (fun c => decide (c.targetIndex ∈ A)) (fun c => decide (c.targetIndex ∈ B))
    (by
      rintro c ⟨ha, hb⟩
      simp only [decide_eq_true_eq] at ha hb
      exact Finset.disjoint_left.mp disjoint ha hb) f
  simpa [Finset.mem_union, Bool.decide_or] using this

/-- The due entries of two disjoint sets of targets number as many as those of their union. -/
private theorem dueList_length_union (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (disjoint : Disjoint A B) :
    (dueList X electra high (A ∪ B)).length =
      (dueList X electra high A).length + (dueList X electra high B).length := by
  have := dueList_sum_union X electra high disjoint (fun _ => 1)
  simpa using this

/-- A later horizon keeps at least the stake of an earlier one. -/
private theorem dueList_sum_mono (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    {high high' : ℕ} (later : high ≤ high') (T : Finset ValidatorIndex) (f : Validator → ℕ) :
    ((dueList X electra high T).map f).sum ≤ ((dueList X electra high' T).map f).sum := by
  unfold dueList
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
    (dueList X electra high T).length ≤ (dueList X electra high' T).length := by
  simpa using dueList_sum_mono X electra later T fun _ => 1

/-- More targets keep at least the entries of fewer. -/
private theorem dueList_length_subset (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (sub : A ⊆ B) :
    (dueList X electra high A).length ≤ (dueList X electra high B).length := by
  unfold dueList
  refine (((List.monotone_filter_right _ fun c hc => ?_).filterMap _).filter _).length_le
  simp only [decide_eq_true_eq] at hc ⊢
  exact sub hc

/-- The due entries of any targets have at most the stake of all entries read at that horizon. -/
private theorem dueList_sum_le_all (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) (T : Finset ValidatorIndex) (f : Validator → ℕ) :
    ((dueList X electra high T).map f).sum ≤
      ((((((X.pendingConsolidations electra).data.toList.filterMap fun c =>
        X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map f)).sum) := by
  unfold dueList
  refine (List.Sublist.map f ?_).sum_le_sum fun _ _ => Nat.zero_le _
  exact (List.filter_sublist.filterMap _).filter _

/-- The two readings of the credit of an event are one definition. -/
private theorem keyCredit_eq (i : ℕ) (e : BalanceEvent preset) :
    keyCredit i e = PinSplit.keyCredit i e := rfl

/-- A whistleblower's share of an amount is at most the amount.

The quotient is at least thirty, so a share of `33/300` of the amount, rounded up, fits. -/
private theorem wShare_le (facts : PinPresetFacts preset) (x : ℕ) : wShare preset fork x ≤ x := by
  have quotient := facts.whistleblower fork
  unfold wShare
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
    (T : Finset ValidatorIndex) : ∑ v ∈ T, dueAt X high {v} = dueAt X high T := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [dueAt_eq X electra high]
    simp [dueList]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, dueAt_eq X electra high, dueAt_eq X electra high,
      dueAt_eq X electra high, show insert a s = {a} ∪ s from rfl,
      dueList_length_union X electra high (Finset.disjoint_singleton_left.mpr ha)]

/-- The band of a key is its upward band for each due entry that names it, and these add over keys.

The due entries of a set of targets are the due entries of its keys. -/
private theorem bandX_sum (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) :
    ∑ v ∈ T, bandX X high v.toNat = preset.upwardBand * dueAt X high T := by
  classical
  have single (v : ValidatorIndex) :
      bandX X high v.toNat = preset.upwardBand * dueAt X high {v} := by
    simp [bandX]
  simp only [single]
  rw [← Finset.mul_sum, dueAt_sum X electra high T]

/-- The classes `K4`, `K5` and `K6` share no key with each other or with `V`. -/
private theorem classes_disjoint (h : Setting config checks g split fin pulled anc counted V) :
    Disjoint (K4 pulled counted V) (K5 counted V) ∧
    Disjoint (K4 pulled counted V) (K6 pulled counted) ∧
    Disjoint (K5 counted V) (K6 pulled counted) ∧
    Disjoint V (K4 pulled counted V) ∧ Disjoint V (K5 counted V) ∧
    Disjoint V (K6 pulled counted) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine Finset.disjoint_left.mpr fun v a b => ?_
  · simp only [K4, K5, Finset.mem_filter] at a b
    exact b.2.1 a.1
  · simp only [K4, K6, Finset.mem_filter] at a b
    exact b.2.2 a.2.1
  · simp only [K5, K6, Finset.mem_filter] at a b
    exact a.2.1 b.1
  · simp only [K4, Finset.mem_filter] at b
    exact b.2.2.2 a
  · simp only [K5, Finset.mem_filter] at b
    exact b.2.2 a
  · simp only [K6, Finset.mem_filter] at b
    exact b.2.2 (h.voting v a).1

/-- A key of `K4`, `K5` or `K6` is in C's quorum, so it is unslashed at C. -/
private theorem classes_unslashed {v : ValidatorIndex}
    (member : v ∈ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted) :
    slashedFlagAt counted v.toNat ≠ some true := by
  have inQ : v ∈ Q counted := by
    simp only [Finset.mem_union] at member
    rcases member with (h4 | h5) | h6
    · simp only [K4, Finset.mem_filter] at h4
      exact h4.2.2.1
    · simp only [K5, Finset.mem_filter] at h5
      exact h5.1
    · simp only [K6, Finset.mem_filter] at h6
      exact h6.2.1
  intro slashed
  simp only [Q, quorumVoters, Finset.mem_filter] at inQ
  have unslashed := inQ.2
  unfold slashedFlagAt at slashed
  rw [slashed] at unslashed
  simp at unslashed

/-- The keys slashed at C and not at the split are in no class of C's quorum, and not in `V`. -/
private theorem sc_disjoint (h : Setting config checks g split fin pulled anc counted V) :
    Disjoint (K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted) (SC pulled counted split) ∧
    Disjoint V (SC pulled counted split) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hk hs
    simp only [SC, Finset.mem_filter] at hs
    exact classes_unslashed hk hs.2.1
  · rw [Finset.disjoint_left]
    intro v hv hs
    simp only [SC, Finset.mem_filter] at hs
    have unslashed := (h.voting v hv).2
    rw [hs.2.1] at unslashed
    simp at unslashed

/-- The keys created after R's registry and slashed at C are in no other class.

They are slashed at C, so they are not in C's quorum or in `V`.

They are absent at the split, so they are not in `SC`. -/
private theorem cs_disjoint (h : Setting config checks g split fin pulled anc counted V) :
    Disjoint (K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪ SC pulled counted split)
      (CS pulled counted) ∧ Disjoint V (CS pulled counted) := by
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hk hc
    simp only [CS, Finset.mem_filter] at hc
    rcases Finset.mem_union.mp hk with quorum | created
    · exact classes_unslashed quorum hc.2.2
    · simp only [SC, Finset.mem_filter] at created
      have absent : slashedFlagAt split v.toNat = none := by
        simp only [slashedFlagAt, Option.map_eq_none_iff]
        exact Array.getElem?_eq_none (by omega)
      rw [absent] at created
      cases created.2.2
  · rw [Finset.disjoint_left]
    intro v hv hc
    simp only [CS, Finset.mem_filter] at hc
    have unslashed := (h.voting v hv).2
    rw [hc.2.2] at unslashed
    simp at unslashed

/-- A key that a run credits.

A block step credits it, or a pending-deposit pass does. -/
private def creditedKey {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) : Bool :=
  decide (0 < grossScan v.toNat high tail +
    (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat high tail).1)

/-- `creditUnits` is `unitGain` for the credited-key slots and for two more of each exiting key.

The same holds for each queue key.

The slots are at least the proposers, the seats and the deposit recipients of the window.

They also hold the seat units of R's branch and the shared segment. -/
private theorem creditUnits_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
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
private theorem debit_keys_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high : ℕ)
    {events eventsF : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents high = .ok eventsF) (A B : Finset ValidatorIndex)
    (debitsF : ∀ v ∈ A, 0 < syncD eventsF v.toNat) (debitsR : ∀ v ∈ B, 0 < syncD events v.toNat) :
    (A ∪ B).card ≤ ((pinTerms config pulled anc fin).depth /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((pinTerms config pulled anc fin).depthFin /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2)) *
      preset.SYNC_COMMITTEE_SIZE.toNat := by
  classical
  obtain ⟨eventsC, replayedC⟩ := tailC.balanceEvents_ok h.early high
  have inj : Function.Injective fun v : ValidatorIndex => v.toNat := fun a b same =>
    UInt64.toNat_inj.mp same
  have union := seat_union_card h fromFin tail tailC high replayed replayedF replayedC
    (A.image fun v => v.toNat) (B.image fun v => v.toNat)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      have := debitsF v hv
      simp only [syncD, List.map_append, List.sum_append] at this ⊢
      omega)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact debitsR v hv)
  rw [← Finset.image_union, Finset.card_image_of_injective _ inj] at union
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp h.called
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

/-- The credited keys of `K4`, `K5`, `K6`, `SC` and `CS` fit the credited-key slots of the window.

The slots are the proposers, the seats and the deposit recipients of the window.

A credited key of `CS` is a credited key of C's run, in C's registry, as the others are. -/
private theorem credited_classes_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    ((K4 pulled counted V).filter fun v => creditedKey tailC highC v = true).card +
      ((K5 counted V).filter fun v => creditedKey tailC highC v = true).card +
      ((K6 pulled counted).filter fun v => creditedKey tailC highC v = true).card +
      ((SC pulled counted split).filter fun v => creditedKey tailC highC v = true).card +
      ((CS pulled counted).filter fun v => creditedKey tailC highC v = true).card ≤
    (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
      ((pinTerms config pulled anc fin).depth /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
          preset.SYNC_COMMITTEE_SIZE.toNat +
      (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  obtain ⟨d45, d46, d56, -, -, -⟩ := classes_disjoint h
  obtain ⟨dSC, -⟩ := sc_disjoint h
  obtain ⟨dCS, -⟩ := cs_disjoint h
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  set C4 := (K4 pulled counted V).filter fun v => creditedKey tailC highC v = true
  set C5 := (K5 counted V).filter fun v => creditedKey tailC highC v = true
  set C6 := (K6 pulled counted).filter fun v => creditedKey tailC highC v = true
  set Csc := (SC pulled counted split).filter fun v => creditedKey tailC highC v = true
  set Ccs := (CS pulled counted).filter fun v => creditedKey tailC highC v = true
  -- The five classes are apart, and each key of them is in C's registry.
  have apart : Disjoint (C4 ∪ C6) C5 :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_filter_filter d45,
      (Finset.disjoint_filter_filter d56).symm⟩
  have apartSC : Disjoint (C4 ∪ C6 ∪ C5) Csc :=
    Finset.disjoint_of_subset_left (u := K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted)
      (fun v hv => by
        simp only [C4, C5, C6, Finset.mem_union, Finset.mem_filter] at hv
        simp only [Finset.mem_union]
        tauto)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dSC)
  have apartCS : Disjoint (C4 ∪ C6 ∪ C5 ∪ Csc) Ccs :=
    Finset.disjoint_of_subset_left (u := K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪
      SC pulled counted split)
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
  have inCounted : ∀ v ∈ K4 pulled counted V ∪ K6 pulled counted ∪ K5 counted V,
      v.toNat < counted.validators.data.size := by
    intro v hv
    simp only [Finset.mem_union] at hv
    rcases hv with (h4 | h6) | h5
    · obtain ⟨w, found, -⟩ := active_of_activeVoters h.early (Finset.mem_filter.mp h4).1
      exact (Array.getElem?_eq_some_iff.mp found).1
    · obtain ⟨w, found, -⟩ := active_of_activeVoters h.early (Finset.mem_filter.mp h6).1
      exact (Array.getElem?_eq_some_iff.mp found).1
    · have listed := (Finset.mem_filter.mp h5).1
      simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at listed
      rcases listed.1 with now | before
      · exact lt_size_of_mem_getActiveValidatorIndices now
      · exact lt_size_of_mem_getActiveValidatorIndices before
  have flagIn : ∀ v : ValidatorIndex, slashedFlagAt counted v.toNat = some true →
      v.toNat < counted.validators.data.size := by
    intro v flag
    simp only [slashedFlagAt, Option.map_eq_some_iff] at flag
    obtain ⟨w, found, -⟩ := flag
    exact (Array.getElem?_eq_some_iff.mp found).1
  have inSC : ∀ v ∈ SC pulled counted split, v.toNat < counted.validators.data.size :=
    fun v hv => flagIn v (Finset.mem_filter.mp hv).2.1
  have inCS : ∀ v ∈ CS pulled counted, v.toNat < counted.validators.data.size :=
    fun v hv => flagIn v (Finset.mem_filter.mp hv).2.2
  -- Those keys are credited keys of the run, which `credited_keys_le` counts by slots.
  have credited := credited_keys_le h tailC highC
  have fit : (C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs).card ≤
      ((Finset.range counted.validators.data.size).filter fun i =>
        0 < grossScan i highC tailC +
          (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC).1).card :=
    by
    refine Finset.card_le_card_of_injOn (fun v : ValidatorIndex => v.toNat) (fun v hv => ?_)
      (fun a _ b _ same => UInt64.toNat_inj.mp same)
    have member : v ∈ C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs := hv
    have classed : v ∈ K4 pulled counted V ∪ K6 pulled counted ∪ K5 counted V ∨
        v ∈ SC pulled counted split ∨ v ∈ CS pulled counted := by
      simp only [C4, C5, C6, Csc, Ccs, Finset.mem_union, Finset.mem_filter] at member ⊢
      tauto
    have flag : creditedKey tailC highC v = true := by
      simp only [C4, C5, C6, Csc, Ccs, Finset.mem_union, Finset.mem_filter] at member
      tauto
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, of_decide_eq_true flag⟩
    rcases classed with held | held | held
    · exact inCounted v held
    · exact inSC v held
    · exact inCS v held
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
  have nonneg := Nat.zero_le (((getCurrentEpoch pulled).toNat + 2 -
    anc.finalizedCheckpoint.epoch.toNat) / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
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

/-- The rounding slacks of a set of keys are the upward band for each credited key. -/
private theorem band_sum {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (S : Finset ValidatorIndex) :
    ∑ v ∈ S, bandC tail high v.toNat =
      preset.upwardBand * (S.filter fun v => creditedKey tail high v = true).card := by
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold bandC creditedKey
  by_cases credited : 0 < grossScan v.toNat high tail +
    (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat high tail).1 <;>
    simp [credited]

/-- The credits that a scan reads for a key are at most the credits of its source's events.

The sources of the scan, block and slot, are those that `p` selects. -/
private theorem scan_le_events (blockP slotP : BalanceSource → Bool) (p : BalanceSource → Prop)
    [DecidablePred p] (selects : ∀ s, (blockP s = true ∨ slotP s = true) ↔ p s)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high : ℕ)
    (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (creditScan blockP slotP v.toNat high tail).1 ≤
      ((events.filter fun e => p e.source).map (keyCredit v.toNat)).sum := by
  have scan := creditScan_sum_le {v} blockP slotP high (keyCredit v.toNat) tail replayed
    fun e _ _ => by simp
  simp only [Finset.sum_singleton] at scan
  refine scan.trans (le_of_eq ?_)
  simp only [selects]
  rw [List.sum_map_ite (fun e : BalanceEvent preset => p e.source) (keyCredit v.toNat)
    (fun _ => 0)]
  simp

/-- The credits of a key on C's branch are its proposer credits and deposits, up to consolidations.

The consolidations are those of the replayed events. -/
private theorem credit_parts_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    credC tail high v.toNat ≤ credN tail high v.toNat + consAmt events v.toNat ∧
    propC tail high v.toNat ≤ propN tail high v.toNat + consAmt events v.toNat := by
  have cons := scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp) tail high v
    replayed
  have c := credC_split tail high v.toNat
  have p := propC_split tail high v.toNat
  exact ⟨by unfold consAmt; omega, by unfold consAmt; omega⟩

/-- K5 (`exitingCredits` with `credits`): C's proposer credits to K5 keys, weight 3.

`bud_consolidations` charges the consolidation amounts, so they are added to the bound.

The `syncProposer` part of the bound is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `exitingCredits`.

The compounding of the credits, an exact tenth of the keys' total, is in the bound.

The two further bands of each credited K5 key are in `bud_exitingBands`. -/
theorem bud_exitingCredits (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * (2 * (∑ v ∈ (K5 counted V), propC tailC highC v.toNat)) +
      2 * (∑ v ∈ (K5 counted V), propN tailC highC v.toNat) +
        22 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).exitingCredits +
        20 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) := by
  -- The proposer credits fit the pin's per-epoch bound, and their consolidation part is `consAmt`.
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have rewards := proposer_rewards_le h (toFin.append fromFin) (.inl ⟨fromFin⟩) Run.nil rfl tailC
    highC (K5 counted V)
  rw [run_nil_append] at rewards
  have parts : ∑ v ∈ (K5 counted V), propC tailC highC v.toNat ≤
      ∑ v ∈ (K5 counted V), propN tailC highC v.toNat +
        ∑ v ∈ (K5 counted V), consAmt eventsC v.toNat := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => (credit_parts_le tailC highC v replayedC).2
  have exiting : (pinTerms config pulled anc fin).exitingCredits =
      (22 * ((pinTerms config pulled anc fin).depth *
        (pinTerms config pulled anc fin).proposerCredit) + 9) / 10 := rfl
  rw [exiting]
  omega

/-- `credits` holds the proposer credit, the deposit queue and the credited-key slots.

`queueDep` is the same queue, three times. -/
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

The keys slashed at C, `SC` and `CS`, count the deposits of events that do not hold them slashed.

The classes of C's quorum are apart from them. -/
private theorem deposits_union_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ K4 pulled counted V ∪ K6 pulled counted,
        (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC).1) +
      (∑ v ∈ SC pulled counted split ∪ CS pulled counted, depPre eventsC v.toNat)) ≤
      (pinTerms config pulled anc fin).queueDep := by
  have quorum : K4 pulled counted V ∪ K6 pulled counted ⊆
      K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted := fun v member => by
    simp only [Finset.mem_union] at member ⊢
    tauto
  refine deposits_active_le h tailC highC endEpochC replayedC _ _ ?_ (fun v member => ?_)
    fun v member => ?_
  · rw [Finset.disjoint_union_right]
    exact ⟨Finset.disjoint_of_subset_left quorum (sc_disjoint h).1,
      Finset.disjoint_of_subset_left (fun v m => Finset.mem_union_left _ (quorum m))
        (cs_disjoint h).1⟩
  · have countedActive : v ∈ AC counted := by
      rcases Finset.mem_union.mp member with m | m
      · exact (Finset.mem_filter.mp m).1
      · exact (Finset.mem_filter.mp m).1
    obtain ⟨w, found, active⟩ := active_of_activeVoters h.early countedActive
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
    exact ⟨w, found, active.2⟩
  · have flag : slashedFlagAt counted v.toNat = some true := by
      rcases Finset.mem_union.mp member with m | m
      · exact (Finset.mem_filter.mp m).2.1
      · exact (Finset.mem_filter.mp m).2.2
    simpa [slashedFlagAt, Option.map_eq_some_iff] using flag

/-- D-7 (credits) from the proposer rewards, the deposits and the credited keys of its classes.

The consolidation amounts are charged by `bud_consolidations`, and the sync part by `bud_sync`.

The deposits of a key slashed at C count only those before its slashing, in its share.

`rewards` is the proposer credits of the five classes and the sync part against `proposerCredit`.

`deposits` is the deposits of the classes against the deposit queue, at weight three.

`cards` is the credited keys of the classes against the credited-key slots. -/
private theorem bud_credits_of (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (rewards : (∑ v ∈ K4 pulled counted V, propN tailC highC v.toNat) +
      (∑ v ∈ K5 counted V, propN tailC highC v.toNat) +
      (∑ v ∈ K6 pulled counted, propN tailC highC v.toNat) +
      (∑ v ∈ SC pulled counted split, propN tailC highC v.toNat) +
      (∑ v ∈ CS pulled counted, propN tailC highC v.toNat) +
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer ≤
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit)
    (deposits : 3 * ((∑ v ∈ K4 pulled counted V ∪ K6 pulled counted,
        (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC).1) +
      (∑ v ∈ SC pulled counted split ∪ CS pulled counted, depPre eventsC v.toNat)) ≤
      (pinTerms config pulled anc fin).queueDep)
    (cards : ((K4 pulled counted V).filter fun v => creditedKey tailC highC v = true).card +
      ((K5 counted V).filter fun v => creditedKey tailC highC v = true).card +
      ((K6 pulled counted).filter fun v => creditedKey tailC highC v = true).card +
      ((SC pulled counted split).filter fun v => creditedKey tailC highC v = true).card +
      ((CS pulled counted).filter fun v => creditedKey tailC highC v = true).card ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) :
    10 * ((∑ v ∈ (K4 pulled counted V), credC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), credC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), propC tailC highC v.toNat) +
      (∑ v ∈ (K4 pulled counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), bandC tailC highC v.toNat) +
      wShare preset fork ((∑ v ∈ SC pulled counted split, propN tailC highC v.toNat) +
        ∑ v ∈ SC pulled counted split, depPre eventsC v.toNat) +
      (∑ v ∈ SC pulled counted split, bandC tailC highC v.toNat) +
      wShare preset fork ((∑ v ∈ CS pulled counted, propN tailC highC v.toNat) +
        ∑ v ∈ CS pulled counted, depPre eventsC v.toNat) +
      (∑ v ∈ CS pulled counted, bandC tailC highC v.toNat)) +
      ((∑ v ∈ (K4 pulled counted V), credN tailC highC v.toNat) +
        (∑ v ∈ (K6 pulled counted), credN tailC highC v.toNat) +
        (∑ v ∈ (K5 counted V), propN tailC highC v.toNat)) +
        11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        10 * ((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
          (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
          (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat)) := by
  classical
  obtain ⟨carry, churn, wb, ck, queue, credits, slots⟩ := credits_budget config pulled anc fin
  obtain ⟨d45, d46, d56, -, -, -⟩ := classes_disjoint h
  have dSCCS : Disjoint (SC pulled counted split) (CS pulled counted) :=
    Finset.disjoint_of_subset_left Finset.subset_union_right (cs_disjoint h).1
  have parts (S : Finset ValidatorIndex) := fun v (_ : v ∈ S) => credit_parts_le tailC highC v
    replayedC
  have sumLe (S : Finset ValidatorIndex) (f g : ValidatorIndex → ℕ)
      (le : ∀ v ∈ S, f v ≤ g v) : ∑ v ∈ S, f v ≤ ∑ v ∈ S, g v := Finset.sum_le_sum le
  have c4 := sumLe (K4 pulled counted V) _ (fun v => credN tailC highC v.toNat +
    consAmt eventsC v.toNat) fun v m => (parts _ v m).1
  have c6 := sumLe (K6 pulled counted) _ (fun v => credN tailC highC v.toNat +
    consAmt eventsC v.toNat) fun v m => (parts _ v m).1
  have c5 := sumLe (K5 counted V) _ (fun v => propN tailC highC v.toNat +
    consAmt eventsC v.toNat) fun v m => (parts _ v m).2
  simp only [Finset.sum_add_distrib] at c4 c6 c5
  have e4 : ∑ v ∈ K4 pulled counted V, credN tailC highC v.toNat =
      (∑ v ∈ K4 pulled counted V, propN tailC highC v.toNat) + ∑ v ∈ K4 pulled counted V,
        (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC).1 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => credN_split tailC highC v.toNat
  have e6 : ∑ v ∈ K6 pulled counted, credN tailC highC v.toNat =
      (∑ v ∈ K6 pulled counted, propN tailC highC v.toNat) + ∑ v ∈ K6 pulled counted,
        (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC).1 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => credN_split tailC highC v.toNat
  rw [Finset.sum_union d46, Finset.sum_union dSCCS] at deposits
  have w1 := wShare_le (fork := fork) h.facts ((∑ v ∈ SC pulled counted split,
    propN tailC highC v.toNat) + ∑ v ∈ SC pulled counted split, depPre eventsC v.toNat)
  have w2 := wShare_le (fork := fork) h.facts ((∑ v ∈ CS pulled counted,
    propN tailC highC v.toNat) + ∑ v ∈ CS pulled counted, depPre eventsC v.toNat)
  have bands : (∑ v ∈ K4 pulled counted V, bandC tailC highC v.toNat) +
      (∑ v ∈ K5 counted V, bandC tailC highC v.toNat) +
      (∑ v ∈ K6 pulled counted, bandC tailC highC v.toNat) +
      (∑ v ∈ SC pulled counted split, bandC tailC highC v.toNat) +
      (∑ v ∈ CS pulled counted, bandC tailC highC v.toNat) ≤ ck * preset.upwardBand := by
    simp only [band_sum, ← Nat.mul_add]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (cards.trans slots)
  omega

/-- D-7 (credits): C's non-attestation credits to keys counted once.

The consolidation amounts are not here either: `bud_consolidations` charges them.

The `syncProposer` part of `credits` is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `credits`.

The compounding of the credits, an exact tenth of the keys' total, is in the bound.

The rounding slacks of the credited keys of `K4` and `K5` are paid by `creditedKeys`. -/
theorem bud_credits (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * ((∑ v ∈ (K4 pulled counted V), credC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), credC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), propC tailC highC v.toNat) +
      (∑ v ∈ (K4 pulled counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), bandC tailC highC v.toNat) +
      wShare preset fork ((∑ v ∈ SC pulled counted split, propN tailC highC v.toNat) +
        ∑ v ∈ SC pulled counted split, depPre eventsC v.toNat) +
      (∑ v ∈ SC pulled counted split, bandC tailC highC v.toNat) +
      wShare preset fork ((∑ v ∈ CS pulled counted, propN tailC highC v.toNat) +
        ∑ v ∈ CS pulled counted, depPre eventsC v.toNat) +
      (∑ v ∈ CS pulled counted, bandC tailC highC v.toNat)) +
      ((∑ v ∈ (K4 pulled counted V), credN tailC highC v.toNat) +
        (∑ v ∈ (K6 pulled counted), credN tailC highC v.toNat) +
        (∑ v ∈ (K5 counted V), propN tailC highC v.toNat)) +
        11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        10 * ((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
          (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
          (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat)) :=
  bud_credits_of h tailC highC replayedC
    (by
      obtain ⟨d45, d46, d56, -, -, -⟩ := classes_disjoint h
      obtain ⟨toFin⟩ := h.toFin
      obtain ⟨fromFin⟩ := h.fromFin
      have := proposer_rewards_le h (toFin.append fromFin) (.inl ⟨fromFin⟩) Run.nil rfl tailC highC
        (K4 pulled counted V ∪ K5 counted V ∪
        K6 pulled counted ∪ SC pulled counted split ∪ CS pulled counted)
      rw [run_nil_append] at this
      rwa [Finset.sum_union (cs_disjoint h).1, Finset.sum_union (sc_disjoint h).1,
        Finset.sum_union (Finset.disjoint_union_left.mpr ⟨d46, d56⟩), Finset.sum_union d45]
        at this)
    (deposits_union_le h tailC highC endEpochC replayedC) (credited_classes_le h tailC highC)

/-- The keys of `K5` are at most the keys that R reads as exiting and the queue keys.

A key of `K5` is read as exiting at R, or has a departure charge on C's run. -/
private theorem card_K5_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (K5 counted V).card ≤ ((pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).exitingB i = true).card +
      (pinTerms config pulled anc fin).queueKeys := by
  classical
  set A := (K5 counted V).filter fun v =>
    (pinTerms config pulled anc fin).exitingB v.toNat = true
  set B := (K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat
  have cover : K5 counted V ⊆ A ∪ B := by
    intro v inK5
    by_cases exiting : (pinTerms config pulled anc fin).exitingB v.toNat = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inK5, exiting⟩)
    · have flag : (pinTerms config pulled anc fin).exitingB v.toNat = false := by
        simpa using exiting
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨inK5, K5_charged h tailC inK5 flag⟩)
  have exitingLe := card_exitingB_le config pulled anc fin A fun v hv =>
    (Finset.mem_filter.mp hv).2
  have chargedLe := charged_count h tailC
  exact (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add exitingLe chargedLe))

/-- The credited keys of `K4`, `K5` and `K6`, with `K5` at weight three, fit the credited-key slots.

The slots are the proposers, the seats and the deposit recipients of the window.

Two more are left for each key that R reads as exiting or that the queues let exit.

A credited key of `K6` beyond R's registry was created by a deposit on C's branch.

It uses a slot of the deposit recipients, as the other credited keys of the three classes do. -/
private theorem credit_slots_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    ((K4 pulled counted V).filter fun v => creditedKey tailC highC v = true).card +
      ((K6 pulled counted).filter fun v => creditedKey tailC highC v = true).card +
      3 * ((K5 counted V).filter fun v => creditedKey tailC highC v = true).card ≤
    (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
      ((pinTerms config pulled anc fin).depth /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
          preset.SYNC_COMMITTEE_SIZE.toNat +
      (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
      2 * ((((pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).exitingB i = true).card +
          (pinTerms config pulled anc fin).queueKeys)) := by
  classical
  have classes := credited_classes_le h tailC highC
  set C5 := (K5 counted V).filter fun v => creditedKey tailC highC v = true
  have fiveCount : C5.card ≤ ((pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).exitingB i = true).card +
      (pinTerms config pulled anc fin).queueKeys :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (card_K5_le h tailC)
  omega

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
  exact (sum_filter_or events (fun s => decide (s = .deposits))
    (fun s => decide (s = .consolidations)) apart f).le

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
      stepCredit (fun _ => false) (fun s => decide (s = .deposits)) v
        (Step.slot ok : Step config checks m n) +
      stepCredit (fun _ => false) (fun s => decide (s = .consolidations)) v
        (Step.slot ok : Step config checks m n) := by
  have altair : .altair ≤ m.fork := Nat.le_trans (by decide) electra
  obtain ⟨events, replayed⟩ := (Step.slot ok : Step config checks m n).balanceEvents_ok early
  have base := PinSplit2.step_balance_le (Step.slot ok : Step config checks m n) early v
  have rewards := PinSplit2.epochRewards_le (Step.slot ok : Step config checks m n) altair early v
    known 0 0 (.inl idle) (.inl idle)
  have rewardsZero : PinSplit2.epochRewards v (Step.slot ok : Step config checks m n) = 0 := by
    simpa using rewards
  have sources := step_credit_le_sources shared genesis (Step.slot ok : Step config checks m n)
    early electra v replayed
  have noSync := PinSplit5.slot_noSync electra ok early replayed
  have syncZero : (events.map (syncCredit v)).sum = 0 :=
    List.sum_eq_zero fun x member => by
      obtain ⟨e, mem, rfl⟩ := List.mem_map.mp member
      simp [syncCredit, noSync e mem]
  have split := sum_filter_cons_dep_le events (keyCredit v)
  simp only [stepCredit, stepNet, replayed, Except.toOption, Option.getD_some,
    syncZero] at base sources ⊢
  simp only [List.filter_false, List.map_nil, List.sum_nil] at sources
  omega

/-- A key that is idle along a prefix of C's run has a balance at most its credits there.

The key is two epochs from its activation at the end of the run.

It is absent at the start.

A block step credits it only through its net rise, which the scan counts.

A slot step credits it the credits of deposits and consolidations, since it is idle. -/
private theorem key_idle_walk (h : Setting config checks g split fin pulled anc counted V)
    {z : ForkedBeaconState preset} (v : ℕ) (small : v < 2 ^ 64) (highC : ℕ)
    (zEarly : z.fork < .glamsterdam)
    (zHigh : (getCurrentEpoch z.state).toNat ≤ highC + 1)
    (ahead : ∀ m : ForkedBeaconState preset, Run config checks m z → ∀ w : Validator,
      m.state.validators.data[v]? = some w → w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch m.state).toNat + 1 < w.activationEpoch.toNat)
    (start : actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v = 0) :
    ∀ {m : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ m),
      Run config checks m z → actualBalanceAt m v ≤ grossScan v highC pre +
        (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v highC pre).1 +
        (creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v highC pre).1 := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  intro m pre
  induction pre with
  | nil =>
    intro _
    rw [start]
    exact Nat.zero_le _
  | @snoc middle last pre step ih =>
    intro post
    have shared : Run config checks g middle := (toFin.append fromFin).append pre
    have afterStep : Run config checks middle z := (Run.nil.snoc step).append post
    have middleZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps afterStep.chainSteps)
    have middleFork := fork_le_of_chainSteps afterStep.chainSteps
    have lastFork := fork_le_of_chainSteps post.chainSteps
    have selected : (getCurrentEpoch middle.state).toNat ≤ highC + 1 := by omega
    rw [grossScan_snoc, creditScan_snoc_fst, creditScan_snoc_fst]
    simp only [selected, ↓reduceIte]
    have before := ih afterStep
    have lastEarly : last.fork < .glamsterdam := Nat.lt_of_le_of_lt lastFork zEarly
    cases step with
    | block engine signed due ok =>
      have gross := block_balance_le_gross (engine := engine) (signed := signed) (due := due)
        (ok := ok) shared h.genesis lastEarly
        (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) v
      omega
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
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActive
        have lowEpoch := UInt64.le_iff_toNat_le.mp isActive.1
        have highEpoch := UInt64.lt_iff_toNat_lt.mp isActive.2
        have previous := getPreviousEpoch_toNat middle.state
        have exitBound := w.exitEpoch.toNat_lt
        by_cases assigned : w.activationEpoch = FAR_FUTURE_EPOCH
        · rw [assigned] at lowEpoch
          have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
          omega
        · have := ahead middle afterStep w found assigned
          omega
      exact slot_idle_step shared h.genesis ok lastEarly middleElectra v known idle |>.trans
        (by omega)

/-- A key active at C and absent at the split holds the activation reserve at a state of C's run.

The run from the split reaches that state first, and then C.

The key is active at C and absent at the split.

At that state its balance is at least `MAX_EFFECTIVE_BALANCE`.

Its effective balance is within the downward band of its balance, and at least that.

The key is idle before that state, so its balance is at most the credits that the scans count. -/
private theorem created_start (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {v : ValidatorIndex} (member : v ∈ activeVoters counted)
    (absent : split.validators.data.size ≤ v.toNat) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks ⟨fork, split⟩ z)
      (post : Run config checks z ⟨fork, counted⟩), tailC = pre.append post ∧
      z.fork < .glamsterdam ∧ z.fork ≤ fork ∧
      (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch counted).toNat ∧
      v.toNat < z.state.validators.data.size ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z v.toNat ∧
      effectiveAt z v.toNat ≤ actualBalanceAt z v.toNat + preset.downwardBand ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ effectiveAt z v.toNat ∧
      actualBalanceAt z v.toNat ≤ grossScan v.toNat highC pre +
        (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC pre).1 +
        (creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v.toNat highC
          pre).1 := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- The key is active at C and absent at the split.
  obtain ⟨w, foundC, activeC⟩ := active_of_activeVoters h.early member
  have activeAt : isActiveAt counted (getCurrentEpoch counted) v.toNat = true :=
    isActiveAt_eq_true_iff.mpr ⟨w, foundC, activeC⟩
  have splitAbsent : split.validators.data[v.toNat]? = none :=
    Array.getElem?_eq_none absent
  have pending : ∀ u, (⟨fork, split⟩ : ForkedBeaconState preset).state.validators.data[v.toNat]? =
      some u → (getCurrentEpoch (⟨fork, split⟩ : ForkedBeaconState preset).state).toNat + 1 <
        u.activationEpoch.toNat := fun u found => by
    simp only [splitAbsent] at found
    cases found
  obtain ⟨z, pre, post, v0, vy, splitEq, found0, -, sameAct, actEq, actLe, exitGt⟩ :=
    PinSplit.Run.start_state tailC h.window v.toNat pending activeAt
  have farToNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have exitBound := vy.exitEpoch.toNat_lt
  have actBound := v0.activationEpoch.toNat_lt
  have actNeFar : v0.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro same
    rw [sameAct] at same
    have := congrArg UInt64.toNat same
    omega
  have zFork : z.fork ≤ fork := fork_le_of_chainSteps post.chainSteps
  have zEarly : z.fork < .glamsterdam := Nat.lt_of_le_of_lt zFork h.early
  have actZ : (getCurrentEpoch z.state).toNat + 2 = v0.activationEpoch.toNat := by
    rw [sameAct]
    exact actEq
  -- At that state the key holds the activation reserve, which is positive.
  obtain ⟨-, funded, hysteresis, reserve⟩ :=
    PinSplit.Run.funded_at_start shared h.genesis h.caps h.aligned electra pre zEarly v.toNat found0
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
  refine ⟨z, pre, post, splitEq, zEarly, zFork, zCounted,
    (Array.getElem?_eq_some_iff.mp found0).1, funded, hysteresis, reserve, ?_⟩
  exact key_idle_walk h v.toNat v.toNat_lt highC zEarly (by omega)
    (fun m run w found assigned => by
      obtain ⟨later, foundLater, life⟩ := run.registryLifecycle.validators v.toNat w found
      have same : later = v0 := Option.some.inj (foundLater.symm.trans found0)
      subst same
      have act := life.activationEpoch assigned
      have mZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps run.chainSteps)
      rw [← act]
      omega)
    startZero pre Run.nil

/-- A key of `K6` beyond R's registry was created on C's branch, and it is credited there.

A block step's net rise or a slot step's deposit credits it, or a consolidation pays it.

It is active at C, and its activation was assigned two epochs before it.

At that state it holds the activation reserve.

No step before it could give it that without such a credit. -/
private theorem created_credited (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (member : v ∈ K6 pulled counted)
    (created : pulled.validators.data.size ≤ v.toNat) :
    creditedKey tailC highC v = true ∨ 0 < consAmt eventsC v.toNat := by
  classical
  by_contra notCredited
  obtain ⟨notFlag, notCons⟩ := not_or.mp notCredited
  have consZero : consAmt eventsC v.toNat = 0 := Nat.eq_zero_of_not_pos notCons
  have scansZero : grossScan v.toNat highC tailC = 0 ∧
      (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC).1 =
        0 := by
    simp only [creditedKey, decide_eq_true_eq, not_lt, Nat.le_zero] at notFlag
    omega
  have consScan : (creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v.toNat
      highC tailC).1 ≤ consAmt eventsC v.toNat :=
    scan_le_events _ _ (· = .consolidations) (by intro s; simp) tailC highC v replayedC
  rw [consZero] at consScan
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  obtain ⟨z, pre, post, splitEq, -, -, -, -, funded, -, -, walk⟩ :=
    created_start h tailC highC endEpochC (Finset.mem_filter.mp member).1 (by omega)
  have positive : 0 < preset.MAX_EFFECTIVE_BALANCE.toNat := by
    have newKey := h.facts.newKey .fusaka
    have size := h.facts.incrementSize
    by_contra zero
    have none : preset.MAX_EFFECTIVE_BALANCE.toNat = 0 := by omega
    rw [none] at newKey
    simp only [Nat.mul_zero, Nat.zero_div, Nat.zero_sub, Nat.le_zero] at newKey
    omega
  subst splitEq
  rw [grossScan_append] at scansZero
  have depSplit := creditScan_append (fun _ => false) (fun s => decide (s = .deposits))
    v.toNat highC pre post
  have consSplit := creditScan_append (fun _ => false) (fun s => decide (s = .consolidations))
    v.toNat highC pre post
  omega

/-- The consolidation credits of a run after the shared segment fit the due entries.

The keys of a set are credited at most the caps of the due entries of X's queue that name them.

The run from X to the end is the shared segment and then the run from the split.

The horizon is within the withdrawal delay of X, as `shallow` says. -/
private theorem cons_due_bound (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {z : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, z⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch z).toNat ≤ high + 1)
    (highLe : high ≤ (getCurrentEpoch pulled).toNat)
    {events eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayed : tail.balanceEvents high = .ok events) (T : Finset ValidatorIndex) :
    ∑ v ∈ T, consAmt (eventsF ++ events) v.toNat ≤
      ((dueList fin (Nat.le_trans (by decide) h.fulu) high T).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
  classical
  have shallow := h.shallow
  obtain ⟨shared⟩ := h.toFin
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp h.called
  have bound := PinSplit.Run.consolidation_credits_le_X_targets (config := config)
    (checks := checks) shared h.genesis h.caps (fromFin.append tail)
    (Nat.le_trans (by decide) h.fulu) h.early high
    (Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed) endEpoch
    (by simp only; omega) (by omega) (T.image UInt64.toNat)
  have injective : Function.Injective UInt64.toNat := fun _ _ same => UInt64.toNat_inj.mp same
  simp only [injective.mem_finset_image] at bound
  rw [← Finset.sum_image (f := fun i => consAmt (eventsF ++ events) i)
    (fun _ _ _ _ e => UInt64.toNat_inj.mp e)]
  exact bound

/-- The keys that a consolidation of X's queue credits on C's run are at most its due entries.

Each such key is the target of a due entry, and each entry names one target. -/
private theorem cons_keys_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    {eventsF eventsC : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents highC = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) (T : Finset ValidatorIndex)
    (credited : ∀ v ∈ T, 0 < consAmt eventsC v.toNat) :
    T.card ≤ (pinTerms config pulled anc fin).consolidationsXCount := by
  classical
  have shallow := h.shallow
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have each (v : ValidatorIndex) (hv : v ∈ T) : 1 ≤ dueAt fin highC {v} := by
    have bound := cons_due_bound h fromFin tailC highC endEpochC highLe replayedF replayedC {v}
    rw [dueAt_eq fin electra highC]
    by_contra none
    have empty : dueList fin electra highC {v} = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [Finset.sum_singleton, empty, List.map_nil, List.sum_nil] at bound
    have positive := credited v hv
    unfold consAmt at positive bound
    simp only [List.filter_append, List.map_append, List.sum_append] at bound
    omega
  calc T.card = ∑ v ∈ T, 1 := by simp
    _ ≤ ∑ v ∈ T, dueAt fin highC {v} := Finset.sum_le_sum each
    _ = dueAt fin highC T := dueAt_sum fin electra highC T
    _ ≤ (dueList fin electra (getCurrentEpoch pulled).toNat T).length := by
      rw [dueAt_eq fin electra highC]
      exact dueList_length_mono fin electra highLe T
    _ ≤ _ := by
      unfold pinTerms
      dsimp only
      simp only [shallow, electra, ↓reduceIte, ↓reduceDIte]
      simpa using dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat T fun _ => 1

/-- `consolidationsX` is the sum of the caps of the sources in X's queue that are due.

It is zero beyond the withdrawal delay, so the setting's `shallow` selects the entries. -/
private theorem consolidationsX_eq (h : Setting config checks g split fin pulled anc counted V)
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

/-- The caps are whole increments, so `consolidationsX` is too. -/
private theorem consolidationsX_aligned
    (h : Setting config checks g split fin pulled anc counted V) :
    (pinTerms config pulled anc fin).consolidationsX % preset.EFFECTIVE_BALANCE_INCREMENT.toNat =
      0 := by
  rw [consolidationsX_eq h (Nat.le_trans (by decide) h.fulu)]
  apply Nat.mod_eq_zero_of_dvd
  refine List.dvd_sum fun x hx => ?_
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  have := congrArg UInt64.toNat (withdrawalMaxEffectiveBalance_aligned (fork := fork) h.aligned v)
  exact Nat.dvd_of_mod_eq_zero (by simpa [UInt64.toNat_mod] using this)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key with no due consolidation entry takes no consolidation credit on C's run.

The horizon of the due entries is cut to R's epoch, which C's replay does not read. -/
private theorem consAmt_zero (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (none : dueAt fin highC {v} = 0) : consAmt eventsC v.toNat = 0 := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have near := h.near
  have called := UInt64.le_iff_toNat_le.mp h.called
  have later := UInt64.le_iff_toNat_le.mp h.later
  obtain ⟨hc, hhc⟩ : ∃ hc, hc = min highC (getCurrentEpoch pulled).toNat := ⟨_, rfl⟩
  rw [balanceEvents_eq_of_endpoint_le fromFin (localHigh := hc) (by simp only; omega)
    (by simp only; omega)] at replayedF
  rw [balanceEvents_eq_of_endpoint_le tailC (localHigh := hc) (by simp only; omega)
    (by simp only; omega)] at replayedC
  have bound := cons_due_bound h fromFin tailC hc (by omega) (by omega) replayedF replayedC {v}
  have empty : dueList fin electra hc {v} = [] := List.length_eq_zero_iff.mp (by
    have := dueList_length_mono fin electra (show hc ≤ highC by omega) {v}
    rw [dueAt_eq fin electra highC] at none
    omega)
  simp only [Finset.sum_singleton, empty, List.map_nil, List.sum_nil] at bound
  unfold consAmt at bound ⊢
  simp only [List.filter_append, List.map_append, List.sum_append] at bound
  omega

/-- The consolidation credits of C's branch, charged to `consolidationsX` (the S9 ruling).

The run from the finalized block's state X to C's state has the run from the split as its tail.

`Run.consolidation_credits_le_X_targets` bounds the credits to a set of targets by the caps at X of
the due entries of X's queue that name them, over the whole run from X.

The run to R's state bounds the credits to V the same way.

The sets `V`, `K4`, `K5` and `K6` are disjoint, so the sum over their union is at most the caps of X's
queue: `consolidationsX`, as `high ≤` the epoch of the call and X is within the withdrawal delay.

The keys of `SC` are slashed at C, so they are not in `K4`, `K5`, `K6` or `V`.

Their credits join those of `K4`, `K5` and `K6` in the bound.

The keys of `CS` are created after R's registry and slashed at C.

So they are in none of those sets either.

Their credits join the bound with the same share and bands.

A whistleblower's share of the amounts of `SC` and `CS` is at most the amounts.

A due entry that names one of them adds its band.

A key of `V` or `K5` weighs three, and the others one.

Each applied entry also adds one upward band to its target's rise, so the left side has `upwardBand`
for each due entry of X's queue.

An entry is charged its cap at X, which is at least `MAX_EFFECTIVE_BALANCE`, so three bands are at
most three tenths of it.

The bound `3.3 · X ≤ (33 · X + 9) / 10` is the charge of `consolidationsX` in `pinReserve`.

Deeper than the withdrawal delay `consolidationsX` is 0, so the setting's `shallow` is used here. -/
private theorem bud_consolidations_base
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (band : 10 * preset.upwardBand ≤ preset.MAX_EFFECTIVE_BALANCE.toNat) :
    (((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
      (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, consAmt events v.toNat) +
      wShare preset fork (∑ v ∈ SC pulled counted split, consAmt eventsC v.toNat) +
      (∑ v ∈ SC pulled counted split, bandX fin highC v.toNat) +
      wShare preset fork (∑ v ∈ CS pulled counted, consAmt eventsC v.toNat) +
      (∑ v ∈ CS pulled counted, bandX fin highC v.toNat) +
      wShare preset fork (∑ v ∈ SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
          consAmt eventsF v.toNat) +
      (∑ v ∈ SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, bandX fin high v.toNat)) +
      preset.upwardBand * (dueAt fin highC (K4 pulled counted V) +
        dueAt fin highC (K6 pulled counted) + 3 * dueAt fin highC (K5 counted V) +
        3 * dueAt fin high V) ≤
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10) ∧
      (∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
        (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
        3 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
  classical
  have shallow := h.shallow
  have early := h.early
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp h.called
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
      K = K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪ SC pulled counted split ∪
        CS pulled counted := ⟨_, rfl⟩
  have boundC := cons_due_bound h fromFin tailC highC endEpochC highLe replayedFin replayedC Kall
  have boundR := cons_due_bound h fromFin tail high endEpoch highLeR replayedF replayed V
  -- The shared segment's amounts of the keys of `SC` that exited before the finalized epoch.
  set S' := (SC pulled counted split).filter fun v =>
    (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true with hS'
  have subS : S' ⊆ Kall := fun v hv => by
    rw [hKall]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mp hv).1)
  have amountC : (∑ v ∈ Kall, consAmt eventsC v.toNat) + (∑ v ∈ S', consAmt eventsFin v.toNat) ≤
      ((dueList fin electra highC Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    have into : ∑ v ∈ S', consAmt eventsFin v.toNat =
        ∑ v ∈ Kall, if v ∈ S' then consAmt eventsFin v.toNat else 0 := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr subS]
    rw [into, ← Finset.sum_add_distrib]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundC
    simp only [consAmt, List.filter_append, List.map_append, List.sum_append]
    split_ifs <;> omega
  have amountR : (∑ v ∈ V, consAmt events v.toNat) ≤
      ((dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundR
    simp only [consAmt, List.filter_append, List.map_append, List.sum_append]
    exact Nat.le_add_left _ _
  -- The target sets are disjoint.
  obtain ⟨d45, d46, d56, -, -, -⟩ := classes_disjoint h
  have d456 : Disjoint (K4 pulled counted V ∪ K5 counted V) (K6 pulled counted) :=
    Finset.disjoint_union_left.mpr ⟨d46, d56⟩
  obtain ⟨dS, dVS⟩ := sc_disjoint h
  obtain ⟨dC, dVC⟩ := cs_disjoint h
  have dKV : Disjoint Kall V := by
    rw [hKall, Finset.disjoint_left]
    intro v hk hv
    simp only [Finset.mem_union] at hk
    rcases hk with (((h4 | h5) | h6) | hS) | hC
    · simp only [K4, Finset.mem_filter] at h4
      exact h4.2.2.2 hv
    · simp only [K5, Finset.mem_filter] at h5
      exact h5.2.2 hv
    · simp only [K6, Finset.mem_filter] at h6
      exact h6.2.2 (h.voting v hv).1
    · exact Finset.disjoint_left.mp dVS hv hS
    · exact Finset.disjoint_left.mp dVC hv hC
  -- The amounts and the entries split over the three sets of C's keys.
  have splitAmount : (∑ v ∈ Kall, consAmt eventsC v.toNat) =
      (∑ v ∈ K4 pulled counted V, consAmt eventsC v.toNat) +
        (∑ v ∈ K5 counted V, consAmt eventsC v.toNat) +
        (∑ v ∈ K6 pulled counted, consAmt eventsC v.toNat) +
        (∑ v ∈ SC pulled counted split, consAmt eventsC v.toNat) +
        (∑ v ∈ CS pulled counted, consAmt eventsC v.toNat) := by
    rw [hKall, Finset.sum_union dC, Finset.sum_union dS, Finset.sum_union d456,
      Finset.sum_union d45]
  have splitEntries (H : ℕ) : (dueList fin electra H Kall).length =
      (dueList fin electra H (K4 pulled counted V)).length +
        (dueList fin electra H (K5 counted V)).length +
        (dueList fin electra H (K6 pulled counted)).length +
        (dueList fin electra H (SC pulled counted split)).length +
        (dueList fin electra H (CS pulled counted)).length := by
    rw [hKall, dueList_length_union fin electra H dC, dueList_length_union fin electra H dS,
      dueList_length_union fin electra H d456, dueList_length_union fin electra H d45]
  -- The caps of the due entries are at least `MAX_EFFECTIVE_BALANCE` each.
  have floorOf (l : List Validator) : preset.MAX_EFFECTIVE_BALANCE.toNat * l.length ≤
      (l.map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    have := List.length_nsmul_le_sum
      (l.map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
      preset.MAX_EFFECTIVE_BALANCE.toNat (by
        simp only [List.mem_map]
        rintro _ ⟨v, -, rfl⟩
        exact UInt64.le_iff_toNat_le.mp
          (Internal.minimum_cap h.caps.activation h.caps.compounding v))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have floorC := floorOf (dueList fin electra (getCurrentEpoch pulled).toNat Kall)
  have floorR := floorOf (dueList fin electra high V)
  -- Both runs charge entries of X's queue, at most those that `consolidationsX` counts.
  have total : ((dueList fin electra (getCurrentEpoch pulled).toNat Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum +
      ((dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum ≤
      (pinTerms config pulled anc fin).consolidationsX := by
    have hcX := consolidationsX_eq h electra
    have laterR := dueList_sum_mono fin electra highLeR V
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have union := dueList_sum_union fin electra (getCurrentEpoch pulled).toNat dKV
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have all := dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat (Kall ∪ V)
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    rw [hcX]
    omega
  have laterC := dueList_sum_mono fin electra highLe Kall
    (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
  -- Whole, the due caps of C's keys fit `consolidationsX`, so the weighted amounts fit three of it.
  have whole : (∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
      (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
    omega
  refine ⟨?_, whole⟩
  have bandLen : (dueList fin electra highC (SC pulled counted split)).length +
      (dueList fin electra highC (CS pulled counted)).length +
      (dueList fin electra highC (K4 pulled counted V)).length +
      (dueList fin electra highC (K6 pulled counted)).length +
      3 * (dueList fin electra highC (K5 counted V)).length +
      (dueList fin electra high S').length ≤
        3 * (dueList fin electra (getCurrentEpoch pulled).toNat Kall).length := by
    have union := splitEntries (getCurrentEpoch pulled).toNat
    have m4 := dueList_length_mono fin electra highLe (K4 pulled counted V)
    have m5 := dueList_length_mono fin electra highLe (K5 counted V)
    have m6 := dueList_length_mono fin electra highLe (K6 pulled counted)
    have mS := dueList_length_mono fin electra highLe (SC pulled counted split)
    have mC := dueList_length_mono fin electra highLe (CS pulled counted)
    have mF := (dueList_length_mono fin electra highLeR S').trans
      (dueList_length_subset fin electra (getCurrentEpoch pulled).toNat
        (Finset.filter_subset _ _ : S' ⊆ SC pulled counted split))
    omega
  have shareF := wShare_le (fork := fork) h.facts (∑ v ∈ S', consAmt eventsFin v.toNat)
  have shareS := wShare_le (fork := fork) h.facts
    (∑ v ∈ SC pulled counted split, consAmt eventsC v.toNat)
  have shareC := wShare_le (fork := fork) h.facts
    (∑ v ∈ CS pulled counted, consAmt eventsC v.toNat)
  rw [bandX_sum fin electra highC (SC pulled counted split),
    bandX_sum fin electra highC (CS pulled counted), bandX_sum fin electra high S']
  rw [dueAt_eq fin electra highC, dueAt_eq fin electra highC, dueAt_eq fin electra highC,
    dueAt_eq fin electra highC, dueAt_eq fin electra highC, dueAt_eq fin electra high,
    dueAt_eq fin electra high]
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  generalize (dueList fin electra highC (K4 pulled counted V)).length = d4 at *
  generalize (dueList fin electra highC (K5 counted V)).length = d5 at *
  generalize (dueList fin electra highC (K6 pulled counted)).length = d6 at *
  generalize (dueList fin electra highC (SC pulled counted split)).length = dS' at *
  generalize (dueList fin electra highC (CS pulled counted)).length = dC' at *
  generalize (∑ v ∈ SC pulled counted split, consAmt eventsC v.toNat) = aS at *
  generalize wShare preset fork aS = wS at *
  generalize (∑ v ∈ CS pulled counted, consAmt eventsC v.toNat) = aC at *
  generalize wShare preset fork aC = wC at *
  generalize (dueList fin electra high S').length = dF at *
  generalize (∑ v ∈ S', consAmt eventsFin v.toNat) = aF at *
  generalize wShare preset fork aF = wF at *
  generalize (dueList fin electra (getCurrentEpoch pulled).toNat Kall).length = dK at *
  generalize (dueList fin electra high V).length = dV at *
  generalize ((dueList fin electra highC Kall).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PK' at *
  generalize ((dueList fin electra (getCurrentEpoch pulled).toNat Kall).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PK at *
  generalize ((dueList fin electra high V).map fun v =>
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
      _ ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * (dK + dV) := Nat.mul_le_mul_right _ band
      _ = preset.MAX_EFFECTIVE_BALANCE.toNat * dK + preset.MAX_EFFECTIVE_BALANCE.toNat * dV :=
        Nat.mul_add _ _ _
  omega

/-- The consolidation credits of the third window, with the shares of `CS` and the shared segment.

The shared segment's shares are those of the keys of `SC` that exited before the finalized epoch. -/
theorem bud_consolidations (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (band : 10 * preset.upwardBand ≤ preset.MAX_EFFECTIVE_BALANCE.toNat) :
    ((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
      (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, consAmt events v.toNat) +
      wShare preset fork (∑ v ∈ SC pulled counted split, consAmt eventsC v.toNat) +
      (∑ v ∈ SC pulled counted split, bandX fin highC v.toNat) +
      wShare preset fork (∑ v ∈ CS pulled counted, consAmt eventsC v.toNat) +
      (∑ v ∈ CS pulled counted, bandX fin highC v.toNat) +
      wShare preset fork (∑ v ∈ SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
          consAmt eventsF v.toNat) +
      (∑ v ∈ SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, bandX fin high v.toNat)) +
      preset.upwardBand * (dueAt fin highC (K4 pulled counted V) +
        dueAt fin highC (K6 pulled counted) + 3 * dueAt fin highC (K5 counted V) +
        3 * dueAt fin high V) ≤
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10 := by
  exact (bud_consolidations_base h fromFin tail high endEpoch replayed replayedF highLeR tailC highC
    endEpochC replayedC highLe band).1

/-- L10: the keys whose exit started on R's branch after the split, in `K6`. -/
theorem bud_exitedR :
    (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitedRB v.toNat = true,
      (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤
        (pinTerms config pulled anc fin).exitedR := by
  rw [exitedR_eq]
  refine sum_toNat_le (fun i => balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
    fun v hv => ?_
  have flag := (Finset.mem_filter.mp hv).2
  obtain ⟨w, found⟩ := validator_of_flag (state := pulled) (i := v.toNat) (Or.inl flag)
  exact mem_positions_filter config pulled anc fin found flag

/-- Three sets with disjoint keys: the weights one, three and one are at most three. -/
private theorem weighted_le {A B C : Finset ValidatorIndex} (f : ValidatorIndex → ℕ)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C) :
    ∑ v ∈ A, f v + 3 * ∑ v ∈ B, f v + ∑ v ∈ C, f v ≤ 3 * ∑ v ∈ A ∪ B ∪ C, f v := by
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨ac, bc⟩), Finset.sum_union ab]
  omega

/-- `slashedRB` reads the slashed flag and the withdrawable epoch of the key's record. -/
private theorem slashedRB_eq (config : Config)
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
  rw [slashedRB_eq] at h
  simp [none] at h

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The exit of a counted voter of the finalized registry is late at R.

The voter is not active at `counted` since an exit before the finalized epoch is excluded.

Its exit at R is then at least the finalized epoch, so it is late for the whole run. -/
private theorem voter_late (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (v : ValidatorIndex) (voter : v ∈ Q counted) :
    ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  classical
  intro wP foundP
  obtain ⟨tailC⟩ := h.toCounted
  have calledNat := UInt64.le_iff_toNat_le.mp h.called
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  have inQ := voter
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inQ
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
  have short := window_short h
  by_cases exitedFin : wP.exitEpoch.toNat < (getCurrentEpoch fin).toNat
  · exfalso
    obtain ⟨uF', foundF', sameExit⟩ := exit_kept_of_le_fin h foundP (Nat.le_of_lt exitedFin)
    have exitNat : uF'.exitEpoch.toNat = wP.exitEpoch.toNat := congrArg UInt64.toNat sameExit
    have assigned : uF'.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      have far1 := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
      have far2 := congrArg UInt64.toNat far
      omega
    have previous := getPreviousEpoch_toNat counted
    have idle : ∀ e : Epoch, uF'.exitEpoch ≤ e → isActiveValidator uC e = false :=
      fun e reached => by
        have inactive := inactive_from_exit (fromFin.append tailC) foundF' assigned reached
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

`voter_late` gives the same for a counted voter. -/
private theorem late_of_exitAfterFin (h : Setting config checks g split fin pulled anc counted V)
    (i : ℕ) (exitAfterFin : ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch fin).toNat ≤ w.exitEpoch.toNat) :
    ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  intro w found
  have after := exitAfterFin w found
  have short := window_short h
  omega

/-- A counted voter is unslashed at the split.

It is unslashed at `counted`, and a slashing stays. -/
private theorem voter_unslashed (h : Setting config checks g split fin pulled anc counted V)
    (v : ValidatorIndex) (voter : v ∈ Q counted) :
    (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false := by
  classical
  obtain ⟨tailC⟩ := h.toCounted
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  have inQ := voter
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inQ
  obtain ⟨listed, unslashedC⟩ := inQ
  obtain ⟨uC, foundC⟩ : ∃ uC, counted.validators.data[v.toNat]? = some uC := by
    rcases listed with now | before
    · obtain ⟨u, foundU, -⟩ := (mem_getActiveValidatorIndices within).mp now
      exact ⟨u, foundU⟩
    · obtain ⟨u, foundU, -⟩ := (mem_getActiveValidatorIndices within).mp before
      exact ⟨u, foundU⟩
  have cleanC : uC.slashed = false := by simpa [foundC] using unslashedC
  cases foundS : split.validators.data[v.toNat]? with
  | none => rfl
  | some uS =>
    simp [unslashed_of_run tailC foundS (fun u read => by
      rw [foundC] at read
      cases read
      exact cleanC)]

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The floor of a key unslashed at the split at each state of R's run from a state `c`.

The run from `c` is the rest of the run from the finalized state to the split, then the run to R.

The floor starts from the smaller of the voter's balance there and its cap there.

The cap there is the cap at R if it is frozen, and less if the voter switches to compounding on R.

It is R's balance, the debits of the rest of R's run, and the slack of a slashing on R.

A voter unslashed at R takes it from `key_floorR_from`.

A voter slashed at R takes it from `slashed_floor`, with the slack that `slashW` holds.

The key is unslashed at the split, so at `c`.

A key slashed on R was slashed after the split.

The pin counts it, so `slashW` holds the slack.

The exit of the key at R is late for the whole run.

`voter_late` and `late_of_exitAfterFin` give that for a finalized key. -/
private theorem voter_floorAt (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (v : ValidatorIndex)
    (unslashed : (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false)
    {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : v.toNat < c.validators.data.size)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
    (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append rest = fromC.append tail →
    ∀ {evs : List (BalanceEvent preset)},
    rest.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs →
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinSplit2.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (evs.map (penaltyDebit v.toNat)).sum + (evs.map (syncDebit v.toNat)).sum +
        (evs.map (floorPartialDebit v)).sum +
          slashW (pinTerms config pulled anc fin) v.toNat := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have calledNat := UInt64.le_iff_toNat_le.mp h.called
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  -- the key's records at the four states
  have sizeC := registryGrows_of_chainSteps fromC.chainSteps
  have sizeSplit := registryGrows_of_chainSteps toPulled.chainSteps
  obtain ⟨uB, foundB⟩ : ∃ uB, c.validators.data[v.toNat]? = some uB :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨uS, foundS⟩ : ∃ uS, split.validators.data[v.toNat]? = some uS :=
    ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside sizeC)⟩
  obtain ⟨wP, foundP⟩ : ∃ wP, pulled.validators.data[v.toNat]? = some wP :=
    ⟨_, Array.getElem?_eq_getElem
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le inside sizeC) sizeSplit)⟩
  -- a record that is unslashed is the unslashed record at its index
  have only : ∀ {s : BeaconState preset fork} {u : Validator},
      s.validators.data[v.toNat]? = some u → u.slashed = false →
      ∀ w, s.validators.data[v.toNat]? = some w → w.slashed = false :=
    fun fu cu w fw => by
      rw [fu] at fw
      cases fw
      exact cu
  have cleanS : uS.slashed = false := by simpa [foundS] using unslashed
  have cleanB : uB.slashed = false := unslashed_of_run fromC foundB (only foundS cleanS)
  have finC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toC.chainSteps)
  have lateP := late wP foundP
  intro zs pre rest cut' evs ev
  have cut : (toC.append pre).append rest = fromFin.append tail := by
    rw [← Run.append_assoc, cut', Run.append_assoc, cutC]
  obtain ⟨val, foundZ⟩ : ∃ val, zs.validators.data[v.toNat]? = some val :=
    ⟨_, Array.getElem?_eq_getElem
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps))⟩
  -- the cap of the voter at the state is the cap that the floor reads
  have atZ : PinSplit2.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat =
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    simp [PinSplit2.capAt, foundZ]
  have retainedZ : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, zs⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pulled⟩),
      (before.snoc step).append after = rest → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) :=
    fun before step after cutB w foundW =>
      retained_of_exit h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_refl _) v foundP lateP
        ((toC.append pre).append before) step after
        (by
          rw [← cut, ← cutB]
          exact (Run.append_assoc (toC.append pre) (before.snoc step) after).symm)
        w foundW
  by_cases slashedP : wP.slashed = true
  · -- slashed on R after the split: the pin counts it, and `slashW` holds its slack
    have newly := (tail.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding
      h.early h.delay v.toNat uS wP foundS foundP cleanS slashedP).2
    have newly' : (getCurrentEpoch split).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        wP.withdrawableEpoch.toNat := newly
    have finalizedNat := UInt64.le_iff_toNat_le.mp h.finalized
    have rb : (pinTerms config pulled anc fin).slashedRB v.toNat = true := by
      rw [slashedRB_eq]
      have key : anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          wP.withdrawableEpoch.toNat := by omega
      simpa [foundP, slashedP] using key
    have topDiv : PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
        slashW (pinTerms config pulled anc fin) v.toNat := by
      have hW : slashW (pinTerms config pulled anc fin) v.toNat =
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
        simp [slashW, rb]
      rw [hW, parameters_of_fusaka h.fulu h.early]
      exact Nat.div_le_div_right (capAt_le_capMax h.caps electra v.toNat)
    have floor := slashed_floor h (toC.append pre) (e := pulled) (Nat.le_succ _) rest
      (getCurrentEpoch pulled).toNat (Nat.le_succ _) ev v val foundZ
      (fun flag => by
        have newly := (pre.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding
          h.early h.delay v.toNat uB val foundB foundZ cleanB flag).2
        simp only at finC newly
        omega)
      (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (fun z member => by
        obtain ⟨q1, q2, -⟩ := balancePath_endpoint rest
          (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) member
        obtain ⟨zf, zs'⟩ := z
        have same : fork = zf := (fork_eq_of_run q1 q2 (Nat.le_refl _)).symm
        subst same
        exact effective_le_cap_pulled h ((toC.append pre).append q1) q2 v.toNat)
      retainedZ
    rw [atZ]
    omega
  · have cleanP : wP.slashed = false := by simpa using slashedP
    have cleanZ : val.slashed = false := unslashed_of_run rest foundZ (only foundP cleanP)
    have floor := key_floorR_from h (toC.append pre) rest (getCurrentEpoch pulled).toNat
      (Nat.le_succ _) ev v
      val foundZ cleanZ
      (fun w fw => by
        rw [← Option.some.inj (foundP.symm.trans fw)]
        exact cleanP)
      retainedZ
    rw [atZ]
    omega

/-- The effective balance of a key at the finalized state is at most `ebUp`. -/
private theorem effective_fin_le_ebUp (h : Setting config checks g split fin pulled anc counted V)
    (i : ℕ) :
    effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i ≤
      (pinTerms config pulled anc fin).ebUp i := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  rw [ebUp_eq config pulled anc fin electra i _ rfl]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key unslashed at the split at each state of R's run from a state `c`.

The run from `c` is the rest of the run from the finalized state to the split, then the run to R.

It is within `ebUp` and a few increments, if it is within `ebUp` at `c`.

The increments are the whole ones of its sync debits and its slashing slack.

The floor of each state of that run is `voter_floorAt`.

`prefix_envelope` turns it into the bound on the effective balance. -/
private theorem envelope_of_voter (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (unslashed : (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false)
    {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : v.toNat < c.validators.data.size)
    (start : effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ z ∈ (fromC.append tail).balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          ((syncD eventsF v.toNat + syncD events v.toNat +
              slashW (pinTerms config pulled anc fin) v.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  exact prefix_envelope h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _) replayedF
    replayed v toC fromC cutC inside (slashW (pinTerms config pulled anc fin) v.toNat) start
    (voter_floorAt h fromFin tail v unslashed toC fromC cutC inside late)

/-- The keys of a set that the pin counts as slashed on this branch are at most `slashedR`. -/
private theorem slashedRB_card_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (W : Finset ValidatorIndex) :
    (W.filter fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat =
      true).card ≤ (pinTerms config state ancestor finalizedState).slashedR := by
  classical
  rw [slashedR_eq]
  refine Finset.card_le_card_of_injOn UInt64.toNat (fun v member => ?_)
    (fun a _ b _ same => UInt64.toNat_inj.mp same)
  obtain ⟨_, flag⟩ := Finset.mem_filter.mp member
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (slashedRB_lt config state ancestor
    finalizedState flag), flag⟩

/-- The keys slashed on this branch after the finalized epoch cost one increment each, once. -/
private theorem slashR_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    (W : Finset ValidatorIndex) :
    ∑ v ∈ W, slashR (pinTerms config state ancestor finalizedState) v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config state ancestor finalizedState).slashedR := by
  classical
  have sum : ∑ v ∈ W, slashR (pinTerms config state ancestor finalizedState) v.toNat =
      ∑ v ∈ W.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
        = true), preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [Finset.sum_filter]
    rfl
  rw [sum, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (slashedRB_card_le config state ancestor finalizedState W)

/-- A key that exited by the epoch of a run's start is inactive at the end of the run.

The run keeps an assigned exit epoch, and the epoch of its end is not before that of its start. -/
private theorem inactive_of_exited (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
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
  exact inactive_from_exit tail found assigned
    (UInt64.le_iff_toNat_le.mpr (Nat.le_trans exited forward))

/-- No block of a run from the finalized state has as proposer a key that exited by that state.

The key's exit is already assigned at the finalized state, so it is inactive on the whole run.

A proposer is active, which the lookahead of the run gives. -/
private theorem exited_not_proposer (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)
    (u : ForkedBeaconState preset) (run : Run config checks ⟨fork, fin⟩ u) (p : ValidatorIndex) :
    u.fork < .glamsterdam → getBeaconProposerIndex u.state = .ok p → p.toNat ≠ i := by
  intro early proposer same
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨w0, foundFin, kept⟩ := exit_kept_of_le_fin h foundPulled exited
  have inactive := inactive_of_exited h.twoSlots run foundFin (by rw [kept]; exact exited)
  have look := Run.lookaheadActive h.facts.covers h.genesis (toFin.append run) early
  have active := look.proposer_active
    (Nat.le_trans h.fulu (fork_le_of_chainSteps run.chainSteps)) proposer
  rw [same, inactive] at active
  exact Bool.false_ne_true active

/-- A key with a sync credit over the events of the shared segment has a gross credit on C's run.

The run is the shared segment followed by C's tail. -/
private theorem syncCr_gross_shared (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (v : ℕ) (positive : 0 < syncCr eventsF v) :
    0 < grossScan v high (fromFin.append tailC) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨-, sync⟩ := creditScan_bounds ∅
    (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) high
    (fun _ => 0) fromFin replayedF (fun e _ _ => by simp)
  have bound := sync (by simp) electra h.early
    (fun ok _ fork early replayed i => (PinSplit5.slot_syncDebit_zero fork ok early replayed i).2) v
  have split := creditScan_append (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync))
    (fun _ => false) v high fromFin tailC
  unfold grossScan
  unfold syncCr at positive
  omega

/-- The rounding bands of a set of keys are the band for each key with a sync debit. -/
private theorem sum_bandR (events : List (BalanceEvent preset)) (T : Finset ValidatorIndex) :
    ∑ v ∈ T, bandR events v.toNat =
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
        (T.filter fun v => 0 < (events.map (syncDebit v.toNat)).sum).card := by
  classical
  simp only [bandR_eq]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- The rounding bands of the classes of keys fit the seats of the committees of the periods.

The keys of `V` are on C's run, and those of `K4`, `K5` and `K6` are on R's run.

The keys of `V` weigh three, as do those of `K5`, and the others weigh one.

Each key that has a band holds a seat, and the seats of the two runs are counted together. -/
private theorem bands_seats (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high : ℕ)
    {events eventsF eventsC : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents high = .ok eventsC) :
    3 * (∑ v ∈ V, bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ K4 pulled counted V, bandR (eventsF ++ events) v.toNat) +
        3 * (∑ v ∈ K5 counted V, bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ K6 pulled counted, bandR (eventsF ++ events) v.toNat) ≤
      3 * ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
        (preset.SYNC_COMMITTEE_SIZE.toNat *
          (((getCurrentEpoch pulled).toNat + 1) /
              max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
          ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat))) := by
  classical
  obtain ⟨d45, d46, d56, d4v, d5v, d6v⟩ := classes_disjoint h
  rw [sum_bandR, sum_bandR, sum_bandR, sum_bandR]
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 = β
  generalize hSeats : preset.SYNC_COMMITTEE_SIZE.toNat *
    (((getCurrentEpoch pulled).toNat + 1) / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
    ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) = seats
  set fV := V.filter fun v => 0 < ((eventsF ++ eventsC).map (syncDebit v.toNat)).sum with hfV
  set f4 := (K4 pulled counted V).filter fun v =>
    0 < ((eventsF ++ events).map (syncDebit v.toNat)).sum with hf4
  set f5 := (K5 counted V).filter fun v =>
    0 < ((eventsF ++ events).map (syncDebit v.toNat)).sum with hf5
  set f6 := (K6 pulled counted).filter fun v =>
    0 < ((eventsF ++ events).map (syncDebit v.toNat)).sum with hf6
  have d45' : Disjoint f4 f5 := d45.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d46' : Disjoint f4 f6 := d46.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d56' : Disjoint f5 f6 := d56.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d4f : Disjoint fV f4 := d4v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d5f : Disjoint fV f5 := d5v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d6f : Disjoint fV f6 := d6v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have inj : Function.Injective fun v : ValidatorIndex => v.toNat := fun a b same =>
    UInt64.toNat_inj.mp same
  -- A key debited on the shared segment is debited on C's run, and any other on R's tail.
  have union := seat_union_card h fromFin tail tailC high replayed replayedF replayedC
    (((fV ∪ (f4 ∪ f5 ∪ f6)).filter fun v =>
      0 < ((eventsF ++ eventsC).map (syncDebit v.toNat)).sum).image fun v => v.toNat)
    (((fV ∪ (f4 ∪ f5 ∪ f6)).filter fun v =>
      0 < (events.map (syncDebit v.toNat)).sum).image fun v => v.toNat)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hv).2)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hv).2)
  rw [hSeats] at union
  have cover : ((fV ∪ (f4 ∪ f5 ∪ f6)).image fun v => v.toNat) ⊆
      (((fV ∪ (f4 ∪ f5 ∪ f6)).filter fun v =>
        0 < ((eventsF ++ eventsC).map (syncDebit v.toNat)).sum).image fun v => v.toNat) ∪
      (((fV ∪ (f4 ∪ f5 ∪ f6)).filter fun v =>
        0 < (events.map (syncDebit v.toNat)).sum).image fun v => v.toNat) := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    have debited : 0 < ((eventsF ++ eventsC).map (syncDebit v.toNat)).sum ∨
        0 < (events.map (syncDebit v.toNat)).sum := by
      rcases Finset.mem_union.mp hv with hv | hv
      · exact .inl (Finset.mem_filter.mp hv).2
      · have pos : 0 < ((eventsF ++ events).map (syncDebit v.toNat)).sum := by
          rcases Finset.mem_union.mp hv with hv | hv
          · rcases Finset.mem_union.mp hv with hv | hv
            · exact (Finset.mem_filter.mp hv).2
            · exact (Finset.mem_filter.mp hv).2
          · exact (Finset.mem_filter.mp hv).2
        simp only [List.map_append, List.sum_append] at pos ⊢
        omega
    rcases debited with c | r
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, c⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, r⟩, rfl⟩)
  have union' := (Finset.card_le_card cover).trans union
  have disjoint : Disjoint fV (f4 ∪ f5 ∪ f6) := by
    rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨d4f, d5f⟩, d6f⟩
  rw [Finset.card_image_of_injective _ inj, Finset.card_union_of_disjoint disjoint,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d46', d56'⟩),
    Finset.card_union_of_disjoint d45'] at union'
  have linear : 3 * fV.card + f4.card + 3 * f5.card + f6.card ≤ 3 * seats := by omega
  have scaled := Nat.mul_le_mul_left β linear
  calc 3 * (β * fV.card) + β * f4.card + 3 * (β * f5.card) + β * f6.card
      = β * (3 * fV.card + f4.card + 3 * f5.card + f6.card) := by ring
    _ ≤ β * (3 * seats) := scaled
    _ = 3 * (β * seats) := by ring

/-- The flag reward of one increment is at most the reward of one increment. -/
private theorem flagRate_le (t : PinTerms preset) : flagRate t ≤ t.perIncrement := by
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
    (Nat.div_le_div_right (Nat.le_trans (sum_toNat_le f fun v hv =>
      Finset.mem_filter.mpr (inside v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2))
      (Nat.le_add_right _ _)))

/-- `branchR` is a whistleblower charge and the slashed, proposer and rounding charges.

The slashed, proposer and rounding charges have weight three.

So has the whistleblower charge `Wh`.

The slashed charge covers the flag gain of two windows and the leak of one increment.

The remainder `W` holds those and the unit gain.

`Wh` pays the whistleblower reward of any set of keys that R's call reads as slashed on its branch.

Each reward is at the key's effective balance and rise. -/
private theorem branchR_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    ∃ Wh W : ℕ, (pinTerms config state ancestor finalizedState).branchR =
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
      (pinTerms config state ancestor finalizedState).slashedR *
          (2 * (pinTerms config state ancestor finalizedState).depthFin *
            flagRate (pinTerms config state ancestor finalizedState)) +
        (pinTerms config state ancestor finalizedState).slashedR *
          slashLeak config fork (pinTerms config state ancestor finalizedState) +
        (pinTerms config state ancestor finalizedState).unitGain *
          (pinTerms config state ancestor finalizedState).slashedR ≤ W ∧
      ∀ A : Finset ValidatorIndex,
        ∑ v ∈ A.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
          = true), (balanceAt state v.toNat +
            (pinTerms config state ancestor finalizedState).rise v.toNat) /
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
          flagRate (pinTerms config state ancestor finalizedState) +
        slashLeak config fork (pinTerms config state ancestor finalizedState) ≤ D ∧
      U = (pinTerms config state ancestor finalizedState).unitGain ∧
      ∀ A : Finset ValidatorIndex,
        ∑ v ∈ A.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
          = true), (balanceAt state v.toNat +
            (pinTerms config state ancestor finalizedState).rise v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ W := by
    refine ⟨_, _, _, rfl, ?_, rfl, fun A => ?_⟩
    · exact charge _ _ _ _ _ _ (flagRate_le _)
        (by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num))
    · -- The reward of a key is read at its position among the keys slashed on this branch.
      refine floor_aux (A := A) (fun i => balanceAt state i +
        (pinTerms config state ancestor finalizedState).rise i)
        (fun i => (pinTerms config state ancestor finalizedState).slashedRB i) fun v _ flag => ?_
      refine ⟨Finset.mem_range.mpr (slashedRB_lt config state ancestor finalizedState flag), ?_⟩
      rw [slashedRB_eq] at flag
      exact of_decide_eq_true flag
  subst unit
  refine ⟨W, D * (pinTerms config state ancestor finalizedState).slashedR +
    (pinTerms config state ancestor finalizedState).unitGain *
      (pinTerms config state ancestor finalizedState).slashedR, by rw [split]; ring, ?_, floorW⟩
  have step : (pinTerms config state ancestor finalizedState).slashedR *
      (2 * (pinTerms config state ancestor finalizedState).depthFin *
          flagRate (pinTerms config state ancestor finalizedState) +
        slashLeak config fork (pinTerms config state ancestor finalizedState)) ≤
      D * (pinTerms config state ancestor finalizedState).slashedR :=
    (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_right _ gain)
  rw [Nat.mul_add] at step
  omega

/-- The sync part of the proposer credit is at most the proposer credit. -/
private theorem syncProposer_le_credit (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).syncProposer ≤
      (pinTerms config state ancestor finalizedState).proposerCredit :=
  Nat.le_add_left _ _

/-- The quotient of a number rounded up is at most the number. -/
private theorem ceil_div_le (c q : ℕ) : (c + q - 1) / q ≤ c := by
  rcases Nat.eq_zero_or_pos q with rfl | pos
  · simp
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rcases Nat.eq_zero_or_pos c with rfl | cpos
    · exact (Nat.div_eq_of_lt (by omega)).le
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      refine Nat.div_le_of_le_mul ?_
      rw [show c' + 1 + (q' + 1) - 1 = c' + q' + 1 by omega]
      nlinarith

/-- R1 from the count of its rounding bands.

The slash charges of the classes fit the slashed keys of `branchR`, with the weights of the classes.

The sync part of the proposer credit fits the proposer credit of each epoch.

The flag gain and the unit of each slashed key fit `W`, by `branchR_split`.

The bands of the classes fit the rounded keys of `branchR`, which is the hypothesis `bands`. -/
private theorem bud_branchR_of (h : Setting config checks g split fin pulled anc counted V)
    {events eventsF eventsC : List (BalanceEvent preset)}
    (bands : 3 * (∑ v ∈ V, bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ K4 pulled counted V, bandR (eventsF ++ events) v.toNat) +
        3 * (∑ v ∈ K5 counted V, bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ K6 pulled counted, bandR (eventsF ++ events) v.toNat) ≤
      3 * ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
        ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
          (pinTerms config pulled anc fin).depth *
            preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
          preset.SYNC_COMMITTEE_SIZE.toNat *
            (((getCurrentEpoch pulled).toNat + 1) /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
              (getCurrentEpoch fin).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
              (pinTerms config pulled anc fin).depth /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)))) :
    3 * ((pinTerms config pulled anc fin).slashedR *
        (2 * (pinTerms config pulled anc fin).depthFin *
          flagRate (pinTerms config pulled anc fin))) +
      3 * ((pinTerms config pulled anc fin).slashedR *
        slashLeak config fork (pinTerms config pulled anc fin)) +
      3 * ((pinTerms config pulled anc fin).unitGain * (pinTerms config pulled anc fin).slashedR) +
      3 * (∑ v ∈ V, bandR (eventsF ++ eventsC) v.toNat) +
        3 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) +
        (∑ v ∈ (K4 pulled counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR (eventsF ++ events) v.toNat)) +
        3 * (∑ v ∈ (K5 counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR (eventsF ++ events) v.toNat)) +
        (∑ v ∈ (K6 pulled counted),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR (eventsF ++ events) v.toNat)) +
        3 * (∑ v ∈ (SC pulled counted split).filter
            (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
          ((balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) /
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
            (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) ≤
      (pinTerms config pulled anc fin).branchR := by
  classical
  obtain ⟨Wh, W, hW, gainW, floorW⟩ := branchR_split config pulled anc fin
  obtain ⟨d45, d46, d56, -, -, -⟩ := classes_disjoint h
  obtain ⟨dSC, -⟩ := sc_disjoint h
  have slashes := weighted_le (A := K4 pulled counted V) (B := K5 counted V)
    (C := K6 pulled counted) (fun v => slashR (pinTerms config pulled anc fin) v.toNat) d45 d46
    d56
  -- A key of `SC` that R slashes takes an increment of `branchR`'s slashed keys.
  --
  -- A key of the classes takes one too, and the two sets are disjoint.
  have slashBound := slashR_le config pulled anc fin
    (K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪ SC pulled counted split)
  rw [Finset.sum_union dSC] at slashBound
  have scFloor := floorW (SC pulled counted split)
  have scReward : ∑ v ∈ (SC pulled counted split).filter
        (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
      ((balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      (∑ v ∈ (SC pulled counted split).filter
          (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
        (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        ∑ v ∈ SC pulled counted split, slashR (pinTerms config pulled anc fin) v.toNat := by
    have each : ∀ v ∈ (SC pulled counted split).filter
        (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
        (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
        (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        slashR (pinTerms config pulled anc fin) v.toNat := fun v hv => by
      have flag := (Finset.mem_filter.mp hv).2
      rw [show slashR (pinTerms config pulled anc fin) v.toNat =
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat by simp [slashR, flag]]
      exact Nat.add_le_add_left (ceil_div_le _ _) _
    refine (Finset.sum_le_sum each).trans ?_
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) _
  have credit := Nat.mul_le_mul_left (pinTerms config pulled anc fin).depth
    (syncProposer_le_credit config pulled anc fin)
  simp only [Finset.sum_add_distrib] at *
  rw [hW]
  omega

/-- R1 (branchR): R's credits to V keys since the split, weight 3.

The slashing of a key on R's branch is charged here for the keys of `K4` and `K5`.

So is a sync debit of R that `rise` omits.

The keys of `K4` weigh one, and those of `K5` weigh three.

`slashCharge`'s surplus pays `flow_split`'s slashed term.

`branchR` also holds the unit of each key slashed on R's branch.

The charge `slashCharge` is at least an increment and `2 * depthFin * flagRate`.

The flag rate is at most the rate of an increment, and `slashCharge` has four of it for each epoch.

The `syncProposer` part of `proposerCredit` is not used by `credR`.

`credR` leaves out sync events, so `bud_sync` takes it.

The keys of `SC` that R slashes after the split also draw on `branchR`, at weight three.

The reward of such a key on C's branch is read at its balance there.

That balance is at most R's balance and its rise, plus one increment for R's initial penalty.

`whistleblowerR` pays the quotient of the first two.

The increment is one of the slashed keys' increments, which no class spends for a key of `SC`. -/
theorem bud_branchR (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((pinTerms config pulled anc fin).slashedR *
        (2 * (pinTerms config pulled anc fin).depthFin *
          flagRate (pinTerms config pulled anc fin))) +
      3 * ((pinTerms config pulled anc fin).slashedR *
        slashLeak config fork (pinTerms config pulled anc fin)) +
      3 * ((pinTerms config pulled anc fin).unitGain * (pinTerms config pulled anc fin).slashedR) +
      3 * (∑ v ∈ V, bandR (eventsF ++ eventsC) v.toNat) +
        3 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) +
        (∑ v ∈ (K4 pulled counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR (eventsF ++ events) v.toNat)) +
        3 * (∑ v ∈ (K5 counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR (eventsF ++ events) v.toNat)) +
        (∑ v ∈ (K6 pulled counted),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR (eventsF ++ events) v.toNat)) +
        3 * (∑ v ∈ (SC pulled counted split).filter
            (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
          ((balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) /
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
            (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) ≤
      (pinTerms config pulled anc fin).branchR := by
  have calledNat := UInt64.le_iff_toNat_le.mp h.called
  have nearC := h.near
  have transport : ∀ {x y : ForkedBeaconState preset} (r : Run config checks x y) (a : ℕ),
      a ≤ max high highC → ∀ {es : List (BalanceEvent preset)},
      (getCurrentEpoch y.state).toNat ≤ a + 1 →
      r.balanceEvents a = .ok es → r.balanceEvents (max high highC) = .ok es := by
    intro x y r a le es endpoint ok
    rw [DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le r (localHigh := a)
      (by omega) endpoint]
    exact ok
  have bands := bands_seats h fromFin tail tailC (max high highC)
    (transport tail high (le_max_left _ _) endEpoch replayed)
    (transport fromFin high (le_max_left _ _) (by simp only; omega) replayedF)
    (transport tailC highC (le_max_right _ _) endEpochC replayedC)
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  refine bud_branchR_of h (le_trans bands ?_)
  rw [depthEq]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))

/-- The sync movement of a key is its sync credits plus its sync debits over the events. -/
private theorem syncF_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    syncF events v = (events.map (syncCredit v)).sum +
      (events.map (syncDebit v)).sum := by
  unfold syncF
  rw [← sum_syncDebit_eq events v]
  exact congrArg (· + ((events.map (syncDebit v)).sum)) (sum_map_sync events (keyCredit v)).symm

/-- The sync movement of keys on a run from the split, within a call's reach, is within an envelope.

The envelope is the seats' one, read at the pulled state's total. -/
private theorem syncF_run_le (h : Setting config checks g split fin pulled anc counted V)
    (pulledTotal : Gwei) (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal)
    {e : BeaconState preset fork} (t : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (highE : ℕ) {evs : List (BalanceEvent preset)} (replayed : t.balanceEvents highE = .ok evs)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, syncF evs i ≤
      ((getCurrentEpoch e).toNat + 1 - (getCurrentEpoch split).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinSplit5.syncSeatEnvelope preset pulledTotal.toNat := by
  obtain ⟨fromFin⟩ := h.fromFin
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      t.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat := by
    intro u w step member T read
    exact step_band_of_guard h (fromFin.append t) within pulledOk step
      ((Run.contains_append _ _ _).mpr (.inr member)) T read
  have moves := (PinSplit5.Run.syncDebits_le t h.fulu h.early highE replayed pulledTotal.toNat
    band keys).2.1
  exact (Finset.sum_le_sum fun i _ => (syncF_eq evs i).le).trans moves

/-- S1 (syncSeats), in the third window: the base bound with the shared segment's K debits.

It also holds the shares of `CS` and of the shared segment's exited keys of `SC`. -/
theorem bud_sync (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (highF : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents highF = .ok eventsF)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ V, (syncD eventsF v.toNat + (syncF events v.toNat + syncF eventsC v.toNat))) +
        (∑ v ∈ (K4 pulled counted V), syncD eventsF v.toNat) +
        (∑ v ∈ (K4 pulled counted V), (syncF events v.toNat + syncF eventsC v.toNat)) +
        (∑ v ∈ (K5 counted V), syncD eventsF v.toNat) +
        (∑ v ∈ (K5 counted V), (syncF events v.toNat + syncF eventsC v.toNat))) +
      (∑ v ∈ (K6 pulled counted), syncD eventsF v.toNat) +
      (∑ v ∈ (K6 pulled counted), (syncF events v.toNat + syncF eventsC v.toNat)) +
      wShare preset fork (∑ v ∈ SC pulled counted split, syncCr eventsC v.toNat) +
      wShare preset fork
        (∑ v ∈ SC pulled counted split, (syncD eventsF v.toNat + syncD events v.toNat)) +
      wShare preset fork (∑ v ∈ CS pulled counted, syncCr eventsC v.toNat) +
      wShare preset fork (∑ v ∈ SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, syncCr eventsF v.toNat) ≤
        (pinTerms config pulled anc fin).syncSeats +
          6 * ((pinTerms config pulled anc fin).depth *
            (pinTerms config pulled anc fin).syncProposer) := by
  classical
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have near := h.near
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  -- the five sets are pairwise disjoint
  obtain ⟨d45, d46, d56, d1, d15, d16⟩ := classes_disjoint h
  obtain ⟨dS, dVS⟩ := sc_disjoint h
  obtain ⟨dCK, dCV⟩ := cs_disjoint h
  have d2 : Disjoint (V ∪ K4 pulled counted V) (K5 counted V) :=
    Finset.disjoint_union_left.mpr ⟨d15, d45⟩
  have d3 : Disjoint (V ∪ K4 pulled counted V ∪ K5 counted V) (K6 pulled counted) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d16, d46⟩, d56⟩
  have d4 : Disjoint (V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted)
      (SC pulled counted split) := by
    rw [Finset.disjoint_left]
    intro v member slashed
    simp only [Finset.mem_union] at member
    rcases member with ((inV | in4) | in5) | in6
    · exact Finset.disjoint_left.mp dVS inV slashed
    · exact Finset.disjoint_left.mp dS (Finset.mem_union_left _ (Finset.mem_union_left _ in4))
        slashed
    · exact Finset.disjoint_left.mp dS (Finset.mem_union_left _ (Finset.mem_union_right _ in5))
        slashed
    · exact Finset.disjoint_left.mp dS (Finset.mem_union_right _ in6) slashed
  have dCS : Disjoint (V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪
      SC pulled counted split) (CS pulled counted) := by
    rw [Finset.disjoint_left]
    intro v member created
    simp only [Finset.mem_union] at member
    rcases member with (((inV | in4) | in5) | in6) | inSC
    · exact Finset.disjoint_left.mp dCV inV created
    · exact Finset.disjoint_left.mp dCK (by simp [in4]) created
    · exact Finset.disjoint_left.mp dCK (by simp [in5]) created
    · exact Finset.disjoint_left.mp dCK (by simp [in6]) created
    · exact Finset.disjoint_left.mp dCK (by simp [inSC]) created
  obtain ⟨U, hU⟩ : ∃ U : Finset ValidatorIndex,
      U = V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪ SC pulled counted split ∪
        CS pulled counted :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ValidatorIndex → ℕ, ∀ v, g v =
      syncF events v.toNat + syncF eventsC v.toNat := ⟨_, fun _ => rfl⟩
  have sumU : ∑ v ∈ U, g v = ∑ v ∈ V, g v + ∑ v ∈ K4 pulled counted V, g v +
      ∑ v ∈ K5 counted V, g v + ∑ v ∈ K6 pulled counted, g v +
      ∑ v ∈ SC pulled counted split, g v + ∑ v ∈ CS pulled counted, g v := by
    rw [hU, Finset.sum_union dCS, Finset.sum_union d4, Finset.sum_union d3, Finset.sum_union d2,
      Finset.sum_union d1]
  -- the keys of SC that exited by the finalized epoch hold the shared credits, and the rest debits
  set EK := (SC pulled counted split).filter
    (fun v => (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) with hEK
  set NF := (SC pulled counted split).filter
    (fun v => ¬ (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) with hNF
  have dKN : Disjoint (V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted) NF :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) d4
  have dKE : Disjoint (V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted) EK :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) d4
  have dNE : Disjoint NF EK := Finset.disjoint_left.mpr fun v inN inE =>
    (Finset.mem_filter.mp inN).2 (Finset.mem_filter.mp inE).2
  have scSplit : ∑ v ∈ SC pulled counted split, syncD eventsF v.toNat =
      ∑ v ∈ EK, syncD eventsF v.toNat + ∑ v ∈ NF, syncD eventsF v.toNat :=
    (Finset.sum_filter_add_sum_filter_not _ _ fun v : ValidatorIndex => syncD eventsF v.toNat).symm
  have unionD : ∑ v ∈ V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪ NF,
      syncD eventsF v.toNat = ∑ v ∈ V, syncD eventsF v.toNat +
        ∑ v ∈ K4 pulled counted V, syncD eventsF v.toNat +
        ∑ v ∈ K5 counted V, syncD eventsF v.toNat + ∑ v ∈ K6 pulled counted, syncD eventsF v.toNat +
        ∑ v ∈ NF, syncD eventsF v.toNat := by
    rw [Finset.sum_union dKN, Finset.sum_union d3, Finset.sum_union d2, Finset.sum_union d1]
  have unionK : ∑ v ∈ EK, (syncCr eventsF v.toNat + syncD eventsF v.toNat) =
      ∑ v ∈ EK, syncCr eventsF v.toNat + ∑ v ∈ EK, syncD eventsF v.toNat :=
    Finset.sum_add_distrib
  -- each class is weighed at most three times its tail movement, and the shares at most their own
  have classV : ∑ v ∈ V, (syncD eventsF v.toNat + (syncF events v.toNat + syncF eventsC v.toNat)) =
      ∑ v ∈ V, syncD eventsF v.toNat + ∑ v ∈ V, g v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hg]
  have class4 : ∑ v ∈ K4 pulled counted V, (syncF events v.toNat + syncF eventsC v.toNat) ≤
      ∑ v ∈ K4 pulled counted V, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have class5 : ∑ v ∈ K5 counted V, (syncF events v.toNat + syncF eventsC v.toNat) ≤
      ∑ v ∈ K5 counted V, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have class6 : ∑ v ∈ K6 pulled counted, (syncF events v.toNat + syncF eventsC v.toNat) ≤
      ∑ v ∈ K6 pulled counted, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have credits : wShare preset fork (∑ v ∈ SC pulled counted split, syncCr eventsC v.toNat) ≤
      ∑ v ∈ SC pulled counted split, syncF eventsC v.toNat :=
    (wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      unfold syncCr
      rw [syncF_eq]
      exact Nat.le_add_right _ _)
  have debits : wShare preset fork
      (∑ v ∈ SC pulled counted split, (syncD eventsF v.toNat + syncD events v.toNat)) ≤
      ∑ v ∈ SC pulled counted split, syncD eventsF v.toNat +
        ∑ v ∈ SC pulled counted split, syncF events v.toNat := by
    rw [← Finset.sum_add_distrib]
    exact (wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      unfold syncD
      rw [syncF_eq]
      omega)
  have creditsF : wShare preset fork (∑ v ∈ EK, syncCr eventsF v.toNat) ≤
      ∑ v ∈ EK, syncCr eventsF v.toNat := wShare_le h.facts _
  have creditsCS : wShare preset fork (∑ v ∈ CS pulled counted, syncCr eventsC v.toNat) ≤
      ∑ v ∈ CS pulled counted, g v :=
    (wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      rw [hg]
      unfold syncCr
      rw [syncF_eq eventsC]
      omega)
  have shares : ∑ v ∈ SC pulled counted split, syncF eventsC v.toNat +
      ∑ v ∈ SC pulled counted split, syncF events v.toNat =
      ∑ v ∈ SC pulled counted split, g v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hg]; omega
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ v ∈ V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪ NF,
      syncD eventsF v.toNat + ∑ v ∈ EK, (syncCr eventsF v.toNat + syncD eventsF v.toNat) :=
    ⟨_, rfl⟩
  refine le_trans (b := 3 * (∑ v ∈ U, g v + S)) ?_ ?_
  · rw [sumU, hS]
    omega
  -- the shared segment moves the debited keys and the keys of EK by one envelope for each seat
  obtain ⟨PD, hPD⟩ : ∃ PD, PD = (V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪
      NF).image fun v : ValidatorIndex => v.toNat := ⟨_, rfl⟩
  obtain ⟨PK, hPK⟩ : ∃ PK, PK = EK.image fun v : ValidatorIndex => v.toNat := ⟨_, rfl⟩
  have dP : Disjoint PD PK := by
    have injective : Function.Injective fun v : ValidatorIndex => v.toNat :=
      fun a b same => UInt64.toNat_inj.mp same
    rw [hPD, hPK, Finset.disjoint_image injective]
    exact Finset.disjoint_union_left.mpr ⟨dKE, dNE⟩
  have posD := sum_toNat_le (S := V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted ∪ NF)
    (P := PD) (fun i => syncD eventsF i)
    fun v member => by rw [hPD]; exact Finset.mem_image_of_mem _ member
  have posK := sum_toNat_le (S := EK) (P := PK) (fun i => syncCr eventsF i + syncD eventsF i)
    fun v member => by rw [hPK]; exact Finset.mem_image_of_mem _ member
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      fromFin.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat :=
    step_band_of_guard h fromFin (by omega) pulledOk
  -- no block of the shared segment has a proposer among the keys of EK
  obtain ⟨toFin⟩ := h.toFin
  have apartK : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      fromFin.Contains step → PinSplit5.stepApart PK step := by
    intro u w step member
    cases step with
    | slot _ => trivial
    | @block f before after engine signed due ok =>
      obtain ⟨pre, post, -, -, -⟩ := fromFin.contains_step_facts member h.early
      intro p found inK
      obtain ⟨v, inEK, same⟩ := Finset.mem_image.mp (hPK ▸ inK)
      -- v exits at R by the finalized epoch, so the finalized state has its record and exit
      obtain ⟨w0, foundPulled, exited⟩ : ∃ w0, pulled.validators.data[v.toNat]? = some w0 ∧
          w0.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat := by
        have flag : ((pulled.validators.data[v.toNat]?).any fun w =>
            decide (w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)) = true :=
          (Finset.mem_filter.mp inEK).2
        cases found0 : pulled.validators.data[v.toNat]? with
        | none => simp [found0] at flag
        | some w0 =>
          simp [found0] at flag
          exact ⟨w0, rfl, flag⟩
      obtain ⟨u0, foundFin, kept⟩ := exit_kept_of_le_fin h foundPulled exited
      have inactive := inactive_of_exited h.twoSlots (pre.snoc (Step.block engine signed due ok))
        foundFin (by rw [kept]; exact exited)
      have look := Run.lookaheadActive h.facts.covers h.genesis
        (toFin.append (pre.snoc (Step.block engine signed due ok)))
        (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      have active := look.proposer_active (Nat.le_trans h.fulu
        (fork_le_of_chainSteps (pre.snoc (Step.block engine signed due ok)).chainSteps)) found
      rw [← same, inactive] at active
      exact Bool.false_ne_true active
  have sharedRun := (PinSplit5.Run.syncDebits_le fromFin h.fulu h.early highF replayedF
    pulledTotal.toNat band ∅).2.2 PD PK dP apartK
  unfold PinSplit5.syncSeatMoves at sharedRun
  have sharedS : S ≤ ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat) *
      preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
        PinSplit5.syncEnvelope preset pulledTotal.toNat := by
    rw [hS]
    exact (Nat.add_le_add posD posK).trans sharedRun
  -- the tails move the keys of the five sets by their seat bounds
  have toPositions : ∑ v ∈ U, g v ≤ ∑ i ∈ U.image (fun v : ValidatorIndex => v.toNat),
      (syncF events i + syncF eventsC i) :=
    (Finset.sum_congr rfl fun v _ => hg v).le.trans (sum_toNat_le (S := U)
      (P := U.image fun v : ValidatorIndex => v.toNat) (fun i => syncF events i + syncF eventsC i)
      fun v member => Finset.mem_image_of_mem _ member)
  have first := syncF_run_le h pulledTotal pulledOk tail (Nat.le_succ _) high replayed
    (U.image fun v : ValidatorIndex => v.toNat)
  have second := syncF_run_le h pulledTotal pulledOk tailC near highC replayedC
    (U.image fun v : ValidatorIndex => v.toNat)
  generalize U.image (fun v : ValidatorIndex => v.toNat) = P at toPositions first second
  have splitP : ∑ i ∈ P, (syncF events i + syncF eventsC i) =
      ∑ i ∈ P, syncF events i + ∑ i ∈ P, syncF eventsC i := Finset.sum_add_distrib
  have totalEq : ((getTotalActiveBalance pulled).toOption.getD 0).toNat = pulledTotal.toNat := by
    rw [pulledOk]
    rfl
  have seats : (pinTerms config pulled anc fin).syncSeats =
      3 * (((pinTerms config pulled anc fin).depth +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinSplit5.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat) := rfl
  have proposer : (pinTerms config pulled anc fin).syncProposer =
      preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
        (PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat *
          PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := rfl
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  rw [totalEq] at seats proposer
  rw [seats, proposer]
  unfold PinSplit5.syncSeatEnvelope at first second
  generalize (pinTerms config pulled anc fin).depth = depth at depthEq ⊢
  generalize PinSplit5.syncEnvelope preset pulledTotal.toNat = env at *
  generalize env * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) =
    share at *
  -- the epochs of the three runs fit the two depths
  have epochs : ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat) +
      ((getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat) +
      ((getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat) ≤
      depth + ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) := by
    omega
  have firstDepth : (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth := by
    omega
  have secondDepth :
      (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth := by
    omega
  generalize (getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat = ef at *
  generalize (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat = e1 at *
  generalize (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat = e2 at *
  generalize (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat = d at *
  have scaleEnv := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) epochs
  have scaleShare := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share)
    (show e1 + e2 ≤ depth + depth by omega)
  have positions : ∑ v ∈ U, g v + S ≤
      (ef + e1 + e2) * (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) +
        (e1 + e2) * (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share) := by
    have tails : ∑ i ∈ P, (syncF events i + syncF eventsC i) ≤
        e1 * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * (env + share) +
          e2 * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * (env + share) := by
      rw [splitP]
      exact Nat.add_le_add first second
    calc _ ≤ _ := Nat.add_le_add (toPositions.trans tails) sharedS
      _ = _ := by ring
  calc 3 * (∑ v ∈ U, g v + S)
      ≤ 3 * ((ef + e1 + e2) *
          (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) +
        (e1 + e2) * (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share)) :=
        Nat.mul_le_mul_left _ positions
    _ ≤ 3 * ((depth + d) * (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) +
        (depth + depth) *
          (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add scaleEnv scaleShare)
    _ = _ := by ring

/-- The sync credits of any keys on C's branch are at most the seats' envelope and a share.

The share is the proposer's, and the bound weighs both at the depth.

This is the second run of `bud_sync` for credits alone, and `syncSeats` weighs it at `depth`. -/
private theorem syncCredits_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (eventsC.map (syncCredit i)).sum ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat *
          PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have near := h.near
  have run := syncF_run_le h pulledTotal pulledOk tailC near highC replayedC keys
  have credits : ∑ i ∈ keys, (eventsC.map (syncCredit i)).sum ≤ ∑ i ∈ keys, syncF eventsC i :=
    Finset.sum_le_sum fun i _ => (Nat.le_add_right _ _).trans (syncF_eq eventsC i).ge
  have totalEq : ((getTotalActiveBalance pulled).toOption.getD 0).toNat = pulledTotal.toNat := by
    rw [pulledOk]
    rfl
  have proposer : (pinTerms config pulled anc fin).syncProposer =
      preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
        (PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat *
          PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := rfl
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  rw [proposer, totalEq]
  unfold PinSplit5.syncSeatEnvelope at run
  generalize (pinTerms config pulled anc fin).depth = depth at depthEq ⊢
  generalize PinSplit5.syncEnvelope preset pulledTotal.toNat = env at *
  generalize env * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) =
    share at *
  have depthCounted : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth :=
    by omega
  have bounded : ∑ i ∈ keys, syncF eventsC i ≤
      depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env +
        depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share := by
    refine run.trans ?_
    rw [Nat.mul_add]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ depthCounted)))
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ depthCounted)))
  calc _ ≤ _ := credits.trans bounded
    _ = _ := by ring

/-- Floored key by key, the flag gains of a key set's other credits are at most one floored gain.

That gain is the gain of their weighted sum.

Each floor of a sum is at least the sum of the floors, in the increments and in the weights. -/
private theorem otherGain_sum_le {ι : Type} (S : Finset ι) (w c : ι → ℕ)
    (depth inc P F WD OC : ℕ) (within : ∑ i ∈ S, w i * c i ≤ OC) :
    ∑ i ∈ S, w i * (depth * (c i / inc * P * F / WD)) ≤ depth * (OC / inc * P * F / WD) := by
  have inner : ∑ i ∈ S, w i * (c i / inc) ≤ OC / inc :=
    (Finset.sum_le_sum fun i _ => Nat.mul_div_le_mul_div_assoc (w i) (c i) inc).trans
      ((DirectSafety.Apriori.Internal.sum_div_le S (fun i => w i * c i) inc).trans
        (Nat.div_le_div_right within))
  have outer : ∑ i ∈ S, w i * (c i / inc * P * F / WD) ≤ (OC / inc * P * F) / WD := by
    calc ∑ i ∈ S, w i * (c i / inc * P * F / WD)
        ≤ ∑ i ∈ S, (w i * (c i / inc) * P * F) / WD := Finset.sum_le_sum fun i _ => by
          have := Nat.mul_div_le_mul_div_assoc (w i) (c i / inc * P * F) WD
          rwa [show w i * (c i / inc * P * F) = w i * (c i / inc) * P * F by ring] at this
      _ ≤ (∑ i ∈ S, w i * (c i / inc) * P * F) / WD :=
          DirectSafety.Apriori.Internal.sum_div_le S _ WD
      _ = ((∑ i ∈ S, w i * (c i / inc)) * P * F) / WD := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ (OC / inc * P * F) / WD :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ inner))
  calc ∑ i ∈ S, w i * (depth * (c i / inc * P * F / WD))
      = depth * ∑ i ∈ S, w i * (c i / inc * P * F / WD) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ depth * (OC / inc * P * F / WD) := Nat.mul_le_mul_left _ outer

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A run from a state after the split bounds a key's balance and effective balance by its credits.

The balance at the start, up to the cap bound, is at most `B`.

Then the balance up to the cap bound is at most `B`, the gains at the largest rate and the credits.

The effective balance at the end is at most that of the start, or that bound.

The cap bound is at least every cap along the run. -/
private theorem ceiling_run (h : Setting config checks g split fin pulled anc counted V)
    {c a : ForkedBeaconState preset} (toC : Run config checks ⟨fork, split⟩ c)
    (tail : Run config checks c a) (aEarly : a.fork < .glamsterdam) (aFork : a.fork ≤ fork)
    (i : ℕ) (inside : i < c.state.validators.data.size) (highC : ℕ)
    (endEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1)
    (near : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (capHigh : ℕ) (capLe : capHigh ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt c i ≤ capHigh) (B : ℕ)
    (startBal : min (actualBalanceAt c i) capHigh ≤ B)
    (capCeil : ∀ z ∈ tail.balancePath, PinSplit2.capAt z i ≤ capHigh) :
    (∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ B +
      ((getCurrentEpoch a.state).toNat - (getCurrentEpoch c.state).toNat) *
        (pinTerms config pulled anc fin).gainRateMax +
      (netScan i highC tail +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail).1)) ∧
    effectiveAt a i ≤ max (effectiveAt c i) (B +
      ((getCurrentEpoch a.state).toNat - (getCurrentEpoch c.state).toNat) *
        (pinTerms config pulled anc fin).gainRateMax +
      (netScan i highC tail +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail).1)) := by
  classical
  obtain ⟨P, hP, gainLe, -⟩ := pin_rate_exists h
  obtain ⟨P', hP', rateAll⟩ := key_rate_forked h
  rw [hP'.trans hP.symm] at rateAll
  have cFork : fork ≤ c.fork := fork_le_of_chainSteps toC.chainSteps
  have rate : ∀ z ∈ tail.balancePath, i.toUInt64 ∉ getActiveValidatorIndices z.state
        (getPreviousEpoch z.state) ∨
      ∀ total perIncrement : Gwei, getTotalActiveBalance z.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
          (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    intro z member
    right
    obtain ⟨r1, r2, -⟩ := balancePath_endpoint tail (Run.nil : Run config checks a a)
      (Nat.le_trans aFork cFork) member
    have order : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch a.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
    exact rateAll z (toC.append r1) (Nat.le_trans (fork_le_of_chainSteps r2.chainSteps) aFork)
      (by omega)
  obtain ⟨-, -, third, fourth⟩ := PinSplit2.Run.effective_floor_pair tail aEarly
    (Nat.le_trans h.fulu cFork) i inside 0 0 capHigh highC
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
  have balances := fourth alignedCap startCap capCeil rate endEpoch
    (max_le (Nat.le_trans startCap capLe) (Nat.le_trans (Nat.min_le_left _ _) capLe))
  have ceiling := (third _ alignedCap startCap balances capCeil).1
  have gain := Nat.mul_le_mul_left ((getCurrentEpoch a.state).toNat -
    (getCurrentEpoch c.state).toNat) gainLe
  have credit : PinSplit2.creditBound tail i highC preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
      capHigh ≤ B +
        ((getCurrentEpoch a.state).toNat - (getCurrentEpoch c.state).toNat) *
          (pinTerms config pulled anc fin).gainRateMax +
        (netScan i highC tail +
          (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail).1) := by
    unfold PinSplit2.creditBound
    omega
  exact ⟨fun z member => Nat.le_trans (balances z member) credit,
    Nat.le_trans ceiling (max_le (Nat.le_max_left _ _) (Nat.le_trans (Nat.min_le_left _ _)
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans credit (Nat.le_max_right _ _)))))⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key beyond R's registry whose exit started on C's run rises at most by its credits and a band.

The exit is charged at the step that assigns it, with the effective balance before that step.

The key is active at that step, so the run crosses an epoch boundary before it.

The key is in the registry at the first state after the boundary.

There the balance is within the upward band of the effective balance.

The effective balance stays through the epoch.

From there the ceiling over the run to the key's state bounds the effective balance.

A key whose cap rose after the boundary is handled by the switch step (`Run.flip_split`).

In that case the effective balance is at the old cap. -/
private theorem earlier_charge (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (created : split.validators.data.size ≤ i) (old : Validator)
    (foundA : a.state.validators.data[i]? = some old)
    (assigned : old.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt a i ≤ chargeAmt tailC i + (preset.upwardBand +
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax +
      (credC tailC highC i + whistC tailC highC i + (eventsC.map (syncCredit i)).sum)) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨pre, post, cut, aEarly, aEpoch⟩ := Run.contains_step_facts member h.early
  have aFork : a.fork ≤ fork :=
    Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)
  -- the key is absent at the split, so it has a charge on the run before `a`
  have unset : ∀ v, (⟨fork, split⟩ : ForkedBeaconState preset).state.validators.data[i]? =
      some v → v.exitEpoch = FAR_FUTURE_EPOCH := fun v found =>
    absurd (Array.getElem?_eq_some_iff.mp found).1 (by simp only; omega)
  obtain ⟨c0, c0Mem, c0Index, -⟩ :=
    PinSplit.Run.charge_of_exit pre electra aEarly i unset old foundA assigned
  obtain ⟨p, q, pre', step', post', cut', v, w, foundP, foundQ, unsetP, setQ, actP, amount, -⟩ :=
    charge_activated (x := ⟨fork, split⟩) electra pre c0 (pre.departure_charge_site c0 c0Mem)
  rw [c0Index] at foundP foundQ
  have inTailC : c0 ∈ tailC.departureCharges := by
    rw [cut, Run.departureCharges_append]
    simp [Run.departureCharges, c0Mem]
  have chargeEq : chargeAmt tailC i = c0.amount := by
    unfold chargeAmt
    rw [find_charge inTailC (by simp [c0Index])
      (fun d inD hd => charge_unique tailC inD inTailC (by simpa [c0Index] using hd))]
    rfl
  have pEarly : p.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps
      ((Run.nil.snoc step').append post' : Run config checks p a).chainSteps) aEarly
  -- the key is active at the start of the charge step
  have activeP : isActiveAt p.state (getCurrentEpoch p.state) i = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨v, foundP, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨actP, UInt64.lt_iff_toNat_lt.mpr ?_⟩
    rw [unsetP]
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots p.state
    omega
  have splitP : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch p.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre'.chainSteps)
  have pBound := (getCurrentEpoch p.state).toNat_lt
  -- so the run from the split crosses an epoch boundary before it
  have splitLt : (getCurrentEpoch split).toNat < (getCurrentEpoch p.state).toNat := by
    by_contra notLt
    have fixed : getCurrentEpoch p.state ≤ activityFixedEpoch split := by
      rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
      omega
    have keep := activeKept_of_chainSteps pre'.chainSteps (getCurrentEpoch p.state) fixed i
    have activeSplit : isActiveAt split (getCurrentEpoch p.state) i = true := by
      rw [← keep]
      exact activeP
    obtain ⟨u, foundU, -⟩ := isActiveAt_eq_true_iff.mp activeSplit
    have := (Array.getElem?_eq_some_iff.mp foundU).1
    omega
  obtain ⟨z, cc, pre0, ok, rest0, splitEq, hz, hcc⟩ := PinSplit.Run.cross_split pre'
    ((getCurrentEpoch p.state).toNat - 1)
    (by show (getCurrentEpoch split).toNat ≤ (getCurrentEpoch p.state).toNat - 1; omega)
    (by omega)
  subst splitEq
  have ccEarly : cc.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) pEarly
  have fuluZ : .fusaka ≤ z.fork :=
    Nat.le_trans h.fulu (fork_le_of_chainSteps pre0.chainSteps)
  have hyst : Hysteresis cc.state :=
    hysteresis_of_crossing_slot ok h.bands fuluZ ccEarly (by omega)
  -- the key is in the registry at the first state of the epoch of the charge
  have fixedC : getCurrentEpoch p.state ≤ activityFixedEpoch cc.state := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    omega
  have keepC := activeKept_of_chainSteps rest0.chainSteps (getCurrentEpoch p.state) fixedC i
  have activeC : isActiveAt cc.state (getCurrentEpoch p.state) i = true := by
    rw [← keepC]
    exact activeP
  obtain ⟨vc, foundC, -⟩ := isActiveAt_eq_true_iff.mp activeC
  have insideC : i < cc.state.validators.data.size := (Array.getElem?_eq_some_iff.mp foundC).1
  have effEq : effectiveAt cc i = c0.amount := by
    have same := run_same_epoch_effective rest0 pEarly
      (UInt64.toNat_inj.mp (by omega)) i insideC
    have atP : effectiveAt p i = c0.amount := by simp [effectiveAt, foundP, amount]
    omega
  -- the run from the start of the epoch to the key's state
  obtain ⟨tail2, h2⟩ : ∃ t : Run config checks cc a, t = (rest0.snoc step').append post' :=
    ⟨_, rfl⟩
  have whole : pre = (pre0.snoc (Step.slot ok)).append tail2 := by
    rw [← cut', h2, Run.append_assoc]
    rfl
  have aElectra : .pectra ≤ a.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have capEnd := capAt_le_capMax h.caps aElectra i
  have toCC : Run config checks ⟨fork, split⟩ cc := pre0.snoc (Step.slot ok)
  have cFork : fork ≤ cc.fork := fork_le_of_chainSteps toCC.chainSteps
  have startEff : effectiveAt cc i ≤ PinSplit2.capAt cc i :=
    effective_le_cap_at (shared.append (fromFin.append toCC)) h.genesis h.caps ccEarly i
  have capCC : PinSplit2.capAt cc i ≤ PinSplit2.capAt a i :=
    cap_le_cap_of_run h.caps tail2 aEarly i
  have alignedCap : PinSplit2.capAt a i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    have := congrArg UInt64.toNat
      (withdrawalMaxEffectiveBalance_aligned (fork := a.fork) h.aligned old)
    simpa [PinSplit2.capAt, foundA, UInt64.toNat_mod] using this
  have capCeil := capCeil_path tail2 h.caps aEarly (Nat.le_trans aFork cFork) i
  have aEpoch' : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch counted).toNat := aEpoch
  have nearC := h.near
  have near : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  have scans : netScan i highC tail2 +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail2).1 ≤
      netScan i highC tailC +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tailC).1 := by
    have eqC : tailC = (((pre0.snoc (Step.slot ok)).append tail2).snoc step).append post := by
      rw [cut, whole]
    rw [eqC]
    simp only [netScan_append, creditScan_append, netScan_snoc, creditScan_snoc_fst]
    split_ifs <;> omega
  have sources := credits_le_sources (shared.append fromFin) h.genesis tailC h.early electra i highC
    replayedC
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have ccLow : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch cc.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toCC.chainSteps)
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  by_cases flipCase : ¬effectiveAt cc i < PinSplit2.capAt cc i ∧
      PinSplit2.capAt a i ≠ PinSplit2.capAt cc i
  · -- the key switched to compounding after the epoch start, with its effective balance at the cap
    obtain ⟨notBelow, capNe⟩ := flipCase
    have electraC : .pectra ≤ cc.fork := Nat.le_trans electra cFork
    have capCCmin : PinSplit2.capAt cc i = preset.MIN_ACTIVATION_BALANCE.toNat := by
      have eqn := capAt_of_found electraC foundC
      split at eqn <;> omega
    obtain ⟨s, s', pre1, step1, post1, eq1, capS, capS', balS', epochAt⟩ :=
      Run.flip_split tail2 aEarly (Nat.le_trans h.fulu cFork)
        ((shared.append (fromFin.append toCC)).invariant h.genesis.invariant) i (by omega)
        (by omega)
    have sFork : s.fork ≤ fork := Nat.le_trans step1.chainStep.fork_le
      (Nat.le_trans (fork_le_of_chainSteps post1.chainSteps) aFork)
    have s'Fork : s'.fork ≤ fork := Nat.le_trans (fork_le_of_chainSteps post1.chainSteps) aFork
    have sEarly : s.fork < .glamsterdam := Nat.lt_of_le_of_lt sFork h.early
    have s'Early : s'.fork < .glamsterdam := Nat.lt_of_le_of_lt s'Fork h.early
    have insideS : i < s.state.validators.data.size :=
      Nat.lt_of_lt_of_le insideC pre1.registryLifecycle.size_le
    have insideS' : i < s'.state.validators.data.size := Nat.lt_of_lt_of_le insideS
      (Run.nil.snoc step1 : Run config checks s s').registryLifecycle.size_le
    have e1 := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre1.chainSteps)
    have e2 := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (Run.nil.snoc step1 : Run config checks s s').chainSteps)
    have e3 := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post1.chainSteps)
    -- the switch step is a block step, so it keeps the epoch and the effective balances
    have epochEq := epochAt insideC
    have effS' : effectiveAt s' i = effectiveAt s i :=
      run_same_epoch_effective (Run.nil.snoc step1 : Run config checks s s') s'Early
        (UInt64.toNat_inj.mp epochEq) i insideS
    have minLe : preset.MIN_ACTIVATION_BALANCE.toNat ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
      UInt64.le_iff_toNat_le.mp h.caps.compounding
    have alignedMin : preset.MIN_ACTIVATION_BALANCE.toNat %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat h.aligned.2.1
    -- the run from the epoch start to the switch, at the activation balance as cap
    obtain ⟨-, ceil1⟩ := ceiling_run h toCC pre1 sEarly sFork i insideC highC (by omega)
      (by omega) preset.MIN_ACTIVATION_BALANCE.toNat minLe alignedMin (by omega)
      (effectiveAt cc i + preset.upwardBand) (by omega)
      (fun z member => Nat.le_trans
        (capCeil_path pre1 h.caps sEarly (Nat.le_trans sFork cFork) i z member) capS)
    -- the run from the switch to the key's state, at its cap
    obtain ⟨-, ceil2⟩ := ceiling_run h (toCC.append (pre1.snoc step1)) post1 aEarly aFork i
      insideS' highC (by omega) near (PinSplit2.capAt a i) capEnd alignedCap
      (Nat.le_trans (effective_le_cap_at (shared.append (fromFin.append
        (toCC.append (pre1.snoc step1)))) h.genesis h.caps s'Early i)
        (cap_le_cap_of_run h.caps post1 aEarly i))
      (effectiveAt cc i + stepCredit (fun _ => true) (fun _ => true) i step1) (by omega)
      (capCeil_path post1 h.caps aEarly (Nat.le_trans aFork
        (fork_le_of_chainSteps (toCC.append (pre1.snoc step1)).chainSteps)) i)
    -- the credits of the three parts are at most the sources of C's run
    have notSlot := step_flip_not_slot step1 s'Early
      (Nat.le_trans (Nat.le_trans h.fulu cFork) (fork_le_of_chainSteps pre1.chainSteps)) i
      insideS (by omega) capS'
    obtain ⟨eT, replayedT⟩ := tail2.balanceEvents_ok aEarly highC
    have eqC' : tailC = (pre0.snoc (Step.slot ok)).append
        (tail2.append ((Run.nil.snoc step).append post)) := by
      rw [cut, whole, Run.append_assoc, Run.append_assoc]
      rfl
    have part : credC tail2 highC i + whistC tail2 highC i + (eT.map (syncCredit i)).sum ≤
        credC tailC highC i + whistC tailC highC i + (eventsC.map (syncCredit i)).sum := by
      obtain ⟨eP, replayedP⟩ := (pre0.snoc (Step.slot ok)).balanceEvents_ok ccEarly highC
      obtain ⟨eQ, replayedQ⟩ := ((Run.nil.snoc step).append post).balanceEvents_ok h.early highC
      have joinedC := balanceEvents_append (pre0.snoc (Step.slot ok))
        (tail2.append ((Run.nil.snoc step).append post)) highC replayedP
        (balanceEvents_append tail2 ((Run.nil.snoc step).append post) highC replayedT replayedQ)
      rw [eqC', joinedC] at replayedC
      obtain rfl := Except.ok.inj replayedC
      rw [eqC']
      unfold credC whistC
      simp only [creditScan_append, List.map_append, List.sum_append]
      omega
    have around := flip_credits_le_sources (shared.append (fromFin.append toCC)) h.genesis pre1
      step1 post1 notSlot aEarly (Nat.le_trans electra cFork) i highC (by omega)
      (by rw [eq1]; exact replayedT)
    rw [eq1] at around
    have epochs : (getCurrentEpoch s.state).toNat - (getCurrentEpoch cc.state).toNat +
        ((getCurrentEpoch a.state).toNat - (getCurrentEpoch s'.state).toNat) ≤
        (pinTerms config pulled anc fin).depth := by omega
    have gains := Nat.mul_le_mul_right (pinTerms config pulled anc fin).gainRateMax epochs
    rw [Nat.add_mul] at gains
    rw [chargeEq]
    omega
  · have startBal : min (actualBalanceAt cc i) (PinSplit2.capAt a i) ≤
        effectiveAt cc i + preset.upwardBand := by
      by_cases below : effectiveAt cc i < PinSplit2.capAt cc i
      · cases hb : cc.state.balances.data[i]? with
        | none => simp [actualBalanceAt, hb]
        | some bal =>
          have up := hyst.up i vc bal foundC hb (UInt64.lt_iff_toNat_lt.mpr
            (by simpa [effectiveAt, PinSplit2.capAt, foundC] using below))
          have read : actualBalanceAt cc i = bal.toNat := by simp [actualBalanceAt, hb]
          have eff : effectiveAt cc i = vc.effectiveBalance.toNat := by simp [effectiveAt, foundC]
          omega
      · have same : PinSplit2.capAt a i = PinSplit2.capAt cc i := by
          by_contra ne
          exact flipCase ⟨below, ne⟩
        have := Nat.min_le_right (actualBalanceAt cc i) (PinSplit2.capAt a i)
        omega
    obtain ⟨-, ceiling⟩ := ceiling_run h toCC tail2 aEarly aFork i insideC highC (by omega) near
      (PinSplit2.capAt a i) capEnd alignedCap (Nat.le_trans startEff capCC)
      (effectiveAt cc i + preset.upwardBand) startBal capCeil
    have epochs : (getCurrentEpoch a.state).toNat - (getCurrentEpoch cc.state).toNat ≤
        (pinTerms config pulled anc fin).depth := by omega
    have gains := Nat.mul_le_mul_right (pinTerms config pulled anc fin).gainRateMax epochs
    rw [chargeEq]
    omega

/-- The whistleblower credits of a set of keys over a run fit the limits of its slashing events. -/
private theorem whistC_sum_le_limits {g m y : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (tail : Run config checks m y) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, whistC tail high v.toNat ≤
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared tail genesis early high
  rw [replayed] at foundOk
  cases foundOk
  simpa [whistC] using creditScan_sum_le S (fun s => decide (s = .slashings)) (fun _ => false)
    high (fun e => e.creditLimit) tail replayed fun e member _ =>
      sum_keyCredit_le_creditLimit S e (bounded e member).1

/-- The positions of the keys slashed on C's branch after the split.

They are unslashed at the split and slashed at C. -/
private def slashedOnC (split counted : BeaconState preset fork) : Finset ℕ :=
  (Finset.range counted.validators.data.size).filter fun i =>
    (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (counted.validators.data[i]?.map (·.slashed)).getD false = true

/-- The bound on the effective balance of a key of R's registry that R's call reads.

It is the key's effective balance, its rise and one increment, if R's branch slashes it.

`branchR` pays that bound for such a key, and its increment covers the drop of R's penalty.

A key that `exitedSlashable`, `late` or `pendingR` charges is read at its balance and rise, or `bF`.

It is read without `ebUp`, which can exceed them.

Otherwise it is also at least the key's bound `ebUp`. -/
private def whistleEnv (t : PinTerms preset) (pulled anc : BeaconState preset fork) (i : ℕ) : ℕ :=
  if t.slashedRB i = true then
    balanceAt pulled i + t.rise i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  else if ((pulled.validators.data[i]?.map (·.slashed)).getD false = false ∧
      ((pulled.validators.data[i]?.map fun v =>
        decide (v.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).getD false = true) ∧
      ((pulled.validators.data[i]?).any fun v =>
        decide (anc.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat)) = true) ∨
      (t.tight = false ∧ (t.lateB i = true ∨ t.pendingRB i = true)) then
    max (balanceAt pulled i + t.rise i) (t.bF i)
  else max (max (t.ebUp i) (balanceAt pulled i + t.rise i)) (t.bF i)

/-- The credits that raise the effective balance of a key of R's registry on C's branch.

They are the key's credits at eleven tenths, rounded up, with the bands of credits and seat debits.

The credits hold the key's own whistleblower credits.

Its unit of gain and the leak that its sync debits induce on R's run come on top, unscaled.

A second unit pays the joint floor that R's slashing penalty can tip.

`bud_whistle` pays them with the sets that it counts.

The seat debits are those of the two runs that R shares with C.

A key that exited before the finalized state also holds its credits on the shared segment.

A sync credit there has the band of its rounding. -/
private def whistleSlack (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (rrun : Run config checks x' y') (highC high : ℕ)
    (eventsC eventsF events : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  (11 * (propN tail highC i + depPre eventsC i + whistC tail highC i + syncCr eventsC i +
    consAmt eventsC i + syncD eventsF i + syncD events i) + 9) / 10 + bandC tail highC i +
    bandX fin highC i + bandR (eventsF ++ events) i +
    unitK t tail highC eventsC events eventsF i + inducedR t rrun i +
    (if 0 < slashW t i then t.unitGain else 0) +
  if t.exitBeforeFin i = true then
    (11 * (syncCr eventsF i + consAmt eventsF i) + 9) / 10 + bandX fin high i +
      (if 0 < syncCr eventsF i then preset.upwardBand else 0)
  else 0

/-- What a created key's charge adds to the effective balance of the key at an earlier exit.

It is the band, the gains at the largest rate and the key's credits on C's branch. -/
private def whistleExtra (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : ℕ) (eventsC : List (BalanceEvent preset)) (i : ℕ) :
    ℕ :=
  preset.upwardBand + t.depth * t.gainRateMax +
    (credC tail high i + whistC tail high i + syncCr eventsC i)

/-- The bound on the effective balance at its slashing of a key of the split's registry.

A key that is not active at C and has a departure charge on C's branch is also read at its charge.

That reading is the charge, the key's rise after it, and the slack.

The slashing starts the key's exit, or finds the exit that an earlier charge started. -/
private def whistleRead (t : PinTerms preset) (pulled anc counted : BeaconState preset fork)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {x' y' : ForkedBeaconState preset} (rrun : Run config checks x' y') (highC high : ℕ)
    (eventsC eventsF events : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  if ¬ isActiveAt counted (getCurrentEpoch counted) i = true ∧
      (tail.departureCharges.any fun c => c.index == i) = true then
    min (whistleEnv t pulled anc i +
        whistleSlack t tail rrun highC high eventsC eventsF events fin i)
      (chargeAmt tail i + riseQ tail highC i +
        whistleSlack t tail rrun highC high eventsC eventsF events fin i)
  else whistleEnv t pulled anc i + whistleSlack t tail rrun highC high eventsC eventsF events fin i

/-- The bound on the effective balance at its slashing of a key created after the split.

The key is active at C.

At a high gain rate it is the largest cap.

Otherwise it is the key's credits, their gains over the window, and a band. -/
private def createdCeil (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : ℕ) (eventsC : List (BalanceEvent preset)) (i : ℕ) :
    ℕ :=
  let credits := credC tail high i + whistC tail high i + syncCr eventsC i
  let rate := t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
  if t.gainHigh = true then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  else
    credits + t.depth * (11 * credits / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * rate /
      WEIGHT_DENOMINATOR.toNat) + t.depth * (rate / WEIGHT_DENOMINATOR.toNat + 2) +
        preset.downwardBand

/-- A key created after the split that is active at C has the bound `createdCeil` at its slashing.

Its credits since its creation are credits of C's branch, which P's `created_ceiling` reads.

That lemma bounds its effective balance at every state after its creation.

The credits of the run are at most `credC`, `whistC` and the seat credits, so the bound reads them.

The key is active at C, so `start_state` finds its creation state.

Off the high gain rate, `gainHigh` is false, which gives the lemma's premise on the rate. -/
private theorem created_active (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (created : ¬ i < split.validators.data.size)
    (active : isActiveAt counted (getCurrentEpoch counted) i = true)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    effectiveAt a i ≤ createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i :=
  sorry

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The whistleblower credits of any set of keys on C's branch are at most the reward base.

The base is the slashing reward of each key slashed on that branch, read at its balance then.

A key of the split's registry is read at the bound `registry` gives for it.

If it is not active at C and has a charge there, it is also read at `registryCharge`.

`registry` is asked for each key that is unslashed at the split, at each step of C's branch.

Its sub-cases are the arms of the key ceilings.

They are: exited before the finalized state, headroom, frozen cap, rising cap, created after it.

A key slashed on the shared segment from the finalized state is slashed at the split.

It is not in `slashedOnC`, so the sums below have no term for it: its credit on C's branch is zero.

A key of R's registry that is also slashed on R's branch is a term of the first sum.

A consumer that pays those terms by another budget splits that sum by the key's slashing on R.

A key created after the split that is active at C is read at `createdCeil`.

A key created after the split that has exited by C is read at its charge and credits.

Each term of the sums is at most the largest cap, which a slashing reads at its balance. -/
private theorem whistle_core (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
          effectiveAt a i ≤ whistleEnv (pinTerms config pulled anc fin) pulled anc i +
            whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
              eventsC eventsF events fin i)
    (registryCharge : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        (tailC.departureCharges.any fun c => c.index == i) = true →
          effectiveAt a i ≤ chargeAmt tailC i + riseQ tailC highC i +
            whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
              eventsC eventsF events fin i)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, whistC tailC highC v.toNat ≤
      (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
            (fromFin.append tail) highC high eventsC eventsF events fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      (∑ i ∈ ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => isActiveAt counted (getCurrentEpoch counted) i = true),
        min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      (∑ i ∈ ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true),
        min (chargeAmt tailC i +
            whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have limit := whistC_sum_le_limits (shared.append fromFin) h.genesis tailC h.early highC
    replayedC S
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ, ∀ i, E i =
      if (split.validators.data[i]?.map (·.slashed)).getD false = false then
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
            (fromFin.append tail) highC high eventsC eventsF events fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨cr, hcr⟩ : ∃ cr : ℕ → ℕ, ∀ i, cr i =
      if isActiveAt counted (getCurrentEpoch counted) i = true then
        min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
      else min (chargeAmt tailC i +
          whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := ⟨_, fun _ => rfl⟩
  -- the keys of R's registry are read at `registry`, or at the largest cap if slashed at the split
  have regE : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i ≤ E i := by
    intro a b step member i inside flag
    rw [hE i]
    obtain ⟨pre, -, -, aEarly, -⟩ := Run.contains_step_facts member h.early
    have capped := PinSplit5.effectiveAt_le_capMax ((shared.append fromFin).append pre) h.genesis
      h.caps aEarly i
    by_cases unslashed : (split.validators.data[i]?.map (·.slashed)).getD false = false
    · simp only [unslashed]
      refine le_min ?_ capped
      simp only [whistleRead]
      split
      · rename_i cond
        exact le_min (registry step member i inside unslashed flag)
          (registryCharge step member i inside unslashed flag cond.2)
      · exact registry step member i inside unslashed flag
    · simp only [unslashed]
      exact capped
  -- the created keys are read at `createdCeil` while active at C, and at their charge after
  have createdE : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, split.validators.data.size ≤ i →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ cr i := by
    intro a b step member i created flag
    rw [hcr i]
    obtain ⟨pre, -, -, aEarly, -⟩ := Run.contains_step_facts member h.early
    have capped := PinSplit5.effectiveAt_le_capMax ((shared.append fromFin).append pre) h.genesis
      h.caps aEarly i
    by_cases act : isActiveAt counted (getCurrentEpoch counted) i = true
    · simp only [act]
      exact Nat.div_le_div_right (le_min (created_active h tailC highC endEpochC replayedC step
        member i (Nat.not_lt.mpr created) act flag) capped)
    · simp only [act]
      exact Nat.div_le_div_right (le_min (created_charge h fromFin tailC
        (whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC)
        (fun step member i created old foundA assigned =>
          earlier_charge h tailC highC endEpochC replayedC step member i created old foundA
            assigned) step member i created flag) capped)
  have charged := slashing_charge h fromFin tailC highC endEpochC replayedC E cr regE createdE
  refine limit.trans (charged.trans (le_of_eq ?_))
  -- the sum over the slashed keys splits into the three kinds of key
  change ∑ i ∈ slashedOnC split counted, _ = _
  rw [← Finset.sum_filter_add_sum_filter_not (slashedOnC split counted)
    (fun i => i < split.validators.data.size)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size))
    (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)]
  rw [← add_assoc]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inSlashed, inside⟩ := Finset.mem_filter.mp member
    have unslashed := (Finset.mem_filter.mp inSlashed).2.1
    simp only [inside, ↓reduceIte, hE i, unslashed]
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inNew, act⟩ := Finset.mem_filter.mp member
    have outside := (Finset.mem_filter.mp inNew).2
    simp [outside, hcr i, act]
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inNew, act⟩ := Finset.mem_filter.mp member
    have outside := (Finset.mem_filter.mp inNew).2
    simp [outside, hcr i, act]

/-- W (`reserveW`, `flagged`, `seatShortfall`, K7, cS): whistleblower rewards on C's branch,
weight 3, are paid by the slashed key's own slack, or charged. -/
theorem bud_whistle (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (highF : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents highF = .ok eventsF)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ (K4 pulled counted V), (whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (K5 counted V), (whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (K6 pulled counted), (whistC tailC highC v.toNat : ℤ))) ≤
      -cK7 pulled counted - cS pulled counted V + (pinTerms config pulled anc fin).reserveW +
        (pinTerms config pulled anc fin).flagged + (pinTerms config pulled anc fin).seatShortfall +
        ((wShare preset fork ((∑ v ∈ SC pulled counted split, propN tailC highC v.toNat) +
            ∑ v ∈ SC pulled counted split, depPre eventsC v.toNat) +
          wShare preset fork (∑ v ∈ SC pulled counted split, syncCr eventsC v.toNat) +
          wShare preset fork (∑ v ∈ SC pulled counted split, consAmt eventsC v.toNat) +
          wShare preset fork
            (∑ v ∈ SC pulled counted split, (syncD eventsF v.toNat + syncD events v.toNat)) +
          (∑ v ∈ SC pulled counted split, bandC tailC highC v.toNat) +
          (∑ v ∈ SC pulled counted split, bandX fin highC v.toNat) +
          wShare preset fork ((∑ v ∈ CS pulled counted, propN tailC highC v.toNat) +
            ∑ v ∈ CS pulled counted, depPre eventsC v.toNat) +
          wShare preset fork (∑ v ∈ CS pulled counted, syncCr eventsC v.toNat) +
          wShare preset fork (∑ v ∈ CS pulled counted, consAmt eventsC v.toNat) +
          (∑ v ∈ CS pulled counted, bandC tailC highC v.toNat) +
          (∑ v ∈ CS pulled counted, bandX fin highC v.toNat) +
          wShare preset fork (∑ v ∈ SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, syncCr eventsF v.toNat) +
          wShare preset fork (∑ v ∈ SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
              consAmt eventsF v.toNat) +
          (∑ v ∈ SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, bandX fin high v.toNat) :
            ℕ) : ℤ) +
      -- The keys that R slashes after the split are read at the bound that `bud_branchR` pays.
      ((3 * (∑ v ∈ (SC pulled counted split).filter
            (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
          ((balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) /
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
            (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) : ℕ) : ℤ) :=
  sorry

/-- Glue: V keys are current at R, and distinct keys have distinct positions. -/
theorem bud_fall (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) ≤ ∑ i ∈ (pinTerms config pulled anc fin).positions with (pinTerms config pulled anc fin).current i = true, (pinTerms config pulled anc fin).fall i := by
  have within := BeaconState.registryWithinLimit_of_lt h.early pulled
  refine sum_toNat_le (pinTerms config pulled anc fin).fall fun v voter => ?_
  have listed : v ∈ getActiveValidatorIndices pulled (getCurrentEpoch pulled) := by
    simpa [activeVoters] using (h.voting v voter).1
  obtain ⟨validator, found, active⟩ := (mem_getActiveValidatorIndices within).mp listed
  exact mem_positions_filter config pulled anc fin found
    (isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩)

/-- Glue: (K4 pulled counted V) keys are current at R. -/
theorem bud_rise (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (K4 pulled counted V), (pinTerms config pulled anc fin).rise v.toNat) ≤ ∑ i ∈ (pinTerms config pulled anc fin).positions with (pinTerms config pulled anc fin).current i = true, (pinTerms config pulled anc fin).rise i := by
  refine sum_toNat_le (fun i => (pinTerms config pulled anc fin).rise i) fun v hv => ?_
  simp only [K4, Finset.mem_filter] at hv
  obtain ⟨w, found, active⟩ := active_of_activeVoters h.early (s := pulled) hv.2.1
  exact mem_positions_filter config pulled anc fin found
    (isActiveAt_eq_true_iff.mpr ⟨w, found, active⟩)

/-- `quorumReserve` holds `joining` (its gain term). -/
theorem bud_joining : (pinTerms config pulled anc fin).joining ≤ (pinTerms config pulled anc fin).quorum := by
  dsimp only [pinTerms, quorumReserve]
  exact (show ∀ a b c : ℕ, a ≤ 2 * (a + b) + 3 * c by intros; omega) _ _ _

/-- The weighted gains of the flows fit `creditLow`, the slashed term and the credits themselves.

The gains are bounded linearly, at the rate `11 * D * FP / (I * WD)` of a unit of flow.

The credit part pays at a rate below one, so it costs at most itself.

The other parts round down their increments once, and `f` at least two covers the rounding.

The consolidations are a whole number `m` of increments, and the slashed keys are at most `n`. -/
private theorem flow_close (I WD FP D D2 m OC Wr Wc Wo Ws n df L : ℕ)
    (hI : 0 < I) (hWD : 0 < WD) (key : 0 < L → 11 * D * FP < WD * I) (f2 : 0 < L → 2 ≤ FP / WD)
    (hD : D ≤ df) (hDD : D ≤ D2) (hc : Wc ≤ 3 * (I * m)) (ho : Wo ≤ OC) (hs : Ws ≤ 3 * (I * n))
    (lin : 10 * (I * WD) * L ≤ 11 * D * FP * (Wr + Wc + Wo + Ws)) :
    10 * L ≤ 10 * ((33 * D2 * (m * FP / WD) + 11 * D2 * ((OC / I) * FP / WD) +
      30 * D2 * (FP / WD + 1) + 9) / 10 + 3 * (n * (2 * df * (FP / WD)))) + Wr := by
  rcases Nat.eq_zero_or_pos L with zero | pos
  · subst zero; simp
  have key := key pos
  have f2 := f2 pos
  generalize hf : FP / WD = f at f2 ⊢
  generalize hcg : m * FP / WD = cg
  generalize hog : OC / I * FP / WD = og
  have cG : m * FP ≤ WD * (cg + 1) := by
    have := Nat.lt_mul_div_succ (m * FP) hWD; rw [hcg] at this; exact this.le
  have oG : OC / I * FP ≤ WD * (og + 1) := by
    have := Nat.lt_mul_div_succ (OC / I * FP) hWD; rw [hog] at this; exact this.le
  have fG : FP ≤ WD * (f + 1) := by
    have := Nat.lt_mul_div_succ FP hWD; rw [hf] at this; exact this.le
  have ocLt : OC < I * (OC / I + 1) := by
    have := Nat.lt_mul_div_succ OC hI; exact this
  -- the credit part pays at the rate below one
  have rate : 11 * D * FP * Wr ≤ I * WD * Wr := by
    have := Nat.mul_le_mul_right Wr key.le; linarith
  have consB : 11 * D * FP * Wc ≤ I * WD * (33 * D * (cg + 1)) := by
    calc 11 * D * FP * Wc ≤ 11 * D * FP * (3 * (I * m)) := Nat.mul_le_mul_left _ hc
      _ = 33 * D * I * (m * FP) := by ring
      _ ≤ 33 * D * I * (WD * (cg + 1)) := Nat.mul_le_mul_left _ cG
      _ = I * WD * (33 * D * (cg + 1)) := by ring
  have otherB : 11 * D * FP * Wo ≤ I * WD * (11 * D * (og + f + 2)) := by
    have step1 : FP * OC ≤ FP * (I * (OC / I)) + FP * I := by
      have := Nat.mul_le_mul_left FP ocLt.le
      calc FP * OC ≤ FP * (I * (OC / I + 1)) := this
        _ = FP * (I * (OC / I)) + FP * I := by ring
    have step2 : FP * (I * (OC / I)) ≤ I * (WD * (og + 1)) := by
      calc FP * (I * (OC / I)) = I * (OC / I * FP) := by ring
        _ ≤ I * (WD * (og + 1)) := Nat.mul_le_mul_left _ oG
    have step3 : FP * I ≤ I * (WD * (f + 1)) := by
      calc FP * I = I * FP := by ring
        _ ≤ I * (WD * (f + 1)) := Nat.mul_le_mul_left _ fG
    calc 11 * D * FP * Wo ≤ 11 * D * (FP * OC) := by
          calc 11 * D * FP * Wo = 11 * D * (FP * Wo) := by ring
            _ ≤ 11 * D * (FP * OC) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ho)
      _ ≤ 11 * D * (I * (WD * (og + 1)) + I * (WD * (f + 1))) := by
          refine Nat.mul_le_mul_left _ ?_
          omega
      _ = I * WD * (11 * D * (og + f + 2)) := by ring
  have slashB : 11 * D * FP * Ws ≤ I * WD * (33 * D * n * (f + 1)) := by
    calc 11 * D * FP * Ws ≤ 11 * D * FP * (3 * (I * n)) := Nat.mul_le_mul_left _ hs
      _ = 33 * D * n * I * FP := by ring
      _ ≤ 33 * D * n * I * (WD * (f + 1)) := Nat.mul_le_mul_left _ fG
      _ = I * WD * (33 * D * n * (f + 1)) := by ring
  have total : 10 * (I * WD) * L ≤ I * WD * (Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) +
      33 * D * n * (f + 1)) := by
    calc 10 * (I * WD) * L ≤ 11 * D * FP * (Wr + Wc + Wo + Ws) := lin
      _ = 11 * D * FP * Wr + 11 * D * FP * Wc + 11 * D * FP * Wo + 11 * D * FP * Ws := by ring
      _ ≤ _ := by nlinarith [rate, consB, otherB, slashB]
  have cancel : 10 * L ≤ Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) + 33 * D * n * (f + 1) := by
    have hq : 0 < I * WD := Nat.mul_pos hI hWD
    have : I * WD * (10 * L) ≤ I * WD * (Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) +
      33 * D * n * (f + 1)) := by linarith
    exact Nat.le_of_mul_le_mul_left this hq
  have t1 : 25 * D ≤ 19 * (D * f) := by nlinarith
  have t2 : 33 * D * n * (f + 1) ≤ 60 * (n * (df * f)) := by
    have a : D * n * f ≤ n * (df * f) := by
      calc D * n * f = n * (D * f) := by ring
        _ ≤ n * (df * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD)
    have b : D * n * 2 ≤ n * (df * f) := by
      calc D * n * 2 ≤ n * (df * 2) := by
            have := Nat.mul_le_mul_left n (Nat.mul_le_mul_right 2 hD); linarith
        _ ≤ n * (df * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ f2)
    have e : 33 * D * n * (f + 1) = 33 * (D * n * f) + 33 * (D * n) := by ring
    have hN := Nat.zero_le (n * (df * f))
    linarith
  have rnd : 33 * D2 * cg + 11 * D2 * og + 30 * D2 * (f + 1) ≤
      10 * ((33 * D2 * cg + 11 * D2 * og + 30 * D2 * (f + 1) + 9) / 10) := by omega
  have m1 : D * cg ≤ D2 * cg := Nat.mul_le_mul_right _ hDD
  have m2 : D * og ≤ D2 * og := Nat.mul_le_mul_right _ hDD
  have m3 : D * f ≤ D2 * f := Nat.mul_le_mul_right _ hDD
  have e1 : 33 * D * (cg + 1) = 33 * D * cg + 33 * D := by ring
  have e2 : 11 * D * (og + f + 2) = 11 * D * og + 11 * (D * f) + 22 * D := by ring
  have e3 : 30 * D2 * (f + 1) = 30 * (D2 * f) + 30 * D2 := by ring
  have e4 : 3 * (n * (2 * df * f)) = 6 * (n * (df * f)) := by ring
  rw [e3] at rnd
  rw [e3, e4]
  linarith

/-- The gains of the counted keys, at their weights, are at most the linear rate of their flows.

The credits of each class are read through the function `cA`, `cB` or `cC` of the key. -/
private theorem flow_lin (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (A B C : Finset ValidatorIndex)
    (cA cB cC : ℕ → ℕ) :
    10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
        ((∑ v ∈ A, flowK t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
          3 * (∑ v ∈ B, flowK t tailC high eventsC events eventsF v.toNat (cB v.toNat)) +
          (∑ v ∈ C, flowK t tailC high eventsC events eventsF v.toNat (cC v.toNat))) ≤
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
        ((∑ v ∈ A, flowCredit t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
          3 * (∑ v ∈ B, flowCredit t tailC high eventsC events eventsF v.toNat (cB v.toNat)) +
          (∑ v ∈ C, flowCredit t tailC high eventsC events eventsF v.toNat (cC v.toNat))) := by
  have each (i c : ℕ) :
      10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
        flowK t tailC high eventsC events eventsF i c ≤
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
        flowCredit t tailC high eventsC events eventsF i c := by
    have lin := gain_lin preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
      (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) (min t.depth t.depthFin)
      (flowCredit t tailC high eventsC events eventsF i c)
    unfold flowK
    split_ifs
    · unfold flowGain
      rwa [Nat.mul_assoc (11 * flowCredit t tailC high eventsC events eventsF i c /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat))]
    · simp
  have sum (S : Finset ValidatorIndex) (cS : ℕ → ℕ) :
      10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
          (∑ v ∈ S, flowK t tailC high eventsC events eventsF v.toNat (cS v.toNat)) ≤
        11 * min t.depth t.depthFin *
            (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
          (∑ v ∈ S, flowCredit t tailC high eventsC events eventsF v.toNat (cS v.toNat)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => each v.toNat (cS v.toNat)
  have a := sum A cA
  have b := sum B cB
  have c := sum C cC
  nlinarith [a, b, c]

/-- The initial slashing penalties of a key set on R's branch are at most `slashedR` increments.

The penalty is at most the increment that `slashR` charges, by `slashBand`. -/
private theorem flow_slash (h : Setting config checks g split fin pulled anc counted V)
    (W : Finset ValidatorIndex) :
    ∑ v ∈ W, slashW (pinTerms config pulled anc fin) v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (pinTerms config pulled anc fin).slashedR := by
  refine le_trans (Finset.sum_le_sum fun v _ => ?_) (slashR_le config pulled anc fin W)
  unfold slashW slashR
  split_ifs
  · have := h.facts.slashBand
    exact le_trans (Nat.le_add_right _ _) this
  · exact le_rfl

/-- The sync flows of any keys fit the sync part of `otherCredits`.

The flows are C's credits and the debits of R's run and of the shared segment.

The debits of the shared segment and of R's run take the epochs from the finalized block to the end.

C's credits take the seats' envelope and the proposer's share, as `syncCredits_le` bounds them. -/
private theorem flow_sync (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (highF : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents highF = .ok eventsF)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (syncCr eventsC i + syncD events i + syncD eventsF i) ≤
      ((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have totalEq : ((getTotalActiveBalance pulled).toOption.getD 0).toNat = pulledTotal.toNat := by
    rw [pulledOk]
    rfl
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp h.called
  have credits := syncCredits_le h tailC highC replayedC keys
  have shared := (PinSplit5.Run.syncDebits_le fromFin h.fulu h.early highF replayedF
    pulledTotal.toNat (step_band_of_guard h fromFin (by omega) pulledOk) keys).1
  have own := (PinSplit5.Run.syncDebits_le tail h.fulu h.early high replayed pulledTotal.toNat
    (fun {u w} step member T read => step_band_of_guard h (fromFin.append tail) (Nat.le_succ _)
      pulledOk step ((Run.contains_append _ _ _).mpr (.inr member)) T read) keys).1
  have epochs : ((getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat) +
      ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat) =
        (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
  rw [totalEq]
  simp only [Finset.sum_add_distrib]
  unfold syncCr syncD
  have scaled := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
      PinSplit5.syncEnvelope preset pulledTotal.toNat) (le_of_eq epochs)
  rw [totalEq] at credits
  nlinarith [credits, shared, own, scaled]

/-- Some counted key has a positive flow gain when the weighted gains are positive. -/
private theorem flow_pos (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (A B C : Finset ValidatorIndex)
    (cA cB cC : ℕ → ℕ)
    (pos : 0 < (∑ v ∈ A, flowK t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
      3 * (∑ v ∈ B, flowK t tailC high eventsC events eventsF v.toNat (cB v.toNat)) +
      (∑ v ∈ C, flowK t tailC high eventsC events eventsF v.toNat (cC v.toNat))) :
    ∃ i c, 0 < flowK t tailC high eventsC events eventsF i c := by
  by_contra none
  have zero : ∀ i c, flowK t tailC high eventsC events eventsF i c = 0 := fun i c =>
    Nat.eq_zero_of_not_pos fun p => none ⟨i, c, p⟩
  simp only [zero, Finset.sum_const_zero] at pos
  omega

/-- A key with a positive flow gain is on a kept arm or beyond R's registry in the low regime.

Either way its rate per increment is below an eleventh, so the credit part pays below its worth. -/
private theorem flow_key (h : Setting config checks g split fin pulled anc counted V)
    {x y : ForkedBeaconState preset} (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i c : ℕ)
    (pos : 0 < flowK (pinTerms config pulled anc fin) tailC high eventsC events eventsF i c) :
    11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have incPos := h.bands.1
  have wdPos : 0 < WEIGHT_DENOMINATOR.toNat := by decide
  have arm : (pinTerms config pulled anc fin).keptArm i = true ∨
      (i ∉ (pinTerms config pulled anc fin).positions ∧
        (pinTerms config pulled anc fin).gainHigh = false) := by
    by_contra none
    unfold flowK at pos
    rw [ite_eq_right_iff.mpr (fun c => absurd c none)] at pos
    exact Nat.lt_irrefl 0 pos
  rcases arm with kept | ⟨-, low⟩
  · have rateLow : 11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).gainRate i + 1) ≤
          (pinTerms config pulled anc fin).ebUp i := by
      have := kept
      simp only [pinTerms, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    exact rate_per_increment _ _ _ _ _ _ incPos wdPos (ebUp_aligned h i) rateLow
  · have rateLow : 11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
        WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      have test : 11 * (pinTerms config pulled anc fin).depth *
          ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
        have shown : (!decide (11 * (pinTerms config pulled anc fin).depth *
            ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
              preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)) = false := low
        simpa using shown
      have aligned : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
        have := congrArg UInt64.toNat h.aligned.2.2
        simpa [UInt64.toNat_mod] using this
      exact rate_per_increment _ _ _ _ _ _ incPos wdPos aligned test
    exact rateLow

/-- The rate of one increment, at the pin's base reward, is at least two.

The base reward per increment is at least four, by `four_le_perIncrement`. -/
private theorem flow_rate (h : Setting config checks g split fin pulled anc counted V) :
    2 ≤ (pinTerms config pulled anc fin).perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
  have four := four_le_perIncrement h
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  omega

/-- SCRATCH stub of C's whistleblower bucket: the slashing credits of any keys fit `WB`.

`WB` is the whistleblower base of `otherCredits`. -/
private theorem flow_whist (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (highF : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents highF = .ok eventsF)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∃ WB : ℕ, (pinTerms config pulled anc fin).otherGain =
        (3 * (WB + (((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
            preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
              PinSplit5.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
            (pinTerms config pulled anc fin).depth *
              (pinTerms config pulled anc fin).syncProposer))) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (pinTerms config pulled anc fin).perIncrement *
            (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ∧
      ∀ keys : Finset ℕ, ∑ i ∈ keys, whistC tailC highC i ≤ WB := sorry

/-- The flow gains of the counted keys, at their weights, fit the low part of `creditGain`.

They also take `slashCharge`'s surplus over R's slashed keys and a tenth of the keys' credits.

The bound is scaled by ten, so the tenth is exact.

One floor of all of a key's flows bounds its gain, and each split by kind costs one step. -/
private theorem flow_split (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * ((∑ v ∈ (K4 pulled counted V),
        flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat) +
      3 * (∑ v ∈ (K5 counted V),
          flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
            (propC tailC highC v.toNat)) +
      (∑ v ∈ (K6 pulled counted),
          flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat)) ≤
      10 * ((pinTerms config pulled anc fin).creditLow +
        3 * ((pinTerms config pulled anc fin).slashedR *
          (2 * (pinTerms config pulled anc fin).depthFin *
            flagRate (pinTerms config pulled anc fin)))) +
        (((∑ v ∈ (K4 pulled counted V), credN tailC highC v.toNat) +
          (∑ v ∈ (K6 pulled counted), credN tailC highC v.toNat) +
          (∑ v ∈ (K5 counted V), propN tailC highC v.toNat)) +
          2 * (∑ v ∈ (K5 counted V), propN tailC highC v.toNat)) := by
  classical
  have incPos := h.bands.1
  have wdPos : 0 < WEIGHT_DENOMINATOR.toNat := by decide
  obtain ⟨d45, d46, d56, -, -, -⟩ := classes_disjoint h
  have called := UInt64.le_iff_toNat_le.mp h.called
  have near := h.near
  -- The consolidations are read at the pulled epoch, where `bud_consolidations_base` holds.
  have whole : (∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
      (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
    have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
    have onR := (DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le tail (high := high)
      (localHigh := (getCurrentEpoch pulled).toNat) endEpoch (by simp only; omega)).symm.trans
      replayed
    have onF := (DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le fromFin
      (high := high) (localHigh := (getCurrentEpoch pulled).toNat) (by simp only; omega)
      (by simp only; omega)).symm.trans
      replayedF
    have onC := (DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le tailC
      (high := highC) (localHigh := (getCurrentEpoch pulled).toNat) endEpochC
      (by simp only; omega)).symm.trans replayedC
    exact (bud_consolidations_base h fromFin tail _ (by omega) onR onF le_rfl tailC _ (by omega)
      onC le_rfl h.facts.band).2
  set t := pinTerms config pulled anc fin with ht
  obtain ⟨B, hOther, hB⟩ : ∃ B : ℕ,
      t.otherGain = (3 * B) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ∧
      ∀ keys : Finset ℕ, ∑ i ∈ keys, (whistC tailC highC i +
        (syncCr eventsC i + syncD events i + syncD eventsF i)) ≤ B := by
    obtain ⟨WB, hOther, hWhist⟩ := flow_whist h fromFin high replayedF tail high replayed tailC
      highC replayedC
    refine ⟨WB + _, hOther, fun keys => ?_⟩
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add (hWhist keys)
      (flow_sync h fromFin high replayedF tail high replayed tailC highC replayedC keys)
  -- The credits of each class split by kind: the credit part, the consolidations, the rest.
  have split4 : ∀ (S : Finset ValidatorIndex) (r cr : ℕ → ℕ),
      (∀ v ∈ S, flowCredit t tailC highC eventsC events eventsF v.toNat (cr v.toNat) ≤
        r v.toNat + consAmt eventsC v.toNat +
          (whistC tailC highC v.toNat + (syncCr eventsC v.toNat + syncD events v.toNat +
            syncD eventsF v.toNat)) + slashW t v.toNat) →
      ∑ v ∈ S, flowCredit t tailC highC eventsC events eventsF v.toNat (cr v.toNat) ≤
        ∑ v ∈ S, r v.toNat + ∑ v ∈ S, consAmt eventsC v.toNat +
          ∑ v ∈ S, (whistC tailC highC v.toNat + (syncCr eventsC v.toNat + syncD events v.toNat +
            syncD eventsF v.toNat)) + ∑ v ∈ S, slashW t v.toNat := by
    intro S r cr each
    refine (Finset.sum_le_sum each).trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib]
  have z4 := split4 (K4 pulled counted V) (fun i => credN tailC highC i)
      (fun i => credC tailC highC i) fun v _ => by
    have := (credit_parts_le tailC highC v replayedC).1
    unfold flowCredit
    omega
  have z5 := split4 (K5 counted V) (fun i => propN tailC highC i)
      (fun i => propC tailC highC i) fun v _ => by
    have := (credit_parts_le tailC highC v replayedC).2
    unfold flowCredit
    omega
  have z6 := split4 (K6 pulled counted) (fun i => credN tailC highC i)
      (fun i => credC tailC highC i) fun v _ => by
    have := (credit_parts_le tailC highC v replayedC).1
    unfold flowCredit
    omega
  -- The other flows and the slashed keys fit their bases, once over the three classes.
  have others : ∑ v ∈ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted,
      (whistC tailC highC v.toNat + (syncCr eventsC v.toNat + syncD events v.toNat +
        syncD eventsF v.toNat)) ≤ B :=
    (sum_toNat_le (P := (K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted).image
      fun v : ValidatorIndex => v.toNat) (fun i => whistC tailC highC i +
        (syncCr eventsC i + syncD events i + syncD eventsF i))
      fun v member => Finset.mem_image_of_mem _ member).trans (hB _)
  have slashed : ∑ v ∈ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted, slashW t v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * t.slashedR :=
    flow_slash h (K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted)
  have weightOther := weighted_le (fun v : ValidatorIndex => whistC tailC highC v.toNat +
    (syncCr eventsC v.toNat + syncD events v.toNat + syncD eventsF v.toNat)) d45 d46 d56
  have weightSlash := weighted_le (fun v : ValidatorIndex => slashW t v.toNat) d45 d46 d56
  have lin := flow_lin t tailC highC eventsC events eventsF (K4 pulled counted V) (K5 counted V)
    (K6 pulled counted) (fun i => credC tailC highC i) (fun i => propC tailC highC i)
    (fun i => credC tailC highC i)
  beta_reduce at z4 z5 z6 weightOther weightSlash lin
  have aligned : t.consolidationsX % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    consolidationsX_aligned h
  have key : 0 < (∑ v ∈ K4 pulled counted V, flowK t tailC highC eventsC events eventsF v.toNat) +
      3 * (∑ v ∈ K5 counted V,
        flowK t tailC highC eventsC events eventsF v.toNat (propC tailC highC v.toNat)) +
      (∑ v ∈ K6 pulled counted, flowK t tailC highC eventsC events eventsF v.toNat) →
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
        WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := fun pos => by
    obtain ⟨i, c, found⟩ := flow_pos t tailC highC eventsC events eventsF _ _ _
      (fun i => credC tailC highC i) (fun i => propC tailC highC i)
      (fun i => credC tailC highC i) pos
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 (min_le_left _ _)))
      (flow_key h tailC highC eventsC events eventsF i c found)
  have rate : 0 < (∑ v ∈ K4 pulled counted V, flowK t tailC highC eventsC events eventsF v.toNat) +
      3 * (∑ v ∈ K5 counted V,
        flowK t tailC highC eventsC events eventsF v.toNat (propC tailC highC v.toNat)) +
      (∑ v ∈ K6 pulled counted, flowK t tailC highC eventsC events eventsF v.toNat) →
      2 ≤ t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat := fun _ => flow_rate h
  have close := flow_close preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
    (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) (min t.depth t.depthFin)
    t.depth
    (t.consolidationsX / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (3 * B)
    ((∑ v ∈ K4 pulled counted V, credN tailC highC v.toNat) +
      (∑ v ∈ K6 pulled counted, credN tailC highC v.toNat) +
      3 * (∑ v ∈ K5 counted V, propN tailC highC v.toNat))
    ((∑ v ∈ K4 pulled counted V, consAmt eventsC v.toNat) +
      (∑ v ∈ K6 pulled counted, consAmt eventsC v.toNat) +
      3 * (∑ v ∈ K5 counted V, consAmt eventsC v.toNat))
    ((∑ v ∈ K4 pulled counted V, (whistC tailC highC v.toNat + (syncCr eventsC v.toNat +
        syncD events v.toNat + syncD eventsF v.toNat))) +
      (∑ v ∈ K6 pulled counted, (whistC tailC highC v.toNat + (syncCr eventsC v.toNat +
        syncD events v.toNat + syncD eventsF v.toNat))) +
      3 * (∑ v ∈ K5 counted V, (whistC tailC highC v.toNat + (syncCr eventsC v.toNat +
        syncD events v.toNat + syncD eventsF v.toNat))))
    ((∑ v ∈ K4 pulled counted V, slashW t v.toNat) + (∑ v ∈ K6 pulled counted, slashW t v.toNat) +
      3 * (∑ v ∈ K5 counted V, slashW t v.toNat))
    t.slashedR t.depthFin _ incPos (by decide) key rate (min_le_right _ _) (min_le_left _ _)
    (by
      have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero aligned)
      omega)
    (by omega)
    (by omega)
    (lin.trans (Nat.mul_le_mul_left _ (by omega)))
  have creditLow : t.creditLow = (33 * t.depth * (t.consolidationsX /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat * t.perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
      11 * t.depth * t.otherGain +
      30 * t.depth * (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat + 1) + 9) / 10 := rfl
  rw [hOther] at creditLow
  rw [Nat.mul_assoc (t.consolidationsX / preset.EFFECTIVE_BALANCE_INCREMENT.toNat),
    Nat.mul_assoc (3 * B / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)] at creditLow
  unfold flagRate
  rw [creditLow]
  linarith

/-- A scan over sources that the gross credits hold is at most the gross credits. -/
private theorem scan_le_gross {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) (p : BalanceSource → Bool)
    (inside : ∀ s, p s = true → s = .rewards ∨ s = .slashings ∨ s = .sync) :
    (creditScan p (fun _ => false) v high tail).1 ≤ grossScan v high tail := by
  have split := creditScan_or (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync))
    (fun _ => false) p (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync) && !p s)
    (fun _ => false) (fun _ => false)
    (fun s => by
      by_cases hp : p s = true
      · simp [hp, inside s hp]
      · simp [hp])
    (fun _ => rfl) (fun s ⟨first, second⟩ => by simp [first] at second)
    (fun s h => by simp at h) v high tail
  unfold grossScan
  omega

/-- A key with a flow credit of `cred` or a whistleblower credit has a gross credit on C's run.

Or a consolidation credits it. -/
private theorem credit_gate {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) {cred : ℕ}
    (source : cred = credC tail high v.toNat ∨ cred = propC tail high v.toNat)
    (positive : 0 < cred + whistC tail high v.toNat) :
    creditedKey tail high v = true ∨
      0 < (creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v.toNat high tail).1 := by
  have prop : propN tail high v.toNat ≤ grossScan v.toNat high tail :=
    scan_le_gross tail high v.toNat _ fun s h => .inl (by simpa using h)
  have whist : whistC tail high v.toNat ≤ grossScan v.toNat high tail :=
    scan_le_gross tail high v.toNat _ fun s h => .inr (.inl (by simpa using h))
  have cn := credN_split tail high v.toNat
  have cc := credC_split tail high v.toNat
  have pc := propC_split tail high v.toNat
  by_cases cons : 0 < (creditScan (fun s => decide (s = .consolidations))
      (fun s => decide (s = .consolidations)) v.toNat high tail).1
  · exact .inr cons
  · left
    simp only [creditedKey, decide_eq_true_eq]
    rcases source with rfl | rfl <;> omega

/-- A key with a sync credit over C's replayed events has a gross credit on C's run. -/
private theorem syncCr_gross (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ℕ) (positive : 0 < syncCr eventsC v) : 0 < grossScan v highC tailC := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨-, sync⟩ := creditScan_bounds ∅
    (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) highC
    (fun _ => 0) tailC replayedC (fun e _ _ => by simp)
  have bound := sync (by simp) electra h.early
    (fun ok _ fork early replayed i => (PinSplit5.slot_syncDebit_zero fork ok early replayed i).2) v
  unfold grossScan
  unfold syncCr at positive
  omega

/-- A key with a flow credit is credited.

Or a consolidation of X, a seat debit or R's slashing takes it. -/
private theorem unit_gate (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (events eventsF : List (BalanceEvent preset)) (v : ValidatorIndex) {cred : ℕ}
    (source : cred = credC tailC highC v.toNat ∨ cred = propC tailC highC v.toNat)
    (positive : 0 < flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
      v.toNat cred) :
    creditedKey tailC highC v = true ∨ 0 < consAmt eventsC v.toNat ∨
      0 < syncD eventsF v.toNat ∨ 0 < syncD events v.toNat ∨
      (pinTerms config pulled anc fin).slashedRB v.toNat = true := by
  unfold flowCredit at positive
  by_cases credit : 0 < cred + whistC tailC highC v.toNat
  · rcases credit_gate tailC highC v source credit with credited | consolidated
    · exact .inl credited
    · exact .inr (.inl (Nat.lt_of_lt_of_le consolidated
        (scan_le_events _ _ (· = .consolidations) (by intro s; simp) tailC highC v replayedC)))
  by_cases seat : 0 < syncCr eventsC v.toNat
  · left
    have := syncCr_gross h tailC highC replayedC v.toNat seat
    simp only [creditedKey, decide_eq_true_eq]
    omega
  by_cases debitF : 0 < syncD eventsF v.toNat
  · exact .inr (.inr (.inl debitF))
  by_cases debitR : 0 < syncD events v.toNat
  · exact .inr (.inr (.inr (.inl debitR)))
  right; right; right; right
  have slash : 0 < slashW (pinTerms config pulled anc fin) v.toNat := by omega
  by_contra not
  simp [slashW, not] at slash

/-- The units of a set of keys are the unit for each key with a flow credit. -/
private theorem sum_unitK (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ) (eventsC events eventsF : List (BalanceEvent preset))
    (S : Finset ValidatorIndex) (cred : ValidatorIndex → ℕ) :
    ∑ v ∈ S, unitK t tailC high eventsC events eventsF v.toNat (cred v) =
      t.unitGain * (S.filter fun v =>
        0 < flowCredit t tailC high eventsC events eventsF v.toNat (cred v)).card := by
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold unitK
  split <;> simp_all

/-- The units of the counted keys, at their weights, fit the unit terms of `pinReserve`.

A credited key's unit takes a slot of `creditUnits`, and a seat-only key's takes a seat unit.

A key credited only by a consolidation of X takes row H's unit.

A key slashed only on R's branch takes its unit in `branchR`. -/
private theorem bud_units (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    (∑ v ∈ (K4 pulled counted V),
        unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat) +
      3 * (∑ v ∈ (K5 counted V),
          unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
            (propC tailC highC v.toNat)) +
      (∑ v ∈ (K6 pulled counted),
          unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat) ≤
      (pinTerms config pulled anc fin).creditUnits +
        3 * (pinTerms config pulled anc fin).unitGain *
          (pinTerms config pulled anc fin).consolidationsXCount +
        3 * ((pinTerms config pulled anc fin).unitGain *
          (pinTerms config pulled anc fin).slashedR) := by
  classical
  obtain ⟨N, units, slots⟩ := creditUnits_eq config pulled anc fin
  obtain ⟨d45, d46, d56, -⟩ := classes_disjoint h
  have credited := credited_classes_le h tailC highC
  have five := card_K5_le h tailC
  -- The consolidation counts read the pulled epoch as their horizon.
  obtain ⟨eventsF', replayedF'⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  have replayedC' : tailC.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsC :=
    (DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le tailC
      (high := (getCurrentEpoch pulled).toNat) (localHigh := highC) h.near endEpochC).trans
      replayedC
  set G4 := (K4 pulled counted V).filter fun v => 0 < flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (credC tailC highC v.toNat)
  set G5 := (K5 counted V).filter fun v => 0 < flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (propC tailC highC v.toNat)
  set G6 := (K6 pulled counted).filter fun v => 0 < flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (credC tailC highC v.toNat)
  have s4 : ∑ v ∈ K4 pulled counted V,
      unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * G4.card :=
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => credC tailC highC v.toNat
  have s5 : ∑ v ∈ K5 counted V,
      unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        (propC tailC highC v.toNat) =
        (pinTerms config pulled anc fin).unitGain * G5.card :=
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => propC tailC highC v.toNat
  have s6 : ∑ v ∈ K6 pulled counted,
      unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * G6.card :=
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => credC tailC highC v.toNat
  set All := K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted
  set Co := All.filter fun v => 0 < consAmt eventsC v.toNat
  set A := All.filter fun v => 0 < syncD eventsF v.toNat
  set B := All.filter fun v => 0 < syncD events v.toNat
  set Sl := All.filter fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true
  set Cr4 := (K4 pulled counted V).filter fun v => creditedKey tailC highC v = true
  set Cr5 := (K5 counted V).filter fun v => creditedKey tailC highC v = true
  set Cr6 := (K6 pulled counted).filter fun v => creditedKey tailC highC v = true
  -- A key with a unit is credited, or a consolidation, a seat debit or a slashing takes it.
  have route : ∀ (v : ValidatorIndex) (cred : ℕ), v ∈ All →
      (cred = credC tailC highC v.toNat ∨ cred = propC tailC highC v.toNat) →
      0 < flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
        v.toNat cred →
      creditedKey tailC highC v = true ∨ v ∈ Co ∪ (A ∪ B) ∪ Sl := by
    intro v cred inAll source positive
    rcases unit_gate h tailC highC replayedC events eventsF v source positive with
      credit | consolidated | debitF | debitR | slashed
    · exact .inl credit
    · exact .inr (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨inAll, consolidated⟩)))
    · exact .inr (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inAll, debitF⟩))))
    · exact .inr (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨inAll, debitR⟩))))
    · exact .inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨inAll, slashed⟩))
  have cover : G4 ∪ G5 ∪ G6 ⊆ (Cr4 ∪ Cr5 ∪ Cr6) ∪ (Co ∪ (A ∪ B) ∪ Sl) := by
    intro v member
    rcases Finset.mem_union.mp member with m45 | m6
    · rcases Finset.mem_union.mp m45 with m4 | m5
      · obtain ⟨inK, positive⟩ := Finset.mem_filter.mp m4
        rcases route v _ (Finset.mem_union_left _ (Finset.mem_union_left _ inK)) (.inl rfl)
          positive with credit | rest
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨inK, credit⟩)))
        · exact Finset.mem_union_right _ rest
      · obtain ⟨inK, positive⟩ := Finset.mem_filter.mp m5
        rcases route v _ (Finset.mem_union_left _ (Finset.mem_union_right _ inK)) (.inr rfl)
          positive with credit | rest
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨inK, credit⟩)))
        · exact Finset.mem_union_right _ rest
    · obtain ⟨inK, positive⟩ := Finset.mem_filter.mp m6
      rcases route v _ (Finset.mem_union_right _ inK) (.inl rfl) positive with credit | rest
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨inK, credit⟩))
      · exact Finset.mem_union_right _ rest
  have apart45 : Disjoint G4 G5 := Finset.disjoint_left.mpr fun v a b =>
    Finset.disjoint_left.mp d45 (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
  have apart456 : Disjoint (G4 ∪ G5) G6 := Finset.disjoint_left.mpr fun v a b => by
    rcases Finset.mem_union.mp a with a | a
    · exact Finset.disjoint_left.mp d46 (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
    · exact Finset.disjoint_left.mp d56 (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
  have total := Finset.card_le_card cover
  rw [Finset.card_union_of_disjoint apart456, Finset.card_union_of_disjoint apart45] at total
  have union1 := Finset.card_union_le (Cr4 ∪ Cr5 ∪ Cr6) (Co ∪ (A ∪ B) ∪ Sl)
  have union2 := Finset.card_union_le (Cr4 ∪ Cr5) Cr6
  have union3 := Finset.card_union_le Cr4 Cr5
  have union4 := Finset.card_union_le (Co ∪ (A ∪ B)) Sl
  have union5 := Finset.card_union_le Co (A ∪ B)
  -- The counts of the credited keys, the consolidations, the seat debits and the slashings.
  have consolidations := cons_keys_le h fromFin tailC (getCurrentEpoch pulled).toNat h.near
    (Nat.le_refl _) replayedF' replayedC' Co fun v hv => (Finset.mem_filter.mp hv).2
  have seats := debit_keys_le h fromFin tail tailC high replayed replayedF A B
    (fun v hv => (Finset.mem_filter.mp hv).2) fun v hv => (Finset.mem_filter.mp hv).2
  have slashed : Sl.card ≤ (pinTerms config pulled anc fin).slashedR :=
    slashedRB_card_le config pulled anc fin All
  have inFive : G5.card ≤ (K5 counted V).card := Finset.card_le_card (Finset.filter_subset _ _)
  have key : G4.card + G6.card + 3 * G5.card ≤ N +
      2 * ((((pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).exitingB i = true).card +
          (pinTerms config pulled anc fin).queueKeys)) +
      3 * (pinTerms config pulled anc fin).consolidationsXCount +
      3 * (pinTerms config pulled anc fin).slashedR := by
    omega
  rw [s4, s5, s6, units]
  calc (pinTerms config pulled anc fin).unitGain * G4.card +
        3 * ((pinTerms config pulled anc fin).unitGain * G5.card) +
        (pinTerms config pulled anc fin).unitGain * G6.card
      = (pinTerms config pulled anc fin).unitGain * (G4.card + G6.card + 3 * G5.card) := by ring
    _ ≤ (pinTerms config pulled anc fin).unitGain * (N +
        2 * ((((pinTerms config pulled anc fin).positions.filter fun i =>
          (pinTerms config pulled anc fin).exitingB i = true).card +
            (pinTerms config pulled anc fin).queueKeys)) +
        3 * (pinTerms config pulled anc fin).consolidationsXCount +
        3 * (pinTerms config pulled anc fin).slashedR) := Nat.mul_le_mul_left _ key
    _ = _ := by ring

/-- The arithmetic of the sync leak: the debited increments `A` of all keys fit `D` at `inc` each.

Three increments of a key fit two of the window's, since `D / (inc - 1)` bounds them.

The floors of the keys add up to at most the floor of their sum. -/
private theorem leak_arith (dF P X Q D inc A F S R SL Sig : ℕ) (hinc : 1 < inc)
    (debits : inc * A ≤ D) (floors : F ≤ inc * A * X / Q) (count : S ≤ R)
    (keys : Sig ≤ dF * (3 * P * A + F) + S * SL) :
    3 * Sig ≤ 3 * dF * (2 * P * (2 * D / (inc - 1) + 1) + 2 * D * X / Q + 1) + 3 * (R * SL) := by
  have within : A ≤ D / (inc - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr
    (le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (by rw [Nat.mul_comm]; exact debits))
  have double := Nat.mul_div_le_mul_div_assoc 2 D (inc - 1)
  have three : 3 * P * A ≤ 2 * P * (2 * D / (inc - 1) + 1) :=
    calc 3 * P * A = P * (3 * A) := by ring
      _ ≤ P * (2 * (2 * D / (inc - 1) + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have rounded : F ≤ 2 * D * X / Q := floors.trans (Nat.div_le_div_right (by
    calc inc * A * X ≤ D * X := Nat.mul_le_mul_right _ debits
      _ ≤ 2 * D * X := Nat.mul_le_mul_right _ (by omega)))
  have := Nat.mul_le_mul_left dF (Nat.add_le_add_right (Nat.add_le_add three rounded) 1)
  have := Nat.mul_le_mul_right SL count
  nlinarith

/-- A key's penalty on R's branch is at most one increment, and only a slashed key has one. -/
private theorem slashW_le (h : Setting config checks g split fin pulled anc counted V) (i : ℕ) :
    slashW (pinTerms config pulled anc fin) i ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (if (pinTerms config pulled anc fin).slashedRB i = true then 1 else 0) := by
  unfold slashW
  split_ifs
  · rw [Nat.mul_one]
    exact (Nat.le_add_right _ _).trans h.facts.slashBand
  · exact Nat.zero_le _

/-- The leak induced by the counted keys' sync debits fits `syncLeak` and the slashed keys' leak.

The envelope of a counted key reads its debits and penalty in whole increments.

A key's induced leak is that of its debited increments and of its penalty's increment.

The weights are at most three, and the debited increments of all keys fit the window's envelope.

The keys that R slashed after the finalized epoch are at most `slashedR`. -/
private theorem syncLeak_of_envelope (h : Setting config checks g split fin pulled anc counted V)
    (perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (envelope : ∀ v ∈ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted,
      ∀ z ∈ (fromFin.append tail).balancePath, effectiveAt z v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          ((syncD eventsF v.toNat + syncD events v.toNat +
              slashW (pinTerms config pulled anc fin) v.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    (∑ v ∈ (K4 pulled counted V), inducedR (pinTerms config pulled anc fin) (fromFin.append tail)
          v.toNat) +
      3 * (∑ v ∈ (K5 counted V), inducedR (pinTerms config pulled anc fin) (fromFin.append tail)
          v.toNat) +
      (∑ v ∈ (K6 pulled counted), inducedR (pinTerms config pulled anc fin) (fromFin.append tail)
          v.toNat) ≤
      (pinTerms config pulled anc fin).syncLeak +
        3 * ((pinTerms config pulled anc fin).slashedR *
          slashLeak config fork (pinTerms config pulled anc fin)) := by
  classical
  obtain ⟨d45, d46, d56, -, -, -⟩ := classes_disjoint h
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  -- the abbreviations of the pin's terms
  obtain ⟨K, hK⟩ : ∃ K, K = K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ValidatorIndex → ℕ, ∀ v, a v = (syncD eventsF v.toNat +
    syncD events v.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ValidatorIndex → ℕ, ∀ v, s v =
    if (pinTerms config pulled anc fin).slashedRB v.toNat = true then 1 else 0 := ⟨_, fun _ => rfl⟩
  have weights := weighted_le (fun v : ValidatorIndex =>
    inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat) d45 d46 d56
  rw [← hK] at weights
  have total := Finset.sum_le_sum fun v (member : v ∈ K) => by
    refine inducedR_le config pulled anc fin incPos perPos _ v.toNat (a v) (s v)
      (by rw [hs]; split_ifs <;> omega) fun z inPath => (envelope v (hK ▸ member) z inPath).trans ?_
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    have within := slashW_le h v.toNat
    rw [← hs] at within
    calc _ ≤ (syncD eventsF v.toNat + syncD events v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat * s v) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
          Nat.div_le_div_right (Nat.add_le_add_left within _)
      _ = a v + s v := by
          rw [Nat.add_mul_div_left _ _ incPos, ha]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul] at total
  have appended := DirectSafety.Apriori.Internal.balanceEvents_append fromFin tail _ replayedF
    replayed
  have epochs : (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
  have hA := (show preset.EFFECTIVE_BALANCE_INCREMENT.toNat * ∑ v ∈ K, a v ≤
      ∑ v ∈ K, ((eventsF ++ events).map (syncDebit v.toNat)).sum by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [ha, List.map_append, List.sum_append]
    exact Nat.mul_div_le _ _).trans
    ((syncDebits_window_le h (fromFin.append tail) (Nat.le_succ _) appended K).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ epochs))))
  have hS : ∑ v ∈ K, s v ≤ (pinTerms config pulled anc fin).slashedR := by
    refine Nat.le_of_mul_le_mul_left (le_trans (le_of_eq ?_)
      (slashR_le config pulled anc fin K)) incPos
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by unfold slashR; rw [hs]; split_ifs <;> simp
  have floors := (DirectSafety.Apriori.Internal.sum_div_le K
    (fun v => preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a v *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat))
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)).trans
    (Nat.div_le_div_right (le_of_eq (by rw [← Finset.sum_mul, ← Finset.mul_sum])))
  have hc : 1 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  exact weights.trans (leak_arith _ _ _ _ _ _ _ _ _ _ _ _ hc hA floors hS total)

/-- The leak that the counted keys' sync debits on R's branch induce, at their weights.

The keys that are slashed at C and not at the split are counted too, at weight one.

The keys slashed at the split that R's call reads as slashed are counted at weight three.

They are the keys of `Kc` in `bud_sync`.

It fits `syncLeak`, and the leak of one increment for each key slashed on R's branch.

The keys slashed at C alone fit `syncLeak` and one such leak for each key slashed on R's branch.

The weights of the counted classes are at most three.

So `syncLeak` pays the debits of the keys slashed at C at weight one. -/
private theorem bud_syncLeak (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    (∑ v ∈ (K4 pulled counted V), inducedR (pinTerms config pulled anc fin) (fromFin.append tail)
          v.toNat) +
      3 * (∑ v ∈ (K5 counted V), inducedR (pinTerms config pulled anc fin) (fromFin.append tail)
          v.toNat) +
      (∑ v ∈ (K6 pulled counted), inducedR (pinTerms config pulled anc fin) (fromFin.append tail)
          v.toNat) +
      (∑ v ∈ (SC pulled counted split), inducedR (pinTerms config pulled anc fin)
          (fromFin.append tail) v.toNat) +
      3 * (∑ v ∈ ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter
            (fun v => ((split.validators.data[v.toNat]?).map (·.slashed)).getD false = true ∧
              (pinTerms config pulled anc fin).slashedRB v.toNat = true),
          inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat) ≤
      (pinTerms config pulled anc fin).syncLeak +
        3 * ((pinTerms config pulled anc fin).slashedR *
          slashLeak config fork (pinTerms config pulled anc fin)) ∧
    (∑ v ∈ (SC pulled counted split), inducedR (pinTerms config pulled anc fin)
        (fromFin.append tail) v.toNat) ≤
      (pinTerms config pulled anc fin).syncLeak +
        (pinTerms config pulled anc fin).slashedR *
          slashLeak config fork (pinTerms config pulled anc fin) :=
  sorry

/-- A counted key's balance at C is at most its balance at R plus its rise and its flows.

It adds the rise of the key and the credits, flows and slacks that `rise` does not read.

The slacks are one increment for a slashing on R's branch.

They are one rounding step for a credit on C's branch.

They are one rounding step for a sync debit on R's branch or on its shared segment with C's.

The key's flows also compound, which `keyExtra` charges with its unit and its induced leak.

The start's rounding is `prefix_envelope`'s floor form. -/
private def keyCeiling (anc : BeaconState preset fork)
    (run : Run config checks ⟨fork, fin⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ) : Prop :=
  balanceAt counted i ≤ balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
    (credC tailC highC i +
      keyExtra (pinTerms config pulled anc fin) run tailC highC eventsC events eventsF i) +
    whistC tailC highC i + (syncF events i + syncF eventsC i) +
    slashR (pinTerms config pulled anc fin) i + bandC tailC highC i +
    bandR (eventsF ++ events) i + bandX fin highC i

/-- The low-rate arm of `rise` is chosen when the depth is within the delay and the gain is low. -/
private theorem keptArm_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (i : ℕ) :
    (pinTerms config state ancestor finalizedState).keptArm i =
      (decide ((pinTerms config state ancestor finalizedState).depthFin ≤
          config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) &&
        decide (11 * (pinTerms config state ancestor finalizedState).depth *
          ((pinTerms config state ancestor finalizedState).gainRate i + 1) ≤
            (pinTerms config state ancestor finalizedState).ebUp i)) := rfl

/-- Under the guard, the window from the finalized epoch through R's horizon is under half a vector.

It is the short window of the guard, read at R's horizon. -/
private theorem depthFin_lt_half (h : Setting config checks g split fin pulled anc counted V) :
    (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat <
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, short, _⟩ := id h.guard
  change (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat + 2 <
    preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 at short
  omega

/-- A slashing penalty and the gain on it over the window fit below one increment.

The penalty leaves a downward band, which is at least a quarter of the increment.

The penalty alone gains the unit gain, as it is under ten elevenths of an increment.

The unit gain is a gain per increment over the window, and two more gwei for each epoch.

`key` bounds the gain per increment by an eleventh of an increment. -/
private theorem slash_gain_small {I db WD F P D W : ℕ} (hI : 0 < I)
    (key : 11 * D * (P * F) < WD * I) (band : I ≤ 4 * db) (slashBand : W + db ≤ I)
    (window : 88 * D ≤ 3 * I) :
    W + (D * (11 * W / (10 * I) * P * F / WD) +
      if 0 < W then D * (P * F / WD + 2) else 0) < I := by
  have zero : 11 * W / (10 * I) = 0 := Nat.div_eq_of_lt (by omega)
  have small : 11 * (D * (P * F / WD)) < I := by
    have h1 := Nat.mul_le_mul_left (11 * D) (Nat.mul_div_le (P * F) WD)
    have h2 : WD * (11 * (D * (P * F / WD))) < WD * I :=
      calc WD * (11 * (D * (P * F / WD))) = 11 * D * (WD * (P * F / WD)) := by ring
        _ ≤ 11 * D * (P * F) := h1
        _ < WD * I := key
    exact Nat.lt_of_mul_lt_mul_left h2
  rw [zero]
  split_ifs
  · rw [Nat.mul_add]
    simp only [Nat.zero_mul, Nat.zero_div, Nat.mul_zero, Nat.zero_add]
    omega
  · simp only [Nat.zero_mul, Nat.zero_div, Nat.mul_zero, Nat.zero_add]
    omega

/-- The deposit credits of some events are within `depPre` when each credited one is unslashed. -/
private theorem deposits_le_depPre (L : List (BalanceEvent preset)) (i : ℕ)
    (clean : ∀ e ∈ L, e.source = .deposits →
      keyCredit i e = 0 ∨ ¬ slashedFlagAt e.before.state i = some true) :
    ((L.filter fun e => e.source = .deposits).map (keyCredit i)).sum ≤ depPre L i := by
  induction L with
  | nil => simp [depPre]
  | cons e rest ih =>
    have tail := ih fun x member => clean x (List.mem_cons_of_mem _ member)
    unfold depPre at tail ⊢
    by_cases dep : e.source = .deposits
    · rcases clean e List.mem_cons_self dep with zero | unslashed
      · by_cases slashed : slashedFlagAt e.before.state i = some true <;>
          simp [dep, zero, slashed] <;> omega
      · simp [dep, unslashed]
        omega
    · simp [dep]
      omega

/-- The credits of C's run before a key's slashing are within the credit terms of `whistleSlack`.

They are the key's net block credits and its slot credits other than rewards, up to the step.

The net block credits are within the gross rewards, slashings and sync credits.

The sync block credits are within the key's sync credits of the whole run.

The deposits before the step are those of `depPre`, since the key is unslashed before it.

The consolidation credits are within `consAmt`. -/
private theorem credits_prefix_le (h : Setting config checks g split fin pulled anc counted V)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)}
    (replayedC : ((pre.snoc step).append post).balanceEvents highC = .ok eventsC) (i : ℕ)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    netScan i highC pre +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC pre).1 ≤
      propN ((pre.snoc step).append post) highC i + depPre eventsC i +
        whistC ((pre.snoc step).append post) highC i + syncCr eventsC i + consAmt eventsC i := by
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have aEarly : a.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le bEarly
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  -- The key is in the registry at `b`, so its position is an index.
  have inside : i < b.state.validators.data.size := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at flag
    | some _ => exact (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨v, rfl⟩ : ∃ v : ValidatorIndex, v.toNat = i := ⟨UInt64.ofNat i, by
    have := BeaconState.validators_size_lt_of_lt_glamsterdam bEarly b.state
    exact UInt64.toNat_ofNat_of_lt' (by rw [UInt64.size]; omega)⟩
  -- The whole run is the prefix and the rest, and so are its events.
  obtain ⟨e1, replayed1⟩ := pre.balanceEvents_ok aEarly highC
  obtain ⟨e2, replayed2⟩ := ((Run.nil.snoc step).append post).balanceEvents_ok h.early highC
  have whole : (pre.snoc step).append post = pre.append ((Run.nil.snoc step).append post) := by
    rw [Run.append_assoc]
    rfl
  rw [whole] at replayedC ⊢
  rw [DirectSafety.Apriori.Internal.balanceEvents_append pre _ highC replayed1 replayed2]
    at replayedC
  obtain rfl := Except.ok.inj replayedC
  -- The prefix's credits are within its sources.
  obtain ⟨gross, net, -⟩ := credits_le_sources (toFin.append fromFin) h.genesis pre aEarly electra
    v.toNat highC replayed1
  have cons := scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp) pre highC v
    replayed1
  have deps := scan_le_events (fun _ => false) (fun s => decide (s = .deposits)) (· = .deposits)
    (by intro s; simp) pre highC v replayed1
  -- Each deposit of the prefix that credits the key finds it unslashed.
  have clean : ∀ e ∈ e1, e.source = .deposits →
      keyCredit v.toNat e = 0 ∨ ¬ slashedFlagAt e.before.state v.toNat = some true := by
    intro e member dep
    rcases run_located pre electra aEarly highC replayed1 e member dep with
      unconditional | ⟨u, w, ok, es, contains, replayedEs, inEs, -⟩
    · have := unconditional v.toNat
      unfold keyCredit
      omega
    · right
      intro slashed
      obtain ⟨p1, p2, -⟩ := pre.contains_split (Step.slot ok) contains
      have wEarly : w.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps p2.chainSteps) aEarly
      have holds := Run.invariant h.genesis.invariant ((toFin.append fromFin).append p1)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, one, two, -⟩ :=
        (Step.balanceEvents_sites (Step.slot ok) wEarly holds h.caps.compounding replayedEs) e inEs
      obtain ⟨x, found, flagged⟩ : ∃ x, e.before.state.validators.data[v.toNat]? = some x ∧
          x.slashed = true := by
        unfold slashedFlagAt at slashed
        cases hx : e.before.state.validators.data[v.toNat]? <;> simp_all
      obtain ⟨y, foundA, flagA⟩ :=
        ((one.trans two).trans p2.slashedPersistence) v.toNat x found flagged
      simp [foundA, flagA] at flag
  have depPreOk := deposits_le_depPre e1 v.toNat clean
  have cSplit := credC_split pre highC v.toNat
  have nSplit := credN_split pre highC v.toNat
  have propSplit := creditScan_append (fun s => decide (s = .rewards)) (fun _ => false) v.toNat
    highC pre ((Run.nil.snoc step).append post)
  have whistSplit := creditScan_append (fun s => decide (s = .slashings)) (fun _ => false) v.toNat
    highC pre ((Run.nil.snoc step).append post)
  unfold propN whistC credC credN at *
  simp only [depPre, syncCr, consAmt, List.filter_append, List.map_append, List.sum_append] at *
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The closing of the per-key core of the rise, for a key on its kept arm with any cap.

Its balance on C's branch is bounded by `Bc`, and the effective balance by `stay`.

`Bc` adds up R's balance and the leak at the largest effective balance.

It adds the debits and slack on R's runs, and the credits and gains of C's run.

R's rise closes it, up to the flows and the bands that pay the rounding.

A key with no band has no credits, and its flows are at most its initial penalty and their gain.

The cap enters only through `stay` and `cappedC`, which the cap arms prove.

`cappedC` is the premise `capped` of `rise_close`.

It says the effective balance at C is at most the cap that `capFor` reads.

An arm with a frozen cap proves it as a constant. -/
private theorem key_close (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC events eventsF : List (BalanceEvent preset)} (v : ValidatorIndex)
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (Df D q gc Cr M Bc capHigh : ℕ)
    (hDf : Df = (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    (hD : D = min (pinTerms config pulled anc fin).depth Df)
    (hq : q = (pinTerms config pulled anc fin).gainRate v.toNat)
    (hM : M = ((fromFin.append tail).balancePath.map fun z => effectiveAt z v.toNat).foldl max 0)
    (hform : gc = D * (11 * ((Cr + (events.map (syncDebit v.toNat)).sum +
          (eventsF.map (syncDebit v.toNat)).sum) +
        slashW (pinTerms config pulled anc fin) v.toNat + D * q + D) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat))
    (hBc : Bc = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (Df * (pinTerms config pulled anc fin).leakAt M v.toNat +
          (dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1) -
            dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1))) +
      ((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum +
        slashW (pinTerms config pulled anc fin) v.toNat) + (Cr + (gc + (D * q + D))))
    (rateLow : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRate v.toNat + 1) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat)
    (maxLe : M ≤ (pinTerms config pulled anc fin).ebUp v.toNat +
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((syncD eventsF v.toNat + syncD events v.toNat +
            slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (stay : balanceAt counted v.toNat = balanceAt pulled v.toNat ∨
      (balanceAt counted v.toNat ≤ Bc + preset.downwardBand ∧
        balanceAt counted v.toNat ≤ max (balanceAt fin v.toNat)
          (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh)))
    (cappedC : balanceAt counted v.toNat ≤
      capForOf (pinTerms config pulled anc fin) pulled v.toNat)
    (creditsLe : Cr ≤ credC tailC highC v.toNat + whistC tailC highC v.toNat +
      (eventsC.map (syncCredit v.toNat)).sum)
    (noCredit : bandC tailC highC v.toNat = 0 → bandX fin highC v.toNat = 0 → Cr = 0) :
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- the gain of the flows, and of the base stake, is the flow gain with a unit and the base gain
  have alignedE0 := ebUp_aligned h v.toNat
  have hDle : D ≤ (pinTerms config pulled anc fin).depth := hD ▸ min_le_left _ _
  have hq' : q = (pinTerms config pulled anc fin).ebUp v.toNat /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
    rw [hq, hP]
    rfl
  have key := rate_per_increment preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P
    ((pinTerms config pulled anc fin).ebUp v.toNat) D h.bands.1 (by decide) alignedE0
    (by
      rw [← hq', hq]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 hDle)) rateLow)
  obtain ⟨toFin⟩ := h.toFin
  have hperIncrement : (pinTerms config pulled anc fin).perIncrement = P := by
    rw [hP]
    rfl
  have hunit : (pinTerms config pulled anc fin).unitGain =
      (pinTerms config pulled anc fin).depth * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat + 2) := by
    rw [← hperIncrement]
    rfl
  have hdf : (pinTerms config pulled anc fin).depthFin = Df := hDf.symm
  have hDF : D ≤ Df := hD ▸ min_le_right _ _
  obtain ⟨Zk, hZk⟩ : ∃ Zk, Zk = Cr + (events.map (syncDebit v.toNat)).sum +
      (eventsF.map (syncDebit v.toNat)).sum + slashW (pinTerms config pulled anc fin) v.toNat :=
    ⟨_, rfl⟩
  have gcEq : gc = D * (11 * (Zk + (D * q + D)) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
      P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) := by
    rw [hform, hZk, Nat.add_assoc _ (D * q) D]
  have gainBound : gc + (D * q + D) ≤
      flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat +
        unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat +
        Df * ((11 * q + 9) / 10 + 3) := by
    have split := flow_gain_split preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P D
      (min (pinTerms config pulled anc fin).depth (pinTerms config pulled anc fin).depthFin) Df q Zk
      (flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat)
      key (le_of_eq (by rw [hD, hdf])) hDF
      (by rw [hZk]; unfold flowCredit syncCr syncD; omega)
    unfold flowGain unitK
    rw [hunit, hperIncrement, gcEq]
    refine le_trans split (Nat.add_le_add_right (Nat.add_le_add_left ?_ _) _)
    split_ifs
    · exact Nat.mul_le_mul_right _ (min_le_left _ _)
    · exact Nat.le_refl _
  -- R's rise closes the balance ceiling of C's run, up to the flows and their slack
  obtain ⟨H, hH⟩ : ∃ H, H = riseTop (pinTerms config pulled anc fin) pulled fin v.toNat :=
    ⟨_, rfl⟩
  have induced : Df * (pinTerms config pulled anc fin).leakAt M v.toNat ≤
      Df * (pinTerms config pulled anc fin).leak v.toNat +
        inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat := by
    unfold inducedR
    rw [hdf, ← hM, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by
      have := (pinTerms config pulled anc fin).leak v.toNat
      show _ ≤ (pinTerms config pulled anc fin).leakAt ((pinTerms config pulled anc fin).ebUp
        v.toNat) v.toNat + _
      omega)
  have hHeq : H = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
      Df * ((11 * q + 9) / 10 + 3 + (pinTerms config pulled anc fin).leak v.toNat) +
        (dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) := by
    rw [hH, hq, hDf]
    unfold riseTop
    simp only [electra, ↓reduceDIte]
    rfl
  have gap : Bc ≤ H + (syncD eventsF v.toNat + syncD events v.toNat +
      slashW (pinTerms config pulled anc fin) v.toNat + Cr +
      inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
      (flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat +
        unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat)) := by
    unfold syncD
    rw [hBc, hHeq, Nat.mul_add (Df) _ _]
    omega
  -- the closing: R's rise, the flows, and the bands that pay the rounding
  have alignedC : balanceAt counted v.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    FloorTrace.effective_aligned (toFin.append (fromFin.append tailC)) h.genesis h.aligned v.toNat
  have close : ∀ S U : ℕ, Bc ≤ H + S → (S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
      (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) →
      balanceAt counted v.toNat ≤
        balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat + S + U :=
    fun S U ceiling slack => rise_close config pulled anc fin v.toNat hH h.bands.1 kept alignedC
      (Nat.le_max_left _ _) stay (Nat.le_trans cappedC (by omega)) ceiling slack
  have fSyncE : syncD events v.toNat ≤ syncF events v.toNat := by
    rw [syncF_eq]; unfold syncD; omega
  have fSyncC : (eventsC.map (syncCredit v.toNat)).sum ≤ syncF eventsC v.toNat := by
    rw [syncF_eq]; omega
  have fK : flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
      flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat := by
    simp [flowK, kept]
  have hWdb : slashW (pinTerms config pulled anc fin) v.toNat + preset.downwardBand ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    unfold slashW
    split
    · exact h.facts.slashBand
    · simpa using h.facts.below.le
  have fW : slashW (pinTerms config pulled anc fin) v.toNat ≤
      slashR (pinTerms config pulled anc fin) v.toNat := by
    have := hWdb
    unfold slashW at this ⊢
    unfold slashR
    split_ifs at this ⊢ <;> omega
  have incPos : 1 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  have bandsOne : 0 < bandC tailC highC v.toNat ∨ 0 < bandR (eventsF ++ events) v.toNat ∨
      0 < bandX fin highC v.toNat → preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        bandC tailC highC v.toNat + bandR (eventsF ++ events) v.toNat +
          bandX fin highC v.toNat + 1 := by
    have up := h.bands.2
    rintro (pos | pos | pos)
    · unfold bandC at pos ⊢
      split_ifs at pos ⊢ <;> omega
    · unfold bandR at pos ⊢
      split_ifs at pos ⊢ <;> omega
    · unfold bandX at pos ⊢
      have dpos : 0 < dueAt fin highC {UInt64.ofNat v.toNat} :=
        Nat.pos_of_ne_zero fun z => by rw [z, Nat.mul_zero] at pos; exact Nat.lt_irrefl _ pos
      have := Nat.le_mul_of_pos_right preset.upwardBand dpos
      omega
  unfold keyCeiling keyExtra
  by_cases bands : 0 < bandC tailC highC v.toNat ∨ 0 < bandR (eventsF ++ events) v.toNat ∨
      0 < bandX fin highC v.toNat
  · have := close _ (bandC tailC highC v.toNat + bandR (eventsF ++ events) v.toNat +
      bandX fin highC v.toNat + (slashR (pinTerms config pulled anc fin) v.toNat -
        slashW (pinTerms config pulled anc fin) v.toNat))
      gap
      (Or.inr (Or.inl (by have := bandsOne bands; omega)))
    omega
  · simp only [not_or, not_lt, Nat.le_zero] at bands
    obtain ⟨hbC, hbR, hbX⟩ := bands
    have up := h.bands.2
    have sD0 : (eventsF.map (syncDebit v.toNat)).sum +
        (events.map (syncDebit v.toNat)).sum = 0 := by
      have := bandR_eq (eventsF ++ events) v.toNat
      simp only [List.map_append, List.sum_append] at this
      split_ifs at this <;> omega
    have Cr0 : Cr = 0 := noCredit hbC hbX
    have hW : slashW (pinTerms config pulled anc fin) v.toNat <
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      have := h.facts.bandLow
      omega
    have M0 : M ≤ (pinTerms config pulled anc fin).ebUp v.toNat := by
      have e := maxLe
      rw [Nat.div_eq_of_lt (show syncD eventsF v.toNat + syncD events v.toNat +
        slashW (pinTerms config pulled anc fin) v.toNat < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
            by unfold syncD; omega), Nat.mul_zero, Nat.add_zero] at e
      exact e
    have ind0 : inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat = 0 := by
      unfold inducedR
      rw [← hM, Nat.sub_eq_zero_of_le (leakAt_mono config pulled anc fin v.toNat M0), Nat.mul_zero]
    have hZkW : Zk = slashW (pinTerms config pulled anc fin) v.toNat := by
      rw [hZk]
      omega
    have gainNet := flow_gain_split preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P D D Df q Zk Zk key
      (Nat.le_refl _) hDF (Nat.le_refl _)
    rw [hZkW] at gainNet
    obtain ⟨εn, hεn⟩ : ∃ εn, εn =
        D * (11 * slashW (pinTerms config pulled anc fin) v.toNat /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
        (if 0 < slashW (pinTerms config pulled anc fin) v.toNat then
          D * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2)
          else 0) := ⟨_, rfl⟩
    rw [← hεn] at gainNet
    have small := slash_gain_small h.bands.1 key h.facts.bandLow hWdb (by
      have := depthFin_lt_half h
      have := h.facts.vectorSmall
      omega)
    rw [← hεn] at small
    rw [hZkW] at gcEq
    have ceilII : Bc ≤ H + (slashW (pinTerms config pulled anc fin) v.toNat + εn) := by
      rw [hBc, hHeq, Nat.mul_add Df _ _]
      omega
    have εle : εn ≤ flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
        v.toNat +
        unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat := by
      have hWle : slashW (pinTerms config pulled anc fin) v.toNat ≤
          flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat := by
        unfold flowCredit
        omega
      have hdf' : min (pinTerms config pulled anc fin).depth
          (pinTerms config pulled anc fin).depthFin = D := by rw [hdf, hD]
      unfold flowGain unitK
      rw [hdf', hperIncrement, hunit, hεn]
      refine Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.div_le_div_right
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right
          (Nat.mul_le_mul_left 11 hWle)))))) ?_
      split_ifs <;> first | exact Nat.zero_le _ | exact Nat.mul_le_mul_right _ hDle | omega
    have slack : slashW (pinTerms config pulled anc fin) v.toNat + εn = 0 ∨
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          (slashR (pinTerms config pulled anc fin) v.toNat -
            slashW (pinTerms config pulled anc fin) v.toNat) + 1 ∨
        (slashW (pinTerms config pulled anc fin) v.toNat + εn <
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            slashW (pinTerms config pulled anc fin) v.toNat + εn +
              (slashR (pinTerms config pulled anc fin) v.toNat -
                slashW (pinTerms config pulled anc fin) v.toNat)) := by
      by_cases w0 : slashW (pinTerms config pulled anc fin) v.toNat = 0
      · left
        rw [hεn, w0]
        simp
      · right
        right
        have sl : slashR (pinTerms config pulled anc fin) v.toNat =
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
          unfold slashW at w0
          unfold slashR
          split_ifs at w0 ⊢ <;> omega
        exact ⟨small, by omega⟩
    have := close _ _ ceilII slack
    omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The per-key core of the rise for a counted voter of R's finalized registry with a frozen cap.

The key keeps its cap from the finalized state to R and C, and its rise is on the kept arm.

Its balance is bounded by the credit ceiling of C's run and the floor of R's.

The replays are read at R's epoch. -/
private theorem key_core_frozen (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (voter : v ∈ Q counted)
    (inFin : v.toNat < fin.validators.data.size)
    (frozen : PinSplit2.capAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat =
      PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (frozenC : PinSplit2.capAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat ≤
      PinSplit2.capAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have sizeFin := registryGrows_of_chainSteps fromFin.chainSteps
  have capC : PinSplit2.capAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat ≤
      PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat := by omega
  -- the floor of each state of R's run, and the largest effective balance on it
  obtain ⟨M, hM⟩ : ∃ M, M = ((fromFin.append tail).balancePath.map
      fun z => effectiveAt z v.toNat).foldl max 0 := ⟨_, rfl⟩
  have below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append post = fromFin.append tail →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M := by
    intro zs pre post cut
    obtain ⟨front, atEnd⟩ := Run.balancePath_last pre
    have path := Run.balancePath_append pre post
    rw [cut] at path
    have member : (⟨fork, zs⟩ : ForkedBeaconState preset) ∈ (fromFin.append tail).balancePath := by
      rw [path, atEnd]
      simp
    have mapped : effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ∈
        (fromFin.append tail).balancePath.map fun z => effectiveAt z v.toNat :=
      List.mem_map.mpr ⟨_, member, rfl⟩
    rw [hM, List.foldl_max_eq_max (List.ne_nil_of_mem mapped)]
    exact Nat.le_trans (List.le_max_of_mem mapped) (Nat.le_max_right _ _)
  -- the credit ceiling of C's run, from the floor and the debits of R's
  have splitSize : v.toNat < split.validators.data.size := Nat.lt_of_lt_of_le inFin sizeFin
  have debitsM := debits_le_top h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _)
    replayedF replayed v splitSize M
    (fun pre post same => below (fromFin.append pre) post
      (by rw [← Run.append_assoc, ← same]))
  have debitsCap := debits_le_top h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _)
    replayedF replayed v splitSize
    (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (fun pre post _ => effective_le_cap_pulled h (fromFin.append pre) post v.toNat)
  have memberSplit : (⟨fork, split⟩ : ForkedBeaconState preset) ∈
      (fromFin.append tail).balancePath := by
    obtain ⟨front, atEnd⟩ := Run.balancePath_last fromFin
    rw [Run.balancePath_append, atEnd]
    simp
  have unslashed := voter_unslashed h v voter
  have late := voter_late h fromFin v voter
  have capSplit : PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat =
      PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat := by
    have := cap_le_cap_of_run h.caps fromFin h.early v.toNat
    have := cap_le_cap_of_run h.caps toPulled h.early v.toNat
    omega
  have envAll := envelope_of_voter h fromFin tail replayedF replayed v unslashed
    (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) fromFin (run_nil_append fromFin) inFin
    (effective_fin_le_ebUp h v.toNat) late
  have startEff := envAll (⟨fork, split⟩ : ForkedBeaconState preset) memberSplit
  have floorR : min (actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
      (PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (syncDebit v.toNat)).sum + slashW (pinTerms config pulled anc fin) v.toNat := by
    have := voter_floorAt h fromFin tail v unslashed Run.nil fromFin (run_nil_append fromFin)
      inFin late fromFin tail rfl replayed
    omega
  have rateLow : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRate v.toNat + 1) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat := by
    rw [keptArm_eq] at kept
    simp only [Bool.and_eq_true, decide_eq_true_eq] at kept
    exact kept.2
  obtain ⟨P, hP⟩ : ∃ P, P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat := ⟨_, rfl⟩
  obtain ⟨Cr, hCr⟩ : ∃ Cr, Cr = netScan v.toNat highC tailC +
    (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC tailC).1 :=
    ⟨_, rfl⟩
  obtain ⟨gc, hform, hgc, bound⟩ := c_ceiling h fromFin tailC highC endEpochC h.near P hP v
    splitSize (slashW (pinTerms config pulled anc fin) v.toNat) replayedC Cr hCr.symm.le
    (fun flip => absurd flip.2 (by have := flip.1; omega)) startEff floorR debitsCap rateLow
  -- the frozen cap is constant along C's run
  have capEq : ∀ z ∈ tailC.balancePath, PinSplit2.capAt z v.toNat =
      PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat := by
    intro z member
    obtain ⟨zs, rfl, ⟨r1⟩, -⟩ := balancePath_state tailC member
    have := cap_le_cap_of_run h.caps r1 h.early v.toNat
    have := capCeil_path tailC h.caps h.early (Nat.le_refl _) v.toNat _ member
    omega
  have bound : ∀ z ∈ tailC.balancePath,
      min (actualBalanceAt z v.toNat)
        (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (syncDebit v.toNat)).sum + slashW (pinTerms config pulled anc fin) v.toNat +
        Cr + (gc + (min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).gainRate v.toNat +
          min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat))) := by
    intro z member
    have := bound z member
    rw [capEq z member] at this
    have := Nat.min_le_left
      (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (syncDebit v.toNat)).sum + slashW (pinTerms config pulled anc fin) v.toNat)
      (PinSplit2.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
    omega
  -- the names of the parts of the ceilings
  obtain ⟨Df, hDf⟩ : ∃ Df, Df = (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth Df := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (pinTerms config pulled anc fin).gainRate v.toNat := ⟨_, rfl⟩
  rw [← hDf, ← hD, ← hq] at hform hgc bound
  rw [← hDf] at debitsM
  -- R's run has the ceiling on its balance, and C's run adds its credits and gains
  have onR : ∀ z ∈ (fromFin.append tail).balancePath,
      min (actualBalanceAt z v.toNat)
          (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (Df * (pinTerms config pulled anc fin).leakAt M v.toNat +
            (dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
              dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1))) +
          ((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum +
            slashW (pinTerms config pulled anc fin) v.toNat) := by
    intro z member
    obtain ⟨r1, r2, cutZ⟩ := balancePath_endpoint (fromFin.append tail)
      (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) member
    obtain ⟨zf, zs⟩ := z
    have same : fork = zf := (fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
    subst same
    have capLow := cap_le_cap_of_run h.caps r1 h.early v.toNat
    have := prefix_ceiling h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _) replayedF
      replayed v (slashW (pinTerms config pulled anc fin) v.toNat) M below r1 r2 cutZ
      (Nat.le_trans inFin (registryGrows_of_chainSteps r1.chainSteps))
      (fun ok => voter_floorAt h fromFin tail v unslashed Run.nil fromFin
        (run_nil_append fromFin) inFin late r1 r2 cutZ ok)
    rw [hDf]
    omega
  obtain ⟨Bc, hBc⟩ : ∃ Bc, Bc = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset)
        v.toNat + (Df * (pinTerms config pulled anc fin).leakAt M v.toNat +
          (dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
            dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1))) +
      ((eventsF.map (syncDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum +
        slashW (pinTerms config pulled anc fin) v.toNat) + (Cr + (gc + (D * q + D))) :=
    ⟨_, rfl⟩
  have onC : ∀ z ∈ (fromFin.append tailC).balancePath,
      min (actualBalanceAt z v.toNat)
        (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) ≤ Bc := by
    intro z member
    rw [Run.balancePath_append] at member
    rcases List.mem_append.mp member with front | later
    · have inR : z ∈ (fromFin.append tail).balancePath := by
        rw [Run.balancePath_append]
        exact List.mem_append_left _ front
      have := onR z inR
      omega
    · have := bound z (List.mem_of_mem_tail later)
      omega
  have stay := key_stay h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) fromFin tail
    tailC v.toNat inFin Bc _
    (fun z member => by
      have := capCeil_path (fromFin.append tailC) h.caps h.early (Nat.le_refl _) v.toNat z member
      have := onC z member
      omega)
    (fun z member => Nat.le_trans (by
      have := capCeil_path (fromFin.append tail) h.caps h.early (Nat.le_refl _) v.toNat z member
      omega) (onR z member))
  have cappedC : balanceAt counted v.toNat ≤
      capForOf (pinTerms config pulled anc fin) pulled v.toNat :=
    Nat.le_trans (effective_le_cap_at (toFin.append (fromFin.append tailC)) h.genesis h.caps
      h.early v.toNat) (Nat.le_trans capC
      (capAt_le_capForOf _ pulled v.toNat (capAt_le_capMax h.caps electra v.toNat)))
  have maxLe : M ≤ (pinTerms config pulled anc fin).ebUp v.toNat +
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((syncD eventsF v.toNat + syncD events v.toNat +
            slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    have mapped : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ∈
        (fromFin.append tail).balancePath.map fun z => effectiveAt z v.toNat :=
      List.mem_map.mpr ⟨_, memberSplit, rfl⟩
    rw [hM, List.foldl_max_eq_max (List.ne_nil_of_mem mapped)]
    refine Nat.max_le.2 ⟨Nat.zero_le _, (List.max_le_iff (List.ne_nil_of_mem mapped)).2 ?_⟩
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact envAll z hz
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨credits, netLe, creditsSlot⟩ := credits_le_sources (toFin.append fromFin) h.genesis tailC
    h.early electra v.toNat highC replayedC
  have creditsLe : Cr ≤ credC tailC highC v.toNat + whistC tailC highC v.toNat +
      (eventsC.map (syncCredit v.toNat)).sum := by
    rw [hCr]
    omega
  have noCredit : bandC tailC highC v.toNat = 0 → bandX fin highC v.toNat = 0 → Cr = 0 := by
    intro hbC hbX
    have up := h.bands.2
    have incPos : 1 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      have := h.facts.incrementSize
      omega
    have scans : netScan v.toNat highC tailC = 0 ∧
        (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC).1 =
          0 := by
      unfold bandC at hbC
      split_ifs at hbC <;> omega
    have hdue : dueAt fin highC {v} = 0 := by
      unfold bandX at hbX
      rw [UInt64.ofNat_toNat] at hbX
      rcases Nat.eq_zero_or_pos (dueAt fin highC {v}) with z | p
      · exact z
      · have := Nat.le_mul_of_pos_right preset.upwardBand p
        omega
    have c0 := consAmt_zero h fromFin replayedF tailC highC endEpochC replayedC v hdue
    have consScan : (creditScan (fun _ => false) (fun s => decide (s = .consolidations))
        v.toNat highC tailC).1 ≤ consAmt eventsC v.toNat :=
      scan_le_events (fun _ => false) (fun s => decide (s = .consolidations))
        (· = .consolidations) (by intro s; simp) tailC highC v replayedC
    have parts := creditScan_or (fun _ => false)
      (fun s => decide (s = .consolidations ∨ s = .deposits)) (fun _ => false) (fun _ => false)
      (fun s => decide (s = .deposits)) (fun s => decide (s = .consolidations))
      (fun s => by simp) (fun s => by cases s <;> decide) (fun s h => by simp at h)
      (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide)) v.toNat highC
      tailC
    omega
  exact key_close h tail fromFin tailC highC v kept P hP Df D q gc Cr M Bc _ hDf hD hq hM hform hBc
    rateLow maxLe stay cappedC creditsLe noCredit

/-- The per-key core of the rise for a counted voter of R's finalized registry whose cap moves.

The key's cap rises on R's branch after the finalized state, or on C's branch.

Its credentials switch to compounding at a step of one of the runs.

The replays are read at R's epoch. -/
private theorem key_core_flip (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (voter : v ∈ Q counted)
    (inFin : v.toNat < fin.validators.data.size)
    (moves : ¬ (PinSplit2.capAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat =
        PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat ∧
      PinSplit2.capAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat ≤
        PinSplit2.capAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat))
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat :=
  sorry

/-- A key off the kept arm rises by its whole headroom to the largest cap.

Within the withdrawal delay, the kept arm fails only at the gain test, which `lowRate` repeats.

So `capFor` reads the largest cap. -/
private theorem rise_of_notKept (h : Setting config checks g split fin pulled anc counted V) (i : ℕ)
    (notKept : ¬ (pinTerms config pulled anc fin).keptArm i = true) :
    (pinTerms config pulled anc fin).rise i =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat - balanceAt pulled i := by
  have shallow := h.shallow
  unfold pinTerms at notKept ⊢
  simp only at notKept ⊢
  rw [ite_eq_right notKept]
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at notKept
  rw [ite_eq_right]
  intro low
  exact notKept shallow (of_decide_eq_true (Bool.and_eq_true_iff.mp low).2)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of the split's registry that is off the kept arm is bounded by the largest cap.

Its rise is its whole headroom, so the bound reads the largest cap at each step of C's branch. -/
private theorem registry_headroom (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (notKept : ¬ (pinTerms config pulled anc fin).keptArm i = true) (slack : ℕ) :
    effectiveAt a i ≤ whistleEnv (pinTerms config pulled anc fin) pulled anc i + slack := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨pre, -, -, aEarly, -⟩ := Run.contains_step_facts member h.early
  have capped := PinSplit5.effectiveAt_le_capMax ((shared.append fromFin).append pre) h.genesis
    h.caps aEarly i
  have headroom := rise_of_notKept h i notKept
  unfold whistleEnv
  split_ifs <;> omega

/-- The per-key core of the rise for a key on the headroom arm.

Its rise is its whole headroom, to the largest cap.

The cap holds the balance on C's branch, whatever the replays read. -/
private theorem key_core_headroom (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (v : ValidatorIndex)
    (notKept : ¬ (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat := by
  obtain ⟨shared⟩ := h.toFin
  have capped := PinSplit5.effectiveAt_le_capMax (shared.append (fromFin.append tailC))
    h.genesis h.caps h.early v.toNat
  have headroom := rise_of_notKept h v.toNat notKept
  have countedLe : balanceAt counted v.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := capped
  unfold keyCeiling
  omega

/-- The per-key core of the rise for a counted voter created after the finalized state.

R's registry holds the key beyond the finalized registry.

The replays are read at R's epoch. -/
private theorem key_core_created (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (voter : v ∈ Q counted)
    (inside : v.toNat < pulled.validators.data.size)
    (created : fin.validators.data.size ≤ v.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat :=
  sorry

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The per-key core of the rise.

A key of R's registry rises from R to C by at most its rise term.

It also rises by the credits and slacks that `rise` does not read.

The slacks are one increment for a slashing on R's branch.

They are one rounding step for a credit on C's branch or a sync debit on R's.

The key's flows also compound, which `keyExtra` charges with its unit and its induced leak.

`keyExtra` also holds the key's sync debits on the shared segment.

The start's rounding is `prefix_envelope`'s floor form. -/
private theorem key_core (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (i : ℕ) (inside : i < pulled.validators.data.size)
    (voter : (UInt64.ofNat i : ValidatorIndex) ∈ Q counted) :
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF i := by
  classical
  have calledNat := UInt64.le_iff_toNat_le.mp h.called
  -- the replays are read at R's epoch
  have replayedF' : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF := by
    rw [balanceEvents_eq_of_endpoint_le fromFin (localHigh := high) (by simp only; omega)
      (by simp only; omega)]
    exact replayedF
  have replayed' : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events := by
    rw [balanceEvents_eq_of_endpoint_le tail (localHigh := high) (by simp only; omega)
      (by simp only; omega)]
    exact replayed
  -- the key as a validator index
  have limit := BeaconState.registryWithinLimit_of_lt h.early pulled
  unfold BeaconState.RegistryWithinLimit at limit
  have limitBound := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  have below : i < 2 ^ 64 := by omega
  generalize hv : (UInt64.ofNat i : ValidatorIndex) = v at voter
  have hvi : v.toNat = i := by
    rw [← hv]
    exact UInt64.toNat_ofNat_of_lt' below
  subst hvi
  by_cases kept : (pinTerms config pulled anc fin).keptArm v.toNat = true
  · by_cases inFin : v.toNat < fin.validators.data.size
    · by_cases frozen : PinSplit2.capAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat =
          PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat ∧
        PinSplit2.capAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat ≤
          PinSplit2.capAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat
      · exact key_core_frozen h tail replayed' fromFin replayedF' tailC highC endEpochC
          replayedC v voter inFin frozen.1 frozen.2 kept
      · exact key_core_flip h tail replayed' fromFin replayedF' tailC highC endEpochC replayedC
          v voter inFin frozen kept
    · exact key_core_created h tail replayed' fromFin replayedF' tailC highC endEpochC replayedC
        v voter inside (Nat.le_of_not_lt inFin) kept
  · exact key_core_headroom h tail fromFin tailC highC v kept

/-- D-7 (rise): other keys active in both. -/
theorem stub_N (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cN pulled counted V ≤ ((∑ v ∈ (K4 pulled counted V), ((pinTerms config pulled anc fin).rise v.toNat +
      (credC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) + whistC tailC highC v.toNat +
      (syncF events v.toNat + syncF eventsC v.toNat) +
      slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
      bandR (eventsF ++ events) v.toNat + bandX fin highC v.toNat)) : ℕ) := by
  have early := h.early
  have term : ∀ v ∈ K4 pulled counted V, ((eC counted v : ℤ) - eR pulled v) ≤
      (((pinTerms config pulled anc fin).rise v.toNat +
        (credC tailC highC v.toNat +
            keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
        whistC tailC highC v.toNat + (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR (eventsF ++ events) v.toNat + bandX fin highC v.toNat : ℕ) : ℤ) := by
    intro v member
    have active : v ∈ AR pulled := (Finset.mem_filter.mp member).2.1
    obtain ⟨w, found, -⟩ := active_of_activeVoters early (s := pulled) active
    have core := key_core h tail high endEpoch replayed fromFin replayedF tailC highC endEpochC
      replayedC v.toNat (Array.getElem?_eq_some_iff.mp found).1
      (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp member).2.2.1)
    simp only [eC, eR]
    push_cast
    unfold keyCeiling at core
    zify at core
    omega
  have eq : cN pulled counted V =
      ∑ v ∈ K4 pulled counted V, ((eC counted v : ℤ) - eR pulled v) := by
    unfold cN
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [K4]
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [U, AC, AR, Q, Finset.mem_union]
    tauto
  rw [eq]
  refine le_trans (Finset.sum_le_sum term) (le_of_eq ?_)
  exact (Nat.cast_sum _ _).symm

/-- The charge of a charged key of `K5`: the run splits at the step that starts its exit.

The charge is the key's effective balance before that step.

It counts as `exitQ`, since a key of `K5` exits at C's epoch. -/
private theorem K5_charge_site (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ K5 counted V) (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    ∃ (a b : ForkedBeaconState preset) (pre : Run config checks ⟨fork, split⟩ a)
      (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩),
      (pre.snoc step).append post = tailC ∧
        step.departureCharges.any (·.index == v.toNat) = true ∧
        (∀ w, a.state.validators.data[v.toNat]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH) ∧
        v.toNat < a.state.validators.data.size ∧
        exitQ tailC v.toNat = effectiveAt a v.toNat := sorry

/-- The start-of-epoch half of the charge arm, for a charge after the split's epoch.

The run to the charge crosses an epoch boundary, at the state `c`.

There the key's balance is within the upward band of its effective balance.

The effective balance stays to the charge.

Over the rest of that epoch the balance rises at most by the key's block credits.

The key is active at the charge step, so it is in the registry at `c`.

The fork of `a` is before Gloas, since `post` runs on to C.

The epoch of `a` is at most `highC + 1`, since `post` runs on to C. -/
private theorem charge_epoch_start (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩) (i : ℕ)
    (inside : i < a.state.validators.data.size)
    (unset : ∀ w, a.state.validators.data[i]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH)
    (started : (getCurrentEpoch split).toNat < (getCurrentEpoch a.state).toNat)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (charged : step.departureCharges.any (·.index == i) = true) :
    ∃ (c : ForkedBeaconState preset) (before : Run config checks ⟨fork, split⟩ c)
      (r : Run config checks c a), before.append r = pre ∧ i < c.state.validators.data.size ∧
      getCurrentEpoch c.state = getCurrentEpoch a.state ∧ effectiveAt c i = effectiveAt a i ∧
      min (actualBalanceAt c i) (PinSplit2.capAt c i) ≤ effectiveAt c i + preset.upwardBand ∧
      (effectiveAt c i < PinSplit2.capAt c i →
        actualBalanceAt c i ≤ effectiveAt c i + preset.upwardBand) ∧
      actualBalanceAt a i ≤ actualBalanceAt c i + netScan i highC r +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC r).1 := sorry

/-- The switch case of the start of the epoch.

A key at its cap that switches to compounding in the epoch keeps at most the old cap of balance.

The switch moves the balance beyond the old cap into the pending deposits.

The step that switches also takes the block credits that follow the switch in it.

So the credits are the gross ones: the net rise of that step can be zero while a credit is not.

The lemmas are `Run.flip_split` and `step_flip_min`. -/
private theorem charge_flip (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) {c a : ForkedBeaconState preset}
    (toC : Run config checks ⟨fork, fin⟩ c) (r : Run config checks c a) (i : ℕ)
    (inside : i < c.state.validators.data.size)
    (same : getCurrentEpoch c.state = getCurrentEpoch a.state)
    (early : a.fork < .glamsterdam) (endEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1)
    (flipped : PinSplit2.capAt c i ≠ PinSplit2.capAt a i)
    (atCap : ¬ effectiveAt c i < PinSplit2.capAt c i) :
    min (actualBalanceAt a i) (PinSplit2.capAt a i) ≤ effectiveAt c i + grossScan i highC r +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC r).1 := sorry

/-- The net credits of a run are at most its gross credits. -/
private theorem netScan_le_grossScan {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (electra : .pectra ≤ x.fork)
    (i high : ℕ) : netScan i high tail ≤ grossScan i high tail := sorry

/-- The exact rise of a charged key's balance after its charge.

The cap is fixed from the state `b` after the step that starts the exit.

The step itself can switch the key to compounding: one payload can switch it, then start its exit.

So the cap is at most `capAt b` on the whole run, and on `post`.

From `a` the balance rises by the exact epoch rewards of the steps from the charge on.

Those are the rewards that `riseScan` sums.

It also rises by the block credits, and by the credits of the slot steps other than the rewards.

From `b` it rises by the same rewards and the credits of `post`. -/
private theorem charge_rise_fold (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩) (i : ℕ)
    (charged : step.departureCharges.any (·.index == i) = true) :
    (∀ z ∈ ((Run.nil.snoc step).append post).balancePath,
      PinSplit2.capAt z i ≤ PinSplit2.capAt b i) ∧
    (∀ z ∈ post.balancePath, PinSplit2.capAt z i ≤ PinSplit2.capAt b i) ∧
    (∀ z ∈ ((Run.nil.snoc step).append post).balancePath, actualBalanceAt z i ≤
      actualBalanceAt a i + (riseScan i highC ((pre.snoc step).append post)).2 +
        netScan i highC ((Run.nil.snoc step).append post) +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC
          ((Run.nil.snoc step).append post)).1) ∧
    ∀ z ∈ post.balancePath, actualBalanceAt z i ≤
      actualBalanceAt b i + (riseScan i highC ((pre.snoc step).append post)).2 +
        netScan i highC post +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC post).1 := sorry

/-- The credits of a charged key from the epoch's start are those of `propC`, `whistC` and sync.

The credits before the charge are the gross ones, which bound the net ones.

The first bound adds the credits of the run from the charge on, read net.

The second bound adds the whole credits of the charge step, then those of `post`, read net.

It needs the charge step to be a block step.

A slot step's whole credits hold its epoch rewards, which none of the three sources pays.

None is a deposit.

The key's deposits are postponed from the step that starts its exit on.

That is `Run.exiting_deposit_credit_zero`.

No deposit is applied in the rest of the epoch before it. -/
private theorem charge_credits (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (member : v ∈ K5 counted V)
    {a b c : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩)
    (site : (pre.snoc step).append post = tailC)
    (charged : step.departureCharges.any (·.index == v.toNat) = true)
    (before : Run config checks ⟨fork, split⟩ c) (r : Run config checks c a)
    (cut : before.append r = pre) (same : getCurrentEpoch c.state = getCurrentEpoch a.state) :
    (grossScan v.toNat highC r + (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards))
        v.toNat highC r).1 +
      (netScan v.toNat highC ((Run.nil.snoc step).append post) +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC
          ((Run.nil.snoc step).append post)).1) ≤
      propC tailC highC v.toNat + whistC tailC highC v.toNat + syncF eventsC v.toNat) ∧
    ((∀ ok, step ≠ Step.slot ok) →
      grossScan v.toNat highC r + (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards))
        v.toNat highC r).1 + stepCredit (fun _ => true) (fun _ => true) v.toNat step +
      (netScan v.toNat highC post +
        (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC post).1) ≤
      propC tailC highC v.toNat + whistC tailC highC v.toNat + syncF eventsC v.toNat) := sorry

/-- A charged key of `K5` whose charge is in the split's epoch.

Its balance at the epoch's start is before the split.

So the credits since come through the shared suffix of the split's epoch.

The statement waits for the shared-suffix header, whose terms pay those credits. -/
private theorem K5_charged_split_epoch
    (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (member : v ∈ K5 counted V)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩)
    (site : (pre.snoc step).append post = tailC)
    (charged : step.departureCharges.any (·.index == v.toNat) = true)
    (inSplitEpoch : ¬ (getCurrentEpoch split).toNat < (getCurrentEpoch a.state).toNat) :
    eC counted v ≤ exitQ tailC v.toNat + riseQ tailC highC v.toNat +
      ((propC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (propC tailC highC v.toNat)) +
        whistC tailC highC v.toNat +
        (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR (eventsF ++ events) v.toNat + bandX fin highC v.toNat) := sorry

/-- A key of `K5` whose exit R reads: no charge on C's run.

Its exit is assigned at the split, so its deposits on C's run are postponed.

So `credC` is `propC`.

The rest is `key_core`. -/
private theorem K5_uncharged_key (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (member : v ∈ K5 counted V)
    (none : ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    eC counted v ≤ eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
      ((propC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (propC tailC highC v.toNat)) +
        whistC tailC highC v.toNat +
        (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR (eventsF ++ events) v.toNat + bandX fin highC v.toNat) := sorry

/-- D-4 (+ D-8 exits): other keys previous-epoch-only in C.

A key with a departure charge on C's run is at its charge plus its rise after that.

Any other key has its exit assigned before the split, so it is at its balance at R plus its rise.

Both add C's proposer credits and sync seats.

A key with a charge pays no deposit credit after it, so `propC` stands for its credits. -/
theorem stub_P (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cP pulled counted V ≤ ((∑ v ∈ (K5 counted V) with
        ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (exitQ tailC v.toNat + riseQ tailC highC v.toNat)) +
      (∑ v ∈ (K5 counted V), ((propC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (propC tailC highC v.toNat)) +
        whistC tailC highC v.toNat +
        (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR (eventsF ++ events) v.toNat + bandX fin highC v.toNat)) : ℕ) := by
  obtain ⟨shared⟩ := h.toFin
  set T : ValidatorIndex → ℕ := fun v => (propC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (propC tailC highC v.toNat)) +
        whistC tailC highC v.toNat +
        (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR (eventsF ++ events) v.toNat + bandX fin highC v.toNat with hT
  -- a charged key: its charge, the start of its epoch, and its exact rise after the charge
  have charged : ∀ v ∈ K5 counted V, (∃ c ∈ tailC.departureCharges, c.index = v.toNat) →
      eC counted v ≤ exitQ tailC v.toNat + riseQ tailC highC v.toNat + T v := by
    intro v member ch
    obtain ⟨a, b, pre, step, post, site, hcharge, unset, hin, hexit⟩ :=
      K5_charge_site h tailC member ch
    subst site
    by_cases started : (getCurrentEpoch split).toNat < (getCurrentEpoch a.state).toNat
    swap
    · exact K5_charged_split_epoch h tail high endEpoch replayed fromFin replayedF _ highC
        endEpochC replayedC member pre step post rfl hcharge started
    have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
    have aFork : a.fork = fork := fork_eq_of_run pre ((Run.nil.snoc step).append post)
      (Nat.le_refl _)
    have bFork : b.fork = fork := fork_eq_of_run (pre.snoc step) post (Nat.le_refl _)
    have aEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1 :=
      Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
        ((Run.nil.snoc step).append post).chainSteps)) endEpochC
    obtain ⟨c, before, r, cut, hc, same, effEq, hyst, hystLt, scanR⟩ :=
      charge_epoch_start h highC pre step post v.toNat hin unset started endEpochC hcharge
    subst cut
    have cFork : c.fork = fork := fork_eq_of_run before
      (r.append ((Run.nil.snoc step).append post)) (Nat.le_refl _)
    have netLe := netScan_le_grossScan (shared.append (fromFin.append before)) h.genesis r
      (aFork ▸ h.early) (cFork ▸ electra) v.toNat highC
    have start : min (actualBalanceAt a v.toNat) (PinSplit2.capAt a v.toNat) ≤
        effectiveAt a v.toNat + preset.upwardBand + (grossScan v.toNat highC r +
          (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC r).1) := by
      by_cases capEq : PinSplit2.capAt c v.toNat = PinSplit2.capAt a v.toNat
      · omega
      · by_cases lt : effectiveAt c v.toNat < PinSplit2.capAt c v.toNat
        · have := hystLt lt
          omega
        · have := charge_flip h highC (fromFin.append before) r v.toNat hc same
            (aFork ▸ h.early) aEpoch capEq lt
          omega
    obtain ⟨capAll, capPost, ceilings, ceilingsPost⟩ :=
      charge_rise_fold h highC endEpochC _ step post v.toNat hcharge
    obtain ⟨creditsAll, creditsStep⟩ := charge_credits h _ highC endEpochC replayedC member _
      step post rfl hcharge before r rfl same
    set TC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩ :=
      ((before.append r).snoc step).append post with hTC
    obtain ⟨wa, foundA⟩ : ∃ w, a.state.validators.data[v.toNat]? = some w :=
      ⟨_, Array.getElem?_eq_getElem hin⟩
    have rise : riseQ TC highC v.toNat =
        preset.upwardBand + (riseScan v.toNat highC TC).2 := by
      simp only [riseQ, (riseScan_fst _ _ _).mpr ch, ↓reduceIte]
    have slack : propC TC highC v.toNat +
        whistC TC highC v.toNat +
        syncF eventsC v.toNat ≤ T v := by
      simp only [hT]
      omega
    have eCeq : eC counted v = effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat :=
      rfl
    have final : effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat ≤
        effectiveAt a v.toNat + preset.upwardBand + (propC TC
          highC v.toNat + whistC TC highC v.toNat +
          syncF eventsC v.toNat) +
        (riseScan v.toNat highC TC).2 := by
      by_cases capEq : PinSplit2.capAt b v.toNat = PinSplit2.capAt a v.toNat
      · -- no switch at the charge step: the rise is read from `a`
        have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax
          (shared.append (fromFin.append (before.append r))) h.genesis h.caps (aFork ▸ h.early)
          foundA
        have startCap : effectiveAt a v.toNat ≤ PinSplit2.capAt a v.toNat := by
          simpa [PinSplit2.capAt, foundA] using capped
        have alignedCap : PinSplit2.capAt a v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
          have := congrArg UInt64.toNat
            (withdrawalMaxEffectiveBalance_aligned (fork := a.fork) h.aligned wa)
          simpa [PinSplit2.capAt, foundA, UInt64.toNat_mod] using this
        have ceil := PinSplit2.Run.effective_ceiling_of_balance_ceiling
          ((Run.nil.snoc step).append post) h.early (aFork ▸ h.fulu) v.toNat hin
          (effectiveAt a v.toNat + preset.upwardBand + (propC TC
            highC v.toNat + whistC TC highC v.toNat +
            syncF eventsC v.toNat) +
            (riseScan v.toNat highC TC).2)
          _ alignedCap startCap
          (fun z member => by have := ceilings z member; omega)
          (fun z member => by have := capAll z member; omega)
        have := ceil.1
        omega
      · -- the charge step switches the key: the rise is read from `b`
        have insideB : v.toNat < b.state.validators.data.size :=
          Nat.lt_of_lt_of_le hin
            (Run.nil.snoc step : Run config checks a b).registryLifecycle.size_le
        obtain ⟨wb, foundB⟩ : ∃ w, b.state.validators.data[v.toNat]? = some w :=
          ⟨_, Array.getElem?_eq_getElem insideB⟩
        have capMono := cap_le_cap_of_run h.caps (Run.nil.snoc step : Run config checks a b)
          (bFork ▸ h.early) v.toNat
        obtain ⟨capAmin, large⟩ : PinSplit2.capAt a v.toNat = preset.MIN_ACTIVATION_BALANCE.toNat ∧
            preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt b v.toNat := by
          have ca := capAt_of_found (aFork ▸ electra) foundA
          have cb := capAt_of_found (bFork ▸ electra) foundB
          have order := UInt64.le_iff_toNat_le.mp h.caps.compounding
          split at ca <;> split at cb <;> omega
        have flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinSplit2.capAt a v.toNat := by omega
        have epochEq := step_flip_epoch step (bFork ▸ h.early) (aFork ▸ h.fulu) v.toNat hin flat
          large
        have creditsFlip := creditsStep (step_flip_not_slot step (bFork ▸ h.early)
          (aFork ▸ h.fulu) v.toNat hin flat large)
        have effB := run_same_epoch_effective (Run.nil.snoc step : Run config checks a b)
          (bFork ▸ h.early) (UInt64.toNat_inj.mp (by omega)) v.toNat hin
        have bound := step_flip_min step (bFork ▸ h.early) (aFork ▸ h.fulu)
          ((shared.append (fromFin.append (before.append r))).invariant h.genesis.invariant)
          v.toNat flat large
        have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax
          (shared.append (fromFin.append ((before.append r).snoc step))) h.genesis h.caps
          (bFork ▸ h.early) foundB
        have startCap : effectiveAt b v.toNat ≤ PinSplit2.capAt b v.toNat := by
          simpa [PinSplit2.capAt, foundB] using capped
        have alignedCap : PinSplit2.capAt b v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
          have := congrArg UInt64.toNat
            (withdrawalMaxEffectiveBalance_aligned (fork := b.fork) h.aligned wb)
          simpa [PinSplit2.capAt, foundB, UInt64.toNat_mod] using this
        have ceil := PinSplit2.Run.effective_ceiling_of_balance_ceiling post h.early
          (bFork ▸ h.fulu) v.toNat insideB
          (effectiveAt a v.toNat + preset.upwardBand + (propC TC
            highC v.toNat + whistC TC highC v.toNat +
            syncF eventsC v.toNat) +
            (riseScan v.toNat highC TC).2)
          _ alignedCap startCap
          (fun z member => by have := ceilingsPost z member; omega) capPost
        have := ceil.1
        omega
    omega
  have eq : cP pulled counted V = ∑ v ∈ K5 counted V, (eC counted v : ℤ) := by
    unfold cP
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [K5]
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [U, AC, AR, Q, Finset.mem_union]
    tauto
  rw [eq, ← Nat.cast_sum]
  refine Nat.cast_le.mpr ?_
  show _ ≤ _ + _ + ∑ v ∈ K5 counted V, T v
  have splitE := Finset.sum_filter_add_sum_filter_not (K5 counted V)
    (fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat) (eC counted)
  have splitT := Finset.sum_filter_add_sum_filter_not (K5 counted V)
    (fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat) T
  have onCharged : ∑ v ∈ (K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
      eC counted v ≤ ∑ v ∈ (K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (exitQ tailC v.toNat + riseQ tailC highC v.toNat) +
      ∑ v ∈ (K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat, T v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v hv => charged v (Finset.mem_filter.mp hv).1
      (Finset.mem_filter.mp hv).2
  have onUncharged : ∑ v ∈ (K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges,
        c.index = v.toNat, eC counted v ≤ ∑ v ∈ (K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges,
        c.index = v.toNat, (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) +
      ∑ v ∈ (K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat, T v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v hv => ?_
    obtain ⟨member, none⟩ := Finset.mem_filter.mp hv
    exact K5_uncharged_key h tail high endEpoch replayed fromFin replayedF tailC highC endEpochC
      replayedC member none
  omega

/-- The keys of `K6` beyond R's registry are paid by the credits.

In the high regime they are also paid by `creditCap`.

They joined the registry on C's branch, so their stake is the credits that reach them.

The credits compound, which `keyExtra`'s flow gain charges, when the gain rate is low.

Otherwise `creditCap` charges the deposits up to the cap. -/
private theorem beyond_keys (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∑ v ∈ (K6 pulled counted) with pulled.validators.data.size ≤ v.toNat, eC counted v ≤
      (∑ v ∈ (K6 pulled counted) with pulled.validators.data.size ≤ v.toNat,
        (((credC tailC highC v.toNat +
            keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR (eventsF ++ events) v.toNat))) +
        (pinTerms config pulled anc fin).creditCap := sorry

/-- D-8 (activations): keys counted in C and not active at R.

A key whose exit started on R's branch after the split is inactive at R and active in C (L10).

Its stake in C is at most its stake at R and its rise.

So is the stake of a key whose exit R reads, which `exiting` and `exitingRise` charge. -/
theorem stub_J (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cJ pulled counted ≤ (((pinTerms config pulled anc fin).joining +
      (pinTerms config pulled anc fin).joinRise + (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat = true,
        (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitedRB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K6 pulled counted), ((credC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) +
        whistC tailC highC v.toNat)) +
      (∑ v ∈ (K6 pulled counted), (syncF events v.toNat + syncF eventsC v.toNat)) +
      (∑ v ∈ (K6 pulled counted),
        (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
          bandR (eventsF ++ events) v.toNat)) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K6 pulled counted), bandX fin highC v.toNat) +
      (pinTerms config pulled anc fin).creditCap) : ℕ) := by
  classical
  -- `cJ` is the stake in C of the keys of `K6`.
  have cJ_eq : cJ pulled counted = ((∑ v ∈ K6 pulled counted, eC counted v : ℕ) : ℤ) := by
    unfold cJ
    push_cast
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [Finset.mem_filter, K6, U, Finset.mem_union]
    tauto
  rw [cJ_eq, Nat.cast_le]
  -- The keys at or beyond R's registry are paid by `creditGain` and the credits.
  have beyond := beyond_keys h tail high endEpoch replayed fromFin replayedF tailC highC endEpochC
    replayedC
  -- The keys inside R's registry rise by `key_core`, and R's record puts each in a class.
  have core : ∀ v ∈ K6 pulled counted, v.toNat < pulled.validators.data.size →
      eC counted v ≤ (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          bandX fin highC v.toNat) +
        (((credC tailC highC v.toNat +
            keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR (eventsF ++ events) v.toNat)) := by
    intro v hv hin
    have := key_core (config := config) h tail high endEpoch replayed fromFin replayedF tailC highC
      endEpochC replayedC v.toNat hin
      (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp hv).2.1)
    unfold eC eR
    unfold keyCeiling at this
    omega
  have classes : ∀ v ∈ K6 pulled counted, v.toNat < pulled.validators.data.size →
      eR pulled v + (pinTerms config pulled anc fin).rise v.toNat ≤
        ((if (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
              isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true) then
            eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).lateB v.toNat = true then
            3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).exitedRB v.toNat = true then
            eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).exitingB v.toNat = true then
            eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).pendingRB v.toNat = true then
            eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0)) := by
    intro v hK hin
    obtain ⟨w, found⟩ : ∃ w, pulled.validators.data[v.toNat]? = some w :=
      ⟨_, Array.getElem?_eq_getElem hin⟩
    rcases K6_class h hK found with c | c | c | c | c
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
  -- Sum the classes over the keys inside R's registry.
  set inside := (K6 pulled counted).filter (fun v => v.toNat < pulled.validators.data.size)
    with hInside
  have partition := Finset.sum_filter_add_sum_filter_not (K6 pulled counted)
    (fun v => v.toNat < pulled.validators.data.size) (eC counted)
  have notInside : (K6 pulled counted).filter (fun v => ¬ v.toNat < pulled.validators.data.size) =
      (K6 pulled counted).filter (fun v => pulled.validators.data.size ≤ v.toNat) := by
    refine Finset.filter_congr fun v _ => ?_
    omega
  rw [notInside, ← hInside] at partition
  have insideSum : ∑ v ∈ inside, eC counted v ≤
      ∑ v ∈ inside, (((eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          bandX fin highC v.toNat) +
        (((credC tailC highC v.toNat +
            keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR (eventsF ++ events) v.toNat)))) :=
    Finset.sum_le_sum fun v hv =>
      core v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  rw [Finset.sum_add_distrib] at insideSum
  -- The consolidation bands of the inside keys are within those of `K6`.
  have bandSplit : ∑ v ∈ inside, (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
        bandX fin highC v.toNat) =
      ∑ v ∈ inside, (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) +
        ∑ v ∈ inside, bandX fin highC v.toNat := Finset.sum_add_distrib
  have bandIn : ∑ v ∈ inside, bandX fin highC v.toNat ≤
      ∑ v ∈ K6 pulled counted, bandX fin highC v.toNat :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have classSum : ∑ v ∈ inside, (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) ≤
      (∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).lateB v.toNat = true,
        (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).exitedRB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).pendingRB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) := by
    refine Nat.le_trans (Finset.sum_le_sum fun v hv =>
      classes v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2) (Nat.le_of_eq ?_)
    simp only [Finset.sum_filter]
    simp only [Finset.sum_add_distrib]
  -- Each class of inside keys is within the matching class of `K6`.
  have restrict : ∀ (p : ValidatorIndex → Prop) [DecidablePred p] (f : ValidatorIndex → ℕ),
      ∑ v ∈ inside with p v, f v ≤ ∑ v ∈ (K6 pulled counted) with p v, f v := fun p _ f =>
    Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
  have joinStake : ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true), eR pulled v ≤
      (pinTerms config pulled anc fin).joining := by
    rw [joining_eq]
    refine sum_toNat_le (fun i => balanceAt pulled i) fun v hv => ?_
    obtain ⟨hi, hj⟩ := Finset.mem_filter.mp hv
    obtain ⟨hK, hin⟩ := Finset.mem_filter.mp hi
    exact mem_positions_filter config pulled anc fin (Array.getElem?_eq_getElem hin) hj
  have joinRise : ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat ≤
      (pinTerms config pulled anc fin).joinRise := by
    rw [joinRise_eq]
    refine sum_toNat_le (fun i => (pinTerms config pulled anc fin).rise i) fun v hv => ?_
    obtain ⟨hi, hj⟩ := Finset.mem_filter.mp hv
    obtain ⟨hK, hin⟩ := Finset.mem_filter.mp hi
    exact mem_positions_filter config pulled anc fin (Array.getElem?_eq_getElem hin) hj
  have joinSplit : ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) =
      (∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true), eR pulled v) +
      ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat := Finset.sum_add_distrib
  have late := restrict (fun v => (pinTerms config pulled anc fin).lateB v.toNat = true)
    (fun v => 3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  have exited := restrict (fun v => (pinTerms config pulled anc fin).exitedRB v.toNat = true)
    (fun v => eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  have exiting := restrict (fun v => (pinTerms config pulled anc fin).exitingB v.toNat = true)
    (fun v => eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  have pending := restrict (fun v => (pinTerms config pulled anc fin).pendingRB v.toNat = true)
    (fun v => eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  -- The credits, sync flows and slash bands over `K6` split at R's registry.
  have bounds := Finset.sum_filter_add_sum_filter_not (K6 pulled counted)
    (fun v => v.toNat < pulled.validators.data.size)
    (fun v => (((credC tailC highC v.toNat +
        keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
          eventsC events eventsF v.toNat) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR (eventsF ++ events) v.toNat)))
  rw [notInside, ← hInside] at bounds
  have boundSplit : ∑ v ∈ K6 pulled counted,
      (((credC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR (eventsF ++ events) v.toNat)) =
      (∑ v ∈ K6 pulled counted, ((credC tailC highC v.toNat +
          keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) +
        whistC tailC highC v.toNat)) +
      (∑ v ∈ K6 pulled counted, (syncF events v.toNat + syncF eventsC v.toNat)) +
      ∑ v ∈ K6 pulled counted, (slashR (pinTerms config pulled anc fin) v.toNat +
        bandC tailC highC v.toNat + bandR (eventsF ++ events) v.toNat) := by
    simp only [Finset.sum_add_distrib]
  omega

end Stubs

/-! ## The top-level step, from the stubs -/

section Closure
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

private theorem sum_eq_U {S W : Finset ValidatorIndex} (sub : S ⊆ W) (f : ValidatorIndex → ℤ) :
    ∑ v ∈ S, f v = ∑ v ∈ W, if v ∈ S then f v else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr sub]

/-- The weighted drift, key by key: exact per-key algebra, no reserve term. -/
private theorem drift_le_costs (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ v ∈ Q counted, (eC counted v : ℤ)) + 3 * (∑ v ∈ V, (eR pulled v : ℤ)) -
        2 * (∑ v ∈ AC counted, (eC counted v : ℤ)) - (∑ v ∈ AR pulled, (eR pulled v : ℤ)) -
        3 * (∑ v ∈ (Q counted).filter (· ∈ V), (eC counted v : ℤ)) ≤
      2 * cV1 pulled counted V + 2 * cV2 pulled counted V + cN pulled counted V +
        3 * cP pulled counted V + cJ pulled counted + cK7 pulled counted +
        cS pulled counted V := by
  have hAR : ∀ v ∈ V, v ∈ AR pulled := fun v m => (h.voting v m).1
  have hQ := glue_quorum h
  have subQ : Q counted ⊆ U pulled counted := fun v m => by simp [U, m]
  have subAC : AC counted ⊆ U pulled counted := fun v m => by simp [U, m]
  have subAR : AR pulled ⊆ U pulled counted := fun v m => by simp [U, m]
  have subV : V ⊆ U pulled counted := fun v m => subAR (hAR v m)
  have subQV : (Q counted).filter (· ∈ V) ⊆ U pulled counted :=
    fun v m => subQ (Finset.mem_filter.mp m).1
  rw [sum_eq_U subQ, sum_eq_U subV, sum_eq_U subAC, sum_eq_U subAR, sum_eq_U subQV]
  unfold cV1 cV2 cN cP cJ cK7 cS
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro v _
  simp only [Finset.mem_filter]
  by_cases hv : v ∈ V
  · have hr := hAR v hv
    by_cases ha : v ∈ AC counted
    · have hq := hQ v hv ha
      simp [hv, ha, hr, hq]
      omega
    · by_cases hq : v ∈ Q counted <;> simp [hv, ha, hr, hq] <;> omega
  · by_cases hq : v ∈ Q counted <;> by_cases ha : v ∈ AC counted <;>
      by_cases hr : v ∈ AR pulled <;> simp [hv, ha, hr, hq] <;> omega

private theorem two_le_three {x : ℤ} {r : ℕ} (le : x ≤ r) : 2 * x ≤ 3 * (r : ℤ) := by omega

/-- The total read is at least the active stake. -/
private theorem stake_le_total {state : BeaconState preset fork} {total : Gwei}
    (ok : getTotalActiveBalance state = .ok total) :
    (∑ v ∈ activeVoters state, balanceAt state v.toNat) ≤ total.toNat := by
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok ok)
  rw [value]
  exact le_max_right _ _

/-- The top-level step, closed from the stubs.

It closes only with the extra term `3 · Σ_{(K5 counted V)} (rise + credC)`: the C-side rise of keys that are
previous-epoch-only in C weighs 3 in the drift, and no term of `pinReserve` charges it at 3. -/
theorem pinDrift_le_of_stubs (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (band : 10 * preset.upwardBand ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    {total pulledTotal : Gwei} (totalOk : getTotalActiveBalance counted = .ok total)
    (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    3 * stake (fun v => balanceAt counted v.toNat) (quorumVoters counted) +
        3 * stake (fun v => balanceAt pulled v.toNat) V ≤
      2 * total.toNat + pulledTotal.toNat + pinReserve config pulled anc fin +
        3 * stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∈ V} := by
  have key := drift_le_costs h
  have tC := stake_le_total totalOk
  have tR := stake_le_total pulledOk
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨eventsF, replayedF⟩ := fromFin.balanceEvents_ok h.early high
  have sV := two_le_three (stub_V (config := config) h high endEpoch events fromFin replayedF
    tailC highC endEpochC replayedC)
  have sN := stub_N (config := config) h tail high endEpoch replayed fromFin replayedF tailC highC
    endEpochC replayedC
  have sP := stub_P (config := config) h tail high endEpoch replayed fromFin replayedF tailC highC
    endEpochC replayedC
  have sJ := stub_J (config := config) h tail high endEpoch replayed fromFin replayedF tailC highC
    endEpochC replayedC
  -- The terms that `keyExtra` adds are paid by the flow split, the units and the induced leak.
  have f1 := flow_split (config := config) h tail high endEpoch replayed fromFin replayedF tailC
    highC endEpochC replayedC
  have u1 := bud_units (config := config) h tail high replayed fromFin replayedF tailC highC
    endEpochC replayedC
  have l1 := (bud_syncLeak (config := config) h tail high endEpoch replayed fromFin replayedF
    tailC highC endEpochC replayedC).1
  have cg := creditGain_split config pulled anc fin
  have b1 := bud_exiting (config := config) h tailC
  have b2 := bud_late (config := config) h
  have b3 := bud_queues (config := config) h tailC
  have b4 := bud_credits (config := config) h tailC highC endEpochC replayedC
  have b5 := bud_branchR (config := config) h tail high endEpoch replayed fromFin replayedF
    tailC highC endEpochC replayedC
  have b6 := bud_sync (config := config) h fromFin high replayedF tail high replayed tailC highC
    replayedC
  have b7 := bud_fall (config := config) h
  have b8 := bud_rise (config := config) h
  have b10 := bud_deposits (config := config) h tail high endEpoch replayed
  have b11 := bud_queueRise (config := config) h tailC highC endEpochC
  have b12 := bud_exitingRise (config := config) h tailC
  have b13 := bud_exitingCredits (config := config) h tailC highC replayedC
  have b17 := bud_exitingBands (config := config) h tailC highC
  have b18 := bud_pendingR (config := config) h
  have b15 := bud_consolidations (config := config) h fromFin tail high endEpoch replayed replayedF
    highLeR tailC highC endEpochC replayedC highLe band
  have b16 := bud_exitedR (config := config) (pulled := pulled) (anc := anc) (fin := fin)
    (counted := counted)
  -- `bud_consolidations` pays the band of each due entry: the counted keys' bands and V's share.
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have bandV : ∑ v ∈ K4 pulled counted V, bandX fin highC v.toNat +
        ∑ v ∈ K6 pulled counted, bandX fin highC v.toNat +
        3 * ∑ v ∈ K5 counted V, bandX fin highC v.toNat +
        3 * (preset.upwardBand * dueAt fin high V) =
      preset.upwardBand * (dueAt fin highC (K4 pulled counted V) +
        dueAt fin highC (K6 pulled counted) + 3 * dueAt fin highC (K5 counted V) +
        3 * dueAt fin high V) := by
    rw [bandX_sum fin electra highC, bandX_sum fin electra highC, bandX_sum fin electra highC]
    ring
  have b15' := Nat.le_trans (Nat.add_le_add_left (Nat.le_of_eq bandV) _) b15
  have qs := queues_split config pulled anc fin
  have b14 := bud_whistle (config := config) h fromFin high replayedF tail high endEpoch replayed
    tailC highC endEpochC replayedC
  have w4 : 0 ≤ ∑ v ∈ (K4 pulled counted V), (whistC tailC highC v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have w6 : 0 ≤ ∑ v ∈ (K6 pulled counted), (whistC tailC highC v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have b9 := bud_joining (config := config) (pulled := pulled) (anc := anc) (fin := fin)
  rw [pinReserve_eq_total]
  unfold PinTerms.total stake
  simp only [AC, AR, Q, eC, eR] at *
  simp only [keyExtra, Finset.sum_add_distrib] at sV sN sP sJ b2 b5 b6 b14 b16 b18 ⊢
  zify at *
  have syncPos : 0 ≤ ∑ x ∈ K4 pulled counted V, (syncF events x.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have syncPosC : 0 ≤ ∑ x ∈ K4 pulled counted V, (syncF eventsC x.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  -- `bud_sync` weighs the shared segment's debits of `K4` three times, and `stub_N` once.
  have syncPosF : 0 ≤ ∑ x ∈ K4 pulled counted V, (syncD eventsF x.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have xPos : 0 ≤ (33 * ((pinTerms config pulled anc fin).consolidationsX : ℤ) + 9) / 10 := by
    positivity
  have proposerPos : 0 ≤ ((pinTerms config pulled anc fin).depth : ℤ) *
      ((pinTerms config pulled anc fin).syncProposer : ℤ) := by positivity
  have unitPos : 0 ≤ ((pinTerms config pulled anc fin).unitGain : ℤ) *
      ((pinTerms config pulled anc fin).consolidationsXCount : ℤ) := by positivity
  -- A key of `K6` whose exit R reads weighs once in the drift and three times in `exiting`.
  have exitingK6 : 0 ≤ ∑ v ∈ K6 pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true, (balanceAt pulled v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have riseK6 : 0 ≤ ∑ v ∈ K6 pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true,
        ((pinTerms config pulled anc fin).rise v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  -- The keys slashed at C add a nonnegative leak to the left side of `bud_syncLeak`.
  have leakSC : 0 ≤ ∑ v ∈ SC pulled counted split,
      (inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  -- The keys slashed at the split add a nonnegative leak to the left side of `bud_syncLeak`.
  have leakKc : 0 ≤ ∑ v ∈ ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter
      (fun v => ((split.validators.data[v.toNat]?).map (·.slashed)).getD false = true ∧
        (pinTerms config pulled anc fin).slashedRB v.toNat = true),
      (inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  linarith

end Closure

end PinSum
end EthLib.Consensus.Models.Network
