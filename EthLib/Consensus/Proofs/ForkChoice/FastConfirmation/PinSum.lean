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
import Mathlib.Data.Nat.Notation
import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.BranchLedger
import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
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

open Base Uint64 Models DirectSafety

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
  drop : ℕ → ℕ

/-- `pinReserve` as the sum of its named terms, with the code's weights. -/
def PinTerms.total (t : PinTerms preset) : ℕ :=
  t.quorum + (3 * t.exiting + t.queues + t.credits + t.branchR + t.late +
    t.syncSeats + (∑ i ∈ t.positions with t.current i = true, t.rise i) + t.joinRise +
    3 * (∑ i ∈ t.positions with t.current i = true, t.fall i) +
    3 * t.exitingRise + t.exitingCredits + t.exitingBands + t.queueRise + t.reserveW + t.flagged +
    t.seatShortfall + (33 * t.consolidationsX + 9) / 10 + t.exitedR + t.pendingR + t.creditGain)

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
  let fall (i : ℕ) := if depthFin ≤ partialDelay then
      let low := min (actualFin i) (cap i) - (depthFin * (leak i + gainRate i) + partialsDue i)
      let floorC := if ebUp i ≤ low + preset.downwardBand then finEB i
        else min (finEB i) (low - low % inc)
      effective i - floorC
    else effective i
  -- Gains compound across the window, so the rise reads the gain at eleven tenths, rounded up.
  let gainScaled (i : ℕ) := (11 * gainRate i + 9) / 10
  let capFor (i : ℕ) :=
    if depth * gainScaled i < inc ∧ 11 * depth * gainRate i < ebUp i then cap i else capMax
  let rise (i : ℕ) :=
    let high := actual i + depthFin * (gainScaled i + leak i) + (partialsX i - partialsR i)
    -- Deeper than `partialDelay`, the call's branch can pay partials that neither queue holds.
    --
    -- So the rise is the key's whole headroom.
    --
    -- It is too once eleven times the gain over the depth reaches that bound on the key's balance.
    if depthFin ≤ partialDelay then
      if 11 * depth * gainRate i ≥ ebUp i then capFor i - effective i
      else
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
  -- Each sync seat of the window debits at most its envelope on each branch.
  --
  -- A key whose sync debits can lower its effective balance has debits of at least an increment.
  --
  -- So there are at most the total seat debits over `inc - 1` such keys.
  let seatExcess := 2 * (depthFin * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope) /
    (inc - 1)
  -- The window's proposer rewards are read at every key that can attest in it.
  --
  -- Such a key is activated by the next epoch and exits no earlier than the finalized epoch.
  --
  -- Its effective balance on either branch is at most its effective balance here plus its rise.
  let proposerBase := ∑ i ∈ positions with (validator i).any (fun v =>
      decide (v.activationEpoch.toNat ≤ epoch.toNat + 1) &&
        decide (finalized ≤ v.exitEpoch.toNat)),
    (effective i + rise i) / inc * perIncrement
  -- The other branch's credits can raise its attesters' effective balances above that read.
  --
  -- Each increment they add is counted, with one rounding step per credited key or seat key.
  --
  -- Each deposit the window can apply to a new key counts at the largest effective balance.
  let attesterExcess := (depositCarry + depthFin * depositChurn + consolidationsX +
      depth * proposerBase + depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope) /
        inc +
    creditedKeys + seatExcess +
    depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * (capMax / inc)
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
          decide (v.withdrawableEpoch.toNat ≤ epoch.toNat))), effective i) +
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
  -- Each key the call's branch credits or debits can move by a rounding step and a band.
  --
  -- The keys are the window's proposers and deposit recipients.
  --
  -- They also hold the sync seats of each period from the finalized epoch to the next epoch.
  --
  -- Each period crossing adds one more set of seats.
  let roundedKeys := depth * slots + depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
    preset.SYNC_COMMITTEE_SIZE.toNat *
      (((epoch.toNat + 1) / period - finalized / period + 1) + depth / period)
  -- The rounding is weighted 3 exactly once, by the `3 *` of this branch term.
  let branchR := 3 * (whistleblowerR + inc * slashedR + depth * proposerCredit +
    (inc + preset.downwardBand - 1) * roundedKeys)
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
  -- Leak over the depth from there, partials, the band and one increment of rounding are drops.
  --
  -- A partial in that state's own epoch can be paid before it, but leaves the activation balance.
  let drop (i : ℕ) := depthFin * leak i + preset.downwardBand + inc
  let lowEB (i : ℕ) := min (min (effective i) (finEB i) - partialsDue i)
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
    (effective i + rise i)
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
  let flagged := ∑ i ∈ positions with slashable i ∧
      2 * (lowEB i - ebUp i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
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
  let otherCredits := 3 * (2 * ((∑ i ∈ positions, ebUp i) +
        depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax +
        consolidationsX + depth * proposerCredit +
        depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope) /
          p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope + depth * syncProposer)
  let otherGain := otherCredits / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  let creditGain := if 11 * depth * gainRateMax < capMax
    then (33 * depth * consolidationGain + 11 * depth * otherGain + 9) / 10
    else depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax
  let pendingR := if tight then 0 else
    ∑ i ∈ positions with (validator i).any (fun v =>
      decide (epoch.toNat < v.activationEligibilityEpoch.toNat) &&
        v.activationEpoch == FAR_FUTURE_EPOCH), (effective i + rise i)
  { quorum := quorumReserve config state ancestor, exiting, queues, queueDep, queueExit, credits,
    branchR, late, syncSeats, rise, fall, positions, current, exitingRise, exitingCredits,
    queueRise, reserveW, flagged, seatShortfall, consolidationsX, exitedR, depth, syncProposer,
    proposerCredit, exitingBands, pendingR, creditGain,
    gainHigh := !decide (11 * depth * gainRateMax < capMax),
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
    lowEB, newKeySeats, newKeySlack, newKeyFloor, leakAt, ebUp, leak, partialsDue, drop }
/-- The copy is faithful: the named terms sum to `pinReserve`. -/
theorem pinReserve_eq_total (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    pinReserve config state ancestor finalizedState =
      (pinTerms config state ancestor finalizedState).total := rfl

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

/-- `lowEB` takes the drops from the smaller of the two effective balances, capped at activation. -/
theorem lowEB_unfold (config : Config) (state ancestor finalizedState : BeaconState preset fork)
    (i : ℕ) :
    (pinTerms config state ancestor finalizedState).lowEB i =
      min (min (balanceAt state i) (balanceAt finalizedState i) -
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

/-- The credit that one balance event gives to the key at position `i`.

This is `keyCredit` of the exiting-credit lemmas, verbatim. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

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

/-- The credits to the key in one step, from the sources that count at that kind of step. -/
def stepCredit (blockP slotP : BalanceSource → Bool) (v : ℕ) {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : ℕ :=
  let events := step.balanceEvents.toOption.getD []
  match step with
  | .slot _ => ((events.filter (slotP ·.source)).map (keyCredit v)).sum
  | .block .. => ((events.filter (blockP ·.source)).map (keyCredit v)).sum

/-- The credits to the key over a run, and the number of block steps that credit it.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def creditScan (blockP slotP : BalanceSource → Bool) (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ × ℕ
  | _, .nil => (0, 0)
  | _, .snoc (middle := m) pre step =>
    let before := creditScan blockP slotP v high pre
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      let credit := stepCredit blockP slotP v step
      (before.1 + credit, before.2 + match step with
        | .block .. => if 0 < credit then 1 else 0
        | .slot _ => 0)
    else before

/-- The net credits to the key in the block steps of a run.

A block step counts the rise of the key's balance across the whole step.

A credit that the same step takes back counts for nothing.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def netScan (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ
  | _, .nil => 0
  | y, .snoc (middle := m) pre step =>
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      netScan v high pre + match step with
        | .block .. => actualBalanceAt y v - actualBalanceAt m v
        | .slot _ => 0
    else netScan v high pre

/-- Proposer and due-consolidation credits to the key on C's branch since the split.

The rounding slack of a credited key is `bandC`, once for each key.

The consolidation bands are not here: `bud_consolidations` charges them. -/
def propC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations)) v high tail).1

/-- Proposer credits to the key on C's branch since the split, without the consolidation credits.

A credited stake compounds by at most a tenth, which the stubs charge as `propN / 10`.

The consolidation credits are under `consolidationsX`, so their compounding is not charged here. -/
def propN {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v high tail).1

/-- Proposer and deposit credits to the key on C's branch since the split.

They are `credC` without its consolidation credits.

A credited stake compounds by at most a tenth, which the stubs charge as `credN / 10`.

The tenth is rounded down, so that the tenths of several keys add up to at most the tenth of their sum. -/
def credN {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards)) (fun s => decide (s = .deposits)) v high tail).1

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

The initial penalty is at most one increment, and `branchR` charges `inc` for each such key. -/
def slashR (t : PinTerms preset) (i : ℕ) : ℕ :=
  if t.slashedRB i = true then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0

/-- The rounding slack of a key with any C-side credit, once for each key.

The credits are those of a block step that nets the key a rise, and an applied deposit.

A proposer reward, a whistleblower reward and a sync reward are block credits.

A consolidation credit is not here: `bud_consolidations` charges its band for each entry.

`credits` charges `upwardBand` for each credited key. -/
def bandC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  if 0 < netScan v high tail +
      (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail).1 then
    preset.upwardBand else 0

/-- The rounding slack of a key whose balance on R's branch took a sync debit that `high` omits.

It is the step of `credR`, one increment and the downward band less one.

`branchR` charges that step for each of its keys. -/
def bandR (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  if 0 < ((events.filter (·.source = .sync)).map (keyDebit v)).sum then
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0

/-- The key's effective balance when its exit starts on a run, or 0.

It is the amount of the key's departure charge, which reads the effective balance at the exit call.

A key has a charge only if its exit was not assigned at the run's start.

Only a charge whose exit epoch is at most the run's last epoch counts. -/
def exitQ {x y : ForkedBeaconState preset} (tail : Run config checks x y) (v : ℕ) : ℕ :=
  ((tail.departureCharges.find? fun c =>
      c.index == v && decide (c.epoch ≤ (getCurrentEpoch y.state).toNat)).map (·.amount)).getD 0

/-- The epoch-pass reward credits to the key in one step.

A slot step's events are those of its epoch pass and its upgrades, so its `.rewards` events are the
epoch's rewards. A block step has none counted: its proposer credits are charged elsewhere. -/
def epochRewards (v : ℕ) {x y : ForkedBeaconState preset} (step : Step config checks x y) : ℕ :=
  match step with
  | .slot ok =>
    ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD []).filter
      (·.source = .rewards)).map (keyCredit v)).sum
  | .block .. => 0

/-- Whether a run has the key's departure charge, and the epoch rewards of the steps after it.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def riseScan (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → Bool × ℕ
  | _, .nil => (false, 0)
  | _, .snoc (middle := m) pre step =>
    let before := riseScan v high pre
    (before.1 || step.departureCharges.any (·.index == v),
      if before.1 = true ∧ (getCurrentEpoch m.state).toNat ≤ high + 1 then
        before.2 + epochRewards v step
      else before.2)

/-- The key's rise on a run after its exit starts there.

It is one upward band for the rise of the effective balance beyond the key's epoch rewards, plus
those rewards over the slot steps that come after the step with its departure charge.

It is 0 for a key whose exit does not start on the run. -/
def riseQ {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  if (riseScan v high tail).1 = true then preset.upwardBand + (riseScan v high tail).2 else 0

/-! ### The keys that a run credits -/

/-- The credits that a scan reads from a run, after one more step. -/
private theorem creditScan_snoc_fst (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m y) :
    (creditScan blockP slotP v high (pre.snoc step)).1 =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        (creditScan blockP slotP v high pre).1 + stepCredit blockP slotP v step
      else (creditScan blockP slotP v high pre).1 := by
  change (if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      ((creditScan blockP slotP v high pre).1 + stepCredit blockP slotP v step, _)
    else creditScan blockP slotP v high pre).1 = _
  split_ifs <;> rfl

/-- The credits of a run to a key, read as a scan, add over `append`. -/
private theorem creditScan_append (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (post : Run config checks m y) :
    (creditScan blockP slotP v high (pre.append post)).1 =
      (creditScan blockP slotP v high pre).1 + (creditScan blockP slotP v high post).1 := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change (creditScan blockP slotP v high ((pre.append post).snoc step)).1 = _
    rw [creditScan_snoc_fst, creditScan_snoc_fst]
    split
    · omega
    · exact ih

/-- The net credits to a key in the block steps of a run, after one more step. -/
private theorem netScan_snoc (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m y) :
    netScan v high (pre.snoc step) =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        netScan v high pre + (match step with
          | .block .. => actualBalanceAt y v - actualBalanceAt m v
          | .slot _ => 0)
      else netScan v high pre := rfl

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

/-- A block step that raises the balance of a key has the key among its proposers or sync seats. -/
private theorem block_credit_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {f : Fork} {s t : BeaconState preset f}
    (engine : ExecutionEngine preset f) (signed : SignedBeaconBlock preset f)
    (due : upgradeDue config ⟨f, s⟩ = false)
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ ∀ i : ℕ,
      actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i →
      i ∈ K ∨ ∃ altair : .altair ≤ f, 0 < syncSeats t altair i := by
  classical
  have invariant := (run_justified_separated shared genesis).1
  have processed := (applySignedBlock_ok ok).2.1
  have same : getCurrentEpoch (⟨f, t⟩ : ForkedBeaconState preset).state =
      getCurrentEpoch (⟨f, s⟩ : ForkedBeaconState preset).state := by
    simp only [getCurrentEpoch, processBlock_slot processed]
  obtain ⟨-, creditedKeys, pc, deposit, -, creditedCard, -, rise, zeroOff, electraZero, -⟩ :=
    (Run.nil.snoc (Step.block engine signed due ok) :
        Run config checks (⟨f, s⟩ : ForkedBeaconState preset) ⟨f, t⟩
          ).balanceCorrections_of_same_epoch
      early fulu same invariant.balancesMatch invariant.exitsOrdered
  have blocksOne : (Run.nil.snoc (Step.block engine signed due ok) :
      Run config checks (⟨f, s⟩ : ForkedBeaconState preset) ⟨f, t⟩).blockCount = 1 := rfl
  have electra : .pectra ≤ f := Nat.le_trans (by decide) fulu
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have hegota : f < .hegota := Nat.lt_trans early (by decide)
  have matchedT : BalancesMatch t :=
    (frame_processBlock processed).balancesMatch invariant.balancesMatch
  have limit := t.registryWithinLimit_of_lt early
  have creditedLe : creditedKeys.card ≤ 1 := by
    refine creditedCard.trans ?_
    simp [blocksOne, electra, hegota]
    have atMost : ∀ (P : Prop) (d : Decidable P), (@ite ℕ P d 0 1) ≤ 1 := fun P d => by
      cases d with
      | isTrue _ => exact Nat.zero_le _
      | isFalse _ => exact Nat.le_refl _
    exact atMost _ _
  refine ⟨creditedKeys.image UInt64.toNat, Finset.card_image_le.trans creditedLe,
    fun i increased => ?_⟩
  have inside : i < t.balances.data.size := by
    by_contra outside
    have missing : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]
    omega
  have below : i < 2 ^ 64 := by
    have sizes := matchedT
    unfold BalancesMatch at sizes
    have registry : i < t.validators.data.size := by omega
    unfold BeaconState.RegistryWithinLimit at limit
    have bound := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    omega
  obtain ⟨v, hv⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  have bound := rise v
  rw [hv] at bound
  have zero := electraZero electra v
  by_cases member : v ∈ creditedKeys
  · exact .inl (Finset.mem_image.mpr ⟨v, member, hv⟩)
  · obtain ⟨pcZero, -⟩ := zeroOff v member
    refine .inr ⟨altair, ?_⟩
    by_contra none
    have seats : syncSeats t altair i = 0 := Nat.eq_zero_of_not_pos none
    dsimp only at bound
    simp [altair, seats, blocksOne] at bound
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
    omega
  have insideV : i < c.validators.data.size := by
    unfold BalancesMatch at matchedC
    omega
  obtain ⟨w, found⟩ : ∃ w, c.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem insideV⟩
  have foundT : t.validators.data[i]? = some w := by rw [vals]; exact found
  refine ⟨w, foundT, ?_⟩
  by_contra none
  have unseated : w.pubkey ∉ (c.currentSyncCommittee altair).value.pubkeys.toList := by
    rw [← congrFun comm altair]
    exact none
  obtain ⟨reward, proposerReward, members, chosen, -, -, membersOk, -, balances⟩ :=
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
  have kept := (syncRewards_bounds (reward := reward.toNat)
    (proposerReward := proposerReward.toNat) (index := i) (chosen := chosen) _ b.toNat).2
    (fun member inside _ => seatless member.2 member inside rfl)
  rw [← value] at kept
  simp only [actualBalanceAt, held, atFinal, Option.map_some, Option.getD_some] at lowered
  omega

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
      obtain ⟨electra, a, b, matched, deposited, before0, after0⟩ := sites e0 mem0 dep0
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
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (altair : .altair ≤ x.fork) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ)
    (same : (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) :
    ∃ B D : Finset ℕ, B.card ≤ r.blockCount ∧
      D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∀ i, 0 < netScan i high r →
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
      rw [netScan_snoc] at pos
      have prior : 0 < netScan i high pre := by
        split at pos
        · simpa using pos
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
      obtain ⟨K, cardK, hK⟩ := block_credit_keys genesis engine signed due ok (shared.append pre)
        fulu' uEarly
      refine ⟨B ∪ K, D ∪ Ds, ?_, cardUnion, fun i pos => ?_, depMem, ?_⟩
      · exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB cardK)
      · rw [netScan_snoc] at pos
        have either : 0 < netScan i high pre ∨
            actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i <
              actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i := by
          split at pos
          · simp only [] at pos
            omega
          · exact .inl pos
        rcases either with prior | risen
        · rcases hB i prior with member | ⟨w, found, mem⟩
          · exact .inl (Finset.mem_union_left _ member)
          · exact .inr (carry i w found mem)
        · rcases hK i risen with member | ⟨altair', seats⟩
          · exact .inl (Finset.mem_union_right _ member)
          · unfold syncSeats at seats
            obtain ⟨key, hkey⟩ := List.length_pos_iff_exists_mem.mp seats
            obtain ⟨keyMem, test⟩ := List.mem_filter.mp hkey
            obtain ⟨w, hv⟩ : ∃ w, t.validators.data[i]? = some w := by
              cases found : t.validators.data[i]? with
              | none =>
                rw [found] at test
                simp at test
              | some w => exact ⟨w, rfl⟩
            rw [hv] at test
            simp only [Option.any_some, beq_iff_eq] at test
            have committee := (Run.snoc pre (Step.block engine signed due ok)
                ).currentSyncCommittee_eq_of_same_period early same altair' altair
            refine .inr ⟨w, hv, ?_⟩
            rw [test, ← committee]
            exact keyMem
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
  · have mapped : ((Finset.range y.state.validators.data.size).filter fun i =>
        ∃ w, y.state.validators.data[i]? = some w ∧ w.pubkey ∈ L).card ≤ L.toFinset.card := by
      refine Finset.card_le_card_of_injOn (keyAt y.state) (fun i member => ?_)
        (fun i mi j mj eq => ?_)
      · obtain ⟨w, found, mem⟩ := (Finset.mem_filter.mp member).2
        simp only [keyAt, found, Option.map_some, Option.getD_some]
        exact List.mem_toFinset.mpr mem
      · obtain ⟨w, found, -⟩ := (Finset.mem_filter.mp mi).2
        obtain ⟨w', found', -⟩ := (Finset.mem_filter.mp mj).2
        simp only [keyAt, found, found', Option.map_some, Option.getD_some] at eq
        exact distinct.index_eq found found' eq
    exact mapped.trans ((List.toFinset_card_le L).trans (by simp [L]))
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

/-- The keys credited in the block steps of a run, counted by the periods that it touches. -/
private theorem credited_pieces {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {y : ForkedBeaconState preset}
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
      (∀ i, 0 < netScan i high r → i ∈ B ∨ i ∈ S) ∧
      (∀ i, 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r).1 →
        i ∈ D) ∧
      ∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (syncDebit i)).sum →
        i ∈ S := by
  classical
  intro n
  induction n with
  | zero =>
    intro x shared r fulu count
    have electra : .pectra ≤ x.fork := Nat.le_trans (by decide) fulu
    have altair : .altair ≤ x.fork := Nat.le_trans (by decide) electra
    obtain ⟨B, D, cardB, cardD, hB, hDep, hD⟩ := credited_piece genesis shared r fulu altair
      early delay high (by simpa using count)
    obtain ⟨S, cardS, hS⟩ := seat_positions genesis shared r altair
    refine ⟨B, S, D, cardB, by simpa using cardS, cardD, fun i pos => ?_, hDep, ?_⟩
    · rcases hB i pos with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (hS i w found mem)
    · intro events replayed i pos
      obtain ⟨w, found, mem⟩ := hD events replayed i pos
      exact hS i w found mem
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
    obtain ⟨B₁, D₁, cardB₁, cardD₁, hB₁, hDep₁, hD₁⟩ := credited_piece genesis shared pre fulu
      altair mEarly delay high (by simpa using mSame)
    obtain ⟨S₁, cardS₁, hS₁⟩ := seat_positions genesis shared pre altair
    obtain ⟨B₂, S₂, D₂, cardB₂, cardS₂, cardD₂, hB₂, hDep₂, hD₂⟩ := ih (x := v)
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
    refine ⟨B₁ ∪ B₂, S₁ ∪ S₂, D₁ ∪ Ds ∪ D₂, ?_, ?_, ?_, fun i pos => ?_, fun i pos => ?_, ?_⟩
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
    · rw [netScan_append] at pos
      by_cases first : 0 < netScan i high (pre.snoc (Step.slot ok))
      · have prior : 0 < netScan i high pre := by
          rw [netScan_snoc] at first
          split at first
          · simpa using first
          · exact first
        rcases hB₁ i prior with member | ⟨w, found, mem⟩
        · exact .inl (Finset.mem_union_left _ member)
        · exact .inr (Finset.mem_union_left _ (hS₁ i w found mem))
      · have later : 0 < netScan i high post := by omega
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
      · refine Finset.mem_union_left _ ?_
        simp only [Run.balanceEvents, bind_ok_iff] at ok1
        obtain ⟨prior, priorOk, rest⟩ := ok1
        split at rest
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
          obtain ⟨added, addedOk, rfl⟩ := rest
          have zero := (PinSplit5.slot_syncDebit_zero
            (Nat.le_trans (show Fork.pectra ≤ Fork.fusaka by decide)
              (Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps))) ok vEarly addedOk i).1
          simp only [List.map_append, List.sum_append, zero, Nat.add_zero] at first
          obtain ⟨w, found, mem⟩ := hD₁ prior priorOk i first
          exact hS₁ i w found mem
        · simp only [pure, Except.pure, Except.ok.injEq] at rest
          subst rest
          obtain ⟨w, found, mem⟩ := hD₁ _ priorOk i first
          exact hS₁ i w found mem
      · exact Finset.mem_union_right _ (hD₂ e2 ok2 i (by omega))

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
    (keys : Finset ℕ) (banded : ∀ i ∈ keys, 0 < netScan i high tail +
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
  obtain ⟨B, S, D, cardB, cardS, cardD, hBS, hD, hSD⟩ := credited_pieces h.genesis (y := ⟨fork, x⟩)
    h.early h.delay high
    ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    shared tail h.fulu periods
  have cardD' : D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) := cardD
  have subset : keys ⊆ B ∪ S ∪ D := fun i member => by
    have pos := banded i member
    by_cases net : 0 < netScan i high tail
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
        0 < netScan i high tail +
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

/-- D-5/D-6 (fall, V): the fall of V keys, and the stake of V keys that left C's active set. -/
theorem stub_V (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cV1 pulled counted V + cV2 pulled counted V ≤
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) + (∑ v ∈ V, credR tail high v.toNat) +
        (∑ v ∈ V, (syncF events v.toNat + syncF eventsC v.toNat)) + (∑ v ∈ V, credDepR events v.toNat) +
        (∑ v ∈ V, consAmt events v.toNat) + preset.upwardBand * dueAt fin high V +
        (∑ v ∈ (VN counted V), exitQ tailC v.toNat) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, eR pulled v) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true, eR pulled v) : ℕ) := sorry

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
      n.state.validators.data[i.toNat]? = some w → high + 1 < w.exitEpoch.toNat) :
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
      high + 1 < w.exitEpoch.toNat) :
    min (actualBalanceAt ⟨fork, split⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat ≤
      actualBalanceAt ⟨fork, pulled⟩ i.toNat +
        (events.map (DirectSafety.Apriori.Internal.penaltyDebit i.toNat)).sum +
        (events.map (syncDebit i.toNat)).sum +
        (events.map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum := by
  obtain ⟨fromFin⟩ := h.fromFin
  exact key_floorR_from h fromFin tail high endEpoch replayed i val initial unslashed stays
    retained

/-! ### One key's reward in an epoch pass -/

/-- The reward credits of a list of events are those of the events, read at one position. -/
private theorem sum_filter_rewards (events : List (BalanceEvent preset)) (v : ℕ) :
    ((events.filter (·.source = .rewards)).map (keyCredit v)).sum =
      (events.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    by_cases rewards : e.source = .rewards
    · simp [rewards, keyCredit, DirectSafety.Apriori.Internal.rewardCredit, ih]
    · simp [rewards, DirectSafety.Apriori.Internal.rewardCredit, ih]

/-- A flag pays a key at most its base reward times the weight of the flag, over the active stake.

The increments that set the flag in the previous epoch are at most those active then.

The rate read there is at most `P` times the active increments. -/
private theorem flagReward_le {f : Fork} (altair : .altair ≤ f) {state : BeaconState preset f}
    (within : state.RegistryWithinLimit) {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flag = .ok (rewards, penalties))
    {total : Gwei} (active : getTotalActiveBalance state = .ok total) (P v : ℕ)
    (inside : v < state.validators.data.size)
    (rate : ∀ perIncrement : Gwei, getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat *
          ((∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
            balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    (rewards.getD v 0).toNat *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) ≤
      balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
    (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      (rewards.getD v 0).toNat = 0) := by
  obtain ⟨participating, participatingBalance, total', flaggedOk, weighed, totalOk, perKey⟩ :=
    getFlagIndexDeltas_getD within computed
  obtain rfl : total = total' := Except.ok.inj (active.symm.trans totalOk)
  obtain ⟨eligible, -, notEligible, eligibleCase⟩ := perKey v inside
  have zero (h : (rewards.getD v 0).toNat = 0) :
      (rewards.getD v 0).toNat *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) ≤
      balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
      (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
        (rewards.getD v 0).toNat = 0) :=
    ⟨by rw [h, Nat.zero_mul]; exact Nat.zero_le _, fun _ => h⟩
  by_cases isEligible : eligible = true
  swap
  · exact zero (by simp [(notEligible (by simpa using isEligible)).1])
  obtain ⟨base, baseOk, member⟩ := eligibleCase isEligible
  by_cases present : v.toUInt64 ∈ participating
  swap
  · exact zero (by simp [(member.2 present).1])
  obtain ⟨leak, leakOk, formula, -⟩ := member.1 present
  cases leak
  swap
  · simp only [↓reduceIte] at formula
    exact zero formula
  simp only [Bool.false_eq_true, ↓reduceIte] at formula
  have index : v.toUInt64.toNat = v := toNat_toUInt64_of_lt within inside
  obtain ⟨per, perOk⟩ : ∃ per, getBaseRewardPerIncrement preset total = .ok per := by
    simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff] at baseOk
    obtain ⟨_, -, per, perOk, -⟩ := baseOk
    exact ⟨per, perOk⟩
  obtain ⟨validator, found, baseEq⟩ := getBaseReward_eq_mul_of_altair altair perOk baseOk
  rw [index] at found
  have stakeV : balanceAt state v = validator.effectiveBalance.toNat := by
    simp [balanceAt, found]
  have increments : (rewards.getD v 0).toNat *
      (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) ≤
      base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    rw [formula]
    exact Nat.div_mul_le_self _ _
  refine ⟨?_, fun none => by rw [formula, none, Nat.zero_mul, Nat.div_zero]⟩
  -- A key with less than one increment has no base reward.
  by_cases small : balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0
  · have noBase : base.toNat = 0 := by rw [baseEq, ← stakeV, small, Nat.zero_mul]
    rw [noBase, Nat.zero_mul, Nat.zero_mul] at increments
    rw [small, Nat.zero_mul, Nat.zero_mul]
    exact increments
  -- The key sets the flag and is active in the previous epoch, so both stakes hold its balance.
  have stakeParticipating : balanceAt state v ≤
      ∑ i ∈ participating.toFinset, balanceAt state i.toNat := by
    have := Finset.single_le_sum (f := fun i : ValidatorIndex => balanceAt state i.toNat)
      (fun _ _ => Nat.zero_le _) (List.mem_toFinset.mpr present)
    simpa only [index] using this
  have subset : ∑ i ∈ participating.toFinset, balanceAt state i.toNat ≤
      ∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
        balanceAt state i.toNat :=
    Finset.sum_le_sum_of_subset fun i member =>
      List.mem_toFinset.mpr (mem_getUnslashedParticipatingIndices flaggedOk i
        (List.mem_toFinset.mp member)).1
  obtain ⟨-, -, balanceEq⟩ := getTotalBalance_ok_iff_stake.mp weighed
  have positive : 0 < balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero small
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    refine Nat.pos_of_ne_zero fun zero => ?_
    rw [zero, Nat.div_zero] at positive
    exact Nat.lt_irrefl _ positive
  have one : 1 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ balanceAt state v :=
    (Nat.le_div_iff_mul_le incPos).mp positive
  rw [Nat.one_mul] at one
  have participatingLe : participatingBalance.toNat ≤
      ∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
        balanceAt state i.toNat := by
    rw [balanceEq]
    exact max_le (Nat.le_trans (Nat.le_trans one stakeParticipating) subset) subset
  have share : participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      (∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
        balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.div_le_div_right participatingLe
  have bound := rate per perOk
  calc (rewards.getD v 0).toNat *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat)
      ≤ base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := increments
    _ ≤ base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        ((∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
          balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :=
        Nat.mul_le_mul_left _ share
    _ = balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (per.toNat * ((∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
          balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
        rw [baseEq, stakeV]
        ring
    _ ≤ balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
        Nat.mul_le_mul_left _ bound

/-- The three flags pay a key, in a rewards replay of a state, at most its stake times `P`.

The credit is scaled by `64` and by the active increments.

It is at most the key's increments times `54`, `P` and the active increments.

A state with no active increment pays nothing. -/
private theorem replayRewards_credit_le {f : Fork} (altair : .altair ≤ f)
    {pass : BeaconState preset f} (within : pass.RegistryWithinLimit)
    {rewarded : BalanceReplay preset f}
    (replayed : replayRewards (config := config) (pass, []) = .ok rewarded) (P v : ℕ)
    (inside : v < pass.validators.data.size)
    (rate : ∀ total perIncrement : Gwei, getTotalActiveBalance pass = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat *
          ((∑ i ∈ (getActiveValidatorIndices pass (getPreviousEpoch pass)).toFinset,
            balanceAt pass i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0 ∨
      ∃ total : Gwei, getTotalActiveBalance pass = .ok total ∧
        (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum *
            (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
          balanceAt pass v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 54 *
            (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
          (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0) := by
  by_cases genesis : getCurrentEpoch pass = GENESIS_EPOCH
  · simp only [replayRewards, genesis, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    exact .inl rfl
  obtain ⟨source, target, head, inactivity, first, second, third, sourceOk, targetOk, headOk,
    inactivityOk, firstOk, secondOk, thirdOk, last⟩ :=
    DirectSafety.Apriori.Internal.replayRewards_passes altair genesis replayed
  obtain ⟨-, -, total, -, -, active, -⟩ := getFlagIndexDeltas_getD within sourceOk
  have wd : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  have flagBound (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length) {deltas : Array Gwei × Array Gwei}
      (computed : getFlagIndexDeltas pass altair flag = .ok deltas) :=
    flagReward_le altair within (flag := flag) (rewards := deltas.1) (penalties := deltas.2)
      computed active P v inside (fun per perOk => rate total per active perOk)
  have one := flagBound ⟨0, by decide⟩ sourceOk
  have two := flagBound ⟨1, by decide⟩ targetOk
  have three := flagBound ⟨2, by decide⟩ headOk
  have flows (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset f}
      (src : BalanceSource) (ok : replayDeltas src deltas pre = .ok post) :=
    (DirectSafety.Apriori.Internal.replayDeltas_flows src deltas ok v).2
  have s1 := flows source .penalties firstOk
  have s2 := flows target .penalties secondOk
  have s3 := flows head .penalties thirdOk
  have s4 := flows inactivity .inactivity last
  have noReward : (inactivity.1.getD v 0).toNat = 0 := by
    simp [getInactivityPenaltyDeltas_rewards inactivityOk]
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at s1
  have weights : PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ : Fin 3)].toNat = 54 := rfl
  have sum : (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum ≤
      (source.1.getD v 0).toNat + (target.1.getD v 0).toNat + (head.1.getD v 0).toNat := by
    omega
  rw [wd] at one two three
  obtain ⟨b1, z1⟩ := one
  obtain ⟨b2, z2⟩ := two
  obtain ⟨b3, z3⟩ := three
  refine .inr ⟨total, active, ?_, fun none => ?_⟩
  · have scaled := Nat.mul_le_mul_right
      (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) sum
    simp only [Nat.add_mul] at scaled
    rw [← weights]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  · have := z1 none
    have := z2 none
    have := z3 none
    omega

/-- Quotients of the reward bound: the rewards of a pass are at most a rate for each increment. -/
private theorem reward_sum_le (S A K Ke P : ℕ)
    (bound : S * (A * 64) ≤ K * 54 * (P * A)) (none : A = 0 → S = 0) (small : K ≤ Ke) :
    S ≤ Ke * P * 54 / 64 := by
  by_cases zero : A = 0
  · rw [none zero]
    exact Nat.zero_le _
  have positive : 0 < A := Nat.pos_of_ne_zero zero
  have times : S * 64 * A ≤ K * 54 * P * A := by
    calc S * 64 * A = S * (A * 64) := by ring
      _ ≤ K * 54 * (P * A) := bound
      _ = K * 54 * P * A := by ring
  have cancelled : S * 64 ≤ K * 54 * P := Nat.le_of_mul_le_mul_right times positive
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 64)]
  calc S * 64 ≤ K * 54 * P := cancelled
    _ ≤ Ke * 54 * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ small)
    _ = Ke * P * 54 := by ring

open DirectSafety.Apriori.Internal in
/-- One key's rewards credit in a step is at most a rate for each epoch that the step ends.

The step is a slot, and it ends an epoch exactly when it runs the epoch's pass.

The key's stake at the start is at most `E`.

`P` bounds the rate read at the active stake, scaled by the previous epoch's share of it. -/
private theorem epochRewards_le {m n : ForkedBeaconState preset}
    (step : Step config checks m n) (altair : .altair ≤ m.fork) (early : n.fork < .glamsterdam)
    (v : ℕ) (inside : v < m.state.validators.data.size) (E P : ℕ)
    (envelope : effectiveAt m v ≤ E)
    (rate : ∀ total perIncrement : Gwei, getTotalActiveBalance m.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat *
          ((∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
            effectiveAt m i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    epochRewards v step ≤ ((getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat) *
      (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) := by
  cases step with
  | block engine signed due ok => simp [epochRewards]
  | slot ok =>
    have mEarly : m.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
    simp only [epochRewards]
    cases hev : (Step.slot (config := config) (checks := checks) ok).balanceEvents with
    | error err => simp [Except.toOption]
    | ok events =>
      simp only [Except.toOption, Option.getD_some]
      rw [sum_filter_rewards]
      obtain ⟨advanced, cached, crossings, -, upgrades, cachedOk, crossingOk, kind⟩ :=
        Step.balanceEvents_slot ok early hev
      have crossed := upgradeBalanceReplay_crossing crossingOk
      have crossingsQuiet : (crossings.map (rewardCredit v)).sum = 0 :=
        List.sum_eq_zero fun x member => by
          obtain ⟨e, mem, rfl⟩ := List.mem_map.mp member
          simp [rewardCredit, crossed e mem]
      rcases kind with ⟨-, eventsEq⟩ |
        ⟨middle, updated, recorded, recordOk, -, -, -, eventsEq, next, nextEq, advSlot, last, -⟩
      · subst eventsEq
        rw [crossingsQuiet]
        exact Nat.zero_le _
      subst eventsEq
      obtain ⟨just, pass, rewarded, later, justified, scored, rewardedOk, recordedEq,
        laterSources, -⟩ := epochReplay_events altair (epochBalanceReplay_trace recordOk)
      simp only at recordedEq
      subst recordedEq
      have laterQuiet : (later.map (rewardCredit v)).sum = 0 :=
        List.sum_eq_zero fun x member => by
          obtain ⟨e, mem, rfl⟩ := List.mem_map.mp member
          rcases laterSources e mem with s | s | s <;> simp [rewardCredit, s]
      simp only [List.map_append, List.sum_append, laterQuiet, crossingsQuiet, Nat.add_zero]
      -- The slot ends one epoch.
      have nSlot : n.state.slot = next := (processUpgrades_slot upgrades).trans advSlot
      have epochs : (getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat = 1 := by
        have boundary := nextSlot_epoch_of_boundary nextEq last
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, nSlot, boundary]
        exact Nat.add_sub_cancel_left _ _
      rw [epochs, Nat.one_mul]
      -- The pass reads the registry and the epoch of the start.
      obtain ⟨-, effectiveEq, -, validatorsEq, slotEq⟩ :=
        pass_kept_of_effective (config := config) (checks := checks)
          (inner := (Run.nil : Run config checks m m)) (effectiveKept_refl m.state) rfl
          cachedOk justified scored
      have within : pass.RegistryWithinLimit := pass.validators.bound mEarly
      have insidePass : v < pass.validators.data.size := by
        rw [validatorsEq]
        exact inside
      have balanceAtEq (i : ℕ) : balanceAt pass i = effectiveAt m i := by
        simp [balanceAt, effectiveAt, validatorsEq]
      have totalEq : getTotalActiveBalance pass = getTotalActiveBalance m.state := by
        simp only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getCurrentEpoch,
          slotEq, validatorsEq, getTotalBalance]
        rfl
      have prevEpoch : getPreviousEpoch pass = getPreviousEpoch m.state := by
        simp only [getPreviousEpoch, getCurrentEpoch, slotEq]
      have prevEq : getActiveValidatorIndices pass (getPreviousEpoch pass) =
          getActiveValidatorIndices m.state (getPreviousEpoch m.state) := by
        rw [prevEpoch]
        simp only [getActiveValidatorIndices, validatorsEq]
      have ratePass : ∀ total perIncrement : Gwei, getTotalActiveBalance pass = .ok total →
          getBaseRewardPerIncrement preset total = .ok perIncrement →
          perIncrement.toNat *
              ((∑ i ∈ (getActiveValidatorIndices pass (getPreviousEpoch pass)).toFinset,
                balanceAt pass i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
            P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
        intro total perIncrement totalOk perOk
        have sums : (∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
            balanceAt pass i.toNat) =
            ∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
              effectiveAt m i.toNat :=
          Finset.sum_congr rfl fun i _ => balanceAtEq i.toNat
        rw [prevEq, sums]
        exact rate total perIncrement (totalEq.symm.trans totalOk) perOk
      have bound := replayRewards_credit_le altair within rewardedOk P v insidePass ratePass
      have small : balanceAt pass v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
        Nat.div_le_div_right (by rw [balanceAtEq]; exact envelope)
      have flagSum : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := rfl
      have wd : WEIGHT_DENOMINATOR.toNat = 64 := by decide
      rw [flagSum, wd]
      rcases bound with zero | ⟨total, -, scaled, none⟩
      · rw [zero]
        exact Nat.zero_le _
      · exact reward_sum_le _ _ _ _ P scaled none small

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

/-- The reward per increment at a state of a run from the finalized state, times the previous
epoch's active increments, is at most the pin's rate times the active increments. -/
private theorem rate_of_guard
    (h : Setting config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork} (toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩)
    (inside : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {pq : Gwei} (pqOk : getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq) :
    ∀ total perIncrement : Gwei, getTotalActiveBalance m = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat *
          ((∑ i ∈ (getActiveValidatorIndices m (getPreviousEpoch m)).toFinset,
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
  have stake := prevStake_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
    electra h.guard toM h.early inside totalOk
  have clamp : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ total.toNat := by
    obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
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

/-- The effective balance of a key that stays on its path is at most the rise of the main regime. -/
private theorem rise_arith {inc band capFor high finEB eR eC Bc capHigh S U : Nat}
    (incPos : 0 < inc)
    (stay : eC = eR ∨ (eC ≤ Bc + band ∧ eC ≤ max finEB (min (Bc - Bc % inc) capHigh)))
    (aligned : eC % inc = 0) (capped : eC ≤ capFor + S + U) (ceiling : Bc ≤ high + S)
    (slack : S = 0 ∨ inc ≤ U + 1) :
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
      have a : eC ≤ max finEB (Bc - Bc % inc) := by
        omega
      have b : high + S - (high + S) % inc ≤ high - high % inc + S + U := by
        rcases slack with z | big
        · subst z; simp only [Nat.add_zero]; omega
        · have := Nat.mod_lt high incPos
          have := Nat.mod_lt (high + S) incPos
          have := Nat.mod_le high inc
          have := Nat.mod_le (high + S) inc
          omega
      omega
    have third : eC ≤ high + band - (high + band) % inc + S + U := by
      have b : high + band + S - (high + band + S) % inc ≤
          high + band - (high + band) % inc + S + U := by
        rcases slack with z | big
        · subst z; simp only [Nat.add_zero]; omega
        · have := Nat.mod_lt (high + band) incPos
          have := Nat.mod_lt (high + band + S) incPos
          have := Nat.mod_le (high + band) inc
          have := Nat.mod_le (high + band + S) inc
          omega
      omega
    omega

/-- On C's branch a key keeps R's effective balance, or stays within the ceiling of its balance. -/
private theorem key_stay {fin pulled counted : BeaconState preset fork}
    (rC : Run config checks ⟨fork, fin⟩ ⟨fork, counted⟩)
    (rR : Run config checks ⟨fork, fin⟩ ⟨fork, pulled⟩)
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (later : (getCurrentEpoch pulled).toNat ≤ (getCurrentEpoch counted).toNat)
    (i : ℕ) (inside : i < fin.validators.data.size) (Bc capHigh Bp capP : ℕ)
    (balanceC : ∀ z ∈ rC.balancePath, actualBalanceAt z i ≤ Bc)
    (capC : ∀ z ∈ rC.balancePath, PinSplit2.capAt z i ≤ capHigh)
    (balanceR : ∀ z ∈ rR.balancePath, actualBalanceAt z i ≤ Bp)
    (capR : ∀ z ∈ rR.balancePath, PinSplit2.capAt z i ≤ capP) :
    effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i =
        effectiveAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i ∨
      (effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i ≤ Bc + preset.downwardBand ∧
        effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i ≤
          max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
            (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh)) := by
  obtain ⟨ceilC, sameC, afterC, -⟩ :=
    PinSplit2.Run.effective_ceiling_of_balance_ceiling rC early fulu i inside Bc capHigh balanceC
      capC
  by_cases flat : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch fin).toNat
  · obtain ⟨-, sameR, -, -⟩ :=
      PinSplit2.Run.effective_ceiling_of_balance_ceiling rR early fulu i inside Bp capP balanceR
        capR
    have atFin : (getCurrentEpoch pulled).toNat ≤ (getCurrentEpoch fin).toNat := by omega
    exact .inl ((sameC flat).trans (sameR atFin).symm)
  · have after : (getCurrentEpoch fin).toNat < (getCurrentEpoch counted).toNat := by omega
    exact .inr ⟨afterC after, ceilC⟩

/-- At a state of a run from genesis, a key's effective balance is a whole number of increments. -/
private theorem effective_aligned {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset) (i : ℕ) :
    effectiveAt x i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have whole := (run.invariant genesis.invariant).aligned aligned
  cases found : x.state.validators.data[i]? with
  | none => simp [effectiveAt, found]
  | some v =>
    have := congrArg UInt64.toNat (whole v (Array.mem_of_getElem? found))
    simpa [effectiveAt, found, UInt64.toNat_mod] using this

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
  · have capped := UInt64.le_iff_toNat_le.mp
      (run.effectiveBalance_capped genesis caps.activation caps.compounding early vC
        (Array.mem_of_getElem? foundC))
    simp only [effectiveAt, foundC, Option.map_some, Option.getD_some]
    rw [low]
    exact le_trans capped
      (UInt64.le_iff_toNat_le.mp (PinSplit.withdrawalMax_le electra electra caps frozen))

/-- A key's effective balance on C's branch is at most R's plus the main rise and the slacks. -/
private theorem key_rise_main {g : ForkedBeaconState preset}
    {fin pulled counted : BeaconState preset fork} (shared : Run config checks g ⟨fork, fin⟩)
    (genesis : Genesis (config := config) (checks := checks) g)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (rC : Run config checks ⟨fork, fin⟩ ⟨fork, counted⟩)
    (rR : Run config checks ⟨fork, fin⟩ ⟨fork, pulled⟩)
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (later : (getCurrentEpoch pulled).toNat ≤ (getCurrentEpoch counted).toNat)
    (i : ℕ) (inside : i < fin.validators.data.size) (Bc capHigh Bp capP : ℕ)
    (balanceC : ∀ z ∈ rC.balancePath, actualBalanceAt z i ≤ Bc)
    (capC : ∀ z ∈ rC.balancePath, PinSplit2.capAt z i ≤ capHigh)
    (balanceR : ∀ z ∈ rR.balancePath, actualBalanceAt z i ≤ Bp)
    (capR : ∀ z ∈ rR.balancePath, PinSplit2.capAt z i ≤ capP)
    (capFor high S U : ℕ)
    (capped : effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i ≤ capFor + S + U)
    (ceiling : Bc ≤ high + S)
    (slack : S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i ≤
      effectiveAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
        (min capFor (min (high + preset.downwardBand -
              (high + preset.downwardBand) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
            (max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
              (high - high % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))) -
          effectiveAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) + S + U :=
  rise_arith incPos
    (key_stay rC rR early fulu later i inside Bc capHigh Bp capP balanceC capC balanceR capR)
    (effective_aligned (shared.append rC) genesis maxAligned i) capped ceiling slack

/-- The per-key core of the rise.

A key of R's registry rises from R to C by at most its rise term.

It also rises by the credits and slacks that `rise` does not read.

The slacks are one increment for a slashing on R's branch.

They are one rounding step for a credit on C's branch or a sync debit on R's.

A credit on C's branch also compounds by a tenth of its amount, without its consolidation credits. -/
private theorem key_core (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (i : ℕ) (inside : i < pulled.validators.data.size) :
    balanceAt counted i ≤ balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
      (credC tailC highC i + credN tailC highC i / 10) + whistC tailC highC i +
      (syncF events i + syncF eventsC i) + slashR (pinTerms config pulled anc fin) i +
      bandC tailC highC i + bandR events i :=
  sorry

/-- D-7 (rise): other keys active in both. -/
theorem stub_N (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cN pulled counted V ≤ ((∑ v ∈ (K4 pulled counted V), ((pinTerms config pulled anc fin).rise v.toNat +
      (credC tailC highC v.toNat + credN tailC highC v.toNat / 10) + whistC tailC highC v.toNat + (syncF events v.toNat + syncF eventsC v.toNat) +
      slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
      bandR events v.toNat)) : ℕ) := by
  have early := h.early
  have term : ∀ v ∈ K4 pulled counted V, ((eC counted v : ℤ) - eR pulled v) ≤
      (((pinTerms config pulled anc fin).rise v.toNat +
        (credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
        whistC tailC highC v.toNat + (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR events v.toNat : ℕ) : ℤ) := by
    intro v member
    have active : v ∈ AR pulled := (Finset.mem_filter.mp member).2.1
    obtain ⟨w, found, -⟩ := active_of_activeVoters early (s := pulled) active
    have core := key_core h tail high endEpoch replayed tailC highC endEpochC replayedC v.toNat
      (Array.getElem?_eq_some_iff.mp found).1
    simp only [eC, eR]
    push_cast
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


/-- D-4 (+ D-8 exits): other keys previous-epoch-only in C. A key whose exit R reads is at its
balance at R plus its rise; any other one is at its balance when its exit starts on C's branch,
plus its rise after that. Both add C's proposer credits and sync seats. -/
theorem stub_P (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cP pulled counted V ≤ ((∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = false,
        (exitQ tailC v.toNat + riseQ tailC highC v.toNat)) +
      (∑ v ∈ (K5 counted V), ((propC tailC highC v.toNat + propN tailC highC v.toNat / 10) +
        whistC tailC highC v.toNat +
        (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR events v.toNat)) : ℕ) := sorry

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

/-- The keys of `K6` beyond R's registry are paid by the credits.

In the high regime they are also paid by `creditGain`.

They joined the registry on C's branch, so their stake is the credits that reach them.

The credits compound by a tenth, which `credN / 10` charges, when the gain rate is low.

Otherwise `creditGain` charges the deposits up to the cap. -/
private theorem beyond_keys (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∑ v ∈ (K6 pulled counted) with pulled.validators.data.size ≤ v.toNat, eC counted v ≤
      (∑ v ∈ (K6 pulled counted) with pulled.validators.data.size ≤ v.toNat,
        (((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR events v.toNat))) +
        (if (pinTerms config pulled anc fin).gainHigh then
          (pinTerms config pulled anc fin).creditGain else 0) := sorry

/-- D-8 (activations): keys counted in C and not active at R.

A key whose exit started on R's branch after the split is inactive at R and active in C (L10).

Its stake in C is at most its stake at R and its rise.

So is the stake of a key whose exit R reads, which `exiting` and `exitingRise` charge. -/
theorem stub_J (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
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
      (∑ v ∈ (K6 pulled counted), ((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
        whistC tailC highC v.toNat)) +
      (∑ v ∈ (K6 pulled counted), (syncF events v.toNat + syncF eventsC v.toNat)) +
      (∑ v ∈ (K6 pulled counted),
        (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
          bandR events v.toNat)) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (if (pinTerms config pulled anc fin).gainHigh then (pinTerms config pulled anc fin).creditGain
        else 0)) : ℕ) := by
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
  have beyond := beyond_keys h tail high endEpoch replayed tailC highC endEpochC replayedC
  -- The keys inside R's registry rise by `key_core`, and R's record puts each in a class.
  have core : ∀ v ∈ K6 pulled counted, v.toNat < pulled.validators.data.size →
      eC counted v ≤ (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) +
        (((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR events v.toNat)) := by
    intro v _ hin
    have := key_core (config := config) h tail high endEpoch replayed tailC highC endEpochC
      replayedC v.toNat hin
    unfold eC eR
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
      ∑ v ∈ inside, (((eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) +
        (((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR events v.toNat)))) :=
    Finset.sum_le_sum fun v hv =>
      core v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  rw [Finset.sum_add_distrib] at insideSum
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
    (fun v => (((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR events v.toNat)))
  rw [notInside, ← hInside] at bounds
  have boundSplit : ∑ v ∈ K6 pulled counted,
      (((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
            whistC tailC highC v.toNat) +
          (syncF events v.toNat + syncF eventsC v.toNat) +
          (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
            bandR events v.toNat)) =
      (∑ v ∈ K6 pulled counted, ((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
        whistC tailC highC v.toNat)) +
      (∑ v ∈ K6 pulled counted, (syncF events v.toNat + syncF eventsC v.toNat)) +
      ∑ v ∈ K6 pulled counted, (slashR (pinTerms config pulled anc fin) v.toNat +
        bandC tailC highC v.toNat + bandR events v.toNat) := by
    simp only [Finset.sum_add_distrib]
  omega


/-- K5 bands: the two bands beyond `credits`' one of each credited K5 key, weight 3.

Split by `exitingB`: the keys whose exit R reads and those the queues let exit on C. -/
theorem bud_exitingBands (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) :
    2 * (∑ v ∈ (K5 counted V), bandC tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).exitingBands := sorry

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
    (count : (((K5 counted V).filter fun v =>
      (pinTerms config pulled anc fin).exitingB v.toNat = false).filter
        fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card ≤
      (pinTerms config pulled anc fin).queueKeys) :
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
  have timesB := Nat.mul_le_mul_right preset.upwardBand count
  rw [parts]
  nlinarith

/-- A key of `K5` that R does not read as exiting has a departure charge on C's run. -/
private theorem K5_charged (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ K5 counted V) (flag : (pinTerms config pulled anc fin).exitingB v.toNat = false) :
    ∃ c ∈ tailC.departureCharges, c.index = v.toNat := by
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
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
  by_cases inherited : ∃ old, split.validators.data[v.toNat]? = some old ∧
      old.exitEpoch ≠ FAR_FUTURE_EPOCH
  · exfalso
    obtain ⟨old, oldFound, oldAssigned⟩ := inherited
    obtain ⟨uC, foundUC, keptC⟩ := tailC.registryLifecycle.validators v.toNat old oldFound
    have sameU : uC = u := Option.some.inj (foundUC.symm.trans foundU)
    rw [sameU] at keptC
    obtain ⟨w, foundW, keptP⟩ := toPulled.registryLifecycle.validators v.toNat old oldFound
    have gap := (shared.append fromFin).exit_activation_gap h.genesis v.toNat old oldFound
      oldAssigned
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide
    have actAssigned : old.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      intro far
      rw [far, farNat] at gap
      have := old.exitEpoch.toNat_lt
      omega
    have exitU : u.exitEpoch = old.exitEpoch := keptC.exitEpoch oldAssigned
    have actU : u.activationEpoch = old.activationEpoch := keptC.activationEpoch actAssigned
    have exitW : w.exitEpoch = old.exitEpoch := keptP.exitEpoch oldAssigned
    have actW : w.activationEpoch = old.activationEpoch := keptP.activationEpoch actAssigned
    have epochU : old.exitEpoch.toNat = (getCurrentEpoch counted).toNat := by
      rw [← exitU]
      exact exitC.2
    have actLt : old.activationEpoch.toNat < (getCurrentEpoch counted).toNat := by
      rw [← actU]
      exact exitC.1
    have laterNat := UInt64.le_iff_toNat_le.mp h.later
    have nearNat := h.near
    have previous := getPreviousEpoch_toNat pulled
    have exitWNat : w.exitEpoch.toNat = (getCurrentEpoch counted).toNat := by
      rw [exitW]
      exact epochU
    have actWNat : w.activationEpoch.toNat = old.activationEpoch.toNat := by rw [actW]
    have activeAt (e : Epoch) (low : w.activationEpoch.toNat ≤ e.toNat)
        (high : e.toNat < w.exitEpoch.toNat) : isActiveAt pulled e v.toNat = true :=
      isActiveAt_eq_true_iff.mpr ⟨w, foundW, by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
        exact ⟨low, high⟩⟩
    have activeR : isActiveAt pulled (getPreviousEpoch pulled) v.toNat = true ∨
        isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true := by
      rcases Nat.lt_or_ge (getCurrentEpoch pulled).toNat (getCurrentEpoch counted).toNat with
        before | same
      · exact .inr (activeAt _ (by omega) (by omega))
      · exact .inl (activeAt _ (by omega) (by omega))
    have notSlashed : w.slashed = false ∨ anc.finalizedCheckpoint.epoch.toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ w.withdrawableEpoch.toNat := by
      cases slashed : w.slashed
      · exact .inl rfl
      · have delayed := slashed_waits (shared.append fromFin) h.genesis toPulled tailC h.early
          h.caps h.delay foundW slashed unslashedC
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

/-- D-4: the keys whose exit R reads. -/
theorem bud_exiting :
    (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, eR pulled v) +
      (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, eR pulled v) +
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
    · rcases Finset.mem_union.mp member with member | member <;>
        exact (Finset.mem_filter.mp member).2
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
      (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = false, exitQ tailC v.toNat)) ≤
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
      ((K5 counted V).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = false) := by
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
        ((K5 counted V).filter fun v => (pinTerms config pulled anc fin).exitingB v.toNat = false))
    omega

/-- D-8 (deposit queue): deposits applied on R's branch to V keys, weight 3. -/
theorem bud_deposits (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (∑ v ∈ V, credDepR events v.toNat) ≤ (pinTerms config pulled anc fin).queueDep := sorry

/-- Two charges of a run at one position are the same charge. -/
private theorem charge_unique {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {c d : DepartureCharge} (hc : c ∈ tail.departureCharges) (hd : d ∈ tail.departureCharges)
    (same : c.index = d.index) : c = d :=
  List.inj_on_of_nodup_map (DirectSafety.departureCharges_run_indices tail) hc hd same

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
  obtain ⟨stop⟩ := Stop.exists (fromFin.append tailC) v.toNat
  -- the charge of `tailC`
  obtain ⟨c0, member0, index0, amount0⟩ : ∃ c ∈ tailC.departureCharges,
      c.index = v.toNat ∧ exitQ tailC v.toNat = c.amount := by
    cases found : tailC.departureCharges.find? fun c =>
        c.index == v.toNat && decide (c.epoch ≤ (getCurrentEpoch counted).toNat) with
    | none => simp [exitQ, found] at charged
    | some c =>
      have both := List.find?_some found
      simp only [Bool.and_eq_true, beq_iff_eq] at both
      exact ⟨c, List.mem_of_find?_eq_some found, both.1, by simp [exitQ, found]⟩
  have inTail : c0 ∈ (fromFin.append tailC).departureCharges := by
    rw [Run.departureCharges_append]
    exact List.mem_append_right _ member0
  obtain ⟨c, chosen⟩ : ∃ c, stop.charge = some c := by
    cases hc : stop.charge with
    | none =>
      have selected := stop.selected
      rw [hc] at selected
      exact absurd index0 (selected.2 c0 inTail)
    | some c => exact ⟨c, rfl⟩
  have selected := stop.selected
  rw [chosen] at selected
  have cEq : c = c0 := charge_unique _ selected.1 inTail (selected.2.1.trans index0.symm)
  subst cEq
  -- the ends
  obtain ⟨w, final, _⟩ := (fromFin.append tailC).registryLifecycle.validators v.toNat val initial
  have cleanEnd := clean w final
  have unslashed : val.slashed = false := by
    cases flag : val.slashed with
    | false => rfl
    | true =>
      obtain ⟨last, located, marked⟩ :=
        (fromFin.append tailC).slashedPersistence v.toNat val initial flag
      have same := Option.some.inj (located.symm.trans final)
      subst last
      simp [cleanEnd] at marked
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

/-- The epoch rewards of a key over a run are at most the rate for each epoch of the run.

Only the steps after the key's departure charge count, and the key is in the registry from then.

So the bound is needed for a step only when the key is in the registry at its start. -/
private theorem riseScan_snd_le (v high R : ℕ) {x : ForkedBeaconState preset}
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (bound : ∀ {m n : ForkedBeaconState preset} (step : Step config checks m n),
      tail.Contains step → v < m.state.validators.data.size →
        epochRewards v step ≤
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
      obtain ⟨seen, -⟩ := cond
      obtain ⟨c, member, same⟩ := (riseScan_fst v high pre).mp seen
      obtain ⟨w, found, -, -⟩ := pre.departure_charge_exit c member
      have inside : v < m.state.validators.data.size := by
        rw [same] at found
        exact (Array.getElem?_eq_some_iff.mp found).1
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
  have gainMax : (pinTerms config pulled anc fin).gainRateMax =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((getBaseRewardPerIncrement preset
          (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
            (getTotalActiveBalance pulled).toOption.getD 0 / 4
          else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := rfl
  obtain ⟨P, gainLe, rateAll⟩ : ∃ P : ℕ,
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
    by_cases anyOk : ∃ total perIncrement : Gwei,
        getBaseRewardPerIncrement preset total = .ok perIncrement
    · obtain ⟨total, perIncrement, perOk⟩ := anyOk
      obtain ⟨pq, pqOk⟩ :=
        quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
      refine ⟨pq.toNat, ?_, fun toM inside => rate_of_guard h toM inside pqOk⟩
      rw [gainMax, pqOk]
      simp only [Except.toOption, Option.getD_some, le_refl]
    · refine ⟨0, ?_, fun _ _ total perIncrement _ perOk =>
        absurd ⟨total, perIncrement, perOk⟩ anyOk⟩
      simp
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
      exact epochRewards_le step altair nEarly v inside
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
        (PinSplit5.effectiveAt_le_capMax (shared.append (fromFin.append pre)) h.genesis h.caps
          mEarly v)
        (rateAll (fromFin.append pre) (by simp only at mEpoch ⊢; omega)))
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
    (pinTerms config pulled anc fin).newKeySlack < (events.map (syncDebit v.toNat)).sum :=
  sorry

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
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    (pinTerms config pulled anc fin).lowEB v.toNat ≤
      exitQ tailC v.toNat + (events.map (syncDebit v.toNat)).sum :=
  sorry

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
  have floor := existing_low_or_floor h fromFin tailC replayed v member w found activated charged
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
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have near := h.near
  have called := UInt64.le_iff_toNat_le.mp h.called
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      (fromFin.append tailC).Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat :=
    step_band_of_guard h (fromFin.append tailC) near pulledOk
  have debits := (PinSplit5.Run.syncDebits_le (fromFin.append tailC) h.fulu h.early
    (getCurrentEpoch pulled).toNat replayed pulledTotal.toNat band
    (B.image fun v : ValidatorIndex => v.toNat)).1
  have covered := sum_toNat_le (S := B) (P := B.image fun v : ValidatorIndex => v.toNat)
    (fun i => (events.map (syncDebit i)).sum) fun v member => Finset.mem_image_of_mem _ member
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
  have totalEq : ((getTotalActiveBalance pulled).toOption.getD 0).toNat = pulledTotal.toNat := by
    rw [pulledOk]
    rfl
  rw [seatsEq, totalEq, Nat.le_div_iff_mul_le (lt_max_of_lt_left Nat.one_pos)]
  have epochs : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
  have window := Nat.mul_le_mul_right (PinSplit5.syncEnvelope preset pulledTotal.toNat)
    (Nat.mul_le_mul_right preset.SYNC_COMMITTEE_SIZE.toNat
      (Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochs))
  have unit : max 1 (pinTerms config pulled anc fin).newKeySlack ≤
      (pinTerms config pulled anc fin).newKeySlack + 1 := by omega
  calc B.card * max 1 (pinTerms config pulled anc fin).newKeySlack
      ≤ B.card * ((pinTerms config pulled anc fin).newKeySlack + 1) := Nat.mul_le_mul_left _ unit
    _ ≤ _ := each
    _ ≤ _ := covered
    _ ≤ _ := debits
    _ ≤ _ := by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using window

/-- The keys of `K5` that are not exiting at the call and that C's branch charges are few.

A key is charged if the run has a departure charge at its position.

They are at most the keys that `queueKeys` counts.

Those are the keys with a large charge, the low keys and the keys that lose seats. -/
private theorem charged_count (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (((K5 counted V).filter fun v =>
      (pinTerms config pulled anc fin).exitingB v.toNat = false).filter
        fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card ≤
      (pinTerms config pulled anc fin).queueKeys := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨events, replayed⟩ := (fromFin.append tailC).balanceEvents_ok h.early
    (getCurrentEpoch pulled).toNat
  set S := ((K5 counted V).filter fun v =>
      (pinTerms config pulled anc fin).exitingB v.toNat = false).filter
        fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat with hS
  have big := card_big_charges_le h tailC S
  set small := S.filter fun v => ¬ (pinTerms config pulled anc fin).exitFloor ≤
    exitQ tailC v.toNat with hSmall
  have claim : ∀ v ∈ small, (pinTerms config pulled anc fin).lowB v.toNat = true ∨
      (pinTerms config pulled anc fin).newKeySlack < (events.map (syncDebit v.toNat)).sum := by
    intro v member
    obtain ⟨inS, notBig⟩ := Finset.mem_filter.mp member
    obtain ⟨inK5, charged⟩ := Finset.mem_filter.mp inS
    obtain ⟨inFilter, -⟩ := Finset.mem_filter.mp inK5
    exact small_charge_claim h fromFin tailC replayed v inFilter charged
      (Nat.lt_of_not_ge notBig)
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

/-- K5 (`queueRise`): the rise of exiting keys after their exit starts on C's branch. -/
theorem bud_queueRise (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) :
    3 * (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = false, riseQ tailC highC v.toNat) ≤
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
        (fun v => (pinTerms config pulled anc fin).exitingB v.toNat = false),
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
      (s := (K5 counted V).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = false)
      (f := fun v : ValidatorIndex => riseQ tailC highC v.toNat)
    have each := Finset.sum_le_card_nsmul
      (((K5 counted V).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = false).filter
          fun v => riseQ tailC highC v.toNat ≠ 0)
      (fun v : ValidatorIndex => riseQ tailC highC v.toNat)
      (preset.upwardBand + (pinTerms config pulled anc fin).depth *
        (pinTerms config pulled anc fin).gainRateMax)
      fun v _ => riseQ_le h tailC highC endEpochC v.toNat
    have subset : (((K5 counted V).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = false).filter
          fun v => riseQ tailC highC v.toNat ≠ 0) ⊆
        (((K5 counted V).filter fun v =>
          (pinTerms config pulled anc fin).exitingB v.toNat = false).filter
            fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat) := by
      intro v member
      obtain ⟨inside, nonzero⟩ := Finset.mem_filter.mp member
      refine Finset.mem_filter.mpr ⟨inside, ?_⟩
      by_contra none
      exact nonzero (riseQ_eq_zero tailC highC v.toNat fun c charged same =>
        none ⟨c, charged, same⟩)
    have count := (Finset.card_le_card subset).trans (charged_count h tailC)
    rw [smul_eq_mul] at each
    rw [← sumEq]
    calc _ ≤ 3 * (((((K5 counted V).filter fun v =>
            (pinTerms config pulled anc fin).exitingB v.toNat = false)).filter
          fun v => riseQ tailC highC v.toNat ≠ 0).card *
        (preset.upwardBand + (pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).gainRateMax)) := Nat.mul_le_mul_left _ each
      _ ≤ _ := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ count)

/-- K5 (`exitingRise`): the keys whose exit R reads. -/
theorem bud_exitingRise (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (pinTerms config pulled anc fin).rise v.toNat) ≤
      (pinTerms config pulled anc fin).exitingRise := by
  have _ := h
  classical
  have exitingRise : (pinTerms config pulled anc fin).exitingRise =
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).exitingB i = true,
        (pinTerms config pulled anc fin).rise i := by
    simp only [pinTerms, decide_eq_true_eq]
  have apart : Disjoint
      ((K5 counted V).filter fun v => (pinTerms config pulled anc fin).exitingB v.toNat = true)
      ((K6 pulled counted).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = true) := by
    refine Finset.disjoint_left.mpr fun v first second => ?_
    have active := (Finset.mem_filter.mp (Finset.mem_filter.mp second).1).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp first).1).2.1 active
  rw [← Finset.sum_union apart, exitingRise]
  refine sum_toNat_le (pinTerms config pulled anc fin).rise fun v selected => ?_
  have exiting : (pinTerms config pulled anc fin).exitingB v.toNat = true := by
    rcases Finset.mem_union.mp selected with chosen | chosen <;>
      exact (Finset.mem_filter.mp chosen).2
  have found : ∃ w, pulled.validators.data[v.toNat]? = some w := by
    obtain ⟨-, -, read⟩ := (by simpa only [pinTerms, decide_eq_true_eq] using exiting :
      _ ∧ _ ∧ ((pulled.validators.data[v.toNat]?).map fun w =>
        decide (w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).getD false = true)
    exact validator_of_flag (.inr read)
  obtain ⟨w, found⟩ := found
  exact mem_positions_filter config pulled anc fin found exiting

/-- K5 (`exitingCredits` with `credits`): C's proposer credits to K5 keys, weight 3.

The consolidation amounts are not here: `bud_consolidations` charges them, so they are added to the
bound.

The `syncProposer` part of the bound is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `exitingCredits`.

The compounding of the credits, a tenth of each key's amount rounded down, is in the bound.

The two further bands of each credited K5 key are in `bud_exitingBands`. -/
theorem bud_exitingCredits (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * (2 * ((∑ v ∈ (K5 counted V), propC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), propN tailC highC v.toNat / 10))) +
        22 * ((pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).exitingCredits +
        20 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) := sorry

/-- D-7 (credits): C's non-attestation credits to keys counted once.

The consolidation amounts are not here either: `bud_consolidations` charges them.

The `syncProposer` part of `credits` is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `credits`.

The compounding of the credits, a tenth of each key's amount rounded down, is in the bound.

The rounding slacks of the credited keys of `K4` and `K5` are paid by `creditedKeys`. -/
theorem bud_credits (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * ((∑ v ∈ (K4 pulled counted V), credC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), credC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), propC tailC highC v.toNat) +
      (∑ v ∈ (K4 pulled counted V), credN tailC highC v.toNat / 10) +
      (∑ v ∈ (K6 pulled counted), credN tailC highC v.toNat / 10) +
      (∑ v ∈ (K5 counted V), propN tailC highC v.toNat / 10) +
      (∑ v ∈ (K4 pulled counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), bandC tailC highC v.toNat)) +
        11 * ((pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        10 * ((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
          (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
          (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat)) :=
  sorry

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

/-- The consolidation credits of C's branch, charged to `consolidationsX` (the S9 ruling).

The run from the finalized block's state X to C's state has the run from the split as its tail.

`Run.consolidation_credits_le_X_targets` bounds the credits to a set of targets by the caps at X of
the due entries of X's queue that name them, over the whole run from X.

The run to R's state bounds the credits to V the same way.

The sets `V`, `K4`, `K5` and `K6` are disjoint, so the sum over their union is at most the caps of X's
queue: `consolidationsX`, as `high ≤` the epoch of the call and X is within the withdrawal delay.

A key of `V` or `K5` weighs three, and the others one.

Each applied entry also adds one upward band to its target's rise, so the left side has `upwardBand`
for each due entry of X's queue.

An entry is charged its cap at X, which is at least `MAX_EFFECTIVE_BALANCE`, so three bands are at
most three tenths of it.

The bound `3.3 · X ≤ (33 · X + 9) / 10` is the charge of `consolidationsX` in `pinReserve`.

Deeper than the withdrawal delay `consolidationsX` is 0, so the setting's `shallow` is used here. -/
theorem bud_consolidations (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (band : 10 * preset.upwardBand ≤ preset.MAX_EFFECTIVE_BALANCE.toNat) :
    ((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
      (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, consAmt events v.toNat)) +
      preset.upwardBand * (dueAt fin highC (K4 pulled counted V) +
        dueAt fin highC (K6 pulled counted) + 3 * dueAt fin highC (K5 counted V) +
        3 * dueAt fin high V) ≤
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10 := by
  classical
  have shallow := h.shallow
  have early := h.early
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨shared⟩ := h.toFin
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp h.called
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by omega
  have withinC : highC + 2 ≤ (getCurrentEpoch fin).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by omega
  have withinR : high + 2 ≤ (getCurrentEpoch fin).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by omega
  obtain ⟨eventsFin, replayedFin⟩ := fromFin.balanceEvents_ok early highC
  obtain ⟨eventsFinR, replayedFinR⟩ := fromFin.balanceEvents_ok early high
  have wholeC := Apriori.Internal.balanceEvents_append fromFin tailC highC replayedFin replayedC
  have wholeR := Apriori.Internal.balanceEvents_append fromFin tail high replayedFinR replayed
  obtain ⟨Kall, hKall⟩ : ∃ K : Finset ValidatorIndex,
      K = K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted := ⟨_, rfl⟩
  have boundC := PinSplit.Run.consolidation_credits_le_X_targets (config := config)
    (checks := checks) shared h.genesis h.caps (fromFin.append tailC) electra early highC wholeC
    endEpochC withinC delay (Kall.image UInt64.toNat)
  have boundR := PinSplit.Run.consolidation_credits_le_X_targets (config := config)
    (checks := checks) shared h.genesis h.caps (fromFin.append tail) electra early high wholeR
    endEpoch withinR delay (V.image UInt64.toNat)
  have injective : Function.Injective UInt64.toNat := fun _ _ same => UInt64.toNat_inj.mp same
  simp only [injective.mem_finset_image] at boundC boundR
  have amountC : (∑ v ∈ Kall, consAmt eventsC v.toNat) ≤
      ((dueList fin electra highC Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    rw [← Finset.sum_image (f := fun i => consAmt eventsC i)
      (fun _ _ _ _ e => UInt64.toNat_inj.mp e)]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundC
    simp only [consAmt, List.filter_append, List.map_append, List.sum_append]
    exact Nat.le_add_left _ _
  have amountR : (∑ v ∈ V, consAmt events v.toNat) ≤
      ((dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    rw [← Finset.sum_image (f := fun i => consAmt events i)
      (fun _ _ _ _ e => UInt64.toNat_inj.mp e)]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundR
    simp only [consAmt, List.filter_append, List.map_append, List.sum_append]
    exact Nat.le_add_left _ _
  -- The target sets are disjoint.
  have d45 : Disjoint (K4 pulled counted V) (K5 counted V) := by
    rw [Finset.disjoint_left]
    intro v h4 h5
    simp only [K4, K5, Finset.mem_filter] at h4 h5
    exact h5.2.1 h4.1
  have d46 : Disjoint (K4 pulled counted V) (K6 pulled counted) := by
    rw [Finset.disjoint_left]
    intro v h4 h6
    simp only [K4, K6, Finset.mem_filter] at h4 h6
    exact h6.2.2 h4.2.1
  have d56 : Disjoint (K5 counted V) (K6 pulled counted) := by
    rw [Finset.disjoint_left]
    intro v h5 h6
    simp only [K5, K6, Finset.mem_filter] at h5 h6
    exact h5.2.1 h6.1
  have d456 : Disjoint (K4 pulled counted V ∪ K5 counted V) (K6 pulled counted) :=
    Finset.disjoint_union_left.mpr ⟨d46, d56⟩
  have dKV : Disjoint Kall V := by
    rw [hKall, Finset.disjoint_left]
    intro v hk hv
    simp only [Finset.mem_union] at hk
    rcases hk with (h4 | h5) | h6
    · simp only [K4, Finset.mem_filter] at h4
      exact h4.2.2.2 hv
    · simp only [K5, Finset.mem_filter] at h5
      exact h5.2.2 hv
    · simp only [K6, Finset.mem_filter] at h6
      exact h6.2.2 (h.voting v hv).1
  -- The amounts and the entries split over the three sets of C's keys.
  have splitAmount : (∑ v ∈ Kall, consAmt eventsC v.toNat) =
      (∑ v ∈ K4 pulled counted V, consAmt eventsC v.toNat) +
        (∑ v ∈ K5 counted V, consAmt eventsC v.toNat) +
        (∑ v ∈ K6 pulled counted, consAmt eventsC v.toNat) := by
    rw [hKall, Finset.sum_union d456, Finset.sum_union d45]
  have splitEntries : (dueList fin electra highC Kall).length =
      (dueList fin electra highC (K4 pulled counted V)).length +
        (dueList fin electra highC (K5 counted V)).length +
        (dueList fin electra highC (K6 pulled counted)).length := by
    rw [hKall, dueList_length_union fin electra highC d456,
      dueList_length_union fin electra highC d45]
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
  have floorC := floorOf (dueList fin electra highC Kall)
  have floorR := floorOf (dueList fin electra high V)
  -- Both runs charge entries of X's queue, at most those that `consolidationsX` counts.
  have total : ((dueList fin electra highC Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum +
      ((dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum ≤
      (pinTerms config pulled anc fin).consolidationsX := by
    have hcX : (pinTerms config pulled anc fin).consolidationsX =
        (((((fin.pendingConsolidations electra).data.toList.filterMap fun c =>
          fin.validators.data[c.sourceIndex.toNat]?).filter fun v =>
            !v.slashed && decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
              fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)).sum := by
      unfold pinTerms
      dsimp only
      simp only [shallow, electra, ↓reduceIte, ↓reduceDIte]
    have laterC := dueList_sum_mono fin electra highLe Kall
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have laterR := dueList_sum_mono fin electra highLeR V
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have union := dueList_sum_union fin electra (getCurrentEpoch pulled).toNat dKV
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have all := dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat (Kall ∪ V)
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    rw [hcX]
    omega
  rw [dueAt_eq fin electra highC, dueAt_eq fin electra highC, dueAt_eq fin electra highC,
    dueAt_eq fin electra high]
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  generalize (dueList fin electra highC (K4 pulled counted V)).length = d4 at *
  generalize (dueList fin electra highC (K5 counted V)).length = d5 at *
  generalize (dueList fin electra highC (K6 pulled counted)).length = d6 at *
  generalize (dueList fin electra highC Kall).length = dK at *
  generalize (dueList fin electra high V).length = dV at *
  generalize ((dueList fin electra highC Kall).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PK at *
  generalize ((dueList fin electra high V).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PV at *
  generalize (pinTerms config pulled anc fin).consolidationsX = cX at *
  have bandsK : preset.upwardBand * (d4 + d6 + 3 * d5 + 3 * dV) ≤
      3 * (preset.upwardBand * (dK + dV)) := by
    have : d4 + d6 + 3 * d5 + 3 * dV ≤ 3 * (dK + dV) := by omega
    calc preset.upwardBand * (d4 + d6 + 3 * d5 + 3 * dV)
        ≤ preset.upwardBand * (3 * (dK + dV)) := Nat.mul_le_mul_left _ this
      _ = 3 * (preset.upwardBand * (dK + dV)) := by ring
  have bandsM : 10 * (preset.upwardBand * (dK + dV)) ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat * dK + preset.MAX_EFFECTIVE_BALANCE.toNat * dV := by
    calc 10 * (preset.upwardBand * (dK + dV))
        = (10 * preset.upwardBand) * (dK + dV) := by ring
      _ ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * (dK + dV) := Nat.mul_le_mul_right _ band
      _ = preset.MAX_EFFECTIVE_BALANCE.toNat * dK + preset.MAX_EFFECTIVE_BALANCE.toNat * dV :=
        Nat.mul_add _ _ _
  omega

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

/-- R1 (branchR): R's credits to V keys since the split, weight 3.

The slashing of a key on R's branch is charged here for the keys of `K4` and `K5`.

So is a sync debit of R that `rise` omits.

The keys of `K4` weigh one, and those of `K5` weigh three.

The `syncProposer` part of `proposerCredit` is not used by `credR`, which leaves out sync events, so
`bud_sync` takes it. -/
theorem bud_branchR (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (∑ v ∈ V, credR tail high v.toNat) +
        3 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) +
        (∑ v ∈ (K4 pulled counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR events v.toNat)) +
        3 * (∑ v ∈ (K5 counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR events v.toNat)) +
        (∑ v ∈ (K6 pulled counted),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR events v.toNat)) ≤
      (pinTerms config pulled anc fin).branchR := sorry

/-- The sync movement of a key is its sync credits plus its sync debits over the events. -/
private theorem syncF_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    syncF events v = (events.map (syncCredit v)).sum +
      (events.map (syncDebit v)).sum := by
  induction events with
  | nil => simp [syncF]
  | cons e rest ih =>
    unfold syncF at ih ⊢
    by_cases sync : e.source = .sync
    · simp only [List.filter_cons, sync, decide_true, ↓reduceIte, List.map_cons, List.sum_cons,
        syncCredit, syncDebit, keyCredit, keyDebit] at ih ⊢
      omega
    · simp only [List.filter_cons, sync, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons, syncCredit, syncDebit] at ih ⊢
      omega

/-- S1 (syncSeats): every seat, weight 3 for V, K4 and K5 and 1 for K6.

The proposer's share of the sync credits is in `syncF`, so the bound adds the `syncProposer` part
that `credits`, `exitingCredits` and `branchR` leave. -/
theorem bud_sync (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ V, (syncF events v.toNat + syncF eventsC v.toNat)) + (∑ v ∈ (K4 pulled counted V), (syncF events v.toNat + syncF eventsC v.toNat)) +
      (∑ v ∈ (K5 counted V), (syncF events v.toNat + syncF eventsC v.toNat))) +
      (∑ v ∈ (K6 pulled counted), (syncF events v.toNat + syncF eventsC v.toNat)) ≤
        (pinTerms config pulled anc fin).syncSeats +
          6 * ((pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer) := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp h.called
  have later := UInt64.le_iff_toNat_le.mp h.later
  have near := h.near
  -- the sync movement of a run from the split over any keys, at the pulled state's total
  have run : ∀ {e : BeaconState preset fork} (t : Run config checks ⟨fork, split⟩ ⟨fork, e⟩),
      (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
      ∀ (highE : ℕ) {evs : List (BalanceEvent preset)}, t.balanceEvents highE = .ok evs →
      ∀ keys : Finset ℕ, ∑ i ∈ keys, syncF evs i ≤
        ((getCurrentEpoch e).toNat + 1 - (getCurrentEpoch split).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinSplit5.syncSeatEnvelope preset pulledTotal.toNat := by
    intro e t within highE evs replayed keys
    have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
        t.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
          2 * T.toNat ≤ 3 * pulledTotal.toNat := by
      intro u w step member T read
      exact step_band_of_guard h (fromFin.append t) within pulledOk step
        ((Run.contains_append _ _ _).mpr (.inr member)) T read
    have moves := (PinSplit5.Run.syncDebits_le t h.fulu h.early highE replayed pulledTotal.toNat
      band keys).2
    exact (Finset.sum_le_sum fun i _ => (syncF_eq evs i).le).trans moves
  -- the four sets are pairwise disjoint
  have voters : ∀ v ∈ V, v ∈ AR pulled := fun v member => (h.voting v member).1
  have d1 : Disjoint V (K4 pulled counted V) := Finset.disjoint_left.mpr fun v first second =>
    (Finset.mem_filter.mp second).2.2.2 first
  have d2 : Disjoint (V ∪ K4 pulled counted V) (K5 counted V) :=
    Finset.disjoint_left.mpr fun v first second => by
      rcases Finset.mem_union.mp first with inV | inK4
      · exact (Finset.mem_filter.mp second).2.2 inV
      · exact (Finset.mem_filter.mp second).2.1 (Finset.mem_filter.mp inK4).1
  have d3 : Disjoint (V ∪ K4 pulled counted V ∪ K5 counted V) (K6 pulled counted) :=
    Finset.disjoint_left.mpr fun v first second => by
      have notR := (Finset.mem_filter.mp second).2.2
      have active := (Finset.mem_filter.mp second).1
      rcases Finset.mem_union.mp first with first | inK5
      · rcases Finset.mem_union.mp first with inV | inK4
        · exact notR (voters v inV)
        · exact notR (Finset.mem_filter.mp inK4).2.1
      · exact (Finset.mem_filter.mp inK5).2.1 active
  have sets : ∑ v ∈ V, (syncF events v.toNat + syncF eventsC v.toNat) +
      ∑ v ∈ K4 pulled counted V, (syncF events v.toNat + syncF eventsC v.toNat) +
      ∑ v ∈ K5 counted V, (syncF events v.toNat + syncF eventsC v.toNat) +
      ∑ v ∈ K6 pulled counted, (syncF events v.toNat + syncF eventsC v.toNat) =
      ∑ v ∈ V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted,
        (syncF events v.toNat + syncF eventsC v.toNat) := by
    rw [Finset.sum_union d3, Finset.sum_union d2, Finset.sum_union d1]
  have covered := sum_toNat_le (S := V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted)
    (P := (V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted).image
      fun v : ValidatorIndex => v.toNat)
    (fun i => syncF events i + syncF eventsC i) fun v member => Finset.mem_image_of_mem _ member
  have first := run tail (Nat.le_succ _) high replayed
    ((V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted).image
      fun v : ValidatorIndex => v.toNat)
  have second := run tailC near highC replayedC
    ((V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted).image
      fun v : ValidatorIndex => v.toNat)
  generalize (V ∪ K4 pulled counted V ∪ K5 counted V ∪ K6 pulled counted).image
    (fun v : ValidatorIndex => v.toNat) = P at covered first second
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
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have firstDepth :
      (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth := by
    omega
  have secondDepth :
      (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth := by
    omega
  have secondDepthFin : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
    omega
  have firstLe := first.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ firstDepth)))
  -- The second run's seats weigh the envelope at the depth from the finalized state.
  --
  -- They weigh the proposer share at the depth from the anchor's finalized epoch.
  have secondLe : ∑ i ∈ P, syncF eventsC i ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env +
      depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share := by
    refine second.trans ?_
    rw [Nat.mul_add]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ secondDepthFin)))
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ secondDepth)))
  have union : ∑ v ∈ V, (syncF events v.toNat + syncF eventsC v.toNat) +
      ∑ v ∈ K4 pulled counted V, (syncF events v.toNat + syncF eventsC v.toNat) +
      ∑ v ∈ K5 counted V, (syncF events v.toNat + syncF eventsC v.toNat) +
      ∑ v ∈ K6 pulled counted, (syncF events v.toNat + syncF eventsC v.toNat) ≤
        depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * (env + share) +
        (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env +
        depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share) := by
    rw [sets]
    omega
  calc _ ≤ 3 * (depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
        (env + share) +
        (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env +
        depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share)) := by
        omega
    _ = _ := by ring

/-- W (`reserveW`, `flagged`, `seatShortfall`, K7, cS): whistleblower rewards on C's branch,
weight 3, are paid by the slashed key's own slack, or charged. -/
theorem bud_whistle (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ (K4 pulled counted V), (whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (K5 counted V), (whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (K6 pulled counted), (whistC tailC highC v.toNat : ℤ))) ≤
      -cK7 pulled counted - cS pulled counted V + (pinTerms config pulled anc fin).reserveW +
        (pinTerms config pulled anc fin).flagged + (pinTerms config pulled anc fin).seatShortfall :=
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
  have sV := two_le_three (stub_V (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC)
  have sN := stub_N (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC
  have sP := stub_P (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC
  have sJ := stub_J (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC
  have b1 := bud_exiting (config := config) (pulled := pulled) (anc := anc) (fin := fin)
    (counted := counted) (V := V)
  have b2 := bud_late (config := config) h
  have b3 := bud_queues (config := config) h tailC
  have b4 := bud_credits (config := config) h tailC highC endEpochC replayedC
  have b5 := bud_branchR (config := config) h tail high endEpoch replayed
  have b6 := bud_sync (config := config) h tail high replayed tailC highC replayedC
  have b7 := bud_fall (config := config) h
  have b8 := bud_rise (config := config) h
  have b10 := bud_deposits (config := config) h tail high endEpoch replayed
  have b11 := bud_queueRise (config := config) h tailC highC endEpochC
  have b12 := bud_exitingRise (config := config) h
  have b13 := bud_exitingCredits (config := config) h tailC highC endEpochC replayedC
  have b17 := bud_exitingBands (config := config) h tailC highC endEpochC
  have b18 := bud_pendingR (config := config) h
  -- `stub_J` reads `creditGain` only in its high regime.
  have gainHighLe : (if (pinTerms config pulled anc fin).gainHigh then
      (pinTerms config pulled anc fin).creditGain else 0) ≤
        (pinTerms config pulled anc fin).creditGain := by
    split <;> omega
  obtain ⟨fromFin⟩ := h.fromFin
  have b15 := bud_consolidations (config := config) h fromFin tail high endEpoch replayed highLeR
    tailC highC endEpochC replayedC highLe band
  have b16 := bud_exitedR (config := config) (pulled := pulled) (anc := anc) (fin := fin)
    (counted := counted)
  -- The band of each due entry naming a V key is paid by `bud_consolidations`' V share.
  have bandV : 3 * (preset.upwardBand * dueAt fin high V) ≤
      preset.upwardBand * (dueAt fin highC (K4 pulled counted V) +
        dueAt fin highC (K6 pulled counted) + 3 * dueAt fin highC (K5 counted V) +
        3 * dueAt fin high V) := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have b15' := Nat.le_trans (Nat.add_le_add_left bandV _) b15
  have qs := queues_split config pulled anc fin
  have b14 := bud_whistle (config := config) h tailC highC endEpochC replayedC
  have w4 : 0 ≤ ∑ v ∈ (K4 pulled counted V), (whistC tailC highC v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have w6 : 0 ≤ ∑ v ∈ (K6 pulled counted), (whistC tailC highC v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have b9 := bud_joining (config := config) (pulled := pulled) (anc := anc) (fin := fin)
  rw [pinReserve_eq_total]
  unfold PinTerms.total stake
  simp only [AC, AR, Q, eC, eR] at *
  simp only [Finset.sum_add_distrib] at sV sN sP sJ b2 b5 b6 b16 b18 ⊢
  zify at *
  have syncPos : 0 ≤ ∑ x ∈ K4 pulled counted V, (syncF events x.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have syncPosC : 0 ≤ ∑ x ∈ K4 pulled counted V, (syncF eventsC x.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have xPos : 0 ≤ (33 * ((pinTerms config pulled anc fin).consolidationsX : ℤ) + 9) / 10 := by
    positivity
  have proposerPos : 0 ≤ ((pinTerms config pulled anc fin).depth : ℤ) *
      ((pinTerms config pulled anc fin).syncProposer : ℤ) := by positivity
  -- A key of `K6` whose exit R reads weighs once in the drift and three times in `exiting`.
  have exitingK6 : 0 ≤ ∑ v ∈ K6 pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true, (balanceAt pulled v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have riseK6 : 0 ≤ ∑ v ∈ K6 pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true,
        ((pinTerms config pulled anc fin).rise v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  linarith

end Closure

end PinSum
end EthLib.Consensus.Models.Network
