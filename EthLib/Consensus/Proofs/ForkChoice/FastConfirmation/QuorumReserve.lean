module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
public import EthLib.Consensus.Churn
public import EthLib.Consensus.Participation
public import EthLib.Consensus.Transition.EpochRewards
public import EthLib.Consensus.Transition.SyncAggregate

/-!
# The reserves of the quorum of a fast-confirmation call

A call of the fast confirmation rule counts the stake of honest voters in its pulled-up head state.

A later state that counts the same voters can hold a different total and different balances.

The reserves use only the call's states to account for changes in the quorum.

The quorum reserve covers a later state on the call's own chain, from Fulu to before Gloas.

The pin reserve also covers a counting state on another branch, from Fulu to before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- The effective balance of validators that join the active set at the next epoch. -/
def joiningStake (state : BeaconState preset fork) : ℕ :=
  ∑ i ∈ Finset.range state.validators.data.size with
      isActiveAt state (getCurrentEpoch state) i = false ∧
        isActiveAt state (getCurrentEpoch state + 1) i = true,
    balanceAt state i

/-- The stake by which the quorum of a call can drift from its state to a later state of its chain.

The state is the call's pulled-up head state, and the ancestor is the state of its target block.

Every term reads the state, except the queue of partial withdrawals, which the ancestor holds.

It takes the total, the base and sync rewards, the churn and the finality delay from their reads.

It bounds the drift, before Gloas from Fulu.

The reserve is twice the gain of the total plus three times the loss of the voters' stake.

The gain counts validators that join the active set, and the band-crossing rises of the others.

The loss counts each active validator's penalties and due partial withdrawals, rounded to bands.

The rewards and penalties of an epoch enter as upper bounds on those of its end. -/
def quorumReserve (config : Config) (state ancestor : BeaconState preset fork) : ℕ :=
  let epoch := getCurrentEpoch state
  let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  let slots := preset.SLOTS_PER_EPOCH.toNat
  let p := parameters preset fork
  let positions := Finset.range state.validators.data.size
  let validator (i : ℕ) := state.validators.data[i]?
  let effective (i : ℕ) := balanceAt state i
  let actual (i : ℕ) := ((state.balances.data[i]?).map (·.toNat)).getD 0
  let cap (i : ℕ) :=
    ((validator i).map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).getD 0
  let capMax := if .pectra ≤ fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    else preset.MAX_EFFECTIVE_BALANCE.toNat
  let current (i : ℕ) := isActiveAt state epoch i
  let upcoming (i : ℕ) := isActiveAt state (epoch + 1) i
  let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
  let recent (i : ℕ) := before i || current i
  let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
  let totalGwei := (getTotalActiveBalance state).toOption.getD 0
  let total := totalGwei.toNat
  let base (i : ℕ) := ((getBaseReward state totalGwei (UInt64.ofNat i)).toOption.getD 0).toNat
  let num := max 1 ((∑ i ∈ positions with before i, effective i) / inc)
  let den := max 1 (total / inc)
  let flagWeight := (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
  let seatReward := if .altair ≤ fork then ((syncParticipantReward state).toOption.getD 0).toNat
    else 0
  let seats (i : ℕ) := if altair : .altair ≤ fork then
      ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
        (validator i).any (·.pubkey == key)).length
    else 0
  let sync (i : ℕ) := seats i * seatReward
  let depositChurn := ((depositChurnLimit config state).toOption.getD 0).toNat
  let score (i : ℕ) := if altair : .altair ≤ fork then
      (((state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  let delay := ((getFinalityDelay state).toOption.getD 0).toNat
  let inactivity (i : ℕ) := if .altair ≤ fork then
      effective i * (score i + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
    else if preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY.toNat < delay then
      4 * base i + effective i * delay / p.INACTIVITY_PENALTY_QUOTIENT.toNat
    else 0
  let credit (i : ℕ) :=
    (if .altair ≤ fork then base i * flagWeight * num / (WEIGHT_DENOMINATOR.toNat * den)
     else 3 * (base i * max num den / den) + base i) + slots * sync i
  let penalty (i : ℕ) :=
    (if .altair ≤ fork then base i else 3 * base i) + inactivity i + slots * sync i
  -- The proposer share of the sync rewards of a full epoch, paid per seat as in the sync step.
  let syncProposer := if .altair ≤ fork then
      slots * preset.SYNC_COMMITTEE_SIZE.toNat *
        ((syncProposerReward (UInt64.ofNat seatReward)).toOption.getD 0).toNat
    else 0
  let proposerCredit := (∑ i ∈ positions with recent i, base i) + syncProposer
  let whistleblower := (∑ i ∈ positions with (validator i).any (fun v =>
      v.activationEpoch ≤ epoch && epoch < v.withdrawableEpoch), effective i) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let depositCredit := if electra : .pectra ≤ fork then
      (state.depositBalanceToConsume electra).toNat + depositChurn else 0
  let due := if electra : .pectra ≤ fork then
      (state.pendingConsolidations electra).data.toList.filter fun c =>
        ((validator c.sourceIndex.toNat).map fun v =>
          v.slashed || decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
    else []
  let dueStake := (due.map fun c => effective c.sourceIndex.toNat).sum
  let proposers := if .altair ≤ fork then slots else 2 * slots
  let depositRecipients := if .pectra ≤ fork then preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
    else slots * preset.MAX_DEPOSITS.toNat
  let recipients := (if .pectra ≤ fork then depositRecipients else 0) + due.length + proposers
  let nP := state.slot.toNat - epoch.toNat * slots + 1
  let debited := ((if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
    (if .pectra ≤ fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) * nP
  let transfers := depositCredit + dueStake + proposerCredit + whistleblower
  let depositGain := if .pectra ≤ fork then 0 else depositRecipients * capMax
  let slashBack (i : ℕ) :=
    if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
  let syncP (i : ℕ) := nP * sync i
  let blockDeposits := if h : fork < .hegota then
      (if .pectra ≤ fork then 0
       else min (preset.MAX_DEPOSITS.toNat * nP) (state.eth1DepositIndex h).toNat)
    else 0
  let creditedP :=
    (if proposerCredit = 0 ∧ seatReward = 0 ∧ positions.filter (slashed ·) = ∅ then 0 else nP) +
      blockDeposits
  let creditMax := positions.sup fun i => if upcoming i then credit i else 0
  let joining := joiningStake state
  let crossing := ∑ i ∈ positions with upcoming i,
    if effective i < cap i then
      (let top := actual i + slashBack i + syncP i + credit i
       if effective i + preset.upwardBand < top then top - effective i else 0)
    else (if preset.upwardBand < credit i then credit i else 0)
  let headroom := ∑ i ∈ positions with upcoming i, (capMax - effective i)
  let gain := joining + min headroom (crossing + (recipients + debited) * preset.upwardBand +
    debited * creditMax + transfers + depositGain)
  let partials (i : ℕ) := if electra : .pectra ≤ fork then
      (((ancestor.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch ≤ epoch).map (·.amount.toNat)).sum
    else 0
  let fall (i : ℕ) :=
    let low := min (actual i - syncP i) (effective i) - (partials i + penalty i)
    if effective i ≤ low + preset.downwardBand then 0 else effective i - (low - low % inc)
  let syncPMax := positions.sup fun i => if current i then syncP i else 0
  let whistleblowerP :=
    (∑ i ∈ positions with slashed i, effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let maskBudget := if .pectra ≤ fork then
      min (proposerCredit + whistleblowerP)
        (preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat *
          (capMax - preset.MIN_ACTIVATION_BALANCE.toNat))
    else 0
  let loss := (∑ i ∈ positions with current i, fall i) +
    creditedP * (inc + 2 * preset.downwardBand + syncPMax) + maskBudget
  2 * gain + 3 * loss

/-- A key's cap at a state, `0` past the registry. -/
def PinTerms.capAt (z : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  ((z.state.validators.data[i]?).map fun v =>
    (withdrawalMaxEffectiveBalance preset z.fork v).toNat).getD 0

/-- The amounts of the queued partial withdrawals of a key that are due by a cutoff epoch. -/
def PinTerms.dueAmount (state : BeaconState preset fork) (electra : .pectra ≤ fork) (i : ℕ)
    (cutoff : ℕ) : ℕ :=
  (((state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
    w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ cutoff).map (·.amount.toNat)).sum

/-- The envelope of one sync seat's reward per slot, at three halves of a total.

The reward is the base rewards of a total, times the sync weight, per slot and per member.

The base rewards of a total are at most the base reward factor times its root plus 2. -/
def PinTerms.syncEnvelope (preset : Preset) (total : ℕ) : ℕ :=
  preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt (3 * total / 2) + 2) *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
      preset.SYNC_COMMITTEE_SIZE.toNat

/-- The pin's bound on another branch's total: three halves of the call's total. -/
def PinTerms.wide (state : BeaconState preset fork) : ℕ :=
  3 * ((getTotalActiveBalance state).toOption.getD 0).toNat / 2

/-- Whether a key of the call's state is unslashed and exits by the next epoch.

It must also not be withdrawable by the finalized epoch of the call's ancestor. -/
def PinTerms.exitedSlashable (anc pulled : BeaconState preset fork) (i : ℕ) : Bool :=
  decide ((pulled.validators.data[i]?.map (·.slashed)).getD false = false ∧
    ((pulled.validators.data[i]?).map fun v =>
      decide (v.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).getD false = true ∧
    ((pulled.validators.data[i]?).any fun v =>
      decide (anc.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat)) = true)

/-- The charges in the pin reserve and the quantities used to compute them. -/
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
  otherGain : ℕ
  flagRate : ℕ
  slashLeak : ℕ
  high : ℕ → ℕ
  capFor : ℕ → ℕ
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
  withdrawnRB : ℕ → Bool

/-- The pin reserve as the sum of its named terms, with their weights. -/
def PinTerms.total (t : PinTerms preset) : ℕ :=
  t.quorum + (3 * t.exiting + t.queues + t.credits + t.branchR + t.late +
    t.syncSeats + (∑ i ∈ t.positions with t.current i = true, t.rise i) + t.joinRise +
    3 * (∑ i ∈ t.positions with t.current i = true, t.fall i) +
    3 * t.exitingRise + t.exitingCredits + t.exitingBands + t.queueRise + t.reserveW + t.flagged +
    t.seatShortfall + (33 * t.consolidationsX + 9) / 10 + t.exitedR + t.pendingR + t.creditGain +
    t.creditUnits + t.syncLeak + 3 * t.unitGain * t.consolidationsXCount)

/-- The charges for changes to a call's quorum on either branch.

The inputs include the pulled-up head state and the state of its target block.

The target block's finalized state gives both branches a common starting point. -/
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
  let cap (i : ℕ) := PinTerms.capAt ⟨fork, state⟩ i
  let capMax := preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  let finalized := ancestor.finalizedCheckpoint.epoch.toNat
  let depth := epoch.toNat + 2 - finalized
  let tight := decide (depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
  let recentSlashing (i : ℕ) := (validator i).any fun v =>
    decide (finalized + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ v.withdrawableEpoch.toNat)
  -- A key whose exit the call reads is active at the previous or the current epoch.
  --
  -- It is unslashed or recently slashed, and it exits by the next epoch.
  let exitingB (i : ℕ) := decide ((before i || current i) = true ∧
    (slashed i = false ∨ recentSlashing i = true) ∧
    ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true)
  let exiting := ∑ i ∈ positions with exitingB i = true, effective i
  let totalGwei := (getTotalActiveBalance state).toOption.getD 0
  let total := totalGwei.toNat
  -- The rates are read at a quarter of the call's total.
  --
  -- A counting state that keeps that much has a base reward per increment at most twice this one.
  --
  -- Below eighteen increments the rates are read at a fifth of an increment, below any total.
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
  -- It holds within the band of totals that the guard at the finalized state gives.
  --
  -- The pin derives that band from the guard, and does not assume it.
  let wide := PinTerms.wide state
  let round (amount : ℕ) := amount - amount % inc
  let exitChurn := if .glamsterdam ≤ fork then
      round (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (wide / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat))
    else DirectSafety.Apriori.activationExitChurn preset config wide
  let consolidationChurn := if .glamsterdam ≤ fork then
      round (wide / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat)
    else DirectSafety.Apriori.consolidationChurn preset config wide
  -- Another branch's consolidation carry was set from one epoch's churn, possibly before finality.
  --
  -- So it is charged at the larger of the finalized block's carry and the churn here.
  let consolidationCarry := max (if electra : .pectra ≤ fork then
      (finalizedState.consolidationBalanceToConsume electra).toNat else 0) consolidationChurn
  -- Before Gloas, the exit carry is at most one epoch's exit churn, which `depositChurn` caps.
  let exitCarry := max capMax depositChurn
  let depthFin := epoch.toNat + 2 - (getCurrentEpoch finalizedState).toNat
  -- A deposit postponed at the head of the queue lets the deposits behind it spend the carry.
  --
  -- So the deposits applied from the finalized block's state are at most its carry and the churn.
  let depositCarry := if electra : .pectra ≤ fork then
      (finalizedState.depositBalanceToConsume electra).toNat else 0
  let queueDep := 3 * (depthFin * depositChurn + depositCarry)
  -- The exit and consolidation churn of the window, and the two carries.
  let queueWindow := depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry
  let queueExit := if tight then 0 else 3 * queueWindow
  let queues := queueDep + queueExit
  -- A sync seat's reward is bounded by its envelope at three halves of the call's total.
  --
  -- The integer reward is not monotone in the total, and the envelope is.
  --
  -- `div_mul_div_sqrt_le` bounds the reward of any total up to that much by it.
  let syncEnvelope := PinTerms.syncEnvelope preset total
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
      PinTerms.dueAmount state electra i (epoch.toNat + 1) else 0
  let partialsX (i : ℕ) := if electra : .pectra ≤ fork then
      PinTerms.dueAmount finalizedState electra i (epoch.toNat + 1) else 0
  -- The rates are read at a computed envelope of the key's effective balance on any branch.
  --
  -- That is at least its effective balance here and at the finalized block's state.
  --
  -- A key can rise by its leak at the cap and its partials, then by a band, up to its cap.
  --
  -- The leak counts from the finalized block's state: both branches keep an update made since.
  let finEB (i : ℕ) := balanceAt finalizedState i
  let ebUp (i : ℕ) :=
    let top := actual i + depthFin * leakAt (cap i) i + (partialsX i - partialsR i) +
      preset.downwardBand + inc - 1
    max (max (effective i) (finEB i)) (min (cap i) (top - top % inc))
  let leak (i : ℕ) := leakAt (ebUp i) i
  -- The flag reward of one increment over one epoch, at the pin's rate.
  let flagRate := perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
    WEIGHT_DENOMINATOR.toNat
  let gainRate (i : ℕ) := ebUp i / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  -- Exit churn starts at the request epoch plus one plus the seed lookahead.
  --
  -- A partial becomes due no earlier than that epoch plus the minimum withdrawability delay.
  --
  -- Using only that delay is conservative by five epochs on mainnet.
  --
  -- Within this shorter window, every partial that falls due was already queued at the start.
  let partialDelay := config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  let partialsDue (i : ℕ) := max (partialsX i) (partialsR i)
  -- Outside that window, the queue reads alone do not cover partials requested on another branch.
  --
  -- The reserve falls back to charging the key's full effective balance at the call.
  --
  -- The floor reads the finalized block's balance.
  --
  -- The call reads no state between the finalized block and the split.
  --
  -- Both branches can share a dip there that this branch's later credits would hide.
  let actualFin (i : ℕ) := ((finalizedState.balances.data[i]?).map (·.toNat)).getD 0
  -- A key whose exit was set by the finalized block's state can be swept here and slashed there.
  --
  -- There it keeps at least its finalized effective balance or its rounded finalized balance.
  let exitBeforeFin (i : ℕ) := (validator i).any fun v =>
    decide (v.exitEpoch.toNat ≤ (getCurrentEpoch finalizedState).toNat)
  let bF (i : ℕ) := if exitBeforeFin i then max (finEB i) (actualFin i - actualFin i % inc) else 0
  -- The floor starts at the finalized block's balance, at most the key's cap there.
  let capFin (i : ℕ) := PinTerms.capAt ⟨fork, finalizedState⟩ i
  let base0 (i : ℕ) := min (actualFin i) (capFin i)
  -- The first pass after the finalized block's state charges its stored effective balance.
  --
  -- That can exceed the state's balance, and later debits are charged against the floor's start.
  let carry (i : ℕ) := leakAt (finEB i - actualFin i + inc) i + 1
  let floorC (i : ℕ) :=
    -- The leak is read at the floor's start plus the band and one increment.
    --
    -- Each epoch also loses at most one unit to the rounding of the rates.
    let low := base0 i - (carry i +
      depthFin * (leakAt (base0 i + preset.downwardBand + inc) i + gainRate i + 1) +
      partialsDue i)
    -- On another branch the key can keep an effective balance that this branch's update raised.
    --
    -- Away from the downward band of its start, it keeps its finalized effective balance.
    --
    -- Near that band, it keeps at least its rounded balance.
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
  -- The kept branch includes equality at the gain bound and uses the shorter partial window.
  --
  -- Its rise is then its rounded balance; otherwise it is its whole headroom.
  let keptArm (i : ℕ) : Bool :=
    decide (depthFin ≤ partialDelay) && decide (11 * depth * (gainRate i + 1) ≤ ebUp i)
  -- The top of a key before the downward band.
  --
  -- It is its balance, the window's gain and leak, and its net partials.
  let high (i : ℕ) := actual i + depthFin * (gainScaled i + leak i) + (partialsX i - partialsR i)
  -- The rise bounds the balance from the finalized block's state on, as `ebUp` does.
  let rise (i : ℕ) :=
    -- Outside the shorter partial window or above the gain bound, charge the full headroom.
    if keptArm i then
      -- On another branch the key can keep an effective balance that this branch's update lowered.
      --
      -- It is at most the balance at that update plus the downward band, rounded down.
      --
      -- It is also its effective balance at the finalized block's state or a rounded balance since.
      let kept := high i + preset.downwardBand
      min (capFor i) (min (kept - kept % inc) (max (finEB i) (high i - high i % inc))) -
        effective i
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
  -- A due consolidation can be applied on one branch and not the other.
  --
  -- Its source can be slashed on one branch only, which drops it there.
  --
  -- Within `partialDelay` of the finalized block's state, the window applies only queued entries.
  --
  -- Each is in that state's queue, with an unslashed source withdrawable by the next epoch.
  --
  -- Each moves at most the source's effective balance, which stays within its cap there.
  --
  -- An exited key cannot switch to compounding.
  --
  -- Deeper, the charge is moot: `fall` charges every key's whole effective balance at this depth.
  let consolidationSourcesX (electra : .pectra ≤ fork) :=
    ((finalizedState.pendingConsolidations electra).data.toList.filterMap fun c =>
      finalizedState.validators.data[c.sourceIndex.toNat]?).filter fun v =>
        !v.slashed && decide (v.withdrawableEpoch.toNat ≤ epoch.toNat + 1)
  let consolidationsX := if depthFin ≤ partialDelay then
      (if electra : .pectra ≤ fork then
        ((consolidationSourcesX electra).map fun v =>
          (withdrawalMaxEffectiveBalance preset fork v).toNat).sum
      else 0)
    else 0
  -- Each entry of `consolidationsX` can raise its target by one more increment.
  --
  -- That increment earns `unitGain`, three times.
  let consolidationsXCount := if depthFin ≤ partialDelay then
      (if electra : .pectra ≤ fork then (consolidationSourcesX electra).length else 0)
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
  -- They also hold the sync seats of each period from the finalized block's epoch to the next one.
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
  --
  -- It can also be its balance at the finalized state, after in-epoch debits before that state.
  let whistleblowerR := ((∑ i ∈ positions with slashed i = true ∧ recentSlashing i = true,
      max (effective i + rise i) (finEB i)) + seatExcess * inc) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let slashedRB (i : ℕ) := decide (slashed i = true ∧ recentSlashing i = true)
  let slashedR := (positions.filter fun i => slashedRB i = true).card
  -- The largest gain rate of one key, its gain rate at the largest effective balance.
  let gainRateMax := capMax / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  -- A late key is charged three times its effective balance here, and its rise once.
  --
  -- A key active by the finalized state can have a larger balance there, and its reward is charged.
  let lateB (i : ℕ) := (validator i).any (fun v =>
    decide (v.activationEligibilityEpoch.toNat ≤ epoch.toNat) &&
      decide (finalized + preset.MAX_SEED_LOOKAHEAD.toNat < v.activationEpoch.toNat))
  let late := if tight then 0 else
    ∑ i ∈ positions with lateB i = true,
      (3 * effective i + rise i +
        3 * ((finEB i - effective i - rise i + (p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
          p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat))
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
  -- A credit can raise a key's effective balance by one more increment than its amount rounds to.
  --
  -- That increment earns the flag rewards over the depth, plus two units per epoch for the floors.
  --
  -- Each credited key pays it once, and a key pays two more if the call reads its exit.
  let unitGain := depth * (flagRate + 2)
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
  let exitingRise := ∑ i ∈ positions with exitingB i = true, rise i
  -- An exiting key can still be credited as a proposer.
  --
  -- `credits` charges those credits once at eleven tenths and their bands once.
  --
  -- These charge them twice more, also at eleven tenths, rounded up; `exitingBands` has the bands.
  --
  -- A due consolidation's credit is charged by `consolidationsX`, to every target.
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
  -- Such a key uses little churn, so each one whose `lowEB` falls below `newKeyFloor` is counted.
  --
  -- `lowEB` leaves out sync-seat debits.
  --
  -- A key at or above `newKeyFloor` falls below the bound only with sync debits over `newKeySlack`.
  --
  -- `newKeySeats` counts those keys by the same Markov step as new keys.
  --
  -- Every key not yet withdrawable after the finalized epoch counts.
  --
  -- Its exit here is not its exit there.
  --
  -- A key not active by this epoch here, or created on the other branch, activates there late.
  --
  -- It activates only with at least the activation balance, which it keeps until then.
  --
  -- The pin's drift bound proves that it keeps at least `newKeyFloor` from its activation.
  --
  -- That floor is less its own sync-seat debits and pending partial payments.
  let newKeyFloor := 2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
    preset.MAX_EFFECTIVE_BALANCE.toNat / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - inc
  -- An exit outside these counts consumes at least `exitFloor` of churn.
  --
  -- It is the ejection balance less an increment, kept positive and at most `newKeyFloor`.
  let exitFloor := max 1 (min (config.EJECTION_BALANCE.toNat - inc) newKeyFloor)
  let newKeySlack := newKeyFloor - exitFloor
  let lowB (i : ℕ) := decide ((validator i).any (fun v =>
    decide (finalized < v.withdrawableEpoch.toNat) &&
      decide (v.activationEpoch.toNat ≤ epoch.toNat)) ∧ lowEB i < newKeyFloor)
  let lowKeys := (positions.filter fun i => lowB i = true).card
  -- Outside the tight window, keys can start to exit on the other branch.
  --
  -- The queues admit at most this many keys at `exitFloor` each.
  --
  -- The `+ 2` counts one key at each end of the window that the churn covers only in part.
  --
  -- `lowKeys` adds every key whose `lowEB` is below `newKeyFloor`.
  --
  -- A key not active by this epoch here, or created there, keeps `newKeyFloor` from its activation.
  --
  -- That floor is less its own sync-seat debits and pending partial payments in the window.
  --
  -- One whose effective balance ends below `exitFloor` has those debits above `newKeySlack`.
  --
  -- So has an existing key whose `lowEB` is at least `newKeyFloor`.
  --
  -- The seats of the window debit at most `depthFin·slots·SIZE·syncEnvelope` in all.
  --
  -- So `newKeySeats` counts the keys that sync debits can bring below.
  --
  -- Within `partialDelay`, a key not active by this epoch is paid no pending partial in the window.
  --
  -- Deeper, the count is moot: `fall` charges every key's whole effective balance at this depth.
  --
  -- After an exit starts, the key's proposer and due-consolidation credits are in `exitingCredits`.
  --
  -- Its whistleblower credits are in `reserveW`, `flagged` and the drift's slashed keys.
  let newKeySeats := depthFin * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope /
    max 1 newKeySlack
  -- A carry is a balance that can let several keys exit, so it counts by `exitFloor` too.
  let queueKeys := queueWindow / exitFloor + 2 + lowKeys + newKeySeats
  -- An exiting key weighs three times, so each credited one needs two more upward bands.
  --
  -- Those are the keys whose exit the call reads and those the queues let exit there.
  let exitingCount := (positions.filter fun i => exitingB i = true).card
  let exitingBands := 2 * (exitingCount + queueKeys) * preset.upwardBand
  let queueRise := if tight then 0 else
    3 * queueKeys * (preset.upwardBand + depth * gainRateMax)
  -- A key slashed on another branch credits its whistleblower, the block's proposer.
  --
  -- A key still active there can offset three times the reward with its own counted stake.
  --
  -- A key that has exited there by then has no such balance in the count, so it is charged here.
  --
  -- Those are the keys whose exit the call reads.
  --
  -- Outside the tight window, they include the keys that the queues let exit on the other branch.
  --
  -- A key's balance at the finalized state can exceed its balance and rise here.
  --
  -- Its debits between the start of that epoch and the finalized state are in neither.
  let exitedSlashable := ∑ i ∈ positions with PinTerms.exitedSlashable ancestor state i = true,
    max (effective i + rise i) (max (bF i) (finEB i))
  let reserveW := 3 * (exitedSlashable + (if tight then 0 else
      queueWindow + queueKeys * (preset.upwardBand + depth * gainRateMax))) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  -- Test whether the balance floor after the slashing penalty can cover the reward in the count.
  --
  -- Charge three times the reward if the floor is too low, and account for seat debits separately.
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
  -- A key can start an exit on this branch after the split and not on the other.
  --
  -- With an exit epoch before this one it is inactive here, but active in the other quorum.
  --
  -- Its exit was set here after the split, at the finalized epoch.
  --
  -- So it lands at the earliest `MAX_SEED_LOOKAHEAD + 1` epochs later; the tight window has none.
  --
  -- Its effective balance there is at most its effective balance here and its rise.
  let exitedRB (i : ℕ) := (validator i).any (fun v =>
    decide (finalized + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ v.exitEpoch.toNat) &&
      decide (v.exitEpoch.toNat + 1 ≤ epoch.toNat))
  let exitedR := ∑ i ∈ positions with exitedRB i = true, (effective i + rise i)
  -- A credit on the other branch alone compounds its gains over the rest of the window.
  --
  -- While eleven gains over the depth stay below the cap, `credits`' eleven tenths pay a new key's.
  --
  -- A consolidation credit's gains are charged at weight three, for every target.
  --
  -- Every key's whistleblower and sync credits on the other branch are charged their gains too.
  --
  -- They are read at every key slashable there, its credits, and the seats.
  --
  -- A key's whistleblower base is the larger of its envelope and its effective balance plus rise.
  --
  -- Its credits count at eleven tenths, with one increment for each credited key.
  --
  -- Its seat debits from the finalized block's state count as a second seat term.
  --
  -- A key whose own gain stays low compounds past that bound too, so its gains count in both.
  --
  -- One floor of all a key's flows bounds its gains, and each split by kind costs an increment's.
  --
  -- Past that bound, each deposit the window can apply to a new key is also charged up to the cap.
  let consolidationGain := consolidationsX / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  -- A key whose only flows are seat debits pays a unit too.
  --
  -- Its seats are those of the call's branch beyond the two shared at the split.
  --
  -- They are also those of the shared segment.
  let seatUnits := (depth / period + (depthFin / period + 2)) * preset.SYNC_COMMITTEE_SIZE.toNat
  let creditUnits := (creditedKeys + seatUnits + 2 * (exitingCount + queueKeys)) * unitGain
  -- The leak of one increment over the window, at the largest score of the finalized state.
  let slashLeak := depthFin * (2 * perIncrement +
    inc * (scoreMaxFin + depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat) + 1)
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
        unitGain * (consolidationsXCount + 2 * slashedR) + slashedR * slashLeak) /
          -- The credits include the keys' own whistleblower credits, so two quotient steps go.
          (p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 2) +
      -- C's seat flows, and R's and the shared segment's seat debits.
      (depth + depthFin) * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope +
        depth * syncProposer)
  let otherGain := otherCredits / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  let creditLow :=
    (33 * depth * consolidationGain + 11 * depth * otherGain +
      30 * depth * (flagRate + 1) + 9) / 10
  let lowRate := 11 * depth * (gainRateMax + 1) ≤ capMax
  let creditCap := if lowRate then 0
    else depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax
  let creditGain := creditLow + creditCap
  -- A key here that is not yet eligible can be topped up on the other branch alone.
  --
  -- It can then become eligible there and activate deep in the window, while inactive here.
  --
  -- Its effective balance here and its rise are charged once; the top-up is the other branch's.
  --
  -- A key active by the finalized state can have a larger balance there, and its reward is charged.
  let pendingRB (i : ℕ) := (validator i).any (fun v =>
    decide (epoch.toNat < v.activationEligibilityEpoch.toNat) &&
      v.activationEpoch == FAR_FUTURE_EPOCH)
  let pendingR := if tight then 0 else
    ∑ i ∈ positions with pendingRB i = true,
      (effective i + rise i +
        3 * ((finEB i - effective i - rise i + (p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
          p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat))
  -- A key that joins at the next epoch here can activate earlier on another branch.
  --
  -- There it gains across its band, so its rise is charged once.
  let joinRise := ∑ i ∈ positions with current i = false ∧ upcoming i = true, rise i
  { quorum := quorumReserve config state ancestor, exiting, queues, queueDep, queueExit, credits,
    branchR, late, syncSeats, rise, fall, positions, current, exitingRise, exitingCredits,
    queueRise, reserveW, flagged, seatShortfall, consolidationsX, exitedR, depth, syncProposer,
    proposerCredit, exitingBands, pendingR, creditGain, creditUnits, syncLeak, unitGain,
    consolidationsXCount, exitBeforeFin, bF, perIncrement, depthFin, scoreMaxFin,
    otherGain, flagRate, slashLeak, high, capFor, keptArm, creditLow, creditCap,
    gainHigh := !decide lowRate, pendingRB,
    joining := joiningStake state,
    joinRise,
    exitingB, lateB, exitedRB, slashedR, slashedRB,
    withdrawnRB := fun i => (validator i).any fun v =>
      decide (v.withdrawableEpoch.toNat ≤ epoch.toNat + 1),
    tight, queueKeys, queueWindow, gainRateMax, exitFloor, lowKeys, lowB,
    lowEB, newKeySeats, newKeySlack, newKeyFloor, leakAt, ebUp, leak, partialsDue, base0, gainRate,
    floorC, drop }

/-- The reserve of a call for a counting state that may be on another branch.

It bounds drift in the quorum inequality at the target's epoch or the next.

The proof covers only `fusaka ≤ fork < glamsterdam` under the pin's drift assumptions.

The reserve's other fork branches are not proved to bound the drift.

The branches can differ in both active stake and validator balances after their last shared state.

The reserve accounts for these differences without reading the other branch's state.

Within the partial window, the rise uses the kept branch even at equality in the gain test.

Past that window, measured from the finalized state, the fall charges the call's effective balance.
-/
def pinReserve (config : Config) (state ancestor finalizedState : BeaconState preset fork) : ℕ :=
  (pinTerms config state ancestor finalizedState).total

/-- The pin reserve contains the quorum reserve. -/
theorem quorumReserve_le_pinReserve (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    quorumReserve config state ancestor ≤ pinReserve config state ancestor finalizedState := by
  unfold pinReserve PinTerms.total pinTerms
  dsimp only
  exact Nat.le_add_right _ _

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- An honest voter set of a call keeps its stake in each counting state, up to the quorum reserve.

The call reads the pulled-up head state and the current target of an honest store.

The counting state belongs to an honest store whose chain reads that target.

It is the state of that chain's block or a later slot of it, in the target's epoch or the next.

Then the stake of unslashed active voters of the call drifts by at most the call's reserve.

The reserve reads the call's block at the target root, so two honest stores may collide instead. -/
def QuorumDriftWithin (horizon : Epoch) (last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n (head : Root) (pulled anc : BeaconState preset fork) (target : Checkpoint),
    (e.world n).time ≤ last →
    ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).blockStates[target.root]? = some anc →
    ∀ w ∈ J, ∀ k (root : Root) (rootState state : BeaconState preset fork),
    (e.world k).time ≤ last → ((e.world k).state w).blockStates[root]? = some rootState →
    ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
    (state = rootState ∨ ∃ slot, processSlots config checks rootState slot = .ok state) →
    target.epoch ≤ getCurrentEpoch state →
    (getCurrentEpoch state).toNat ≤ target.epoch.toNat + 1 → getCurrentEpoch state ≤ horizon →
    ∀ (voters : Finset ValidatorIndex) (total pulledTotal : Gwei),
    (∀ v ∈ voters, v ∈ activeVoters pulled ∧ (slashedFlagAt state v.toNat).getD false = false) →
    getTotalActiveBalance state = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
    2 * total.toNat + 3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
        2 * pulledTotal.toNat + 3 * stake (fun v => balanceAt state v.toNat) voters +
          quorumReserve config pulled anc ∨
      HonestCollision (e := e) last

end EthLib.Consensus.Models.Network
