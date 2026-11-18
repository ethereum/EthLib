module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Churn
public import EthLib.Consensus.Participation
public import EthLib.Consensus.Transition.EpochRewards
public import EthLib.Consensus.Transition.SyncAggregate

/-!
# The reserves of the quorum of a fast-confirmation call

A call of the fast confirmation rule counts the stake of honest voters in its pulled-up head state.

A later state that counts the same voters can hold a different total and different balances.

The reserves are meant to bound how much that changes the quorum, from the call's states alone.

One covers a later state on the call's own chain, the other a counting state on another branch.

A theorem proves the bound of the first, before Gloas from Fulu.

The drift premise of the checked-call headlines follows from it.

No theorem derives the bound of the second yet.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

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
  let joining := ∑ i ∈ positions with current i = false ∧ upcoming i = true, effective i
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

/-- The reserve of a call for a counting state that may be on another branch.

It reads the call's pulled-up head state, the target block's state and that block's finalized state.

It adds to the quorum reserve what a counting state of the target's epoch or the next can change.

It covers exits, the queues, credits since finality, late activations, sync seats and band changes.

The depth is the call's epoch plus 2, minus the finalized epoch of the target block's state.

Up to the seed lookahead plus one, the exit and consolidation queues add nothing.

Neither do the late activations at that depth.

Every epoch of that window was fixed before the branches split.

Rates are read at a quarter of the call's total active balance.

Inactivity scores and the queue of partial withdrawals are read at the finalized block's state. -/
def pinReserve (config : Config) (state ancestor finalizedState : BeaconState preset fork) : ℕ :=
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
  let quarter := max preset.EFFECTIVE_BALANCE_INCREMENT (totalGwei / 4)
  let perIncrement := ((getBaseRewardPerIncrement preset quarter).toOption.getD 0).toNat
  let base (i : ℕ) := effective i / inc * perIncrement
  let depositChurn := config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  let exitChurn := ((exitChurnLimit config state).toOption.getD 0).toNat
  let consolidationChurn := ((getConsolidationChurnLimit config state).toOption.getD 0).toNat
  let queues := 3 * (depth * depositChurn + capMax) +
    (if tight then 0 else 3 * (depth * (exitChurn + consolidationChurn) + 2 * capMax))
  let seatReward := total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat /
    WEIGHT_DENOMINATOR.toNat / slots / preset.SYNC_COMMITTEE_SIZE.toNat
  -- The inactivity score is read at the finalized block's state, with depth from its epoch.
  --
  -- That state lies on every branch, and a score rises by at most the bias per epoch on any.
  --
  -- So this bounds the score of a counting state, whose score can rise while the call's falls.
  let scoreFin (i : ℕ) := if altair : .altair ≤ fork then
      (((finalizedState.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  let depthFin := epoch.toNat + 2 - (getCurrentEpoch finalizedState).toNat
  -- Sync-seat penalties are charged in aggregate, by the sync-seat terms, not per key.
  let leak (i : ℕ) := 2 * base i +
    effective i * (scoreFin i + depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
  let gainRate (i : ℕ) := base i * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
    WEIGHT_DENOMINATOR.toNat
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
  -- A partial due by the next epoch was queued at least `partialDelay` epochs before it.
  --
  -- Within that depth it predates finality and sits in the queue of the finalized block's state.
  --
  -- Deeper, another branch can queue new partials, which withdraw at most the key's excess.
  let partialDelay := 1 + preset.MAX_SEED_LOOKAHEAD.toNat +
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  let partialsDue (i : ℕ) := if depth ≤ partialDelay + 1 then max (partialsX i) (partialsR i)
    else max (max (partialsX i) (partialsR i)) (actual i - preset.MIN_ACTIVATION_BALANCE.toNat)
  let fall (i : ℕ) :=
    let low := actual i - (depth * (leak i + gainRate i) + partialsDue i)
    if effective i ≤ low + preset.downwardBand then 0 else effective i - (low - low % inc)
  let capFor (i : ℕ) := if depth * gainRate i < inc then cap i else capMax
  let rise (i : ℕ) :=
    let high := actual i + depth * (gainRate i + leak i) + (partialsX i - partialsR i)
    -- Deeper than `partialDelay + 1`, the call's branch can pay partials that neither queue holds.
    --
    -- So the rise is the key's whole headroom.
    if depth ≤ partialDelay + 1 then
      if high ≤ effective i + preset.upwardBand then 0
      else min (capFor i) (high - high % inc) - effective i
    else capFor i - effective i
  let syncProposer := slots * preset.SYNC_COMMITTEE_SIZE.toNat *
    ((syncProposerReward (UInt64.ofNat seatReward)).toOption.getD 0).toNat
  let proposerCredit := (∑ i ∈ positions with (before i || current i) = true, base i) +
    syncProposer
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
  let whistleblowerR := (∑ i ∈ positions with slashed i = true ∧ recentSlashing i = true,
      effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let slashedR := (positions.filter fun i => slashed i = true ∧ recentSlashing i = true).card
  let late := if tight then 0 else
    3 * ∑ i ∈ positions with (validator i).any (fun v =>
      decide (v.activationEligibilityEpoch.toNat ≤ epoch.toNat) &&
        decide (finalized + preset.MAX_SEED_LOOKAHEAD.toNat < v.activationEpoch.toNat)), effective i
  let period := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat
  -- Every seat of every sync committee in the window counts, at the call's seat reward.
  --
  -- The window can include the call's previous period, which its state does not store.
  let syncSeats := 3 * (depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * seatReward)
  let syncFar := 3 * ((depth / period) * preset.SYNC_COMMITTEE_SIZE.toNat * period * slots *
    seatReward)
  let depositCredit := if electra : .pectra ≤ fork then
      (state.depositBalanceToConsume electra).toNat + depositChurn else 0
  let due := if electra : .pectra ≤ fork then
      (state.pendingConsolidations electra).data.toList.filter fun c =>
        ((validator c.sourceIndex.toNat).map fun v =>
          v.slashed || decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
    else []
  let dueStake := (due.map fun c => effective c.sourceIndex.toNat).sum
  let depositRecipients := preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
  let creditedKeys := depth * slots + (depth / period + 2) * preset.SYNC_COMMITTEE_SIZE.toNat +
    depth * depositRecipients + due.length
  let credits := depth * (proposerCredit + depositCredit) + dueStake +
    creditedKeys * preset.upwardBand + whistleblowerExtra
  let branchR := 3 * (whistleblowerR + inc * slashedR + depth * proposerCredit +
    inc * (depth * slots + preset.SYNC_COMMITTEE_SIZE.toNat))
  quorumReserve config state ancestor + (3 * exiting + queues + credits + branchR + late +
    syncSeats + syncFar + (∑ i ∈ positions with current i = true, rise i) +
    3 * (∑ i ∈ positions with current i = true, fall i))

/-- The pin reserve contains the quorum reserve. -/
theorem quorumReserve_le_pinReserve (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    quorumReserve config state ancestor ≤ pinReserve config state ancestor finalizedState := by
  unfold pinReserve
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
