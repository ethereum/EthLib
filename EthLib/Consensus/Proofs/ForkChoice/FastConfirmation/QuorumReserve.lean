module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.Transition.FfgJustification

/-!
# The reserves of the quorum of a fast-confirmation call

A call of the fast confirmation rule counts the stake of honest voters in its pulled-up head state.

A later state that counts the same voters can hold a different total and different balances.

The reserves bound by how much that changes the quorum, from the fields of the call's state alone.

`quorumReserve` covers a later state on the call's own chain.

`pinReserve` adds what a counting state on another branch can change since the finalized epoch.

This file holds only the definitions, so that the bounds and their consumers read one copy.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- The stake by which the quorum of the call can drift from the reference state to a later state.

The state is the pulled-up head state of the call, and the ancestor is the state of its target root.

Every term reads the state, except the queue of partial withdrawals, which the ancestor holds.

Every read is a function on natural numbers of the fields of the state.

Each equals the executable read whenever that read succeeds, as the lemmas on the reads show.

The reserve is twice the gain plus three times the loss.

```text
gain  = joining + min headroom (crossing + (recipients + debited) * upwardBand
          + debited * creditMax + transfers + depositGain)
loss  = sum of fall + creditedP * (increment + 2 * downwardBand + syncPMax) + maskBudget
```

- The gain is the rise of the total active balance over the next epoch.
  Validators that join the active set count in full.
  A validator that stays active gains at most the credit that crosses the upward band.
  Validators that receive a transfer, or that a block of the epoch debits, gain one band more.
- The loss is the fall of the stake of the active validators.
  A validator falls by its penalties and the partial withdrawals that the ancestor queue pays.
  Validators credited on the branch of the state, other than by sync rewards, add a band.
  The partial withdrawals that those credits hide add the mask budget.
- The credits and penalties of an epoch are bounds on the rewards of its end.
  Altair pays a share of the base reward for each flag, scaled by the previous-to-current ratio.
  Before Altair the three components of the attestation rewards and the inclusion reward count.
- From Electra the deposit churn and the pending consolidations that come due add transfers.
  Before Electra the deposits of a block add a gain at the largest effective balance.
-/
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
  let total := max inc (∑ i ∈ positions with current i, effective i)
  let root := (integerSquareroot (UInt64.ofNat total)).toNat
  let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
  let base (i : ℕ) := if .altair ≤ fork then effective i / inc * perIncrement
    else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
  let num := max 1 ((∑ i ∈ positions with before i, effective i) / inc)
  let den := max 1 (total / inc)
  let flagWeight := (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
  let seatReward := if .altair ≤ fork then
      total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
        slots / preset.SYNC_COMMITTEE_SIZE.toNat
    else 0
  let seats (i : ℕ) := if altair : .altair ≤ fork then
      ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
        (validator i).any (·.pubkey == key)).length
    else 0
  let sync (i : ℕ) := seats i * seatReward
  let depositChurn :=
    if .glamsterdam ≤ fork then
      let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat)
      min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat (limit - limit % inc)
    else
      let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total / config.CHURN_LIMIT_QUOTIENT.toNat)
      min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (limit - limit % inc)
  let score (i : ℕ) := if altair : .altair ≤ fork then
      (((state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  let delay := (getPreviousEpoch state).toNat - state.finalizedCheckpoint.epoch.toNat
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
        (seatReward * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
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

It starts with `quorumReserve`, which covers the call's own branch.

The other terms bound what a counting state of the target's epoch or the next can change.

```text
pinReserve = quorumReserve                               the call's branch
           + 3 * exiting                                 keys active only in the previous epoch
           + 3 * (depth * depositChurn + capMax)         the deposit queue
           + 3 * (depth * (exitChurn + consolidationChurn) + 2 * capMax)
                                                         the exit and consolidation queues
           + credits                                     credits other than attestation rewards
           + rise + 3 * fall                             band changes of each key on another branch
```

- The depth is the call's epoch plus 2, minus the finalized epoch of the target block's state.
- The exit and consolidation queues add nothing at a depth of at most the seed lookahead plus one.
  Every exit epoch in that window was fixed before the branches split.
- From Fulu, every Electra and Altair field it reads exists.

On mainnet the depth is typically 4.

There it costs about 1.05 to 1.41 points of the Byzantine threshold at an epoch's last slot.

It costs about 0.07 points at the middle of an epoch.

These figures come from three mainnet states.

On those states it stays below 1.5 points through depth 5, and below 5 points through depth 42.

From depth 6 the exit and consolidation queues add about 0.08 points for each further epoch.

So the reserve grows with the number of epochs since finality.
-/
def pinReserve (config : Config) (state ancestor : BeaconState preset fork) : ℕ :=
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
  let total := max inc (∑ i ∈ positions with current i = true, effective i)
  let root := (integerSquareroot (UInt64.ofNat total)).toNat
  let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
  let base (i : ℕ) := effective i / inc * perIncrement
  let depositChurn :=
    let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total / config.CHURN_LIMIT_QUOTIENT.toNat)
    min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (limit - limit % inc)
  let exitChurn := ((exitChurnLimit config state).toOption.getD 0).toNat
  let consolidationChurn := ((getConsolidationChurnLimit config state).toOption.getD 0).toNat
  let queues := 3 * (depth * depositChurn + capMax) +
    (if tight then 0 else 3 * (depth * (exitChurn + consolidationChurn) + 2 * capMax))
  let seatReward := total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat /
    WEIGHT_DENOMINATOR.toNat / slots / preset.SYNC_COMMITTEE_SIZE.toNat
  let seats (i : ℕ) := if altair : .altair ≤ fork then
      ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
        (validator i).any (·.pubkey == key)).length +
      ((state.nextSyncCommittee altair).value.pubkeys.toList.filter fun key =>
        (validator i).any (·.pubkey == key)).length
    else 0
  let score (i : ℕ) := if altair : .altair ≤ fork then
      (((state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  let leak (i : ℕ) := 2 * base i + slots * seats i * seatReward +
    effective i * (score i + depth * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
  let gainRate (i : ℕ) := base i * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
    WEIGHT_DENOMINATOR.toNat
  let partials (i : ℕ) := if electra : .pectra ≤ fork then
      (((state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ epoch.toNat + 1).map
          (·.amount.toNat)).sum
    else 0
  let fall (i : ℕ) :=
    let low := actual i - (depth * (leak i + gainRate i) + partials i)
    if effective i ≤ low + preset.downwardBand then 0 else effective i - (low - low % inc)
  let capFor (i : ℕ) := if depth * gainRate i < inc then cap i else capMax
  let rise (i : ℕ) :=
    let high := actual i + depth * (gainRate i + leak i)
    if high ≤ effective i + preset.upwardBand then 0
    else min (capFor i) (high - high % inc) - effective i
  let syncProposer := slots * preset.SYNC_COMMITTEE_SIZE.toNat *
    (seatReward * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
  let proposerCredit := (∑ i ∈ positions with (before i || current i) = true, base i) +
    syncProposer
  -- The slashable keys of the window that the whistleblower term of `quorumReserve` leaves out.
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
  let whistleblowerR := (∑ i ∈ positions with slashed i = true ∧ (validator i).any (fun v =>
      decide (finalized + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ v.withdrawableEpoch.toNat)),
      effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let depositCredit := if electra : .pectra ≤ fork then
      (state.depositBalanceToConsume electra).toNat + depositChurn else 0
  let due := if electra : .pectra ≤ fork then
      (state.pendingConsolidations electra).data.toList.filter fun c =>
        ((validator c.sourceIndex.toNat).map fun v =>
          v.slashed || decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
    else []
  let dueStake := (due.map fun c => effective c.sourceIndex.toNat).sum
  let depositRecipients := preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
  let creditedKeys := depth * slots + 2 * preset.SYNC_COMMITTEE_SIZE.toNat +
    depth * depositRecipients + due.length
  let credits := depth * (proposerCredit + depositCredit) + dueStake +
    creditedKeys * preset.upwardBand + whistleblowerExtra
  let branchR := 3 * (whistleblowerR + depth * proposerCredit +
    inc * (depth * slots + preset.SYNC_COMMITTEE_SIZE.toNat))
  quorumReserve config state ancestor + 3 * exiting + queues + credits + branchR +
    (∑ i ∈ positions with current i = true, rise i) +
    3 * (∑ i ∈ positions with current i = true, fall i)

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- Every honest voter set of a call keeps its stake in each counting state, up to the pin reserve.

The call reads the pulled-up head state and the current target of an honest store.

The counting state belongs to an honest store, and is in the target's epoch or the next.

Each held chain that it is built from must contain the finalized checkpoint of the target's state.

Then the quorum voters of the counting state and the voters of the call fit the bound.
-/
def PinDriftWithin (horizon : Epoch) (last : ℕ) : Prop :=
  -- Fast confirmation was implemented at Fulu, so no pre-Electra queue or churn case arises.
  .fusaka ≤ fork →
  ∀ u ∈ J, ∀ n (head : Root) (pulled anc : BeaconState preset fork) (target : Checkpoint),
    (e.world n).time ≤ last →
    ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).blockStates[target.root]? = some anc →
    ∀ w ∈ J, ∀ k (counted : BeaconState preset fork), (e.world k).time ≤ last →
    CountedState ((e.world k).state w) config counted →
    target.epoch ≤ getCurrentEpoch counted →
    (getCurrentEpoch counted).toNat ≤ target.epoch.toNat + 1 → getCurrentEpoch counted ≤ horizon →
    -- Every held chain that the counting state is built from reads the finalized checkpoint.
    --
    -- That checkpoint is the one of the target block's state, as `pinReserve` reads it.
    (∀ (r : Root) (base : BeaconState preset fork),
      ((e.world k).state w).blockStates[r]? = some base →
      (counted = base ∨
        ∃ (checks' : SignatureChecks) (slot : Slot),
          processSlots config checks' base slot = .ok counted) →
      ((e.world k).state w).getCheckpointBlock r anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root) →
    ∀ (voters : Finset ValidatorIndex) (total pulledTotal : Gwei),
    (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters pulled) →
    getTotalActiveBalance counted = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
    3 * stake (fun v => balanceAt counted v.toNat) (quorumVoters counted) +
        3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
      2 * total.toNat + pulledTotal.toNat + pinReserve config pulled anc +
        3 * stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∈ voters}

end EthLib.Consensus.Models.Network
