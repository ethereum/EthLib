module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
public import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.Safety
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBeforeAltair
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Monotone.Defs

/-!
# The a priori drift bound

The numbers that bound the drift of accountable safety from a reference state.

Each reads only observables of the reference state and the length of the window.

The two statements of the bound close the module.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Uint64

variable {preset : Preset}

/-! ## The bound

The definitions below state the a priori drift bound.

Each one is a ceiling on a rule of the specification, or a number read at the reference state.

The churn and slashing rules of Electra stay the same through Fulu.

The window of a bound at `x` and `high` holds the epochs from the epoch of `x` through `high + 1`.

The docstrings call their count `H`.

The last epoch that the budgets read is the epoch of `x` plus `H` plus one.

"Within the window" in a budget means at or before that epoch.

The docstrings write the paper's symbols in ASCII, and each is defined where it first appears.
-/

namespace Apriori

/-- The active-count path before the fork: `A_0` is given, and `A_(t+1) = A_t + c A_t`.

Here `c` is the validator churn limit of Phase 0, a count of validators per epoch.

It is the active count over the churn quotient, and at least the minimum churn of Phase 0.

The path is a derived bound on the active count, not a rule of the specification. -/
def activeCountPath (config : Config) (start : Nat) : Nat → Nat
  | 0 => start
  | t + 1 => activeCountPath config start t + cohortCap config (activeCountPath config start t)

/-- An upper envelope `delta T` of the Electra balance churn, in Gwei, at an active stake `T`.

It rounds the stake over the churn quotient down to an increment.

It then takes the minimum if that is larger.

The balance churn of EIP-7251 takes the larger value first, and rounds after.

So `delta T` is at least that churn, and equal when the minimum is a multiple of the increment.

The minimum `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA` is a multiple in the mainnet and minimal configs. -/
def balanceChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (total / config.CHURN_LIMIT_QUOTIENT.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)

/-- The activation and exit part `activationExitChurn T` of the balance churn.

It is the activation and exit churn of EIP-7251, with `delta T` in place of the balance churn. -/
def activationExitChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (balanceChurn preset config total)

/-- The consolidation part `C T` of the balance churn.

It is the consolidation churn of EIP-7251, with `delta T` in place of the balance churn.

Both parts grow with `delta`, so each is an upper envelope of its churn in the specification. -/
def consolidationChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  balanceChurn preset config total - activationExitChurn preset config total

/-- The whistleblower quotient `WQ` of the window: the quotient before the fork, or from Electra.

They divide the whistleblower reward of a slashing, in Phase 0 and from Electra. -/
def whistleblowerQuotient (preset : Preset) (forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then preset.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  else preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat

/-- The minimum slashing penalty quotient `MSPQ` of the window.

A window before the fork takes the least quotient of Phase 0, Altair and Bellatrix.

These divide the initial penalty of a slashing at each of those forks.

The least quotient gives the largest penalty, so before the fork this is an envelope. -/
def minSlashingPenaltyQuotient (preset : Preset) (forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then
    min (min preset.MIN_SLASHING_PENALTY_QUOTIENT.toNat
      preset.MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR.toNat)
      preset.MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX.toNat
  else preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA.toNat

/-- The divisor of the leak penalty: the score bias times the least inactivity penalty quotient.

From Altair it divides by the bias times the fork's quotient, and later forks keep Bellatrix's.

Phase 0's quotient is included in the minimum for the envelope.

The least quotient makes this divisor at most each fork's, so the penalty is an upper envelope. -/
def inactivityPenaltyDivisor (preset : Preset) (config : Config) : Nat :=
  config.INACTIVITY_SCORE_BIAS.toNat *
    min (min preset.INACTIVITY_PENALTY_QUOTIENT.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat)
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat

/-- The activations of the window.

It is a derived bound, not a rule of the specification. -/
def windowActivations (preset : Preset) (config : Config)
    (count scheduled pending carry horizon forkEpochs : Nat) : Nat :=
  -- Before the fork they are the growth of the active-count path.
  if 0 < forkEpochs then activeCountPath config (count + scheduled) (horizon + 1) - count
  -- From Electra, keys already scheduled at `x` count separately.
  --
  -- Each other activation needs `MAX_EFFECTIVE_BALANCE` of funding.
  --
  -- That funding comes from the unassigned stake, or from the deposit carry.
  --
  -- It may also come from the deposit churn of each epoch.
  --
  -- A key made eligible before Electra has at least `MAX_EFFECTIVE_BALANCE` effective.
  else scheduled +
    (pending + carry + config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat * (horizon + 2)) /
    preset.MAX_EFFECTIVE_BALANCE.toNat

/-- The fixed whistleblower allowance `Omega` of the window.

Every key that is slashable in the window pays it at most the window cap over `WQ`, once.

It bounds the whistleblower rewards of slashings; it is not a rule of the specification. -/
def whistleblowerAllowance (preset : Preset) (config : Config)
    (count scheduled pending carry inactive horizon forkEpochs : Nat) : Nat :=
  -- The slashable keys are active at `x`, activate in the window, or are exited.
  --
  -- The exited ones are not yet withdrawable.
  (count + windowActivations preset config count scheduled pending carry horizon forkEpochs +
      inactive) *
    -- Before the fork the window cap is `MAX_EFFECTIVE_BALANCE`.
    (if 0 < forkEpochs then preset.MAX_EFFECTIVE_BALANCE.toNat
      -- From Electra it is `MAX_EFFECTIVE_BALANCE_ELECTRA`, since a key may switch to compounding.
      else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) /
    whistleblowerQuotient preset forkEpochs

/-- The ceiling `T_plus t` on the total active stake at epoch `t` of the window.

It is a derived bound, not a rule of the specification. -/
def stakeCeiling (preset : Preset) (config : Config)
    (count scheduled pending carry inactive funded horizon forkEpochs : Nat) : Nat → Nat
  | 0 =>
    -- Before the fork it is `MIN_ACTIVATION_BALANCE` times the active-count path.
    if 0 < forkEpochs then preset.MIN_ACTIVATION_BALANCE.toNat * (count + scheduled)
    -- From Electra it starts at the funded stake, plus the deposit carry, plus `Omega`.
    --
    -- The funded stake also counts the stake active only at the previous epoch.
    else funded + carry +
      whistleblowerAllowance preset config count scheduled pending carry inactive horizon forkEpochs
  | t + 1 =>
    if 0 < forkEpochs ∧ t + 1 ≤ forkEpochs then
      preset.MIN_ACTIVATION_BALANCE.toNat * activeCountPath config (count + scheduled) (t + 1)
    else
      let previous := stakeCeiling preset config count scheduled pending carry inactive funded
        horizon forkEpochs t
      -- Each epoch then adds twice the issuance envelope.
      --
      -- It also adds `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`.
      --
      -- The factor two covers one epoch's rewards and proposer rewards for two epochs of flags.
      --
      -- It also covers the sync rewards.
      previous + 2 * preset.epochIssuanceBeforeAltair previous +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- The exits `nX_t` of epoch `t`. -/
def exitFlow (preset : Preset) (config : Config) (count scheduled horizon forkEpochs : Nat)
    (ceiling : Nat → Nat) (t : Nat) : Nat :=
  -- Before the fork they are the count churn at the end of the path, in `MIN_ACTIVATION_BALANCE`.
  --
  -- Before the fork the count churn is the validator churn limit of Phase 0.
  if t < forkEpochs then
    preset.MIN_ACTIVATION_BALANCE.toNat *
      cohortCap config (activeCountPath config (count + scheduled) (horizon + 1))
  -- From Electra they are the activation and exit part of `delta`, read at the ceiling.
  --
  -- That is the activation and exit churn of EIP-7251, read at the ceiling.
  else activationExitChurn preset config (ceiling t)

/-- The consolidations `nC_t` of epoch `t`: none before the fork, the constant cap `Cc` after.

`Cc` is the consolidation churn `C (T_plus (H + 1))` at the last ceiling of the window.

That is the consolidation churn of EIP-7251, read at that ceiling. -/
def consolidationFlow (preset : Preset) (config : Config) (horizon forkEpochs : Nat)
    (ceiling : Nat → Nat) (t : Nat) : Nat :=
  if t < forkEpochs then 0 else consolidationChurn preset config (ceiling (horizon + 1))

/-- The non-slashing penalty `lambda_t` of epoch `t` over a stake `weight`, at a floor `lower`.

It is a derived envelope, not a rule of the specification. -/
def epochPenalty (preset : Preset) (config : Config) (score weight lower t : Nat) : Nat :=
  -- The first part is `omega * BRF * weight / sqrt lower`, with `omega = (3 + BRPE) / BRPE`.
  --
  -- `BRF` is `BASE_REWARD_FACTOR`, and `BRPE` is `BASE_REWARDS_PER_EPOCH`.
  --
  -- The first part bounds the source and target penalties of the participation flags from Altair.
  --
  -- It also bounds the penalties of the sync committee.
  (3 + BASE_REWARDS_PER_EPOCH.toNat) * preset.BASE_REWARD_FACTOR.toNat * weight /
      (BASE_REWARDS_PER_EPOCH.toNat * lower.sqrt) +
    -- The second part is the leak penalty at the score `score + bias * (t + 1)`.
    --
    -- The second part bounds the inactivity penalty at that score.
    weight * (score + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) / inactivityPenaltyDivisor
        preset config

/-- The floor `T_minus t` on the total active stake at epoch `t` of the window.

Each epoch takes its outflow and its penalty from it.

It is a derived bound, not a rule of the specification. -/
def stakeFloorPath (preset : Preset) (config : Config) (score : Nat)
    (weight outflow : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | t + 1 =>
    let lower := stakeFloorPath preset config score weight outflow start t
    lower - outflow t - epochPenalty preset config score (weight t) lower t

/-- The keys `N_plus` that a branch may hold at the end of the window.

Growth of the last ceiling above the stake adds at most one key per `MIN_ACTIVATION_BALANCE`.

A partial `MIN_ACTIVATION_BALANCE` of growth counts as one key. -/
def finalKeyCount (preset : Preset) (stake count last : Nat) : Nat :=
  count + (last - stake + preset.MIN_ACTIVATION_BALANCE.toNat - 1) /
    preset.MIN_ACTIVATION_BALANCE.toNat

/-- The start `T_minus 0` of the floor. -/
def stakeFloorStart (preset : Preset)
    (stake slashed count slack departures partials budget last forkEpochs : Nat) : Nat :=
  -- It is the stake less the slashed stake, the slack and one increment per key of `N_plus`.
  stake - slashed - slack -
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat * finalKeyCount preset stake count last -
    -- It also loses the slashing penalties of the ceiling, the due partials and the departures.
    --
    -- The departures are the scheduled ones and the whole departure budget of the window.
    --
    -- The slashing penalty term divides by `MSPQ`.
    --
    -- That is the least quotient of the initial slashing penalty.
    last / minSlashingPenaltyQuotient preset forkEpochs - partials - departures - budget

/-- The floor path of a window, with every input read from the observables.

The start takes the departure budget in full.

So no epoch has an outflow, and each epoch takes only its penalty. -/
def stakeFloor (preset : Preset) (config : Config)
    (stake slashed penalised count score slack carry pending scheduled departures partials budget
      inactive funded horizon forkEpochs : Nat) : Nat → Nat :=
  let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded horizon
    forkEpochs
  stakeFloorPath preset config score (fun t => ceiling t + penalised) (fun _ => 0)
    (stakeFloorStart preset stake slashed count slack departures partials budget
      (ceiling (horizon + 1)) forkEpochs)

/-- The conditions under which the drift uses its formula.

When the guard fails, the drift is the unslashed active stake, and the bound says nothing. -/
abbrev aprioriGuard (preset : Preset) (config : Config)
    (stake slashed penalised count score slack carry pending scheduled departures partials budget
      inactive funded horizon forkEpochs : Nat) : Prop :=
  -- The increment and the churn quotient are positive.
  0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧ 0 < config.CHURN_LIMIT_QUOTIENT.toNat ∧
    -- The minimum validator churn of Phase 0, a count of validators per epoch, is positive.
    --
    -- With a zero minimum, a queue still lets one validator exit per epoch.
    --
    -- The formula does not charge that exit.
    0 < config.MIN_PER_EPOCH_CHURN_LIMIT.toNat ∧
    -- The other divisors are positive, and the whistleblower quotient exceeds one.
    0 < preset.MAX_EFFECTIVE_BALANCE.toNat ∧
    0 < preset.MIN_ACTIVATION_BALANCE.toNat ∧ 0 < preset.downwardBand ∧
    0 < inactivityPenaltyDivisor preset config ∧ 0 < minSlashingPenaltyQuotient preset forkEpochs ∧
    1 < whistleblowerQuotient preset forkEpochs ∧
    -- The withdrawal delay is at least two epochs.
    2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ∧
    -- The window ends before half the slashings vector, and the floor stays positive through it.
    --
    -- The floor takes the departure budget at its start.
    horizon + 2 < preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 ∧
    (∀ t < horizon + 2, 0 < stakeFloor preset config stake slashed penalised count score slack
      carry pending scheduled departures partials budget inactive funded horizon forkEpochs t) ∧
    -- From the fork on, twice the ceiling is at most three times the floor.
    --
    -- That ratio keeps one epoch's issuance below twice the issuance envelope of the ceiling.
    (∀ t, forkEpochs ≤ t → t ≤ horizon + 1 →
      2 * stakeCeiling preset config count scheduled pending carry inactive funded horizon
        forkEpochs t ≤
      3 * stakeFloor preset config stake slashed penalised count score slack carry pending
        scheduled departures partials budget inactive funded horizon forkEpochs t) ∧
    -- The last condition asks that a window from a state before Electra end before the fork.
    --
    -- The condition also carries two fallbacks, both set through `forkEpochs = 1`.
    --
    -- They are for a state before Altair and for a state that cannot reach Electra.
    --
    -- Dropping the condition for crossing windows would also drop both fallbacks.
    (forkEpochs = 0 ∨ horizon + 2 ≤ forkEpochs)

/-- The departures that the queues admit in the window, from their ends at `x`.

It is a derived bound on the churn of the exit and consolidation queues of Electra.

Those queues spend the activation and exit churn and the consolidation churn of EIP-7251. -/
def departureBudget (preset : Preset) (config : Config)
    (count scheduled pending carry inactive funded queued exitEnd consolidationEnd horizon
      forkEpochs : Nat) : Nat :=
  let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded
    horizon forkEpochs
  -- Before the fork the exit churn is the count churn at the end of the active-count path.
  let exitRate := if 0 < forkEpochs then
      preset.MIN_ACTIVATION_BALANCE.toNat *
        cohortCap config (activeCountPath config (count + scheduled) (horizon + 1))
    -- From Electra it is `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`.
    else config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  -- From Electra consolidations add `Cc`, the consolidation churn at the last ceiling.
  let consolidationRate := if 0 < forkEpochs then 0
    else consolidationChurn preset config (ceiling (horizon + 1))
  -- It is the carry of the queues, and the churn of each epoch from the end of each queue on.
  queued + (horizon + 2 - exitEnd) * exitRate +
    (horizon + 2 - consolidationEnd) * consolidationRate +
    -- Two `MAX_EFFECTIVE_BALANCE_ELECTRA` cover one departure at each end of the window.
    2 * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- `W`: the active effective stake at `x`, slashed keys included. -/
noncomputable def referenceStake (x : ForkedBeaconState preset) : Nat :=
  Models.stake (effectiveWeight x.state) (activeKeys x.state)

/-- `Z`: the active effective stake at `x` of the slashed keys. -/
noncomputable def slashedActiveStake (x : ForkedBeaconState preset) : Nat :=
  referenceStake x - Models.stake (effectiveWeight x.state) (unslashedKeys x.state)

/-- `Y`: the effective stake of slashed, inactive keys that are not yet withdrawable. -/
def slashedUnwithdrawnStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if v.slashed && !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.withdrawableEpoch) then
      v.effectiveBalance.toNat else 0).sum

/-- `N`: the number of active keys at `x`. -/
noncomputable def referenceCount (x : ForkedBeaconState preset) : Nat :=
  (activeKeys x.state).card

/-- `sigma`: the larger of the largest inactivity score and the bias times the finality delay.

Before Altair there is no score. -/
def startInactivityScore (config : Config) (x : ForkedBeaconState preset) : Nat :=
  max (if altair : .altair ≤ x.fork then
      ((x.state.inactivityScores altair).data.toList.map (·.toNat)).foldr max 0 else 0)
    (config.INACTIVITY_SCORE_BIAS.toNat *
      ((getPreviousEpoch x.state).toNat - x.state.finalizedCheckpoint.epoch.toNat))

/-- `Lambda`: the effective balance above the balance, summed over the active validators at `x`. -/
def startSlack (x : ForkedBeaconState preset) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    effectiveAt x i.toNat - actualBalanceAt x i.toNat).sum

/-- `Pre`: the stake of validators that are neither active nor exited at `x`.

Each counts the larger of its effective balance and its balance up to its cap. -/
def preActiveStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    if !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.exitEpoch) then
      max (effectiveAt x i)
        (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    else 0).sum

/-- `PreU`: Pre restricted to validators whose activation epoch is not assigned at `x`. -/
def unassignedPreStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    if !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.exitEpoch) &&
        v.activationEpoch == FAR_FUTURE_EPOCH then
      max (effectiveAt x i)
        (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    else 0).sum

/-- `Sx`: the number of validators whose activation epoch is set and after `x`. -/
def scheduledActivationCount (x : ForkedBeaconState preset) : Nat :=
  x.state.validators.data.toList.countP fun v =>
    decide (getCurrentEpoch x.state < v.activationEpoch) && v.activationEpoch != FAR_FUTURE_EPOCH

/-- `Sch`: the effective balance of active validators whose exit epoch is within the window. -/
def scheduledExitStake (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if isActiveValidator v (getCurrentEpoch x.state) &&
        decide (v.exitEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1) then
      v.effectiveBalance.toNat else 0).sum

/-- `Pi_p`: the pending partial withdrawals that are withdrawable within the window.

Overdue entries count too, and there are none before Electra. -/
def duePartialWithdrawals (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    ((x.state.pendingPartialWithdrawals electra).data.toList.map fun w =>
      if w.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1 then
        w.amount.toNat else 0).sum
  else 0

/-- `Pi_c`: the credits of pending consolidations whose source is withdrawable within the window.

Each credit is the smaller of the balance and the effective balance of its source. -/
def dueConsolidationCredits (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    ((x.state.pendingConsolidations electra).data.toList.map fun c =>
      match x.state.validators.data[c.sourceIndex.toNat]? with
      | some v =>
        if v.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1 then
          min (actualBalanceAt x c.sourceIndex.toNat) v.effectiveBalance.toNat else 0
      | none => 0).sum
  else 0

/-- `Bd`: the largest effective balance that exits in two adjacent epochs of the window. -/
def adjacentExitStake (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  ((List.range (horizon + 1)).map fun t =>
    (x.state.validators.data.toList.map fun v =>
      if v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t ∨
          v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t + 1 then
        v.effectiveBalance.toNat else 0).sum).foldr max 0

/-- `nXS`: the number of unslashed validators that have exited but are not yet withdrawable. -/
def exitedSlashableCount (x : ForkedBeaconState preset) : Nat :=
  x.state.validators.data.toList.countP fun v =>
    !v.slashed && decide (v.exitEpoch ≤ getCurrentEpoch x.state) &&
      decide (getCurrentEpoch x.state < v.withdrawableEpoch)

/-- `B`: the slashable base at `x`.

It counts the validators that are unslashed at `x` and not yet withdrawable at its epoch.

Each counts at the larger of its effective and actual balance. -/
def slashableBase (x : ForkedBeaconState preset) : Nat :=
  ∑ i ∈ Finset.range x.state.validators.data.size,
    (x.state.validators.data[i]?.map fun v =>
      if !v.slashed && decide (getCurrentEpoch x.state < v.withdrawableEpoch) then
        max (effectiveAt x i) (actualBalanceAt x i) else 0).getD 0

/-- The effective stake at `x` of the validators active at the previous epoch but not at `x`.

Slashed validators count too.

Their attestations of the previous epoch still pay proposers in the first epoch of a branch. -/
def previousOnlyStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if isActiveValidator v (getPreviousEpoch x.state) &&
        !isActiveValidator v (getCurrentEpoch x.state) then
      v.effectiveBalance.toNat else 0).sum

/-- `H1`: the epochs of the window before Electra, and zero from Electra on. -/
def preElectraEpochs (config : Config) (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if x.fork < .pectra then
    -- A state before Altair takes `H1 = 1`, so a window from it falls back to `W - Z`.
    if x.fork < .altair then 1
    else if (getCurrentEpoch x.state).toNat < config.ELECTRA_FORK_EPOCH.toNat then
      min (driftHorizon x high + 2)
        (config.ELECTRA_FORK_EPOCH.toNat - (getCurrentEpoch x.state).toNat)
    -- A state before Electra whose epoch has reached the fork epoch never upgrades.
    --
    -- The upgrade fires only at the boundary of that epoch.
    --
    -- `H1 = 1` then fails the clause of the guard against crossing.
    --
    -- So the drift falls back to `W - Z`.
    else 1
  else 0

/-- The guard of a branch from `x` through `high + 1`, with every observable read at `x`. -/
noncomputable def aprioriGuardAt (config : Config) (x : ForkedBeaconState preset)
    (high : Nat) : Prop :=
  aprioriGuard preset config (referenceStake x) (slashedActiveStake x) (slashedUnwithdrawnStake x)
    (referenceCount x) (startInactivityScore config x) (startSlack x) (fundingCarry x)
        (unassignedPreStake x)
    (scheduledActivationCount x) (scheduledExitStake x (driftHorizon x high))
    (duePartialWithdrawals x (driftHorizon x high))
    (departureBudget preset config (referenceCount x) (scheduledActivationCount x)
          (unassignedPreStake x)
      (fundingCarry x) (exitedSlashableCount x) (fundedStake x + previousOnlyStake x)
      (queueCarry x high) (exitQueueStart x - (getCurrentEpoch x.state).toNat)
      (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
      (driftHorizon x high) (preElectraEpochs config x high))
    (exitedSlashableCount x)
    (fundedStake x + previousOnlyStake x) (driftHorizon x high) (preElectraEpochs config x high)

/-- The ceiling `T_plus` of a branch from `x` through `high + 1`, from observables at `x`. -/
noncomputable def stakeCeilingAt (config : Config) (x : ForkedBeaconState preset)
    (high : Nat) : Nat → Nat :=
  stakeCeiling preset config (referenceCount x) (scheduledActivationCount x) (unassignedPreStake x)
      (fundingCarry x)
    (exitedSlashableCount x) (fundedStake x + previousOnlyStake x) (driftHorizon x high)
    (preElectraEpochs config x high)

/-- The floor `T_minus` of a branch from `x` through `high + 1`, from observables at `x`. -/
noncomputable def stakeFloorAt (config : Config) (x : ForkedBeaconState preset)
    (high : Nat) : Nat → Nat :=
  stakeFloor preset config (referenceStake x) (slashedActiveStake x) (slashedUnwithdrawnStake x)
    (referenceCount x) (startInactivityScore config x) (startSlack x) (fundingCarry x)
        (unassignedPreStake x)
    (scheduledActivationCount x) (scheduledExitStake x (driftHorizon x high))
    (duePartialWithdrawals x (driftHorizon x high))
    (departureBudget preset config (referenceCount x) (scheduledActivationCount x)
          (unassignedPreStake x)
      (fundingCarry x) (exitedSlashableCount x) (fundedStake x + previousOnlyStake x)
      (queueCarry x high) (exitQueueStart x - (getCurrentEpoch x.state).toNat)
      (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
      (driftHorizon x high) (preElectraEpochs config x high))
    (exitedSlashableCount x)
    (fundedStake x + previousOnlyStake x) (driftHorizon x high) (preElectraEpochs config x high)

section

open Cryptography.Bls Classical

variable {config : Config} {checks : SignatureChecks}

noncomputable section

/-- The last epoch that the budgets read: the epoch of `x` plus `H` plus one.

"Within the window" in a budget means at or before this epoch. -/
abbrev horizonEnd (x : ForkedBeaconState preset) (high : Nat) :=
  (getCurrentEpoch x.state).toNat + driftHorizon x high + 1

/-- The consolidation balance to consume at `x`, or zero before Electra. -/
abbrev consolidationBalanceCarry (x : ForkedBeaconState preset) :=
  if h : .pectra ≤ x.fork then (x.state.consolidationBalanceToConsume h).toNat else 0

/-- The exit balance to consume at `x`, or zero before Electra. -/
abbrev exitBalanceCarry (x : ForkedBeaconState preset) :=
  if h : .pectra ≤ x.fork then (x.state.exitBalanceToConsume h).toNat else 0

/-- The consolidation balance carry if the queue's start plus the withdrawal delay is in the window.

Otherwise it is zero. -/
def dueConsolidationCarry (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if consolidationQueueStart x + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
      horizonEnd x high
  then consolidationBalanceCarry x else 0

/-- The exit balance carry if the exit queue's start falls within the window, and zero otherwise. -/
def dueExitCarry (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if exitQueueStart x ≤ horizonEnd x high then exitBalanceCarry x else 0

/-- The excess of some pending consolidation sources at `x`, and zero before Electra.

A source counts when it is inactive at `x` and withdrawable within the window.

Its excess is its balance capped at its largest effective balance, minus its effective balance.

The cap applies before the subtraction. -/
def pendingSourceExcess (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if h : .pectra ≤ x.fork then
    ((x.state.pendingConsolidations h).data.toList.map fun c =>
      match x.state.validators.data[c.sourceIndex.toNat]? with
      | none => 0
      | some v =>
        if !isActiveValidator v (getCurrentEpoch x.state) &&
            decide (v.withdrawableEpoch.toNat ≤ horizonEnd x high) then
          min (actualBalanceAt x c.sourceIndex.toNat)
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat - v.effectiveBalance.toNat
        else 0).sum
  else 0

namespace Internal

/-- A key's balance capped at its largest effective balance, or its effective balance if larger.

It is zero at an index with no key. -/
def potential (x : ForkedBeaconState preset) (i : Nat) :=
  (x.state.validators.data[i]?.map fun v => max v.effectiveBalance.toNat
    (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)).getD 0

end Internal

/-- The excess of the keys active at `x`, with each balance capped at `x`.

A key counts its balance capped at its largest effective balance, minus its effective balance.

The cap applies before the subtraction. -/
def initialCappedExcess (x : ForkedBeaconState preset) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    Internal.potential x i.toNat - effectiveAt x i.toNat).sum

/-- The largest growth room of the unslashed keys that exit in one epoch of the window.

The growth room of a key is its cap minus twice its effective balance. -/
def exitCohortGrowth (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  ((List.range (horizonEnd x high + 1)).map fun epoch =>
    (x.state.validators.data.toList.map fun v =>
      if isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = epoch) then
        (withdrawalMaxEffectiveBalance preset x.fork v).toNat - 2 * v.effectiveBalance.toNat
      else 0).sum).foldl max 0

/-- The departures that the queues admit in the window, read at `x`. -/
abbrev departureBudgetAt (x : ForkedBeaconState preset) (high : Nat) :=
  departureBudget preset config (referenceCount x) (scheduledActivationCount x)
      (unassignedPreStake x) (fundingCarry x)
    (exitedSlashableCount x) (fundedStake x + previousOnlyStake x) (queueCarry x high)
    (exitQueueStart x - (getCurrentEpoch x.state).toNat)
    (consolidationQueueStart x - (getCurrentEpoch x.state).toNat) (driftHorizon x high)
    (preElectraEpochs config x high)

/-- The exits of the window epoch given as the next argument, read at `x`. -/
abbrev exitFlowAt (x : ForkedBeaconState preset) (high : Nat) :=
  exitFlow preset config (referenceCount x) (scheduledActivationCount x) (driftHorizon x high)
      (preElectraEpochs config x high)
    (stakeCeilingAt config x high)

/-- The consolidations of the window epoch given as the next argument, read at `x`. -/
abbrev consolidationFlowAt (x : ForkedBeaconState preset) (high : Nat) :=
  consolidationFlow preset config (driftHorizon x high) (preElectraEpochs config x high)
      (stakeCeilingAt config x high)

/-- The non-slashing penalties of the first `count` epochs of the window. -/
def windowPenalties (x : ForkedBeaconState preset) (high count : Nat) :=
  ((List.range count).map fun t => epochPenalty preset config (startInactivityScore config x)
    (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) (stakeFloorAt config x high t)
        t).sum

/-- Twice the issuance envelope of the ceiling, over the Electra epochs of the window. -/
def windowIssuance (x : ForkedBeaconState preset) (high : Nat) :=
  (((List.range (driftHorizon x high + 1)).filter (preElectraEpochs config x high ≤ ·)).map fun t =>
    2 * preset.epochIssuanceBeforeAltair (stakeCeilingAt config x high t)).sum

/-- The consolidation churn of the epochs after the consolidation queue's start.

It counts only the epochs that the withdrawal delay leaves inside the window. -/
def consolidationTransfers (x : ForkedBeaconState preset) (high : Nat) :=
  (((List.range (driftHorizon x high + 2 - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)).filter
    (max (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
      (preElectraEpochs config x high) ≤ ·)).map
      (consolidationFlowAt (config := config) x high)).sum

/-- The stake that can become active in the window. -/
def activationBudget (x : ForkedBeaconState preset) (high : Nat) :=
  preActiveStake x + fundingCarry x +
      ((List.range (driftHorizon x high + 1)).map (exitFlowAt (config := config) x high)).sum +
    if 0 < preElectraEpochs config x high then preset.MIN_ACTIVATION_BALANCE.toNat *
        referenceCount x - referenceStake x else 0

/-- The whistleblower allowance of the window, read at `x`. -/
abbrev whistleblowerAllowanceAt (x : ForkedBeaconState preset) (high : Nat) :=
  let omega := whistleblowerAllowance preset config (referenceCount x)
    (scheduledActivationCount x) (unassignedPreStake x) (fundingCarry x)
    (exitedSlashableCount x) (driftHorizon x high) (preElectraEpochs config x high)
  -- When the window has an epoch before Electra, it is `Omega`.
  if 0 < preElectraEpochs config x high then omega
  -- Otherwise, when `WQ` is at least 2, it is also at most a bound over `WQ - 1`.
  --
  -- That bound is the base `B` plus the issuance envelope of the window.
  --
  -- It also adds the deposit carry and the exit flow of the window.
  else if 2 ≤ preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat then
    min omega ((slashableBase x + windowIssuance (config := config) x high + fundingCarry x +
        ((List.range (driftHorizon x high + 1)).map (exitFlowAt (config := config) x high)).sum) /
      (preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat - 1))
  else omega

/-- The credits of the window.

They are the capped excess, due credits, whistleblower allowance, issuance and transfers. -/
def creditBudget (x : ForkedBeaconState preset) (high : Nat) :=
  initialCappedExcess x + dueConsolidationCredits x (driftHorizon x high) +
      whistleblowerAllowanceAt (config := config) x high +
      windowIssuance (config := config) x high +
    consolidationTransfers (config := config) x high

/-- The stake paid out in the window.

It is the due partials, the exit carry and the exits after the queue start. -/
def withdrawalBudget (x : ForkedBeaconState preset) (high : Nat) :=
  duePartialWithdrawals x (driftHorizon x high) + dueExitCarry x high +
    (((List.range (driftHorizon x high + 2)).filter
      (max (exitQueueStart x - (getCurrentEpoch x.state).toNat)
        (preElectraEpochs config x high) ≤ ·)).map (exitFlowAt (config := config) x high)).sum

/-- The effective-balance rounding of downward hysteresis over the window, in Gwei.

It is a number of rounding steps times `EFFECTIVE_BALANCE_INCREMENT`.

That number is the least of three bounds: the final key count and two counts of losses. -/
def roundingBudget (x : ForkedBeaconState preset) (high : Nat) :=
  let a := startSlack x + windowPenalties (config := config) x high (driftHorizon x high + 1)
  preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
    min (finalKeyCount preset (referenceStake x) (referenceCount x)
          (stakeCeilingAt config x high (driftHorizon x high + 1)))
      -- The first count divides the losses and the withdrawal budget by the downward band.
      (min ((a + withdrawalBudget (config := config) x high) / preset.downwardBand)
        -- The second divides the losses by the downward band.
        --
        -- It adds the number of active keys at `x`.
        (a / preset.downwardBand + referenceCount x))

/-- The total gain budget of a branch: activations, credits and pending source excess.

From Electra it adds the rounding budget and the consolidation carry. -/
def gainBudget (x : ForkedBeaconState preset) (high : Nat) :=
  activationBudget (config := config) x high + creditBudget (config := config) x high +
      pendingSourceExcess x high +
    if .pectra ≤ x.fork then roundingBudget (config := config) x high +
        dueConsolidationCarry (config := config) x high
    else 0

/-- Twice the larger exit plus consolidation load of the last two epochs of the window.

It adds `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
def windowEdgeLoad (x : ForkedBeaconState preset) (high : Nat) :=
  2 * max (exitFlowAt (config := config) x high (driftHorizon x high) +
        consolidationFlowAt (config := config) x high (driftHorizon x high))
    (exitFlowAt (config := config) x high (driftHorizon x high + 1) +
          consolidationFlowAt (config := config) x high (driftHorizon x high + 1))
        +
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- The a priori bound on the drift of a window from `x` up to epoch `high + 1`.

When the guard fails, the bound says nothing. -/
def drift (x : ForkedBeaconState preset) (high : Nat) :=
  -- When the guard holds, it is a weighted sum of the budgets of the window.
  --
  -- They are the departures, due partials, scheduled exits, start slack, penalties and rounding.
  --
  -- They also include the gain budget, adjacent exits, previous-only stake and cohort growth.
  --
  -- The edge load is the last.
  if aprioriGuardAt config x high then
    2 * (departureBudgetAt (config := config) x high +
        duePartialWithdrawals x (driftHorizon x high) +
        scheduledExitStake x (driftHorizon x high) + startSlack x +
        windowPenalties (config := config) x high (driftHorizon x high + 1) +
        roundingBudget (config := config) x high) +
      gainBudget (config := config) x high + 2 * adjacentExitStake x (driftHorizon x high) +
      previousOnlyStake x + 2 * exitCohortGrowth x high +
      2 * max (windowEdgeLoad (config := config) x high) (gainBudget (config := config) x high)
  -- Otherwise it is the reference stake less the slashed active stake.
  --
  -- That is the unslashed active stake at `x`, so the bound then says nothing.
  else referenceStake x - slashedActiveStake x

/-- The keys active and unslashed at `x` of validators whose exit epoch is before `cutoff`.

It is empty when `cutoff` is not after the epoch of `x`. -/
def exitedBefore (x : ForkedBeaconState preset) (cutoff : Nat) : Finset BLSPubkey :=
  if cutoff ≤ (getCurrentEpoch x.state).toNat then ∅ else
    (unslashedKeys x.state).filter fun k => ∃ v ∈ x.state.validators.data.toList,
      v.pubkey = k ∧ v.exitEpoch.toNat < cutoff

/-- The a priori accountable-safety statement for two conflicting finalized checkpoints.

When the guard fails at `x`, twice the drift is twice the unslashed stake, and the bound is trivial.
-/
def AccountableDriftBound : Prop := ∀ {g x a b : ForkedBeaconState preset}
  -- Two runs extend a common run from a genesis state `g` to `x`.
  (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b),
  -- The preset meets the parameters of the source bound, and `g` is a genesis state.
  Parameters preset → Genesis (config := config) (checks := checks) g →
  -- The withdrawal delay is positive, and the preset has at least two slots per epoch.
  0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  -- The preset orders its caps.
  --
  -- Its largest effective balances are whole numbers of increments.
  CapOrder preset → MaxEffectiveBalancesAligned preset →
  -- They reach `a` and `b`, before Glamsterdam.
  a.fork < .glamsterdam → b.fork < .glamsterdam →
  -- `x` is at most one epoch past the finalized epoch of `b`.
  (getCurrentEpoch x.state).toNat ≤ b.state.finalizedCheckpoint.epoch.toNat + 1 →
  -- Both runs keep enough stake to the finalized epoch of `b`.
  EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat →
  EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat →
  -- The finalized epoch of `a` is at most that of `b`.
  a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch →
  -- The two finalized checkpoints conflict.
  Conflict (shared.append left) (shared.append right)
    a.state.finalizedCheckpoint b.state.finalizedCheckpoint →
    -- Then the unslashed stake at `x` is at most a bound.
    --
    -- The bound is three times the accountable stake plus twice the drift.
    --
    -- The drift is read at `x`, with the finalized epoch of `b` as `high`.
    Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
        2 * drift (config := config) x b.state.finalizedCheckpoint.epoch.toNat ∨
      -- Otherwise the hash objects of the two runs contain hash evidence.
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects)

/-- The guarded form of the drift bound, which also counts keys that exit before two calls.

It adds the guard at `x` and `high` to the hypotheses of the drift bound. -/
def AccountableWindowBound : Prop := ∀ {g x a b : ForkedBeaconState preset}
  (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b),
  Parameters preset → Genesis (config := config) (checks := checks) g →
  CapOrder preset → MaxEffectiveBalancesAligned preset →
  0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  a.fork < .glamsterdam → b.fork < .glamsterdam →
  (getCurrentEpoch x.state).toNat ≤ b.state.finalizedCheckpoint.epoch.toNat + 1 →
  EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat →
  EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat →
  a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch →
  Conflict (shared.append left) (shared.append right)
    a.state.finalizedCheckpoint b.state.finalizedCheckpoint →
  -- Here `high` is the finalized epoch of `b`.
  aprioriGuardAt config x b.state.finalizedCheckpoint.epoch.toNat →
  -- Then two calls drawn from the runs have target epochs between the two finalized epochs.
  (∃ one two : EitherCall (shared.append left) (shared.append right),
    a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧
    one.targetEpoch ≤ b.state.finalizedCheckpoint.epoch.toNat ∧
    a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧
    two.targetEpoch ≤ b.state.finalizedCheckpoint.epoch.toNat ∧
    -- Let `cutoff` be the earlier of their two target epochs.
    --
    -- The unslashed stake at `x`, plus three times the stake of the keys exiting first, is bounded.
    --
    -- Those keys are active and unslashed at `x`, and their exit epoch is before `cutoff`.
    Models.stake (effectiveWeight x.state) (unslashedKeys x.state) +
      3 * Models.stake (effectiveWeight x.state)
          (exitedBefore x (min one.targetEpoch two.targetEpoch)) ≤
      -- The bound is three times the accountable stake plus twice the drift.
      3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
        2 * drift (config := config) x b.state.finalizedCheckpoint.epoch.toNat) ∨
    -- Otherwise the hash objects of the two runs contain hash evidence.
    HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects)

end

end

end Apriori

end EthLib.Consensus.DirectSafety
