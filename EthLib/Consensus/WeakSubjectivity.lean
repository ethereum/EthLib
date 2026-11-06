module

public import EthLib.Consensus.Churn
public import EthLib.Consensus.ForkChoice.Store

/-!
# `Consensus.WeakSubjectivity`

A node that starts from a recent checkpoint instead of genesis trusts that checkpoint.

That trust is weak subjectivity.

The weak subjectivity period is the number of epochs during which a checkpoint stays safe.

Take an attacker who controls the validator set at the start of the period.

If it finalizes a conflicting checkpoint within the period, it is slashed at least a minimum.

`SAFETY_DECAY` is the largest loss, in percent, that the period allows in the `1/3` safety margin.

So an attack on the period has a safety margin of at least `1/3 - SAFETY_DECAY/100`.

A checkpoint older than the period is stale, and a node should not start from it.

The period is the delay before a validator can withdraw, plus further epochs for the churn.

The churn bounds how fast the validator set can change.

It has three forms.

- Phase 0 counts validators, and bounds the change by the churn of validators and by top-ups.
  A top-up is a deposit to a validator that already exists.
- From Electra, the churn counts Gwei, since [EIP-7251] lets one validator hold more than 32 ether.
- From Gloas, [EIP-8061] gives activations, exits and consolidations separate churns.
  Exits weigh two thirds, activations one third and consolidations one.

Every operation is on 64-bit integers.

A product or a sum that reaches `2^64` is an error, and so is a division by zero.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#churn-computations
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- Why weak subjectivity has no answer for a state, a checkpoint or a store. -/
inductive WeakSubjectivityError where
  /-- A state accessor fails. -/
  | accessor (error : AccessorError)
  /-- The current slot of the store has no value. -/
  | forkChoice (error : ForkChoiceError)
  /-- A 64-bit operation has no result. -/
  | arith (error : ArithError)
  /-- The state does not hold the root of the checkpoint at the checkpoint's epoch. -/
  | blockRootMismatch
  /-- The state is not at the epoch of the checkpoint. -/
  | epochMismatch (checkpointEpoch stateEpoch : Epoch)
  deriving Repr

/-- The code of an error at the C boundary, one for each constructor. -/
def WeakSubjectivityError.code : WeakSubjectivityError → UInt32
  | .accessor _ => 1
  | .forkChoice _ => 2
  | .arith _ => 3
  | .blockRootMismatch => 4
  | .epochMismatch .. => 5

/-! ## Phase 0 -/

/-- Phase 0: the epochs added to the withdrawal delay, from counts of validators and ether.

The arguments are those of the analysis.

- `N` is the number of active validators.
- `t` is their average balance in ether, and `T` the largest effective balance in ether.
- `delta` is the churn of validators in one epoch.
- `Delta` is the number of deposits in one epoch.

Small balances cost the attacker little to top up, so the deposits bound the period.

Otherwise both the churn and the top-ups bound it, and the period waits for the longer. -/
def phase0PeriodEpochs (N t T delta Delta : UInt64) : Except ArithError Epoch := do
  let D := SAFETY_DECAY
  let low ← mulChecked T (200 + 3 * D)
  let high ← mulChecked t (200 + 12 * D)
  if high > low then
    let churnDivisor ← mulChecked (← mulChecked 600 delta)
      (← addChecked (← mulChecked 2 t) T)
    let epochsForValidatorSetChurn ← divChecked (← mulChecked N (high - low)) churnDivisor
    let epochsForBalanceTopUps ←
      divChecked (← mulChecked N (200 + 3 * D)) (← mulChecked 600 Delta)
    return max epochsForValidatorSetChurn epochsForBalanceTopUps
  else
    let numerator ← mulChecked (← mulChecked (← mulChecked 3 N) D) t
    let denominator ← mulChecked (← mulChecked 200 Delta) (← subChecked T t)
    divChecked numerator denominator

/-- Phase 0: the weak subjectivity period of a state.

The average balance divides the total active balance by the number of active validators.

So a state without active validators has no period. -/
def computeWeakSubjectivityPeriodPhase0 (config : Config) (state : BeaconState preset fork) :
    Except WeakSubjectivityError Epoch := do
  let N := (getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64
  let total ← (getTotalActiveBalance state).mapError .accessor
  let t := (← (divChecked total N).mapError .arith) / ETH_TO_GWEI
  let T := preset.MAX_EFFECTIVE_BALANCE / ETH_TO_GWEI
  let delta := getValidatorChurnLimit config state
  let Delta ← (mulChecked preset.MAX_DEPOSITS preset.SLOTS_PER_EPOCH).mapError .arith
  let epochs ← (phase0PeriodEpochs N t T delta Delta).mapError .arith
  (addChecked config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY epochs).mapError .arith

/-! ## From Electra -/

/-- From Electra: the weak subjectivity period of a total active balance and a churn, in Gwei.

The churn must change the decayed margin, `SAFETY_DECAY / 100` of half the balance. -/
def balanceChurnPeriod (minDelay total churn : UInt64) : Except ArithError Epoch := do
  let epochsForValidatorSetChurn ←
    divChecked (← mulChecked SAFETY_DECAY total) (← mulChecked (← mulChecked 2 churn) 100)
  addChecked minDelay epochsForValidatorSetChurn

/-- Electra and Fulu: the weak subjectivity period of a state, with the churn of its balance. -/
def computeWeakSubjectivityPeriodElectra (config : Config) (state : BeaconState preset fork) :
    Except WeakSubjectivityError Epoch := do
  let total ← (getTotalActiveBalance state).mapError .accessor
  let churn ← (getBalanceChurnLimit config state).mapError .accessor
  (balanceChurnPeriod config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY total churn).mapError .arith

/-- From Gloas: the churn that the period counts, a weighted sum of the three churns.

Exits weigh two thirds, activations one third and consolidations one. -/
def gloasWeightedChurn (config : Config) (state : BeaconState preset fork) :
    Except WeakSubjectivityError Gwei := do
  let exit ← (getExitChurnLimit config state).mapError .accessor
  let activation ← (getActivationChurnLimit config state).mapError .accessor
  let consolidation ← (getConsolidationChurnLimit config state).mapError .accessor
  let exitPart := (← (mulChecked 2 exit).mapError .arith) / 3
  let sum ← (addChecked exitPart (activation / 3)).mapError .arith
  (addChecked sum consolidation).mapError .arith

/-- From Gloas: the weak subjectivity period of a state, with the weighted churn. -/
def computeWeakSubjectivityPeriodGloas (config : Config) (state : BeaconState preset fork) :
    Except WeakSubjectivityError Epoch := do
  let total ← (getTotalActiveBalance state).mapError .accessor
  let churn ← gloasWeightedChurn config state
  (balanceChurnPeriod config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY total churn).mapError .arith

/-! ## The period and the staleness check -/

/-- The weak subjectivity period of a state, by the rule of its fork. -/
def computeWeakSubjectivityPeriod (config : Config) (state : BeaconState preset fork) :
    Except WeakSubjectivityError Epoch :=
  if .glamsterdam ≤ fork then computeWeakSubjectivityPeriodGloas config state
  else if .pectra ≤ fork then computeWeakSubjectivityPeriodElectra config state
  else computeWeakSubjectivityPeriodPhase0 config state

/-- Whether a checkpoint is still within its weak subjectivity period at the time of a store.

The state is the state at the checkpoint, which the client supplies with it.

The state must hold the checkpoint's root at the checkpoint's epoch, and be at that epoch.

The check then compares the current epoch of the store with the end of the period. -/
def isWithinWeakSubjectivityPeriod {storeFork : Base.Fork} (config : Config)
    (store : Store preset storeFork) (wsState : BeaconState preset fork)
    (wsCheckpoint : Checkpoint) : Except WeakSubjectivityError Bool := do
  let root ← (getBlockRoot wsState wsCheckpoint.epoch).mapError .accessor
  if root ≠ wsCheckpoint.root then throw .blockRootMismatch
  let wsStateEpoch := computeEpochAtSlot preset wsState.slot
  if wsStateEpoch ≠ wsCheckpoint.epoch then throw (.epochMismatch wsCheckpoint.epoch wsStateEpoch)
  let wsPeriod ← computeWeakSubjectivityPeriod config wsState
  let currentSlot ← (store.getCurrentSlot config).mapError .forkChoice
  let currentEpoch := computeEpochAtSlot preset currentSlot
  return currentEpoch ≤ (← (addChecked wsStateEpoch wsPeriod).mapError .arith)

end EthLib.Consensus
